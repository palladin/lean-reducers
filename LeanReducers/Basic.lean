import Init.Data.Float
import Init.System.IO
import LeanReducers.Internal.Array
import LeanReducers.Internal.File
import LeanReducers.Internal.GroupBy

namespace LeanReducers

/--
A lazy, fused pipeline over input elements of type `α`.

The producer chooses the effect `m`: in-memory arrays use `Id`, while producers
such as file readers use `IO`. Transformations remain fused by rewriting the
terminal step instead of allocating intermediate collections.
-/
structure ReducerM (m : Type → Type) (α : Type) where
  run : {ρ : Type} → Config → FoldSpec α ρ → m ρ

abbrev Reducer (α : Type) :=
  ReducerM Id α

abbrev ReducerIO (α : Type) :=
  ReducerM IO α

namespace Reducer

def ofArray (as : Array α) : Reducer α where
  run := fun cfg q => (Internal.foldArrayTask cfg q as).get

def ofArrayM [Monad m] (as : m (Array α)) : ReducerM m α where
  run := fun cfg q => do
    let as ← as
    pure (Internal.foldArrayTask cfg q as).get

def readFile (path : System.FilePath) : ReducerIO String :=
  ofArrayM do
    let contents ← IO.FS.readFile path
    pure #[contents]

def readLines (path : System.FilePath) : ReducerIO String :=
  { run := fun cfg q => Internal.foldFileLinesIO cfg q path }

def readLinesFromFiles (paths : Array System.FilePath) : ReducerIO String :=
  { run := fun cfg q => Internal.foldFilesLinesIO cfg q paths }

def readLinesFromFilesWithPath (paths : Array System.FilePath) :
    ReducerIO (System.FilePath × String) :=
  { run := fun cfg q => Internal.foldFilesLinesWithPathIO cfg q paths }

def readChars (path : System.FilePath) : ReducerIO Char :=
  ofArrayM do
    let contents ← IO.FS.readFile path
    pure contents.toList.toArray

private def mapM (xs : ReducerM m α) (f : α → β) : ReducerM m β where
  run := fun cfg q =>
    xs.run cfg { unit := q.unit, combine := q.combine, step := fun a acc => q.step (f a) acc }

private def flatMapM (xs : ReducerM m α) (f : α → Array β) : ReducerM m β where
  run := fun cfg q =>
    xs.run cfg {
      unit := q.unit
      combine := q.combine
      step := fun a acc => (f a).foldr q.step acc
    }

private def filterM (xs : ReducerM m α) (p : α → Bool) : ReducerM m α where
  run := fun cfg q =>
    let q' := ({
      unit := q.unit
      combine := q.combine
      step := fun a acc => if p a then q.step a acc else acc
    } : FoldSpec α _)
    xs.run cfg q'

private def foldWithConfigM (cfg : Config) (spec : MonoidSpec ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ := do
  xs.run cfg (FoldSpec.ofMonoid spec step)

/--
Reduce with a proven monoid combiner and caller-provided local step. For
parallel-grouping-invariant results, the step should agree with the combiner:
`step a acc = spec.combine (step a spec.unit) acc`.
-/
private def foldM (spec : MonoidSpec ρ) (step : α → ρ → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  foldWithConfigM Config.default spec step xs

private def foldMapWithConfigM (cfg : Config) (spec : MonoidSpec ρ) (f : α → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  foldWithConfigM cfg spec (fun a acc => spec.combine (f a) acc) xs

private def foldMapM (spec : MonoidSpec ρ) (f : α → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  foldMapWithConfigM Config.default spec f xs

private def groupByWithConfigM [BEq κ] (cfg : Config) (valueSpec : MonoidSpec ν)
    (key : α → κ) (step : α → ν → ν) [Monad m]
    (xs : ReducerM m α) : m (Array (κ × ν)) := do
  xs.run cfg {
    unit := #[]
    combine := Internal.mergeGroups valueSpec
    step := Internal.groupStep valueSpec key step
  }

private def groupByM [BEq κ] (valueSpec : MonoidSpec ν) (key : α → κ) (step : α → ν → ν)
    [Monad m] (xs : ReducerM m α) : m (Array (κ × ν)) :=
  groupByWithConfigM Config.default valueSpec key step xs

/--
Approximate fold for operations where the caller does not want to claim monoid
laws. This is intended for practical numeric reductions such as `Float`, where
parallel grouping can change the final rounded value.
-/
private def foldApproxWithConfigM (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (step : α → ρ → ρ) [Monad m] (xs : ReducerM m α) : m ρ := do
  xs.run cfg { unit := unit, combine := combine, step := step }

private def foldApproxM (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  foldApproxWithConfigM Config.default unit combine step xs

private def sumM [Add α] [OfNat α 0] [LawfulAddMonoid α] [Monad m]
    (xs : ReducerM m α) : m α :=
  foldM (MonoidSpec.additive α) (fun a acc => a + acc) xs

/--
Floating-point sum is intentionally approximate: IEEE floating-point addition is
not a lawful monoid, so this terminal is separate from `.sum`.
-/
private def sumFloatApproxM [Monad m] (xs : ReducerM m Float) : m Float :=
  foldApproxM (0.0 : Float) (fun a b => a + b) (fun a acc => a + acc) xs

def map (xs : Reducer α) (f : α → β) : Reducer β :=
  mapM xs f

def flatMap (xs : Reducer α) (f : α → Array β) : Reducer β :=
  flatMapM xs f

def filter (xs : Reducer α) (p : α → Bool) : Reducer α :=
  filterM xs p

def foldWithConfig (cfg : Config) (spec : MonoidSpec ρ) (step : α → ρ → ρ)
    (xs : Reducer α) : ρ :=
  foldWithConfigM cfg spec step xs

def fold (spec : MonoidSpec ρ) (step : α → ρ → ρ) (xs : Reducer α) : ρ :=
  foldM spec step xs

def foldMapWithConfig (cfg : Config) (spec : MonoidSpec ρ) (f : α → ρ)
    (xs : Reducer α) : ρ :=
  foldMapWithConfigM cfg spec f xs

def foldMap (spec : MonoidSpec ρ) (f : α → ρ) (xs : Reducer α) : ρ :=
  foldMapM spec f xs

def groupByWithConfig [BEq κ] (cfg : Config) (valueSpec : MonoidSpec ν)
    (key : α → κ) (step : α → ν → ν) (xs : Reducer α) : Array (κ × ν) :=
  groupByWithConfigM cfg valueSpec key step xs

def groupBy [BEq κ] (valueSpec : MonoidSpec ν) (key : α → κ) (step : α → ν → ν)
    (xs : Reducer α) : Array (κ × ν) :=
  groupByM valueSpec key step xs

def foldApproxWithConfig (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (step : α → ρ → ρ) (xs : Reducer α) : ρ :=
  foldApproxWithConfigM cfg unit combine step xs

def foldApprox (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    (xs : Reducer α) : ρ :=
  foldApproxM unit combine step xs

def sum [Add α] [OfNat α 0] [LawfulAddMonoid α] (xs : Reducer α) : α :=
  sumM xs

def sumFloatApprox (xs : Reducer Float) : Float :=
  sumFloatApproxM xs

end Reducer

namespace ReducerM

def map (xs : ReducerM m α) (f : α → β) : ReducerM m β :=
  Reducer.mapM xs f

def flatMap (xs : ReducerM m α) (f : α → Array β) : ReducerM m β :=
  Reducer.flatMapM xs f

def filter (xs : ReducerM m α) (p : α → Bool) : ReducerM m α :=
  Reducer.filterM xs p

def foldWithConfig (cfg : Config) (spec : MonoidSpec ρ) (step : α → ρ → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  Reducer.foldWithConfigM cfg spec step xs

def fold (spec : MonoidSpec ρ) (step : α → ρ → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  Reducer.foldM spec step xs

def foldMapWithConfig (cfg : Config) (spec : MonoidSpec ρ) (f : α → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  Reducer.foldMapWithConfigM cfg spec f xs

def foldMap (spec : MonoidSpec ρ) (f : α → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  Reducer.foldMapM spec f xs

def groupByWithConfig [BEq κ] (cfg : Config) (valueSpec : MonoidSpec ν)
    (key : α → κ) (step : α → ν → ν) [Monad m]
    (xs : ReducerM m α) : m (Array (κ × ν)) :=
  Reducer.groupByWithConfigM cfg valueSpec key step xs

def groupBy [BEq κ] (valueSpec : MonoidSpec ν) (key : α → κ) (step : α → ν → ν)
    [Monad m] (xs : ReducerM m α) : m (Array (κ × ν)) :=
  Reducer.groupByM valueSpec key step xs

def foldApproxWithConfig (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (step : α → ρ → ρ) [Monad m] (xs : ReducerM m α) : m ρ :=
  Reducer.foldApproxWithConfigM cfg unit combine step xs

def foldApprox (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  Reducer.foldApproxM unit combine step xs

def sum [Add α] [OfNat α 0] [LawfulAddMonoid α] [Monad m]
    (xs : ReducerM m α) : m α :=
  Reducer.sumM xs

def sumFloatApprox [Monad m] (xs : ReducerM m Float) : m Float :=
  Reducer.sumFloatApproxM xs

end ReducerM

end LeanReducers

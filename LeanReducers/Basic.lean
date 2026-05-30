import Init.Data.Float
import Init.Data.Array.Lemmas
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

private def reduceWithLawsWithConfigM (cfg : Config) (spec : MonoidSpec ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ := do
  xs.run cfg (FoldSpec.ofMonoid spec step)

/--
Reduce with a proven monoid combiner and caller-provided local step. For
parallel-grouping-invariant results, the step should agree with the combiner:
`step a acc = spec.combine (step a spec.unit) acc`.
-/
private def reduceWithLawsM (spec : MonoidSpec ρ) (step : α → ρ → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  reduceWithLawsWithConfigM Config.default spec step xs

private def reduceMapWithLawsWithConfigM (cfg : Config) (spec : MonoidSpec ρ) (f : α → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  reduceWithLawsWithConfigM cfg spec (fun a acc => spec.combine (f a) acc) xs

private def reduceMapWithLawsM (spec : MonoidSpec ρ) (f : α → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  reduceMapWithLawsWithConfigM Config.default spec f xs

private def groupByWithConfigM [BEq κ] [Hashable κ] (cfg : Config) (valueSpec : MonoidSpec ν)
    (key : α → κ) (step : α → ν → ν) [Monad m]
    (xs : ReducerM m α) : m (Array (κ × ν)) := do
  let groups ← xs.run cfg {
    unit := Internal.emptyGroups
    combine := Internal.mergeGroups valueSpec
    step := Internal.groupStep valueSpec key step
  }
  pure (Internal.groupsToArray groups)

private def groupByM [BEq κ] [Hashable κ] (valueSpec : MonoidSpec ν) (key : α → κ)
    (step : α → ν → ν) [Monad m] (xs : ReducerM m α) : m (Array (κ × ν)) :=
  groupByWithConfigM Config.default valueSpec key step xs

/--
Reduce without law proofs for operations where the caller does not want to provide
a `MonoidSpec`. The same parallel regrouping rules still apply; the library
just does not require proofs for the supplied combiner.
-/
private def reduceWithoutLawsWithConfigM (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (step : α → ρ → ρ) [Monad m] (xs : ReducerM m α) : m ρ := do
  xs.run cfg { unit := unit, combine := combine, step := step }

private def reduceWithoutLawsM (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  reduceWithoutLawsWithConfigM Config.default unit combine step xs

private def sumM [Add α] [OfNat α 0] [LawfulAddMonoid α] [Monad m]
    (xs : ReducerM m α) : m α :=
  reduceWithLawsM (MonoidSpec.additive α) (fun a acc => a + acc) xs

/--
Floating-point sum uses the reduce-without-laws path: IEEE floating-point addition is
not a lawful monoid, so this terminal is separate from `.sum`.
-/
private def sumFloatM [Monad m] (xs : ReducerM m Float) : m Float :=
  reduceWithoutLawsM (0.0 : Float) (fun a b => a + b) (fun a acc => a + acc) xs

private def reversedArraySpec (α : Type) : MonoidSpec (Array α) where
  unit := #[]
  combine := fun left right => right ++ left
  assoc := by
    intro a b c
    simp [Array.append_assoc]
  left_unit := by
    intro a
    simp
  right_unit := by
    intro a
    simp

private def toArrayM [Monad m] (xs : ReducerM m α) : m (Array α) := do
  let reversed ← reduceWithLawsM (reversedArraySpec α) (fun a acc => acc.push a) xs
  pure reversed.reverse

private def lengthM [Monad m] (xs : ReducerM m α) : m Nat :=
  reduceMapWithLawsM (MonoidSpec.additive Nat) (fun _ => (1 : Nat)) xs

private def minOption [Min α] (left right : Option α) : Option α :=
  match left, right with
  | none, other => other
  | other, none => other
  | some a, some b => some (min a b)

private def maxOption [Max α] (left right : Option α) : Option α :=
  match left, right with
  | none, other => other
  | other, none => other
  | some a, some b => some (max a b)

private def minM [Min α] [Monad m] (xs : ReducerM m α) : m (Option α) :=
  reduceWithoutLawsM (none : Option α) (minOption (α := α))
    (fun a acc => minOption (α := α) (some a) acc) xs

private def maxM [Max α] [Monad m] (xs : ReducerM m α) : m (Option α) :=
  reduceWithoutLawsM (none : Option α) (maxOption (α := α))
    (fun a acc => maxOption (α := α) (some a) acc) xs

private structure FloatAverage where
  sum : Float
  count : Nat

private def avgFloatM [Monad m] (xs : ReducerM m Float) : m (Option Float) := do
  let total ←
    reduceWithoutLawsM ({ sum := 0.0, count := 0 } : FloatAverage)
      (fun left right => {
        sum := left.sum + right.sum
        count := left.count + right.count
      })
      (fun a acc => {
        sum := a + acc.sum
        count := acc.count + 1
      })
      xs
  if total.count == 0 then
    pure none
  else
    pure (some (total.sum / Float.ofNat total.count))

def map (xs : Reducer α) (f : α → β) : Reducer β :=
  mapM xs f

def flatMap (xs : Reducer α) (f : α → Array β) : Reducer β :=
  flatMapM xs f

def filter (xs : Reducer α) (p : α → Bool) : Reducer α :=
  filterM xs p

def reduceWithLawsWithConfig (cfg : Config) (spec : MonoidSpec ρ) (step : α → ρ → ρ)
    (xs : Reducer α) : ρ :=
  reduceWithLawsWithConfigM cfg spec step xs

def reduceWithLaws (spec : MonoidSpec ρ) (step : α → ρ → ρ) (xs : Reducer α) : ρ :=
  reduceWithLawsM spec step xs

def reduceMapWithLawsWithConfig (cfg : Config) (spec : MonoidSpec ρ) (f : α → ρ)
    (xs : Reducer α) : ρ :=
  reduceMapWithLawsWithConfigM cfg spec f xs

def reduceMapWithLaws (spec : MonoidSpec ρ) (f : α → ρ) (xs : Reducer α) : ρ :=
  reduceMapWithLawsM spec f xs

def groupByWithConfig [BEq κ] [Hashable κ] (cfg : Config) (valueSpec : MonoidSpec ν)
    (key : α → κ) (step : α → ν → ν) (xs : Reducer α) : Array (κ × ν) :=
  groupByWithConfigM cfg valueSpec key step xs

def groupBy [BEq κ] [Hashable κ] (valueSpec : MonoidSpec ν) (key : α → κ)
    (step : α → ν → ν) (xs : Reducer α) : Array (κ × ν) :=
  groupByM valueSpec key step xs

def reduceWithoutLawsWithConfig (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (step : α → ρ → ρ) (xs : Reducer α) : ρ :=
  reduceWithoutLawsWithConfigM cfg unit combine step xs

def reduceWithoutLaws (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    (xs : Reducer α) : ρ :=
  reduceWithoutLawsM unit combine step xs

def sum [Add α] [OfNat α 0] [LawfulAddMonoid α] (xs : Reducer α) : α :=
  sumM xs

def sumFloat (xs : Reducer Float) : Float :=
  sumFloatM xs

def toArray (xs : Reducer α) : Array α :=
  toArrayM xs

def length (xs : Reducer α) : Nat :=
  lengthM xs

def min? [Min α] (xs : Reducer α) : Option α :=
  minM xs

def min [Min α] (xs : Reducer α) (h : xs.min?.isSome) : α :=
  xs.min?.get h

def max? [Max α] (xs : Reducer α) : Option α :=
  maxM xs

def max [Max α] (xs : Reducer α) (h : xs.max?.isSome) : α :=
  xs.max?.get h

def avgFloat (xs : Reducer Float) : Option Float :=
  avgFloatM xs

def avg (xs : Reducer Float) : Option Float :=
  avgFloatM xs

end Reducer

namespace ReducerM

def map (xs : ReducerM m α) (f : α → β) : ReducerM m β :=
  Reducer.mapM xs f

def flatMap (xs : ReducerM m α) (f : α → Array β) : ReducerM m β :=
  Reducer.flatMapM xs f

def filter (xs : ReducerM m α) (p : α → Bool) : ReducerM m α :=
  Reducer.filterM xs p

def reduceWithLawsWithConfig (cfg : Config) (spec : MonoidSpec ρ) (step : α → ρ → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  Reducer.reduceWithLawsWithConfigM cfg spec step xs

def reduceWithLaws (spec : MonoidSpec ρ) (step : α → ρ → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  Reducer.reduceWithLawsM spec step xs

def reduceMapWithLawsWithConfig (cfg : Config) (spec : MonoidSpec ρ) (f : α → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  Reducer.reduceMapWithLawsWithConfigM cfg spec f xs

def reduceMapWithLaws (spec : MonoidSpec ρ) (f : α → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  Reducer.reduceMapWithLawsM spec f xs

def groupByWithConfig [BEq κ] [Hashable κ] (cfg : Config) (valueSpec : MonoidSpec ν)
    (key : α → κ) (step : α → ν → ν) [Monad m]
    (xs : ReducerM m α) : m (Array (κ × ν)) :=
  Reducer.groupByWithConfigM cfg valueSpec key step xs

def groupBy [BEq κ] [Hashable κ] (valueSpec : MonoidSpec ν) (key : α → κ)
    (step : α → ν → ν) [Monad m] (xs : ReducerM m α) : m (Array (κ × ν)) :=
  Reducer.groupByM valueSpec key step xs

def reduceWithoutLawsWithConfig (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (step : α → ρ → ρ) [Monad m] (xs : ReducerM m α) : m ρ :=
  Reducer.reduceWithoutLawsWithConfigM cfg unit combine step xs

def reduceWithoutLaws (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  Reducer.reduceWithoutLawsM unit combine step xs

def sum [Add α] [OfNat α 0] [LawfulAddMonoid α] [Monad m]
    (xs : ReducerM m α) : m α :=
  Reducer.sumM xs

def sumFloat [Monad m] (xs : ReducerM m Float) : m Float :=
  Reducer.sumFloatM xs

def toArray [Monad m] (xs : ReducerM m α) : m (Array α) :=
  Reducer.toArrayM xs

def length [Monad m] (xs : ReducerM m α) : m Nat :=
  Reducer.lengthM xs

def min? [Min α] [Monad m] (xs : ReducerM m α) : m (Option α) :=
  Reducer.minM xs

def max? [Max α] [Monad m] (xs : ReducerM m α) : m (Option α) :=
  Reducer.maxM xs

def avgFloat [Monad m] (xs : ReducerM m Float) : m (Option Float) :=
  Reducer.avgFloatM xs

def avg [Monad m] (xs : ReducerM m Float) : m (Option Float) :=
  Reducer.avgFloatM xs

end ReducerM

end LeanReducers

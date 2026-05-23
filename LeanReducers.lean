import Init.Data.Array.Basic
import Init.Data.Float
import Init.Data.Int.Lemmas
import Init.System.IO
import Init.Util

namespace LeanReducers

/--
Runtime knobs for parallel reductions.

`grain` is the smallest chunk size worth splitting, `maxDepth` bounds the task
tree, and `priority` is passed to Lean's task scheduler.
-/
structure Config where
  grain : Nat := 2048
  maxDepth : Nat := 4
  priority : Task.Priority := Task.Priority.default
  deriving Repr

namespace Config

def default : Config := {}

end Config

/--
A tiny law-carrying monoid record. This deliberately avoids Mathlib so the
library remains light and self-contained.
-/
structure MonoidSpec (α : Type) where
  unit : α
  combine : α → α → α
  assoc : ∀ a b c, combine (combine a b) c = combine a (combine b c)
  left_unit : ∀ a, combine unit a = a
  right_unit : ∀ a, combine a unit = a

/--
Minimal additive law class used by `.sum`. We keep it separate from Lean's
runtime `Add` instances because not every `Add` instance is associative in the
mathematical sense; notably, `Float` is intentionally not an instance.
-/
class LawfulAddMonoid (α : Type) [Add α] [OfNat α 0] : Prop where
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  zero_add : ∀ a : α, 0 + a = a
  add_zero : ∀ a : α, a + 0 = a

instance : LawfulAddMonoid Nat where
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero

instance : LawfulAddMonoid Int where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero

namespace MonoidSpec

def additive (α : Type) [Add α] [OfNat α 0] [LawfulAddMonoid α] :
    MonoidSpec α where
  unit := 0
  combine := (· + ·)
  assoc := LawfulAddMonoid.add_assoc
  left_unit := LawfulAddMonoid.zero_add
  right_unit := LawfulAddMonoid.add_zero

end MonoidSpec

/--
Internal fold description used at runtime. Lawful public folds are constructed
from `MonoidSpec`; approximate folds such as floating-point reductions use the
same runtime path without claiming algebraic laws.
-/
structure FoldSpec (α : Type) (ρ : Type) where
  unit : ρ
  combine : ρ → ρ → ρ
  step : α → ρ → ρ

namespace FoldSpec

def ofMonoid (spec : MonoidSpec ρ) (step : α → ρ → ρ) : FoldSpec α ρ where
  unit := spec.unit
  combine := spec.combine
  step := step

end FoldSpec

namespace Internal

@[inline]
def foldRange (q : FoldSpec α ρ) (as : Array α) (start stop : Nat) : ρ :=
  as.foldr q.step q.unit (start := stop) (stop := start)

def foldArrayTaskCore (cfg : Config) (q : FoldSpec α ρ) (as : Array α)
    (start stop : Nat) : Nat → ρ
  | 0 => foldRange q as start stop
  | depth + 1 =>
      let len := stop - start
      if len ≤ cfg.grain then
        foldRange q as start stop
      else if len ≤ 1 then
        foldRange q as start stop
      else
        let mid := start + len / 2
        let right := Task.spawn (fun _ => foldArrayTaskCore cfg q as mid stop depth) cfg.priority
        let left := foldArrayTaskCore cfg q as start mid depth
        q.combine left right.get

def foldArrayTask (cfg : Config) (q : FoldSpec α ρ) (as : Array α) : Task ρ :=
  Task.spawn (fun _ => foldArrayTaskCore cfg q as 0 as.size cfg.maxDepth) cfg.priority

def removeGroupKey [BEq κ] (k : κ) (groups : Array (κ × ν)) : Array (κ × ν) :=
  groups.foldl (fun acc row => if row.1 == k then acc else acc.push row) #[]

def groupStep [BEq κ] (valueSpec : MonoidSpec ν) (key : α → κ) (step : α → ν → ν)
    (a : α) (groups : Array (κ × ν)) : Array (κ × ν) :=
  let k := key a
  match groups.find? (fun row => row.1 == k) with
  | some row => #[(k, step a row.2)] ++ removeGroupKey k groups
  | none => #[(k, step a valueSpec.unit)] ++ groups

def mergeGroupInto [BEq κ] (valueSpec : MonoidSpec ν)
    (groups : Array (κ × ν)) (row : κ × ν) : Array (κ × ν) :=
  match groups.findIdx? (fun existing => existing.1 == row.1) with
  | some i => groups.modify i (fun existing => (existing.1, valueSpec.combine existing.2 row.2))
  | none => groups.push row

def mergeGroups [BEq κ] (valueSpec : MonoidSpec ν)
    (left right : Array (κ × ν)) : Array (κ × ν) :=
  right.foldl (mergeGroupInto valueSpec) left

end Internal

/--
A lazy, fused pipeline over input elements of type `α`.

The producer chooses the effect `m`: in-memory arrays use `Id`, while producers
such as file readers use `IO`. Transformations remain fused by rewriting the
terminal step instead of allocating intermediate collections.
-/
structure ReducerM (m : Type → Type) (α : Type) where
  run : {ρ : Type} → Config → FoldSpec α ρ → m (Task ρ)

abbrev Reducer (α : Type) :=
  ReducerM Id α

abbrev ReducerIO (α : Type) :=
  ReducerM IO α

namespace Reducer

def ofArray (as : Array α) : Reducer α where
  run := fun cfg q => Internal.foldArrayTask cfg q as

def ofArrayM [Monad m] (as : m (Array α)) : ReducerM m α where
  run := fun cfg q => do
    let as ← as
    pure (Internal.foldArrayTask cfg q as)

def ofFile (path : System.FilePath) : ReducerIO String :=
  ofArrayM do
    let contents ← IO.FS.readFile path
    pure #[contents]

def ofFileLines (path : System.FilePath) : ReducerIO String :=
  ofArrayM do
    let contents ← IO.FS.readFile path
    pure (contents.splitOn "\n").toArray

def ofFileChars (path : System.FilePath) : ReducerIO Char :=
  ofArrayM do
    let contents ← IO.FS.readFile path
    pure contents.toList.toArray

def mapM (xs : ReducerM m α) (f : α → β) : ReducerM m β where
  run := fun cfg q =>
    xs.run cfg { unit := q.unit, combine := q.combine, step := fun a acc => q.step (f a) acc }

def flatMapM (xs : ReducerM m α) (f : α → Array β) : ReducerM m β where
  run := fun cfg q =>
    xs.run cfg {
      unit := q.unit
      combine := q.combine
      step := fun a acc => (f a).foldr q.step acc
    }

def filterM (xs : ReducerM m α) (p : α → Bool) : ReducerM m α where
  run := fun cfg q =>
    let q' := ({
      unit := q.unit
      combine := q.combine
      step := fun a acc => if p a then q.step a acc else acc
    } : FoldSpec α _)
    xs.run cfg q'

def foldWithConfigM (cfg : Config) (spec : MonoidSpec ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ := do
  let task ← xs.run cfg (FoldSpec.ofMonoid spec step)
  pure task.get

/--
Reduce with a proven monoid combiner and caller-provided local step. For
parallel-grouping-invariant results, the step should agree with the combiner:
`step a acc = spec.combine (step a spec.unit) acc`.
-/
def foldM (spec : MonoidSpec ρ) (step : α → ρ → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  foldWithConfigM Config.default spec step xs

def foldMapWithConfigM (cfg : Config) (spec : MonoidSpec ρ) (f : α → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  foldWithConfigM cfg spec (fun a acc => spec.combine (f a) acc) xs

def foldMapM (spec : MonoidSpec ρ) (f : α → ρ) [Monad m]
    (xs : ReducerM m α) : m ρ :=
  foldMapWithConfigM Config.default spec f xs

def groupByWithConfigM [BEq κ] (cfg : Config) (valueSpec : MonoidSpec ν)
    (key : α → κ) (step : α → ν → ν) [Monad m]
    (xs : ReducerM m α) : m (Array (κ × ν)) := do
  let task ← xs.run cfg {
    unit := #[]
    combine := Internal.mergeGroups valueSpec
    step := Internal.groupStep valueSpec key step
  }
  pure task.get

def groupByM [BEq κ] (valueSpec : MonoidSpec ν) (key : α → κ) (step : α → ν → ν)
    [Monad m] (xs : ReducerM m α) : m (Array (κ × ν)) :=
  groupByWithConfigM Config.default valueSpec key step xs

/--
Approximate fold for operations where the caller does not want to claim monoid
laws. This is intended for practical numeric reductions such as `Float`, where
parallel grouping can change the final rounded value.
-/
def foldApproxWithConfigM (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (step : α → ρ → ρ) [Monad m] (xs : ReducerM m α) : m ρ := do
  let task ← xs.run cfg { unit := unit, combine := combine, step := step }
  pure task.get

def foldApproxM (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerM m α) : m ρ :=
  foldApproxWithConfigM Config.default unit combine step xs

def sumM [Add α] [OfNat α 0] [LawfulAddMonoid α] [Monad m]
    (xs : ReducerM m α) : m α :=
  foldM (MonoidSpec.additive α) (fun a acc => a + acc) xs

/--
Floating-point sum is intentionally approximate: IEEE floating-point addition is
not a lawful monoid, so this terminal is separate from `.sum`.
-/
def sumFloatApproxM [Monad m] (xs : ReducerM m Float) : m Float :=
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

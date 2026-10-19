import Init.Data.Float
import Init.Data.Array.Lemmas
import Init.Data.String.Iterate
import Init.System.IO
import LeanReducers.Internal.Array
import LeanReducers.Internal.File
import LeanReducers.Internal.GroupBy
import LeanReducers.Seq
import LeanReducers.ParallelIO

namespace LeanReducers

/--
A lazy, fused parallel pipeline over input elements of type `α`.

The producer chooses the effect `m`: in-memory arrays use `Id`, while producers
such as file readers use `IO`. Transformations remain fused by rewriting the
terminal step instead of allocating intermediate collections.
-/
structure ReducerParM (m : Type → Type) (α : Type) where
  run : {ρ : Type} → Config → FoldSpec α ρ → m ρ

abbrev ReducerPar (α : Type) :=
  ReducerParM Id α

abbrev ReducerParIO (α : Type) :=
  ReducerParM IO α

namespace ReducerPar

/-- Reduce independently assigned byte ranges using the same seek, newline
repair and task tree as local files. Only the byte-source adapter changes. -/
def readSourceRanges (ranges : Array (ByteRange ByteSource))
    (trailingEmpty : Bool := true) : ReducerParIO String where
  run := fun cfg q => Internal.foldFileLineRangesIO cfg q ranges trailingEmpty

def readSources (sources : Array ByteSource) (trailingEmpty : Bool := true) : ReducerParIO String :=
  readSourceRanges (sources.map fun source => { source, start := 0, stop := source.size }) trailingEmpty

/-- Independent IO inputs, evaluated with a bounded number of local tasks.
Transformations and the terminal fold still run locally; all tasks are joined
before an IO exception can escape. The input array should be a bounded batch. -/
def ofArrayIO (values : Array σ) (read : σ → IO α) : ReducerParIO α where
  run := fun cfg q => do
    let results ← mapTasks (2 ^ cfg.maxDepth) values read
    return (Internal.foldArrayTask cfg q results).get

def ofArray (as : Array α) : ReducerPar α where
  run := fun cfg q => (Internal.foldArrayTask cfg q as).get

def ofArrayM [Monad m] (as : m (Array α)) : ReducerParM m α where
  run := fun cfg q => do
    let as ← as
    pure (Internal.foldArrayTask cfg q as).get

def readFile (path : System.FilePath) : ReducerParIO String :=
  ofArrayM do
    let contents ← IO.FS.readFile path
    pure #[contents]

def readLines (path : System.FilePath) : ReducerParIO String :=
  { run := fun cfg q => Internal.foldFileLinesIO cfg q path }

def readLinesFromFiles (paths : Array System.FilePath) : ReducerParIO String :=
  { run := fun cfg q => Internal.foldFilesLinesIO cfg q paths }

def readLinesFromFilesWithPath (paths : Array System.FilePath) :
    ReducerParIO (System.FilePath × String) :=
  { run := fun cfg q => Internal.foldFilesLinesWithPathIO cfg q paths }

def readChars (path : System.FilePath) : ReducerParIO Char :=
  ofArrayM do
    let contents ← IO.FS.readFile path
    pure contents.toSlice.chars.toArray

private def mapM (xs : ReducerParM m α) (f : α → β) : ReducerParM m β where
  run := fun cfg q =>
    xs.run cfg { unit := q.unit, combine := q.combine, step := fun a acc => q.step (f a) acc }

private def flatMapM (xs : ReducerParM m α) (f : α → ReducerSeq β) : ReducerParM m β where
  run := fun cfg q =>
    xs.run cfg {
      unit := q.unit
      combine := q.combine
      step := fun a acc => (f a).run acc q.step
    }

private def filterM (xs : ReducerParM m α) (p : α → Bool) : ReducerParM m α where
  run := fun cfg q =>
    let q' := ({
      unit := q.unit
      combine := q.combine
      step := fun a acc => if p a then q.step a acc else acc
    } : FoldSpec α _)
    xs.run cfg q'

private def reduceWithLawsWithConfigM (cfg : Config) (spec : MonoidSpec ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerParM m α) : m ρ := do
  xs.run cfg (FoldSpec.ofMonoid spec step)

/--
Reduce with a proven monoid combiner and caller-provided local step. For
parallel-grouping-invariant results, the step should agree with the combiner:
`step a acc = spec.combine (step a spec.unit) acc`.
-/
private def reduceWithLawsM (spec : MonoidSpec ρ) (step : α → ρ → ρ) [Monad m]
    (xs : ReducerParM m α) : m ρ :=
  reduceWithLawsWithConfigM Config.default spec step xs

private def reduceMapWithLawsWithConfigM (cfg : Config) (spec : MonoidSpec ρ) (f : α → ρ)
    [Monad m] (xs : ReducerParM m α) : m ρ :=
  reduceWithLawsWithConfigM cfg spec (fun a acc => spec.combine (f a) acc) xs

private def reduceMapWithLawsM (spec : MonoidSpec ρ) (f : α → ρ) [Monad m]
    (xs : ReducerParM m α) : m ρ :=
  reduceMapWithLawsWithConfigM Config.default spec f xs

private def groupByWithConfigM [BEq κ] [Hashable κ] (cfg : Config) (valueSpec : MonoidSpec ν)
    (key : α → κ) (step : α → ν → ν) [Monad m]
    (xs : ReducerParM m α) : m (Array (κ × ν)) := do
  let groups ← xs.run cfg {
    unit := Internal.emptyGroups
    combine := Internal.mergeGroups valueSpec
    step := Internal.groupStep valueSpec key step
  }
  pure (Internal.groupsToArray groups)

private def groupByM [BEq κ] [Hashable κ] (valueSpec : MonoidSpec ν) (key : α → κ)
    (step : α → ν → ν) [Monad m] (xs : ReducerParM m α) : m (Array (κ × ν)) :=
  groupByWithConfigM Config.default valueSpec key step xs

/--
Reduce without law proofs for operations where the caller does not want to provide
a `MonoidSpec`. The same parallel regrouping rules still apply; the library
just does not require proofs for the supplied combiner.
-/
private def reduceWithoutLawsWithConfigM (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (step : α → ρ → ρ) [Monad m] (xs : ReducerParM m α) : m ρ := do
  xs.run cfg { unit := unit, combine := combine, step := step }

private def reduceWithoutLawsM (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerParM m α) : m ρ :=
  reduceWithoutLawsWithConfigM Config.default unit combine step xs

private def sumM [Add α] [OfNat α 0] [LawfulAddMonoid α] [Monad m]
    (xs : ReducerParM m α) : m α :=
  reduceWithLawsM (MonoidSpec.additive α) (fun a acc => a + acc) xs

/--
Floating-point sum uses the reduce-without-laws path: IEEE floating-point addition is
not a lawful monoid, so this terminal is separate from `.sum`.
-/
private def sumFloatM [Monad m] (xs : ReducerParM m Float) : m Float :=
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

private def toArrayM [Monad m] (xs : ReducerParM m α) : m (Array α) := do
  let reversed ← reduceWithLawsM (reversedArraySpec α) (fun a acc => acc.push a) xs
  pure reversed.reverse

private def lengthM [Monad m] (xs : ReducerParM m α) : m Nat :=
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

private def minM [Min α] [Monad m] (xs : ReducerParM m α) : m (Option α) :=
  reduceWithoutLawsM (none : Option α) (minOption (α := α))
    (fun a acc => minOption (α := α) (some a) acc) xs

private def maxM [Max α] [Monad m] (xs : ReducerParM m α) : m (Option α) :=
  reduceWithoutLawsM (none : Option α) (maxOption (α := α))
    (fun a acc => maxOption (α := α) (some a) acc) xs

private structure FloatAverage where
  sum : Float
  count : Nat

private def avgFloatM [Monad m] (xs : ReducerParM m Float) : m (Option Float) := do
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

def map (xs : ReducerPar α) (f : α → β) : ReducerPar β :=
  mapM xs f

def flatMap (xs : ReducerPar α) (f : α → ReducerSeq β) : ReducerPar β :=
  flatMapM xs f

def filter (xs : ReducerPar α) (p : α → Bool) : ReducerPar α :=
  filterM xs p

/--
Parallel reduce with a proven monoid combiner (`MonoidSpec`) and a local step.
This is the lawful, default path; the unchecked variant is `reduceWithoutLaws`.
Tuning is optional via the trailing `cfg` (defaults to `Config.default`).
-/
def reduce (spec : MonoidSpec ρ) (step : α → ρ → ρ) (xs : ReducerPar α)
    (cfg : Config := {}) : ρ :=
  reduceWithLawsWithConfigM cfg spec step xs

/-- Parallel map-then-reduce with a proven monoid (`MonoidSpec`); `cfg` is optional. -/
def reduceMap (spec : MonoidSpec ρ) (f : α → ρ) (xs : ReducerPar α)
    (cfg : Config := {}) : ρ :=
  reduceMapWithLawsWithConfigM cfg spec f xs

/-- Group by `key`, combining per-key values with a proven monoid; `cfg` is optional. -/
def groupBy [BEq κ] [Hashable κ] (valueSpec : MonoidSpec ν) (key : α → κ)
    (step : α → ν → ν) (xs : ReducerPar α) (cfg : Config := {}) : Array (κ × ν) :=
  groupByWithConfigM cfg valueSpec key step xs

/--
Reduce without law proofs, for callers who cannot provide a `MonoidSpec`. The
same parallel regrouping rules still apply, so the supplied `combine` must be
associative with `unit` as identity for the result to be deterministic.
-/
def reduceWithoutLaws (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    (xs : ReducerPar α) (cfg : Config := {}) : ρ :=
  reduceWithoutLawsWithConfigM cfg unit combine step xs

def sum [Add α] [OfNat α 0] [LawfulAddMonoid α] (xs : ReducerPar α) : α :=
  sumM xs

def sumFloat (xs : ReducerPar Float) : Float :=
  sumFloatM xs

def toArray (xs : ReducerPar α) : Array α :=
  toArrayM xs

def length (xs : ReducerPar α) : Nat :=
  lengthM xs

def min? [Min α] (xs : ReducerPar α) : Option α :=
  minM xs

def min [Min α] (xs : ReducerPar α) (h : xs.min?.isSome) : α :=
  xs.min?.get h

def max? [Max α] (xs : ReducerPar α) : Option α :=
  maxM xs

def max [Max α] (xs : ReducerPar α) (h : xs.max?.isSome) : α :=
  xs.max?.get h

def avgFloat (xs : ReducerPar Float) : Option Float :=
  avgFloatM xs

def avg (xs : ReducerPar Float) : Option Float :=
  avgFloatM xs

end ReducerPar

namespace ReducerParM

def map (xs : ReducerParM m α) (f : α → β) : ReducerParM m β :=
  ReducerPar.mapM xs f

def flatMap (xs : ReducerParM m α) (f : α → ReducerSeq β) : ReducerParM m β :=
  ReducerPar.flatMapM xs f

def filter (xs : ReducerParM m α) (p : α → Bool) : ReducerParM m α :=
  ReducerPar.filterM xs p

/--
Parallel reduce with a proven monoid combiner (`MonoidSpec`) and a local step.
This is the lawful, default path; the unchecked variant is `reduceWithoutLaws`.
Tuning is optional via the trailing `cfg` (defaults to `Config.default`).
-/
def reduce (spec : MonoidSpec ρ) (step : α → ρ → ρ) [Monad m]
    (xs : ReducerParM m α) (cfg : Config := {}) : m ρ :=
  ReducerPar.reduceWithLawsWithConfigM cfg spec step xs

/-- Parallel map-then-reduce with a proven monoid (`MonoidSpec`); `cfg` is optional. -/
def reduceMap (spec : MonoidSpec ρ) (f : α → ρ) [Monad m]
    (xs : ReducerParM m α) (cfg : Config := {}) : m ρ :=
  ReducerPar.reduceMapWithLawsWithConfigM cfg spec f xs

/-- Group by `key`, combining per-key values with a proven monoid; `cfg` is optional. -/
def groupBy [BEq κ] [Hashable κ] (valueSpec : MonoidSpec ν) (key : α → κ)
    (step : α → ν → ν) [Monad m] (xs : ReducerParM m α) (cfg : Config := {}) : m (Array (κ × ν)) :=
  ReducerPar.groupByWithConfigM cfg valueSpec key step xs

/--
Reduce without law proofs, for callers who cannot provide a `MonoidSpec`. The
same parallel regrouping rules still apply, so the supplied `combine` must be
associative with `unit` as identity for the result to be deterministic.
-/
def reduceWithoutLaws (unit : ρ) (combine : ρ → ρ → ρ) (step : α → ρ → ρ)
    [Monad m] (xs : ReducerParM m α) (cfg : Config := {}) : m ρ :=
  ReducerPar.reduceWithoutLawsWithConfigM cfg unit combine step xs

def sum [Add α] [OfNat α 0] [LawfulAddMonoid α] [Monad m]
    (xs : ReducerParM m α) : m α :=
  ReducerPar.sumM xs

def sumFloat [Monad m] (xs : ReducerParM m Float) : m Float :=
  ReducerPar.sumFloatM xs

def toArray [Monad m] (xs : ReducerParM m α) : m (Array α) :=
  ReducerPar.toArrayM xs

def length [Monad m] (xs : ReducerParM m α) : m Nat :=
  ReducerPar.lengthM xs

def min? [Min α] [Monad m] (xs : ReducerParM m α) : m (Option α) :=
  ReducerPar.minM xs

def max? [Max α] [Monad m] (xs : ReducerParM m α) : m (Option α) :=
  ReducerPar.maxM xs

def avgFloat [Monad m] (xs : ReducerParM m Float) : m (Option Float) :=
  ReducerPar.avgFloatM xs

def avg [Monad m] (xs : ReducerParM m Float) : m (Option Float) :=
  ReducerPar.avgFloatM xs

end ReducerParM

namespace ReducerParIO

/-- Checked parsing stays fused and errors are selected in source order,
independently of task completion order. -/
def tryMap (xs : ReducerParIO α) (f : α → Except String β) : ReducerParIO β where
  run := fun cfg q => do
    let result ← xs.run cfg {
      unit := Except.ok q.unit
      combine := fun left right => do return q.combine (← left) (← right)
      step := fun a rest => do return q.step (← f a) (← rest) }
    IO.ofExcept result

end ReducerParIO

end LeanReducers

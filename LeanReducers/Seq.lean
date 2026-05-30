import Init.Data.Float
import Init.Data.String.Iterate
import Init.System.IO
import LeanReducers.Internal.GroupBy
import LeanReducers.Internal.Lines

namespace LeanReducers

/--
A lazy, fused sequential pipeline over input elements of type `α`.

Sequential reducers preserve the pipeline model without requiring parallel
configuration or algebraic laws from callers.
-/
structure ReducerSeqM (m : Type → Type) (α : Type) where
  run : {ρ : Type} → ρ → (α → ρ → ρ) → m ρ

abbrev ReducerSeq (α : Type) :=
  ReducerSeqM Id α

abbrev ReducerSeqIO (α : Type) :=
  ReducerSeqM IO α

namespace ReducerSeq

def empty : ReducerSeq α where
  run := fun unit _ => unit

def one (a : α) : ReducerSeq α where
  run := fun unit step => step a unit

def append (left right : ReducerSeq α) : ReducerSeq α where
  run := fun unit step => left.run (right.run unit step) step

def ofArray (as : Array α) : ReducerSeq α where
  run := fun unit step => as.foldr step unit

def ofList (as : List α) : ReducerSeq α where
  run := fun unit step => as.foldr step unit

def ofArrayM [Monad m] (as : m (Array α)) : ReducerSeqM m α where
  run := fun unit step => do
    let as ← as
    pure (as.foldr step unit)

def readFile (path : System.FilePath) : ReducerSeqIO String where
  run := fun unit step => do
    let contents ← IO.FS.readFile path
    pure (step contents unit)

private def reduceLinesFromFiles (paths : List System.FilePath) (unit : ρ)
    (step : String → ρ → ρ) : IO ρ := do
  match paths with
  | [] => pure unit
  | path :: rest =>
      let acc ← reduceLinesFromFiles rest unit step
      let contents ← IO.FS.readFile path
      pure (Internal.foldLinesRight contents acc step)

private def reduceLinesFromFilesWithPath (paths : List System.FilePath) (unit : ρ)
    (step : System.FilePath × String → ρ → ρ) : IO ρ := do
  match paths with
  | [] => pure unit
  | path :: rest =>
      let acc ← reduceLinesFromFilesWithPath rest unit step
      let contents ← IO.FS.readFile path
      pure (Internal.foldLinesRight contents acc (fun line acc => step (path, line) acc))

def readLines (path : System.FilePath) : ReducerSeqIO String where
  run := fun unit step => reduceLinesFromFiles [path] unit step

def readLinesFromFiles (paths : Array System.FilePath) : ReducerSeqIO String where
  run := fun unit step => reduceLinesFromFiles paths.toList unit step

def readLinesFromFilesWithPath (paths : Array System.FilePath) :
    ReducerSeqIO (System.FilePath × String) where
  run := fun unit step => reduceLinesFromFilesWithPath paths.toList unit step

def readChars (path : System.FilePath) : ReducerSeqIO Char where
  run := fun unit step => do
    let contents ← IO.FS.readFile path
    pure (contents.toSlice.foldr step unit)

private def mapM (xs : ReducerSeqM m α) (f : α → β) : ReducerSeqM m β where
  run := fun unit step =>
    xs.run unit (fun a acc => step (f a) acc)

private def flatMapM (xs : ReducerSeqM m α) (f : α → ReducerSeq β) : ReducerSeqM m β where
  run := fun unit step =>
    xs.run unit (fun a acc => (f a).run acc step)

private def filterM (xs : ReducerSeqM m α) (p : α → Bool) : ReducerSeqM m α where
  run := fun unit step =>
    xs.run unit (fun a acc => if p a then step a acc else acc)

private def reduceM (unit : ρ) (step : α → ρ → ρ) (xs : ReducerSeqM m α) : m ρ :=
  xs.run unit step

private def reduceMapM (unit : ρ) (combine : ρ → ρ → ρ) (f : α → ρ)
    (xs : ReducerSeqM m α) : m ρ :=
  reduceM unit (fun a acc => combine (f a) acc) xs

private def groupByM [BEq κ] [Hashable κ] (unit : ν) (key : α → κ)
    (step : α → ν → ν) [Monad m] (xs : ReducerSeqM m α) : m (Array (κ × ν)) := do
  let groups ← xs.run Internal.emptyGroups fun a groups =>
    let k := key a
    groups.insert k (step a (groups.getD k unit))
  pure (Internal.groupsToArray groups)

private def sumM [Add α] [OfNat α 0] (xs : ReducerSeqM m α) : m α :=
  reduceM 0 (fun a acc => a + acc) xs

private def sumFloatM (xs : ReducerSeqM m Float) : m Float :=
  reduceM 0.0 (fun a acc => a + acc) xs

private def toArrayM [Monad m] (xs : ReducerSeqM m α) : m (Array α) := do
  let reversed ← reduceM #[] (fun a acc => acc.push a) xs
  pure reversed.reverse

private def lengthM (xs : ReducerSeqM m α) : m Nat :=
  reduceM 0 (fun _ acc => acc + 1) xs

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

private def minM [Min α] (xs : ReducerSeqM m α) : m (Option α) :=
  reduceM none (fun a acc => minOption (some a) acc) xs

private def maxM [Max α] (xs : ReducerSeqM m α) : m (Option α) :=
  reduceM none (fun a acc => maxOption (some a) acc) xs

private structure FloatAverage where
  sum : Float
  count : Nat

private def avgFloatM [Monad m] (xs : ReducerSeqM m Float) : m (Option Float) := do
  let total ←
    reduceM ({ sum := 0.0, count := 0 } : FloatAverage)
      (fun a acc => { sum := a + acc.sum, count := acc.count + 1 })
      xs
  if total.count == 0 then
    pure none
  else
    pure (some (total.sum / Float.ofNat total.count))

def map (xs : ReducerSeq α) (f : α → β) : ReducerSeq β :=
  mapM xs f

def flatMap (xs : ReducerSeq α) (f : α → ReducerSeq β) : ReducerSeq β :=
  flatMapM xs f

def filter (xs : ReducerSeq α) (p : α → Bool) : ReducerSeq α :=
  filterM xs p

def reduce (unit : ρ) (step : α → ρ → ρ) (xs : ReducerSeq α) : ρ :=
  reduceM unit step xs

def reduceMap (unit : ρ) (combine : ρ → ρ → ρ) (f : α → ρ) (xs : ReducerSeq α) : ρ :=
  reduceMapM unit combine f xs

def groupBy [BEq κ] [Hashable κ] (unit : ν) (key : α → κ)
    (step : α → ν → ν) (xs : ReducerSeq α) : Array (κ × ν) :=
  groupByM unit key step xs

def sum [Add α] [OfNat α 0] (xs : ReducerSeq α) : α :=
  sumM xs

def sumFloat (xs : ReducerSeq Float) : Float :=
  sumFloatM xs

def toArray (xs : ReducerSeq α) : Array α :=
  toArrayM xs

def length (xs : ReducerSeq α) : Nat :=
  lengthM xs

def min? [Min α] (xs : ReducerSeq α) : Option α :=
  minM xs

def min [Min α] (xs : ReducerSeq α) (h : xs.min?.isSome) : α :=
  xs.min?.get h

def max? [Max α] (xs : ReducerSeq α) : Option α :=
  maxM xs

def max [Max α] (xs : ReducerSeq α) (h : xs.max?.isSome) : α :=
  xs.max?.get h

def avgFloat (xs : ReducerSeq Float) : Option Float :=
  avgFloatM xs

def avg (xs : ReducerSeq Float) : Option Float :=
  avgFloatM xs

end ReducerSeq

namespace ReducerSeqM

def map (xs : ReducerSeqM m α) (f : α → β) : ReducerSeqM m β :=
  ReducerSeq.mapM xs f

def flatMap (xs : ReducerSeqM m α) (f : α → ReducerSeq β) : ReducerSeqM m β :=
  ReducerSeq.flatMapM xs f

def filter (xs : ReducerSeqM m α) (p : α → Bool) : ReducerSeqM m α :=
  ReducerSeq.filterM xs p

def reduce (unit : ρ) (step : α → ρ → ρ) (xs : ReducerSeqM m α) : m ρ :=
  ReducerSeq.reduceM unit step xs

def reduceMap (unit : ρ) (combine : ρ → ρ → ρ) (f : α → ρ)
    (xs : ReducerSeqM m α) : m ρ :=
  ReducerSeq.reduceMapM unit combine f xs

def groupBy [BEq κ] [Hashable κ] (unit : ν) (key : α → κ)
    (step : α → ν → ν) [Monad m] (xs : ReducerSeqM m α) : m (Array (κ × ν)) :=
  ReducerSeq.groupByM unit key step xs

def sum [Add α] [OfNat α 0] (xs : ReducerSeqM m α) : m α :=
  ReducerSeq.sumM xs

def sumFloat (xs : ReducerSeqM m Float) : m Float :=
  ReducerSeq.sumFloatM xs

def toArray [Monad m] (xs : ReducerSeqM m α) : m (Array α) :=
  ReducerSeq.toArrayM xs

def length (xs : ReducerSeqM m α) : m Nat :=
  ReducerSeq.lengthM xs

def min? [Min α] (xs : ReducerSeqM m α) : m (Option α) :=
  ReducerSeq.minM xs

def max? [Max α] (xs : ReducerSeqM m α) : m (Option α) :=
  ReducerSeq.maxM xs

def avgFloat [Monad m] (xs : ReducerSeqM m Float) : m (Option Float) :=
  ReducerSeq.avgFloatM xs

def avg [Monad m] (xs : ReducerSeqM m Float) : m (Option Float) :=
  ReducerSeq.avgFloatM xs

end ReducerSeqM

end LeanReducers

# LeanReducers

Parallel, fused reducers for Lean 4.

`LeanReducers` is a small library for reducing data in parallel with Lean's
`Task`. The core design is law-aware: terminal reductions are based on a
`MonoidSpec`, so the combiner and unit carry the laws needed for safe chunk
combination.

## Quick Start

```lean
import LeanReducers

open LeanReducers

#eval
  #[(1 : Nat), 2, 3, 4]
    |> Reducer.ofArray
    |>.map (fun x => x + 1)
    |>.filter (fun x => x % 2 == 0)
    |>.sum
-- 6
```

Build and run the test executable:

```sh
lake build
lake exe lean_reducers_tests
```

The test executable uses Plausible to generate arrays, file contents, and
parallel configurations. Each test compares a reducer pipeline against a
sequential Lean model of the same producer, transforms, and terminal.

### Native Backend And Interpreted Runs

Line-oriented file producers use a small native `pread` bridge in compiled
code. The normal path is to run through a Lake executable, as above.

If you run a file through Lean's interpreter, load the generated dynamic
libraries explicitly:

```sh
lake build LeanReducers:shared
lake env lean \
  --load-dynlib .lake/build/lib/libleanreducersio.dylib \
  --load-dynlib .lake/build/lib/liblean__reducers_LeanReducers.dylib \
  --run Test.lean
```

On Linux, use the generated `.so` files instead of `.dylib`.

## Pipeline Model

Reducers are built as a three-stage pipeline:

```lean
producer |> intermediate |> intermediate |> terminal
```

- A producer creates the reducer and chooses the effect: `Reducer.ofArray`
  creates a pure `Reducer α`, while `Reducer.readLines` creates a
  `ReducerIO String`. Multi-file producers such as
  `Reducer.readLinesFromFiles` keep the same pipeline shape while adding
  parallelism across files.
- Intermediate operations such as `map`, `filter`, and `flatMap` transform the
  reducer without running it. They are fused into the terminal fold plan instead
  of allocating intermediate collections.
- A terminal operation such as `foldWithLaws`, `foldMapWithLaws`, `foldWithoutLaws`, `toArray`,
  `length`, `sum`, `sumFloat`, `min?`, `max?`, `avgFloat`, or `groupBy` runs
  the reduction. Pure reducers return a value directly; effectful reducers
  return through their producer monad.

For example:

```lean
#[(1 : Nat), 2, 3, 4] -- source data
  |> Reducer.ofArray  -- producer
  |>.map (fun x => x + 1) -- intermediate
  |>.filter (fun x => x % 2 == 0) -- intermediate
  |>.sum -- terminal
```

## Core Types

```lean
structure MonoidSpec (α : Type) where
  unit : α
  combine : α → α → α
  assoc : ∀ a b c, combine (combine a b) c = combine a (combine b c)
  left_unit : ∀ a, combine unit a = a
  right_unit : ∀ a, combine a unit = a

structure ReducerM (m : Type → Type) (α : Type)

abbrev Reducer (α : Type) := ReducerM Id α
abbrev ReducerIO (α : Type) := ReducerM IO α
```

`Reducer α` is for pure producers. `ReducerIO α` is for producers that must
perform `IO`, such as reading a file.

Internally, producers run the terminal fold plan. Array producers use a pure
`Task` tree. Line-oriented file producers use parallel IO tasks that read byte
ranges and repair newline boundaries before folding lines.

## API Overview

Producers:

```lean
Reducer.ofArray     : Array α → Reducer α
Reducer.ofArrayM    : [Monad m] → m (Array α) → ReducerM m α
Reducer.readFile    : System.FilePath → ReducerIO String
Reducer.readLines   : System.FilePath → ReducerIO String
Reducer.readLinesFromFiles : Array System.FilePath → ReducerIO String
Reducer.readLinesFromFilesWithPath :
  Array System.FilePath → ReducerIO (System.FilePath × String)
Reducer.readChars   : System.FilePath → ReducerIO Char
```

Transforms:

```lean
.map     : ReducerM m α → (α → β) → ReducerM m β
.filter  : ReducerM m α → (α → Bool) → ReducerM m α
.flatMap : ReducerM m α → (α → Array β) → ReducerM m β
```

Terminals:

```lean
.foldWithLaws    : MonoidSpec ρ → (α → ρ → ρ) → ReducerM m α → m ρ
.foldMapWithLaws : MonoidSpec ρ → (α → ρ) → ReducerM m α → m ρ
.foldWithoutLaws : ρ → (ρ → ρ → ρ) → (α → ρ → ρ) → ReducerM m α → m ρ
.toArray         : ReducerM m α → m (Array α)
.length         : ReducerM m α → m Nat
.sum             : ReducerM m α → m α
.sumFloat        : ReducerM m Float → m Float
.min?            : [Min α] → ReducerM m α → m (Option α)
.max?            : [Max α] → ReducerM m α → m (Option α)
.avgFloat        : ReducerM m Float → m (Option Float)
.avg             : ReducerM m Float → m (Option Float)
```

For pure `Reducer α`, `m` is `Id`, so terminals return the value directly.
For `ReducerIO α`, terminals return `IO`.
`min?`, `max?`, and floating averages return `none` for empty reducers.
Pure reducers also expose total proof-bearing extrema:

```lean
.min : [Min α] → (xs : Reducer α) → xs.min?.isSome → α
.max : [Max α] → (xs : Reducer α) → xs.max?.isSome → α
```

Grouping:

```lean
.groupBy :
  [BEq κ] →
  [Hashable κ] →
  MonoidSpec ν →
  (α → κ) →
  (α → ν → ν) →
  ReducerM m α →
  m (Array (κ × ν))
```

The grouped value starts at the value monoid's `unit`, then the per-key step is
applied for each element in the group. Group output order is unspecified. For
pure reducers, `m` is `Id`.

## Examples

### `flatMap`

```lean
#eval
  #[1, 2, 3]
    |> Reducer.ofArray
    |>.flatMap (fun x => #[x, x * 10])
    |>.sum
-- 66
```

### Convenience Terminals

```lean
#eval
  #[3, 1, 4, 1, 5]
    |> Reducer.ofArray
    |>.min?
-- some 1

#eval
  match (#[3.0, 1.0, 4.0] |> Reducer.ofArray |>.avgFloat) with
  | some avg => avg > 2.0 && avg < 3.0
  | none => false
-- true
```

### `groupBy`

```lean
#eval
  #[("a", 1), ("b", 2), ("a", 3)]
    |> Reducer.ofArray
    |>.groupBy
      (MonoidSpec.additive Nat)
      (fun row => row.1)
      (fun row acc => row.2 + acc)
    |>.qsort (fun left right => compare left.1 right.1 == Ordering.lt)
-- #[("a", 4), ("b", 2)]
```

### File Producers

`Reducer.readLines` is the large-file path: it splits the file into byte ranges,
reads those ranges in parallel, then adjusts each range to whole-line boundaries
so every line is folded exactly once.

`Reducer.readLinesFromFiles` and `Reducer.readLinesFromFilesWithPath` use the
same source byte-range scheduler as `Reducer.readLines`, so skewed file sizes can
be balanced by splitting large files into multiple ranges.

Because these producers use the native backend in compiled code, interpreted
`lean --run` sessions need the dynamic libraries described above.

```lean
def countLinesByLength (path : System.FilePath) : IO (Array (Nat × Nat)) := do
  Reducer.readLines path
    |>.filter (fun line => line != "")
    |>.groupBy
      (MonoidSpec.additive Nat)
      String.length
      (fun _ acc => 1 + acc)
```

Use `readLinesFromFilesWithPath` when the terminal needs to know which file
produced each line:

```lean
def countNonemptyLinesByFile
    (paths : Array System.FilePath) : IO (Array (System.FilePath × Nat)) := do
  Reducer.readLinesFromFilesWithPath paths
    |>.filter (fun row => row.2 != "")
    |>.groupBy
      (MonoidSpec.additive Nat)
      (fun row => row.1)
      (fun _ acc => 1 + acc)
```

## Lawfulness

Parallel reduction can regroup chunk results. That is why lawful reductions use
`MonoidSpec`: the result combiner must be associative and must have a lawful
unit.

Use `foldWithoutLaws` when you have a useful `unit` and `combine` but do not want
to provide monoid proofs. The fold still runs in parallel, so the supplied
combiner should be stable under regrouping if you need deterministic equality
with a sequential fold.

`Float` is intentionally not a lawful `.sum` target. IEEE floating-point
addition is not mathematically associative, so the library exposes:

```lean
sumFloat : Reducer Float → Float
avgFloat : Reducer Float → Option Float
```

and the monadic equivalents for practical floating-point reductions over the
without-laws fold path.

Likewise, `min?` and `max?` use the `Min` and `Max` classes. For
parallel-stable results, those operations should behave consistently under
regrouping.

## Configuration

```lean
structure Config where
  grain : Nat := 2048
  maxDepth : Nat := 4
  priority : Task.Priority := Task.Priority.default
```

Use `foldWithLawsWithConfig`, `foldMapWithLawsWithConfig`, `foldWithoutLawsWithConfig`, or
`groupByWithConfig` to tune parallel splitting. For line readers, `grain` is
interpreted as a target byte chunk size before newline-boundary repair.

## Design Notes

- Array producers use index-based chunking. Line readers use a small native
  `pread` bridge for true parallel range reads.
- Line producers schedule over source byte ranges. Single-file reads start from
  one range, while multi-file reads start from one range per file and may split a
  large file into multiple ranges.
- File line chunks are expanded or trimmed at newline boundaries. A line that
  starts exactly at a split belongs to the right chunk, so boundary lines are not
  duplicated.
- `readFile` and `readChars` still read the whole file before reducing.
- `map`, `filter`, and `flatMap` are fused by rewriting the terminal fold plan;
  they do not build intermediate pipeline collections.
- `groupBy` uses a `Std.HashMap` accumulator internally and returns an
  `Array (key × value)` at the API boundary.

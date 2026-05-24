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
  reducer without running it. They are fused into the terminal fold instead of
  allocating intermediate collections.
- A terminal operation such as `fold`, `foldMap`, `sum`, `sumFloatApprox`, or
  `groupBy` runs the reduction. Pure reducers return a value directly;
  effectful reducers return through their producer monad.

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
.fold    : MonoidSpec ρ → (α → ρ → ρ) → ReducerM m α → m ρ
.foldMap : MonoidSpec ρ → (α → ρ) → ReducerM m α → m ρ
.sum     : ReducerM m α → m α
```

For pure `Reducer α`, `m` is `Id`, so terminals return the value directly.
For `ReducerIO α`, terminals return `IO`.

Grouping:

```lean
.groupBy :
  [BEq κ] →
  MonoidSpec ν →
  (α → κ) →
  (α → ν → ν) →
  ReducerM m α →
  m (Array (κ × ν))
```

The grouped value starts at the value monoid's `unit`, then the per-key step is
applied for each element in the group. For pure reducers, `m` is `Id`.

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

### `groupBy`

```lean
#eval
  #[("a", 1), ("b", 2), ("a", 3)]
    |> Reducer.ofArray
    |>.groupBy
      (MonoidSpec.additive Nat)
      (fun row => row.1)
      (fun row acc => row.2 + acc)
-- #[("a", 4), ("b", 2)]
```

### File Producers

`Reducer.readLines` is the large-file path: it splits the file into byte ranges,
reads those ranges in parallel, then adjusts each range to whole-line boundaries
so every line is folded exactly once.

`Reducer.readLinesFromFiles` and `Reducer.readLinesFromFilesWithPath` add a
second level of parallelism across an array of files.

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

`Float` is intentionally not a lawful `.sum` target. IEEE floating-point
addition is not mathematically associative, so the library exposes:

```lean
sumFloatApprox : Reducer Float → Float
```

and the monadic equivalent for practical approximate floating-point reductions.

## Configuration

```lean
structure Config where
  grain : Nat := 2048
  maxDepth : Nat := 4
  priority : Task.Priority := Task.Priority.default
```

Use `foldWithConfig`, `foldMapWithConfig`, or `groupByWithConfig` to tune
parallel splitting. For line readers, `grain` is interpreted as a target byte
chunk size before newline-boundary repair.

## Design Notes

- Array producers use index-based chunking. Line readers use a small native
  `pread` bridge for true parallel range reads.
- Multi-file line producers split the file array in parallel, then each file
  uses the same byte-range line reader. Results are combined in input file order.
- File line chunks are expanded or trimmed at newline boundaries. A line that
  starts exactly at a split belongs to the right chunk, so boundary lines are not
  duplicated.
- `readFile` and `readChars` still read the whole file before reducing.
- `map`, `filter`, and `flatMap` are fused by rewriting the terminal fold plan;
  they do not build intermediate pipeline collections.
- `groupBy` currently uses an `Array (key × value)` accumulator with linear key
  lookup. This keeps v1 simple and dependency-free.

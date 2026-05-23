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

## Core Types

```lean
structure MonoidSpec (α : Type) where
  unit : α
  combine : α → α → α
  assoc : ∀ a b c, combine (combine a b) c = combine a (combine b c)
  left_unit : ∀ a, combine unit a = a
  right_unit : ∀ a, combine a unit = a

structure FoldSpec (α : Type) (ρ : Type) where
  unit : ρ
  combine : ρ → ρ → ρ
  step : α → ρ → ρ

structure ReducerM (m : Type → Type) (α : Type)

abbrev Reducer (α : Type) := ReducerM Id α
abbrev ReducerIO (α : Type) := ReducerM IO α
```

`Reducer α` is for pure producers. `ReducerIO α` is for producers that must
perform `IO`, such as reading a file.

Internally, producers create a `Task`, and terminal operations bind the producer
effect and call `.get` on the task.

## API Overview

Producers:

```lean
Reducer.ofArray     : Array α → Reducer α
Reducer.ofArrayM    : [Monad m] → m (Array α) → ReducerM m α
Reducer.ofFile      : System.FilePath → ReducerIO String
Reducer.ofFileLines : System.FilePath → ReducerIO String
Reducer.ofFileChars : System.FilePath → ReducerIO Char
```

Transforms:

```lean
Reducer.map      : Reducer α → (α → β) → Reducer β
Reducer.filter   : Reducer α → (α → Bool) → Reducer α
Reducer.flatMap  : Reducer α → (α → Array β) → Reducer β

ReducerM.map     : ReducerM m α → (α → β) → ReducerM m β
ReducerM.filter  : ReducerM m α → (α → Bool) → ReducerM m α
ReducerM.flatMap : ReducerM m α → (α → Array β) → ReducerM m β
```

Terminals:

```lean
fold    : MonoidSpec ρ → (α → ρ → ρ) → Reducer α → ρ
foldMap : MonoidSpec ρ → (α → ρ) → Reducer α → ρ
sum     : Reducer α → α
```

Effectful terminals return through the producer's monad:

```lean
ReducerM.fold    : [Monad m] → MonoidSpec ρ → (α → ρ → ρ) → ReducerM m α → m ρ
ReducerM.foldMap : [Monad m] → MonoidSpec ρ → (α → ρ) → ReducerM m α → m ρ
ReducerM.sum     : [Monad m] → ReducerM m α → m α
```

Grouping:

```lean
groupBy :
  [BEq κ] →
  MonoidSpec ν →
  (α → κ) →
  (α → ν → ν) →
  Reducer α →
  Array (κ × ν)
```

The grouped value starts at the value monoid's `unit`, then the per-key step is
applied for each element in the group.

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

```lean
def countLinesByLength (path : System.FilePath) : IO (Array (Nat × Nat)) := do
  Reducer.ofFileLines path
    |>.filter (fun line => line != "")
    |>.groupBy
      (MonoidSpec.additive Nat)
      String.length
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
parallel splitting.

## Design Notes

- Only `Array` producers are provided for now. Parallel chunking is index-based,
  and `Array` gives predictable splitting.
- `map`, `filter`, and `flatMap` are fused by rewriting the terminal `FoldSpec`;
  they do not build intermediate pipeline collections.
- `groupBy` currently uses an `Array (key × value)` accumulator with linear key
  lookup. This keeps v1 simple and dependency-free.

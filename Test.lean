import LeanReducers

open LeanReducers

def assertEq {α : Type} [BEq α] [ToString α] (name : String) (expected actual : α) :
    IO Unit := do
  if actual == expected then
    pure ()
  else
    throw <| IO.userError
      s!"{name}: expected {expected}, got {actual}"

def assertBool (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw <| IO.userError s!"{name}: assertion failed"

def natMulSpec : MonoidSpec Nat where
  unit := 1
  combine := (· * ·)
  assoc := Nat.mul_assoc
  left_unit := Nat.one_mul
  right_unit := Nat.mul_one

def main : IO Unit := do
  let mappedFiltered : Nat :=
    #[(1 : Nat), 2, 3, 4]
      |> Reducer.ofArray
      |>.map (fun x => x + 1)
      |>.filter (fun x => x % 2 == 0)
      |>.sum
  assertEq "map/filter Nat sum" 6 mappedFiltered

  let intTotal : Int :=
    #[(-5 : Int), 10, -3, 8]
      |> Reducer.ofArray
      |>.sum
  assertEq "Int sum" 10 intTotal

  let emptyTotal : Nat :=
    (#[] : Array Nat)
      |> Reducer.ofArray
      |>.sum
  assertEq "empty Nat sum" 0 emptyTotal

  let singletonTotal : Nat :=
    #[(42 : Nat)]
      |> Reducer.ofArray
      |>.sum
  assertEq "singleton Nat sum" 42 singletonTotal

  let largerTotal : Nat :=
    Array.range 1000
      |> Reducer.ofArray
      |>.sum
  assertEq "larger Nat sum" 499500 largerTotal

  let parallelCfg : Config := {
    grain := 1
    maxDepth := 8
    priority := Task.Priority.default
  }
  let forcedParallel : Nat :=
    Array.range 128
      |> Reducer.ofArray
      |> Reducer.foldWithConfig parallelCfg (MonoidSpec.additive Nat) (fun a acc => a + acc)
  assertEq "forced parallel Nat sum" 8128 forcedParallel

  let customProduct : Nat :=
    #[2, 3, 4]
      |> Reducer.ofArray
      |> Reducer.fold natMulSpec (fun a acc => a * acc)
  assertEq "custom fold product" 24 customProduct

  let foldMapped : Nat :=
    #[1, 2, 3, 4]
      |> Reducer.ofArray
      |> Reducer.foldMap natMulSpec (fun x => x + 1)
  assertEq "foldMap product" 120 foldMapped

  let flatMapped : Nat :=
    #[1, 2, 3]
      |> Reducer.ofArray
      |>.flatMap (fun x => #[x, x * 10])
      |>.sum
  assertEq "flatMap Nat sum" 66 flatMapped

  let grouped : Array (String × Nat) :=
    #[("a", 1), ("b", 2), ("a", 3), ("b", 4), ("c", 5)]
      |> Reducer.ofArray
      |>.groupBy (MonoidSpec.additive Nat) (fun row => row.1) (fun row acc => row.2 + acc)
  assertBool "groupBy String Nat sum" (grouped == #[("a", 4), ("b", 6), ("c", 5)])

  let groupedParallel : Array (Nat × Nat) :=
    #[(0, 1), (1, 2), (0, 3), (2, 4), (1, 5)]
      |> Reducer.ofArray
      |> Reducer.groupByWithConfig parallelCfg (MonoidSpec.additive Nat)
        (fun row => row.1) (fun row acc => row.2 + acc)
  assertBool "forced parallel groupBy Nat sum" (groupedParallel == #[(0, 4), (1, 7), (2, 4)])

  let floatTotal : Float :=
    #[1.0, 2.0, 3.0]
      |> Reducer.ofArray
      |>.sumFloatApprox
  assertEq "Float approximate sum" 6.0 floatTotal

  let path : System.FilePath := "/private/tmp/lean_reducers_test_input.txt"
  IO.FS.writeFile path "alpha\nbeta\ngamma\n"

  let fileLineChars ←
    Reducer.ofFileLines path
      |>.map String.length
      |>.sum
  assertEq "file line char sum" 14 fileLineChars

  let fileContentChars ←
    Reducer.ofFile path
      |>.foldMap (MonoidSpec.additive Nat) String.length
  assertEq "file content char count" 17 fileContentChars

  let fileChars ←
    Reducer.ofFileChars path
      |>.foldMap (MonoidSpec.additive Nat) (fun _ => 1)
  assertEq "file char count" 17 fileChars

  let fileFlatMapped ←
    Reducer.ofFileLines path
      |>.flatMap (fun line => #[line.length, line.length + 1])
      |>.sum
  assertEq "file flatMap line length sum" 32 fileFlatMapped

  let fileGrouped ←
    Reducer.ofFileLines path
      |>.filter (fun line => line != "")
      |>.groupBy (MonoidSpec.additive Nat) String.length (fun _ acc => 1 + acc)
  assertBool "file groupBy line length count" (fileGrouped == #[(5, 2), (4, 1)])

  IO.println "lean_reducers_tests: ok"

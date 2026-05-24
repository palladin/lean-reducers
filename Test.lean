import LeanReducers
import Plausible

open LeanReducers

namespace LeanReducersTests

def assertEq {α : Type} [BEq α] [Repr α] (name : String) (expected actual : α) :
    IO Unit := do
  if actual == expected then
    pure ()
  else
    throw <| IO.userError
      s!"{name}: expected {repr expected}, got {repr actual}"

def assertBool (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw <| IO.userError s!"{name}: assertion failed"

def plausibleCfg : Plausible.Configuration := {
  numInst := 300
  maxSize := 120
  numRetries := 20
  randomSeed := some 20260524
  quiet := true
}

def effectCases : Nat :=
  80

def fileCases : Nat :=
  80

def ok (name detail : String) : IO Unit :=
  IO.println s!"  ok {name} ({detail})"

def reportSection (name : String) : IO Unit :=
  IO.println s!"\n{name}"

def checkProp (name : String) (p : Prop) [Plausible.Testable p] : IO Unit := do
  match ← Plausible.Testable.checkIO p plausibleCfg with
  | Plausible.TestResult.success _ =>
      ok name s!"{plausibleCfg.numInst} generated cases, maxSize={plausibleCfg.maxSize}, seed={plausibleCfg.randomSeed}"
  | Plausible.TestResult.gaveUp n =>
      throw <| IO.userError s!"{name}: gave up after {n} discarded examples"
  | Plausible.TestResult.failure _ counters shrinks =>
      throw <| IO.userError
        s!"{name}: counter-example after {shrinks} shrinks\n{String.intercalate "\n" counters}"

def cfgOf (grainSeed depthSeed : Nat) : Config := {
  grain := grainSeed % 64 + 1
  maxDepth := depthSeed % 10
  priority := Task.Priority.default
}

def smallNats (xs : Array Nat) : Array Nat :=
  xs.map (fun x => x % 200)

def smallInts (xs : Array Nat) : Array Int :=
  xs.map (fun x => Int.ofNat (x % 401) - 200)

def smallFloats (xs : Array Nat) : Array Float :=
  xs.map (fun x => Float.ofNat (x % 1024))

def mapNat (x : Nat) : Nat :=
  x % 97 + 1

def keepNat (x : Nat) : Bool :=
  x % 3 != 1

def expandNat (x : Nat) : Array Nat :=
  #[x, x * 2 + 1, x % 5]

def arrayFlatMap (xs : Array α) (f : α → Array β) : Array β :=
  xs.foldl (fun acc x => acc ++ f x) #[]

def seqPipelineNat (raw : Array Nat) : Array Nat :=
  smallNats raw
    |>.map mapNat
    |>.filter keepNat
    |> fun xs => arrayFlatMap xs expandNat

def seqNatSum (xs : Array Nat) : Nat :=
  xs.foldl (fun acc x => acc + x) 0

def seqIntSum (xs : Array Int) : Int :=
  xs.foldl (fun acc x => acc + x) 0

def seqFloatSum (xs : Array Float) : Float :=
  xs.foldl (fun acc x => acc + x) 0.0

def collectReducerWithConfig (cfg : Config) (xs : Reducer α) : List α :=
  Reducer.foldApproxWithConfig cfg ([] : List α)
    (fun left right => left ++ right)
    (fun x acc => x :: acc)
    xs

def collectReducer (xs : Reducer α) : List α :=
  Reducer.foldApprox ([] : List α)
    (fun left right => left ++ right)
    (fun x acc => x :: acc)
    xs

def collectReducerIOWithConfig (cfg : Config) (xs : ReducerIO α) : IO (List α) :=
  ReducerM.foldApproxWithConfig cfg ([] : List α)
    (fun left right => left ++ right)
    (fun x acc => x :: acc)
    xs

def collectReducerIO (xs : ReducerIO α) : IO (List α) :=
  ReducerM.foldApprox ([] : List α)
    (fun left right => left ++ right)
    (fun x acc => x :: acc)
    xs

def groupTotals (groups : Array (Nat × Nat)) : List Nat :=
  (List.range 7).map fun k =>
    groups.foldl (fun acc row => if row.1 == k then row.2 else acc) 0

def seqGroupTotals (xs : Array Nat) : List Nat :=
  (List.range 7).map fun k =>
    xs.foldl (fun acc x => if x % 7 == k then acc + (x + 1) else acc) 0

def seqLineCountGroups (lines : List String) : List Nat :=
  (List.range 7).map fun k =>
    lines.foldl (fun acc line => if line.length % 7 == k then acc + 1 else acc) 0

abbrev pureArrayConfigProperty (f : Array Nat → Nat → Nat → Bool) : Prop :=
  Plausible.NamedBinder "xs" <| ∀ xs : Array Nat,
  Plausible.NamedBinder "grain" <| ∀ grain : Nat,
  Plausible.NamedBinder "depth" <| ∀ depth : Nat,
    f xs grain depth = true

abbrev pureArrayProperty (f : Array Nat → Bool) : Prop :=
  Plausible.NamedBinder "xs" <| ∀ xs : Array Nat,
    f xs = true

def propMapFilterFlatMapMatchesSeq (raw : Array Nat) (grain depth : Nat) : Bool :=
  let cfg := cfgOf grain depth
  let actual :=
    smallNats raw
      |> Reducer.ofArray
      |>.map mapNat
      |>.filter keepNat
      |>.flatMap expandNat
      |> collectReducerWithConfig cfg
  actual == (seqPipelineNat raw).toList

def propFoldWithConfigMatchesSeq (raw : Array Nat) (grain depth : Nat) : Bool :=
  let cfg := cfgOf grain depth
  let data := smallNats raw
  let actual :=
    data
      |> Reducer.ofArray
      |> Reducer.foldWithConfig cfg (MonoidSpec.additive Nat) (fun x acc => x + acc)
  actual == seqNatSum data

def propFoldMatchesSeq (raw : Array Nat) : Bool :=
  let data := smallNats raw
  let actual :=
    data
      |> Reducer.ofArray
      |> Reducer.fold (MonoidSpec.additive Nat) (fun x acc => x + acc)
  actual == seqNatSum data

def propFoldMapWithConfigMatchesSeq (raw : Array Nat) (grain depth : Nat) : Bool :=
  let cfg := cfgOf grain depth
  let data := smallNats raw
  let f := fun x => x * 3 + 1
  let actual :=
    data
      |> Reducer.ofArray
      |> Reducer.foldMapWithConfig cfg (MonoidSpec.additive Nat) f
  let expected := data.foldl (fun acc x => acc + f x) 0
  actual == expected

def propFoldMapMatchesSeq (raw : Array Nat) : Bool :=
  let data := smallNats raw
  let f := fun x => x * 3 + 1
  let actual :=
    data
      |> Reducer.ofArray
      |> Reducer.foldMap (MonoidSpec.additive Nat) f
  let expected := data.foldl (fun acc x => acc + f x) 0
  actual == expected

def propGroupByWithConfigMatchesSeq (raw : Array Nat) (grain depth : Nat) : Bool :=
  let cfg := cfgOf grain depth
  let data := smallNats raw
  let actual :=
    data
      |> Reducer.ofArray
      |> Reducer.groupByWithConfig cfg (MonoidSpec.additive Nat)
        (fun x => x % 7)
        (fun x acc => x + 1 + acc)
      |> groupTotals
  actual == seqGroupTotals data

def propGroupByMatchesSeq (raw : Array Nat) : Bool :=
  let data := smallNats raw
  let actual :=
    data
      |> Reducer.ofArray
      |>.groupBy (MonoidSpec.additive Nat)
        (fun x => x % 7)
        (fun x acc => x + 1 + acc)
      |> groupTotals
  actual == seqGroupTotals data

def propFoldApproxMatchesSeq (raw : Array Nat) : Bool :=
  let data := smallNats raw
  collectReducer (Reducer.ofArray data) == data.toList

def propSumNatMatchesSeq (raw : Array Nat) : Bool :=
  let data := smallNats raw
  (Reducer.ofArray data).sum == seqNatSum data

def propSumIntMatchesSeq (raw : Array Nat) : Bool :=
  let data := smallInts raw
  (Reducer.ofArray data).sum == seqIntSum data

def propSumFloatApproxMatchesSeq (raw : Array Nat) : Bool :=
  let data := smallFloats raw
  (Reducer.ofArray data).sumFloatApprox == seqFloatSum data

def propOfArrayMIdMatchesSeq (raw : Array Nat) (grain depth : Nat) : Bool :=
  let cfg := cfgOf grain depth
  let data := smallNats raw
  let reducer : Reducer Nat := Reducer.ofArrayM (m := Id) data
  collectReducerWithConfig cfg reducer == data.toList

def runPureArrayProperties : IO Unit := do
  reportSection "Pure Reducer properties"
  checkProp "ofArray/map/filter/flatMap/foldApproxWithConfig"
    (pureArrayConfigProperty propMapFilterFlatMapMatchesSeq)
  checkProp "foldWithConfig"
    (pureArrayConfigProperty propFoldWithConfigMatchesSeq)
  checkProp "fold"
    (pureArrayProperty propFoldMatchesSeq)
  checkProp "foldMapWithConfig"
    (pureArrayConfigProperty propFoldMapWithConfigMatchesSeq)
  checkProp "foldMap"
    (pureArrayProperty propFoldMapMatchesSeq)
  checkProp "groupByWithConfig"
    (pureArrayConfigProperty propGroupByWithConfigMatchesSeq)
  checkProp "groupBy"
    (pureArrayProperty propGroupByMatchesSeq)
  checkProp "foldApprox"
    (pureArrayProperty propFoldApproxMatchesSeq)
  checkProp "sum Nat"
    (pureArrayProperty propSumNatMatchesSeq)
  checkProp "sum Int"
    (pureArrayProperty propSumIntMatchesSeq)
  checkProp "sumFloatApprox"
    (pureArrayProperty propSumFloatApproxMatchesSeq)
  checkProp "ofArrayM Id"
    (pureArrayConfigProperty propOfArrayMIdMatchesSeq)

def sample (α : Type) [Plausible.Arbitrary α] (size : Nat) : IO α :=
  Plausible.Gen.run (Plausible.Arbitrary.arbitrary : Plausible.Gen α) size

abbrev EffectCase :=
  Array Nat × Nat × Nat

def checkEffectCase (idx : Nat) (raw : EffectCase) : IO Unit := do
  let (xs, grain, depth) := raw
  let cfg := cfgOf grain depth
  let data := smallNats xs
  let label := s!"effect case {idx}"

  let source : ReducerIO Nat := Reducer.ofArrayM (m := IO) (pure data)
  let actualPipeline ←
    source
      |>.map mapNat
      |>.filter keepNat
      |>.flatMap expandNat
      |>.foldApproxWithConfig cfg ([] : List Nat)
        (fun left right => left ++ right)
        (fun x acc => x :: acc)
  assertEq s!"{label}: ReducerM map/filter/flatMap/foldApproxWithConfig"
    (seqPipelineNat xs).toList actualPipeline

  let actualFold ←
    source
      |>.foldWithConfig cfg (MonoidSpec.additive Nat) (fun x acc => x + acc)
  assertEq s!"{label}: ReducerM foldWithConfig" (seqNatSum data) actualFold

  let actualFoldDefault ←
    source
      |>.fold (MonoidSpec.additive Nat) (fun x acc => x + acc)
  assertEq s!"{label}: ReducerM fold" (seqNatSum data) actualFoldDefault

  let f := fun x => x * 3 + 1
  let expectedFoldMap := data.foldl (fun acc x => acc + f x) 0
  let actualFoldMapWithConfig ←
    source
      |>.foldMapWithConfig cfg (MonoidSpec.additive Nat) f
  assertEq s!"{label}: ReducerM foldMapWithConfig" expectedFoldMap actualFoldMapWithConfig

  let actualFoldMap ←
    source
      |>.foldMap (MonoidSpec.additive Nat) f
  assertEq s!"{label}: ReducerM foldMap" expectedFoldMap actualFoldMap

  let actualGroupByWithConfig ←
    source
      |>.groupByWithConfig cfg (MonoidSpec.additive Nat)
        (fun x => x % 7)
        (fun x acc => x + 1 + acc)
  assertEq s!"{label}: ReducerM groupByWithConfig"
    (seqGroupTotals data) (groupTotals actualGroupByWithConfig)

  let actualGroupBy ←
    source
      |>.groupBy (MonoidSpec.additive Nat)
        (fun x => x % 7)
        (fun x acc => x + 1 + acc)
  assertEq s!"{label}: ReducerM groupBy"
    (seqGroupTotals data) (groupTotals actualGroupBy)

  let actualApprox ← collectReducerIO source
  assertEq s!"{label}: ReducerM foldApprox" data.toList actualApprox

  let actualSum ← source.sum
  assertEq s!"{label}: ReducerM sum" (seqNatSum data) actualSum

  let floats := smallFloats xs
  let floatSource : ReducerIO Float := Reducer.ofArrayM (m := IO) (pure floats)
  let actualFloat ← floatSource.sumFloatApprox
  assertBool s!"{label}: ReducerM sumFloatApprox"
    (actualFloat == seqFloatSum floats)

def runEffectProperties : IO Unit := do
  reportSection "Effectful ReducerM properties"
  IO.println s!"  generated cases: {effectCases}"
  IO.println "  APIs: ofArrayM IO, map, filter, flatMap, fold*, foldMap*, groupBy*, foldApprox, sum, sumFloatApprox"
  for idx in List.range effectCases do
    let raw ← sample EffectCase (20 + idx % 80)
    checkEffectCase idx raw
  ok "ReducerM generated cases" s!"{effectCases} cases"

def lineOfNat (n : Nat) : String :=
  s!"line-{n % 1000}"

def linesOf (xs : Array Nat) : List String :=
  (smallNats xs).toList.map lineOfNat

def renderLines (lines : List String) (trailingNewline : Bool) : String :=
  let body := String.intercalate "\n" lines
  if trailingNewline then
    body ++ "\n"
  else
    body

def seqLinePipeline (lines : List String) : Array Nat :=
  lines.foldl
    (fun acc line =>
      let n := line.length
      if n % 2 == 0 then
        acc ++ #[n, n + 1]
      else
        acc)
    #[]

abbrev FileCase :=
  Array Nat × Bool × Array Nat × Bool × Nat × Nat

def writeGeneratedFile (path : System.FilePath) (rawLines : Array Nat) (trailing : Bool) :
    IO (String × List String) := do
  let lines := linesOf rawLines
  let contents := renderLines lines trailing
  IO.FS.writeFile path contents
  pure (contents, contents.splitOn "\n")

def checkFileCase (idx : Nat) (raw : FileCase) : IO Unit := do
  let (leftRaw, leftTrailing, rightRaw, rightTrailing, grain, depth) := raw
  let cfg := cfgOf grain depth
  let leftPath : System.FilePath := s!"/private/tmp/lean_reducers_prop_{idx}_left.txt"
  let rightPath : System.FilePath := s!"/private/tmp/lean_reducers_prop_{idx}_right.txt"
  let label := s!"file case {idx}"

  let (leftContents, leftLines) ← writeGeneratedFile leftPath leftRaw leftTrailing
  let (_rightContents, rightLines) ← writeGeneratedFile rightPath rightRaw rightTrailing

  let readFileLength ←
    Reducer.readFile leftPath
      |>.foldMap (MonoidSpec.additive Nat) String.length
  assertEq s!"{label}: readFile/foldMap"
    leftContents.length readFileLength

  let readChars ←
    Reducer.readChars leftPath
      |> collectReducerIOWithConfig cfg
  assertEq s!"{label}: readChars" leftContents.toList readChars

  let readLines ←
    Reducer.readLines leftPath
      |> collectReducerIOWithConfig cfg
  assertEq s!"{label}: readLines/foldApproxWithConfig" leftLines readLines

  let readLinesDefault ←
    Reducer.readLines leftPath
      |> collectReducerIO
  assertEq s!"{label}: readLines/foldApprox" leftLines readLinesDefault

  let pipelineSum ←
    Reducer.readLines leftPath
      |>.map String.length
      |>.filter (fun n => n % 2 == 0)
      |>.flatMap (fun n => #[n, n + 1])
      |>.sum
  assertEq s!"{label}: file map/filter/flatMap/sum"
    (seqNatSum (seqLinePipeline leftLines)) pipelineSum

  let foldLength ←
    Reducer.readLines leftPath
      |>.foldWithConfig cfg (MonoidSpec.additive Nat)
        (fun line acc => line.length + acc)
  assertEq s!"{label}: file foldWithConfig"
    (leftLines.foldl (fun acc line => acc + line.length) 0) foldLength

  let foldLengthDefault ←
    Reducer.readLines leftPath
      |>.fold (MonoidSpec.additive Nat)
        (fun line acc => line.length + acc)
  assertEq s!"{label}: file fold"
    (leftLines.foldl (fun acc line => acc + line.length) 0) foldLengthDefault

  let foldMapLengthWithConfig ←
    Reducer.readLines leftPath
      |>.foldMapWithConfig cfg (MonoidSpec.additive Nat) String.length
  assertEq s!"{label}: file foldMapWithConfig"
    (leftLines.foldl (fun acc line => acc + line.length) 0) foldMapLengthWithConfig

  let groupsWithConfig ←
    Reducer.readLines leftPath
      |>.groupByWithConfig cfg (MonoidSpec.additive Nat)
        (fun line => line.length % 7)
        (fun _ acc => acc + 1)
  assertEq s!"{label}: file groupByWithConfig"
    (seqLineCountGroups leftLines) (groupTotals groupsWithConfig)

  let groups ←
    Reducer.readLines leftPath
      |>.groupBy (MonoidSpec.additive Nat)
        (fun line => line.length % 7)
        (fun _ acc => acc + 1)
  assertEq s!"{label}: file groupBy"
    (seqLineCountGroups leftLines) (groupTotals groups)

  let allLines ←
    Reducer.readLinesFromFiles #[leftPath, rightPath]
      |> collectReducerIOWithConfig cfg
  assertEq s!"{label}: readLinesFromFiles"
    (leftLines ++ rightLines) allLines

  let allPathLines ←
    Reducer.readLinesFromFilesWithPath #[leftPath, rightPath]
      |>.map (fun row => (toString row.1, row.2))
      |> collectReducerIOWithConfig cfg
  let expectedPathLines :=
    leftLines.map (fun line => (toString leftPath, line)) ++
    rightLines.map (fun line => (toString rightPath, line))
  assertEq s!"{label}: readLinesFromFilesWithPath"
    expectedPathLines allPathLines

def runFileProperties : IO Unit := do
  reportSection "File producer properties"
  IO.println s!"  generated cases: {fileCases}"
  IO.println "  APIs: readFile, readChars, readLines, readLinesFromFiles, readLinesFromFilesWithPath"
  for idx in List.range fileCases do
    let raw ← sample FileCase (20 + idx % 80)
    checkFileCase idx raw
  ok "file producer generated cases" s!"{fileCases} cases"

  let longLine := String.ofList (List.replicate 5000 'x')
  let boundaryPath : System.FilePath := "/private/tmp/lean_reducers_prop_boundary.txt"
  let boundaryContents := s!"first\n{longLine}\n\nlast\n"
  IO.FS.writeFile boundaryPath boundaryContents
  let cfg := cfgOf 0 99
  let actual ← Reducer.readLines boundaryPath |> collectReducerIOWithConfig cfg
  assertEq "large line boundary repair against sequential split"
    (boundaryContents.splitOn "\n") actual
  ok "large line boundary repair" "1 targeted case"

def main : IO Unit := do
  IO.println "LeanReducers property test report"
  IO.println s!"Plausible: numInst={plausibleCfg.numInst}, maxSize={plausibleCfg.maxSize}, retries={plausibleCfg.numRetries}, seed={plausibleCfg.randomSeed}"
  IO.println "Oracle: every reducer result is compared with a sequential Lean model"
  runPureArrayProperties
  runEffectProperties
  runFileProperties
  IO.println "\nlean_reducers_tests: ok"

end LeanReducersTests

def main : IO Unit :=
  LeanReducersTests.main

import Init.Data.Array.QSort.Basic
import Init.Data.Ord.String
import Examples.ReducerArgs

open LeanReducers
open Examples

namespace Examples.WordCount

structure Options where
  top : Nat := 25
  fused : Bool := false
  paths : Array System.FilePath := #[]
  reducer : ReducerArgs := {}

private def usage : String :=
  String.intercalate "\n" [
    "Usage: lake exe word_count [options] <text-file>...",
    "",
    "--top N                 show the N most common words",
    "--fused                 fuse tokenization and counting in one reduce,",
    "                        hashing word bytes in place with no per-token alloc",
    ReducerArgs.usage
  ]

private partial def parseArgs : List String -> Options -> Except String Options
  | [], opts => .ok opts
  | "--top" :: n :: rest, opts =>
      match n.toNat? with
      | some top => parseArgs rest { opts with top := top }
      | none => .error s!"--top expects a natural number, got {n}"
  | "--top" :: [], _ =>
      .error "--top expects a natural number"
  | "--fused" :: rest, opts => parseArgs rest { opts with fused := true }
  | args, opts => do
      match ← ReducerArgs.parse? args opts.reducer with
      | some (rest, reducer) => parseArgs rest { opts with reducer := reducer }
      | none =>
          match args with
          | arg :: rest =>
              if arg.startsWith "--" then
                .error s!"unknown option: {arg}"
              else
                parseArgs rest { opts with paths := opts.paths.push arg }
          | [] => .ok opts

private structure TokenState (ρ : Type) where
  current : String
  apply : ρ → ρ

private def flushToken (step : String → ρ → ρ) (state : TokenState ρ) : TokenState ρ :=
  if state.current.isEmpty then
    state
  else
    { current := "", apply := fun acc => state.apply (step state.current acc) }

private def wordsOfLine (line : String) : ReducerSeq String where
  run := fun unit step =>
    let state :=
      line.foldl
        (fun state c =>
          if c.isAlphanum then
            { state with current := state.current.push c.toLower }
          else
            flushToken step state)
        { current := "", apply := id }
    (flushToken step state).apply unit

private def wordCounts (cfg : Config) (paths : Array System.FilePath) : IO (Array (String × Nat)) :=
  ReducerPar.readLinesFromFiles paths
    |>.flatMap wordsOfLine
    |>.groupByWithConfig cfg (MonoidSpec.additive Nat) id (fun _ count => count + 1)

private def wordCountsSequential (paths : Array System.FilePath) : IO (Array (String × Nat)) :=
  ReducerSeq.readLinesFromFiles paths
    |>.flatMap wordsOfLine
    |>.groupBy 0 id (fun _ count => count + 1)

/-! ## Fused tokenize-and-count

A single `reduce` over lines that tokenizes each line by scanning its UTF-8
bytes and updates counts directly in a custom open-addressed table keyed by the
lowercased word bytes. Each incoming word is compared against the stored keys
*in place* against the line's bytes, so an owned key (`ByteArray`) is allocated
only the first time a word is seen — never once per occurrence. Word characters
are exactly the ASCII alphanumerics (matching `Char.isAlphanum`), so the counts
are identical to the `flatMap`/`groupBy` implementation. -/

private def fnvOffset : UInt64 := 0xcbf29ce484222325
private def fnvPrime : UInt64 := 0x00000100000001b3

@[inline] private def lowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b + 32 else b

@[inline] private def isWordByte (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (97 ≤ b && b ≤ 122) || (65 ≤ b && b ≤ 90)

@[inline] private def fnvStep (h : UInt64) (b : UInt8) : UInt64 :=
  (h ^^^ b.toUInt64) * fnvPrime

@[inline] private def slotIndex (h : UInt64) (cap : Nat) : Nat :=
  h.toNat % cap

private structure WordTable where
  size : Nat
  keys : Array ByteArray    -- a size-0 ByteArray marks an empty slot
  hashes : Array UInt64
  counts : Array Nat

private def WordTable.empty (cap : Nat) : WordTable where
  size := 0
  keys := Array.replicate cap ByteArray.empty
  hashes := Array.replicate cap 0
  counts := Array.replicate cap 0

private partial def materializeKey (bytes : ByteArray) (i stop : Nat) (acc : ByteArray) : ByteArray :=
  if i ≥ stop then acc
  else materializeKey bytes (i + 1) stop (acc.push (lowerByte bytes[i]!))

-- compare a stored (already lowercased) key to the line's word bytes, in place
private partial def keyMatches (k bytes : ByteArray) (start stop j : Nat) : Bool :=
  if j ≥ stop - start then true
  else if lowerByte bytes[start + j]! == k[j]! then keyMatches k bytes start stop (j + 1)
  else false

-- probe for a fresh (known-distinct) key; used only when rehashing on growth
private partial def insertFresh (key : ByteArray) (h : UInt64) (count : Nat)
    (table : WordTable) (idx : Nat) : WordTable :=
  if table.keys[idx]!.size == 0 then
    { size := table.size + 1
      keys := table.keys.set! idx key
      hashes := table.hashes.set! idx h
      counts := table.counts.set! idx count }
  else insertFresh key h count table ((idx + 1) % table.keys.size)

private def growTable (table : WordTable) : WordTable := Id.run do
  let newCap := table.keys.size * 2
  let mut grown := WordTable.empty newCap
  for i in [0:table.keys.size] do
    let k := table.keys[i]!
    if k.size != 0 then
      let h := table.hashes[i]!
      grown := insertFresh k h table.counts[i]! grown (slotIndex h newCap)
  return grown

@[inline] private def reserve (table : WordTable) : WordTable :=
  if (table.size + 1) * 4 ≥ table.keys.size * 3 then growTable table else table

-- hot path: bump the count for the word [start, stop) of `bytes`, allocating a
-- key only on a miss; `bytes` are never turned into a String per occurrence
private partial def bumpWord (bytes : ByteArray) (start stop : Nat) (h : UInt64)
    (table : WordTable) (idx : Nat) : WordTable :=
  let k := table.keys[idx]!
  if k.size == 0 then
    { size := table.size + 1
      keys := table.keys.set! idx (materializeKey bytes start stop ByteArray.empty)
      hashes := table.hashes.set! idx h
      counts := table.counts.set! idx 1 }
  else if table.hashes[idx]! == h && k.size == stop - start && keyMatches k bytes start stop 0 then
    { table with counts := table.counts.set! idx (table.counts[idx]! + 1) }
  else bumpWord bytes start stop h table ((idx + 1) % table.keys.size)

private def feedWord (bytes : ByteArray) (start stop : Nat) (h : UInt64) (table : WordTable) : WordTable :=
  let table := reserve table
  bumpWord bytes start stop h table (slotIndex h table.keys.size)

private partial def feedBytes (bytes : ByteArray) (n i start : Nat) (h : UInt64) (inWord : Bool)
    (table : WordTable) : WordTable :=
  if i ≥ n then
    if inWord then feedWord bytes start i h table else table
  else
    let b := bytes[i]!
    if isWordByte b then
      if inWord then feedBytes bytes n (i + 1) start (fnvStep h (lowerByte b)) true table
      else feedBytes bytes n (i + 1) i (fnvStep fnvOffset (lowerByte b)) true table
    else if inWord then feedBytes bytes n (i + 1) 0 0 false (feedWord bytes start i h table)
    else feedBytes bytes n (i + 1) 0 0 false table

private def countLine (line : String) (table : WordTable) : WordTable :=
  let bytes := line.toUTF8
  feedBytes bytes bytes.size 0 0 fnvOffset false table

-- merge: fold the smaller table's entries into the larger (combine for parallel)
private partial def addKey (key : ByteArray) (h : UInt64) (incr : Nat)
    (table : WordTable) (idx : Nat) : WordTable :=
  let k := table.keys[idx]!
  if k.size == 0 then
    { size := table.size + 1
      keys := table.keys.set! idx key
      hashes := table.hashes.set! idx h
      counts := table.counts.set! idx incr }
  else if table.hashes[idx]! == h && k == key then
    { table with counts := table.counts.set! idx (table.counts[idx]! + incr) }
  else addKey key h incr table ((idx + 1) % table.keys.size)

private def mergeTables (a b : WordTable) : WordTable := Id.run do
  let (small, large) := if a.size ≤ b.size then (a, b) else (b, a)
  let mut merged := large
  for i in [0:small.keys.size] do
    let k := small.keys[i]!
    if k.size != 0 then
      merged := reserve merged
      merged := addKey k small.hashes[i]! small.counts[i]! merged (slotIndex small.hashes[i]! merged.keys.size)
  return merged

private def WordTable.toArray (table : WordTable) : Array (String × Nat) := Id.run do
  let mut out := Array.mkEmpty table.size
  for i in [0:table.keys.size] do
    let k := table.keys[i]!
    if k.size != 0 then
      out := out.push (String.fromUTF8! k, table.counts[i]!)
  return out

private def wordCountsFused (paths : Array System.FilePath) : IO (Array (String × Nat)) := do
  let table ← (ReducerSeq.readLinesFromFiles paths).reduce (WordTable.empty 4096) countLine
  return table.toArray

private def wordCountsFusedPar (cfg : Config) (paths : Array System.FilePath) : IO (Array (String × Nat)) := do
  let table ← (ReducerPar.readLinesFromFiles paths).reduceWithoutLawsWithConfig
    cfg (WordTable.empty 4096) mergeTables countLine
  return table.toArray

private def wordLess (left right : String × Nat) : Bool :=
  if left.snd == right.snd then
    match compare left.fst right.fst with
    | Ordering.lt => true
    | _ => false
  else
    right.snd < left.snd

private def spaces (n : Nat) : String :=
  "".pushn ' ' n

private def dashes (n : Nat) : String :=
  "".pushn '-' n

private def padLeft (width : Nat) (s : String) : String :=
  spaces (width - s.length) ++ s

private def natWidth (n : Nat) : Nat :=
  (toString n).length

private def maxCountWidth (rows : Array (String × Nat)) : Nat :=
  rows.foldl (fun width row => Nat.max width (natWidth row.snd)) "count".length

private def totalWords (counts : Array (String × Nat)) : Nat :=
  counts.foldl (fun total row => total + row.snd) 0

private def formatTenths (n : Nat) : String :=
  s!"{n / 10}.{n % 10}"

private def secondsTenths (ms : Nat) : Nat :=
  ms / 100

private def printTop (paths : Array System.FilePath) (top : Nat)
    (implementation : String) (elapsedMs : Nat) (counts : Array (String × Nat)) : IO Unit := do
  let rows := (counts.qsort wordLess).take top
  let rankWidth := Nat.max "rank".length (natWidth rows.size)
  let countWidth := maxCountWidth rows
  IO.println "Word count"
  IO.println s!"implementation: {implementation}"
  IO.println s!"files: {paths.size}"
  IO.println s!"elapsed: {formatTenths (secondsTenths elapsedMs)}s"
  IO.println s!"words: {totalWords counts}"
  IO.println s!"unique words: {counts.size}"
  IO.println s!"shown: {rows.size}"
  IO.println ""
  IO.println s!"{padLeft rankWidth "rank"}  {padLeft countWidth "count"}  word"
  IO.println s!"{dashes rankWidth}  {dashes countWidth}  ----"
  let mut rank := 1
  for row in rows do
    IO.println s!"{padLeft rankWidth (toString rank)}  {padLeft countWidth (toString row.snd)}  {row.fst}"
    rank := rank + 1

private def checkInputPaths (paths : Array System.FilePath) : IO Unit := do
  for path in paths do
    if !(← path.pathExists) then
      IO.eprintln s!"missing input file: {path}"
      if toString path == "Examples/data/wikitext-103/wiki.train.tokens" then
        IO.eprintln "prepare WikiText-103 with: lake exe fetch_wikitext103"
        IO.eprintln "the default mirror extracts to: Examples/data/wikitext-103/train.csv"
      IO.Process.exit 1

def main (args : List String) : IO Unit := do
  let opts ←
    match parseArgs args {} with
    | .ok opts => pure opts
    | .error message => do
        IO.eprintln message
        IO.eprintln usage
        IO.Process.exit 1
  if opts.reducer.help then
    IO.println usage
  else if opts.paths.isEmpty then
    IO.eprintln "missing input file"
    IO.eprintln usage
    IO.Process.exit 1
  else
    checkInputPaths opts.paths
    match opts.reducer.validate with
    | .error message =>
        IO.eprintln message
        IO.Process.exit 1
    | .ok () => pure ()
    let startMs ← IO.monoMsNow
    let (implementation, counts) ←
      if opts.fused then
        if opts.reducer.baseline then
          pure ("fused sequential reduce", ← wordCountsFused opts.paths)
        else
          let cfg := opts.reducer.config
          pure (s!"fused parallel reduce (maxDepth {cfg.maxDepth})", ← wordCountsFusedPar cfg opts.paths)
      else if opts.reducer.baseline then
        pure ("sequential reducer", ← wordCountsSequential opts.paths)
      else
        let cfg := opts.reducer.config
        let name :=
          if cfg.maxDepth == 0 then
            s!"sequential reducer (maxDepth {cfg.maxDepth})"
          else
            s!"parallel reducer (maxDepth {cfg.maxDepth})"
        pure (name, ← wordCounts cfg opts.paths)
    let elapsedMs := (← IO.monoMsNow) - startMs
    printTop opts.paths opts.top implementation elapsedMs counts

end Examples.WordCount

def main (args : List String) : IO Unit :=
  Examples.WordCount.main args

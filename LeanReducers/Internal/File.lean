import Init.Data.ByteArray
import Init.System.IO
import LeanReducers.Config
import LeanReducers.FoldSpec

namespace LeanReducers
namespace Internal

def preadFallback (path : System.FilePath) (offset bytes : UInt64) : IO ByteArray := do
  let contents ← IO.FS.readBinFile path
  let start := offset.toNat
  pure (contents.extract start (start + bytes.toNat))

@[extern c "lean_reducers_pread"]
def pread (path : @& System.FilePath) (offset bytes : UInt64) : IO ByteArray :=
  preadFallback path offset bytes

def newlineByte : UInt8 :=
  10

def preadNat (path : System.FilePath) (offset bytes : Nat) : IO ByteArray :=
  pread path offset.toUInt64 bytes.toUInt64

def byteAt? (path : System.FilePath) (pos : Nat) : IO (Option UInt8) := do
  let bytes ← preadNat path pos 1
  if bytes.size == 0 then
    pure none
  else
    pure (some (bytes.get! 0))

partial def findByteFrom (bytes : ByteArray) (target : UInt8) (idx : Nat) : Option Nat :=
  if idx < bytes.size then
    if bytes.get! idx == target then
      some idx
    else
      findByteFrom bytes target (idx + 1)
  else
    none

partial def findNextLineStart (path : System.FilePath) (fileSize pos : Nat) : IO Nat := do
  if pos >= fileSize then
    pure fileSize
  else
    let bytesToRead := min 8192 (fileSize - pos)
    let bytes ← preadNat path pos bytesToRead
    match findByteFrom bytes newlineByte 0 with
    | some idx => pure (pos + idx + 1)
    | none =>
        if bytes.size == 0 then
          pure fileSize
        else
          findNextLineStart path fileSize (pos + bytes.size)

def lineChunkStart (path : System.FilePath) (fileSize start : Nat) : IO Nat := do
  if start == 0 then
    pure 0
  else
    match (← byteAt? path (start - 1)) with
    | some b =>
        if b == newlineByte then
          pure start
        else
          findNextLineStart path fileSize start
    | none => pure fileSize

def lineChunkStop (path : System.FilePath) (fileSize stop : Nat) : IO Nat := do
  if stop >= fileSize then
    pure fileSize
  else if stop == 0 then
    pure 0
  else
    match (← byteAt? path (stop - 1)) with
    | some b =>
        if b == newlineByte then
          pure stop
        else
          findNextLineStart path fileSize stop
    | none => pure fileSize

def foldLineString (q : FoldSpec String ρ) (isFinal : Bool) (text : String) : ρ :=
  let lines := text.splitOn "\n"
  let lines :=
    if !isFinal && text.endsWith "\n" then
      lines.dropLast
    else
      lines
  lines.foldr q.step q.unit

def foldFileLineRange (q : FoldSpec String ρ) (path : System.FilePath)
    (fileSize start stop : Nat) : IO ρ := do
  let actualStart ← lineChunkStart path fileSize start
  let actualStop ← lineChunkStop path fileSize stop
  if actualStart >= actualStop then
    pure q.unit
  else
    let bytes ← preadNat path actualStart (actualStop - actualStart)
    match String.fromUTF8? bytes with
    | some text => pure (foldLineString q (actualStop >= fileSize) text)
    | none => throw <| IO.userError s!"Tried to read file '{path}' containing non UTF-8 data."

structure FileLineRange where
  source : System.FilePath
  fileSize : Nat
  start : Nat
  stop : Nat

def fileLineRangeOfPath (path : System.FilePath) : IO FileLineRange := do
  let metadata ← path.metadata
  let fileSize := metadata.byteSize.toNat
  pure { source := path, fileSize := fileSize, start := 0, stop := fileSize }

def fileLineRangesOfPaths (paths : Array System.FilePath) : IO (Array FileLineRange) := do
  let mut ranges := #[]
  for path in paths do
    ranges := ranges.push (← fileLineRangeOfPath path)
  pure ranges

def fileLineRangeBytes (range : FileLineRange) : Nat :=
  range.stop - range.start

def fileLineRangesBytes (ranges : Array FileLineRange) : Nat :=
  ranges.foldl (fun total range => total + fileLineRangeBytes range) 0

def foldFileLineSourceRange (q : FoldSpec String ρ) (range : FileLineRange) : IO ρ := do
  if range.fileSize == 0 then
    pure (q.step "" q.unit)
  else
    foldFileLineRange q range.source range.fileSize range.start range.stop

def splitFileLineRangesByCount (ranges : Array FileLineRange) :
    Option (Array FileLineRange × Array FileLineRange) :=
  let mid := ranges.size / 2
  if mid == 0 || mid == ranges.size then
    none
  else
    some (ranges.extract 0 mid, ranges.extract mid ranges.size)

def splitFileLineRangesAtHalf (ranges : Array FileLineRange) :
    Option (Array FileLineRange × Array FileLineRange) :=
  let total := fileLineRangesBytes ranges
  if total == 0 then
    splitFileLineRangesByCount ranges
  else
    let target := total / 2
    if target == 0 then
      splitFileLineRangesByCount ranges
    else
      Id.run do
        let mut left : Array FileLineRange := #[]
        let mut right : Array FileLineRange := #[]
        let mut leftBytes := 0
        let mut onRight := false
        for range in ranges do
          if onRight then
            right := right.push range
          else
            let bytes := fileLineRangeBytes range
            if bytes == 0 then
              left := left.push range
            else if leftBytes + bytes < target then
              left := left.push range
              leftBytes := leftBytes + bytes
            else if leftBytes + bytes == target then
              left := left.push range
              leftBytes := target
              onRight := true
            else
              let cutBytes := target - leftBytes
              if cutBytes == 0 then
                right := right.push range
              else if cutBytes >= bytes then
                left := left.push range
                leftBytes := leftBytes + bytes
              else
                let mid := range.start + cutBytes
                left := left.push { range with stop := mid }
                right := right.push { range with start := mid }
                leftBytes := target
              onRight := true
        if left.isEmpty || right.isEmpty then
          splitFileLineRangesByCount ranges
        else
          some (left, right)

def foldFileLineRangesIORange (unit : ρ) (combine : ρ → ρ → ρ)
    (foldOne : FileLineRange → IO ρ) (ranges : Array FileLineRange) : IO ρ := do
  let mut acc := unit
  for range in ranges do
    let result ← foldOne range
    acc := combine acc result
  pure acc

partial def foldFileLineRangesIOCore (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (foldOne : FileLineRange → IO ρ) (ranges : Array FileLineRange) : Nat → IO ρ
  | 0 => foldFileLineRangesIORange unit combine foldOne ranges
  | depth + 1 => do
      let bytes := fileLineRangesBytes ranges
      if ranges.isEmpty then
        pure unit
      else if bytes ≤ cfg.grain then
        foldFileLineRangesIORange unit combine foldOne ranges
      else if bytes ≤ 1 then
        foldFileLineRangesIORange unit combine foldOne ranges
      else
        match splitFileLineRangesAtHalf ranges with
        | none => foldFileLineRangesIORange unit combine foldOne ranges
        | some (leftRanges, rightRanges) =>
            let rightTask ← IO.asTask
              (foldFileLineRangesIOCore cfg unit combine foldOne rightRanges depth)
              cfg.priority
            let left ← foldFileLineRangesIOCore cfg unit combine foldOne leftRanges depth
            match rightTask.get with
            | Except.ok right => pure (combine left right)
            | Except.error err => throw err

def foldFileLineRangesIO (cfg : Config) (q : FoldSpec String ρ)
    (ranges : Array FileLineRange) : IO ρ :=
  foldFileLineRangesIOCore cfg q.unit q.combine (foldFileLineSourceRange q)
    ranges cfg.maxDepth

def foldFileLinesIO (cfg : Config) (q : FoldSpec String ρ)
    (path : System.FilePath) : IO ρ := do
  let ranges ← fileLineRangesOfPaths #[path]
  foldFileLineRangesIO cfg q ranges

def foldFilesLinesIO (cfg : Config) (q : FoldSpec String ρ)
    (paths : Array System.FilePath) : IO ρ := do
  let ranges ← fileLineRangesOfPaths paths
  foldFileLineRangesIO cfg q ranges

def fileLineWithPathSpec (q : FoldSpec (System.FilePath × String) ρ)
    (path : System.FilePath) : FoldSpec String ρ where
  unit := q.unit
  combine := q.combine
  step := fun line acc => q.step (path, line) acc

def foldFileLineRangesWithPathIO (cfg : Config) (q : FoldSpec (System.FilePath × String) ρ)
    (ranges : Array FileLineRange) : IO ρ :=
  foldFileLineRangesIOCore cfg q.unit q.combine
    (fun range => foldFileLineSourceRange (fileLineWithPathSpec q range.source) range)
    ranges cfg.maxDepth

def foldFilesLinesWithPathIO (cfg : Config) (q : FoldSpec (System.FilePath × String) ρ)
    (paths : Array System.FilePath) : IO ρ := do
  let ranges ← fileLineRangesOfPaths paths
  foldFileLineRangesWithPathIO cfg q ranges

end Internal
end LeanReducers

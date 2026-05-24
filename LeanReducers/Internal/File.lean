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

partial def foldFileLinesIOCore (cfg : Config) (q : FoldSpec String ρ)
    (path : System.FilePath) (fileSize start stop : Nat) : Nat → IO ρ
  | 0 => foldFileLineRange q path fileSize start stop
  | depth + 1 => do
      let len := stop - start
      if len ≤ cfg.grain then
        foldFileLineRange q path fileSize start stop
      else if len ≤ 1 then
        foldFileLineRange q path fileSize start stop
      else
        let mid := start + len / 2
        let rightTask ← IO.asTask
          (foldFileLinesIOCore cfg q path fileSize mid stop depth)
          cfg.priority
        let left ← foldFileLinesIOCore cfg q path fileSize start mid depth
        match rightTask.get with
        | Except.ok right => pure (q.combine left right)
        | Except.error err => throw err

def foldFileLinesIO (cfg : Config) (q : FoldSpec String ρ)
    (path : System.FilePath) : IO ρ := do
  let metadata ← path.metadata
  let fileSize := metadata.byteSize.toNat
  if fileSize == 0 then
    pure (q.step "" q.unit)
  else
    foldFileLinesIOCore cfg q path fileSize 0 fileSize cfg.maxDepth

def foldFileLineReadersIORange (unit : ρ) (combine : ρ → ρ → ρ)
    (foldOne : System.FilePath → IO ρ) (paths : Array System.FilePath)
    (start stop : Nat) : IO ρ := do
  let mut acc := unit
  for path in paths.extract start stop do
    let result ← foldOne path
    acc := combine acc result
  pure acc

partial def foldFileLineReadersIOCore (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (foldOne : System.FilePath → IO ρ) (paths : Array System.FilePath)
    (start stop : Nat) : Nat → IO ρ
  | 0 => foldFileLineReadersIORange unit combine foldOne paths start stop
  | depth + 1 => do
      let len := stop - start
      if len ≤ 1 then
        foldFileLineReadersIORange unit combine foldOne paths start stop
      else
        let mid := start + len / 2
        let rightTask ← IO.asTask
          (foldFileLineReadersIOCore cfg unit combine foldOne paths mid stop depth)
          cfg.priority
        let left ← foldFileLineReadersIOCore cfg unit combine foldOne paths start mid depth
        match rightTask.get with
        | Except.ok right => pure (combine left right)
        | Except.error err => throw err

def foldFilesLinesIO (cfg : Config) (q : FoldSpec String ρ)
    (paths : Array System.FilePath) : IO ρ :=
  foldFileLineReadersIOCore cfg q.unit q.combine
    (fun path => foldFileLinesIO cfg q path)
    paths 0 paths.size cfg.maxDepth

def fileLineWithPathSpec (q : FoldSpec (System.FilePath × String) ρ)
    (path : System.FilePath) : FoldSpec String ρ where
  unit := q.unit
  combine := q.combine
  step := fun line acc => q.step (path, line) acc

def foldFilesLinesWithPathIO (cfg : Config) (q : FoldSpec (System.FilePath × String) ρ)
    (paths : Array System.FilePath) : IO ρ :=
  foldFileLineReadersIOCore cfg q.unit q.combine
    (fun path => foldFileLinesIO cfg (fileLineWithPathSpec q path) path)
    paths 0 paths.size cfg.maxDepth

end Internal
end LeanReducers

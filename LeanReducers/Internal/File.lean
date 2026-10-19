import Init.Data.ByteArray
import Init.System.IO
import Std.Sync.Mutex
import LeanReducers.Config
import LeanReducers.ByteSource
import LeanReducers.FoldSpec
import LeanReducers.Internal.Lines

namespace LeanReducers
namespace Internal

def preadFallback (path : System.FilePath) (offset bytes : UInt64) : IO ByteArray := do
  let contents ← IO.FS.readBinFile path
  let start := offset.toNat
  pure (contents.extract start (start + bytes.toNat))

@[extern c "lean_reducers_pread"]
def pread (path : @& System.FilePath) (offset bytes : UInt64) : IO ByteArray :=
  preadFallback path offset bytes

@[extern c "lean_reducers_cpu_percentages"]
def cpuPercentagesString : IO String :=
  pure ""

@[extern c "lean_reducers_process_sample"]
def processSampleString : IO String :=
  pure ""

def newlineByte : UInt8 :=
  10

def fileSource (path : System.FilePath) : IO ByteSource := do
  let size := (← path.metadata).byteSize.toNat
  return { size, name := path.toString
           read := fun offset count => pread path offset.toUInt64 (min count (size - offset)).toUInt64 }

private def readExact (source : ByteSource) (offset count : Nat) : IO ByteArray := do
  let expected := min count (source.size - offset)
  let bytes ← source.read offset expected
  unless bytes.size == expected do throw (IO.userError s!"Short read from {source.name}")
  return bytes

private partial def nextLineStart (source : ByteSource) (pos remaining : Nat) : IO Nat := do
  if pos ≥ source.size then return source.size
  if remaining == 0 then throw (IO.userError "Line exceeds maxLineBytes")
  let bytes ← readExact source pos (min 8192 remaining)
  if let some index := bytes.data.findIdx? (· == newlineByte) then return pos + index + 1
  nextLineStart source (pos + bytes.size) (remaining - bytes.size)

private def lineBoundary (source : ByteSource) (pos limit : Nat) : IO Nat := do
  if pos == 0 then return 0
  if pos ≥ source.size then return source.size
  let previous ← readExact source (pos - 1) 1
  if previous.get! 0 == newlineByte then return pos
  nextLineStart source pos limit

private def foldLineRange (cfg : Config) (q : FoldSpec String ρ)
    (range : ByteRange ByteSource) (trailingEmpty : Bool) : IO ρ := do
  let source := range.source
  let start ← lineBoundary source range.start cfg.maxLineBytes
  let stop ← lineBoundary source range.stop cfg.maxLineBytes
  if start ≥ stop then return q.unit
  let bytes ← readExact source start (stop - start)
  let mut length := 0
  for byte in bytes do
    if byte == newlineByte then length := 0
    else
      length := length + 1
      if length > cfg.maxLineBytes then throw (IO.userError "Line exceeds maxLineBytes")
  let some text := String.fromUTF8? bytes
    | throw (IO.userError s!"Non UTF-8 data in {source.name}")
  return foldLinesRight text q.unit q.step
    (dropTrailingEmpty := !trailingEmpty || stop < source.size)

abbrev FileLineRange := ByteRange ByteSource

def fileLineRangeOfPath (path : System.FilePath) : IO FileLineRange := do
  let source ← fileSource path
  return { source, start := 0, stop := source.size }

def fileLineRangesOfPaths (paths : Array System.FilePath) : IO (Array FileLineRange) :=
  paths.mapM fileLineRangeOfPath

def fileLineRangeBytes (range : FileLineRange) : Nat := range.size

def fileLineRangesBytes (ranges : Array FileLineRange) : Nat :=
  ranges.foldl (fun total range => total + range.size) 0

structure DiagnosticsState where
  totalBytes : Nat
  doneBytes : Nat
  activeRanges : Nat
  completedRanges : Nat
  cpuBars : Nat
  startMs : Nat
  finished : Bool

structure ProcessSample where
  rssKB : Option Nat
  readBytes : Option Nat
  writeBytes : Option Nat
  cpuMicros : Option Nat
  systemTotalKB : Option Nat
  systemAvailableKB : Option Nat

structure ProcessIORates where
  readTenths : Option Nat := none
  writeTenths : Option Nat := none
  cpuPercentTenths : Option Nat := none

structure DiagnosticsRenderState where
  renderedLines : Nat := 0
  lastSampleMs : Option Nat := none
  lastProcessSample : Option ProcessSample := none

private def repeated (n : Nat) (c : Char) : String :=
  "".pushn c n

private def barFill (width done total : Nat) : Nat :=
  if total == 0 then
    width
  else
    let filled := min width ((done * width) / total)
    if done > 0 && filled == 0 then
      1
    else
      filled

private def esc : String :=
  String.singleton (Char.ofNat 27)

private def csi (code : String) : String :=
  esc ++ "[" ++ code

private def sgr (code : String) : String :=
  csi (code ++ "m")

private def paint (cfg : DiagnosticsConfig) (code text : String) : String :=
  if cfg.useColor && !text.isEmpty then
    sgr code ++ text ++ sgr "0"
  else
    text

private def label (cfg : DiagnosticsConfig) (text : String) : String :=
  paint cfg "1;36" text

private def value (cfg : DiagnosticsConfig) (text : String) : String :=
  paint cfg "1;37" text

private def dim (cfg : DiagnosticsConfig) (text : String) : String :=
  paint cfg "90" text

private def bar (cfg : DiagnosticsConfig) (color : String) (width done total : Nat) : String :=
  let filled :=
    barFill width done total
  "[" ++ paint cfg color (repeated filled '#') ++ dim cfg (repeated (width - filled) '-') ++ "]"

private def formatTenths (n : Nat) : String :=
  s!"{n / 10}.{n % 10}"

private def mbTenths (bytes : Nat) : Nat :=
  (bytes * 10) / (1024 * 1024)

private def mbPerSecondTenths (bytes elapsedMs : Nat) : Nat :=
  if elapsedMs == 0 then
    0
  else
    (bytes * 10000) / (elapsedMs * 1024 * 1024)

private def percentTenths (done total : Nat) : Nat :=
  if total == 0 then
    1000
  else
    min 1000 ((done * 1000) / total)

private def secondsTenths (ms : Nat) : Nat :=
  ms / 100

private def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

private structure WordState where
  words : Array String
  current : String

private def flushWord (state : WordState) : WordState :=
  if state.current.isEmpty then
    state
  else
    { words := state.words.push state.current, current := "" }

private def wordsAscii (s : String) : Array String :=
  let state :=
    s.foldl
      (fun state c =>
        if c.isWhitespace then
          flushWord state
        else
          { state with current := state.current.push c })
      { words := #[], current := "" }
  (flushWord state).words

private def parseNatArray (s : String) : Array Nat :=
  (wordsAscii s).foldl
    (fun values field =>
      match field.toNat? with
      | some value => values.push value
      | none => values)
    #[]

private def parseOptionalNat (field : String) : Option Nat :=
  if field == "-" then
    none
  else
    field.toNat?

private def sampleCpuPercentages : IO (Array Nat) := do
  pure (parseNatArray (← cpuPercentagesString))

private def sampleProcess : IO (Option ProcessSample) := do
  try
    let fields := wordsAscii (← processSampleString)
    match fields[0]?, fields[1]?, fields[2]?, fields[3]?, fields[4]?, fields[5]? with
    | some rss, some readBytes, some writeBytes, some cpuMicros, some systemTotal, some systemAvailable =>
        let sample : ProcessSample := {
          rssKB := parseOptionalNat rss,
          readBytes := parseOptionalNat readBytes,
          writeBytes := parseOptionalNat writeBytes,
          cpuMicros := parseOptionalNat cpuMicros,
          systemTotalKB := parseOptionalNat systemTotal,
          systemAvailableKB := parseOptionalNat systemAvailable
        }
        match sample.rssKB, sample.readBytes, sample.writeBytes, sample.cpuMicros,
            sample.systemTotalKB, sample.systemAvailableKB with
        | none, none, none, none, none, none => pure none
        | _, _, _, _, _, _ => pure (some sample)
    | _, _, _, _, _, _ => pure none
  catch
  | _ => pure none

private def pad2 (n : Nat) : String :=
  if n < 10 then
    "0" ++ toString n
  else
    toString n

private def averageCpuPercent (samples : Array Nat) : Option Nat :=
  if samples.isEmpty then
    none
  else
    some (samples.foldl (fun total pct => total + pct) 0 / samples.size)

private def percentTenthsValue (cfg : DiagnosticsConfig) (pct? : Option Nat) : String :=
  match pct? with
  | some pct => value cfg s!"{formatTenths pct}%"
  | none => dim cfg "n/a"

private def cpuSummaryLayer (cfg : DiagnosticsConfig) (samples : Array Nat)
    (cpuBars : Nat) (processCpu? : Option Nat) : String :=
  let osAvg :=
    match averageCpuPercent samples with
    | some pct => value cfg s!"{pct}%"
    | none => dim cfg "n/a"
  s!"  {label cfg "CPU     "} os avg {osAvg}  " ++
  s!"proc {percentTenthsValue cfg processCpu?}  " ++
  s!"bars {value cfg (toString cpuBars)}"

private def cpuLayerRows (cfg : DiagnosticsConfig) (samples : Array Nat)
    (cpuBars : Nat) : List String :=
  List.range cpuBars |>.map fun idx =>
    let name := s!"CPU {pad2 idx}"
    match samples[idx]? with
    | some pct =>
        s!"  {label cfg name} {bar cfg "32" cfg.width pct 100} {value cfg s!"{pct}%"}"
    | none =>
        s!"  {label cfg name} {bar cfg "32" cfg.width 0 100} {dim cfg "n/a"}"

private def sampleRateTenths (previous? current? : Option Nat) (elapsedMs : Nat) :
    Option Nat :=
  match previous?, current? with
  | some previous, some current =>
      some (mbPerSecondTenths (if current >= previous then current - previous else 0) elapsedMs)
  | _, _ => none

private def sampleCpuPercentTenths (previous? current? : Option Nat) (elapsedMs : Nat) :
    Option Nat :=
  match previous?, current? with
  | some previous, some current =>
      if elapsedMs == 0 then
        some 0
      else
        some ((if current >= previous then current - previous else 0) / elapsedMs)
  | _, _ => none

private def sampleIORates (renderState : IO.Ref DiagnosticsRenderState) (now : Nat)
    (sample? : Option ProcessSample) : IO ProcessIORates := do
  let render ← renderState.get
  let rates :=
    match render.lastSampleMs, render.lastProcessSample, sample? with
    | some lastMs, some previous, some current => {
        readTenths := sampleRateTenths previous.readBytes current.readBytes (now - lastMs),
        writeTenths := sampleRateTenths previous.writeBytes current.writeBytes (now - lastMs),
        cpuPercentTenths :=
          sampleCpuPercentTenths previous.cpuMicros current.cpuMicros (now - lastMs)
      }
    | _, _, _ => {}
  match sample? with
  | some sample =>
      renderState.set { render with lastSampleMs := some now, lastProcessSample := some sample }
  | none =>
      pure ()
  pure rates

private def optionalAdd (left? right? : Option Nat) : Option Nat :=
  match left?, right? with
  | some left, some right => some (left + right)
  | some left, none => some left
  | none, some right => some right
  | none, none => none

private def rateValue (cfg : DiagnosticsConfig) (rate? : Option Nat) : String :=
  match rate? with
  | some rate => value cfg (formatTenths rate)
  | none => dim cfg "n/a"

private def ioLayer (cfg : DiagnosticsConfig) (rates : ProcessIORates) : String :=
  let total? := optionalAdd rates.readTenths rates.writeTenths
  match total? with
  | some total =>
      s!"  {label cfg "IO os   "} {bar cfg "34" cfg.width total (cfg.ioScaleMBps * 10)} " ++
      s!"{value cfg s!"{formatTenths total} MB/s"}  " ++
      s!"r {rateValue cfg rates.readTenths}  w {rateValue cfg rates.writeTenths}"
  | none =>
      s!"  {label cfg "IO os   "} {bar cfg "34" cfg.width 0 (cfg.ioScaleMBps * 10)} " ++
      s!"{dim cfg "n/a"}  r {dim cfg "n/a"}  w {dim cfg "n/a"}"

private def processMemoryLayer (cfg : DiagnosticsConfig) (sample? : Option ProcessSample) : String :=
  match sample?.bind (fun sample => sample.rssKB) with
  | some kb =>
      let mb := kb / 1024
      s!"  {label cfg "MEM proc"} {bar cfg "35" cfg.width mb cfg.memoryScaleMB} {value cfg s!"{mb} MB"}"
  | none =>
      s!"  {label cfg "MEM proc"} {bar cfg "35" cfg.width 0 cfg.memoryScaleMB} {dim cfg "n/a"}"

private def systemMemoryLayer (cfg : DiagnosticsConfig) (sample? : Option ProcessSample) : String :=
  match sample?.bind (fun sample => sample.systemTotalKB),
      sample?.bind (fun sample => sample.systemAvailableKB) with
  | some totalKB, some availableKB =>
      let availableKB := min totalKB availableKB
      let usedKB := totalKB - availableKB
      let usedPercent :=
        if totalKB == 0 then
          0
        else
          (usedKB * 100) / totalKB
      s!"  {label cfg "MEM sys "} {bar cfg "35" cfg.width usedKB totalKB} " ++
      s!"{value cfg s!"{usedPercent}%"}  avail {value cfg s!"{availableKB / 1024} MB"}"
  | _, _ =>
      s!"  {label cfg "MEM sys "} {bar cfg "35" cfg.width 0 1} {dim cfg "n/a"}"

private def renderDiagnosticsFrame (cfg : DiagnosticsConfig)
    (state : DiagnosticsState) (renderState : IO.Ref DiagnosticsRenderState) : IO String := do
  let now ← IO.monoMsNow
  let elapsed := now - state.startMs
  let pct := percentTenths state.doneBytes state.totalBytes
  let doneMB := mbTenths state.doneBytes
  let totalMB := mbTenths state.totalBytes
  let cpuSamples ←
    if cfg.sampleSystem then
      sampleCpuPercentages
    else
      pure #[]
  let sample? ←
    if cfg.sampleSystem then
      sampleProcess
    else
      pure none
  let ioRates ←
    if cfg.sampleSystem then
      sampleIORates renderState now sample?
    else
      pure {}
  let title := paint cfg "1;36" "LeanReducers diagnostics"
  let progress :=
    s!"  {label cfg "PROGRESS"} {bar cfg "32" cfg.width state.doneBytes state.totalBytes} " ++
    s!"{value cfg s!"{formatTenths pct}%"}  " ++
    s!"{dim cfg s!"{formatTenths doneMB}/{formatTenths totalMB} MB"}"
  let io := ioLayer cfg ioRates
  let cpuSummary := cpuSummaryLayer cfg cpuSamples state.cpuBars ioRates.cpuPercentTenths
  let cpuRows := cpuLayerRows cfg cpuSamples state.cpuBars
  let processMemory := processMemoryLayer cfg sample?
  let systemMemory := systemMemoryLayer cfg sample?
  let ranges :=
    s!"  {label cfg "RANGES  "} active {value cfg (toString state.activeRanges)}  " ++
    s!"done {value cfg (toString state.completedRanges)}  " ++
    s!"elapsed {value cfg s!"{formatTenths (secondsTenths elapsed)}s"}"
  pure (String.intercalate "\n"
    ([title, progress, io, cpuSummary] ++ cpuRows ++ [processMemory, systemMemory, ranges]))

private def frameLineCount (frame : String) : Nat :=
  frame.foldl
    (fun count c =>
      if c == '\n' then
        count + 1
      else
        count)
    1

private def emitDiagnosticsFrame (cfg : DiagnosticsConfig)
    (renderState : IO.Ref DiagnosticsRenderState) (frame : String) : IO Unit := do
  let state ← renderState.get
  let lead :=
    if cfg.topAnchor then
      if state.renderedLines == 0 then
        csi "?25l"
      else
        csi s!"{state.renderedLines}A" ++ "\r" ++ csi "J"
    else
      ""
  cfg.output.emit (lead ++ frame ++ "\n")
  renderState.set { state with renderedLines := frameLineCount frame }

private def finishDiagnosticsFrame (cfg : DiagnosticsConfig) : IO Unit := do
  if cfg.topAnchor then
    cfg.output.emit (csi "?25h")

private def renderDiagnosticsSnapshot (cfg : DiagnosticsConfig)
    (state : Std.Mutex DiagnosticsState)
    (renderState : IO.Ref DiagnosticsRenderState) : IO Unit := do
  let snapshot ← state.atomically do get
  let frame ← renderDiagnosticsFrame cfg snapshot renderState
  emitDiagnosticsFrame cfg renderState frame

partial def renderDiagnosticsLoop (cfg : DiagnosticsConfig)
    (state : Std.Mutex DiagnosticsState)
    (renderState : IO.Ref DiagnosticsRenderState) : IO Unit := do
  IO.sleep cfg.intervalMs.toUInt32
  let snapshot ← state.atomically do get
  if !snapshot.finished then
    let frame ← renderDiagnosticsFrame cfg snapshot renderState
    emitDiagnosticsFrame cfg renderState frame
    renderDiagnosticsLoop cfg state renderState

private def markDiagnosticsFinished (state : Std.Mutex DiagnosticsState) : IO Unit :=
  state.atomically do
    modify fun s => { s with finished := true }

private def renderFinalDiagnosticsLine (cfg : DiagnosticsConfig)
    (state : Std.Mutex DiagnosticsState)
    (renderState : IO.Ref DiagnosticsRenderState) : IO Unit := do
  renderDiagnosticsSnapshot cfg state renderState
  finishDiagnosticsFrame cfg

private def waitDiagnosticsLoop (task : Task (Except IO.Error Unit)) : IO Unit :=
  match task.get with
  | Except.ok () => pure ()
  | Except.error _ => pure ()

private def withRangeDiagnostics (cfg : Config) (ranges : Array FileLineRange)
    (action : Option (Std.Mutex DiagnosticsState) → IO ρ) : IO ρ := do
  if !cfg.diagnostics.enabled then
    action none
  else
    let startMs ← IO.monoMsNow
    let warmCpuSamples ←
      if cfg.diagnostics.cpuBars == 0 then
        sampleCpuPercentages
      else
        pure #[]
    let cpuBars :=
      if cfg.diagnostics.cpuBars == 0 then
        max 1 (if warmCpuSamples.isEmpty then pow2 cfg.maxDepth else warmCpuSamples.size)
      else
        max 1 cfg.diagnostics.cpuBars
    let state ← Std.Mutex.new {
      totalBytes := fileLineRangesBytes ranges
      doneBytes := 0
      activeRanges := 0
      completedRanges := 0
      cpuBars := cpuBars
      startMs := startMs
      finished := false
    }
    let renderState ← IO.mkRef {}
    renderDiagnosticsSnapshot cfg.diagnostics state renderState
    let task ← IO.asTask (renderDiagnosticsLoop cfg.diagnostics state renderState) cfg.priority
    try
      let result ← action (some state)
      markDiagnosticsFinished state
      waitDiagnosticsLoop task
      renderFinalDiagnosticsLine cfg.diagnostics state renderState
      pure result
    catch
    | err =>
        markDiagnosticsFinished state
        waitDiagnosticsLoop task
        renderFinalDiagnosticsLine cfg.diagnostics state renderState
        throw err

private def noteRangeStart (diagnostics? : Option (Std.Mutex DiagnosticsState)) : IO Unit := do
  match diagnostics? with
  | none => pure ()
  | some diagnostics =>
      diagnostics.atomically do
        modify fun s => { s with activeRanges := s.activeRanges + 1 }

private def noteRangeFinish (diagnostics? : Option (Std.Mutex DiagnosticsState))
    (range : FileLineRange) : IO Unit := do
  match diagnostics? with
  | none => pure ()
  | some diagnostics =>
      diagnostics.atomically do
        modify fun s => {
          s with
          doneBytes := s.doneBytes + fileLineRangeBytes range
          activeRanges := s.activeRanges - 1
          completedRanges := s.completedRanges + 1
        }

private def noteRangeAbort (diagnostics? : Option (Std.Mutex DiagnosticsState)) : IO Unit := do
  match diagnostics? with
  | none => pure ()
  | some diagnostics =>
      diagnostics.atomically do
        modify fun s => { s with activeRanges := s.activeRanges - 1 }

def foldFileLineSourceRange (cfg : Config) (q : FoldSpec String ρ)
    (range : FileLineRange) (trailingEmpty : Bool := true) : IO ρ := do
  unless range.start ≤ range.stop && range.stop ≤ range.source.size do
    throw (IO.userError "Invalid source byte range")
  if range.source.size == 0 then
    return if trailingEmpty then q.step "" q.unit else q.unit
  let mut result := q.unit
  for part in ByteRange.partition #[range] cfg.maxReadBytes do
    result := q.combine result (← foldLineRange cfg q part trailingEmpty)
  return result

def foldFileLineRangesIORange (diagnostics? : Option (Std.Mutex DiagnosticsState))
    (unit : ρ) (combine : ρ → ρ → ρ) (foldOne : FileLineRange → IO ρ)
    (ranges : Array FileLineRange) : IO ρ := do
  let mut acc := unit
  for range in ranges do
    noteRangeStart diagnostics?
    try
      let result ← foldOne range
      noteRangeFinish diagnostics? range
      acc := combine acc result
    catch
    | err =>
        noteRangeAbort diagnostics?
        throw err
  pure acc

partial def foldFileLineRangesIOCore (cfg : Config) (unit : ρ) (combine : ρ → ρ → ρ)
    (diagnostics? : Option (Std.Mutex DiagnosticsState)) (foldOne : FileLineRange → IO ρ)
    (ranges : Array FileLineRange) : Nat → IO ρ
  | 0 => foldFileLineRangesIORange diagnostics? unit combine foldOne ranges
  | depth + 1 => do
      let bytes := fileLineRangesBytes ranges
      if ranges.isEmpty then
        pure unit
      else if bytes ≤ cfg.grain then
        foldFileLineRangesIORange diagnostics? unit combine foldOne ranges
      else if bytes ≤ 1 then
        foldFileLineRangesIORange diagnostics? unit combine foldOne ranges
      else
        match ByteRange.splitAtHalf ranges with
        | none => foldFileLineRangesIORange diagnostics? unit combine foldOne ranges
        | some (leftRanges, rightRanges) =>
            let rightTask ← IO.asTask
              (foldFileLineRangesIOCore cfg unit combine diagnostics? foldOne rightRanges depth)
              cfg.priority
            let left ← try
              pure (.ok (← foldFileLineRangesIOCore cfg unit combine diagnostics? foldOne leftRanges depth))
            catch error => pure (Except.error error)
            -- Join even when the left half failed; resource scopes cannot exit
            -- while their right-hand tasks still use the reader.
            let right ← IO.wait rightTask
            let left ← IO.ofExcept left
            match right with
            | Except.ok right => pure (combine left right)
            | Except.error err => throw err

def foldFileLineRangesIO (cfg : Config) (q : FoldSpec String ρ)
    (ranges : Array FileLineRange) (trailingEmpty : Bool := true) : IO ρ :=
  withRangeDiagnostics cfg ranges fun diagnostics? =>
    foldFileLineRangesIOCore cfg q.unit q.combine diagnostics? (fun range => foldFileLineSourceRange cfg q range trailingEmpty)
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
  withRangeDiagnostics cfg ranges fun diagnostics? =>
    foldFileLineRangesIOCore cfg q.unit q.combine diagnostics?
      (fun range => foldFileLineSourceRange cfg (fileLineWithPathSpec q range.source.name) range)
      ranges cfg.maxDepth

def foldFilesLinesWithPathIO (cfg : Config) (q : FoldSpec (System.FilePath × String) ρ)
    (paths : Array System.FilePath) : IO ρ := do
  let ranges ← fileLineRangesOfPaths paths
  foldFileLineRangesWithPathIO cfg q ranges

end Internal
end LeanReducers

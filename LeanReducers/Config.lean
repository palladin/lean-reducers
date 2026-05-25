import Init.System.IO

namespace LeanReducers

structure DiagnosticsOutput where
  emit : String → IO Unit

namespace DiagnosticsOutput

private def emitStream (stream : BaseIO IO.FS.Stream) (text : String) : IO Unit := do
  let out ← stream
  out.putStr text
  out.flush

def emitLine (output : DiagnosticsOutput) (line : String) : IO Unit :=
  output.emit (line.push '\n')

def console : DiagnosticsOutput where
  emit := emitStream IO.getStderr

def stderr : DiagnosticsOutput :=
  console

def stdout : DiagnosticsOutput where
  emit := emitStream IO.getStdout

end DiagnosticsOutput

instance : Repr DiagnosticsOutput where
  reprPrec _ _ := "DiagnosticsOutput"

structure DiagnosticsConfig where
  enabled : Bool := false
  intervalMs : Nat := 250
  width : Nat := 24
  sampleSystem : Bool := true
  useColor : Bool := true
  topAnchor : Bool := true
  cpuBars : Nat := 0
  memoryScaleMB : Nat := 1024
  ioScaleMBps : Nat := 500
  output : DiagnosticsOutput := DiagnosticsOutput.console
  deriving Repr

/--
Runtime knobs for parallel reductions.

`grain` is the smallest chunk size worth splitting, `maxDepth` bounds the task
tree, and `priority` is passed to Lean's task scheduler. Diagnostics emit
through the configured output sink and do not affect reducer results.
-/
structure Config where
  grain : Nat := 2048
  maxDepth : Nat := 4
  priority : Task.Priority := Task.Priority.default
  diagnostics : DiagnosticsConfig := {}
  deriving Repr

namespace Config

def default : Config := {}

end Config

end LeanReducers

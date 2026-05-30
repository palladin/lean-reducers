import LeanReducers

open LeanReducers

namespace Examples

structure ReducerArgs where
  config : Config := {}
  baseline : Bool := false
  help : Bool := false

namespace ReducerArgs

def usage : String :=
  String.intercalate "\n" [
    "--baseline              run the sequential ReducerSeq implementation",
    "--grain N               set the smallest byte range worth splitting",
    "--max-depth N           set reducer split depth; ranges are capped at 2^N",
    "--diagnostics           show a colorized top-anchored diagnostics panel",
    "--diagnostics-output D  choose console, stderr, or stdout",
    "--help                  show this help"
  ]

private def withDiagnostics (args : ReducerArgs) : ReducerArgs :=
  { args with
    config := { args.config with
      diagnostics := { args.config.diagnostics with enabled := true, sampleSystem := true }
    }
  }

private def withDiagnosticsOutput (args : ReducerArgs) (output : DiagnosticsOutput) : ReducerArgs :=
  { args with
    config := { args.config with
      diagnostics := { args.config.diagnostics with output := output }
    }
  }

def parse? : List String → ReducerArgs → Except String (Option (List String × ReducerArgs))
  | "--baseline" :: rest, args =>
      .ok (some (rest, { args with baseline := true }))
  | "--grain" :: n :: rest, args =>
      match n.toNat? with
      | some grain => .ok (some (rest, { args with config := { args.config with grain := grain } }))
      | none => .error s!"--grain expects a natural number, got {n}"
  | "--grain" :: [], _ =>
      .error "--grain expects a natural number"
  | "--max-depth" :: n :: rest, args =>
      match n.toNat? with
      | some maxDepth =>
          .ok (some (rest, { args with config := { args.config with maxDepth := maxDepth } }))
      | none => .error s!"--max-depth expects a natural number, got {n}"
  | "--max-depth" :: [], _ =>
      .error "--max-depth expects a natural number"
  | "--diagnostics" :: rest, args =>
      .ok (some (rest, withDiagnostics args))
  | "--diagnostics-output" :: "console" :: rest, args =>
      .ok (some (rest, withDiagnosticsOutput args DiagnosticsOutput.console))
  | "--diagnostics-output" :: "stderr" :: rest, args =>
      .ok (some (rest, withDiagnosticsOutput args DiagnosticsOutput.stderr))
  | "--diagnostics-output" :: "stdout" :: rest, args =>
      .ok (some (rest, withDiagnosticsOutput args DiagnosticsOutput.stdout))
  | "--diagnostics-output" :: value :: _, _ =>
      .error s!"--diagnostics-output expects console, stderr, or stdout, got {value}"
  | "--diagnostics-output" :: [], _ =>
      .error "--diagnostics-output expects console, stderr, or stdout"
  | "--help" :: _, args =>
      .ok (some ([], { args with help := true }))
  | _, _ =>
      .ok none

def validate (args : ReducerArgs) : Except String Unit :=
  if args.baseline && args.config.diagnostics.enabled then
    .error "--diagnostics is only available for the parallel ReducerPar implementation"
  else
    .ok ()

end ReducerArgs
end Examples

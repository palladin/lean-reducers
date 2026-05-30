import Init.Data.String.Basic

namespace LeanReducers
namespace Internal

private def newlineByte : UInt8 :=
  10

@[inline]
private def extractLine (text : String) (start stop : Nat) : String :=
  text.extract (text.pos! ⟨start⟩) (text.pos! ⟨stop⟩)

-- Newline is ASCII, so byte scanning still produces valid UTF-8 extraction boundaries.
private partial def foldLinesRightAux (text : String) (bytes : ByteArray) (stop idx : Nat) (unit : ρ)
    (step : String → ρ → ρ) : ρ :=
  if idx == 0 then
    step (extractLine text 0 stop) unit
  else
    let idx := idx - 1
    if bytes.get! idx == newlineByte then
      foldLinesRightAux text bytes idx idx (step (extractLine text (idx + 1) stop) unit) step
    else
      foldLinesRightAux text bytes stop idx unit step

def foldLinesRight (text : String) (unit : ρ) (step : String → ρ → ρ)
    (dropTrailingEmpty : Bool := false) : ρ :=
  let bytes := text.toByteArray
  let stop :=
    if dropTrailingEmpty && bytes.size > 0 && bytes.get! (bytes.size - 1) == newlineByte then
      bytes.size - 1
    else
      bytes.size
  foldLinesRightAux text bytes stop stop unit step

end Internal
end LeanReducers

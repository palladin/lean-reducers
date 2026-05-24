import LeanReducers.Algebra

namespace LeanReducers

/--
Internal fold description used at runtime. Lawful public folds are constructed
from `MonoidSpec`; approximate folds such as floating-point reductions use the
same runtime path without claiming algebraic laws.
-/
structure FoldSpec (α : Type) (ρ : Type) where
  unit : ρ
  combine : ρ → ρ → ρ
  step : α → ρ → ρ

namespace FoldSpec

def ofMonoid (spec : MonoidSpec ρ) (step : α → ρ → ρ) : FoldSpec α ρ where
  unit := spec.unit
  combine := spec.combine
  step := step

end FoldSpec

end LeanReducers

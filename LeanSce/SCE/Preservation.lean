import LeanSce.SCE.Elaboration
import LeanSce.SCE.SmallStep
import LeanSce.SCE.Syntax

-- Generalized preservation: SCE small steps preserve elaboration types
theorem sgpreservation
    {e e' v : SCE.Exp}
    (hstep : SStep v e e') :
    ∀ {Γ A : SCE.Typ},
    (∃ ce, elabExp Γ e A ce)
    → SCE.Value v
    → (∃ ρc, elabExp SCE.Typ.top v Γ ρc)
    → ∃ ce', elabExp Γ e' A ce' := by
  sorry


-- Whole-program preservation
theorem spreservation {e e' : SCE.Exp} {A : SCE.Typ}
    : (∃ ce, elabExp SCE.Typ.top e A ce)
    → SStep SCE.Exp.unit e e'
    → ∃ ce', elabExp SCE.Typ.top e' A ce' := by
  sorry

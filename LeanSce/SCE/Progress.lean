import LeanSce.SCE.Elaboration
import LeanSce.SCE.SmallStep
import LeanSce.SCE.Syntax

-- Generalized progress: well-elaborated expressions are values or can step
theorem sgprogress
    {Γ A : SCE.Typ} {e : SCE.Exp}
    (htyp : ∃ ce, elabExp Γ e A ce) :
    ∀ {v : SCE.Exp},
    SCE.Value v
    → (∃ ρc, elabExp SCE.Typ.top v Γ ρc)
    → SCE.Value e ∨ ∃ e', SStep v e e' := by
  sorry


-- Whole-program progress
theorem sprogress {e : SCE.Exp} {A : SCE.Typ}
    : (∃ ce, elabExp SCE.Typ.top e A ce)
    → SCE.Value e ∨ ∃ e', SStep SCE.Exp.unit e e' := by
  sorry

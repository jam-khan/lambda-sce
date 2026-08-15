import LeanSce.Seal.Typing

-- Small-step semantics of λE^≤: the ternary environment-passing relation of the Core
-- mechanization (per-construct congruence rules, no frames).  New relative to λE: the
-- sanno/sannov rules for the sealing primitive, and the cast premise + result reseal in
-- sbeta (both ported from Eᵢ).
namespace Seal

inductive Step : Exp → Exp → Exp → Prop where
  | squery {v}
    : Value v
    → Step v .query v
  | sappl {v e₁ e₁' e₂}
    : Value v
    → Step v e₁ e₁'
    → Step v (.app e₁ e₂) (.app e₁' e₂)
  | sappr {v v₁ e₂ e₂'}
    : Value v
    → Value v₁
    → Step v e₂ e₂'
    → Step v (.app v₁ e₂) (.app v₁ e₂')
  | sbeta {v v₁ A B e v₂ v₂'}
    : Value v
    → Value v₁
    → Value v₂
    → Cast v₂ A v₂'
    → Step v (.app (.clos v₁ A B e) v₂) (.box (.mrg v₁ v₂') (.anno e B))
  | sclos {v A B e}
    : Value v
    → Step v (.lam A B e) (.clos v A B e)
  | sboxl {v e₁ e₁' e₂}
    : Value v
    → Step v e₁ e₁'
    → Step v (.box e₁ e₂) (.box e₁' e₂)
  | sboxr {v v₁ e₂ e₂'}
    : Value v
    → Value v₁
    → Step v₁ e₂ e₂'
    → Step v (.box v₁ e₂) (.box v₁ e₂')
  | sboxv {v v₁ v₂}
    : Value v
    → Value v₁
    → Value v₂
    → Step v (.box v₁ v₂) v₂
  | smrgl {v e₁ e₁' e₂}
    : Value v
    → Step v e₁ e₁'
    → Step v (.mrg e₁ e₂) (.mrg e₁' e₂)
  | smrgr {v v₁ e₂ e₂'}
    : Value v
    → Value v₁
    → Step (.mrg v v₁) e₂ e₂'
    → Step v (.mrg v₁ e₂) (.mrg v₁ e₂')
  | sproj {v e e' n}
    : Value v
    → Step v e e'
    → Step v (.proj e n) (.proj e' n)
  | sprojv {v v₁ v' n}
    : Value v
    → Value v₁
    → LookupV v₁ n v'
    → Step v (.proj v₁ n) v'
  | slrec {v e e' l}
    : Value v
    → Step v e e'
    → Step v (.lrec l e) (.lrec l e')
  | srproj {v e e' l}
    : Value v
    → Step v e e'
    → Step v (.rproj e l) (.rproj e' l)
  | srprojv {v v₁ v' l}
    : Value v
    → Value v₁
    → RLookupV v₁ l v'
    → Step v (.rproj v₁ l) v'
  | sanno {v e e' A}
    : Value v
    → Step v e e'
    → Step v (.anno e A) (.anno e' A)
  | sannov {v v₁ v' A}
    : Value v
    → Value v₁
    → Cast v₁ A v'
    → Step v (.anno v₁ A) v'

inductive MStep : Exp → Exp → Exp → Prop where
  | refl {v e}
    : MStep v e e
  | step {v e₁ e₂ e₃}
    : Step v e₁ e₂
    → MStep v e₂ e₃
    → MStep v e₁ e₃

theorem mstep_trans {v e₁ e₂ e₃ : Exp} (h₁ : MStep v e₁ e₂) (h₂ : MStep v e₂ e₃)
    : MStep v e₁ e₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact MStep.step hs (ih h₂)

theorem mstep_one {v e₁ e₂ : Exp} (h : Step v e₁ e₂) : MStep v e₁ e₂ :=
  MStep.step h MStep.refl

-- Values do not step (in any environment — the merge congruence changes the environment,
-- so the quantifier must stay inside the induction).
theorem value_not_step {e : Exp} (hv : Value e) : ∀ {v e' : Exp}, Step v e e' → False := by
  induction hv with
  | vint => intro _ _ h; nomatch h
  | vunit => intro _ _ h; nomatch h
  | vclos _ => intro _ _ h; nomatch h
  | vrcd _ ih => intro _ _ h; cases h with | slrec _ hs => exact ih hs
  | vmrg _ _ ih₁ ih₂ =>
    intro _ _ h
    cases h with
    | smrgl _ hs => exact ih₁ hs
    | smrgr _ _ hs => exact ih₂ hs

theorem mstep_value_eq {v e e' : Exp} (hv : Value e) (h : MStep v e e') : e = e' := by
  cases h with
  | refl => rfl
  | step hs _ => exact absurd hs (fun hs' => value_not_step hv hs')

end Seal

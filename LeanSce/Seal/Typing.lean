import LeanSce.Seal.Casting

-- The type system of λE^≤.  Syntax-directed: no subsumption rule.  Subtyping enters at
-- exactly three points — tanno (the sealing rule), and the two runtime slacks of tclos
-- (input widening C <: A and body-result B' <: B), which are what preservation of
-- Casting-arrow requires.  Merge typing carries Eᵢ's disjointness side conditions; tmergev
-- is Eᵢ's runtime rule for consistent value merges (needed for value closedness).
namespace Seal

inductive HasType : Typ → Exp → Typ → Prop where
  | tquery {Γ : Typ}
    : HasType Γ .query Γ
  | tint {Γ : Typ} {i : Nat}
    : HasType Γ (.lit i) .int
  | tunit {Γ : Typ}
    : HasType Γ .unit .top
  | tapp {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ (.arr A B)
    → HasType Γ e₂ A
    → HasType Γ (.app e₁ e₂) B
  | tbox {Γ Γ₁ A : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ Γ₁
    → HasType Γ₁ e₂ A
    → HasType Γ (.box e₁ e₂) A
  | tproj {Γ A B : Typ} {e : Exp} {n : Nat}
    : HasType Γ e B
    → Lookup B n A
    → HasType Γ (.proj e n) A
  | trcd {Γ A : Typ} {l : String} {e : Exp}
    : HasType Γ e A
    → HasType Γ (.lrec l e) (.rcd l A)
  | trproj {Γ A B : Typ} {l : String} {e : Exp}
    : HasType Γ e B
    → RLookup B l A
    → HasType Γ (.rproj e l) A
  | tmrg {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ A
    → HasType (.and Γ A) e₂ B
    → Disj A Γ
    → Disj A B
    → HasType Γ (.mrg e₁ e₂) (.and A B)
  | tmergev {Γ A B : Typ} {v₁ v₂ : Exp}
    : Value v₁
    → Value v₂
    → HasType .top v₁ A
    → HasType .top v₂ B
    → Consistent v₁ v₂
    → HasType Γ (.mrg v₁ v₂) (.and A B)
  | tlam {Γ A B : Typ} {e : Exp}
    : Disj Γ A
    → HasType (.and Γ A) e B
    → HasType Γ (.lam A B e) (.arr A B)
  | tclos {Γ Γ₁ A B B' C : Typ} {v e : Exp}
    : Value v
    → HasType .top v Γ₁
    → Disj Γ₁ A
    → HasType (.and Γ₁ A) e B'
    → Sub B' B
    → Sub C A
    → HasType Γ (.clos v A B e) (.arr C B)
  | tanno {Γ A B : Typ} {e : Exp}
    : HasType Γ e B
    → Sub B A
    → HasType Γ (.anno e A) A

end Seal

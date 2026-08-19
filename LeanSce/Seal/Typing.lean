import LeanSce.Seal.Casting

-- The type system of λE^≤.  Syntax-directed: no subsumption rule.  Subtyping enters at
-- exactly three points — tanno (the sealing rule), and the two runtime slacks of tclos
-- (input widening C <: A and body-result B' <: B), which are what preservation of
-- Casting-arrow requires.  Merge typing carries Eᵢ's disjointness side conditions; tmergev
-- is Eᵢ's runtime rule for consistent value merges (needed for value closedness).
--
-- Type abstraction: the judgment carries a brand store Δ (the unit's *knowledge* of
-- representations).  Exactly three rules consult it — twrap, tseal, tunseal — and each
-- requires `Δ n = some R`.  A client typed with `Δ n = none` therefore cannot brand,
-- seal or unseal at α_n; it can only *use* α_n opaquely.  Both a client derivation and a
-- provider derivation weaken to any larger store (`hastype_weaken_store`), which is how
-- the composed program types.
namespace Seal

-- The label under which the coercion proxies (SmallStep: SealV/UnsealV at arrows) store
-- the underlying closure in their environment.  Signatures may not use it, which is what
-- makes the proxy environment disjoint from every signature type (tclos's `Disj Γ₁ A`).
def reservedLabel : String := "#f"

-- `NoRes T`: T does not use the reserved label anywhere.
inductive NoRes : Typ → Prop where
  | int          : NoRes .int
  | top          : NoRes .top
  | brand {n}    : NoRes (.brand n)
  | arr {A B}    : NoRes A → NoRes B → NoRes (.arr A B)
  | rcd {l A}    : l ≠ reservedLabel → NoRes A → NoRes (.rcd l A)
  | and {A B}    : NoRes A → NoRes B → NoRes (.and A B)

-- Signature well-formedness for sealing at S abstracting α_n over R: every intersection
-- inside S is disjoint in *both* views (abstract, so sealed merges re-type via tmergev;
-- and representation, so unsealed merges do), and S does not use the reserved label.
-- Disjointness is not preserved by substitution in either direction (α_n & Int vs
-- Int & Int; α_n & α_n vs ε & ε), hence both conditions.
inductive WfSig (n : Nat) (R : Typ) : Typ → Prop where
  | int          : WfSig n R .int
  | top          : WfSig n R .top
  | brand {m}    : WfSig n R (.brand m)
  | arr {A B}    : WfSig n R A → WfSig n R B → WfSig n R (.arr A B)
  | rcd {l A}    : l ≠ reservedLabel → WfSig n R A → WfSig n R (.rcd l A)
  | and {A B}    : WfSig n R A → WfSig n R B
                   → Disj A B → Disj (substBrand n R A) (substBrand n R B)
                   → WfSig n R (.and A B)

inductive HasType : BrandStore → Typ → Exp → Typ → Prop where
  | tquery {Δ : BrandStore} {Γ : Typ}
    : HasType Δ Γ .query Γ
  | tint {Δ : BrandStore} {Γ : Typ} {i : Nat}
    : HasType Δ Γ (.lit i) .int
  | tunit {Δ : BrandStore} {Γ : Typ}
    : HasType Δ Γ .unit .top
  | tapp {Δ : BrandStore} {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Δ Γ e₁ (.arr A B)
    → HasType Δ Γ e₂ A
    → HasType Δ Γ (.app e₁ e₂) B
  | tbox {Δ : BrandStore} {Γ Γ₁ A : Typ} {e₁ e₂ : Exp}
    : HasType Δ Γ e₁ Γ₁
    → HasType Δ Γ₁ e₂ A
    → HasType Δ Γ (.box e₁ e₂) A
  | tproj {Δ : BrandStore} {Γ A B : Typ} {e : Exp} {n : Nat}
    : HasType Δ Γ e B
    → Lookup B n A
    → HasType Δ Γ (.proj e n) A
  | trcd {Δ : BrandStore} {Γ A : Typ} {l : String} {e : Exp}
    : HasType Δ Γ e A
    → HasType Δ Γ (.lrec l e) (.rcd l A)
  | trproj {Δ : BrandStore} {Γ A B : Typ} {l : String} {e : Exp}
    : HasType Δ Γ e B
    → RLookup B l A
    → HasType Δ Γ (.rproj e l) A
  | tmrg {Δ : BrandStore} {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Δ Γ e₁ A
    → HasType Δ (.and Γ A) e₂ B
    → Disj A Γ
    → Disj A B
    → HasType Δ Γ (.mrg e₁ e₂) (.and A B)
  | tmergev {Δ : BrandStore} {Γ A B : Typ} {v₁ v₂ : Exp}
    : Value v₁
    → Value v₂
    → HasType Δ .top v₁ A
    → HasType Δ .top v₂ B
    → Consistent v₁ v₂
    → HasType Δ Γ (.mrg v₁ v₂) (.and A B)
  | tlam {Δ : BrandStore} {Γ A B : Typ} {e : Exp}
    : Disj Γ A
    → HasType Δ (.and Γ A) e B
    → HasType Δ Γ (.lam A B e) (.arr A B)
  | tclos {Δ : BrandStore} {Γ Γ₁ A B B' C : Typ} {v e : Exp}
    : Value v
    → HasType Δ .top v Γ₁
    → Disj Γ₁ A
    → HasType Δ (.and Γ₁ A) e B'
    → Sub B' B
    → Sub C A
    → HasType Δ Γ (.clos v A B e) (.arr C B)
  | tanno {Δ : BrandStore} {Γ A B : Typ} {e : Exp}
    : HasType Δ Γ e B
    → Sub B A
    → HasType Δ Γ (.anno e A) A
  -- A branded value: the payload is a closed value of the representation type.  This is
  -- the only rule that gives a value type `brand n`, so brands are inhabited exactly by
  -- wrappers (canonical forms).
  | twrap {Δ : BrandStore} {Γ R : Typ} {n : Nat} {v : Exp}
    : Δ n = some R
    → Value v
    → HasType Δ .top v R
    → HasType Δ Γ (.wrap n v) (.brand n)
  -- The sealing coercion S[n:=R] ⇒ S.  Its operand is typed at the *representation view*
  -- of the signature; the result is typed at the abstract view.
  | tseal {Δ : BrandStore} {Γ R S : Typ} {n : Nat} {e : Exp}
    : Δ n = some R
    → NoRes R
    → WfSig n R S
    → HasType Δ Γ e (substBrand n R S)
    → HasType Δ Γ (.seal n R S e) S
  -- The converse coercion S ⇒ S[n:=R], used inside the proxies `seal` builds at arrows.
  -- The result type is a variable guarded by an equation so that dependent elimination
  -- (cases at a concrete type) does not get stuck on substBrand.
  | tunseal {Δ : BrandStore} {Γ R S T : Typ} {n : Nat} {e : Exp}
    : Δ n = some R
    → NoRes R
    → WfSig n R S
    → HasType Δ Γ e S
    → T = substBrand n R S
    → HasType Δ Γ (.unseal n R S e) T

-- Store extension: Δ' knows everything Δ knows.
def StoreLe (Δ Δ' : BrandStore) : Prop := ∀ n R, Δ n = some R → Δ' n = some R

theorem storele_refl {Δ : BrandStore} : StoreLe Δ Δ := fun _ _ h => h

theorem storele_noBrands {Δ : BrandStore} : StoreLe noBrands Δ := fun _ _ h => nomatch h

-- Typing is monotone in the store: a derivation under Δ is a derivation under any Δ' ⊇ Δ.
theorem hastype_weaken_store {Δ Δ' : BrandStore} (hle : StoreLe Δ Δ') {Γ : Typ} {e : Exp}
    {A : Typ} (ht : HasType Δ Γ e A) : HasType Δ' Γ e A := by
  induction ht with
  | tquery => exact HasType.tquery
  | tint => exact HasType.tint
  | tunit => exact HasType.tunit
  | tapp _ _ ih₁ ih₂ => exact HasType.tapp ih₁ ih₂
  | tbox _ _ ih₁ ih₂ => exact HasType.tbox ih₁ ih₂
  | tproj _ hl ih => exact HasType.tproj ih hl
  | trcd _ ih => exact HasType.trcd ih
  | trproj _ hl ih => exact HasType.trproj ih hl
  | tmrg _ _ hd₁ hd₂ ih₁ ih₂ => exact HasType.tmrg ih₁ ih₂ hd₁ hd₂
  | tmergev hv₁ hv₂ _ _ hc ih₁ ih₂ => exact HasType.tmergev hv₁ hv₂ ih₁ ih₂ hc
  | tlam hd _ ih => exact HasType.tlam hd ih
  | tclos hv _ hd _ hs₁ hs₂ ih₁ ih₂ => exact HasType.tclos hv ih₁ hd ih₂ hs₁ hs₂
  | tanno _ hs ih => exact HasType.tanno ih hs
  | twrap hΔ hv _ ih => exact HasType.twrap (hle _ _ hΔ) hv ih
  | tseal hΔ hnr hwf _ ih => exact HasType.tseal (hle _ _ hΔ) hnr hwf ih
  | tunseal hΔ hnr hwf _ heq ih => exact HasType.tunseal (hle _ _ hΔ) hnr hwf ih heq

end Seal

import LeanSce.Seal.Lookup

-- Generalized progress for λE^≤ (λE Theorem 4.8 + Eᵢ Theorem 13's casting cases).
-- The new redexes: (v : A) fires by progress of casting (the typing rule guarantees the
-- value's type sits below the annotation), and beta's argument-cast fires because the
-- closure's input slack C <: A₀ composes with the argument's typing.
namespace Seal

theorem gprogress {Γ A : Typ} {e : Exp} (ht : HasType Γ e A)
    {v : Exp} (hv : Value v) (henv : HasType .top v Γ)
    : Value e ∨ ∃ e', Step v e e' := by
  induction ht generalizing v with
  | tquery => exact Or.inr ⟨_, Step.squery hv⟩
  | tint => exact Or.inl Value.vint
  | tunit => exact Or.inl Value.vunit
  | tapp h₁ h₂ ih₁ ih₂ =>
    cases ih₁ hv henv with
    | inr hs =>
      obtain ⟨e₁', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sappl hv hs'⟩
    | inl hv₁ =>
      cases ih₂ hv henv with
      | inr hs =>
        obtain ⟨e₂', hs'⟩ := hs
        exact Or.inr ⟨_, Step.sappr hv hv₁ hs'⟩
      | inl hv₂ =>
        cases h₁ with
        | tclos _ _ _ _ _ hs₂ =>
          obtain ⟨v₂', hc⟩ := cast_progress hv₂ h₂ hs₂
          cases hv₁ with
          | vclos hu => exact Or.inr ⟨_, Step.sbeta hv hu hv₂ hc⟩
        | tquery => nomatch hv₁
        | tapp _ _ => nomatch hv₁
        | tbox _ _ => nomatch hv₁
        | tproj _ _ => nomatch hv₁
        | trproj _ _ => nomatch hv₁
        | tanno _ _ => nomatch hv₁
        | tlam _ _ => nomatch hv₁
  | tbox h₁ _ ih₁ ih₂ =>
    cases ih₁ hv henv with
    | inr hs =>
      obtain ⟨e₁', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sboxl hv hs'⟩
    | inl hv₁ =>
      cases ih₂ hv₁ (value_weaken h₁ hv₁) with
      | inr hs =>
        obtain ⟨e₂', hs'⟩ := hs
        exact Or.inr ⟨_, Step.sboxr hv hv₁ hs'⟩
      | inl hv₂ => exact Or.inr ⟨_, Step.sboxv hv hv₁ hv₂⟩
  | tproj h hl ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sproj hv hs'⟩
    | inl hve =>
      obtain ⟨v', hlv⟩ := lookup_prog hl hve h
      exact Or.inr ⟨_, Step.sprojv hv hve hlv⟩
  | trcd _ ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.slrec hv hs'⟩
    | inl hve => exact Or.inl (Value.vrcd hve)
  | trproj h hl ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.srproj hv hs'⟩
    | inl hve =>
      obtain ⟨v', hlv⟩ := rlookup_prog hl hve h
      exact Or.inr ⟨_, Step.srprojv hv hve hlv⟩
  | tmrg h₁ _ hd₁ _ ih₁ ih₂ =>
    cases ih₁ hv henv with
    | inr hs =>
      obtain ⟨e₁', hs'⟩ := hs
      exact Or.inr ⟨_, Step.smrgl hv hs'⟩
    | inl hv₁ =>
      cases ih₂ (Value.vmrg hv hv₁) (env_extend_typing hv hv₁ henv h₁ hd₁) with
      | inr hs =>
        obtain ⟨e₂', hs'⟩ := hs
        exact Or.inr ⟨_, Step.smrgr hv hv₁ hs'⟩
      | inl hv₂ => exact Or.inl (Value.vmrg hv₁ hv₂)
  | tmergev hv₁ hv₂ _ _ _ _ _ => exact Or.inl (Value.vmrg hv₁ hv₂)
  | tlam _ _ _ => exact Or.inr ⟨_, Step.sclos hv⟩
  | tclos hu _ _ _ _ _ _ _ => exact Or.inl (Value.vclos hu)
  | tanno h hsub ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sanno hv hs'⟩
    | inl hve =>
      obtain ⟨w, hc⟩ := cast_progress hve h hsub
      exact Or.inr ⟨_, Step.sannov hv hve hc⟩

-- Whole-program corollary.
theorem progress {e : Exp} {A : Typ} (ht : HasType .top e A)
    : Value e ∨ ∃ e', Step .unit e e' :=
  gprogress ht Value.vunit HasType.tunit

end Seal

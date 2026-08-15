import LeanSce.Seal.Lookup

-- Generalized preservation for λE^≤ (λE Theorem 4.9 + the casting premises of Eᵢ
-- Theorem 14).  The genuinely new cases: sbeta re-types the extended closure environment
-- via tmergev + disjointness-implies-consistency (never via tmrg), and sannov is exactly
-- preservation of casting.
namespace Seal

theorem gpreservation {venv e e' : Exp} (hstep : Step venv e e')
    {Γ A : Typ} (ht : HasType Γ e A) (henv : HasType .top venv Γ)
    : HasType Γ e' A := by
  induction hstep generalizing Γ A with
  | squery hv =>
    cases ht
    exact value_weaken henv hv
  | sappl _ _ ih =>
    cases ht with
    | tapp h₁ h₂ => exact HasType.tapp (ih h₁ henv) h₂
  | sappr _ _ _ ih =>
    cases ht with
    | tapp h₁ h₂ => exact HasType.tapp h₁ (ih h₂ henv)
  | sbeta _ _ hv₂ hc =>
    cases ht with
    | tapp h₁ h₂ =>
      cases h₁ with
      | tclos hu henv₁ hd hb hs₁ _ =>
        have hv₂' := cast_value hv₂ hc
        have ht₂' : HasType .top _ _ := value_weaken (cast_preservation hc hv₂ h₂) hv₂'
        exact HasType.tbox
          (HasType.tmergev hu hv₂' henv₁ ht₂'
            (disjoint_consistent hu hv₂' henv₁ ht₂' hd))
          (HasType.tanno hb hs₁)
  | sclos hv =>
    cases ht with
    | tlam hd hb =>
      exact HasType.tclos hv (value_weaken henv hv) hd hb (sub_refl _) (sub_refl _)
  | sboxl _ _ ih =>
    cases ht with
    | tbox h₁ h₂ => exact HasType.tbox (ih h₁ henv) h₂
  | sboxr _ hv₁ _ ih =>
    cases ht with
    | tbox h₁ h₂ => exact HasType.tbox h₁ (ih h₂ (value_weaken h₁ hv₁))
  | sboxv _ _ hv₂ =>
    cases ht with
    | tbox h₁ h₂ => exact value_weaken h₂ hv₂
  | smrgl _ hs ih =>
    cases ht with
    | tmrg h₁ h₂ hd₁ hd₂ => exact HasType.tmrg (ih h₁ henv) h₂ hd₁ hd₂
    | tmergev hva _ _ _ _ => exact (value_not_step hva hs).elim
  | smrgr hv hv₁ hs ih =>
    cases ht with
    | tmrg h₁ h₂ hd₁ hd₂ =>
      exact HasType.tmrg h₁ (ih h₂ (env_extend_typing hv hv₁ henv h₁ hd₁)) hd₁ hd₂
    | tmergev _ hvb _ _ _ => exact (value_not_step hvb hs).elim
  | sproj _ _ ih =>
    cases ht with
    | tproj h hl => exact HasType.tproj (ih h henv) hl
  | sprojv _ hv₁ hlv =>
    cases ht with
    | tproj h hl => exact lookup_pres hl hv₁ h hlv
  | slrec _ _ ih =>
    cases ht with
    | trcd h => exact HasType.trcd (ih h henv)
  | srproj _ _ ih =>
    cases ht with
    | trproj h hl => exact HasType.trproj (ih h henv) hl
  | srprojv _ hv₁ hlv =>
    cases ht with
    | trproj h hl => exact rlookup_pres hl hv₁ h hlv
  | sanno _ _ ih =>
    cases ht with
    | tanno h hsub => exact HasType.tanno (ih h henv) hsub
  | sannov _ hv₁ hc =>
    cases ht with
    | tanno h _ => exact cast_preservation hc hv₁ h

-- Whole-program corollary.
theorem preservation {e e' : Exp} {A : Typ} (ht : HasType .top e A)
    (hstep : Step .unit e e') : HasType .top e' A :=
  gpreservation hstep ht HasType.tunit

theorem mstep_preservation {venv e e' : Exp} (hstep : MStep venv e e')
    {Γ A : Typ} (ht : HasType Γ e A) (henv : HasType .top venv Γ)
    : HasType Γ e' A := by
  induction hstep generalizing A with
  | refl => exact ht
  | step hs _ ih => exact ih (gpreservation hs ht henv)

end Seal

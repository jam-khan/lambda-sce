import LeanSce.SCE.Theories
import LeanSce.SCE.Preservation
import LeanSce.SCE.Progress

open SCE S_Sem

-- Source-side determinism and uniqueness, re-witnessed by the sealing elaboration
-- (elabSeal, SCE → λE^≤).  Supersedes the elabExp-witnessed half of SCE/Theories.lean
-- (inference/elaboration_uniqueness, sel/selpkg_deterministic, bigstep_deterministic),
-- which will be deleted together with LeanSce/Core.

namespace Seal

variable {Δ : SCE.BrandStore}

-- ── Uniqueness of inference and elaboration, in one pass ─────────────────────────────

-- The two elabExp uniqueness theorems merged: the inferred type and the elaborated term
-- are unique.  The statement is generalized over the two contexts, equal OR the subject
-- a value (value elaborations are context-irrelevant): this is exactly what the mixed
-- edmrg/evmrg inversions of a value merge need.
theorem elabSeal_uniqueness {Γ₁ : SCE.Typ} {e : SCE.Exp} {T₁ : SCE.Typ} {ce₁ : Seal.Exp}
    (h₁ : elabSeal Δ Γ₁ e T₁ ce₁)
    : ∀ {Γ₂ T₂ : SCE.Typ} {ce₂ : Seal.Exp}, elabSeal Δ Γ₂ e T₂ ce₂
    → (Γ₁ = Γ₂ ∨ SCE.Value e)
    → T₁ = T₂ ∧ ce₁ = ce₂ := by
  induction h₁ with
  | equery =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂
    exact ⟨rfl, rfl⟩
  | elit _ _ =>
    intro Γ₂ T₂ ce₂ h₂ _
    cases h₂
    exact ⟨rfl, rfl⟩
  | eunit _ =>
    intro Γ₂ T₂ ce₂ h₂ _
    cases h₂
    exact ⟨rfl, rfl⟩
  | eapp h1 h2 ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | eapp h1' h2' =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hce2
      exact ⟨rfl, rfl⟩
  | eproj h1 hlook ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | eproj h1' hlook' =>
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hT; cases hce
      exact ⟨index_lookup_uniqueness hlook hlook', rfl⟩
  | ebox h1 h2 ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | ebox h1' h2' =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | @edmrg ctx A _ se₁ se₂ _ _ h1 h2 hd1 hd2 ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | edmrg h1' h2' _ _ =>
      have hc1 : ctx = Γ₂ ∨ SCE.Value se₁ := by
        rcases hctx with rfl | hval
        · exact Or.inl rfl
        · cases hval with | vmrg hv1 _ => exact Or.inr hv1
      obtain ⟨hT, hce⟩ := ih1 h1' hc1
      cases hT; cases hce
      have hc2 : SCE.Typ.and ctx A = .and Γ₂ A ∨ SCE.Value se₂ := by
        rcases hctx with rfl | hval
        · exact Or.inl rfl
        · cases hval with | vmrg _ hv2 => exact Or.inr hv2
      obtain ⟨hT2, hce2⟩ := ih2 h2' hc2
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
    | evmrg hv1 hv2 h1' h2' _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inr hv1)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inr hv2)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | evmrg hv1 hv2 h1 h2 hd ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | edmrg h1' h2' _ _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inr hv1)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inr hv2)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
    | evmrg _ _ h1' h2' _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | enmrg h1 h2 hd1 hd2 ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | enmrg h1' h2' _ _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | elam h1 hd ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | elam h1' _ =>
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hT; cases hce
      exact ⟨rfl, rfl⟩
  | erproj h1 hlook ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | erproj h1' hlook' =>
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hT; cases hce
      exact ⟨record_lookup_uniqueness hlook hlook', rfl⟩
  | eclos hval h1 h2 hd ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | eclos _ h1' h2' _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | @elrec ctx _ se _ _ h1 ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | elrec h1' =>
      have hc : ctx = Γ₂ ∨ SCE.Value se := by
        rcases hctx with rfl | hval
        · exact Or.inl rfl
        · cases hval with | vlrec hv => exact Or.inr hv
      obtain ⟨hT, hce⟩ := ih h1' hc
      cases hT; cases hce
      exact ⟨rfl, rfl⟩
  | eletb h1 h2 hd ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | eletb h1' h2' _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | eopenm h1 h2 hd ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | eopenm h1' h2' _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | @einl ctx _ _ se _ h1 ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | einl h1' =>
      have hc : ctx = Γ₂ ∨ SCE.Value se := by
        rcases hctx with rfl | hval
        · exact Or.inl rfl
        · cases hval with | vinl hv => exact Or.inr hv
      obtain ⟨hT, hce⟩ := ih h1' hc
      cases hT; cases hce
      exact ⟨rfl, rfl⟩
  | @einr ctx _ _ se _ h1 ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | einr h1' =>
      have hc : ctx = Γ₂ ∨ SCE.Value se := by
        rcases hctx with rfl | hval
        · exact Or.inl rfl
        · cases hval with | vinr hv => exact Or.inr hv
      obtain ⟨hT, hce⟩ := ih h1' hc
      cases hT; cases hce
      exact ⟨rfl, rfl⟩
  | ecase h h1 h2 hd1 hd2 ih ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | ecase h' h1' h2' _ _ =>
      obtain ⟨hT, hce⟩ := ih h' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT1, hce1⟩ := ih1 h1' (Or.inl rfl)
      cases hT1; cases hce1
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hce2
      exact ⟨rfl, rfl⟩
  | eflam h1 hd1 hd2 ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | eflam h1' _ _ =>
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hce
      exact ⟨rfl, rfl⟩
  | efclos hval h1 h2 hd1 hd2 ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | efclos _ h1' h2' _ _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hce2
      exact ⟨rfl, rfl⟩
  | @efold ctx _ se _ h1 ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | efold h1' =>
      have hc : ctx = Γ₂ ∨ SCE.Value se := by
        rcases hctx with rfl | hval
        · exact Or.inl rfl
        · cases hval with | vfold hv => exact Or.inr hv
      obtain ⟨hT, hce⟩ := ih h1' hc
      cases hce
      exact ⟨rfl, rfl⟩
  | eunfold h1 heq ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | eunfold h1' heq' =>
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hT; cases hce
      subst heq; subst heq'
      exact ⟨rfl, rfl⟩
  | @emstruct _ ctxInner _ sb _ _ hsb hop h1 ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | @emstruct _ ctxInner' _ _ _ _ hsb' hop' h1' =>
      have hCtx : ctxInner = ctxInner' := by
        cases sb with
        | sandboxed => rw [hsb rfl, hsb' rfl]
        | open_ => rw [hop rfl, hop' rfl]
      subst hCtx
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hT; cases hce
      exact ⟨rfl, rfl⟩
  | @emfunctor _ ctxInner _ _ sb _ _ hsb hop hdop h1 ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | @emfunctor _ ctxInner' _ _ _ _ _ hsb' hop' _ h1' =>
      have hCtx : ctxInner = ctxInner' := by
        cases sb with
        | sandboxed => rw [hsb rfl, hsb' rfl]
        | open_ => rw [hop rfl, hop' rfl]
      subst hCtx
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hT; cases hce
      exact ⟨rfl, rfl⟩
  | emclos hval h1 h2 hd ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | emclos _ h1' h2' _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | emapp h1 h2 ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | emapp h1' h2' =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hce2
      exact ⟨rfl, rfl⟩
  | emlink h1 h2 hlook hd1 hd2 ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | emlink h1' h2' _ _ _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | emlinkn h1 h2 hwire hd1 hd2 ih1 ih2 =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | emlinkn h1' h2' _ _ _ =>
      obtain ⟨hT, hce⟩ := ih1 h1' (Or.inl rfl)
      cases hT; cases hce
      obtain ⟨hT2, hce2⟩ := ih2 h2' (Or.inl rfl)
      cases hT2; cases hce2
      exact ⟨rfl, rfl⟩
  | ewrap hΔ hval h1 ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    cases h₂ with
    | ewrap hΔ' _ h1' =>
      rw [hΔ] at hΔ'
      cases hΔ'
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hce
      exact ⟨rfl, rfl⟩
  | emseal hΔ hnr hwf h1 ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | emseal _ _ _ h1' =>
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hce
      exact ⟨rfl, rfl⟩
  | emunseal hΔ hnr hwf h1 heq ih =>
    intro Γ₂ T₂ ce₂ h₂ hctx
    obtain rfl : _ = Γ₂ := hctx.elim id fun hv => nomatch hv
    cases h₂ with
    | emunseal _ _ _ h1' heq' =>
      obtain ⟨hT, hce⟩ := ih h1' (Or.inl rfl)
      cases hce
      subst heq; subst heq'
      exact ⟨rfl, rfl⟩

-- ── Selection determinism (feeds label-disjointness through the elaboration) ─────────

-- A successful selection witnesses containment in the elaborated type.
theorem source_sel_labelin {v v' : SCE.Exp} {l : String} (hsel : S_Sem.Sel v l v')
    : ∀ {Γ A : SCE.Typ} {ce : Seal.Exp}, SCE.Value v → elabSeal Δ Γ v A ce
    → SCE.LabelIn l A := by
  induction hsel with
  | rcd =>
    intro Γ A ce hval helab
    cases helab with
    | elrec _ => exact SCE.LabelIn.rcd _ _
  | dmrg_left _ ih =>
    intro Γ A ce hval helab
    cases hval with
    | vmrg hv1 hv2 =>
      cases helab with
      | edmrg h1 _ _ _ => exact SCE.LabelIn.andl _ _ _ (ih hv1 h1)
      | evmrg _ _ h1 _ _ => exact SCE.LabelIn.andl _ _ _ (ih hv1 h1)
  | dmrg_right _ ih =>
    intro Γ A ce hval helab
    cases hval with
    | vmrg hv1 hv2 =>
      cases helab with
      | edmrg _ h2 _ _ => exact SCE.LabelIn.andr _ _ _ (ih hv2 h2)
      | evmrg _ _ _ h2 _ => exact SCE.LabelIn.andr _ _ _ (ih hv2 h2)
  | nmrg_left _ _ =>
    intro Γ A ce hval _
    nomatch hval
  | nmrg_right _ _ =>
    intro Γ A ce hval _
    nomatch hval

private theorem source_lookupv_det {v v₁ v₂ : SCE.Exp} {n : Nat}
    (h₁ : S_Sem.LookupV v n v₁) (h₂ : S_Sem.LookupV v n v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | dmrg_zero => cases h₂ with | dmrg_zero => rfl
  | dmrg_succ _ ih => cases h₂ with | dmrg_succ h₂' => exact ih h₂'
  | nmrg_zero => cases h₂ with | nmrg_zero => rfl
  | nmrg_succ _ ih => cases h₂ with | nmrg_succ h₂' => exact ih h₂'

-- Selection at a looked-up label is deterministic on well-elaborated values: the
-- SRLookup's negative premises exclude the other component.
theorem source_sel_det {v v₁ : SCE.Exp} {l : String} (hsel₁ : S_Sem.Sel v l v₁)
    : ∀ {Γ A B : SCE.Typ} {ce : Seal.Exp} {v₂ : SCE.Exp},
    SCE.Value v → elabSeal Δ Γ v A ce → SCE.SRLookup A l B → S_Sem.Sel v l v₂
    → v₁ = v₂ := by
  induction hsel₁ with
  | rcd =>
    intro Γ A B ce v₂ hval helab hlookup hsel₂
    cases helab with
    | elrec _ =>
      cases hsel₂ with
      | rcd => rfl
  | @dmrg_left va vb v' l' hsel_inner ih =>
    intro Γ A B ce v₂ hval helab hlookup hsel₂
    cases hval with
    | vmrg hv1 hv2 =>
      have hg : ∃ Γa Γb Aa Ab wa wb, elabSeal Δ Γa va Aa wa ∧ elabSeal Δ Γb vb Ab wb
          ∧ A = .and Aa Ab := by
        cases helab with
        | edmrg h1 h2 _ _ => exact ⟨_, _, _, _, _, _, h1, h2, rfl⟩
        | evmrg _ _ h1 h2 _ => exact ⟨_, _, _, _, _, _, h1, h2, rfl⟩
      obtain ⟨Γa, Γb, Aa, Ab, wa, wb, h1, h2, rfl⟩ := hg
      cases hlookup with
      | andl _ _ _ _ hrl hcond =>
        cases hsel₂ with
        | dmrg_left hsel₂' => exact ih hv1 h1 hrl hsel₂'
        | dmrg_right hsel₂' => exact absurd (source_sel_labelin hsel₂' hv2 h2) hcond
      | andr _ _ _ _ hrl hcond =>
        exact absurd (source_sel_labelin hsel_inner hv1 h1) hcond
  | @dmrg_right va vb v' l' hsel_inner ih =>
    intro Γ A B ce v₂ hval helab hlookup hsel₂
    cases hval with
    | vmrg hv1 hv2 =>
      have hg : ∃ Γa Γb Aa Ab wa wb, elabSeal Δ Γa va Aa wa ∧ elabSeal Δ Γb vb Ab wb
          ∧ A = .and Aa Ab := by
        cases helab with
        | edmrg h1 h2 _ _ => exact ⟨_, _, _, _, _, _, h1, h2, rfl⟩
        | evmrg _ _ h1 h2 _ => exact ⟨_, _, _, _, _, _, h1, h2, rfl⟩
      obtain ⟨Γa, Γb, Aa, Ab, wa, wb, h1, h2, rfl⟩ := hg
      cases hlookup with
      | andr _ _ _ _ hrl hcond =>
        cases hsel₂ with
        | dmrg_right hsel₂' => exact ih hv2 h2 hrl hsel₂'
        | dmrg_left hsel₂' => exact absurd (source_sel_labelin hsel₂' hv1 h1) hcond
      | andl _ _ _ _ hrl hcond =>
        exact absurd (source_sel_labelin hsel_inner hv2 h2) hcond
  | nmrg_left _ _ =>
    intro Γ A B ce v₂ hval _ _ _
    nomatch hval
  | nmrg_right _ _ =>
    intro Γ A B ce v₂ hval _ _ _
    nomatch hval

-- Package extraction is deterministic (one selection per import of the interface).
theorem source_selpkg_det {Γc : Seal.Typ} {Γ₁ D : SCE.Typ} (hok : WireOk Γc Γ₁ D)
    : ∀ {Γ : SCE.Typ} {v : SCE.Exp} {ce : Seal.Exp} {pkg₁ pkg₂ : SCE.Exp},
    SCE.Value v → elabSeal Δ Γ v Γ₁ ce
    → S_Sem.SelPkg v D pkg₁ → S_Sem.SelPkg v D pkg₂
    → pkg₁ = pkg₂ := by
  induction hok with
  | one hrl =>
    intro Γ v ce pkg₁ pkg₂ hval helab hsp₁ hsp₂
    cases hsp₁ with
    | one hsel₁ =>
      cases hsp₂ with
      | one hsel₂ => rw [source_sel_det hsel₁ hval helab hrl hsel₂]
  | more hok' hrl _ _ ih =>
    intro Γ v ce pkg₁ pkg₂ hval helab hsp₁ hsp₂
    cases hsp₁ with
    | more hsp₁' hsel₁ =>
      cases hsp₂ with
      | more hsp₂' hsel₂ =>
        rw [ih hval helab hsp₁' hsp₂', source_sel_det hsel₁ hval helab hrl hsel₂]

end Seal

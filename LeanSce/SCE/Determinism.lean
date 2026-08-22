import LeanSce.SCE.Theories
import LeanSce.SCE.Preservation
import LeanSce.SCE.Progress
import LeanSce.Seal.Correctness

open SCE S_Sem

-- Source-side determinism and uniqueness, witnessed by the sealing elaboration
-- (elabSeal, SCE → λE^≤).

namespace Seal

variable {Δ : SCE.BrandStore}

-- ── Uniqueness of inference and elaboration, in one pass ─────────────────────────────

-- Inference and elaboration uniqueness merged: the inferred type and the elaborated term
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

-- ── Big-step preservation of elaboration ─────────────────────────────────────────────

-- Big-step results of well-elaborated programs still elaborate (at the empty context —
-- results are values).  This is the source-only content of seal_semantic_preservation,
-- proved directly so determinism below does not need the simulation.
theorem source_bigstep_elab_pres {ρ e v : SCE.Exp} (heval : S_Sem.BStep ρ e v)
    : ∀ {Γ A : SCE.Typ} {ce ρc : Seal.Exp},
    elabSeal Δ Γ e A ce → SCE.Value ρ → elabSeal Δ .top ρ Γ ρc
    → ∃ w, elabSeal Δ .top v A w := by
  induction heval with
  | query _ =>
    intro Γ A ce ρc helab hρ henv
    cases helab
    exact ⟨ρc, henv⟩
  | lit _ =>
    intro Γ A ce ρc helab hρ henv
    cases helab
    exact ⟨_, elabSeal.elit .top _⟩
  | unit _ =>
    intro Γ A ce ρc helab hρ henv
    cases helab
    exact ⟨_, elabSeal.eunit .top⟩
  | clos_val _ hv =>
    intro Γ A ce ρc helab hρ henv
    exact ⟨_, elabSeal_weaken helab (SCE.Value.vclos hv) .top⟩
  | mclos_val _ hv =>
    intro Γ A ce ρc helab hρ henv
    exact ⟨_, elabSeal_weaken helab (SCE.Value.vmclos hv) .top⟩
  | proj _ hstep hlook ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | eproj h1 hslook =>
      obtain ⟨w, hw⟩ := ih h1 hρ henv
      exact elabSeal_lookup_pres hslook hw (eval_produces_value hρ hstep) hlook
  | lam _ =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | elam h1 hd => exact ⟨_, elabSeal.eclos hρ henv h1 hd⟩
  | box _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | ebox he1 he2 =>
      obtain ⟨w1, hw1⟩ := ih1 he1 hρ henv
      exact ih2 he2 (eval_produces_value hρ h1) hw1
  | app_clos _ hf ha hb ihf iha ihb =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | eapp he1 he2 =>
      obtain ⟨wf, hwf⟩ := ihf he1 hρ henv
      obtain ⟨wa, hwa⟩ := iha he2 hρ henv
      have hva := eval_produces_value hρ ha
      have hvf := eval_produces_value hρ hf
      cases hvf with
      | vclos hval' =>
        cases hwf with
        | eclos _ ht hb' hd =>
          exact ihb hb' (SCE.Value.vmrg hval' hva)
            (elabSeal.evmrg hval' hva ht hwa hd)
  | app_mclos _ hf ha hb ihf iha ihb =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | emapp he1 he2 =>
      obtain ⟨wf, hwf⟩ := ihf he1 hρ henv
      obtain ⟨wa, hwa⟩ := iha he2 hρ henv
      have hva := eval_produces_value hρ ha
      have hvf := eval_produces_value hρ hf
      cases hvf with
      | vmclos hval' =>
        cases hwf with
        | emclos _ ht hb' hd =>
          exact ihb hb' (SCE.Value.vmrg hval' hva)
            (elabSeal.evmrg hval' hva ht hwa hd)
  | dmrg _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | edmrg he1 he2 hd1 hd2 =>
      obtain ⟨w1, hw1⟩ := ih1 he1 hρ henv
      have hv1 := eval_produces_value hρ h1
      obtain ⟨w2, hw2⟩ := ih2 he2 (SCE.Value.vmrg hρ hv1)
        (elabSeal.evmrg hρ hv1 henv hw1 (disj_symm hd1))
      have hv2 := eval_produces_value (SCE.Value.vmrg hρ hv1) h2
      exact ⟨_, elabSeal.evmrg hv1 hv2 hw1 hw2 hd2⟩
    | evmrg hv1' hv2' he1 he2 hd =>
      have heq1 := bstep_value_id h1 hv1'
      subst heq1
      have heq2 := bstep_value_id h2 hv2'
      subst heq2
      exact ⟨_, elabSeal.evmrg hv1' hv2' he1 he2 hd⟩
  | nmrg _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | enmrg he1 he2 hd1 hd2 =>
      obtain ⟨w1, hw1⟩ := ih1 he1 hρ henv
      obtain ⟨w2, hw2⟩ := ih2 he2 hρ henv
      exact ⟨_, elabSeal.evmrg (eval_produces_value hρ h1) (eval_produces_value hρ h2)
        hw1 hw2 hd2⟩
  | lrec _ _ ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | elrec h1 =>
      obtain ⟨w, hw⟩ := ih h1 hρ henv
      exact ⟨_, elabSeal.elrec hw⟩
  | rproj _ hstep hsel ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | erproj h1 hslook =>
      obtain ⟨w, hw⟩ := ih h1 hρ henv
      exact elabSeal_sel_pres hslook hw (eval_produces_value hρ hstep) hsel
  | letb _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | eletb he1 he2 hd =>
      obtain ⟨w1, hw1⟩ := ih1 he1 hρ henv
      have hv1 := eval_produces_value hρ h1
      exact ih2 he2 (SCE.Value.vmrg hρ hv1) (elabSeal.evmrg hρ hv1 henv hw1 hd)
  | openm _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | eopenm he1 he2 hd =>
      obtain ⟨w1, hw1⟩ := ih1 he1 hρ henv
      have hv1 := eval_produces_value hρ h1
      cases hv1 with
      | vlrec hv' =>
        cases hw1 with
        | elrec hinner =>
          exact ih2 he2 (SCE.Value.vmrg hρ hv') (elabSeal.evmrg hρ hv' henv hinner hd)
  | mstruct_sandboxed _ _ ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | emstruct hsb hop h1 =>
      have heq := hsb rfl; subst heq
      exact ih h1 SCE.Value.vunit (elabSeal.eunit .top)
  | mstruct_open _ _ ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | emstruct hsb hop h1 =>
      have heq := hop rfl; subst heq
      exact ih h1 hρ henv
  | mfunctor_sandboxed _ =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | emfunctor hsb hop hdop h1 =>
      have heq := hsb rfl; subst heq
      exact ⟨_, elabSeal.emclos SCE.Value.vunit (elabSeal.eunit .top) h1 disj_top⟩
  | mfunctor_open _ =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | emfunctor hsb hop hdop h1 =>
      have heq := hop rfl; subst heq
      exact ⟨_, elabSeal.emclos hρ henv h1 (hdop rfl)⟩
  | mlink _ h1 h2 hsel h3 ih1 ih2 ih3 =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | emlink he1 he2 hslook hd1 hd2 =>
      obtain ⟨w1, hw1⟩ := ih1 he1 hρ henv
      have hv1 := eval_produces_value hρ h1
      obtain ⟨wm, hwm⟩ := ih2 he2 hρ henv
      cases hwm with
      | emclos hval2 henv2 hbody hd_mclos =>
        have hvl := S_Sem.sel_value hsel hv1
        obtain ⟨wl, hwl⟩ := elabSeal_sel_pres hslook hw1 hv1 hsel
        obtain ⟨w3, hw3⟩ := ih3 hbody
          (SCE.Value.vmrg hval2 (SCE.Value.vlrec hvl))
          (elabSeal.evmrg hval2 (SCE.Value.vlrec hvl) henv2 (elabSeal.elrec hwl) hd_mclos)
        have hv3 := eval_produces_value (SCE.Value.vmrg hval2 (SCE.Value.vlrec hvl)) h3
        exact ⟨_, elabSeal.evmrg hv1 hv3 hw1 hw3 hd2⟩
  | mlinkn _ h1 h2 hsp h3 ih1 ih2 ih3 =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | emlinkn he1 he2 hwire hd1 hd2 =>
      obtain ⟨w1, hw1⟩ := ih1 he1 hρ henv
      have hv1 := eval_produces_value hρ h1
      obtain ⟨wm, hwm⟩ := ih2 he2 hρ henv
      cases hwm with
      | emclos hval2 henv2 hbody hd_mclos =>
        have hvpkg := S_Sem.selpkg_value hsp hv1
        obtain ⟨wp, hwp⟩ := elabSeal_selpkg_pres hwire hsp hv1 hw1
        obtain ⟨w3, hw3⟩ := ih3 hbody
          (SCE.Value.vmrg hval2 hvpkg)
          (elabSeal.evmrg hval2 hvpkg henv2 hwp hd_mclos)
        have hv3 := eval_produces_value (SCE.Value.vmrg hval2 hvpkg) h3
        exact ⟨_, elabSeal.evmrg hv1 hv3 hw1 hw3 hd2⟩
  | inl _ _ ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | einl h1 =>
      obtain ⟨w, hw⟩ := ih h1 hρ henv
      exact ⟨_, elabSeal.einl hw⟩
  | inr _ _ ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | einr h1 =>
      obtain ⟨w, hw⟩ := ih h1 hρ henv
      exact ⟨_, elabSeal.einr hw⟩
  | case_inl _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | ecase he he1 he2 hd1 hd2 =>
      obtain ⟨w0, hw0⟩ := ih1 he hρ henv
      have hv0 := eval_produces_value hρ h1
      cases hv0 with
      | vinl hv1 =>
        cases hw0 with
        | einl hinner =>
          exact ih2 he1 (SCE.Value.vmrg hρ hv1) (elabSeal.evmrg hρ hv1 henv hinner hd1)
  | case_inr _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | ecase he he1 he2 hd1 hd2 =>
      obtain ⟨w0, hw0⟩ := ih1 he hρ henv
      have hv0 := eval_produces_value hρ h1
      cases hv0 with
      | vinr hv1 =>
        cases hw0 with
        | einr hinner =>
          exact ih2 he2 (SCE.Value.vmrg hρ hv1) (elabSeal.evmrg hρ hv1 henv hinner hd2)
  | fclos_val _ hv =>
    intro Γ A ce ρc helab hρ henv
    exact ⟨_, elabSeal_weaken helab (SCE.Value.vfclos hv) .top⟩
  | flam _ =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | eflam h1 hd1 hd2 => exact ⟨_, elabSeal.efclos hρ henv h1 hd1 hd2⟩
  | app_fclos _ hf ha hb ihf iha ihb =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | eapp he1 he2 =>
      obtain ⟨wf, hwf⟩ := ihf he1 hρ henv
      obtain ⟨wa, hwa⟩ := iha he2 hρ henv
      have hva := eval_produces_value hρ ha
      have hvf := eval_produces_value hρ hf
      cases hvf with
      | vfclos hval' =>
        cases hwf with
        | efclos _ ht hb' hd1 hd2 =>
          exact ihb hb'
            (SCE.Value.vmrg (SCE.Value.vmrg hval' (SCE.Value.vfclos hval')) hva)
            (elabSeal.evmrg (SCE.Value.vmrg hval' (SCE.Value.vfclos hval')) hva
              (elabSeal.evmrg hval' (SCE.Value.vfclos hval') ht
                (elabSeal.efclos hval' ht hb' hd1 hd2) hd1)
              hwa hd2)
  | fold _ _ ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | efold h1 =>
      obtain ⟨w, hw⟩ := ih h1 hρ henv
      exact ⟨_, elabSeal.efold hw⟩
  | unfold _ _ ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | eunfold h1 heq =>
      subst heq
      obtain ⟨w, hw⟩ := ih h1 hρ henv
      cases hw with
      | efold hinner => exact ⟨_, hinner⟩
  | wrap _ h ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | ewrap hΔ hvp hp =>
      have heq := bstep_value_id h hvp
      subst heq
      exact ⟨_, elabSeal.ewrap hΔ hvp hp⟩
  | mseal _ h hsv ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | emseal hΔ hnr hwf h1 =>
      obtain ⟨w0, hw0⟩ := ih h1 hρ henv
      exact source_ssealv_pres hsv hΔ hnr hwf (eval_produces_value hρ h) hw0
  | munseal _ h hsv ih =>
    intro Γ A ce ρc helab hρ henv
    cases helab with
    | emunseal hΔ hnr hwf h1 heq =>
      subst heq
      obtain ⟨w0, hw0⟩ := ih h1 hρ henv
      exact source_sunsealv_pres hsv hΔ hnr hwf (eval_produces_value hρ h) hw0

-- ── Big-step determinism ─────────────────────────────────────────────────────────────

theorem source_bigstep_deterministic_gen {ρ e v₁ : SCE.Exp} (heval₁ : S_Sem.BStep ρ e v₁)
    : ∀ {Γ A : SCE.Typ} {ec ρc : Seal.Exp} {v₂ : SCE.Exp},
    elabSeal Δ Γ e A ec → elabSeal Δ .top ρ Γ ρc → SCE.Value ρ
    → S_Sem.BStep ρ e v₂
    → v₁ = v₂ := by
  induction heval₁ with
  | query _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab; cases heval₂; rfl
  | lit _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab; cases heval₂; rfl
  | unit _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab; cases heval₂; rfl
  | clos_val _ _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases heval₂ with | clos_val _ _ => rfl
  | mclos_val _ _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases heval₂ with | mclos_val _ _ => rfl
  | proj _ hstep₁ hlook₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | eproj h1 hslook =>
      cases heval₂ with
      | proj _ hstep₂ hlook₂ =>
        have heq := ih h1 henv hρ hstep₂
        rw [heq] at hlook₁
        exact source_lookupv_det hlook₁ hlook₂
  | lam _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases heval₂ with | lam _ => rfl
  | box _ hstep₁a hstep₁b ih1 ih2 =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | ebox he1 he2 =>
      cases heval₂ with
      | box _ hstep₂a hstep₂b =>
        have heq_a := ih1 he1 henv hρ hstep₂a
        rw [← heq_a] at hstep₂b
        obtain ⟨w1, hw1⟩ := source_bigstep_elab_pres hstep₁a he1 hρ henv
        exact ih2 he2 hw1 (eval_produces_value hρ hstep₁a) hstep₂b
  | app_clos _ hstep₁f hstep₁a hstep₁b ihf iha ihb =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | eapp he1 he2 =>
      cases heval₂ with
      | app_clos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ihf he1 henv hρ hstep₂f
        cases heq_f
        have heq_a := iha he2 henv hρ hstep₂a
        rw [← heq_a] at hstep₂b
        have hvf := eval_produces_value hρ hstep₁f
        cases hvf with
        | vclos hval' =>
          have hva := eval_produces_value hρ hstep₁a
          obtain ⟨wf, hwf⟩ := source_bigstep_elab_pres hstep₁f he1 hρ henv
          cases hwf with
          | eclos _ ht hb' hd =>
            obtain ⟨wa, hwa⟩ := source_bigstep_elab_pres hstep₁a he2 hρ henv
            exact ihb hb' (elabSeal.evmrg hval' hva ht hwa hd)
              (SCE.Value.vmrg hval' hva) hstep₂b
      | app_fclos _ hstep₂f _ _ =>
        have heq_f := ihf he1 henv hρ hstep₂f
        cases heq_f
  | app_mclos _ hstep₁f hstep₁a hstep₁b ihf iha ihb =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | emapp he1 he2 =>
      cases heval₂ with
      | app_mclos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ihf he1 henv hρ hstep₂f
        cases heq_f
        have heq_a := iha he2 henv hρ hstep₂a
        rw [← heq_a] at hstep₂b
        have hvf := eval_produces_value hρ hstep₁f
        cases hvf with
        | vmclos hval' =>
          have hva := eval_produces_value hρ hstep₁a
          obtain ⟨wf, hwf⟩ := source_bigstep_elab_pres hstep₁f he1 hρ henv
          cases hwf with
          | emclos _ ht hb' hd =>
            obtain ⟨wa, hwa⟩ := source_bigstep_elab_pres hstep₁a he2 hρ henv
            exact ihb hb' (elabSeal.evmrg hval' hva ht hwa hd)
              (SCE.Value.vmrg hval' hva) hstep₂b
  | dmrg _ hstep₁a hstep₁b ih1 ih2 =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | edmrg he1 he2 hd1 hd2 =>
      cases heval₂ with
      | dmrg _ hstep₂a hstep₂b =>
        have heq_a := ih1 he1 henv hρ hstep₂a
        rw [← heq_a] at hstep₂b
        have hv1 := eval_produces_value hρ hstep₁a
        obtain ⟨w1, hw1⟩ := source_bigstep_elab_pres hstep₁a he1 hρ henv
        have heq_b := ih2 he2
          (elabSeal.evmrg hρ hv1 henv hw1 (disj_symm hd1))
          (SCE.Value.vmrg hρ hv1) hstep₂b
        rw [heq_a, heq_b]
    | evmrg hv1' hv2' he1 he2 hd =>
      cases heval₂ with
      | dmrg _ hstep₂a hstep₂b =>
        have hida := bstep_value_id hstep₁a hv1'
        have hida' := bstep_value_id hstep₂a hv1'
        subst hida
        have hidb := bstep_value_id hstep₁b hv2'
        subst hida'
        have hidb' := bstep_value_id hstep₂b hv2'
        rw [hidb, hidb']
  | nmrg _ hstep₁a hstep₁b ih1 ih2 =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | enmrg he1 he2 _ _ =>
      cases heval₂ with
      | nmrg _ hstep₂a hstep₂b =>
        rw [ih1 he1 henv hρ hstep₂a, ih2 he2 henv hρ hstep₂b]
  | lrec _ hstep₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | elrec h1 =>
      cases heval₂ with
      | lrec _ hstep₂ =>
        rw [ih h1 henv hρ hstep₂]
  | rproj _ hstep₁ hsel₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | erproj h1 hslook =>
      cases heval₂ with
      | rproj _ hstep₂ hsel₂ =>
        have heq := ih h1 henv hρ hstep₂
        rw [heq] at hsel₁
        have hv_val := eval_produces_value hρ hstep₂
        obtain ⟨w, hw⟩ := source_bigstep_elab_pres hstep₂ h1 hρ henv
        exact source_sel_det hsel₁ hv_val hw hslook hsel₂
  | letb _ hstep₁a hstep₁b ih1 ih2 =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | eletb he1 he2 hd =>
      cases heval₂ with
      | letb _ hstep₂a hstep₂b =>
        have heq_a := ih1 he1 henv hρ hstep₂a
        rw [← heq_a] at hstep₂b
        have hv1 := eval_produces_value hρ hstep₁a
        obtain ⟨w1, hw1⟩ := source_bigstep_elab_pres hstep₁a he1 hρ henv
        exact ih2 he2 (elabSeal.evmrg hρ hv1 henv hw1 hd) (SCE.Value.vmrg hρ hv1) hstep₂b
  | openm _ hstep₁a hstep₁b ih1 ih2 =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | eopenm he1 he2 hd =>
      cases heval₂ with
      | openm _ hstep₂a hstep₂b =>
        have heq_a := ih1 he1 henv hρ hstep₂a
        cases heq_a
        have hv_rcd := eval_produces_value hρ hstep₂a
        cases hv_rcd with
        | vlrec hv' =>
          obtain ⟨w1, hw1⟩ := source_bigstep_elab_pres hstep₂a he1 hρ henv
          cases hw1 with
          | elrec hinner =>
            exact ih2 he2 (elabSeal.evmrg hρ hv' henv hinner hd)
              (SCE.Value.vmrg hρ hv') hstep₂b
  | mstruct_sandboxed _ hstep₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | emstruct hsb hop h1 =>
      have heq := hsb rfl; subst heq
      cases heval₂ with
      | mstruct_sandboxed _ hstep₂ =>
        exact ih h1 (elabSeal.eunit .top) SCE.Value.vunit hstep₂
  | mstruct_open _ hstep₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | emstruct hsb hop h1 =>
      have heq := hop rfl; subst heq
      cases heval₂ with
      | mstruct_open _ hstep₂ =>
        exact ih h1 henv hρ hstep₂
  | mfunctor_sandboxed _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases heval₂ with | mfunctor_sandboxed _ => rfl
  | mfunctor_open _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases heval₂ with | mfunctor_open _ => rfl
  | mlink _ hstep₁a hstep₁b hsel₁ hstep₁c ih1 ih2 ih3 =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | emlink he1 he2 hslook hd1 hd2 =>
      cases heval₂ with
      | mlink _ hstep₂a hstep₂b hsel₂ hstep₂c =>
        have heq_a := ih1 he1 henv hρ hstep₂a
        have heq_b := ih2 he2 henv hρ hstep₂b
        cases heq_b
        have hv1 := eval_produces_value hρ hstep₁a
        obtain ⟨w1, hw1⟩ := source_bigstep_elab_pres hstep₁a he1 hρ henv
        obtain ⟨wm, hwm⟩ := source_bigstep_elab_pres hstep₁b he2 hρ henv
        cases hwm with
        | emclos hval2 henv2 hbody hd_mclos =>
          rw [← heq_a] at hsel₂
          have heq_sel := source_sel_det hsel₁ hv1 hw1 hslook hsel₂
          subst heq_sel
          have hvl := S_Sem.sel_value hsel₁ hv1
          obtain ⟨wl, hwl⟩ := elabSeal_sel_pres hslook hw1 hv1 hsel₁
          have heq_c := ih3 hbody
            (elabSeal.evmrg hval2 (SCE.Value.vlrec hvl) henv2 (elabSeal.elrec hwl) hd_mclos)
            (SCE.Value.vmrg hval2 (SCE.Value.vlrec hvl)) hstep₂c
          rw [heq_a, heq_c]
  | mlinkn _ hstep₁a hstep₁b hsp₁ hstep₁c ih1 ih2 ih3 =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | emlinkn he1 he2 hwire hd1 hd2 =>
      cases heval₂ with
      | mlinkn _ hstep₂a hstep₂b hsp₂ hstep₂c =>
        have heq_a := ih1 he1 henv hρ hstep₂a
        have heq_b := ih2 he2 henv hρ hstep₂b
        cases heq_b
        have hv1 := eval_produces_value hρ hstep₁a
        obtain ⟨w1, hw1⟩ := source_bigstep_elab_pres hstep₁a he1 hρ henv
        obtain ⟨wm, hwm⟩ := source_bigstep_elab_pres hstep₁b he2 hρ henv
        cases hwm with
        | emclos hval2 henv2 hbody hd_mclos =>
          rw [← heq_a] at hsp₂
          have heq_pkg := source_selpkg_det hwire hv1 hw1 hsp₁ hsp₂
          subst heq_pkg
          have hvpkg := S_Sem.selpkg_value hsp₁ hv1
          obtain ⟨wp, hwp⟩ := elabSeal_selpkg_pres hwire hsp₁ hv1 hw1
          have heq_c := ih3 hbody
            (elabSeal.evmrg hval2 hvpkg henv2 hwp hd_mclos)
            (SCE.Value.vmrg hval2 hvpkg) hstep₂c
          rw [heq_a, heq_c]
  | inl _ hstep₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | einl h1 =>
      cases heval₂ with
      | inl _ hstep₂ => rw [ih h1 henv hρ hstep₂]
  | inr _ hstep₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | einr h1 =>
      cases heval₂ with
      | inr _ hstep₂ => rw [ih h1 henv hρ hstep₂]
  | case_inl _ hstep₁a hstep₁b ih1 ih2 =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | ecase he he1 he2 hd1 hd2 =>
      cases heval₂ with
      | case_inl _ hstep₂a hstep₂b =>
        have heq_a := ih1 he henv hρ hstep₂a
        cases heq_a
        have hv0 := eval_produces_value hρ hstep₁a
        cases hv0 with
        | vinl hv1 =>
          obtain ⟨w0, hw0⟩ := source_bigstep_elab_pres hstep₁a he hρ henv
          cases hw0 with
          | einl hinner =>
            exact ih2 he1 (elabSeal.evmrg hρ hv1 henv hinner hd1)
              (SCE.Value.vmrg hρ hv1) hstep₂b
      | case_inr _ hstep₂a _ =>
        have heq_a := ih1 he henv hρ hstep₂a
        cases heq_a
  | case_inr _ hstep₁a hstep₁b ih1 ih2 =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | ecase he he1 he2 hd1 hd2 =>
      cases heval₂ with
      | case_inr _ hstep₂a hstep₂b =>
        have heq_a := ih1 he henv hρ hstep₂a
        cases heq_a
        have hv0 := eval_produces_value hρ hstep₁a
        cases hv0 with
        | vinr hv1 =>
          obtain ⟨w0, hw0⟩ := source_bigstep_elab_pres hstep₁a he hρ henv
          cases hw0 with
          | einr hinner =>
            exact ih2 he2 (elabSeal.evmrg hρ hv1 henv hinner hd2)
              (SCE.Value.vmrg hρ hv1) hstep₂b
      | case_inl _ hstep₂a _ =>
        have heq_a := ih1 he henv hρ hstep₂a
        cases heq_a
  | fclos_val _ _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases heval₂ with | fclos_val _ _ => rfl
  | flam _ =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases heval₂ with | flam _ => rfl
  | app_fclos _ hstep₁f hstep₁a hstep₁b ihf iha ihb =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | eapp he1 he2 =>
      cases heval₂ with
      | app_clos _ hstep₂f _ _ =>
        have heq_f := ihf he1 henv hρ hstep₂f
        cases heq_f
      | app_fclos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ihf he1 henv hρ hstep₂f
        cases heq_f
        have heq_a := iha he2 henv hρ hstep₂a
        rw [← heq_a] at hstep₂b
        have hvf := eval_produces_value hρ hstep₁f
        cases hvf with
        | vfclos hval' =>
          have hva := eval_produces_value hρ hstep₁a
          obtain ⟨wf, hwf⟩ := source_bigstep_elab_pres hstep₁f he1 hρ henv
          cases hwf with
          | efclos _ ht hb' hd1 hd2 =>
            obtain ⟨wa, hwa⟩ := source_bigstep_elab_pres hstep₁a he2 hρ henv
            exact ihb hb'
              (elabSeal.evmrg (SCE.Value.vmrg hval' (SCE.Value.vfclos hval')) hva
                (elabSeal.evmrg hval' (SCE.Value.vfclos hval') ht
                  (elabSeal.efclos hval' ht hb' hd1 hd2) hd1)
                hwa hd2)
              (SCE.Value.vmrg (SCE.Value.vmrg hval' (SCE.Value.vfclos hval')) hva)
              hstep₂b
  | fold _ hstep₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | efold h1 =>
      cases heval₂ with
      | fold _ hstep₂ => rw [ih h1 henv hρ hstep₂]
  | unfold _ hstep₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | eunfold h1 heq =>
      cases heval₂ with
      | unfold _ hstep₂ =>
        have heq_f := ih h1 henv hρ hstep₂
        cases heq_f
        rfl
  | wrap _ hstep₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | ewrap hΔ hvp hp =>
      cases heval₂ with
      | wrap _ hstep₂ =>
        rw [bstep_value_id hstep₁ hvp, bstep_value_id hstep₂ hvp]
  | mseal _ hstep₁ hsv₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | emseal hΔ hnr hwf h1 =>
      cases heval₂ with
      | mseal _ hstep₂ hsv₂ =>
        have heq := ih h1 henv hρ hstep₂
        subst heq
        exact S_Sem.ssealv_det hsv₁ hsv₂
  | munseal _ hstep₁ hsv₁ ih =>
    intro Γ A ec ρc v₂ helab henv hρ heval₂
    cases helab with
    | emunseal hΔ hnr hwf h1 heq =>
      cases heval₂ with
      | munseal _ hstep₂ hsv₂ =>
        have heqv := ih h1 henv hρ hstep₂
        subst heqv
        exact S_Sem.sunsealv_det hsv₁ hsv₂

-- Whole-program determinism, elabSeal-witnessed.
theorem source_bigstep_deterministic {A : SCE.Typ} {e v₁ v₂ : SCE.Exp}
    (helab : ∃ ec, elabSeal Δ .top e A ec)
    (heval₁ : S_Sem.BStep SCE.Exp.unit e v₁)
    (heval₂ : S_Sem.BStep SCE.Exp.unit e v₂)
    : v₁ = v₂ := by
  obtain ⟨ec, helab⟩ := helab
  exact source_bigstep_deterministic_gen heval₁ helab (elabSeal.eunit .top)
    SCE.Value.vunit heval₂

end Seal

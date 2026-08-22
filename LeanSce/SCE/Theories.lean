import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics

open SCE S_Sem

-- Pure source-level metatheory of λSCE: lookup uniqueness and value soundness of the
-- big-step semantics.  (The elaboration-witnessed results live in SCE/Preservation.lean,
-- SCE/Progress.lean and SCE/Determinism.lean, all against the sealing target λE^≤.)

theorem index_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {n : Nat}
    (h₁ : SLookup T n T₁)
    (h₂ : SLookup T n T₂)
    : T₁ = T₂ := by
  induction h₁ with
  | zero A B => cases h₂; rfl
  | succ A B n C _ ih => cases h₂ with | succ _ _ _ _ h₂ => exact ih h₂

theorem record_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {l : String}
    (h₁ : SCE.SRLookup T l T₁)
    (h₂ : SCE.SRLookup T l T₂)
    : T₁ = T₂ := by
  induction h₁ with
  | zero l T => cases h₂; rfl
  | andl A B l T hsr h_cond ih =>
    cases h₂ with
    | andl _ _ _ _ h₂' _ => exact ih h₂'
    | andr _ _ _ _ h₂' h_cond₂ =>
      exact absurd (SCE.srlookup_labelin hsr) h_cond₂
  | andr A B l T hsr h_cond ih =>
    cases h₂ with
    | andr _ _ _ _ h₂' _ => exact ih h₂'
    | andl _ _ _ _ h₂' h_cond₂ =>
      exact absurd (SCE.srlookup_labelin hsr) h_cond₂
  | sig l T A _ ih =>
    cases h₂ with
    | sig _ _ _ h₂' => exact ih h₂'

theorem source_lookupv_value
    {v v' : SCE.Exp} {n : Nat}
    (hval : SCE.Value v)
    (hlook : S_Sem.LookupV v n v')
    : SCE.Value v' := by
  induction hlook with
  | dmrg_zero => cases hval with | vmrg h1 h2 => exact h2
  | dmrg_succ _ ih => cases hval with | vmrg h1 h2 => exact ih h1
  | nmrg_zero => cases hval
  | nmrg_succ => cases hval

theorem source_sel_value
    {v v' : SCE.Exp} {l : String}
    (hval : SCE.Value v)
    (hsel : S_Sem.Sel v l v')
    : SCE.Value v' := by
  induction hsel with
  | rcd => cases hval with | vlrec h => exact h
  | dmrg_left _ ih => cases hval with | vmrg h1 h2 => exact ih h1
  | dmrg_right _ ih => cases hval with | vmrg h1 h2 => exact ih h2
  | nmrg_left _ ih => cases hval
  | nmrg_right _ ih => cases hval

theorem eval_produces_value
    {ρ e v : SCE.Exp}
    (hval : SCE.Value ρ)
    (heval : S_Sem.BStep ρ e v)
    : SCE.Value v := by
  induction heval with
  | query _ => exact hval
  | lit _ => exact SCE.Value.vint
  | unit _ => exact SCE.Value.vunit
  | clos_val _ hv => exact SCE.Value.vclos hv
  | mclos_val _ hv => exact SCE.Value.vmclos hv
  | proj _ _ hlook ih1 =>
    exact source_lookupv_value (ih1 hval) hlook
  | lam _ => exact SCE.Value.vclos hval
  | box _ _ _ ih1 ih2 => exact ih2 (ih1 hval)
  | app_clos _ _ _ _ ih1 ih2 ih3 =>
    have hvclos := ih1 hval
    cases hvclos with | vclos hv => exact ih3 (SCE.Value.vmrg hv (ih2 hval))
  | app_mclos _ _ _ _ ih1 ih2 ih3 =>
    have hvclos := ih1 hval
    cases hvclos with | vmclos hv => exact ih3 (SCE.Value.vmrg hv (ih2 hval))
  | dmrg _ _ _ ih1 ih2 =>
    exact SCE.Value.vmrg (ih1 hval) (ih2 (SCE.Value.vmrg hval (ih1 hval)))
  | nmrg _ _ _ ih1 ih2 =>
    exact SCE.Value.vmrg (ih1 hval) (ih2 hval)
  | lrec _ _ ih => exact SCE.Value.vlrec (ih hval)
  | rproj _ _ hsel ih =>
    exact source_sel_value (ih hval) hsel
  | letb _ _ _ ih1 ih2 =>
    exact ih2 (SCE.Value.vmrg hval (ih1 hval))
  | openm _ _ _ ih1 ih2 =>
    have := ih1 hval
    cases this with | vlrec hv => exact ih2 (SCE.Value.vmrg hval hv)
  | mstruct_sandboxed _ _ ih => exact ih SCE.Value.vunit
  | mstruct_open _ _ ih => exact ih hval
  | mfunctor_sandboxed _ => exact SCE.Value.vmclos SCE.Value.vunit
  | mfunctor_open hv => exact SCE.Value.vmclos hv
  | mlink hv hstep1 hstep2 hsel hstep3 ih1 ih2 ih3 =>
    have hv1 := ih1 hv
    have hv2 := ih2 hv
    cases hv2 with
    | vmclos hvv2 =>
      have hvl := source_sel_value hv1 hsel
      exact SCE.Value.vmrg hv1 (ih3 (SCE.Value.vmrg hvv2 (SCE.Value.vlrec hvl)))
  | mlinkn hv hstep1 hstep2 hsp hstep3 ih1 ih2 ih3 =>
    have hv1 := ih1 hv
    have hv2 := ih2 hv
    cases hv2 with
    | vmclos hvv2 =>
      exact SCE.Value.vmrg hv1 (ih3 (SCE.Value.vmrg hvv2 (S_Sem.selpkg_value hsp hv1)))
  | inl _ _ ih => exact SCE.Value.vinl (ih hval)
  | inr _ _ ih => exact SCE.Value.vinr (ih hval)
  | case_inl _ _ _ ih1 ih2 =>
    have hinl := ih1 hval
    cases hinl with | vinl hv1 => exact ih2 (SCE.Value.vmrg hval hv1)
  | case_inr _ _ _ ih1 ih2 =>
    have hinr := ih1 hval
    cases hinr with | vinr hv1 => exact ih2 (SCE.Value.vmrg hval hv1)
  | fclos_val _ hv => exact SCE.Value.vfclos hv
  | flam _ => exact SCE.Value.vfclos hval
  | app_fclos _ _ _ _ ih1 ih2 ih3 =>
    have hvclos := ih1 hval
    cases hvclos with
    | vfclos hv =>
      exact ih3 (SCE.Value.vmrg (SCE.Value.vmrg hv (SCE.Value.vfclos hv)) (ih2 hval))
  | fold _ _ ih => exact SCE.Value.vfold (ih hval)
  | unfold _ _ ih =>
    have hfold := ih hval
    cases hfold with | vfold hv => exact hv
  | wrap _ _ ih => exact SCE.Value.vwrap (ih hval)
  | mseal _ _ hsv ih => exact S_Sem.ssealv_value (ih hval) hsv
  | munseal _ _ hsv ih => exact S_Sem.sunsealv_value (ih hval) hsv

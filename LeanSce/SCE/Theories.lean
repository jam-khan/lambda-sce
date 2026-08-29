import LeanSce.Core.Syntax
import LeanSce.Core.Semantics.BigStep
import LeanSce.Core.Semantics.Equivalence
import LeanSce.Core.Typing
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics.BigStep
import LeanSce.SCE.Elaboration.Elaboration
import LeanSce.SCE.Elaboration.Uniqueness
import LeanSce.SCE.Elaboration.Preservation
import LeanSce.SCE.Preservation

open SCE Core

/-- The linker's binary step, as a relation on compiled units: given a provider
`ec₁ : A₁` and a functor `ec₂ : {l:A} → B` with `A₁ ∋ l : A`, the linked unit is
`linkedCore A₁ {l:A} B ec₁ ec₂`.  The linearized step is closed — it does not
mention the ambient context — so the relation carries none. -/
inductive CoreLink
    : String → Core.Typ → Core.Typ → Core.Typ
    → Core.Exp → Core.Exp → Core.Exp → Prop where
  | link (A₁ A B : Core.Typ) (l : String) (ec₁ ec₂ : Core.Exp)
    : Core.RLookup A₁ l A
    → CoreLink l A₁ A B ec₁ ec₂ (linkedCore A₁ (.rcd l A) B ec₁ ec₂)

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
  | mstruct_sandboxed _ _ ih => exact SCE.Value.vmstruct (ih SCE.Value.vunit)
  | mstruct_open _ _ ih => exact SCE.Value.vmstruct (ih hval)
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

-- A value big-steps only to itself
theorem bstep_value_id {v : SCE.Exp}
    (hv : SCE.Value v)
    : ∀ {ρ v' : SCE.Exp}, S_Sem.BStep ρ v v' → v' = v := by
  induction hv with
  | vint => intro _ _ h; cases h; rfl
  | vunit => intro _ _ h; cases h; rfl
  | vclos _ => intro _ _ h; cases h; rfl
  | vmclos _ => intro _ _ h; cases h; rfl
  | vmstruct _ ih =>
    intro _ _ h
    cases h with
    | mstruct_sandboxed _ hb => rw [ih hb]
    | mstruct_open _ hb => rw [ih hb]
  | vmrg _ _ ih1 ih2 =>
    intro _ _ h
    cases h with
    | dmrg _ hb1 hb2 => rw [ih1 hb1, ih2 hb2]
  | vlrec _ ih =>
    intro _ _ h
    cases h with
    | lrec _ hb => rw [ih hb]
  | vinl _ ih =>
    intro _ _ h
    cases h with
    | inl _ hb => rw [ih hb]
  | vinr _ ih =>
    intro _ _ h
    cases h with
    | inr _ hb => rw [ih hb]
  | vfclos _ => intro _ _ h; cases h; rfl
  | vfold _ ih =>
    intro _ _ h
    cases h with
    | fold _ hb => rw [ih hb]

theorem sel_implies_label_in
    {v v' : SCE.Exp} {vc : Core.Exp} {A : SCE.Typ} {l : String}
    (hval : SCE.Value v)
    (helab : elabExp SCE.Typ.top v A vc)
    (hsel : S_Sem.Sel v l v')
    : SCE.LabelIn l A := by
  induction hsel generalizing A vc with
  | rcd =>
    cases hval with | vlrec hv =>
    cases helab with | elrec _ _ _ _ _ h =>
    exact SCE.LabelIn.rcd _ _
  | dmrg_left _ ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    exact SCE.LabelIn.andl _ _ _ (ih hv1 h1)
  | dmrg_right _ ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    exact SCE.LabelIn.andr _ _ _ (ih hv2 (elab_value_weaken h2 hv2 _))
  | nmrg_left => cases hval
  | nmrg_right => cases hval

theorem lookup_preservation
    {v_e v' : SCE.Exp} {vc_e : Core.Exp} {A B : SCE.Typ} {i : Nat}
    (hval : SCE.Value v_e)
    (helab : elabExp SCE.Typ.top v_e A vc_e)
    (hlook : S_Sem.LookupV v_e i v')
    (htyp_look : SCE.SLookup A i B)
    : ∃ vc', Core.LookupV vc_e i vc' ∧ elabExp SCE.Typ.top v' B vc' := by
  induction hlook generalizing A B vc_e with
  | dmrg_zero =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ _ _ _ _ ce1 ce2 h1 h2 =>
    cases htyp_look with | zero =>
    exact ⟨ce2, Core.LookupV.lvzero, elab_value_weaken h2 hv2 _⟩
  | dmrg_succ _ ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ _ _ _ _ ce1 ce2 h1 h2 =>
    cases htyp_look with | succ _ _ _ _ htyp_inner =>
    obtain ⟨vc', hlookvc, helab_v'⟩ := ih hv1 h1 htyp_inner
    exact ⟨vc', Core.LookupV.lvsucc hlookvc, helab_v'⟩
  | nmrg_zero => cases hval
  | nmrg_succ => cases hval

theorem sel_preservation
    {v_e v' : SCE.Exp} {vc_e : Core.Exp} {A B : SCE.Typ} {l : String}
    (hval : SCE.Value v_e)
    (helab : elabExp SCE.Typ.top v_e A vc_e)
    (hlook : S_Sem.Sel v_e l v')
    (htyp_look : SCE.SRLookup A l B)
    : ∃ vc', Core.RLookupV vc_e l vc' ∧ elabExp SCE.Typ.top v' B vc' := by
  induction hlook generalizing A B vc_e with
  | rcd =>
    cases hval with | vlrec hv =>
    cases helab with | elrec _ _ _ vc_inner _ h_inner =>
    cases htyp_look with | zero =>
    exact ⟨vc_inner, Core.RLookupV.rvlzero, h_inner⟩
  | dmrg_left hsel_inner ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    cases htyp_look with
    | andl _ _ _ _ hrl hcond =>
      obtain ⟨vc', hlookvc, helab_v'⟩ := ih hv1 h1 hrl
      exact ⟨vc', Core.RLookupV.vlandl hlookvc, helab_v'⟩
    | andr _ _ _ _ hrl hcond =>
      have hlin := sel_implies_label_in hv1 h1 hsel_inner
      exact absurd hlin hcond
  | dmrg_right hsel_inner ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    rename_i v1 v2 v3 l'
    have h2_weak : elabExp SCE.Typ.top v2 B' ce2 :=
      elab_value_weaken h2 hv2 (SCE.Typ.top)
    cases htyp_look with
    | andr _ _ _ _ hrl hcond =>
      obtain ⟨vc', hlookvc, helab_v'⟩ := ih hv2 h2_weak hrl
      exact ⟨vc', Core.RLookupV.vlandr hlookvc, helab_v'⟩
    | andl _ _ _ _ hrl hcond =>
      have hlin := sel_implies_label_in hv2 h2_weak hsel_inner
      exact absurd hlin hcond
  | nmrg_left => cases hval
  | nmrg_right => cases hval

/-! ### Evaluation of the linearized combinators

Operational lemmas assembling `EBig` derivations for the linearized terms.  Note
the premise shapes: each operand evaluation appears **once**, mirroring the terms
themselves. -/

/-- Bind-once merge: if each operand evaluates once under `ρ`, the linearized
merge evaluates to the merged values. -/
theorem nmrgCore_eval
    {ρc vc₁ vc₂ : Core.Exp} {a b : Core.Typ} {ce₁ ce₂ : Core.Exp}
    (hρ : Core.Value ρc)
    (hbig1 : EBig ρc ce₁ vc₁)
    (hbig2 : EBig ρc ce₂ vc₂)
    : EBig ρc (nmrgCore a b ce₁ ce₂) (.mrg vc₁ vc₂) := by
  have hv1 := ebig_produces_value hρ hbig1
  have hv2 := ebig_produces_value hρ hbig2
  simp only [nmrgCore, nmrgStep]
  apply EBig.ebapp
  · exact EBig.ebapp (EBig.ebclos hρ) hbig1 (EBig.ebclos (Core.Value.vmrg hρ hv1))
  · exact hbig2
  · apply EBig.ebmrg
    · exact EBig.ebproj
        (EBig.equery (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hv2))
        (Core.LookupV.lvsucc Core.LookupV.lvzero)
    · exact EBig.ebproj
        (EBig.equery
          (Core.Value.vmrg (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hv2) hv1))
        (Core.LookupV.lvsucc Core.LookupV.lvzero)

-- the extracted package elaborates at the interface type
theorem selpkg_elab {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D) :
    ∀ {v pkg : SCE.Exp} {vc : Core.Exp},
    S_Sem.SelPkg v D pkg
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ₁ vc
    → ∃ cpkg, elabExp SCE.Typ.top pkg D cpkg := by
  induction hok with
  | one hrl =>
    intro v pkg vc hsp hv helab
    cases hsp with
    | one hsel =>
      obtain ⟨vcl, _, helab_vl⟩ := sel_preservation hv helab hsel hrl
      exact ⟨_, elabExp.elrec _ _ _ _ _ helab_vl⟩
  | more hok' hrl ih =>
    intro v pkg vc hsp hv helab
    cases hsp with
    | more hsp' hsel =>
      obtain ⟨cpkg', helab'⟩ := ih hsp' hv helab
      obtain ⟨vcl, _, helab_vl⟩ := sel_preservation hv helab hsel hrl
      have hvl := source_sel_value hv hsel
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _ helab'
        (elab_value_weaken (elabExp.elrec SCE.Typ.top _ _ _ _ helab_vl)
          (SCE.Value.vlrec hvl) _)⟩

/-- The linearized wire evaluates by projection alone.  Generalized over the
environment: wherever the provider *value* `vc₁` is reachable at index `shift`,
`wire_shift ⟦D⟧` evaluates to a package that elaborates the source package.  No
premise about the provider *term* appears, because the wire never mentions it. -/
theorem wire_eval {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D)
    : ∀ {v₁ pkg : SCE.Exp} {ρ' vc₁ : Core.Exp} {shift : Nat},
      S_Sem.SelPkg v₁ D pkg
      → SCE.Value v₁
      → elabExp SCE.Typ.top v₁ Γ₁ vc₁
      → Core.Value ρ'
      → Core.LookupV ρ' shift vc₁
      → ∃ cpkg, EBig ρ' (wire shift (elabTyp D)) cpkg ∧ elabExp SCE.Typ.top pkg D cpkg := by
  induction hok with
  | one hrl =>
    intro v₁ pkg ρ' vc₁ shift hsp hv₁ helab₁ hρ' hlook
    cases hsp with
    | one hsel =>
      obtain ⟨vcl, hrlv, helab_vl⟩ := sel_preservation hv₁ helab₁ hsel hrl
      exact ⟨_,
        EBig.ebrec (EBig.ebsel (EBig.ebproj (EBig.equery hρ') hlook) hrlv),
        elabExp.elrec _ _ _ _ _ helab_vl⟩
  | more hok' hrl ih =>
    intro v₁ pkg ρ' vc₁ shift hsp hv₁ helab₁ hρ' hlook
    cases hsp with
    | more hsp' hsel =>
      obtain ⟨cpkg', hbig', helab'⟩ := ih hsp' hv₁ helab₁ hρ' hlook
      obtain ⟨vcl, hrlv, helab_vl⟩ := sel_preservation hv₁ helab₁ hsel hrl
      have hvl := source_sel_value hv₁ hsel
      have hcpkg' := ebig_produces_value hρ' hbig'
      exact ⟨_,
        EBig.ebmrg hbig'
          (EBig.ebrec (EBig.ebsel
            (EBig.ebproj (EBig.equery (Core.Value.vmrg hρ' hcpkg'))
              (Core.LookupV.lvsucc hlook)) hrlv)),
        elabExp.edmrg _ _ _ _ _ _ _ helab'
          (elab_value_weaken (elabExp.elrec SCE.Typ.top _ _ _ _ helab_vl)
            (SCE.Value.vlrec hvl) _)⟩

/-- The assembly lemma for the linearized composition: one evaluation of each
operand, one wire evaluation under the spine-built environment
`((ρ , v₁) , f) , v₁`, one closure-body evaluation — exactly the derivation
shape of the term.  Shared by `link` and `linkall`. -/
theorem linkStep_eval
    {ρc vc₁ vc₂ cpkg vc₃ : Core.Exp} {g1 D B DT : Core.Typ}
    {ce₁ ce₂ body : Core.Exp}
    (hρ : Core.Value ρc)
    (hbig1 : EBig ρc ce₁ vc₁)
    (hbig2 : EBig ρc ce₂ (.clos vc₂ DT body))
    (hbigw : EBig (.mrg (.mrg (.mrg ρc vc₁) (.clos vc₂ DT body)) vc₁)
               (wire 0 D) cpkg)
    (hbig3 : EBig (.mrg vc₂ cpkg) body vc₃)
    : EBig ρc (linkedCore g1 D B ce₁ ce₂) (.mrg vc₁ vc₃) := by
  have hv1 := ebig_produces_value hρ hbig1
  have hvf := ebig_produces_value hρ hbig2
  simp only [linkedCore, linkStep]
  apply EBig.ebapp
  · exact EBig.ebapp (EBig.ebclos hρ) hbig1 (EBig.ebclos (Core.Value.vmrg hρ hv1))
  · exact hbig2
  · apply EBig.ebmrg
    · exact EBig.ebproj
        (EBig.equery (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hvf))
        (Core.LookupV.lvsucc Core.LookupV.lvzero)
    · exact EBig.ebapp
        (EBig.ebproj
          (EBig.equery
            (Core.Value.vmrg (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hvf) hv1))
          (Core.LookupV.lvsucc Core.LookupV.lvzero))
        hbigw
        hbig3

/-- The single-import wire evaluated in the spine-built environment: the
`link` instance of `wire_eval`, stated directly at the target. -/
theorem wire_eval_rcd
    {ρc vc₁ f vc_l : Core.Exp} {l : String} {A : Core.Typ}
    (hρ : Core.Value ρc) (hv1 : Core.Value vc₁) (hf : Core.Value f)
    (hsel : Core.RLookupV vc₁ l vc_l)
    : EBig (.mrg (.mrg (.mrg ρc vc₁) f) vc₁) (wire 0 (.rcd l A)) (.lrec l vc_l) := by
  simp only [wire]
  exact EBig.ebrec (EBig.ebsel
    (EBig.ebproj
      (EBig.equery (Core.Value.vmrg (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hf) hv1))
      Core.LookupV.lvzero)
    hsel)

theorem semantic_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (heval : S_Sem.BStep ρs es vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc ∧ elabExp SCE.Typ.top vs A vc := by
  induction heval generalizing Γ A ec ρc with
  | query hval=>
    rename_i v
    exists ρc
    constructor
    · cases helab
      refine EBig.equery ?_
      exact elab_value henv hval
    · cases helab
      assumption
  | lit hval =>
    cases helab
    exact ⟨Core.Exp.lit _, EBig.eblit (elab_value henv henv_val), elabExp.elit .top _⟩
  | unit =>
    cases helab
    exists Core.Exp.unit
    constructor
    · apply EBig.ebunit
      (expose_names; exact elab_value henv h)
    · exact elabExp.eunit SCE.Typ.top
  | clos_val henv_src hval =>
    cases helab with
    | eclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact ⟨_, EBig.eclos (elab_value henv henv_val) (elab_value h1 hval),
               elabExp.eclos .top _ _ _ _ _ _ _ hval h1 h2⟩
  | mclos_val henv_src hval =>
    cases helab with
    | mclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact ⟨_, EBig.eclos (elab_value henv henv_val) (elab_value h1 hval),
               elabExp.mclos .top _ _ _ _ _ _ _ hval h1 h2⟩
  | proj ρ1 hstep hlookv ih1 =>
    cases helab with
    | eproj _ A' _ _ ce _ h_elab h_slook =>
      obtain ⟨vc, hbig, helab_v⟩ := ih1 h_elab henv henv_val
      obtain ⟨vc', hlookvc, helab_v'⟩ := lookup_preservation
        (eval_produces_value henv_val hstep)
        helab_v hlookv h_slook
      exact ⟨vc', EBig.ebproj hbig hlookvc, helab_v'⟩
  | lam hval =>
    cases helab with
    | elam _ _ _ _ ce h_body =>
      exact ⟨Core.Exp.clos ρc _ ce,
             EBig.ebclos (elab_value henv henv_val),
             elabExp.eclos .top _ _ _ _ _ _ _ henv_val henv h_body⟩
  | box hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | ebox _ ctx' _ _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      obtain ⟨vc, hbig2, helab_v⟩ := ih2 h_elab2 helab_v1 hv1_val
      exact ⟨vc, EBig.ebbox hbig1 hbig2, helab_v⟩
  | app_clos hval_ρ hstep1 hstep2 hstep_body ih1 ih2 ih3 =>
    cases helab with
    | eapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc_clos, hbig1, helab_clos⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_clos with
      | eclos _ _ _ _ _ _ _ _ hval_v1 h_env_v1 h_body_elab =>
        rename_i ctx_clos ce_env ce_body
        have hv1_val := eval_produces_value henv_val hstep1
        cases hv1_val with
        | vclos hval_inner =>
          have hv2_val := eval_produces_value henv_val hstep2
          have hval_body_env := SCE.Value.vmrg hval_inner hv2_val
          have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
            h_env_v1 (elab_value_weaken helab_v2 hv2_val (SCE.Typ.and .top ctx_clos))
          obtain ⟨vc_result, hbig3, helab_result⟩ := ih3 h_body_elab helab_body_env hval_body_env
          exact ⟨vc_result,
                 EBig.ebapp hbig1 hbig2 hbig3,
                 helab_result⟩
  | app_mclos hval_ρ hstep1 hstep2 hstep_body ih1 ih2 ih3 =>
    cases helab with
    | mapp _ A_param mt _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc_clos, hbig1, helab_clos⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_clos with
      | mclos _ _ _ _ _ _ _ _ hval_v1 h_env_v1 h_body_elab =>
        have hv1_val := eval_produces_value henv_val hstep1
        cases hv1_val with
        | vmclos hval_inner =>
          have hv2_val := eval_produces_value henv_val hstep2
          have hval_body_env := SCE.Value.vmrg hval_inner hv2_val
          have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
            h_env_v1 (elab_value_weaken helab_v2 hv2_val _)
          obtain ⟨vc_result, hbig3, helab_result⟩ := ih3 h_body_elab helab_body_env hval_body_env
          exact ⟨vc_result,
                 EBig.ebapp hbig1 hbig2 hbig3,
                 helab_result⟩
  | dmrg hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | edmrg _ A_inner B_inner _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      have hval_mrg := SCE.Value.vmrg henv_val hv1_val
      have helab_mrg_env := elabExp.edmrg .top _ _ _ _ _ _
        henv (elab_value_weaken helab_v1 hv1_val _)
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 helab_mrg_env hval_mrg
      have hv2_val := eval_produces_value hval_mrg hstep2
      have helab_result := elabExp.edmrg .top _ _ _ _ _ _
        helab_v1 (elab_value_weaken helab_v2 hv2_val _)
      exact ⟨.mrg vc1 vc2, EBig.ebmrg hbig1 hbig2, helab_result⟩
  | nmrg hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | enmrg _ A_inner B_inner _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      have hv2_val := eval_produces_value henv_val hstep2
      have helab_result := elabExp.edmrg .top _ _ _ _ _ _
        helab_v1 (elab_value_weaken helab_v2 hv2_val _)
      exact ⟨.mrg vc1 vc2,
             nmrgCore_eval (elab_value henv henv_val) hbig1 hbig2,
             helab_result⟩
  | openm hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | openm _ A_inner B_inner _ _ ce1 ce2 l_inner h_elab1 h_elab2 =>
      -- IH on e₁: produces lrec l v'
      obtain ⟨vc_rcd, hbig1, helab_rcd⟩ := ih1 h_elab1 henv henv_val
      -- extract inner value from lrec elaboration
      cases helab_rcd with
      | elrec _ _ _ vc_inner _ helab_inner =>
        -- build env for body: ρ ,, v'
        have hv'_val := eval_produces_value henv_val hstep1
        cases hv'_val with
        | vlrec hval_inner =>
          have hval_mrg := SCE.Value.vmrg henv_val hval_inner
          have helab_mrg_env := elabExp.edmrg .top _ _ _ _ _ _
            henv (elab_value_weaken helab_inner hval_inner _)
          -- IH on e₂
          obtain ⟨vc_result, hbig2, helab_result⟩ := ih2 h_elab2 helab_mrg_env hval_mrg
          -- core big-step: app (lam ce2) (rproj ce1 l)
          exact ⟨vc_result,
                 EBig.ebapp
                   (EBig.ebclos (elab_value henv henv_val))
                   (EBig.ebsel hbig1 Core.RLookupV.rvlzero)
                   hbig2,
                 helab_result⟩
  | letb hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | letb _ A_inner B_inner _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      have hval_mrg := SCE.Value.vmrg henv_val hv1_val
      have helab_mrg_env := elabExp.edmrg .top _ _ _ _ _ _
        henv (elab_value_weaken helab_v1 hv1_val _)
      obtain ⟨vc_result, hbig2, helab_result⟩ := ih2 h_elab2 helab_mrg_env hval_mrg
      exact ⟨vc_result,
             EBig.ebapp (EBig.ebclos (elab_value henv henv_val)) hbig1 hbig2,
             helab_result⟩
  | mstruct_sandboxed hval_ρ hstep_body ih =>
    cases helab with
    | mstruct _ _ _ _ _ ce _ _ hs1 hs2 h_elab_body =>
      have hctx := hs1 rfl
      rw [hctx] at h_elab_body
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab_body (elabExp.eunit .top) SCE.Value.vunit
      have hv_body := eval_produces_value SCE.Value.vunit hstep_body
      exact ⟨vc, EBig.ebbox (EBig.ebunit (elab_value henv henv_val)) hbig,
             elabExp.mstructv _ _ _ _ _ hv_body helab_v⟩
    | mstructv _ _ _ _ _ hvse h =>
      have hveq := bstep_value_id hvse hstep_body
      subst hveq
      exact ⟨_, ebig_value_refl (elab_value h hvse) (elab_value henv henv_val),
             elabExp.mstructv _ _ _ _ _ hvse (elab_value_weaken h hvse _)⟩
  | mstruct_open hval_ρ hstep_body ih =>
    cases helab with
    | mstruct _ _ _ _ _ ce _ _ hs1 hs2 h_elab_body =>
      have hctx := hs2 rfl
      rw [hctx] at h_elab_body
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab_body henv henv_val
      have hv_body := eval_produces_value henv_val hstep_body
      exact ⟨vc, EBig.ebbox (EBig.equery (elab_value henv henv_val)) hbig,
             elabExp.mstructv _ _ _ _ _ hv_body helab_v⟩
    | mstructv _ _ _ _ _ hvse h =>
      have hveq := bstep_value_id hvse hstep_body
      subst hveq
      exact ⟨_, ebig_value_refl (elab_value h hvse) (elab_value henv henv_val),
             elabExp.mstructv _ _ _ _ _ hvse (elab_value_weaken h hvse _)⟩
  | mfunctor_sandboxed hval_ρ =>
    cases helab with
    | mfunctor _ ctxInner _ _ sb _ ce hs1 hs2 h_body =>
      have hctx := hs1 rfl
      rw [hctx] at h_body
      exact ⟨Core.Exp.clos .unit _ ce,
             EBig.ebbox (EBig.ebunit (elab_value henv henv_val))
                        (EBig.ebclos Value.vunit),
             elabExp.mclos .top _ _ _ _ _ _ _ Value.vunit (elabExp.eunit .top) h_body⟩
  | mfunctor_open hval_ρ =>
    cases helab with
    | mfunctor _ ctxInner _ _ sb _ ce hs1 hs2 h_body =>
      have hctx := hs2 rfl
      rw [hctx] at h_body
      exact ⟨Core.Exp.clos ρc _ ce,
             EBig.ebclos (elab_value henv henv_val),
             elabExp.mclos .top _ _ _ _ _ _ _ henv_val henv h_body⟩
  | lrec hval_ρ hstep ih =>
    cases helab with
    | elrec _ A_inner _ ce l h_elab =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      exact ⟨Core.Exp.lrec _ vc,
             EBig.ebrec hbig,
             elabExp.elrec .top _ _ _ _ helab_v⟩
  | rproj hval_ρ hstep hsel ih =>
    cases helab with
    | erproj _ A_inner B_inner _ ce l_inner h_elab h_slook =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      have hv_val := eval_produces_value henv_val hstep
      obtain ⟨vc', hrlookup_v, helab_v'⟩ :=
        sel_preservation hv_val helab_v hsel h_slook
      exact ⟨vc', EBig.ebsel hbig hrlookup_v, helab_v'⟩
  | mlink h1 bstep1 bstep2 sel1 step2 step3 ih1 ih2 =>
    rename_i _ e1 e2 v1 v2 vl v3 A_src body_src l_name
    cases helab with
    | mlink _ Γ₁ A_inner mt l_inner _ _ ce1 ce2 h_elab1 h_elab2 h_lookup =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := step3 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih1 h_elab2 henv henv_val
      cases helab_v2 with
      | mclos _ _ _ _ _ _ _ _ hval_v2 h_env2 h_body =>
        rename_i ctx_inner ce1_inner ce2_inner
        have hv1_val := eval_produces_value henv_val bstep1
        obtain ⟨vc_l, hrlookup_v, helab_vl⟩ :=
          sel_preservation hv1_val helab_v1 sel1 h_lookup
        have hvl_val := source_sel_value hv1_val sel1
        have hval_lrec := SCE.Value.vlrec (l := l_name) hvl_val
        have hval_env := SCE.Value.vmrg hval_v2 hval_lrec
        have helab_lrec := elabExp.elrec .top _ _ _ l_name helab_vl
        have helab_lrec_weak :=
          elab_value_weaken helab_lrec hval_lrec (SCE.Typ.and .top ctx_inner)
        have helab_env := elabExp.edmrg .top _ _ _ _ _ _ h_env2 helab_lrec_weak
        obtain ⟨vc3, hbig3, helab_v3⟩ := ih2 h_body helab_env hval_env
        have hv3_val := eval_produces_value hval_env step2
        have helab_v3_weak :=
          elab_value_weaken helab_v3 hv3_val (SCE.Typ.and .top Γ₁)
        have helab_result := elabExp.edmrg .top _ _ _ _ _ _
          helab_v1 helab_v3_weak
        have hρc := elab_value henv henv_val
        exact ⟨.mrg vc1 vc3,
               linkStep_eval hρc hbig1 hbig2
                 (wire_eval_rcd hρc (ebig_produces_value hρc hbig1)
                   (ebig_produces_value hρc hbig2) hrlookup_v)
                 hbig3,
               helab_result⟩
  | mlinkn h1 bstep1 bstep2 hsp bstep3 ih1 ih2 ih3 =>
    cases helab with
    | mlinkn _ Γ₁ D_e B_e _ _ ce1 ce2 h_elab1 h_elab2 hok =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_v2 with
      | mclos _ ctx_inner _ _ _ _ ce_env ce_body hval_v2 h_env2 h_body =>
        have hv1_val := eval_produces_value henv_val bstep1
        have hρc := elab_value henv henv_val
        obtain ⟨cpkg, hbigw, helab_pkg⟩ :=
          wire_eval hok hsp hv1_val helab_v1
            (Core.Value.vmrg
              (Core.Value.vmrg (Core.Value.vmrg hρc (ebig_produces_value hρc hbig1))
                (ebig_produces_value hρc hbig2))
              (ebig_produces_value hρc hbig1))
            Core.LookupV.lvzero
        have hvpkg := S_Sem.selpkg_value hsp hv1_val
        have hval_env := SCE.Value.vmrg hval_v2 hvpkg
        have helab_env := elabExp.edmrg .top _ _ _ _ _ _ h_env2
          (elab_value_weaken helab_pkg hvpkg _)
        obtain ⟨vc3, hbig3, helab_v3⟩ := ih3 h_body helab_env hval_env
        have hv3_val := eval_produces_value hval_env bstep3
        have helab_result := elabExp.edmrg .top _ _ _ _ _ _
          helab_v1 (elab_value_weaken helab_v3 hv3_val _)
        exact ⟨.mrg vc1 vc3,
               linkStep_eval hρc hbig1 hbig2 hbigw hbig3,
               helab_result⟩
  | inl hval_ρ hstep ih =>
    cases helab with
    | einl _ A_inner B_inner _ ce h_elab =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      exact ⟨_, EBig.ebinl hbig, elabExp.einl .top _ _ _ _ helab_v⟩
  | inr hval_ρ hstep ih =>
    cases helab with
    | einr _ A_inner B_inner _ ce h_elab =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      exact ⟨_, EBig.ebinr hbig, elabExp.einr .top _ _ _ _ helab_v⟩
  | case_inl hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | ecase _ A_inner B_inner C_inner _ _ _ ce ce1 ce2 h_elab h_elab1 h_elab2 =>
      obtain ⟨vc_inl, hbig1, helab_inl⟩ := ih1 h_elab henv henv_val
      cases helab_inl with
      | einl _ _ _ _ ce_v h_v =>
        have h_inl_val := eval_produces_value henv_val hstep1
        cases h_inl_val with
        | vinl hv1 =>
          have hval_mrg := SCE.Value.vmrg henv_val hv1
          have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _
            henv (elab_value_weaken h_v hv1 _)
          obtain ⟨vc, hbig2, helab_v⟩ := ih2 h_elab1 helab_mrg hval_mrg
          exact ⟨vc, EBig.ebcasel hbig1 hbig2, helab_v⟩
  | case_inr hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | ecase _ A_inner B_inner C_inner _ _ _ ce ce1 ce2 h_elab h_elab1 h_elab2 =>
      obtain ⟨vc_inr, hbig1, helab_inr⟩ := ih1 h_elab henv henv_val
      cases helab_inr with
      | einr _ _ _ _ ce_v h_v =>
        have h_inr_val := eval_produces_value henv_val hstep1
        cases h_inr_val with
        | vinr hv1 =>
          have hval_mrg := SCE.Value.vmrg henv_val hv1
          have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _
            henv (elab_value_weaken h_v hv1 _)
          obtain ⟨vc, hbig2, helab_v⟩ := ih2 h_elab2 helab_mrg hval_mrg
          exact ⟨vc, EBig.ebcaser hbig1 hbig2, helab_v⟩
  | fclos_val henv_src hval =>
    cases helab with
    | efclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact ⟨_, EBig.efclos (elab_value henv henv_val) (elab_value h1 hval),
               elabExp.efclos .top _ _ _ _ _ _ _ hval h1 h2⟩
  | flam hval =>
    cases helab with
    | eflam _ _ _ _ ce h_body =>
      exact ⟨Core.Exp.fclos ρc _ _ ce,
             EBig.ebflam (elab_value henv henv_val),
             elabExp.efclos .top _ _ _ _ _ _ _ henv_val henv h_body⟩
  | app_fclos hval_ρ hstep1 hstep2 hstep_body ih1 ih2 ih3 =>
    cases helab with
    | eapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc_clos, hbig1, helab_clos⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_clos with
      | efclos _ _ _ _ _ _ _ _ hval_v1 h_env_v1 h_body_elab =>
        rename_i ctx_clos ce_env ce_body
        have hv1_val := eval_produces_value henv_val hstep1
        cases hv1_val with
        | vfclos hval_inner =>
          have hv2_val := eval_produces_value henv_val hstep2
          have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
            (elabExp.edmrg .top _ _ _ _ _ _ h_env_v1
              (elabExp.efclos _ _ _ _ _ _ _ _ hval_inner h_env_v1 h_body_elab))
            (elab_value_weaken helab_v2 hv2_val _)
          obtain ⟨vc_result, hbig3, helab_result⟩ := ih3 h_body_elab helab_body_env
            (SCE.Value.vmrg (SCE.Value.vmrg hval_inner (SCE.Value.vfclos hval_inner)) hv2_val)
          exact ⟨vc_result,
                 EBig.ebfapp hbig1 hbig2 hbig3,
                 helab_result⟩
  | fold hval_ρ hstep ih =>
    cases helab with
    | efold _ T_inner _ ce h_elab =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      exact ⟨_, EBig.ebfold hbig, elabExp.efold .top _ _ _ helab_v⟩
  | unfold hval_ρ hstep ih =>
    cases helab with
    | eunfold _ T_inner _ _ ce h_elab heq =>
      subst heq
      obtain ⟨vc_fold, hbig, helab_fold⟩ := ih h_elab henv henv_val
      cases helab_fold with
      | efold _ _ _ ce_v h_v =>
        exact ⟨_, EBig.ebunfold hbig, h_v⟩

theorem whole_program_correctness
    {A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp} {vs : SCE.Exp}
    (helab : elabExp SCE.Typ.top es A ec)
    (heval : S_Sem.BStep .unit es vs)
    : ∃ vc, EBig .unit ec vc ∧ elabExp SCE.Typ.top vs A vc := by
  exact semantic_preservation helab heval (elabExp.eunit SCE.Typ.top) SCE.Value.vunit

-- Linking and separate compilation

def linkSCE (e₁ e₂ : SCE.Exp) : SCE.Exp :=
  .mlink e₁ e₂

/-- The linker's binary step produces a well-typed unit at `A₁ & B`. -/
theorem core_link_typed
    {Γ A₁ A B : Core.Typ} {l : String} {ec₁ ec₂ ec : Core.Exp}
    (hlink : CoreLink l A₁ A B ec₁ ec₂ ec)
    (h₁ : HasType Γ ec₁ A₁)
    (h₂ : HasType Γ ec₂ (.arr (.rcd l A) B))
    : HasType Γ ec (.and A₁ B) := by
  cases hlink with
  | link _ _ _ _ _ _ hrlookup =>
    exact linkedCore_typed h₁ h₂ (wire_typed_rcd hrlookup)

/-- **Separate compilation (binary `link`).**  Elaborate the provider and the
functor separately, compose the compiled pieces with the linker's step, and the
result evaluates in lock-step with source-level `link`. -/
theorem separate_compilation
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (hlink : CoreLink l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂ ec)
    (heval : S_Sem.BStep ρs (.mlink es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  cases hlink with
  | link _ _ _ _ _ _ _ =>
    have hmlink := elabExp.mlink Γ Γ₁ A B l es₁ es₂ ec₁ ec₂ helab₁ helab₂ hlookup
    exact semantic_preservation hmlink heval henv henv_val

/-- **Separate compilation, closed** — the toolchain's actual case: closed
compiled units, empty initial environment. -/
theorem separate_compilation_closed
    {Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (heval : S_Sem.BStep .unit (.mlink es₁ es₂) vs)
    : ∃ vc, EBig .unit (linkedCore (elabTyp Γ₁) (elabTyp (SCE.Typ.rcd l A)) (elabTyp B) ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  have hlink : CoreLink l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂
      (linkedCore (elabTyp Γ₁) (elabTyp (SCE.Typ.rcd l A)) (elabTyp B) ec₁ ec₂) :=
    CoreLink.link _ _ _ _ _ _ (type_safe_record_lookup hlookup)
  exact separate_compilation helab₁ helab₂ hlookup hlink heval (elabExp.eunit .top) SCE.Value.vunit

-- N-ary linking and separate compilation

/-- The linker's n-ary step: the provider is wired to every import of the
elaborated interface `⟦D⟧` by projection from its single binding. -/
inductive CoreLinkN
    : SCE.Typ → Core.Typ → Core.Typ → Core.Exp → Core.Exp → Core.Exp → Prop where
  | link (D : SCE.Typ) (A₁ B : Core.Typ) (ec₁ ec₂ : Core.Exp)
    : CoreLinkN D A₁ B ec₁ ec₂ (linkedCore A₁ (elabTyp D) B ec₁ ec₂)

theorem core_linkn_typed
    {Γ₁ D : SCE.Typ} {Γc B : Core.Typ} {ec₁ ec₂ ec : Core.Exp}
    (hlink : CoreLinkN D (elabTyp Γ₁) B ec₁ ec₂ ec)
    (hok : LinkOk Γ₁ D)
    (h₁ : HasType Γc ec₁ (elabTyp Γ₁))
    (h₂ : HasType Γc ec₂ (.arr (elabTyp D) B))
    : HasType Γc ec (.and (elabTyp Γ₁) B) := by
  cases hlink with
  | link => exact linkedCore_typed h₁ h₂ (wire_typed hok)

/-- **Separate compilation (n-ary `linkall`).**  As above, with a whole import
interface `D` wired by projection from the once-bound provider. -/
theorem separate_compilation_n
    {Γ Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (hlink : CoreLinkN D (elabTyp Γ₁) (elabTyp B) ec₁ ec₂ ec)
    (heval : S_Sem.BStep ρs (.mlinkn es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  cases hlink with
  | link =>
    have hn := elabExp.mlinkn Γ Γ₁ D B es₁ es₂ ec₁ ec₂ helab₁ helab₂ hok
    exact semantic_preservation hn heval henv henv_val

/-- **Separate compilation, n-ary, closed.** -/
theorem separate_compilation_n_closed
    {Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (heval : S_Sem.BStep .unit (.mlinkn es₁ es₂) vs)
    : ∃ vc, EBig .unit (linkedCore (elabTyp Γ₁) (elabTyp D) (elabTyp B) ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  have hlink : CoreLinkN D (elabTyp Γ₁) (elabTyp B) ec₁ ec₂
      (linkedCore (elabTyp Γ₁) (elabTyp D) (elabTyp B) ec₁ ec₂) :=
    CoreLinkN.link _ _ _ _ _
  exact separate_compilation_n helab₁ helab₂ hok hlink heval (elabExp.eunit .top) SCE.Value.vunit

-- Determinism

private theorem lookupV_deterministic
    {v v₁ v₂ : SCE.Exp} {n : Nat}
    (h₁ : S_Sem.LookupV v n v₁)
    (h₂ : S_Sem.LookupV v n v₂)
    : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | dmrg_zero => cases h₂ with | dmrg_zero => rfl
  | dmrg_succ _ ih => cases h₂ with | dmrg_succ h₂' => exact ih h₂'
  | nmrg_zero => cases h₂ with | nmrg_zero => rfl
  | nmrg_succ _ ih => cases h₂ with | nmrg_succ h₂' => exact ih h₂'

private theorem sel_deterministic
    {v v₁ v₂ : SCE.Exp} {vc : Core.Exp} {A B : SCE.Typ} {l : String}
    (hval : SCE.Value v)
    (helab : elabExp SCE.Typ.top v A vc)
    (hlookup : SCE.SRLookup A l B)
    (hsel₁ : S_Sem.Sel v l v₁)
    (hsel₂ : S_Sem.Sel v l v₂)
    : v₁ = v₂ := by
  induction hsel₁ generalizing v₂ A B vc with
  | rcd =>
    cases hval with | vlrec hv =>
    cases helab with | elrec _ _ _ _ _ h =>
    cases hlookup with | zero =>
    cases hsel₂ with | rcd => rfl
  | dmrg_left hsel_inner ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    cases hlookup with
    | andl _ _ _ _ hrl hcond =>
      cases hsel₂ with
      | dmrg_left hsel₂' => exact ih hv1 h1 hrl hsel₂'
      | dmrg_right hsel₂' =>
        have hlin := sel_implies_label_in hv2
          (elab_value_weaken h2 hv2 (SCE.Typ.top)) hsel₂'
        exact absurd hlin hcond
    | andr _ _ _ _ hrl hcond =>
      have hlin := sel_implies_label_in hv1 h1 hsel_inner
      exact absurd hlin hcond
  | dmrg_right hsel_inner ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    have h2_weak := elab_value_weaken h2 hv2 (SCE.Typ.top)
    cases hlookup with
    | andr _ _ _ _ hrl hcond =>
      cases hsel₂ with
      | dmrg_right hsel₂' => exact ih hv2 h2_weak hrl hsel₂'
      | dmrg_left hsel₂' =>
        have hlin := sel_implies_label_in hv1 h1 hsel₂'
        exact absurd hlin hcond
    | andl _ _ _ _ hrl hcond =>
      have hlin := sel_implies_label_in hv2 h2_weak hsel_inner
      exact absurd hlin hcond
  | nmrg_left   => cases hval
  | nmrg_right  => cases hval

private theorem selpkg_deterministic
    {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D)
    {v : SCE.Exp} {vc : Core.Exp}
    (hval : SCE.Value v)
    (helab : elabExp SCE.Typ.top v Γ₁ vc)
    : ∀ {pkg₁ pkg₂ : SCE.Exp},
      S_Sem.SelPkg v D pkg₁
      → S_Sem.SelPkg v D pkg₂
      → pkg₁ = pkg₂ := by
  induction hok with
  | one hrl =>
    intro pkg₁ pkg₂ hsp₁ hsp₂
    cases hsp₁ with | one hsel₁ =>
    cases hsp₂ with | one hsel₂ =>
    rw [sel_deterministic hval helab hrl hsel₁ hsel₂]
  | more hok' hrl ih =>
    intro pkg₁ pkg₂ hsp₁ hsp₂
    cases hsp₁ with | more hsp₁' hsel₁ =>
    cases hsp₂ with | more hsp₂' hsel₂ =>
    rw [ih hsp₁' hsp₂', sel_deterministic hval helab hrl hsel₁ hsel₂]

theorem bigstep_deterministic_gen
    {Γ A : SCE.Typ} {e ρ v₁ v₂ : SCE.Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ e A ec)
    (henv : elabExp SCE.Typ.top ρ Γ ρc)
    (henv_val : SCE.Value ρ)
    (heval₁ : S_Sem.BStep ρ e v₁)
    (heval₂ : S_Sem.BStep ρ e v₂)
    : v₁ = v₂ := by
  induction heval₁ generalizing v₂ Γ A ec ρc with
  | query _ =>
    cases helab; cases heval₂; rfl
  | lit _ =>
    cases helab; cases heval₂; rfl
  | unit _ =>
    cases helab; cases heval₂; rfl
  | clos_val _ _ =>
    cases helab with
    | eclos _ _ _ _ _ _ _ _ _ h1 h2 =>
      cases heval₂ with | clos_val => rfl
  | mclos_val _ _ =>
    cases helab with
    | mclos _ _ _ _ _ _ _ _ _ h1 h2 =>
      cases heval₂ with | mclos_val => rfl
  | proj hval₁ hstep₁ hlook₁ ih₁ =>
    cases helab with
    | eproj _ A' _ _ ce _ h_elab h_slook =>
      cases heval₂ with
      | proj _ hstep₂ hlook₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this] at hlook₁
        exact lookupV_deterministic hlook₁ hlook₂
  | lam _ =>
    cases helab; cases heval₂; rfl
  | box hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | ebox _ ctx' _ _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | box _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hv₁_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, hv₁_elab⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        exact ih₁b h_elab2 hv₁_elab hv₁_val hstep₂b
  | app_clos hval₁ hstep₁f hstep₁a hstep₁b ih₁f ih₁a ih₁b =>
    cases helab with
    | eapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | app_clos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
        have heq_a := ih₁a h_elab2 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hvclos := eval_produces_value henv_val hstep₁f
        cases hvclos with
        | vclos hval_inner =>
          have hva := eval_produces_value henv_val hstep₁a
          have ⟨_, _, helab_clos⟩ := semantic_preservation h_elab1 hstep₁f henv henv_val
          cases helab_clos with
          | eclos _ _ _ _ _ _ _ _ _ h_env_inner h_body =>
            have ⟨_, _, helab_arg⟩ := semantic_preservation h_elab2 hstep₁a henv henv_val
            have hval_body_env := SCE.Value.vmrg hval_inner hva
            have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _ h_env_inner
              (elab_value_weaken helab_arg hva _)
            exact ih₁b h_body helab_body_env hval_body_env hstep₂b
      | app_fclos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
  | app_mclos hval₁ hstep₁f hstep₁a hstep₁b ih₁f ih₁a ih₁b =>
    cases helab with
    | mapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | app_mclos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
        have heq_a := ih₁a h_elab2 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hvclos := eval_produces_value henv_val hstep₁f
        cases hvclos with
        | vmclos hval_inner =>
          have hva := eval_produces_value henv_val hstep₁a
          have ⟨_, _, helab_clos⟩ := semantic_preservation h_elab1 hstep₁f henv henv_val
          cases helab_clos with
          | mclos _ _ _ _ _ _ _ _ _ h_env_inner h_body =>
            have ⟨_, _, helab_arg⟩ := semantic_preservation h_elab2 hstep₁a henv henv_val
            have hval_body_env := SCE.Value.vmrg hval_inner hva
            have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _ h_env_inner
              (elab_value_weaken helab_arg hva _)
            exact ih₁b h_body helab_body_env hval_body_env hstep₂b
  | dmrg hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | edmrg _ A' B' _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | dmrg _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hv1_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, helab_v1⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        have hval_mrg := SCE.Value.vmrg henv_val hv1_val
        have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _ henv
          (elab_value_weaken helab_v1 hv1_val _)
        have heq_b := ih₁b h_elab2 helab_mrg hval_mrg hstep₂b
        rw [heq_a, heq_b]
  | nmrg hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | enmrg _ A' B' _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | nmrg _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        have heq_b := ih₁b h_elab2 henv henv_val hstep₂b
        rw [heq_a, heq_b]
  | lrec hval₁ hstep₁ ih₁ =>
    cases helab with
    | elrec _ _ _ _ _ h_elab =>
      cases heval₂ with
      | lrec _ hstep₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this]
  | rproj hval₁ hstep₁ hsel₁ ih₁ =>
    cases helab with
    | erproj _ A' B' _ _ l h_elab h_slook =>
      cases heval₂ with
      | rproj _ hstep₂ hsel₂ =>
        have heq := ih₁ h_elab henv henv_val hstep₂
        rw [heq] at hsel₁
        have hv_val := eval_produces_value henv_val hstep₂
        have ⟨_, _, helab_v⟩ := semantic_preservation h_elab hstep₂ henv henv_val
        exact sel_deterministic hv_val helab_v h_slook hsel₁ hsel₂
  | letb hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | letb _ A' B' _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | letb _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hv1_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, helab_v1⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        have hval_mrg := SCE.Value.vmrg henv_val hv1_val
        have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _ henv
          (elab_value_weaken helab_v1 hv1_val _)
        exact ih₁b h_elab2 helab_mrg hval_mrg hstep₂b
  | openm hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | openm _ A' B' _ _ ce1 ce2 l h_elab1 h_elab2 =>
      cases heval₂ with
      | openm _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        cases heq_a
        have hv_val := eval_produces_value henv_val hstep₂a
        cases hv_val with
        | vlrec hval_inner =>
          have ⟨_, _, helab_rcd⟩ := semantic_preservation h_elab1 hstep₂a henv henv_val
          cases helab_rcd with
          | elrec _ _ _ _ _ helab_inner =>
            have hval_mrg := SCE.Value.vmrg henv_val hval_inner
            have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _ henv
              (elab_value_weaken helab_inner hval_inner _)
            exact ih₁b h_elab2 helab_mrg hval_mrg hstep₂b
  | mstruct_sandboxed hval₁ hstep₁ ih₁ =>
    cases helab with
    | mstruct _ _ _ _ _ ce _ _ hs1 hs2 h_elab =>
      have hctx := hs1 rfl; rw [hctx] at h_elab
      cases heval₂ with
      | mstruct_sandboxed _ hstep₂ =>
        rw [ih₁ h_elab (elabExp.eunit .top) SCE.Value.vunit hstep₂]
    | mstructv _ _ _ _ _ hvse h =>
      cases heval₂ with
      | mstruct_sandboxed _ hstep₂ =>
        rw [bstep_value_id hvse hstep₁, bstep_value_id hvse hstep₂]
  | mstruct_open hval₁ hstep₁ ih₁ =>
    cases helab with
    | mstruct _ _ _ _ _ ce _ _ hs1 hs2 h_elab =>
      have hctx := hs2 rfl; rw [hctx] at h_elab
      cases heval₂ with
      | mstruct_open _ hstep₂ =>
        rw [ih₁ h_elab henv henv_val hstep₂]
    | mstructv _ _ _ _ _ hvse h =>
      cases heval₂ with
      | mstruct_open _ hstep₂ =>
        rw [bstep_value_id hvse hstep₁, bstep_value_id hvse hstep₂]
  | mfunctor_sandboxed _ =>
    cases helab with | mfunctor => cases heval₂ with | mfunctor_sandboxed => rfl
  | mfunctor_open _ =>
    cases helab with | mfunctor => cases heval₂ with | mfunctor_open => rfl
  | mlink hval₁ hstep₁a hstep₁b hsel₁ hstep₁c ih₁a ih₁b ih₁c =>
    rename_i _ _ _ _ _ _ _ l_bstep
    cases helab with
    | mlink _ Γ₁ A_inner B_inner l_elab _ _ ce1 ce2 h_elab1 h_elab2 h_lookup =>
      cases heval₂ with
      | mlink _ hstep₂a hstep₂b hsel₂ hstep₂c =>
        -- e₁ produces the same value
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        -- e₂ produces the same mclos (unifies labels, bodies, etc.)
        have heq_b := ih₁b h_elab2 henv henv_val hstep₂b
        cases heq_b
        -- Now hsel₁ and hsel₂ use the same label (l_bstep from BStep)
        -- but h_lookup uses l_elab. Connect them via semantic_preservation.
        have hv1_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, helab_v1⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        have ⟨_, _, helab_mclos⟩ := semantic_preservation h_elab2 hstep₁b henv henv_val
        cases helab_mclos with
        | mclos _ ctx_inner _ _ _ _ _ _ hval_v2 h_env2 h_body =>
          have htype_eq := inference_uniqueness
            (semantic_preservation h_elab2 hstep₁b henv henv_val).choose_spec.2
            (elabExp.mclos .top ctx_inner _ _ _ _ _ _ hval_v2 h_env2 h_body)
          cases htype_eq
          -- Rewrite hsel₂ to use heval₁'s v₁
          rw [← heq_a] at hsel₂
          -- sel deterministic: vₗ₁ = vₗ₂, then subst to unify
          have heq_sel := sel_deterministic hv1_val helab_v1 h_lookup hsel₁ hsel₂
          subst heq_sel
          -- build env elaboration for body
          have hvl_val := source_sel_value hv1_val hsel₁
          obtain ⟨_, _, helab_vl⟩ := sel_preservation hv1_val helab_v1 hsel₁ h_lookup
          have helab_lrec := elabExp.elrec .top _ _ _ l_bstep helab_vl
          have hval_lrec := SCE.Value.vlrec (l := l_bstep) hvl_val
          have hval_env := SCE.Value.vmrg hval_v2 hval_lrec
          have helab_lrec_weak :=
            elab_value_weaken helab_lrec hval_lrec (SCE.Typ.and .top ctx_inner)
          have helab_env := elabExp.edmrg .top _ _ _ _ _ _ h_env2 helab_lrec_weak
          have heq_c := ih₁c h_body helab_env hval_env hstep₂c
          rw [heq_a, heq_c]
  | mlinkn hval₁ hstep₁a hstep₁b hsp₁ hstep₁c ih₁a ih₁b ih₁c =>
    cases helab with
    | mlinkn _ Γ₁ D_e B_e _ _ ce1 ce2 h_elab1 h_elab2 hok =>
      cases heval₂ with
      | mlinkn _ hstep₂a hstep₂b hsp₂ hstep₂c =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        have heq_b := ih₁b h_elab2 henv henv_val hstep₂b
        cases heq_b
        have hv1_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, helab_v1⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        have ⟨_, _, helab_mclos⟩ := semantic_preservation h_elab2 hstep₁b henv henv_val
        cases helab_mclos with
        | mclos _ ctx_inner _ _ _ _ _ _ hval_v2 h_env2 h_body =>
          rw [← heq_a] at hsp₂
          have heq_pkg := selpkg_deterministic hok hv1_val helab_v1 hsp₁ hsp₂
          subst heq_pkg
          have hvpkg := S_Sem.selpkg_value hsp₁ hv1_val
          have ⟨_, helab_pkg⟩ := selpkg_elab hok hsp₁ hv1_val helab_v1
          have hval_env := SCE.Value.vmrg hval_v2 hvpkg
          have helab_env := elabExp.edmrg .top _ _ _ _ _ _ h_env2
            (elab_value_weaken helab_pkg hvpkg _)
          have heq_c := ih₁c h_body helab_env hval_env hstep₂c
          rw [heq_a, heq_c]
  | inl hval₁ hstep₁ ih₁ =>
    cases helab with
    | einl _ _ _ _ _ h_elab =>
      cases heval₂ with
      | inl _ hstep₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this]
  | inr hval₁ hstep₁ ih₁ =>
    cases helab with
    | einr _ _ _ _ _ h_elab =>
      cases heval₂ with
      | inr _ hstep₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this]
  | case_inl hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | ecase _ A' B' C' _ _ _ ce ce1 ce2 h_elab h_elab1 h_elab2 =>
      cases heval₂ with
      | case_inl _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab henv henv_val hstep₂a
        cases heq_a
        have h_inl_val := eval_produces_value henv_val hstep₁a
        cases h_inl_val with
        | vinl hv1 =>
          have ⟨_, _, helab_inl⟩ := semantic_preservation h_elab hstep₁a henv henv_val
          cases helab_inl with
          | einl _ _ _ _ _ h_v =>
            have hval_mrg := SCE.Value.vmrg henv_val hv1
            have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _
              henv (elab_value_weaken h_v hv1 _)
            exact ih₁b h_elab1 helab_mrg hval_mrg hstep₂b
      | case_inr _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab henv henv_val hstep₂a
        cases heq_a
  | case_inr hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | ecase _ A' B' C' _ _ _ ce ce1 ce2 h_elab h_elab1 h_elab2 =>
      cases heval₂ with
      | case_inr _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab henv henv_val hstep₂a
        cases heq_a
        have h_inr_val := eval_produces_value henv_val hstep₁a
        cases h_inr_val with
        | vinr hv1 =>
          have ⟨_, _, helab_inr⟩ := semantic_preservation h_elab hstep₁a henv henv_val
          cases helab_inr with
          | einr _ _ _ _ _ h_v =>
            have hval_mrg := SCE.Value.vmrg henv_val hv1
            have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _
              henv (elab_value_weaken h_v hv1 _)
            exact ih₁b h_elab2 helab_mrg hval_mrg hstep₂b
      | case_inl _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab henv henv_val hstep₂a
        cases heq_a
  | fclos_val _ _ =>
    cases helab with
    | efclos _ _ _ _ _ _ _ _ _ h1 h2 =>
      cases heval₂ with | fclos_val => rfl
  | flam _ =>
    cases helab; cases heval₂; rfl
  | app_fclos hval₁ hstep₁f hstep₁a hstep₁b ih₁f ih₁a ih₁b =>
    cases helab with
    | eapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | app_clos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
      | app_fclos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
        have heq_a := ih₁a h_elab2 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hvclos := eval_produces_value henv_val hstep₁f
        cases hvclos with
        | vfclos hval_inner =>
          have hva := eval_produces_value henv_val hstep₁a
          have ⟨_, _, helab_clos⟩ := semantic_preservation h_elab1 hstep₁f henv henv_val
          cases helab_clos with
          | efclos _ _ _ _ _ _ _ _ _ h_env_inner h_body =>
            have ⟨_, _, helab_arg⟩ := semantic_preservation h_elab2 hstep₁a henv henv_val
            have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
              (elabExp.edmrg .top _ _ _ _ _ _ h_env_inner
                (elabExp.efclos _ _ _ _ _ _ _ _ hval_inner h_env_inner h_body))
              (elab_value_weaken helab_arg hva _)
            exact ih₁b h_body helab_body_env
              (SCE.Value.vmrg (SCE.Value.vmrg hval_inner (SCE.Value.vfclos hval_inner)) hva)
              hstep₂b
  | fold hval₁ hstep₁ ih₁ =>
    cases helab with
    | efold _ _ _ _ h_elab =>
      cases heval₂ with
      | fold _ hstep₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this]
  | unfold hval₁ hstep₁ ih₁ =>
    cases helab with
    | eunfold _ _ _ _ _ h_elab heq =>
      cases heval₂ with
      | unfold _ hstep₂ =>
        have heq_f := ih₁ h_elab henv henv_val hstep₂
        cases heq_f
        rfl

theorem bigstep_deterministic
    {A : SCE.Typ} {e v₁ v₂ : SCE.Exp}
    (helab : ∃ ec, elabExp SCE.Typ.top e A ec)
    (heval₁ : S_Sem.BStep SCE.Exp.unit e v₁)
    (heval₂ : S_Sem.BStep SCE.Exp.unit e v₂)
    : v₁ = v₂ := by
  obtain ⟨ec, helab⟩ := helab
  exact bigstep_deterministic_gen helab (elabExp.eunit .top) SCE.Value.vunit heval₁ heval₂

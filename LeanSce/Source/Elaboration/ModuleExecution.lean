import LeanSce.Source.Elaboration.ExecutionRelation
import LeanSce.Source.Elaboration.Templates
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.Evaluation

/-!
# Source / Elaboration / ModuleExecution

Proofs and supporting constructions for module execution.
-/

/-! ## Source Head Infrastructure -/

namespace LeanSce.Source

theorem FiniteCorrespondence.prefix_right (hc : FiniteCorrespondence n ν e N E')
    (hs : Target.Steps N E E') : FiniteCorrespondence n ν e N E := by
  constructor
  · intro k hk v hv
    obtain ⟨V,hV,hr⟩ := hc.1 k hk v hv
    exact ⟨V,⟨hs.trans hV.1,hV.2⟩,hr⟩
  · intro k hk V hV
    obtain ⟨i,hi,hbody⟩ := hV.after_steps hs
    exact hc.2 i (by omega) V hbody

theorem HasType.box_operands (ht : HasType Δ h e a) :
    ∀ x body, e = .box x body → ∃ env, HasType Δ h x env ∧ HasType Δ env body a := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ => ∀ x body, e = .box x body →
      ∃ env, HasType Δ h x env ∧ HasType Δ env body a)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (t := ht)
  all_goals intros
  all_goals try trivial
  all_goals intros
  all_goals rename_i he
  all_goals cases he
  case box => exact ⟨_,by assumption,by assumption⟩
  case value => simp_all [Value,Term.isValue]
  case conv =>
    rename_i Δ h a b he hw x body ht ih
    obtain ⟨env,hx,hbody⟩ := ih x body rfl
    exact ⟨env,hx,.conv hbody he hw⟩

theorem SmallCorrespondence.forward (small : SmallCorrespondence n) (hk : k < n)
    (hΔ : Context.Valid Δ) (ht : HasType Δ h e a) (he : Elaborates e E)
    (hν : ValueType Δ ν h) (henv : Related ν N) (hv : TerminatesIn ν e k v) :
    ∃ V, Target.Terminates N E V ∧ Related v V :=
  (small k hk Δ h a e E ν N hΔ ht he hν henv).1 k (Nat.le_refl _) v hv

theorem SmallCorrespondence.backward (small : SmallCorrespondence n) (hk : k < n)
    (hΔ : Context.Valid Δ) (ht : HasType Δ h e a) (he : Elaborates e E)
    (hν : ValueType Δ ν h) (henv : Related ν N) (hV : Target.TerminatesIn N E k V) :
    ∃ v, Terminates ν e v ∧ Related v V :=
  (small k hk Δ h a e E ν N hΔ ht he hν henv).2 k (Nat.le_refl _) V hV

end LeanSce.Source

/-! ## Source Link Evaluation -/

namespace LeanSce.Source

theorem TerminatesIn.run_head_inv (hν : Value ν)
    (ht : TerminatesIn ν (.run p i o cd m provider) n w) :
    ∃ M P a b c, a < n ∧ b < n ∧ c < n ∧
      TerminatesIn ν m a M ∧ TerminatesIn ν provider b P ∧
      TerminatesIn ν (.invoke i o M (.view (.record p) (.record i) cd P)) c w := by
  obtain ⟨M,a,q,hq,hm,hr⟩ := strict_run_module.decompose_counted ht
  obtain ⟨P,b,r,hr',hp,hrest⟩ := (strict_run_provider hm.2).decompose_counted hr
  obtain ⟨c,hc,hcall⟩ := hrest.after_step (e' := .invoke i o M (.view (.record p) (.record i) cd P))
    ⟨hν,by simp [step_run_eq,(show M.isValue = true from hm.2),(show P.isValue = true from hp.2)]⟩
  exact ⟨M,P,a,b,c,by omega,by omega,by omega,hm,hp,hcall⟩

theorem Terminates.run_head_forward (hν : Value ν) (hm : Terminates ν m M)
    (hp : Terminates ν provider P)
    (ht : Terminates ν (.invoke i o M (.view (.record p) (.record i) cd P)) w) :
    Terminates ν (.run p i o cd m provider) w := by
  apply strict_run_module.terminates hm
  apply (strict_run_provider hm.2).terminates hp
  exact ⟨.next ⟨hν,by simp [step_run_eq,(show M.isValue = true from hm.2),
    (show P.isValue = true from hp.2)]⟩ ht.1,ht.2⟩

theorem TerminatesIn.link_head_inv (hν : Value ν)
    (ht : TerminatesIn ν (.link p i o cd provider m) n w) :
    ∃ P M a b c, a < n ∧ b < n ∧ c < n ∧
      TerminatesIn ν provider a P ∧ TerminatesIn ν m b M ∧
      TerminatesIn ν (.merge P (.run p i o cd M P)) c w := by
  obtain ⟨P,a,q,hq,hp,hr⟩ := strict_link_provider.decompose_counted ht
  obtain ⟨M,b,r,hr',hm,hrest⟩ := (strict_link_module hp.2).decompose_counted hr
  obtain ⟨c,hc,hcall⟩ := hrest.after_step (e' := .merge P (.run p i o cd M P))
    ⟨hν,by simp [step_link_eq,(show M.isValue = true from hm.2),(show P.isValue = true from hp.2)]⟩
  exact ⟨P,M,a,b,c,by omega,by omega,by omega,hp,hm,hcall⟩

theorem Terminates.link_head_forward (hν : Value ν) (hp : Terminates ν provider P)
    (hm : Terminates ν m M) (ht : Terminates ν (.merge P (.run p i o cd M P)) w) :
    Terminates ν (.link p i o cd provider m) w := by
  apply strict_link_provider.terminates hp
  apply (strict_link_module hp.2).terminates hm
  exact ⟨.next ⟨hν,by simp [step_link_eq,(show M.isValue = true from hm.2),
    (show P.isValue = true from hp.2)]⟩ ht.1,ht.2⟩

theorem TerminatesIn.provide_head_inv (hν : Value ν)
    (ht : TerminatesIn ν (.provide p j k o cd provider m) n w) :
    ∃ P M a b c, a < n ∧ b < n ∧ c < n ∧
      TerminatesIn ν provider a P ∧ TerminatesIn ν m b M ∧
      TerminatesIn ν (.resid M (.view (.record p) (.record j) cd P) j k o) c w := by
  obtain ⟨P,a,q,hq,hp,hr⟩ := strict_provide_provider.decompose_counted ht
  obtain ⟨M,b,r,hr',hm,hrest⟩ := (strict_provide_module hp.2).decompose_counted hr
  obtain ⟨c,hc,hcall⟩ := hrest.after_step (e' := .resid M (.view (.record p) (.record j) cd P) j k o)
    ⟨hν,by simp [step_provide_eq,(show M.isValue = true from hm.2),(show P.isValue = true from hp.2)]⟩
  exact ⟨P,M,a,b,c,by omega,by omega,by omega,hp,hm,hcall⟩

theorem Terminates.provide_head_forward (hν : Value ν) (hp : Terminates ν provider P)
    (hm : Terminates ν m M)
    (ht : Terminates ν (.resid M (.view (.record p) (.record j) cd P) j k o) w) :
    Terminates ν (.provide p j k o cd provider m) w := by
  apply strict_provide_provider.terminates hp
  apply (strict_provide_module hp.2).terminates hm
  exact ⟨.next ⟨hν,by simp [step_provide_eq,(show M.isValue = true from hm.2),
    (show P.isValue = true from hp.2)]⟩ ht.1,ht.2⟩

end LeanSce.Source

/-! ## Invoke Correspondence -/

namespace LeanSce.Source

private theorem finite_invoke_captured (small : SmallCorrespondence n)
    (hΔ : Context.Valid Δ)
    (hm : HasType Δ h (.moduleVal (.record fs) c i₀ o₀ body) (.module i o))
    (hi : HasType Δ h imports (.record i))
    (hcap : Related (.record fs) Cap) (hb : Elaborates body B) (hI : Related imports I)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.invoke i o (.moduleVal (.record fs) c i₀ o₀ body) imports) N
      (.app (.clo (.pair .unit Cap) (.record i₀.erase)
        (.box (.merge (.ix 1) (.ix 0)) B)) I) := by
  have hbox := invoke_moduleVal_typed hm hcap.values.1 hi hΔ
  obtain ⟨env,hmrg,hbody⟩ := hbox.box_operands _ _ rfl
  have hstep : Step ν (.invoke i o (.moduleVal (.record fs) c i₀ o₀ body) imports)
      (.box (.merge (.record fs) imports) body) :=
    ⟨hν.1,by simp [step_invoke_eq,Term.isValue,(show fs.isValue = true from hcap.values.1),
      (show imports.isValue = true from hI.values.1)]⟩
  constructor
  · intro k hk w hw
    obtain ⟨j,hj,ht⟩ := hw.after_step hstep
    obtain ⟨cap,a,b,hab,hmerge,hbdy⟩ := ht.native_box_inv hν.1
    obtain ⟨C,hC,hrC⟩ := small.forward (by omega) hΔ hmrg
      (.merge (.value hcap) (.value hI)) hν henv hmerge
    have hcapt := valueType_of_typed_value (hmerge.1.toSteps.preservation hν hmrg hΔ) hmerge.2
    obtain ⟨W,hW,hrW⟩ := small.forward (by omega) hΔ hbody hb hcapt hrC hbdy
    exact ⟨W,Templates.captured_call_forward henv.values.2 hcap.values.2 hI.values.2
      (hC.merge_caller rfl hcap.values.2 hI.values.2) hW,hrW⟩
  · intro k hk W hW
    obtain ⟨C,a,b,ha,hb',hmerge,hbody'⟩ := Templates.captured_call_counted_inv
      henv.values.2 hcap.values.2 hI.values.2 hW
    have hmerge' := hmerge.merge_caller henv.values.2 hcap.values.2 hI.values.2
    obtain ⟨cap,hC,hrC⟩ := small.backward (by omega) hΔ hmrg
      (.merge (.value hcap) (.value hI)) hν henv hmerge'
    have hcapt := valueType_of_typed_value (hC.1.preservation hν hmrg hΔ) hC.2
    obtain ⟨w,hw,hrw⟩ := small.backward (by omega) hΔ hbody hb hcapt hrC hbody'
    exact ⟨w,⟨.next hstep (Terminates.native_box hν.1 hC hw).1,hw.2⟩,hrw⟩

private theorem finite_invoke_sandbox (small : SmallCorrespondence n)
    (hΔ : Context.Valid Δ)
    (hm : HasType Δ h (.moduleVal (.record .nil) .empty i₀ o₀ body) (.module i o))
    (hi : HasType Δ h imports (.record i))
    (hb : Elaborates body B) (hI : Related imports I)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.invoke i o (.moduleVal (.record .nil) .empty i₀ o₀ body) imports) N
      (.app (.clo .unit (.record i₀.erase) (.box (.ix 0) B)) I) := by
  obtain ⟨gs,rfl⟩ := hi.value_shape hI.values.1
  have hbox := invoke_moduleVal_typed hm rfl hi hΔ
  obtain ⟨env,hmrg,hbody⟩ := hbox.box_operands _ _ rfl
  have hmstep := merge_records_step hν.1 (show Value (.nil : Fields) from rfl) hI.values.1 rfl
  have hit := valueType_of_typed_value (hmrg.preservation hΔ ν hν _ hmstep.2) hI.values.1
  have hstep : Step ν (.invoke i o (.moduleVal (.record .nil) .empty i₀ o₀ body) (.record gs))
      (.box (.merge (.record .nil) (.record gs)) body) :=
    ⟨hν.1,by simp [step_invoke_eq,Term.isValue,(show gs.isValue = true from hI.values.1)]⟩
  have hprefix : Steps ν (.box (.merge (.record .nil) (.record gs)) body) (.box (.record gs) body) :=
    strict_box_left.lift_steps (.single hmstep)
  constructor
  · intro k hk w hw
    obtain ⟨j,hj,ht⟩ := hw.after_step hstep
    obtain ⟨p,hp,ht⟩ := ht.after_steps hprefix
    obtain ⟨q,hq,hbdy⟩ := ht.box_inv hν.1 hI.values.1
    obtain ⟨W,hW,hrW⟩ := small.forward (by omega) hΔ hbody hb hit hI hbdy
    exact ⟨W,Templates.sandbox_call_forward henv.values.2 hI.values.2 hW,hrW⟩
  · intro k hk W hW
    obtain ⟨j,hj,hbody'⟩ := Templates.sandbox_call_counted_inv henv.values.2 hI.values.2 hW
    obtain ⟨w,hw,hrw⟩ := small.backward (by omega) hΔ hbody hb hit hI hbody'
    exact ⟨w,⟨.next hstep (hprefix.trans (hw.box hν.1 hI.values.1).1),hw.2⟩,hrw⟩

private theorem finite_invoke_residual (small : SmallCorrespondence n)
    (hΔ : Context.Valid Δ)
    (hm : HasType Δ h (.resid original saved j k o₀) (.module i o))
    (hi : HasType Δ h imports (.record i))
    (hM : Related original M) (hs : Related saved S) (hI : Related imports I)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.invoke i o (.resid original saved j k o₀) imports) N
      (.app (.clo (.pair M S) (.record k.erase) Templates.residualBody) I) := by
  have hvm : Value (.resid original saved j k o₀) := Bool.and_eq_true_iff.mpr ⟨hM.values.1,hs.values.1⟩
  have hred := invoke_resid_typed hm hvm hi hΔ
  have hstep : Step ν (.invoke i o (.resid original saved j k o₀) imports)
      (.invoke (.union j k) o original (.merge saved imports)) :=
    ⟨hν.1,by simp [step_invoke_eq,Term.isValue,(show original.isValue = true from hM.values.1),
      (show saved.isValue = true from hs.values.1),(show imports.isValue = true from hI.values.1)]⟩
  have hElab : Elaborates (.invoke (.union j k) o original (.merge saved imports))
      (.app M (.merge S I)) := .invoke (.value hM) (.merge (.value hs) (.value hI))
  cases hm.value_origin hvm with
  | resid hm₀ hsaved wj wk hd he =>
    have hi' : HasType Δ h imports (.record k) :=
      .conv hi (.record he.module_inv.1.symm) (.record wk)
    obtain ⟨fs,Fs,rfl,rfl,_,hs⟩ := hs.record_shape hsaved.2 hΔ
    obtain ⟨gs,Gs,rfl,rfl,_,hI⟩ := hI.record_shape hi' hΔ
    have hft := (hsaved.2.elaborates hΔ (.value hs)).value_record_inv hs.values.2 wj.erase
    have hgt := (hi'.elaborates hΔ (.value hI)).value_record_inv hI.values.2 wk.erase
    have hcheck := hft.merge_check hgt hd.erase
    have hmerge : Target.Step N (.merge (.record Fs) (.record Gs)) (.record (Fs.append Gs)) := by
      refine ⟨henv.values.2,?_⟩
      rw [Target.step_merge_eq]
      simp only [Target.Term.isValue,(show Fs.isValue = true from hs.values.2),
        (show Gs.isValue = true from hI.values.2),Bool.not_true,Bool.false_eq_true,↓reduceIte,hcheck]
    have hjoinV : Target.Value (.record (Fs.append Gs)) := Target.Term.append_value Fs hs.values.2 hI.values.2
    have hMerge : Target.Terminates N (.merge (.record Fs) (.record Gs)) (.record (Fs.append Gs)) :=
      ⟨.single hmerge,hjoinV⟩
    constructor
    · intro q hq w hw
      obtain ⟨p,hp,hbody⟩ := hw.after_step hstep
      obtain ⟨W,hW,hrW⟩ := small.forward (by omega) hΔ hred hElab hν henv hbody
      obtain ⟨F,X,hF,hX,hCall⟩ := hW.app_decompose
      have hF' := hF.1.value_result hM.values.2
      subst F
      have hX' := hX.unique hMerge
      subst X
      exact ⟨W,Templates.residual_call_forward henv.values.2 hM.values.2 hs.values.2 hI.values.2 hcheck
        (hCall.app_caller rfl hM.values.2 hjoinV),hrW⟩
    · intro q hq W hW
      obtain ⟨p,hp,hcall⟩ := Templates.residual_call_inv_slack henv.values.2 hM.values.2
        hs.values.2 hI.values.2 hcheck hW
      have happStep : Target.Step N (.app M (.merge (.record Fs) (.record Gs)))
          (.app M (.record (Fs.append Gs))) := by
        refine ⟨henv.values.2,?_⟩
        rw [(Target.strict_app_right hM.values.2).step _ (by intro hv; cases hv),hmerge.2]
        rfl
      have hexp : Target.TerminatesIn N (.app M (.merge (.record Fs) (.record Gs))) (p+1) W :=
        ⟨.next happStep (hcall.app_caller henv.values.2 hM.values.2 hjoinV).1,hcall.2⟩
      obtain ⟨w,hw,hrw⟩ := small.backward (by omega) hΔ hred hElab hν henv hexp
      exact ⟨w,⟨.next hstep hw.1,hw.2⟩,hrw⟩

private theorem finite_invoke_values (small : SmallCorrespondence n)
    (hΔ : Context.Valid Δ) (hm : HasType Δ h m (.module i o))
    (hi : HasType Δ h imports (.record i))
    (hrm : Related m M) (hri : Related imports I)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.invoke i o m imports) N (.app M I) := by
  rcases hm.value_shape hrm.values.1 with hmod | hres
  · obtain ⟨cap,c,i₀,o₀,body,rfl⟩ := hmod
    cases hrm with
    | moduleCaptured hcap hb => exact finite_invoke_captured small hΔ hm hi hcap hb hri hν henv
    | moduleSandbox hb => exact finite_invoke_sandbox small hΔ hm hi hb hri hν henv
  · obtain ⟨original,saved,j,k,o₀,rfl⟩ := hres
    cases hrm with
    | resid hM hs => exact finite_invoke_residual small hΔ hm hi hM hs hri hν henv

/-- Native module invocation preserves both bounded-to-actual execution
    directions, including every suspended residual and empty-capture representation. -/
theorem finite_invoke (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (hm : HasType Δ h m (.module i o)) (hi : HasType Δ h imports (.record i))
    (he : Elaborates (.invoke i o m imports) E)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.invoke i o m imports) N E := by
  obtain ⟨M,I,rfl,hmE,hiE⟩ := he.invoke_inv
  apply FiniteCorrespondence.bind_strict
    (fun k hk => small k hk Δ h (.module i o) m M ν N hΔ hm hmE hν henv)
    strict_invoke_module Target.strict_app_left
    (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
  intro v V hv hrel
  have hm' := hv.1.preservation hν hm hΔ
  apply FiniteCorrespondence.bind_strict
    (fun k hk => small k hk Δ h (.record i) imports I ν N hΔ hi hiE hν henv)
    (strict_invoke_imports hrel.values.1) (Target.strict_app_right hrel.values.2)
    (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
  intro w W hw harg
  have hi' := hw.1.preservation hν hi hΔ
  exact finite_invoke_values small hΔ hm' hi' hrel harg hν henv

end LeanSce.Source

/-! ## Source Link Correspondence -/

namespace LeanSce.Source

private theorem certificate_shapes (hc : CertType Δ a b cd) (he : Elaborates cd C) :
    ∃ code CODE, cd = .close code ∧ C = .close CODE := by
  cases hc with
  | closed _ _ =>
    obtain ⟨U,CODE,rfl,hU,_⟩ := he.box_inv
    cases hU.unit_inv
    exact ⟨_,_,rfl,rfl⟩

private theorem result_value_type (ht : HasType Δ h e a) (hΔ : Context.Valid Δ)
    (hν : ValueType Δ ν h) (he : Terminates ν e v) : ValueType Δ v a :=
  valueType_of_typed_value (he.1.preservation hν ht hΔ) he.2

theorem finite_run (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (hm : HasType Δ h m (.module i o)) (hp : HasType Δ h provider (.record p))
    (hc : CertType Δ (.record p) (.record i) cd)
    (helab : Elaborates (.run p i o cd m provider) E)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.run p i o cd m provider) N E := by
  obtain ⟨C,M,P,rfl,hC,hM,hP⟩ := helab.run_inv
  obtain ⟨code,CODE,rfl,rfl⟩ := certificate_shapes hc hC
  constructor
  · intro k hk w hw
    obtain ⟨m₀,p₀,a,b,c,ha,hb,hc',hm₀,hp₀,hrest⟩ := hw.run_head_inv hν.1
    obtain ⟨M₀,hMt,hrM⟩ := (small a (by omega) Δ h (.module i o) m M ν N hΔ hm hM hν henv).1
      a (Nat.le_refl _) m₀ hm₀
    obtain ⟨P₀,hPt,hrP⟩ := (small b (by omega) Δ h (.record p) provider P ν N hΔ hp hP hν henv).1
      b (Nat.le_refl _) p₀ hp₀
    have hmt := hm₀.1.toSteps.preservation hν hm hΔ
    have hpt := hp₀.1.toSteps.preservation hν hp hΔ
    have hrt : HasType Δ h (.invoke i o m₀ (.view (.record p) (.record i) (.close code) p₀)) (.record o) :=
      .invoke hmt (.view hpt hc)
    obtain ⟨W,hWt,hrW⟩ := (small c (by omega) Δ h (.record o)
      (.invoke i o m₀ (.view (.record p) (.record i) (.close code) p₀))
      (.app M₀ (.app (.close CODE) P₀)) ν N hΔ hrt
      (.invoke (.value hrM) (.view hC (.value hrP))) hν henv).1
      c (Nat.le_refl _) w hrest
    obtain ⟨F,I,hF,hI,hcall⟩ := hWt.app_decompose
    cases hF.1.from_value hrM.values.2
    exact ⟨W,Templates.run_forward henv.values.2 hMt hPt
      (hI.certificate_caller henv.values.2 rfl hrP.values.2)
      (hcall.app_caller rfl hrM.values.2 hI.2),hrW⟩
  · intro k hk W hW
    obtain ⟨M₀,P₀,I,a,b,c,d,ha,hb,hc',hd,hMt,hPt,hct,hcall⟩ :=
      Templates.run_counted_inv henv.values.2 hW
    obtain ⟨m₀,hm₀,hrM⟩ := (small a (by omega) Δ h (.module i o) m M ν N hΔ hm hM hν henv).2
      a (Nat.le_refl _) M₀ hMt
    obtain ⟨p₀,hp₀,hrP⟩ := (small b (by omega) Δ h (.record p) provider P ν N hΔ hp hP hν henv).2
      b (Nat.le_refl _) P₀ hPt
    have hmVT := result_value_type hm hΔ hν hm₀
    have hpVT := result_value_type hp hΔ hν hp₀
    have hcode : HasType Δ .unit (.app (.close code) p₀) (.record i) :=
      .app (hc.typed .unit) hpVT.2
    obtain ⟨imports,himports,hrI⟩ := (small c (by omega) Δ .unit (.record i)
      (.app (.close code) p₀) (.app (.close CODE) P₀) .unit .unit hΔ hcode
      (.app hC (.value hrP)) ⟨rfl,.unit .unit⟩ .unit).2 c (Nat.le_refl _) I hct
    have hiVT := result_value_type (ν := .unit) hcode hΔ ⟨rfl,.unit .unit⟩ himports
    have hinvoke : HasType Δ .unit (.invoke i o m₀ imports) (.record o) := .invoke hmVT.2 hiVT.2
    obtain ⟨w,hw,hrw⟩ := (small d (by omega) Δ .unit (.record o)
      (.invoke i o m₀ imports) (.app M₀ I) .unit .unit hΔ hinvoke
      (.invoke (.value hrM) (.value hrI)) ⟨rfl,.unit .unit⟩ .unit).2 d (Nat.le_refl _) W hcall
    have hcν := himports.certificate_caller rfl hν.1 hpVT.1
    have hiν := hw.invoke_caller hmVT hiVT hΔ rfl hν.1
    have hview : Terminates ν (.view (.record p) (.record i) (.close code) p₀) imports :=
      hcν.app_to_view hν.1
    have hresult := (strict_invoke_imports hmVT.1).terminates hview hiν
    exact ⟨w,Terminates.run_head_forward hν.1 hm₀ hp₀ hresult,hrw⟩

theorem finite_provide (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (hp : HasType Δ h provider (.record p)) (hm : HasType Δ h m (.module (.union j k) o))
    (hc : CertType Δ (.record p) (.record j) cd)
    (hj : WellFormed Δ j) (hk : WellFormed Δ k) (hd : Disjoint Δ j k)
    (helab : Elaborates (.provide p j k o cd provider m) E)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.provide p j k o cd provider m) N E := by
  obtain ⟨C,P,M,rfl,hC,hP,hM⟩ := helab.provide_inv
  obtain ⟨code,CODE,rfl,rfl⟩ := certificate_shapes hc hC
  constructor
  · intro budget hb w hw
    obtain ⟨p₀,m₀,a,b,c,ha,hb',hc',hp₀,hm₀,hrest⟩ := hw.provide_head_inv hν.1
    obtain ⟨P₀,hPt,hrP⟩ := (small a (by omega) Δ h (.record p) provider P ν N hΔ hp hP hν henv).1
      a (Nat.le_refl _) p₀ hp₀
    obtain ⟨M₀,hMt,hrM⟩ := (small b (by omega) Δ h (.module (.union j k) o) m M ν N hΔ hm hM hν henv).1
      b (Nat.le_refl _) m₀ hm₀
    have hmVT := result_value_type hm hΔ hν hm₀.toTerminates
    have hpt := hp₀.1.toSteps.preservation hν hp hΔ
    have hrt : HasType Δ h (.resid m₀ (.view (.record p) (.record j) (.close code) p₀) j k o)
        (.module k o) := .resid hmVT.1 hmVT.2 (.view hpt hc) hj hk hd
    obtain ⟨W,hWt,hrW⟩ := (small c (by omega) Δ h (.module k o)
      (.resid m₀ (.view (.record p) (.record j) (.close code) p₀) j k o)
      (.app (.app (Templates.residual j.erase k.erase o.erase) M₀) (.app (.close CODE) P₀))
      ν N hΔ hrt (.resid hrM (by intro hv; cases hv) (.view hC (.value hrP))) hν henv).1
      c (Nat.le_refl _) w hrest
    obtain ⟨q,hq⟩ := hWt.counted
    obtain ⟨I,a',_,hIt,heq⟩ := Templates.residual_counted_inv henv.values.2 hrM.values.2 hq
    cases heq
    exact ⟨_,Templates.provide_forward henv.values.2 hPt hMt
      (hIt.toTerminates.certificate_caller henv.values.2 rfl hrP.values.2),hrW⟩
  · intro budget hb W hW
    obtain ⟨P₀,M₀,I,a,b,c,ha,hb',hc',hPt,hMt,hct,heq⟩ :=
      Templates.provide_counted_inv henv.values.2 hW
    cases heq
    obtain ⟨p₀,hp₀,hrP⟩ := (small a (by omega) Δ h (.record p) provider P ν N hΔ hp hP hν henv).2
      a (Nat.le_refl _) P₀ hPt
    obtain ⟨m₀,hm₀,hrM⟩ := (small b (by omega) Δ h (.module (.union j k) o) m M ν N hΔ hm hM hν henv).2
      b (Nat.le_refl _) M₀ hMt
    have hpVT := result_value_type hp hΔ hν hp₀
    have hcode : HasType Δ .unit (.app (.close code) p₀) (.record j) := .app (hc.typed .unit) hpVT.2
    obtain ⟨imports,himports,hrI⟩ := (small c (by omega) Δ .unit (.record j)
      (.app (.close code) p₀) (.app (.close CODE) P₀) .unit .unit hΔ hcode
      (.app hC (.value hrP)) ⟨rfl,.unit .unit⟩ .unit).2 c (Nat.le_refl _) I hct
    have hview : Terminates ν (.view (.record p) (.record j) (.close code) p₀) imports :=
      (himports.certificate_caller rfl hν.1 hpVT.1).app_to_view hν.1
    have hres : Terminates ν (.resid m₀ (.view (.record p) (.record j) (.close code) p₀) j k o)
        (.resid m₀ imports j k o) :=
      (strict_resid_saved hm₀.2).terminates hview ⟨.refl,Bool.and_eq_true_iff.mpr ⟨hm₀.2,himports.2⟩⟩
    exact ⟨_,Terminates.provide_head_forward hν.1 hp₀ hm₀ hres,.resid hrM hrI⟩

theorem finite_link (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (hp : HasType Δ h provider (.record p)) (hm : HasType Δ h m (.module i o))
    (hc : CertType Δ (.record p) (.record i) cd) (hd : Disjoint Δ p o)
    (helab : Elaborates (.link p i o cd provider m) E)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.link p i o cd provider m) N E := by
  obtain ⟨C,P,M,rfl,hC,hP,hM⟩ := helab.link_inv
  obtain ⟨code,CODE,rfl,rfl⟩ := certificate_shapes hc hC
  constructor
  · intro budget hb w hw
    obtain ⟨p₀,m₀,a,b,c,ha,hb',hc',hp₀,hm₀,hrest⟩ := hw.link_head_inv hν.1
    obtain ⟨P₀,hPt,hrP⟩ := (small a (by omega) Δ h (.record p) provider P ν N hΔ hp hP hν henv).1
      a (Nat.le_refl _) p₀ hp₀
    obtain ⟨M₀,hMt,hrM⟩ := (small b (by omega) Δ h (.module i o) m M ν N hΔ hm hM hν henv).1
      b (Nat.le_refl _) m₀ hm₀
    have hmt := hm₀.1.toSteps.preservation hν hm hΔ
    have hpt := hp₀.1.toSteps.preservation hν hp hΔ
    have hrt : HasType Δ h (.merge p₀ (.run p i o (.close code) m₀ p₀)) (.record (.union p o)) :=
      .merge hpt (.run hmt hpt hc) hd
    obtain ⟨W,hWt,hrW⟩ := (small c (by omega) Δ h (.record (.union p o))
      (.merge p₀ (.run p i o (.close code) m₀ p₀))
      (.merge P₀ (.app (.app (Templates.run p.erase i.erase o.erase (.close CODE)) M₀) P₀))
      ν N hΔ hrt (.merge (.value hrP) (.run hC (.value hrM) (.value hrP))) hν henv).1
      c (Nat.le_refl _) w hrest
    obtain ⟨O,hRun,hMerge⟩ := (Target.strict_merge_right hrP.values.2).decompose hWt
    obtain ⟨q,hq⟩ := hRun.counted
    obtain ⟨M',P',I,a',b',c',d',_,_,_,_,hM',hP',hCode,hCall⟩ :=
      Templates.run_counted_inv henv.values.2 hq
    obtain ⟨_,heqM⟩ := hM'.1.value_inv hrM.values.2
    obtain ⟨_,heqP⟩ := hP'.1.value_inv hrP.values.2
    cases heqM; cases heqP
    exact ⟨W,Templates.link_forward henv.values.2 hPt hMt hCode.toTerminates
      hCall.toTerminates (hMerge.merge_caller rfl hrP.values.2 hRun.2),hrW⟩
  · intro budget hb W hW
    obtain ⟨P₀,M₀,I,O,a,b,c,d,q,ha,hb',hc',hd',hq,hPt,hMt,hct,hcall,hmerge⟩ :=
      Templates.link_counted_inv henv.values.2 hW
    obtain ⟨p₀,hp₀,hrP⟩ := (small a (by omega) Δ h (.record p) provider P ν N hΔ hp hP hν henv).2
      a (Nat.le_refl _) P₀ hPt
    obtain ⟨m₀,hm₀,hrM⟩ := (small b (by omega) Δ h (.module i o) m M ν N hΔ hm hM hν henv).2
      b (Nat.le_refl _) M₀ hMt
    have hmVT := result_value_type hm hΔ hν hm₀
    have hpVT := result_value_type hp hΔ hν hp₀
    have hcode : HasType Δ .unit (.app (.close code) p₀) (.record i) := .app (hc.typed .unit) hpVT.2
    obtain ⟨imports,himports,hrI⟩ := (small c (by omega) Δ .unit (.record i)
      (.app (.close code) p₀) (.app (.close CODE) P₀) .unit .unit hΔ hcode
      (.app hC (.value hrP)) ⟨rfl,.unit .unit⟩ .unit).2 c (Nat.le_refl _) I hct
    have hiVT := result_value_type (ν := .unit) hcode hΔ ⟨rfl,.unit .unit⟩ himports
    have hinvoke : HasType Δ .unit (.invoke i o m₀ imports) (.record o) := .invoke hmVT.2 hiVT.2
    obtain ⟨exports,hout,hrO⟩ := (small d (by omega) Δ .unit (.record o)
      (.invoke i o m₀ imports) (.app M₀ I) .unit .unit hΔ hinvoke
      (.invoke (.value hrM) (.value hrI)) ⟨rfl,.unit .unit⟩ .unit).2 d (Nat.le_refl _) O hcall
    have hoVT := result_value_type (ν := .unit) hinvoke hΔ ⟨rfl,.unit .unit⟩ hout
    have hmerged : HasType Δ .unit (.merge p₀ exports) (.record (.union p o)) := .merge hpVT.2 hoVT.2 hd
    obtain ⟨w,hw,hrw⟩ := (small q (by omega) Δ .unit (.record (.union p o))
      (.merge p₀ exports) (.merge P₀ O) .unit .unit hΔ hmerged
      (.merge (.value hrP) (.value hrO)) ⟨rfl,.unit .unit⟩ .unit).2 q (Nat.le_refl _) W hmerge
    have hview : Terminates ν (.view (.record p) (.record i) (.close code) p₀) imports :=
      (himports.certificate_caller rfl hν.1 hpVT.1).app_to_view hν.1
    have hbody := hout.invoke_caller hmVT hiVT hΔ rfl hν.1
    have hrun : Terminates ν (.run p i o (.close code) m₀ p₀) exports :=
      Terminates.run_head_forward hν.1 ⟨.refl,hmVT.1⟩ ⟨.refl,hpVT.1⟩
        ((strict_invoke_imports hmVT.1).terminates hview hbody)
    have hresult := (strict_merge_right hpVT.1).terminates hrun (hw.merge_caller hν.1 hpVT.1 hoVT.1)
    exact ⟨w,Terminates.link_head_forward hν.1 hp₀ hm₀ hresult,hrw⟩

end LeanSce.Source

/-! ## Source Simple Correspondence -/

namespace LeanSce.Source
set_option linter.unusedVariables false

theorem strict_letVal : StrictFrame ν (fun e => .letVal a e body) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he : e.isValue = false := by
      cases hh : e.isValue <;> first | rfl | exact False.elim (hn hh)
    simp [step_letVal_eq,he]

theorem TerminatesIn.letVal_inv (hν : Value ν)
    (ht : TerminatesIn ν (.letVal a e body) k w) :
    ∃ v i j, k = i+j+2 ∧ TerminatesIn ν e i v ∧
      TerminatesIn (.pair ν v) body j w := by
  obtain ⟨v,i,p,hip,hv,hrest⟩ := strict_letVal.decompose_counted ht
  obtain ⟨q,hq,hbox⟩ := hrest.after_step (e' := .box (.pair ν v) body) ⟨hν,by
    simp only [step_letVal_eq,(show v.isValue = true from hv.2),Bool.not_true,
      Bool.false_eq_true,↓reduceIte]⟩
  obtain ⟨j,hj,hbody⟩ := hbox.box_inv hν
    (show Value (.pair ν v) from Bool.and_eq_true_iff.mpr ⟨hν,hv.2⟩)
  exact ⟨v,i,j,by omega,hv,hbody⟩

theorem Terminates.letVal (hν : Value ν) (he : Terminates ν e v)
    (hb : Terminates (.pair ν v) body w) : Terminates ν (.letVal a e body) w :=
  strict_letVal.terminates he ⟨.next ⟨hν,by
    simp only [step_letVal_eq,(show v.isValue = true from he.2),Bool.not_true,
      Bool.false_eq_true,↓reduceIte]⟩ (hb.box hν (Bool.and_eq_true_iff.mpr ⟨hν,he.2⟩)).1,hb.2⟩

theorem finite_letVal (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (wa : WellFormed Δ a) (he : HasType Δ h e a)
    (hb : HasType Δ (.prod h a) body b)
    (helab : Elaborates (.letVal a e body) E)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.letVal a e body) N E := by
  obtain ⟨A,B,rfl,hA,hB⟩ := helab.letVal_inv
  constructor
  · intro k hk w hw
    obtain ⟨v,i,j,hij,hv,hbody⟩ := hw.letVal_inv hν.1
    obtain ⟨V,hV,hr⟩ := (small i (by omega) Δ h a e A ν N hΔ he hA hν henv).1
      i (Nat.le_refl _) v hv
    have hvt := valueType_of_typed_value (hv.1.toSteps.preservation hν he hΔ) hv.2
    have hpair : ValueType Δ (.pair ν v) (.prod h a) :=
      ⟨Bool.and_eq_true_iff.mpr ⟨hν.1,hv.2⟩,.pair hν.2 hvt.2⟩
    obtain ⟨W,hW,hrW⟩ := (small j (by omega) Δ (.prod h a) b body B
      (.pair ν v) (.pair N V) hΔ hb hB hpair (.pair henv hr)).1 j (Nat.le_refl _) w hbody
    exact ⟨W,Target.Terminates.letIn henv.values.2 hV hW,hrW⟩
  · intro k hk W hW
    obtain ⟨V,i,j,hij,hV,hbody⟩ := hW.letIn_inv henv.values.2
    obtain ⟨v,hv,hr⟩ := (small i (by omega) Δ h a e A ν N hΔ he hA hν henv).2
      i (Nat.le_refl _) V hV
    have hvt := valueType_of_typed_value (hv.1.preservation hν he hΔ) hv.2
    have hpair : ValueType Δ (.pair ν v) (.prod h a) :=
      ⟨Bool.and_eq_true_iff.mpr ⟨hν.1,hv.2⟩,.pair hν.2 hvt.2⟩
    obtain ⟨w,hw,hrw⟩ := (small j (by omega) Δ (.prod h a) b body B
      (.pair ν v) (.pair N V) hΔ hb hB hpair (.pair henv hr)).2 j (Nat.le_refl _) W hbody
    exact ⟨w,Terminates.letVal hν.1 hv hw,hrw⟩

theorem finite_module (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (wh : WellFormed Δ h) (wi : WellFormed Δ i) (wo : WellFormed Δ o)
    (hb : HasType Δ (.record i) body (.record o))
    (helab : Elaborates (.module i o body) E)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.module i o body) N E := by
  obtain ⟨B,rfl,hB⟩ := helab.module_inv
  exact .creation ⟨.single ⟨hν.1,rfl⟩,rfl⟩
    (Target.close_lam_counted henv.values.2).toTerminates (.moduleSandbox hB)

theorem finite_capture (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (hc : HasType Δ h cap (.record c)) (wi : WellFormed Δ i) (wo : WellFormed Δ o)
    (hd : Disjoint Δ c i) (hb : HasType Δ (.record (.union c i)) body (.record o))
    (helab : Elaborates (.capture c i o cap body) E)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.capture c i o cap body) N E := by
  obtain ⟨C,B,rfl,hC,hB⟩ := helab.capture_inv
  constructor
  · intro k hk w hw
    obtain ⟨v,a,b,hab,hv,hrest⟩ := strict_capture.decompose_counted hw
    obtain ⟨q,hq,hvalue⟩ := hrest.after_step
      (e' := .moduleVal v c i o body) ⟨hν.1,by
        simp only [step_capture_eq,(show v.isValue = true from hv.2),Bool.not_true,
          Bool.false_eq_true,↓reduceIte]⟩
    have htyped := hv.1.toSteps.preservation hν hc hΔ
    obtain ⟨fs,rfl⟩ := htyped.value_shape hv.2
    obtain ⟨rfl,rfl⟩ := hvalue.1.value_inv hv.2
    obtain ⟨V,hV,hr⟩ := (small a (by omega) Δ h (.record c) cap C ν N hΔ hc hC hν henv).1
      a (Nat.le_refl _) (.record fs) hv
    have hcap : Target.Value (.pair .unit V) := Bool.and_eq_true_iff.mpr ⟨rfl,hV.2⟩
    have ht : Target.Terminates N (.app (Templates.captured c.erase i.erase B) C)
        (.clo (.pair .unit V) (.record i.erase) (.box (.merge (.ix 1) (.ix 0)) B)) :=
      Target.Terminates.close_lam_app_forward henv.values.2 hV
        ⟨.single ⟨hcap,rfl⟩,hcap⟩
    exact ⟨_,ht,.moduleCaptured hr hB⟩
  · intro k hk W hW
    obtain ⟨V,a,b,hab,hV,hclosure⟩ := hW.close_lam_app_inv henv.values.2
    have hcap : Target.Value (.pair .unit V) := Bool.and_eq_true_iff.mpr ⟨rfl,hV.2⟩
    obtain ⟨_,rfl⟩ := hclosure.lam_inv hcap
    obtain ⟨v,hv,hr⟩ := (small a (by omega) Δ h (.record c) cap C ν N hΔ hc hC hν henv).2
      a (Nat.le_refl _) V hV
    obtain ⟨fs,rfl⟩ := (hv.1.preservation hν hc hΔ).value_shape hv.2
    have hresult : Value (.moduleVal (.record fs) c i o body) := hv.2
    exact ⟨_,strict_capture.terminates hv ⟨.single ⟨hν.1,by
      simp only [step_capture_eq,(show (Term.record fs).isValue = true from hv.2),
        Bool.not_true,Bool.false_eq_true,↓reduceIte]⟩,hresult⟩,.moduleCaptured hr hB⟩

theorem strict_complete : StrictFrame ν (.complete o) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he : e.isValue = false := by
      cases hh : e.isValue <;> first | rfl | exact False.elim (hn hh)
    simp [step_complete_eq,he]

theorem TerminatesIn.complete_to_run (hν : Value ν)
    (ht : TerminatesIn ν (.complete o m) k w) :
    ∃ j, k = j+1 ∧ TerminatesIn ν
      (.run .empty .empty o (identityAdapter (.record .empty)) m (.record .nil)) j w := by
  obtain ⟨v,i,p,hip,hv,hrest⟩ := strict_complete.decompose_counted ht
  obtain ⟨q,hq,hcall⟩ := hrest.after_step
    (e' := .run .empty .empty o (identityAdapter (.record .empty)) v (.record .nil)) ⟨hν,by
      simp only [step_complete_eq,(show v.isValue = true from hv.2),Bool.not_true,
        Bool.false_eq_true,↓reduceIte]
      rfl⟩
  exact ⟨i+q,by omega,((strict_run_module (ν := ν)).lift_counted hv.1).trans hcall.1,hcall.2⟩

theorem Terminates.run_to_complete (hν : Value ν)
    (ht : Terminates ν
      (.run .empty .empty o (identityAdapter (.record .empty)) m (.record .nil)) w) :
    Terminates ν (.complete o m) w := by
  obtain ⟨v,hv,hrest⟩ := strict_run_module.decompose ht
  exact strict_complete.terminates hv ⟨.next ⟨hν,by
    simp only [step_complete_eq,(show v.isValue = true from hv.2),Bool.not_true,
      Bool.false_eq_true,↓reduceIte]
    rfl⟩ hrest.1,hrest.2⟩

theorem finite_complete_of_run (hν : Value ν)
    (hrun : FiniteCorrespondence n ν
      (.run .empty .empty o (identityAdapter (.record .empty)) m (.record .nil)) N E) :
    FiniteCorrespondence n ν (.complete o m) N E := by
  constructor
  · intro k hk w hw
    obtain ⟨j,hj,hcall⟩ := hw.complete_to_run hν
    exact hrun.1 j (by omega) w hcall
  · intro k hk W hW
    obtain ⟨w,hw,hr⟩ := hrun.2 k hk W hW
    exact ⟨w,hw.run_to_complete hν,hr⟩

theorem finite_complete (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (hm : HasType Δ h m (.module .empty o)) (helab : Elaborates (.complete o m) E)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.complete o m) N E := by
  obtain ⟨M,rfl,hM⟩ := helab.complete_inv
  apply finite_complete_of_run hν.1
  exact finite_run small hΔ hm (.record (.nil hm.ambient_wf)) (empty_identity_cert Δ)
    (.run .canonical hM .canonical) hν henv

end LeanSce.Source

/-! ## Source Head Correspondence -/

namespace LeanSce.Source

/-- Every source-only head preserves actual execution in both directions.
    All continuations use strictly smaller own-side reduction budgets. -/
theorem source_heads (small : SmallCorrespondence n) : SourceHeadCorrespondence n := by
  intro Δ h a e hΔ ht hh
  revert hΔ hh
  apply HasType.rec
    (motive_1 := fun Δ h e _ _ => Context.Valid Δ → e.sourceHead = true → ElaborationComputes n Δ h e)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (t := ht)
  all_goals intros
  all_goals intros
  all_goals try simp only [Term.sourceHead,Bool.false_eq_true] at *
  case value =>
    rename_i hv ht hh ih hΔ hhead
    exact False.elim (Term.sourceHead_not_value hhead hv)
  case conv =>
    rename_i ht he hw ih hΔ hhead
    exact ih hΔ hhead
  all_goals unfold ElaborationComputes
  all_goals intros
  case letVal => apply finite_letVal small <;> assumption
  case view => apply finite_view small <;> assumption
  case module => apply finite_module small <;> assumption
  case capture => apply finite_capture small <;> assumption
  case run => apply finite_run small <;> assumption
  case link => apply finite_link small <;> assumption
  case provide => apply finite_provide small <;> assumption
  case complete => apply finite_complete small <;> assumption
  case invoke => apply finite_invoke small <;> assumption

end LeanSce.Source

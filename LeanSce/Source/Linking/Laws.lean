import LeanSce.Source.Definitions.Typing
import LeanSce.Source.Metatheory.Adapters
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.Evaluation
import LeanSce.Source.Metatheory.Substitution

/-!
# Source / Linking / Laws

Proofs and supporting constructions for laws.
-/

/-! ## Confinement -/

namespace LeanSce.Source

/-- S4.1: module entry is independent of its caller ambient, for exact returned
    values and for actual infinite executions. -/
theorem module_confinement
    (hm : ValueType .empty m (.module i o)) (hi : ValueType .empty imports (.record i))
    (hν : ValueType .empty ν h) (hN : ValueType .empty N H) :
    (∀ w, Terminates ν (.invoke i o m imports) w ↔ Terminates N (.invoke i o m imports) w) ∧
    (Diverges ν (.invoke i o m imports) ↔ Diverges N (.invoke i o m imports)) := by
  obtain ⟨env,body,r,he,henv,hbody⟩ := module_entry_exists hm hi .empty
  have htν : HasType .empty h (.invoke i o m imports) (.record o) :=
    .invoke (hm.inclusion (hν.2.result_wf .empty)) (hi.inclusion (hν.2.result_wf .empty))
  have htN : HasType .empty H (.invoke i o m imports) (.record o) :=
    .invoke (hm.inclusion (hN.2.result_wf .empty)) (hi.inclusion (hN.2.result_wf .empty))
  have ht : ∀ w, Terminates ν (.invoke i o m imports) w ↔
      Terminates N (.invoke i o m imports) w :=
    fun w => (he.terminates_iff hν.1).trans (he.terminates_iff hN.1).symm
  refine ⟨ht,?_⟩
  rw [diverges_iff_not_terminates htν .empty hν,
    diverges_iff_not_terminates htN .empty hN]
  exact not_congr (exists_congr ht)

/-- A retained adapter is evaluated to its exact import value before entry. -/
theorem run_values_steps (hν : Value ν) (hm : Value m) (hp : Value provider)
    (hi : Terminates ν (.view (.record p) (.record i) cd provider) imports) :
    Steps ν (.run p i o cd m provider) (.invoke i o m imports) :=
  .next ⟨hν,by simp [step_run_eq,(show m.isValue = true from hm),
    (show provider.isValue = true from hp)]⟩
    ((strict_invoke_imports hm).lift_steps hi.1)

theorem run_values_terminates_iff (hν : Value ν) (hm : Value m) (hp : Value provider)
    (hi : Terminates ν (.view (.record p) (.record i) cd provider) imports) :
    Terminates ν (.run p i o cd m provider) w ↔ Terminates ν (.invoke i o m imports) w := by
  have hs := run_values_steps (o := o) hν hm hp hi
  exact ⟨fun ht => ht.after_steps hs,fun ht => ht.prepend hs⟩

/-- Unused provider fields and distinct caller environments cannot change
    execution once the retained certificates yield the same exact imports. -/
theorem provider_confinement
    (hm : ValueType .empty m (.module i o)) (hi : ValueType .empty imports (.record i))
    (hν : ValueType .empty ν h) (hN : ValueType .empty N H)
    (hp : ValueType .empty provider (.record p)) (hP : ValueType .empty Provider (.record P))
    (hc : CertType .empty (.record p) (.record i) cd)
    (hC : CertType .empty (.record P) (.record i) Cd)
    (hv : Terminates ν (.view (.record p) (.record i) cd provider) imports)
    (hV : Terminates N (.view (.record P) (.record i) Cd Provider) imports) :
    (∀ w, Terminates ν (.run p i o cd m provider) w ↔
      Terminates N (.run P i o Cd m Provider) w) ∧
    (Diverges ν (.run p i o cd m provider) ↔ Diverges N (.run P i o Cd m Provider)) := by
  have hmν := hm.inclusion (hν.2.result_wf .empty)
  have hmN := hm.inclusion (hN.2.result_wf .empty)
  have htν := HasType.run hmν (hp.inclusion (hν.2.result_wf .empty)) hc
  have htN := HasType.run hmN (hP.inclusion (hN.2.result_wf .empty)) hC
  have hiν := fun w => run_values_terminates_iff (o := o) (w := w) hν.1 hm.1 hp.1 hv
  have hiN := fun w => run_values_terminates_iff (o := o) (w := w) hN.1 hm.1 hP.1 hV
  have hconf := (module_confinement hm hi hν hN).1
  have ht : ∀ w, Terminates ν (.run p i o cd m provider) w ↔
      Terminates N (.run P i o Cd m Provider) w :=
    fun w => (hiν w).trans ((hconf w).trans (hiN w).symm)
  refine ⟨ht,?_⟩
  rw [diverges_iff_not_terminates htν .empty hν,
    diverges_iff_not_terminates htN .empty hN]
  exact not_congr (exists_congr ht)

end LeanSce.Source

/-! ## Link Typing Inversion -/

namespace LeanSce.Source

theorem HasType.link_operands (ht : HasType Δ h e a) :
    ∀ p i o cd provider m, e = .link p i o cd provider m →
      HasType Δ h provider (.record p) ∧ HasType Δ h m (.module i o) ∧
      CertType Δ (.record p) (.record i) cd ∧ Disjoint Δ p o := by
  apply HasType.rec
    (motive_1 := fun Δ h e _ _ => ∀ p i o cd provider m, e = .link p i o cd provider m →
      HasType Δ h provider (.record p) ∧ HasType Δ h m (.module i o) ∧
      CertType Δ (.record p) (.record i) cd ∧ Disjoint Δ p o)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (t := ht)
  all_goals intros
  all_goals try trivial
  all_goals intros
  all_goals rename_i he
  all_goals cases he
  case link => exact ⟨by assumption,by assumption,by assumption,by assumption⟩
  case value => simp_all [Value,Term.isValue]

end LeanSce.Source

/-! ## Export Retention -/

namespace LeanSce.Source

/-- A terminating disjoint extension retains the exact left map and adds
    exactly the right map; no field initializer is repeated. -/
theorem merge_export_retention
    (hp : HasType .empty h p (.record r)) (hq : HasType .empty h q (.record s))
    (hd : Disjoint .empty r s) (hν : ValueType .empty ν h)
    (ht : Terminates ν (.merge p q) w) :
    ∃ fs gs, Terminates ν p (.record fs) ∧ Terminates ν q (.record gs) ∧
      ValueType .empty (.record fs) (.record r) ∧ ValueType .empty (.record gs) (.record s) ∧
      w = .record (fs.append gs) ∧
      (fs.append gs).labels.Perm (r.knownLabels ++ s.knownLabels) ∧
      (fs.append gs).labels.Nodup ∧
      (fs.append gs).filter fs.labels.contains = fs := by
  obtain ⟨P,Q,hP,hQ,hr⟩ := ht.merge_decompose
  have hpt := valueType_of_typed_value (hP.1.preservation hν hp .empty) hP.2
  have hqt := valueType_of_typed_value (hQ.1.preservation hν hq .empty) hQ.2
  obtain ⟨fs,rfl⟩ := hpt.2.value_shape hpt.1
  obtain ⟨gs,rfl⟩ := hqt.2.value_shape hqt.1
  have hf := hpt.2.value_record_inv hpt.1 (hp.result_wf .empty).record_row
  have hg := hqt.2.value_record_inv hqt.1 (hq.result_wf .empty).record_row
  refine ⟨fs,gs,hP,hQ,hpt,hqt,?_,?_,(hf.append .empty hg hd).labels_nodup,?_⟩
  · exact (Terminates.merge_records hν.1 hpt.1 hqt.1 (hf.merge_check hg hd)).mp hr
  · rw [Term.labels_append]
    exact hf.labels_perm.append hg.labels_perm
  · exact Term.append_restrict_left fs gs (fun l hl hL =>
      hd.knownLabels l (hf.labels_mem.mp hL) (hg.labels_mem.mp hl))

/-- The operational core of S4.2, already at a closed instance. -/
theorem link_export_retention_closed
    (hp : HasType .empty h provider (.record p))
    (hm : HasType .empty h m (.module i o))
    (hc : CertType .empty (.record p) (.record i) cd)
    (hd : Disjoint .empty p o) (hν : ValueType .empty ν h)
    (ht : Terminates ν (.link p i o cd provider m) w) :
    ∃ m₀ fs gs, Terminates ν provider (.record fs) ∧ Terminates ν m m₀ ∧
      ValueType .empty m₀ (.module i o) ∧
      Terminates ν (.run p i o cd m₀ (.record fs)) (.record gs) ∧
      ValueType .empty (.record fs) (.record p) ∧ ValueType .empty (.record gs) (.record o) ∧
      w = .record (fs.append gs) ∧
      (fs.append gs).labels.Perm (p.knownLabels ++ o.knownLabels) ∧
      (fs.append gs).labels.Nodup ∧
      (fs.append gs).filter fs.labels.contains = fs := by
  obtain ⟨P,M,hP,hM,hr⟩ := ht.link_decompose hν.1
  have hpt := valueType_of_typed_value (hP.1.preservation hν hp .empty) hP.2
  have hmt := valueType_of_typed_value (hM.1.preservation hν hm .empty) hM.2
  obtain ⟨O,hO,hmerge⟩ := (strict_merge_right hP.2).decompose hr
  have hrun := HasType.run (hmt.inclusion hm.ambient_wf) (hpt.inclusion hp.ambient_wf) hc
  have hot := valueType_of_typed_value (hO.1.preservation hν hrun .empty) hO.2
  obtain ⟨fs,rfl⟩ := hpt.2.value_shape hpt.1
  obtain ⟨gs,rfl⟩ := hot.2.value_shape hot.1
  have hf := hpt.2.value_record_inv hpt.1 (hp.result_wf .empty).record_row
  have hg := hot.2.value_record_inv hot.1 (hrun.result_wf .empty).record_row
  refine ⟨M,fs,gs,hP,hM,hmt,hO,hpt,hot,?_,?_,(hf.append .empty hg hd).labels_nodup,?_⟩
  · exact (Terminates.merge_records hν.1 hpt.1 hot.1 (hf.merge_check hg hd)).mp hmerge
  · rw [Term.labels_append]
    exact hf.labels_perm.append hg.labels_perm
  · exact Term.append_restrict_left fs gs (fun l hl hL =>
      hd.knownLabels l (hf.labels_mem.mp hL) (hg.labels_mem.mp hl))

/-- S4.2: exact export retention under every satisfying closing substitution. -/
theorem link_export_retention
    (hΔ : Context.Valid Δ)
    (htype : HasType Δ h (.link p i o cd provider m) (.record (.union p o)))
    (hθ : Closing θ Δ) (hν : ValueType .empty ν (h.subst θ))
    (ht : Terminates ν ((.link p i o cd provider m : Expr).subst θ) w) :
    ∃ m₀ fs gs, Terminates ν (provider.subst θ) (.record fs) ∧ Terminates ν (m.subst θ) m₀ ∧
      ValueType .empty m₀ (.module (i.subst θ) (o.subst θ)) ∧
      Terminates ν (.run (p.subst θ) (i.subst θ) (o.subst θ) (cd.subst θ) m₀ (.record fs)) (.record gs) ∧
      ValueType .empty (.record fs) (.record (p.subst θ)) ∧
      ValueType .empty (.record gs) (.record (o.subst θ)) ∧
      w = .record (fs.append gs) ∧
      (fs.append gs).labels.Perm ((p.subst θ).knownLabels ++ (o.subst θ).knownLabels) ∧
      (fs.append gs).labels.Nodup ∧
      (fs.append gs).filter fs.labels.contains = fs := by
  obtain ⟨hp,hm,hc,hd⟩ := htype.link_operands p i o cd provider m rfl
  exact link_export_retention_closed (hp.subst hΔ hθ.respects) (hm.subst hΔ hθ.respects)
    (hc.subst hΔ hθ.respects) (hd.subst hθ.respects) hν (by simpa [Term.subst] using ht)

end LeanSce.Source

/-! ## Identity Evaluation -/

namespace LeanSce.Source

theorem identity_view_terminates (hν : Value ν) (hv : Value v) :
    Terminates ν (.view a a (identityAdapter a) v) v := by
  apply evaluate_sound hν (fuel := 12)
  simp [evaluate,step,identityAdapter,Term.close,Term.ix,Term.isValue,
    (show v.isValue = true from hv)]

theorem identity_run_terminates_iff (hν : Value ν) (hm : Value m) (hv : Value v) :
    Terminates ν (.run i i o (identityAdapter (.record i)) m v) w ↔
      Terminates ν (.invoke i o m v) w :=
  run_values_terminates_iff hν hm hv (identity_view_terminates hν hv)

theorem identity_provide_steps (hν : Value ν) (hm : Value m) (hv : Value v) :
    Steps ν (.provide j j k o (identityAdapter (.record j)) v m) (.resid m v j k o) := by
  apply Steps.next (e' := .resid m (.view (.record j) (.record j) (identityAdapter (.record j)) v) j k o)
  · exact ⟨hν,by simp [step_provide_eq,(show m.isValue = true from hm),(show v.isValue = true from hv)]⟩
  · exact (strict_resid_saved hm).lift_steps (identity_view_terminates hν hv).1

theorem identity_provide_terminates (hν : Value ν) (hm : Value m) (hv : Value v) :
    Terminates ν (.provide j j k o (identityAdapter (.record j)) v m) (.resid m v j k o) :=
  ⟨identity_provide_steps hν hm hv,Bool.and_eq_true_iff.mpr ⟨hm,hv⟩⟩

end LeanSce.Source

/-! ## Staged Evaluation -/

namespace LeanSce.Source

def stagedRun (j k o : Row) (m x y : Expr) : Expr :=
  .run k k o (identityAdapter (.record k))
    (.provide j j k o (identityAdapter (.record j)) x m) y

def directRun (i o : Row) (m imports : Expr) : Expr :=
  .run i i o (identityAdapter (.record i)) m imports

theorem identity_run_steps (hν : Value ν) (hm : Value m) (hv : Value v) :
    Steps ν (directRun i o m v) (.invoke i o m v) :=
  run_values_steps hν hm hv (identity_view_terminates hν hv)

/-- Staging has only finite administrative work before the identical service
    invocation on the exact union of the evaluated imports. -/
theorem staged_run_prefix (hν : Value ν) (hm : Value m) (hx : Value fs) (hy : Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true) :
    Steps ν (stagedRun j k o m (.record fs) (.record gs))
      (.invoke (.union j k) o m (.record (fs.append gs))) := by
  have hres : Value (.resid m (.record fs) j k o) := Bool.and_eq_true_iff.mpr ⟨hm,hx⟩
  apply Steps.trans (strict_run_module.lift_steps (identity_provide_steps hν hm hx))
  apply Steps.trans (identity_run_steps hν hres hy)
  apply Steps.next (e' := .invoke (.union j k) o m (.merge (.record fs) (.record gs)))
  · exact ⟨hν,by simp [step_invoke_eq,Term.isValue,(show m.isValue = true from hm),
      (show fs.isValue = true from hx),(show gs.isValue = true from hy)]⟩
  · exact (strict_invoke_imports hm).lift_steps (.single (merge_records_step hν hx hy hd))

theorem direct_merge_run_prefix (hν : Value ν) (hm : Value m) (hx : Value fs) (hy : Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true) :
    Steps ν (directRun (.union j k) o m (.merge (.record fs) (.record gs)))
      (.invoke (.union j k) o m (.record (fs.append gs))) := by
  exact ((strict_run_provider hm).lift_steps
    (.single (merge_records_step hν hx hy hd))).trans
      (identity_run_steps hν hm (Term.append_value fs hx hy))

/-- The complete operational staging law: exact values and actual divergence. -/
theorem staged_run_behaviour (hν : Value ν) (hm : Value m) (hx : Value fs) (hy : Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true) :
    (∀ w, Terminates ν (stagedRun j k o m (.record fs) (.record gs)) w ↔
      Terminates ν (directRun (.union j k) o m (.merge (.record fs) (.record gs))) w) ∧
    (Diverges ν (stagedRun j k o m (.record fs) (.record gs)) ↔
      Diverges ν (directRun (.union j k) o m (.merge (.record fs) (.record gs)))) := by
  have hleft := staged_run_prefix (j := j) (k := k) (o := o) hν hm hx hy hd
  have hright := direct_merge_run_prefix (j := j) (k := k) (o := o) hν hm hx hy hd
  refine ⟨fun w => ⟨fun ht => (ht.after_steps hleft).prepend hright,
    fun ht => (ht.after_steps hright).prepend hleft⟩,hleft.diverges_iff.trans hright.diverges_iff.symm⟩

def twiceStagedRun (j k l o : Row) (m x y z : Expr) : Expr :=
  stagedRun k l o (.provide j j (.union k l) o (identityAdapter (.record j)) x m) y z

theorem twice_staged_run_prefix (hν : Value ν) (hm : Value m)
    (hx : Value fs) (hy : Value gs) (hz : Value hs)
    (hkl : gs.labels.all (fun l => !hs.labels.contains l) = true)
    (hjkl : fs.labels.all (fun l => !(gs.append hs).labels.contains l) = true) :
    Steps ν (twiceStagedRun j k l o m (.record fs) (.record gs) (.record hs))
      (.invoke (.union j (.union k l)) o m (.record (fs.append (gs.append hs)))) := by
  have hres : Value (.resid m (.record fs) j (.union k l) o) :=
    Bool.and_eq_true_iff.mpr ⟨hm,hx⟩
  apply Steps.trans (strict_run_module.lift_steps
    ((strict_provide_module hy).lift_steps (identity_provide_steps hν hm hx)))
  apply Steps.trans (staged_run_prefix hν hres hy hz hkl)
  apply Steps.next (e' := .invoke (.union j (.union k l)) o m
    (.merge (.record fs) (.record (gs.append hs))))
  · exact ⟨hν,by simp [step_invoke_eq,Term.isValue,(show m.isValue = true from hm),
      (show fs.isValue = true from hx),(show (gs.append hs).isValue = true from Term.append_value gs hy hz)]⟩
  · exact (strict_invoke_imports hm).lift_steps
      (.single (merge_records_step hν hx (Term.append_value gs hy hz) hjkl))

theorem direct_triple_run_prefix (hν : Value ν) (hm : Value m)
    (hx : Value fs) (hy : Value gs) (hz : Value hs)
    (hkl : gs.labels.all (fun l => !hs.labels.contains l) = true)
    (hjkl : fs.labels.all (fun l => !(gs.append hs).labels.contains l) = true) :
    Steps ν (directRun (.union j (.union k l)) o m
      (.merge (.record fs) (.merge (.record gs) (.record hs))))
      (.invoke (.union j (.union k l)) o m (.record (fs.append (gs.append hs)))) := by
  apply Steps.trans ((strict_run_provider hm).lift_steps
    ((strict_merge_right hx).lift_steps (.single (merge_records_step hν hy hz hkl))))
  exact direct_merge_run_prefix hν hm hx (Term.append_value gs hy hz) hjkl

/-- Nested provisions and direct execution enter exactly the same body. -/
theorem twice_staged_run_behaviour (hν : Value ν) (hm : Value m)
    (hx : Value fs) (hy : Value gs) (hz : Value hs)
    (hkl : gs.labels.all (fun l => !hs.labels.contains l) = true)
    (hjkl : fs.labels.all (fun l => !(gs.append hs).labels.contains l) = true) :
    (∀ w, Terminates ν (twiceStagedRun j k l o m (.record fs) (.record gs) (.record hs)) w ↔
      Terminates ν (directRun (.union j (.union k l)) o m
        (.merge (.record fs) (.merge (.record gs) (.record hs)))) w) ∧
    (Diverges ν (twiceStagedRun j k l o m (.record fs) (.record gs) (.record hs)) ↔
      Diverges ν (directRun (.union j (.union k l)) o m
        (.merge (.record fs) (.merge (.record gs) (.record hs))))) := by
  have hleft := twice_staged_run_prefix (j := j) (k := k) (l := l) (o := o) hν hm hx hy hz hkl hjkl
  have hright := direct_triple_run_prefix (j := j) (k := k) (l := l) (o := o) hν hm hx hy hz hkl hjkl
  exact ⟨fun w => ⟨fun ht => (ht.after_steps hleft).prepend hright,
    fun ht => (ht.after_steps hright).prepend hleft⟩,hleft.diverges_iff.trans hright.diverges_iff.symm⟩

end LeanSce.Source

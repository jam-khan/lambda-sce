import LeanSce.Source.Definitions.Elaboration
import LeanSce.Source.Metatheory.Basic
import LeanSce.Target.LogicalRelation.Data
import LeanSce.Target.LogicalRelation.Evaluation
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Semantics.Templates

/-!
# Source / Elaboration / Templates

Proofs and supporting constructions for templates.
-/

/-! ## Module Template Evaluation -/

namespace LeanSce.Source.Templates
open LeanSce.Target

/-- Inverting Run exposes both original-caller operands, the frozen certificate,
    and the saved module call. Every extracted trace is strictly smaller. -/
theorem run_counted_inv (hν : Target.Value ν)
    (ht : Target.TerminatesIn ν (.app (.app (run p i o (.close code)) e) provider) n w) :
    ∃ m P imports a b c d,
      a < n ∧ b < n ∧ c < n ∧ d < n ∧
      Target.TerminatesIn ν e a m ∧ Target.TerminatesIn ν provider b P ∧
      Target.TerminatesIn .unit (.app (.close code) P) c imports ∧
      Target.TerminatesIn .unit (.app m imports) d w := by
  obtain ⟨m,P,a,b,k,hn,hm,hP,hbody⟩ := ht.curried_template_inv hν
  have henv : Target.Value (.pair (.pair .unit m) P) :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl,hm.2⟩,hP.2⟩
  obtain ⟨k',hk',hbody'⟩ := hbody.projected_function (projection1 rfl hm.2 hP.2)
  obtain ⟨imports,c,d,hkd,himports,hcall⟩ := (strict_app_right hm.2).decompose_counted hbody'
  obtain ⟨c',hc',hcode⟩ := himports.projected_argument
    (projection0 (Bool.and_eq_true_iff.mpr ⟨rfl,hm.2⟩) hP.2)
  exact ⟨m,P,imports,a,b,c',d,by omega,by omega,by omega,by omega,hm,hP,
    hcode.certificate_caller henv rfl hP.2,hcall.app_caller rfl hm.2 himports.2⟩

theorem run_forward (hν : Target.Value ν)
    (hm : Target.Terminates ν e m) (hP : Target.Terminates ν provider P)
    (hc : Target.Terminates .unit (.app (.close code) P) imports)
    (hb : Target.Terminates .unit (.app m imports) w) :
    Target.Terminates ν (.app (.app (run p i o (.close code)) e) provider) w := by
  have henv : Target.Value (.pair (.pair .unit m) P) :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl,hm.2⟩,hP.2⟩
  have harg := (projection0 (cap := .pair .unit m)
    (Bool.and_eq_true_iff.mpr ⟨rfl,hm.2⟩) hP.2).app_argument
    (hc.certificate_caller rfl henv hP.2)
  have hbody := (harg.app_argument (hb.app_caller henv hm.2 hc.2)).projected_function
    (projection1 (cap := .unit) rfl hm.2 hP.2)
  exact Target.Terminates.curried_template_forward hν hm hP hbody

private theorem provide_capture (hP : Target.Value P) (hm : Target.Value m)
    (hI : Target.Value imports) :
    Target.Terminates (.pair (.pair (.pair .unit P) m) imports)
      (.box (.pair (.ix 1) (.ix 0)) (.lam (.record k) residualBody))
      (.clo (.pair m imports) (.record k) residualBody) := by
  apply Target.evaluate_sound (fuel := 16)
    (ν := .pair (.pair (.pair .unit P) m) imports)
    (Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨rfl,hP⟩,hm⟩,hI⟩)
  simp [Target.evaluate,Target.step,Target.Term.ix,Target.Term.isValue,
    (show P.isValue = true from hP),(show m.isValue = true from hm),
    (show imports.isValue = true from hI)]

theorem provide_counted_inv (hν : Target.Value ν)
    (ht : Target.TerminatesIn ν
      (.app (.app (provide p j k o (.close code)) provider) e) n w) :
    ∃ P m imports a b c,
      a < n ∧ b < n ∧ c < n ∧
      Target.TerminatesIn ν provider a P ∧ Target.TerminatesIn ν e b m ∧
      Target.TerminatesIn .unit (.app (.close code) P) c imports ∧
      w = .clo (.pair m imports) (.record k) residualBody := by
  obtain ⟨P,m,a,b,q,hn,hP,hm,hbody⟩ := ht.curried_template_inv hν
  have henv : Target.Value (.pair (.pair .unit P) m) :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl,hP.2⟩,hm.2⟩
  obtain ⟨imports,c,d,hq,hcode,hcapture⟩ := hbody.letIn_inv henv
  obtain ⟨c',hc',hcall⟩ := hcode.projected_argument (projection1 rfl hP.2 hm.2)
  have heq := hcapture.toTerminates.unique (provide_capture hP.2 hm.2 hcode.2)
  exact ⟨P,m,imports,a,b,c',by omega,by omega,by omega,hP,hm,
    hcall.certificate_caller henv rfl hP.2,heq⟩

theorem provide_forward (hν : Target.Value ν)
    (hP : Target.Terminates ν provider P) (hm : Target.Terminates ν e m)
    (hc : Target.Terminates .unit (.app (.close code) P) imports) :
    Target.Terminates ν (.app (.app (provide p j k o (.close code)) provider) e)
      (.clo (.pair m imports) (.record k) residualBody) := by
  have henv : Target.Value (.pair (.pair .unit P) m) :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl,hP.2⟩,hm.2⟩
  have hcode := (projection1 (cap := .unit) rfl hP.2 hm.2).app_argument
    (hc.certificate_caller rfl henv hP.2)
  exact Target.Terminates.curried_template_forward hν hP hm
    (Target.Terminates.letIn henv hcode (provide_capture hP.2 hm.2 hc.2))

private theorem projected_merge_inv
    (ht : Target.TerminatesIn ν (.merge e f) n w)
    (he : Target.Terminates ν e x) (hf : Target.Terminates ν f y) :
    ∃ q, q ≤ n ∧ Target.TerminatesIn .unit (.merge x y) q w := by
  obtain ⟨x',a,b,rfl,hx,hrest⟩ := Target.strict_merge_left.decompose_counted ht
  have hxEq := hx.toTerminates.unique he
  subst x'
  obtain ⟨y',c,d,hb,hy,hmerge⟩ :=
    (Target.strict_merge_right he.2).decompose_counted hrest
  have hyEq := hy.toTerminates.unique hf
  subst y'
  exact ⟨d,by omega,hmerge.merge_caller rfl he.2 hf.2⟩

theorem link_counted_inv (hν : Target.Value ν)
    (ht : Target.TerminatesIn ν
      (.app (.app (link p i o (.close code)) provider) e) n w) :
    ∃ P m imports exports a b c d q,
      a < n ∧ b < n ∧ c < n ∧ d < n ∧ q < n ∧
      Target.TerminatesIn ν provider a P ∧ Target.TerminatesIn ν e b m ∧
      Target.TerminatesIn .unit (.app (.close code) P) c imports ∧
      Target.TerminatesIn .unit (.app m imports) d exports ∧
      Target.TerminatesIn .unit (.merge P exports) q w := by
  obtain ⟨P,m,a,b,k,hn,hP,hm,hbody⟩ := ht.curried_template_inv hν
  have henv : Target.Value (.pair (.pair .unit P) m) :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl,hP.2⟩,hm.2⟩
  obtain ⟨imports,c,t,hk,hcode,hrest⟩ := hbody.letIn_inv henv
  obtain ⟨c',hc',hcode'⟩ := hcode.projected_argument (projection1 rfl hP.2 hm.2)
  have henv' : Target.Value (.pair (.pair (.pair .unit P) m) imports) :=
    Bool.and_eq_true_iff.mpr ⟨henv,hcode.2⟩
  obtain ⟨exports,d,u,ht,hcall,hmerge⟩ := hrest.letIn_inv henv'
  obtain ⟨d',hd',hcall'⟩ := hcall.projected_function
    (projection1 (Bool.and_eq_true_iff.mpr ⟨rfl,hP.2⟩) hm.2 hcode.2)
  obtain ⟨d'',hd'',hcall''⟩ := hcall'.projected_argument (projection0 henv hcode.2)
  obtain ⟨q,hq,hmerge'⟩ := projected_merge_inv hmerge
    (projection3 rfl hP.2 hm.2 hcode.2 hcall.2) (projection0 henv' hcall.2)
  exact ⟨P,m,imports,exports,a,b,c',d'',q,by omega,by omega,by omega,by omega,by omega,
    hP,hm,hcode'.certificate_caller henv rfl hP.2,
    hcall''.app_caller rfl hm.2 hcode.2,hmerge'⟩

theorem link_forward (hν : Target.Value ν)
    (hP : Target.Terminates ν provider P) (hm : Target.Terminates ν e m)
    (hc : Target.Terminates .unit (.app (.close code) P) imports)
    (hb : Target.Terminates .unit (.app m imports) exports)
    (hu : Target.Terminates .unit (.merge P exports) w) :
    Target.Terminates ν (.app (.app (link p i o (.close code)) provider) e) w := by
  have hbase : Target.Value (.pair .unit P) := Bool.and_eq_true_iff.mpr ⟨rfl,hP.2⟩
  have henv : Target.Value (.pair (.pair .unit P) m) := Bool.and_eq_true_iff.mpr ⟨hbase,hm.2⟩
  have henv' : Target.Value (.pair (.pair (.pair .unit P) m) imports) :=
    Bool.and_eq_true_iff.mpr ⟨henv,hc.2⟩
  have henv'' : Target.Value (.pair (.pair (.pair (.pair .unit P) m) imports) exports) :=
    Bool.and_eq_true_iff.mpr ⟨henv',hb.2⟩
  have hcode := (projection1 (cap := .unit) rfl hP.2 hm.2).app_argument
    (hc.certificate_caller rfl henv hP.2)
  have hcall := ((projection0 (cap := .pair (.pair .unit P) m) henv hc.2).app_argument
    (hb.app_caller henv' hm.2 hc.2)).projected_function
      (projection1 (cap := .pair .unit P) hbase hm.2 hc.2)
  have hmerge := Target.strict_merge_left.terminates
    (projection3 (cap := .unit) rfl hP.2 hm.2 hc.2 hb.2)
    ((Target.strict_merge_right hP.2).terminates
      (projection0 (cap := .pair (.pair (.pair .unit P) m) imports) henv' hb.2)
      (hu.merge_caller henv'' hP.2 hb.2))
  exact Target.Terminates.curried_template_forward hν hP hm
    (Target.Terminates.letIn henv hcode (Target.Terminates.letIn henv' hcall hmerge))

theorem sandbox_call_counted_inv (hν : Target.Value ν) (hI : Target.Value imports)
    (ht : Target.TerminatesIn ν
      (.app (.clo .unit (.record i) (.box (.ix 0) body)) imports) n w) :
    ∃ j, j < n ∧ Target.TerminatesIn imports body j w := by
  obtain ⟨a,ha,hbody⟩ := Target.LogicalRelation.ApplyBody.clo.counted_inv hν
    (show Target.Value (.clo .unit (.record i) (.box (.ix 0) body)) from rfl) hI ht
  have henv : Target.Value (.pair .unit imports) := Bool.and_eq_true_iff.mpr ⟨rfl,hI⟩
  obtain ⟨env,b,j,hbj,hentry,hresult⟩ := hbody.native_box_inv henv
  have heq := hentry.toTerminates.unique (projection0 rfl hI)
  subst env
  exact ⟨j,by omega,hresult⟩

theorem sandbox_call_forward (hν : Target.Value ν) (hI : Target.Value imports)
    (ht : Target.Terminates imports body w) :
    Target.Terminates ν (.app (.clo .unit (.record i) (.box (.ix 0) body)) imports) w := by
  have henv : Target.Value (.pair .unit imports) := Bool.and_eq_true_iff.mpr ⟨rfl,hI⟩
  exact Target.LogicalRelation.ApplyBody.clo.terminates hν rfl hI
    (Target.Terminates.native_box henv (projection0 (cap := .unit) rfl hI) ht)

theorem captured_call_counted_inv (hν : Target.Value ν)
    (hC : Target.Value cap) (hI : Target.Value imports)
    (ht : Target.TerminatesIn ν
      (.app (.clo (.pair .unit cap) (.record i)
        (.box (.merge (.ix 1) (.ix 0)) body)) imports) n w) :
    ∃ env a b, a < n ∧ b < n ∧
      Target.TerminatesIn .unit (.merge cap imports) a env ∧
      Target.TerminatesIn env body b w := by
  have hcap : Target.Value (.pair .unit cap) := Bool.and_eq_true_iff.mpr ⟨rfl,hC⟩
  obtain ⟨q,hq,hbody⟩ := (Target.LogicalRelation.ApplyBody.clo
    (cap := .pair .unit cap) (a := .record i)
    (body := .box (.merge (.ix 1) (.ix 0)) body) (x := imports)).counted_inv hν hcap hI ht
  have henv : Target.Value (.pair (.pair .unit cap) imports) :=
    Bool.and_eq_true_iff.mpr ⟨hcap,hI⟩
  obtain ⟨env,a,b,hab,hentry,hresult⟩ := hbody.native_box_inv henv
  obtain ⟨a',ha',hentry'⟩ := projected_merge_inv hentry
    (projection1 rfl hC hI) (projection0 hcap hI)
  exact ⟨env,a',b,by omega,by omega,hentry',hresult⟩

theorem captured_call_forward (hν : Target.Value ν)
    (hC : Target.Value cap) (hI : Target.Value imports)
    (hm : Target.Terminates .unit (.merge cap imports) env)
    (ht : Target.Terminates env body w) :
    Target.Terminates ν (.app (.clo (.pair .unit cap) (.record i)
      (.box (.merge (.ix 1) (.ix 0)) body)) imports) w := by
  have hcap : Target.Value (.pair .unit cap) := Bool.and_eq_true_iff.mpr ⟨rfl,hC⟩
  have henv : Target.Value (.pair (.pair .unit cap) imports) :=
    Bool.and_eq_true_iff.mpr ⟨hcap,hI⟩
  have hentry := Target.strict_merge_left.terminates
    (projection1 (cap := .unit) rfl hC hI)
    ((Target.strict_merge_right hC).terminates
      (projection0 (cap := .pair .unit cap) hcap hI) (hm.merge_caller henv hC hI))
  exact (Target.LogicalRelation.ApplyBody.clo (cap := .pair .unit cap) (a := .record i)
    (body := .box (.merge (.ix 1) (.ix 0)) body) (x := imports)).terminates hν hcap hI
    (Target.Terminates.native_box henv hentry ht)

end LeanSce.Source.Templates

/-! ## Residual Template Evaluation -/

namespace LeanSce.Source.Templates

/-- The residual constructor saves its module and import values, without
    invoking the module. This is an actual finite evaluation. -/
theorem residual_values (hν : Target.Value ν) (hm : Target.Value m)
    (hs : Target.Value saved) :
    Target.Terminates ν (.app (.app (residual j k o) m) saved)
      (.clo (.pair m saved) (.record k) residualBody) := by
  apply Target.evaluate_sound (fuel := 32) hν
  simp [Target.evaluate,Target.step,residual,residualBody,Target.Term.close,
    Target.Term.ix,Target.Term.isValue,(show m.isValue = true from hm),
    (show saved.isValue = true from hs)]

/-- Constructor administration preserves the saved operand's actual remaining
    evaluation budget. -/
theorem residual_counted_inv (hν : Target.Value ν) (hm : Target.Value m)
    (ht : Target.TerminatesIn ν (.app (.app (residual j k o) m) e) n w) :
    ∃ saved i, i ≤ n ∧ Target.TerminatesIn ν e i saved ∧
      w = .clo (.pair m saved) (.record k) residualBody := by
  obtain ⟨saved,i,hi,hs,hcall⟩ := ht.app_input
  exact ⟨saved,i,hi,hs,hcall.unique (residual_values hν hm hs.2)⟩

theorem residual_forward (hν : Target.Value ν) (hm : Target.Value m)
    (ht : Target.Terminates ν e saved) :
    Target.Terminates ν (.app (.app (residual j k o) m) e)
      (.clo (.pair m saved) (.record k) residualBody) :=
  ht.app_argument (residual_values hν hm ht.2)

end LeanSce.Source.Templates

/-! ## Staged Template Evaluation -/

namespace LeanSce.Source.Templates
open LeanSce.Target
open LeanSce.Target.LogicalRelation

/-- The suspended wrapper returned by exact provision. -/
def exactResidual (k : Target.Row) (m saved : Target.Expr) : Target.Expr :=
  .clo (.pair m saved) (.record k) residualBody

private theorem residual_service_prefix (hm : Target.Value m)
    (hf : Target.Value fs) (hg : Target.Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true) :
    Target.Steps (.pair (.pair m (.record fs)) (.record gs)) residualBody
      (.app m (.record (fs.append gs))) := by
  let env : Target.Expr := .pair (.pair m (.record fs)) (.record gs)
  have henv : Target.Value env :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hm,hf⟩,hg⟩
  have hfun : Target.Terminates env (.fst (.fst .query)) m := by
    apply Target.evaluate_sound henv (fuel := 8)
    simp [Target.evaluate,Target.step,Target.Term.isValue,env,(show m.isValue = true from hm),
      (show fs.isValue = true from hf),(show gs.isValue = true from hg)]
  have hleft : Target.Terminates env (.snd (.fst .query)) (.record fs) := by
    apply Target.evaluate_sound henv (fuel := 8)
    simp [Target.evaluate,Target.step,Target.Term.isValue,env,(show m.isValue = true from hm),
      (show fs.isValue = true from hf),(show gs.isValue = true from hg)]
  have hright : Target.Terminates env (.snd .query) (.record gs) := by
    apply Target.evaluate_sound henv (fuel := 8)
    simp [Target.evaluate,Target.step,Target.Term.isValue,env,(show m.isValue = true from hm),
      (show fs.isValue = true from hf),(show gs.isValue = true from hg)]
  have hmerge : Target.Step env (.merge (.record fs) (.record gs)) (.record (fs.append gs)) := by
    refine ⟨henv,?_⟩
    rw [Target.step_merge_eq]
    simp only [Target.Term.isValue,(show fs.isValue = true from hf),(show gs.isValue = true from hg),
      Bool.not_true,Bool.false_eq_true,↓reduceIte,hd]
  exact hfun.1.app_left.trans ((Target.strict_merge_left.lift_steps hleft.1 |>.trans
    ((Target.strict_merge_right hf).lift_steps hright.1 |>.trans (.single hmerge))).app_right hm)

/-- Counted residual activation exposes exactly one original module service. -/
theorem residual_activation_inv (hν : Target.Value ν) (hm : Target.Value m)
    (hf : Target.Value fs) (hg : Target.Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true)
    (hb : ApplyBody m (.record (fs.append gs)) q)
    (ht : Target.TerminatesIn ν (.app (exactResidual k m (.record fs)) (.record gs)) n w) :
    ∃ i, i ≤ n ∧ Target.TerminatesIn q.1 q.2 i w := by
  have hcap : Target.Value (.pair m (.record fs)) := Bool.and_eq_true_iff.mpr ⟨hm,hf⟩
  obtain ⟨i,hi,ht⟩ := (ApplyBody.clo (cap := .pair m (.record fs)) (a := .record k)
    (body := residualBody) (x := .record gs)).counted_inv hν hcap hg ht
  obtain ⟨j,hj,ht⟩ := ht.after_steps (residual_service_prefix hm hf hg hd)
  have henv : Target.Value (.pair (.pair m (.record fs)) (.record gs)) :=
    Bool.and_eq_true_iff.mpr ⟨hcap,hg⟩
  obtain ⟨l,hl,hbody⟩ := hb.counted_inv henv hm (Target.Term.append_value fs hf hg) ht
  exact ⟨l,by omega,hbody⟩

theorem residual_activation_forward (hν : Target.Value ν) (hm : Target.Value m)
    (hf : Target.Value fs) (hg : Target.Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true)
    (hb : ApplyBody m (.record (fs.append gs)) q)
    (ht : Target.Terminates q.1 q.2 w) :
    Target.Terminates ν (.app (exactResidual k m (.record fs)) (.record gs)) w := by
  have hcap : Target.Value (.pair m (.record fs)) := Bool.and_eq_true_iff.mpr ⟨hm,hf⟩
  have henv : Target.Value (.pair (.pair m (.record fs)) (.record gs)) :=
    Bool.and_eq_true_iff.mpr ⟨hcap,hg⟩
  have hcall := hb.terminates henv hm (Target.Term.append_value fs hf hg) ht
  have hbody : Target.Terminates (.pair (.pair m (.record fs)) (.record gs)) residualBody w :=
    ⟨(residual_service_prefix hm hf hg hd).trans hcall.1,hcall.2⟩
  exact (ApplyBody.clo (cap := .pair m (.record fs)) (a := .record k)
    (body := residualBody) (x := .record gs)).terminates hν hcap hg hbody

/-- A residual call delegates to exactly one call of its saved module. -/
theorem residual_call_inv_slack (hν : Target.Value ν) (hm : Target.Value m)
    (hf : Target.Value fs) (hg : Target.Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true)
    (ht : Target.TerminatesIn ν (.app (exactResidual k m (.record fs)) (.record gs)) n w) :
    ∃ i, i+2 ≤ n ∧ Target.TerminatesIn .unit (.app m (.record (fs.append gs))) i w := by
  have hcap : Target.Value (.pair m (.record fs)) := Bool.and_eq_true_iff.mpr ⟨hm,hf⟩
  obtain ⟨i,hi,ht⟩ := (ApplyBody.clo (cap := .pair m (.record fs)) (a := .record k)
    (body := residualBody) (x := .record gs)).counted_inv hν hcap hg ht
  obtain ⟨j,hj,ht⟩ := ht.after_steps (residual_service_prefix hm hf hg hd)
  exact ⟨j,by omega,ht.app_caller rfl hm (Target.Term.append_value fs hf hg)⟩

theorem residual_call_inv (hν : Target.Value ν) (hm : Target.Value m)
    (hf : Target.Value fs) (hg : Target.Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true)
    (ht : Target.TerminatesIn ν (.app (exactResidual k m (.record fs)) (.record gs)) n w) :
    ∃ i, i < n ∧ Target.TerminatesIn .unit (.app m (.record (fs.append gs))) i w := by
  obtain ⟨i,hi,ht⟩ := residual_call_inv_slack hν hm hf hg hd ht
  exact ⟨i,by omega,ht⟩

theorem residual_call_forward (hν : Target.Value ν) (hm : Target.Value m)
    (hf : Target.Value fs) (hg : Target.Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true)
    (ht : Target.Terminates .unit (.app m (.record (fs.append gs))) w) :
    Target.Terminates ν (.app (exactResidual k m (.record fs)) (.record gs)) w := by
  have hcap : Target.Value (.pair m (.record fs)) := Bool.and_eq_true_iff.mpr ⟨hm,hf⟩
  have henv : Target.Value (.pair (.pair m (.record fs)) (.record gs)) :=
    Bool.and_eq_true_iff.mpr ⟨hcap,hg⟩
  have hbody : Target.Terminates (.pair (.pair m (.record fs)) (.record gs)) residualBody w :=
    ⟨(residual_service_prefix hm hf hg hd).trans
      (ht.app_caller henv hm (Target.Term.append_value fs hf hg)).1,ht.2⟩
  exact (ApplyBody.clo (cap := .pair m (.record fs)) (a := .record k)
    (body := residualBody) (x := .record gs)).terminates hν hcap hg hbody

/-- A finite chain of suspended provisions delegates to one original call. -/
inductive CallPath : Target.Expr → Target.Expr → Target.Expr → Target.Expr → Prop where
  | direct (hm : Target.Value m) (hi : Target.Value imports) : CallPath m imports m imports
  | residual (hm : Target.Value m) (hf : Target.Value fs) (hg : Target.Value gs)
      (hd : fs.labels.all (fun l => !gs.labels.contains l) = true)
      (hp : CallPath m (.record (fs.append gs)) original imports) :
      CallPath (exactResidual k m (.record fs)) (.record gs) original imports

theorem CallPath.counted_inv (hp : CallPath m input original imports)
    (hν : Target.Value ν) (ht : Target.TerminatesIn ν (.app m input) n w) :
    ∃ i, i ≤ n ∧ Target.TerminatesIn .unit (.app original imports) i w := by
  induction hp generalizing n ν with
  | direct hm hi => exact ⟨n,Nat.le_refl _,ht.app_caller rfl hm hi⟩
  | residual hm hf hg hd hp ih =>
    obtain ⟨j,hj,ht⟩ := residual_call_inv hν hm hf hg hd ht
    obtain ⟨i,hi,hbody⟩ := ih (ν := .unit) (show Target.Value .unit from rfl) ht
    exact ⟨i,by omega,hbody⟩

theorem CallPath.forward (hp : CallPath m input original imports)
    (hν : Target.Value ν) (ht : Target.Terminates .unit (.app original imports) w) :
    Target.Terminates ν (.app m input) w := by
  induction hp generalizing ν with
  | direct hm hi => exact ht.app_caller hν hm hi
  | residual hm hf hg hd hp ih => exact residual_call_forward hν hm hf hg hd (ih (ν := .unit) (show Target.Value .unit from rfl) ht)

end LeanSce.Source.Templates

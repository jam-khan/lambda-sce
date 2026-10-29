import LeanSce.Source.Elaboration.Contexts
import LeanSce.Source.Elaboration.Correctness
import LeanSce.Source.Elaboration.Templates
import LeanSce.Source.Linking.Laws
import LeanSce.Source.Metatheory.Adapters
import LeanSce.Source.Metatheory.Basic
import LeanSce.Target.LogicalRelation.Evaluation
import LeanSce.Target.LogicalRelation.Functions

/-!
# Source / Linking / Staging

Proofs and supporting constructions for staging.
-/

/-! ## Exact Template Pipelines -/

namespace LeanSce.Source.Templates
open LeanSce.Target
open LeanSce.Target.LogicalRelation

def exactRun (i o : Target.Row) (m imports : Target.Expr) : Target.Expr :=
  .app (.app (run i i o (Target.identityAdapter (.record i))) m) imports

def exactProvide (j k o : Target.Row) (saved m : Target.Expr) : Target.Expr :=
  .app (.app (provide j j k o (Target.identityAdapter (.record j))) saved) m

theorem exact_identity_app (hν : Target.Value ν) (hv : Target.Value v) :
    Target.Terminates ν (.app (Target.identityAdapter a) v) v :=
  Target.Terminates.close_lam_app hν hv (Target.ix_zero_terminates hv)

theorem exact_provide_forward (hν : Target.Value ν)
    (hs : Target.Terminates ν saved imports) (hm : Target.Terminates ν e m) :
    Target.Terminates ν (exactProvide j k o saved e) (exactResidual k m imports) :=
  provide_forward hν hs hm (exact_identity_app rfl hs.2)

theorem exact_run_call_inv (hν : Target.Value ν)
    (hm : Target.Terminates ν e m) (hp : Target.Terminates ν provider imports)
    (ht : Target.TerminatesIn ν (exactRun i o e provider) n w) :
    ∃ k, k < n ∧ Target.TerminatesIn .unit (.app m imports) k w := by
  obtain ⟨m',P,I,a,b,c,d,ha,hb,hc,hd,hM,hP,hI,hcall⟩ := run_counted_inv hν ht
  have hem := hM.toTerminates.unique hm
  have hep := hP.toTerminates.unique hp
  subst m'
  subst P
  have hei := hI.toTerminates.unique (exact_identity_app rfl hp.2)
  subst I
  exact ⟨d,hd,hcall⟩

theorem exact_run_call_forward (hν : Target.Value ν)
    (hm : Target.Terminates ν e m) (hp : Target.Terminates ν provider imports)
    (ht : Target.Terminates .unit (.app m imports) w) :
    Target.Terminates ν (exactRun i o e provider) w :=
  run_forward hν hm hp (exact_identity_app rfl hp.2) ht

/-- Exact linking templates may differ in their finite staging work. They
    preserve the complete logical behavior of the original module calls. -/
theorem exact_run_path_logical
    (hν : Target.Value ν) (hN : Target.Value N)
    (hm : Target.Terminates ν e m) (hM : Target.Terminates N E M)
    (hp : Target.Terminates ν provider input) (hP : Target.Terminates N Provider Input)
    (hl : CallPath m input original imports) (hr : CallPath M Input Original Imports)
    (hcore : ExprRel n a (.unit,.app original imports) (.unit,.app Original Imports)) :
    ExprRel n a (ν,exactRun i o e provider) (N,exactRun I O E Provider) := by
  apply ExprRel.pipelines (P := id) (Q := id) hcore
  · intro k hk w hw
    obtain ⟨j,hj,hcall⟩ := exact_run_call_inv hν hm hp hw
    obtain ⟨l,hjl,hbody⟩ := hl.counted_inv (ν := .unit) (show Target.Value .unit from rfl) hcall
    exact ⟨w,l,by omega,hbody,rfl⟩
  · intro k hk w hw
    obtain ⟨j,hj,hcall⟩ := exact_run_call_inv hN hM hP hw
    obtain ⟨l,hjl,hbody⟩ := hr.counted_inv (ν := .unit) (show Target.Value .unit from rfl) hcall
    exact ⟨w,l,by omega,hbody,rfl⟩
  · intro v hv
    exact exact_run_call_forward hν hm hp (hl.forward rfl hv)
  · intro V hV
    exact exact_run_call_forward hN hM hP (hr.forward rfl hV)
  · intros; assumption

end LeanSce.Source.Templates

/-! ## Staged Record Relation -/

namespace LeanSce.Source.Templates
open LeanSce.Target
open LeanSce.Target.LogicalRelation

private theorem lookup_swap_front (fs gs hs : Target.Fields)
    (hd : ∀ l ∈ fs.labels, l ∉ gs.labels) (l : String) :
    (fs.append (gs.append hs)).lookup l = (gs.append (fs.append hs)).lookup l := by
  by_cases hl : l ∈ fs.labels
  · have hg := Target.Term.lookup_none_of_not_mem gs (hd l hl)
    simp only [Target.Term.lookup_append,hg]
    cases fs.lookup l <;> rfl
  · have hf := Target.Term.lookup_none_of_not_mem fs hl
    simp only [Target.Term.lookup_append,hf]
    cases gs.lookup l <;> rfl

/-- Independent imports may be merged in either order, including values
    supplied by instantiated abstract rows. -/
theorem merge_swap_logical
    (hx : ValRel n (.record j) (.record fs) (.record Fs))
    (hy : ValRel n (.record k) (.record gs) (.record Gs))
    (hz : ValRel n (.record l) (.record hs) (.record Hs))
    (hjk : Target.Disjoint .empty j k) (hjl : Target.Disjoint .empty j l)
    (hkl : Target.Disjoint .empty k l) :
    ValRel n (.record (.union j (.union k l)))
      (.record (fs.append (gs.append hs))) (.record (Gs.append (Fs.append Hs))) := by
  have hdj := Target.disjoint_union_right.mpr ⟨hjk,hjl⟩
  have hdk := Target.disjoint_union_right.mpr ⟨hjk.symm,hkl⟩
  have hnormal := hx.merge (hy.merge hz hkl) hdj
  have hswapped := hy.merge (hx.merge hz hjl) hdk
  have wj := (hx.right.2.result_wf .empty).record_row
  have wk := (hy.right.2.result_wf .empty).record_row
  have wf := hx.right.2.value_record_inv hx.right.1 wj
  have wg := hy.right.2.value_record_inv hy.right.1 wk
  have hrow : Target.TyEq (.union k (.union j l)) (.union j (.union k l)) :=
    Target.TyEq.union_assoc.symm.trans ((Target.TyEq.union .union_comm .refl).trans .union_assoc)
  have hright : Target.ValueType .empty (.record (Gs.append (Fs.append Hs)))
      (.record (.union j (.union k l))) :=
    ⟨hswapped.right.1,.conv hswapped.right.2 (.record hrow) (hnormal.left.2.result_wf .empty)⟩
  apply ValRel.of_record_lookups hnormal.left hright
  intro label a hmem
  have wr := (hnormal.left.2.result_wf .empty).record_row
  obtain ⟨x,X,hx,hX,hrel⟩ := hnormal.get (wr.knownField_lookup hmem)
  refine ⟨_,_,x,X,rfl,rfl,hx,?_,hrel⟩
  rw [← lookup_swap_front Fs Gs Hs
    (fun label hl hL => hjk.knownLabels label (wf.labels_mem.mp hl) (wg.labels_mem.mp hL)) label]
  exact hX

end LeanSce.Source.Templates

/-! ## Staged Logical -/

namespace LeanSce.Source.Templates
open LeanSce.Target
open LeanSce.Target.LogicalRelation

private theorem record_merge_check
    (hf : Target.ValueType .empty (.record fs) (.record j))
    (hg : Target.ValueType .empty (.record gs) (.record k))
    (hd : Target.Disjoint .empty j k) :
    fs.labels.all (fun l => !gs.labels.contains l) = true :=
  (hf.2.value_record_inv hf.1 (hf.2.result_wf .empty).record_row).merge_check
    (hg.2.value_record_inv hg.1 (hg.2.result_wf .empty).record_row) hd

private theorem merge_value_records (hν : Target.Value ν)
    (hf : Target.ValueType .empty (.record fs) (.record j))
    (hg : Target.ValueType .empty (.record gs) (.record k))
    (hd : Target.Disjoint .empty j k) :
    Target.Terminates ν (.merge (.record fs) (.record gs)) (.record (fs.append gs)) := by
  refine ⟨.single ⟨hν,?_⟩,Target.Term.append_value fs hf.1 hg.1⟩
  rw [Target.step_merge_eq]
  simp only [Target.Term.isValue,(show fs.isValue = true from hf.1),
    (show gs.isValue = true from hg.1),Bool.not_true,Bool.false_eq_true,↓reduceIte,
    record_merge_check hf hg hd]

/-- Exact one-stage linking is logically equivalent to one direct call. -/
theorem staged_exact_logical
    (hm : ValRel n (.arr (.record (.union j k)) (.record o)) m M)
    (hx : ValRel n (.record j) x X) (hy : ValRel n (.record k) y Y)
    (hd : Target.Disjoint .empty j k) (hν : Target.Value ν) (hN : Target.Value N) :
    ExprRel n (.record o)
      (ν,exactRun k o (exactProvide j k o x m) y)
      (N,exactRun (.union j k) o M (.merge X Y)) := by
  obtain ⟨fs,rfl⟩ := hx.left.2.value_shape hx.left.1
  obtain ⟨Fs,rfl⟩ := hx.right.2.value_shape hx.right.1
  obtain ⟨gs,rfl⟩ := hy.left.2.value_shape hy.left.1
  obtain ⟨Gs,rfl⟩ := hy.right.2.value_shape hy.right.1
  have hjoin := hx.merge hy hd
  have hcore := hm.toExpr.app (ν := .unit) (N := .unit) hjoin.toExpr rfl rfl
  apply exact_run_path_logical hν hN
    (exact_provide_forward hν ⟨.refl,hx.left.1⟩ ⟨.refl,hm.left.1⟩)
    ⟨.refl,hm.right.1⟩ ⟨.refl,hy.left.1⟩
    (merge_value_records hN hx.right hy.right hd) ?_ ?_ hcore
  · exact .residual hm.left.1 hx.left.1 hy.left.1
      (record_merge_check hx.left hy.left hd) (.direct hm.left.1 hjoin.left.1)
  · exact .direct hm.right.1 hjoin.right.1

def exactTwiceStaged (j k l o : Target.Row) (m x y z : Target.Expr) : Target.Expr :=
  exactRun l o (exactProvide k l o y (exactProvide j (.union k l) o x m)) z

def exactTripleDirect (j k l o : Target.Row) (m x y z : Target.Expr) : Target.Expr :=
  exactRun (.union j (.union k l)) o m (.merge x (.merge y z))

private theorem twice_path (hν : Target.Value ν) (hm : Target.Value m)
    (hx : Target.Value fs) (hy : Target.Value gs) (hz : Target.Value hs)
    (hkl : gs.labels.all (fun l => !hs.labels.contains l) = true)
    (hjkl : fs.labels.all (fun l => !(gs.append hs).labels.contains l) = true) :
    Target.Terminates ν
      (exactProvide k l o (.record gs) (exactProvide j (.union k l) o (.record fs) m))
      (exactResidual l (exactResidual (.union k l) m (.record fs)) (.record gs)) ∧
    CallPath (exactResidual l (exactResidual (.union k l) m (.record fs)) (.record gs))
      (.record hs) m (.record (fs.append (gs.append hs))) := by
  have hstate : Target.Value (exactResidual (.union k l) m (.record fs)) :=
    Bool.and_eq_true_iff.mpr ⟨hm,hx⟩
  refine ⟨exact_provide_forward hν ⟨.refl,hy⟩
    (exact_provide_forward hν ⟨.refl,hx⟩ ⟨.refl,hm⟩),?_⟩
  exact .residual hstate hy hz hkl
    (.residual hm hx (Target.Term.append_value gs hy hz) hjkl
      (.direct hm (Target.Term.append_value fs hx (Target.Term.append_value gs hy hz))))

/-- Two suspended stages have the behavior of the original service on their
    exact import union, with both source operand orders preserved. -/
theorem twice_staged_exact_logical
    (hm : ValRel n (.arr (.record (.union j (.union k l))) (.record o)) m M)
    (hx : ValRel n (.record j) x X) (hy : ValRel n (.record k) y Y)
    (hz : ValRel n (.record l) z Z)
    (hjk : Target.Disjoint .empty j k) (hjl : Target.Disjoint .empty j l)
    (hkl : Target.Disjoint .empty k l) (hν : Target.Value ν) (hN : Target.Value N) :
    ExprRel n (.record o) (ν,exactTwiceStaged j k l o m x y z)
      (N,exactTripleDirect j k l o M X Y Z) := by
  obtain ⟨fs,rfl⟩ := hx.left.2.value_shape hx.left.1
  obtain ⟨Fs,rfl⟩ := hx.right.2.value_shape hx.right.1
  obtain ⟨gs,rfl⟩ := hy.left.2.value_shape hy.left.1
  obtain ⟨Gs,rfl⟩ := hy.right.2.value_shape hy.right.1
  obtain ⟨hs,rfl⟩ := hz.left.2.value_shape hz.left.1
  obtain ⟨Hs,rfl⟩ := hz.right.2.value_shape hz.right.1
  have hjkl := Target.disjoint_union_right.mpr ⟨hjk,hjl⟩
  have htail := hy.merge hz hkl
  have hjoin := hx.merge htail hjkl
  obtain ⟨hstate,hpath⟩ := twice_path (j := j) (k := k) (l := l) (o := o) hν hm.left.1
    hx.left.1 hy.left.1 hz.left.1 (record_merge_check hy.left hz.left hkl)
    (record_merge_check hx.left htail.left hjkl)
  have hprovider := (Target.strict_merge_right hx.right.1).terminates
    (merge_value_records hN hy.right hz.right hkl) (merge_value_records hN hx.right htail.right hjkl)
  exact exact_run_path_logical hν hN hstate ⟨.refl,hm.right.1⟩ ⟨.refl,hz.left.1⟩ hprovider
    hpath (.direct hm.right.1 hjoin.right.1)
    (hm.toExpr.app (ν := .unit) (N := .unit) hjoin.toExpr rfl rfl)

/-- Commuting stages preserve the original service and relate the permuted
    import maps field by field at every observation index. -/
theorem commuting_staged_exact_logical
    (hm : ValRel n (.arr (.record (.union j (.union k l))) (.record o)) m M)
    (hx : ValRel n (.record j) x X) (hy : ValRel n (.record k) y Y)
    (hz : ValRel n (.record l) z Z)
    (hjk : Target.Disjoint .empty j k) (hjl : Target.Disjoint .empty j l)
    (hkl : Target.Disjoint .empty k l) (hν : Target.Value ν) (hN : Target.Value N) :
    ExprRel n (.record o) (ν,exactTwiceStaged j k l o m x y z)
      (N,exactTwiceStaged k j l o M Y X Z) := by
  obtain ⟨fs,rfl⟩ := hx.left.2.value_shape hx.left.1
  obtain ⟨Fs,rfl⟩ := hx.right.2.value_shape hx.right.1
  obtain ⟨gs,rfl⟩ := hy.left.2.value_shape hy.left.1
  obtain ⟨Gs,rfl⟩ := hy.right.2.value_shape hy.right.1
  obtain ⟨hs,rfl⟩ := hz.left.2.value_shape hz.left.1
  obtain ⟨Hs,rfl⟩ := hz.right.2.value_shape hz.right.1
  have hjkl := Target.disjoint_union_right.mpr ⟨hjk,hjl⟩
  have hkjl := Target.disjoint_union_right.mpr ⟨hjk.symm,hkl⟩
  have htail := hy.merge hz hkl
  have hTail := hx.merge hz hjl
  have hjoin := merge_swap_logical hx hy hz hjk hjl hkl
  obtain ⟨hstate,hpath⟩ := twice_path (j := j) (k := k) (l := l) (o := o) hν hm.left.1
    hx.left.1 hy.left.1 hz.left.1 (record_merge_check hy.left hz.left hkl)
    (record_merge_check hx.left htail.left hjkl)
  obtain ⟨hState,hPath⟩ := twice_path (j := k) (k := j) (l := l) (o := o) hN hm.right.1
    hy.right.1 hx.right.1 hz.right.1 (record_merge_check hx.right hz.right hjl)
    (record_merge_check hy.right hTail.right hkjl)
  exact exact_run_path_logical hν hN hstate hState ⟨.refl,hz.left.1⟩ ⟨.refl,hz.right.1⟩ hpath hPath
    (hm.toExpr.app (ν := .unit) (N := .unit) hjoin.toExpr rfl rfl)

/-- The opposite staging order also agrees directly with the canonical union. -/
theorem swapped_staged_exact_logical
    (hm : ValRel n (.arr (.record (.union j (.union k l))) (.record o)) m M)
    (hx : ValRel n (.record j) x X) (hy : ValRel n (.record k) y Y)
    (hz : ValRel n (.record l) z Z)
    (hjk : Target.Disjoint .empty j k) (hjl : Target.Disjoint .empty j l)
    (hkl : Target.Disjoint .empty k l) (hν : Target.Value ν) (hN : Target.Value N) :
    ExprRel n (.record o) (ν,exactTwiceStaged k j l o m y x z)
      (N,exactTripleDirect j k l o M X Y Z) := by
  obtain ⟨fs,rfl⟩ := hx.left.2.value_shape hx.left.1
  obtain ⟨Fs,rfl⟩ := hx.right.2.value_shape hx.right.1
  obtain ⟨gs,rfl⟩ := hy.left.2.value_shape hy.left.1
  obtain ⟨Gs,rfl⟩ := hy.right.2.value_shape hy.right.1
  obtain ⟨hs,rfl⟩ := hz.left.2.value_shape hz.left.1
  obtain ⟨Hs,rfl⟩ := hz.right.2.value_shape hz.right.1
  have hjkl := Target.disjoint_union_right.mpr ⟨hjk,hjl⟩
  have hkjl := Target.disjoint_union_right.mpr ⟨hjk.symm,hkl⟩
  have htail := hy.merge hz hkl
  have hTail := hx.merge hz hjl
  have hnormal := hx.merge htail hjkl
  have hswap := merge_swap_logical hy hx hz hjk.symm hkl hjl
  have hrow : Target.TyEq (.union k (.union j l)) (.union j (.union k l)) :=
    Target.TyEq.union_assoc.symm.trans ((Target.TyEq.union .union_comm .refl).trans .union_assoc)
  have hjoin := ((equal_type n (hswap.left.2.result_wf .empty)
    (hnormal.left.2.result_wf .empty) (.record hrow)).1 _ _).mp hswap
  obtain ⟨hstate,hpath⟩ := twice_path (j := k) (k := j) (l := l) (o := o) hν hm.left.1
    hy.left.1 hx.left.1 hz.left.1 (record_merge_check hx.left hz.left hjl)
    (record_merge_check hy.left hTail.left hkjl)
  have hprovider := (Target.strict_merge_right hx.right.1).terminates
    (merge_value_records hN hy.right hz.right hkl) (merge_value_records hN hx.right htail.right hjkl)
  exact exact_run_path_logical hν hN hstate ⟨.refl,hm.right.1⟩ ⟨.refl,hz.left.1⟩ hprovider
    hpath (.direct hm.right.1 hnormal.right.1)
    (hm.toExpr.app (ν := .unit) (N := .unit) hjoin.toExpr rfl rfl)

end LeanSce.Source.Templates

/-! ## Staged Linking -/

namespace LeanSce.Source
open LeanSce.Target.LogicalRelation

private theorem value_erasure_related (hv : ValueType Δ v a) (hΔ : Context.Valid Δ)
    (hθ : Target.Closing θ Δ.erase) (n : Nat) :
    ValRel n (a.erase.subst θ) (v.erase.subst θ) (v.erase.subst θ) :=
  ((hv.2.erase hΔ).logical hΔ.erase).values (Term.erase_value v hv.1)
    (Term.erase_value v hv.1) hθ

private theorem identity_certificate (ha : WellFormed Δ a) :
    CertType Δ a a (identityAdapter a) := (Adapts.equal ha ha TyEq.refl).certificate

def tripleDirectRun (j k l o : Row) (m x y z : Expr) : Expr :=
  directRun (.union j (.union k l)) o m (.merge x (.merge y z))

/-- S3.1's canonical artifacts are related under every closing substitution,
    at every index, and under arbitrary related caller environments. -/
theorem staging_erasure_logical {h : Typ}
    (hm : ValueType Δ m (.module (.union j k) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hd : Disjoint Δ j k) (hΔ : Context.Valid Δ) :
    Target.LogicalRelation.OpenRel Δ.erase h.erase
      (stagedRun j k o m x y).erase
      (directRun (.union j k) o m (.merge x y)).erase (Ty.record o).erase := by
  intro θ hθ n ν N hν
  have hr := Templates.staged_exact_logical (value_erasure_related hm hΔ hθ n)
    (value_erasure_related hx hΔ hθ n) (value_erasure_related hy hΔ hθ n)
    (hd.erase.subst hθ.respects) hν.left.1 hν.right.1
  simpa only [stagedRun,directRun,Term.erase,identityAdapter,
    Target.identityAdapter,Templates.exactRun,Templates.exactProvide,
    Templates.run,Templates.provide,Target.Term.subst,Ty.erase,Target.Ty.subst,
    Term.close,Term.ix,Target.Term.close,Target.Term.letIn,Target.Term.ix] using hr

private theorem twice_erasure_logical {h : Typ}
    (hm : ValueType Δ m (.module (.union j (.union k l)) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hz : ValueType Δ z (.record l))
    (hjk : Disjoint Δ j k) (hjl : Disjoint Δ j l) (hkl : Disjoint Δ k l)
    (hΔ : Context.Valid Δ) :
    Target.LogicalRelation.OpenRel Δ.erase h.erase
      (twiceStagedRun j k l o m x y z).erase
      (tripleDirectRun j k l o m x y z).erase (Ty.record o).erase := by
  intro θ hθ n ν N hν
  have hr := Templates.twice_staged_exact_logical (value_erasure_related hm hΔ hθ n)
    (value_erasure_related hx hΔ hθ n) (value_erasure_related hy hΔ hθ n)
    (value_erasure_related hz hΔ hθ n) (hjk.erase.subst hθ.respects)
    (hjl.erase.subst hθ.respects) (hkl.erase.subst hθ.respects) hν.left.1 hν.right.1
  simpa only [twiceStagedRun,tripleDirectRun,stagedRun,directRun,Term.erase,identityAdapter,
    Target.identityAdapter,Templates.exactTwiceStaged,Templates.exactTripleDirect,
    Templates.exactRun,Templates.exactProvide,Templates.run,Templates.provide,
    Target.Term.subst,Ty.erase,Target.Ty.subst,Term.close,Term.ix,
    Target.Term.close,Target.Term.letIn,Target.Term.ix] using hr

theorem commuting_erasure_logical {h : Typ}
    (hm : ValueType Δ m (.module (.union j (.union k l)) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hz : ValueType Δ z (.record l))
    (hjk : Disjoint Δ j k) (hjl : Disjoint Δ j l) (hkl : Disjoint Δ k l)
    (hΔ : Context.Valid Δ) :
    Target.LogicalRelation.OpenRel Δ.erase h.erase
      (twiceStagedRun j k l o m x y z).erase
      (twiceStagedRun k j l o m y x z).erase (Ty.record o).erase := by
  intro θ hθ n ν N hν
  have hr := Templates.commuting_staged_exact_logical (value_erasure_related hm hΔ hθ n)
    (value_erasure_related hx hΔ hθ n) (value_erasure_related hy hΔ hθ n)
    (value_erasure_related hz hΔ hθ n) (hjk.erase.subst hθ.respects)
    (hjl.erase.subst hθ.respects) (hkl.erase.subst hθ.respects) hν.left.1 hν.right.1
  simpa only [twiceStagedRun,stagedRun,Term.erase,identityAdapter,
    Target.identityAdapter,Templates.exactTwiceStaged,Templates.exactRun,Templates.exactProvide,
    Templates.run,Templates.provide,Target.Term.subst,Ty.erase,Target.Ty.subst,
    Term.close,Term.ix,Target.Term.close,Target.Term.letIn,Target.Term.ix] using hr

private theorem swapped_erasure_logical {h : Typ}
    (hm : ValueType Δ m (.module (.union j (.union k l)) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hz : ValueType Δ z (.record l))
    (hjk : Disjoint Δ j k) (hjl : Disjoint Δ j l) (hkl : Disjoint Δ k l)
    (hΔ : Context.Valid Δ) :
    Target.LogicalRelation.OpenRel Δ.erase h.erase
      (twiceStagedRun k j l o m y x z).erase
      (tripleDirectRun j k l o m x y z).erase (Ty.record o).erase := by
  intro θ hθ n ν N hν
  have hr := Templates.swapped_staged_exact_logical (value_erasure_related hm hΔ hθ n)
    (value_erasure_related hx hΔ hθ n) (value_erasure_related hy hΔ hθ n)
    (value_erasure_related hz hΔ hθ n) (hjk.erase.subst hθ.respects)
    (hjl.erase.subst hθ.respects) (hkl.erase.subst hθ.respects) hν.left.1 hν.right.1
  simpa only [twiceStagedRun,tripleDirectRun,stagedRun,directRun,Term.erase,identityAdapter,
    Target.identityAdapter,Templates.exactTwiceStaged,Templates.exactTripleDirect,
    Templates.exactRun,Templates.exactProvide,Templates.run,Templates.provide,
    Target.Term.subst,Ty.erase,Target.Ty.subst,Term.close,Term.ix,
    Target.Term.close,Target.Term.letIn,Target.Term.ix] using hr

/-- Exact staging remains well typed at every well-formed caller ambient. -/
theorem staging_typed
    (hm : ValueType Δ m (.module (.union j k) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hd : Disjoint Δ j k) (hΔ : Context.Valid Δ) (hh : WellFormed Δ h) :
    HasType Δ h (stagedRun j k o m x y) (.record o) ∧
    HasType Δ h (directRun (.union j k) o m (.merge x y)) (.record o) := by
  have wj := (hx.2.result_wf hΔ).record_row
  have wk := (hy.2.result_wf hΔ).record_row
  exact ⟨.run (.provide (hx.inclusion hh) (hm.inclusion hh)
    (identity_certificate (.record wj)) wj wk hd) (hy.inclusion hh) (identity_certificate (.record wk)),
    .run (hm.inclusion hh) (.merge (hx.inclusion hh) (hy.inclusion hh) hd)
      (identity_certificate (.record (.union wj wk hd)))⟩

private theorem twice_typed
    (hm : ValueType Δ m (.module (.union j (.union k l)) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hz : ValueType Δ z (.record l))
    (hjk : Disjoint Δ j k) (hjl : Disjoint Δ j l) (hkl : Disjoint Δ k l)
    (hΔ : Context.Valid Δ) (hh : WellFormed Δ h) :
    HasType Δ h (twiceStagedRun j k l o m x y z) (.record o) ∧
    HasType Δ h (twiceStagedRun k j l o m y x z) (.record o) ∧
    HasType Δ h (tripleDirectRun j k l o m x y z) (.record o) := by
  have wj := (hx.2.result_wf hΔ).record_row
  have wk := (hy.2.result_wf hΔ).record_row
  have wl := (hz.2.result_wf hΔ).record_row
  have wo := (hm.2.result_wf hΔ).module_exports
  have hjkl := disjoint_union_right.mpr ⟨hjk,hjl⟩
  have hkjl := disjoint_union_right.mpr ⟨hjk.symm,hkl⟩
  have hleft : HasType Δ h (twiceStagedRun j k l o m x y z) (.record o) :=
    .run (.provide (hy.inclusion hh)
      (.provide (hx.inclusion hh) (hm.inclusion hh) (identity_certificate (.record wj))
        wj (.union wk wl hkl) hjkl)
      (identity_certificate (.record wk)) wk wl hkl)
      (hz.inclusion hh) (identity_certificate (.record wl))
  have he : TyEq (.union j (.union k l)) (.union k (.union j l)) :=
    TyEq.union_assoc.symm.trans ((TyEq.union .union_comm .refl).trans .union_assoc)
  have hms : HasType Δ h m (.module (.union k (.union j l)) o) :=
    .conv (hm.inclusion hh) (.module he .refl) (.module (.union wk (.union wj wl hjl) hkjl) wo)
  refine ⟨hleft,?_,?_⟩
  · exact .run (.provide (hx.inclusion hh)
      (.provide (hy.inclusion hh) hms (identity_certificate (.record wk))
        wk (.union wj wl hjl) hkjl)
      (identity_certificate (.record wj)) wj wl hjl)
      (hz.inclusion hh) (identity_certificate (.record wl))
  · exact .run (hm.inclusion hh) (.merge (hx.inclusion hh)
      (.merge (hy.inclusion hh) (hz.inclusion hh) hkl) hjkl)
      (identity_certificate (.record (.union wj (.union wk wl hkl) hjkl)))

/-- S3.1. No observer restriction is used: the conclusion is full source
    contextual equivalence, including stored code and higher-order exports. -/
theorem staging_of_correspondence
    (hterm : Goals.TerminationCorrespondence) (hdiv : Goals.DivergenceCorrespondence)
    (hm : ValueType Δ m (.module (.union j k) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hd : Disjoint Δ j k) (hΔ : Context.Valid Δ) (hh : WellFormed Δ h) :
    ContextualEq Δ h (.record o) (stagedRun j k o m x y)
      (directRun (.union j k) o m (.merge x y)) := by
  obtain ⟨hl,hr⟩ := staging_typed hm hx hy hd hΔ hh
  exact erasure_logical_contextual_of_correspondence hterm hdiv hl hr hΔ
    (staging_erasure_logical hm hx hy hd hΔ)

/-- S3.2. Both staging orders agree, and the second agrees directly with the
    declared import union; all premises are exactly value/disjointness typing. -/
theorem commuting_stages_of_correspondence
    (hterm : Goals.TerminationCorrespondence) (hdiv : Goals.DivergenceCorrespondence)
    (hm : ValueType Δ m (.module (.union j (.union k l)) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hz : ValueType Δ z (.record l))
    (hjk : Disjoint Δ j k) (hjl : Disjoint Δ j l) (hkl : Disjoint Δ k l)
    (hΔ : Context.Valid Δ) (hh : WellFormed Δ h) :
    ContextualEq Δ h (.record o) (twiceStagedRun j k l o m x y z)
      (twiceStagedRun k j l o m y x z) ∧
    ContextualEq Δ h (.record o) (twiceStagedRun k j l o m y x z)
      (tripleDirectRun j k l o m x y z) := by
  obtain ⟨hl,hr,hdirect⟩ := twice_typed hm hx hy hz hjk hjl hkl hΔ hh
  exact ⟨erasure_logical_contextual_of_correspondence hterm hdiv hl hr hΔ
      (commuting_erasure_logical hm hx hy hz hjk hjl hkl hΔ),
    erasure_logical_contextual_of_correspondence hterm hdiv hr hdirect hΔ
      (swapped_erasure_logical hm hx hy hz hjk hjl hkl hΔ)⟩

end LeanSce.Source

/-! ## Linking Correctness -/

namespace LeanSce.Source

/-- S3.1: supplying exact imports in stages is fully contextually equivalent
    to supplying their disjoint union at execution. -/
theorem staging
    (hm : ValueType Δ m (.module (.union j k) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hd : Disjoint Δ j k) (hΔ : Context.Valid Δ) (hh : WellFormed Δ h) :
    ContextualEq Δ h (.record o) (stagedRun j k o m x y)
      (directRun (.union j k) o m (.merge x y)) :=
  staging_of_correspondence termination_correspondence divergence_correspondence hm hx hy hd hΔ hh

/-- S3.2: independent stages commute, and both orders retain the behavior of
    direct execution on the exact declared import union. -/
theorem commuting_stages
    (hm : ValueType Δ m (.module (.union j (.union k l)) o))
    (hx : ValueType Δ x (.record j)) (hy : ValueType Δ y (.record k))
    (hz : ValueType Δ z (.record l))
    (hjk : Disjoint Δ j k) (hjl : Disjoint Δ j l) (hkl : Disjoint Δ k l)
    (hΔ : Context.Valid Δ) (hh : WellFormed Δ h) :
    ContextualEq Δ h (.record o) (twiceStagedRun j k l o m x y z)
      (twiceStagedRun k j l o m y x z) ∧
    ContextualEq Δ h (.record o) (twiceStagedRun k j l o m y x z)
      (tripleDirectRun j k l o m x y z) :=
  commuting_stages_of_correspondence termination_correspondence divergence_correspondence
    hm hx hy hz hjk hjl hkl hΔ hh

end LeanSce.Source

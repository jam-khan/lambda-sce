import LeanSce.Target.Adapters.Evaluation
import LeanSce.Target.LogicalRelation.Data
import LeanSce.Target.LogicalRelation.Evaluation
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Semantics / Templates

Proofs and supporting constructions for templates.
-/

/-! ## Projection Evaluation -/

namespace LeanSce.Target

theorem projection0 (hc : Value cap) (hx : Value x) :
    Terminates (.pair cap x) (.ix 0) x := by
  apply evaluate_sound (fuel := 2) (ν := .pair cap x) (Bool.and_eq_true_iff.mpr ⟨hc,hx⟩)
  simp [evaluate,step,Term.ix,Term.isValue,(show cap.isValue = true from hc),
    (show x.isValue = true from hx)]

theorem projection1 (hc : Value cap) (hx : Value x) (hy : Value y) :
    Terminates (.pair (.pair cap x) y) (.ix 1) x := by
  apply evaluate_sound (fuel := 3) (ν := .pair (.pair cap x) y)
    (Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hc,hx⟩,hy⟩)
  simp [evaluate,step,Term.ix,Term.isValue,(show cap.isValue = true from hc),
    (show x.isValue = true from hx),(show y.isValue = true from hy)]

theorem projection2 (hc : Value cap) (hx : Value x) (hy : Value y) (hz : Value z) :
    Terminates (.pair (.pair (.pair cap x) y) z) (.ix 2) x := by
  apply evaluate_sound (fuel := 4) (ν := .pair (.pair (.pair cap x) y) z)
    (Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hc,hx⟩,hy⟩,hz⟩)
  simp [evaluate,step,Term.ix,Term.isValue,(show cap.isValue = true from hc),
    (show x.isValue = true from hx),(show y.isValue = true from hy),(show z.isValue = true from hz)]

theorem projection3 (hc : Value cap) (hx : Value x) (hy : Value y) (hz : Value z)
    (hu : Value u) :
    Terminates (.pair (.pair (.pair (.pair cap x) y) z) u) (.ix 3) x := by
  apply evaluate_sound (fuel := 5) (ν := .pair (.pair (.pair (.pair cap x) y) z) u)
    (Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hc,hx⟩,hy⟩,hz⟩,hu⟩)
  simp [evaluate,step,Term.ix,Term.isValue,(show cap.isValue = true from hc),
    (show x.isValue = true from hx),(show y.isValue = true from hy),
    (show z.isValue = true from hz),(show u.isValue = true from hu)]

theorem TerminatesIn.projected_function (ht : TerminatesIn ν (.app f e) n w)
    (hf : Terminates ν f F) :
    ∃ k, k ≤ n ∧ TerminatesIn ν (.app F e) k w := by
  obtain ⟨F',i,k,rfl,hF,hrest⟩ := strict_app_left.decompose_counted ht
  have heq := hF.toTerminates.unique hf
  subst F'
  exact ⟨k,by omega,hrest⟩

theorem TerminatesIn.projected_argument (ht : TerminatesIn ν (.app f e) n w)
    (he : Terminates ν e x) :
    ∃ k, k ≤ n ∧ TerminatesIn ν (.app f x) k w := by
  obtain ⟨F,i,j,rfl,hF,hrest⟩ := strict_app_left.decompose_counted ht
  obtain ⟨x',p,q,hj,hx,hcall⟩ := (strict_app_right hF.2).decompose_counted hrest
  have heq := hx.toTerminates.unique he
  subst x'
  exact ⟨i+q,by omega,⟨hF.1.app_left.trans hcall.1,ht.2⟩⟩

theorem Terminates.projected_function (ht : Terminates ν (.app F e) w)
    (hf : Terminates ν f F) : Terminates ν (.app f e) w :=
  ⟨hf.1.app_left.trans ht.1,ht.2⟩

theorem TerminatesIn.merge_caller (ht : TerminatesIn ν (.merge a b) n w)
    (hμ : Value μ) (ha : Value a) (hb : Value b) :
    TerminatesIn μ (.merge a b) n w := by
  cases ht.1 with
  | refl => cases ht.2
  | next hs htail =>
    have hh := hs.2
    simp only [step_merge_eq,(show a.isValue = true from ha),
      (show b.isValue = true from hb),Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
    cases a <;> try simp only [reduceCtorEq] at hh
    case record fs =>
      cases b <;> try simp only [reduceCtorEq] at hh
      case record gs =>
        split at hh
        · rename_i hd
          simp only [Option.some.injEq] at hh
          subst_vars
          have hv : Value (.record (fs.append gs)) := Term.append_value fs ha hb
          obtain ⟨rfl,rfl⟩ := htail.value_inv hv
          exact ⟨.next ⟨hμ,by simpa only [step_merge_eq,Term.isValue,
            (show fs.isValue = true from ha),(show gs.isValue = true from hb),
            Bool.not_true,Bool.false_eq_true,↓reduceIte] using hs.2⟩ .refl,hv⟩
        · cases hh

theorem Terminates.merge_caller (ht : Terminates ν (.merge a b) w)
    (hμ : Value μ) (ha : Value a) (hb : Value b) :
    Terminates μ (.merge a b) w := by
  obtain ⟨n,hn⟩ := ht.counted
  exact (hn.merge_caller hμ ha hb).toTerminates

end LeanSce.Target

/-! ## Closed Template Evaluation -/

namespace LeanSce.Target
open LogicalRelation

theorem close_lam_counted (hν : Value ν) :
    TerminatesIn ν (.close (.lam a body)) 2 (.clo .unit a body) := by
  refine ⟨.next ⟨hν,rfl⟩ (.next (box_value hν rfl rfl) .refl),rfl⟩

theorem TerminatesIn.close_lam_inv (ht : TerminatesIn ν (.close (.lam a body)) n w)
    (hν : Value ν) : n = 2 ∧ w = .clo .unit a body := by
  obtain ⟨j,hj,ht⟩ := ht.after_prefix (close_lam_counted hν).1
  obtain ⟨rfl,rfl⟩ := ht.1.value_inv rfl
  exact ⟨by omega,rfl⟩

theorem TerminatesIn.lam_inv (ht : TerminatesIn ν (.lam a body) n w)
    (hν : Value ν) : n = 1 ∧ w = .clo ν a body := by
  obtain ⟨j,hj,ht⟩ := ht.after_step ⟨hν,rfl⟩
  obtain ⟨rfl,rfl⟩ := ht.1.value_inv hν
  exact ⟨by omega,rfl⟩

/-- A closed template reads no caller environment while constructing its
    function. Its argument is nevertheless evaluated in the original caller. -/
theorem TerminatesIn.close_lam_app_inv
    (ht : TerminatesIn ν (.app (.close (.lam a body)) e) n w) (hν : Value ν) :
    ∃ x i j, n = i+j+4 ∧ TerminatesIn ν e i x ∧
      TerminatesIn (.pair .unit x) body j w := by
  obtain ⟨F,p,q,hpq,hF,hrest⟩ := strict_app_left.decompose_counted ht
  obtain ⟨rfl,rfl⟩ := hF.close_lam_inv hν
  obtain ⟨x,i,j,hij,hx,hcall⟩ := (strict_app_right (show Value (.clo .unit a body) from rfl)).decompose_counted hrest
  obtain ⟨k,hk,hbody⟩ := (ApplyBody.clo (cap := .unit) (a := a) (body := body) (x := x)).counted_inv
    hν rfl hx.2 hcall
  exact ⟨x,i,k,by omega,hx,hbody⟩

theorem Terminates.close_lam_app_forward (hν : Value ν) (he : Terminates ν e x)
    (hb : Terminates (.pair .unit x) body w) :
    Terminates ν (.app (.close (.lam a body)) e) w :=
  he.app_argument (Terminates.close_lam_app hν he.2 hb)

/-- A curried closed template spends seven steps outside its two operands and
    its final body. Both operands retain the original caller environment. -/
theorem TerminatesIn.curried_template_inv
    (ht : TerminatesIn ν (.app (.app (.close (.lam a (.lam b body))) e) f) n w)
    (hν : Value ν) :
    ∃ x y i j k, n = i+j+k+7 ∧ TerminatesIn ν e i x ∧
      TerminatesIn ν f j y ∧ TerminatesIn (.pair (.pair .unit x) y) body k w := by
  obtain ⟨F,p,q,hpq,hF,hrest⟩ := strict_app_left.decompose_counted ht
  obtain ⟨x,i,k,hik,hx,hclosure⟩ := hF.close_lam_app_inv hν
  have henv : Value (.pair .unit x) := Bool.and_eq_true_iff.mpr ⟨rfl,hx.2⟩
  obtain ⟨rfl,rfl⟩ := hclosure.lam_inv henv
  have hfun : Value (.clo (.pair .unit x) b body) := henv
  obtain ⟨y,j,l,hjl,hy,hcall⟩ := (strict_app_right hfun).decompose_counted hrest
  obtain ⟨k,hk,hbody⟩ := (ApplyBody.clo (cap := .pair .unit x) (a := b) (body := body) (x := y)).counted_inv
    hν hfun hy.2 hcall
  exact ⟨x,y,i,j,k,by omega,hx,hy,hbody⟩

theorem Terminates.curried_template_forward (hν : Value ν)
    (he : Terminates ν e x) (hf : Terminates ν f y)
    (hb : Terminates (.pair (.pair .unit x) y) body w) :
    Terminates ν (.app (.app (.close (.lam a (.lam b body))) e) f) w := by
  have henv : Value (.pair .unit x) := Bool.and_eq_true_iff.mpr ⟨rfl,he.2⟩
  have hfirst : Terminates ν (.app (.close (.lam a (.lam b body))) e)
      (.clo (.pair .unit x) b body) :=
    Terminates.close_lam_app_forward hν he ⟨.single ⟨henv,rfl⟩,henv⟩
  have hsecond := (ApplyBody.clo (cap := .pair .unit x) (a := b) (body := body) (x := y)).terminates
    hν henv hf.2 hb
  exact ⟨hfirst.1.app_left.trans ((hf.1.app_right hfirst.2).trans hsecond.1),hsecond.2⟩

end LeanSce.Target

/-! ## Native Evaluation -/

namespace LeanSce.Target

theorem strict_native_box : StrictFrame ν (fun e => .box e body) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he : e.isValue = false := by
      cases hh : e.isValue <;> first | rfl | exact False.elim (hn hh)
    simp [step_box_eq,he]

theorem TerminatesIn.pair_inv (ht : TerminatesIn ν (.pair e f) n w) :
    ∃ x y i j, n = i+j ∧ TerminatesIn ν e i x ∧ TerminatesIn ν f j y ∧ w = .pair x y := by
  obtain ⟨x,i,p,hip,hx,hrest⟩ := strict_pair_left.decompose_counted ht
  obtain ⟨y,j,q,hjq,hy,hpair⟩ := (strict_pair_right hx.2).decompose_counted hrest
  have hv : Value (.pair x y) := Bool.and_eq_true_iff.mpr ⟨hx.2,hy.2⟩
  obtain ⟨rfl,rfl⟩ := hpair.1.value_inv hv
  exact ⟨x,y,i,j,by omega,hx,hy,rfl⟩

theorem Terminates.pair (he : Terminates ν e x) (hf : Terminates ν f y) :
    Terminates ν (.pair e f) (.pair x y) :=
  strict_pair_left.terminates he ((strict_pair_right he.2).terminates hf
    ⟨.refl,Bool.and_eq_true_iff.mpr ⟨he.2,hf.2⟩⟩)

theorem TerminatesIn.query_inv (ht : TerminatesIn ν .query n w) (hν : Value ν) :
    n = 1 ∧ w = ν := by
  obtain ⟨i,hi,ht⟩ := ht.after_step (query_step hν)
  obtain ⟨rfl,rfl⟩ := ht.1.value_inv hν
  exact ⟨by omega,rfl⟩

/-- Entering a native box retains precisely the evaluated replacement ambient. -/
theorem TerminatesIn.native_box_inv (ht : TerminatesIn ν (.box e body) n w)
    (hν : Value ν) :
    ∃ cap i j, n = i+j+1 ∧ TerminatesIn ν e i cap ∧ TerminatesIn cap body j w := by
  obtain ⟨cap,i,k,hik,hcap,hrest⟩ := strict_native_box.decompose_counted ht
  obtain ⟨j,hj,hbody⟩ := hrest.box_inv hν hcap.2
  exact ⟨cap,i,j,by omega,hcap,hbody⟩

theorem Terminates.native_box (hν : Value ν) (he : Terminates ν e cap)
    (hb : Terminates cap body w) : Terminates ν (.box e body) w :=
  strict_native_box.terminates he (hb.box hν he.2)

theorem TerminatesIn.letIn_inv (ht : TerminatesIn ν (.letIn e body) n w)
    (hν : Value ν) :
    ∃ x i j, n = i+j+2 ∧ TerminatesIn ν e i x ∧
      TerminatesIn (.pair ν x) body j w := by
  obtain ⟨cap,p,j,hpj,hcap,hbody⟩ := ht.native_box_inv hν
  obtain ⟨v,x,i,q,hiq,hν',hx,rfl⟩ := hcap.pair_inv
  obtain ⟨rfl,rfl⟩ := hν'.query_inv hν
  exact ⟨x,q,j,by omega,hx,hbody⟩

theorem Terminates.letIn (hν : Value ν) (he : Terminates ν e x)
    (hb : Terminates (.pair ν x) body w) : Terminates ν (.letIn e body) w :=
  Terminates.native_box hν ((show Terminates ν .query ν from ⟨.single (query_step hν),hν⟩).pair he) hb

end LeanSce.Target

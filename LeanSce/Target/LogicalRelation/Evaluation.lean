import LeanSce.Target.Adapters.Termination
import LeanSce.Target.LogicalRelation.Contexts
import LeanSce.Target.Metatheory.Basic

/-!
# Target / LogicalRelation / Evaluation

Proofs and supporting constructions for evaluation.
-/

/-! ## Adapter Coherence Evaluation -/

namespace LeanSce.Target

theorem Terminates.unique (h₁ : Terminates ν e v) (h₂ : Terminates ν e w) : v = w := by
  obtain ⟨hs,hv⟩ := h₁
  induction hs generalizing w with
  | refl => exact h₂.1.from_value hv
  | next hs htail ih =>
    cases h₂.1 with
    | refl => exact False.elim (value_irreducible h₂.2 hs)
    | next hs' htail' =>
      have he := step_deterministic hs hs'
      cases he
      exact ih ⟨htail',h₂.2⟩ hv

theorem TerminatesIn.app_input (he : TerminatesIn ν (.app c e) k w) :
    ∃ v i, i ≤ k ∧ TerminatesIn ν e i v ∧ Terminates ν (.app c v) w := by
  obtain ⟨F,i,j,hk,hF,hrest⟩ := strict_app_left.decompose_counted he
  obtain ⟨v,p,q,hj,hv,hcall⟩ := (strict_app_right hF.2).decompose_counted hrest
  exact ⟨v,p,by omega,hv,
    (hF.1.toSteps.app_left.trans hcall.1.toSteps),hcall.2⟩

private theorem box_inverse_steps (hs : StepsN ν k start w) :
    ∀ env body, start = .box env body → Value env → Value w →
      ∃ j, k = j+1 ∧ TerminatesIn env body j w := by
  induction hs with
  | refl =>
    intro env body he henv hw
    rw [he] at hw
    simp [Value,Term.isValue] at hw
  | @next start next k finish hs htail ih =>
    intro env body he henv hw
    subst start
    have hstep := hs.2
    rw [step_box_eq] at hstep
    simp only [(show env.isValue = true from henv),Bool.not_true,Bool.false_eq_true,↓reduceIte] at hstep
    cases hb : body.isValue with
    | true =>
      simp only [hb,↓reduceIte,Option.some.injEq] at hstep
      subst next
      obtain ⟨rfl,rfl⟩ := htail.value_inv hb
      exact ⟨0,rfl,.refl,hb⟩
    | false =>
      simp only [hb,Bool.false_eq_true,↓reduceIte] at hstep
      obtain ⟨body',hbody,heq⟩ := Option.map_eq_some_iff.mp hstep
      obtain ⟨j,hj,ht⟩ := ih env body' heq.symm henv hw
      exact ⟨j+1,by omega,.next ⟨henv,hbody⟩ ht.1,ht.2⟩

/-- A box contributes exactly its final removal step to a terminating body run. -/
theorem TerminatesIn.box_inv (_hν : Value ν) (henv : Value env)
    (hs : TerminatesIn ν (.box env body) k w) :
    ∃ j, k = j+1 ∧ TerminatesIn env body j w :=
  box_inverse_steps hs.1 env body rfl henv hs.2

theorem TerminatesIn.after_step (ht : TerminatesIn ν e k w) (hs : Step ν e e') :
    ∃ j, k = j+1 ∧ TerminatesIn ν e' j w := by
  cases ht.1 with
  | refl => exact False.elim (value_irreducible ht.2 hs)
  | next hfirst htail =>
    have he := step_deterministic hs hfirst
    cases he
    exact ⟨_,rfl,htail,ht.2⟩

namespace LogicalRelation

theorem ApplyBody.env_value (hb : ApplyBody f x q) (hf : Value f) (hx : Value x) : Value q.1 := by
  cases hb with
  | clo => exact Bool.and_eq_true_iff.mpr ⟨hf,hx⟩
  | rclo => exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hf,hf⟩,hx⟩

theorem ApplyBody.step (hb : ApplyBody f x q) (hν : Value ν) (hf : Value f) (hx : Value x) :
    Step ν (.app f x) (.box q.1 q.2) := by
  cases hb <;> exact ⟨hν,by simp [step_app_eq,(show _ = true from hf),(show _ = true from hx)]⟩

theorem ApplyBody.terminates (hb : ApplyBody f x q) (hν : Value ν) (hf : Value f) (hx : Value x)
    (ht : Terminates q.1 q.2 w) : Terminates ν (.app f x) w :=
  ⟨.next (hb.step hν hf hx) (ht.box hν (hb.env_value hf hx)).1,ht.2⟩

theorem ApplyBody.counted_inv (hb : ApplyBody f x q) (hν : Value ν) (hf : Value f) (hx : Value x)
    (ht : TerminatesIn ν (.app f x) k w) :
    ∃ j, k = j+2 ∧ TerminatesIn q.1 q.2 j w := by
  obtain ⟨i,hi,ht⟩ := ht.after_step (hb.step hν hf hx)
  obtain ⟨j,hj,hbody⟩ := ht.box_inv hν (hb.env_value hf hx)
  exact ⟨j,by omega,hbody⟩

theorem TypeBody.env_value (hb : TypeBody f u q) (hf : Value f) : Value q.1 := by
  cases hb; exact hf

theorem TypeBody.step (hb : TypeBody f u q) (hν : Value ν) (hf : Value f) :
    Step ν (.tapp f u) (.box q.1 q.2) := by
  cases hb
  exact ⟨hν,by simp [step_tapp_eq,(show _ = true from hf)]⟩

theorem TypeBody.terminates (hb : TypeBody f u q) (hν : Value ν) (hf : Value f)
    (ht : Terminates q.1 q.2 w) : Terminates ν (.tapp f u) w :=
  ⟨.next (hb.step hν hf) (ht.box hν (hb.env_value hf)).1,ht.2⟩

theorem TypeBody.counted_inv (hb : TypeBody f u q) (hν : Value ν) (hf : Value f)
    (ht : TerminatesIn ν (.tapp f u) k w) :
    ∃ j, k = j+2 ∧ TerminatesIn q.1 q.2 j w := by
  obtain ⟨i,hi,ht⟩ := ht.after_step (hb.step hν hf)
  obtain ⟨j,hj,hbody⟩ := ht.box_inv hν (hb.env_value hf)
  exact ⟨j,by omega,hbody⟩

/-- Total value transformations lift to computations with residual budgets. -/
theorem ExprRel.total_adapters (he : ExprRel n a (ν,e) (N,E))
    (hl : ∀ v, ValueType .empty v a → ∃ w, Terminates ν (.app c v) w)
    (hr : ∀ V, ValueType .empty V a → ∃ W, Terminates N (.app d V) W)
    (hmap : ∀ m, m ≤ n → ∀ v V, ValRel m a v V → ∀ w W,
      Terminates ν (.app c v) w → Terminates N (.app d V) W → ValRel m b w W) :
    ExprRel n b (ν,.app c e) (N,.app d E) := by
  rw [ExprRel] at he ⊢
  constructor
  · intro k hk w hw
    obtain ⟨v,i,hik,hv,hcall⟩ := hw.app_input
    obtain ⟨V,hV,hrel⟩ := he.1 i (Nat.lt_of_le_of_lt hik hk) v hv
    have htV : ValueType .empty V a := by rw [ValRel] at hrel; exact hrel.2.1
    obtain ⟨W,hW⟩ := hr V htV
    refine ⟨W,hV.app_argument hW,?_⟩
    exact (hmap (n-i) (Nat.sub_le _ _) v V hrel w W hcall hW).mono
      (Nat.sub_le_sub_left hik n)
  · intro k hk W hW
    obtain ⟨V,i,hik,hV,hcall⟩ := hW.app_input
    obtain ⟨v,hv,hrel⟩ := he.2 i (Nat.lt_of_le_of_lt hik hk) V hV
    have htv : ValueType .empty v a := by rw [ValRel] at hrel; exact hrel.1
    obtain ⟨w,hw⟩ := hl v htv
    refine ⟨w,hv.app_argument hw,?_⟩
    exact (hmap (n-i) (Nat.sub_le _ _) v V hrel w W hw hcall).mono
      (Nat.sub_le_sub_left hik n)

end LogicalRelation
end LeanSce.Target

/-! ## Caller Independence -/

namespace LeanSce.Target

theorem TerminatesIn.box_caller (ht : TerminatesIn ν (.box env body) n w)
    (hν : Value ν) (hμ : Value μ) (he : Value env) :
    TerminatesIn μ (.box env body) n w := by
  obtain ⟨j,rfl,hbody⟩ := ht.box_inv hν he
  exact hbody.box hμ he

private theorem value_app_step (hf : Value f) (hx : Value x)
    (hs : Step ν (.app f x) e') :
    ∃ env body, e' = .box env body ∧ Value env ∧
      ∀ μ, Value μ → Step μ (.app f x) (.box env body) := by
  have hh := hs.2
  simp only [step_app_eq,(show f.isValue = true from hf),
    (show x.isValue = true from hx),Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases f <;> simp only [reduceCtorEq,Option.some.injEq] at hh
  case clo cap a body =>
    subst e'
    refine ⟨.pair cap x,body,rfl,Bool.and_eq_true_iff.mpr ⟨hf,hx⟩,?_⟩
    intro μ hμ
    exact ⟨hμ,by simp [step_app_eq,Term.isValue,(show cap.isValue = true from hf),
      (show x.isValue = true from hx)]⟩
  case rclo cap a b body =>
    subst e'
    refine ⟨.pair (.pair cap (.rclo cap a b body)) x,body,rfl,
      Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hf,hf⟩,hx⟩,?_⟩
    intro μ hμ
    exact ⟨hμ,by simp [step_app_eq,Term.isValue,(show cap.isValue = true from hf),
      (show x.isValue = true from hx)]⟩

/-- A saved value-function call has exactly the same reductions under any
    caller: activation installs its own captured environment. -/
theorem TerminatesIn.app_caller (ht : TerminatesIn ν (.app f x) n w)
    (hμ : Value μ) (hf : Value f) (hx : Value x) :
    TerminatesIn μ (.app f x) n w := by
  cases ht.1 with
  | refl => cases ht.2
  | next hs htail =>
    obtain ⟨env,body,rfl,he,hstep⟩ := value_app_step hf hx hs
    exact ⟨.next (hstep μ hμ)
      (TerminatesIn.box_caller ⟨htail,ht.2⟩ hs.1 hμ he).1,ht.2⟩

/-- A closed certificate is evaluated under unit, with its original reduction
    count retained, even if its stored code is an arbitrary computation. -/
theorem TerminatesIn.certificate_caller
    (ht : TerminatesIn ν (.app (.box .unit code) x) n w)
    (hν : Value ν) (hμ : Value μ) (hx : Value x) :
    TerminatesIn μ (.app (.box .unit code) x) n w := by
  obtain ⟨f,i,j,rfl,hf,hrest⟩ := strict_app_left.decompose_counted ht
  have hf' := hf.box_caller hν hμ (show Value .unit from rfl)
  have hrest' := hrest.app_caller hμ hf.2 hx
  exact ⟨hf'.1.app_left.trans hrest'.1,ht.2⟩

theorem Terminates.app_caller (ht : Terminates ν (.app f x) w)
    (hμ : Value μ) (hf : Value f) (hx : Value x) :
    Terminates μ (.app f x) w := by
  obtain ⟨n,hn⟩ := ht.counted
  exact (hn.app_caller hμ hf hx).toTerminates

theorem Terminates.certificate_caller
    (ht : Terminates ν (.app (.box .unit code) x) w)
    (hν : Value ν) (hμ : Value μ) (hx : Value x) :
    Terminates μ (.app (.box .unit code) x) w := by
  obtain ⟨n,hn⟩ := ht.counted
  exact (hn.certificate_caller hν hμ hx).toTerminates

end LeanSce.Target

/-! ## Logical Relation Administrative -/

namespace LeanSce.Target.LogicalRelation

/-- Finite extra work may be prepended on either side. The bounded side pays
    for its own extra step; the other side only needs to terminate. -/
theorem ExprRel.step_left (hr : ExprRel n a (ν,e') (N,E)) (hs : Step ν e e') :
    ExprRel n a (ν,e) (N,E) := by
  rw [ExprRel] at hr ⊢
  constructor
  · intro k hk v hv
    obtain ⟨j,hj,hbody⟩ := hv.after_step hs
    obtain ⟨w,hw,hrel⟩ := hr.1 j (by omega) v hbody
    exact ⟨w,hw,hrel.mono (by omega)⟩
  · intro k hk w hw
    obtain ⟨v,hv,hrel⟩ := hr.2 k hk w hw
    exact ⟨v,⟨.next hs hv.1,hv.2⟩,hrel⟩

theorem ExprRel.step_right (hr : ExprRel n a (ν,e) (N,E')) (hs : Step N E E') :
    ExprRel n a (ν,e) (N,E) := by
  rw [ExprRel] at hr ⊢
  constructor
  · intro k hk v hv
    obtain ⟨w,hw,hrel⟩ := hr.1 k hk v hv
    exact ⟨w,⟨.next hs hw.1,hw.2⟩,hrel⟩
  · intro k hk w hw
    obtain ⟨j,hj,hbody⟩ := hw.after_step hs
    obtain ⟨v,hv,hrel⟩ := hr.2 j (by omega) w hbody
    exact ⟨v,hv,hrel.mono (by omega)⟩

theorem ExprRel.prefix_left (hr : ExprRel n a (ν,e') (N,E)) (hs : Steps ν e e') :
    ExprRel n a (ν,e) (N,E) := by
  induction hs with
  | refl => exact hr
  | next hs _ ih => exact (ih hr).step_left hs

theorem ExprRel.prefix_right (hr : ExprRel n a (ν,e) (N,E')) (hs : Steps N E E') :
    ExprRel n a (ν,e) (N,E) := by
  induction hs with
  | refl => exact hr
  | next hs _ ih => exact (ih hr).step_right hs

/-- Strict pipelines may have different saved environments and finite overhead.
    Inversion exposes their actual underlying computation, with its measured
    budget; forward execution returns the advertised total value map. -/
theorem ExprRel.pipelines {P Q : Expr → Expr} (he : ExprRel n a q r)
    (hl : ∀ k, k < n → ∀ w, TerminatesIn ν e k w →
      ∃ v i, i ≤ k ∧ TerminatesIn q.1 q.2 i v ∧ w = P v)
    (hr : ∀ k, k < n → ∀ W, TerminatesIn N E k W →
      ∃ V i, i ≤ k ∧ TerminatesIn r.1 r.2 i V ∧ W = Q V)
    (fl : ∀ v, Terminates q.1 q.2 v → Terminates ν e (P v))
    (fr : ∀ V, Terminates r.1 r.2 V → Terminates N E (Q V))
    (hm : ∀ m, m ≤ n → ∀ v V, ValRel m a v V → ValRel m b (P v) (Q V)) :
    ExprRel n b (ν,e) (N,E) := by
  rw [ExprRel] at he ⊢
  constructor
  · intro k hk w hw
    obtain ⟨v,i,hi,hv,rfl⟩ := hl k hk w hw
    obtain ⟨V,hV,hrel⟩ := he.1 i (by omega) v hv
    exact ⟨Q V,fr V hV,(hm (n-i) (Nat.sub_le _ _) v V hrel).mono (by omega)⟩
  · intro k hk W hW
    obtain ⟨V,i,hi,hV,rfl⟩ := hr k hk W hW
    obtain ⟨v,hv,hrel⟩ := he.2 i (by omega) V hV
    exact ⟨P v,fl v hv,(hm (n-i) (Nat.sub_le _ _) v V hrel).mono (by omega)⟩

end LeanSce.Target.LogicalRelation

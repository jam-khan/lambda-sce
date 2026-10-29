import LeanSce.Target.Metatheory.Values
import LeanSce.Target.Metatheory.Typing
import LeanSce.Target.Metatheory.Safety
import LeanSce.Target.LogicalRelation.Definitions
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Substitution

/-!
# Target / LogicalRelation / Properties

Proofs and supporting constructions for properties.
-/

/-! ## Logical Relation Properties -/

namespace LeanSce.Target.LogicalRelation

private theorem val_mono_of_shape (hs : ∀ {v w}, ShapeRel n a v w → ShapeRel m a v w)
    (h : ValRel n a v w) : ValRel m a v w := by
  rw [ValRel] at h ⊢
  exact ⟨h.1,h.2.1,hs h.2.2⟩

theorem ShapeRel.mono (h : ShapeRel n a v w) (hm : m ≤ n) : ShapeRel m a v w := by
  induction a generalizing v w with
  | unit | int | bool | string => rw [ShapeRel] at h ⊢; exact h
  | tvar | rvar => rw [ShapeRel] at h; exact False.elim h
  | empty | gnil | gcons => rw [ShapeRel]; trivial
  | prod a b iha ihb =>
    rw [ShapeRel] at h ⊢
    obtain ⟨x,y,X,Y,hv,hw,hx,hy⟩ := h
    exact ⟨x,y,X,Y,hv,hw,val_mono_of_shape iha hx,val_mono_of_shape ihb hy⟩
  | sum a b iha ihb =>
    rw [ShapeRel] at h ⊢
    rcases h with ⟨t,t',x,X,hv,hw,hx⟩ | ⟨t,t',y,Y,hv,hw,hy⟩
    · exact Or.inl ⟨t,t',x,X,hv,hw,val_mono_of_shape iha hx⟩
    · exact Or.inr ⟨t,t',y,Y,hv,hw,val_mono_of_shape ihb hy⟩
  | tag l a ih =>
    rw [ShapeRel] at h ⊢
    obtain ⟨x,X,hv,hw,hx⟩ := h
    exact ⟨x,X,hv,hw,val_mono_of_shape ih hx⟩
  | record r ih =>
    rw [ShapeRel] at h ⊢
    exact ih h
  | arr a b iha ihb =>
    rw [ShapeRel] at h ⊢
    intro j hj x X hx
    exact h j (Nat.lt_of_lt_of_le hj hm) x X hx
  | all k gs a ihg iha =>
    rw [ShapeRel] at h ⊢
    intro j hj u hk hu hg
    exact h j (Nat.lt_of_lt_of_le hj hm) u hk hu hg
  | ex k gs a ihg iha =>
    rw [ShapeRel] at h ⊢
    obtain ⟨u,t,t',x,X,hv,hw,hk,hu,hg,hx⟩ := h
    exact ⟨u,t,t',x,X,hv,hw,hk,hu,hg,fun j hj => hx j (Nat.lt_of_lt_of_le hj hm)⟩
  | mu a ih =>
    rw [ShapeRel] at h ⊢
    obtain ⟨t,t',x,X,hv,hw,hx⟩ := h
    exact ⟨t,t',x,X,hv,hw,fun j hj => hx j (Nat.lt_of_lt_of_le hj hm)⟩
  | field l a ih =>
    rw [ShapeRel] at h ⊢
    obtain ⟨fs,gs,x,X,hv,hw,hl,hr,hx⟩ := h
    exact ⟨fs,gs,x,X,hv,hw,hl,hr,val_mono_of_shape ih hx⟩
  | union r s ihr ihs =>
    rw [ShapeRel] at h ⊢
    exact ⟨ihr h.1,ihs h.2⟩

theorem ValRel.mono (h : ValRel n a v w) (hm : m ≤ n) : ValRel m a v w :=
  val_mono_of_shape (fun {_ _} hs => ShapeRel.mono hs hm) h

theorem ExprRel.mono (h : ExprRel n a q r) (hm : m ≤ n) : ExprRel m a q r := by
  rw [ExprRel] at h ⊢
  constructor
  · intro k hk v hv
    obtain ⟨w,hw,hr⟩ := h.1 k (Nat.lt_of_lt_of_le hk hm) v hv
    exact ⟨w,hw,hr.mono (Nat.sub_le_sub_right hm k)⟩
  · intro k hk w hw
    obtain ⟨v,hv,hr⟩ := h.2 k (Nat.lt_of_lt_of_le hk hm) w hw
    exact ⟨v,hv,hr.mono (Nat.sub_le_sub_right hm k)⟩

end LeanSce.Target.LogicalRelation

/-! ## Contextual Equivalence — facts -/

namespace LeanSce.Target
namespace LogicalRelation

theorem ValRel.ground_eq (h : ValRel n a v w) (hg : GroundType a) : v = w := by
  rw [ValRel] at h
  have hs := h.2.2
  cases hg with
  | unit => rw [ShapeRel] at hs; obtain ⟨rfl,rfl⟩ := hs; rfl
  | int => rw [ShapeRel] at hs; obtain ⟨_,rfl,rfl⟩ := hs; rfl
  | bool => rw [ShapeRel] at hs; obtain ⟨_,rfl,rfl⟩ := hs; rfl
  | string => rw [ShapeRel] at hs; obtain ⟨_,rfl,rfl⟩ := hs; rfl

/-- All-index logical relatedness gives the actual ground observation, including
    an infinite reduction when no finite result exists. -/
theorem ground_adequacy (hr : ∀ n, ExprRel n g (ν,e) (ν,E)) (hg : GroundType g)
    (hν : ValueType .empty ν H) (he : HasType .empty H e g)
    (hE : HasType .empty H E g) : ObservationEq ν e E := by
  have ht : ∀ v, Terminates ν e v ↔ Terminates ν E v := by
    intro v
    constructor
    · intro hv
      obtain ⟨k,hk⟩ := hv.counted
      have hrk := hr (k+1)
      rw [ExprRel] at hrk
      obtain ⟨w,hw,heq⟩ := hrk.1 k (by omega) v hk
      have hvw := heq.ground_eq hg
      simpa only [hvw] using hw
    · intro hv
      obtain ⟨k,hk⟩ := hv.counted
      have hrk := hr (k+1)
      rw [ExprRel] at hrk
      obtain ⟨w,hw,heq⟩ := hrk.2 k (by omega) v hk
      have hwv := heq.ground_eq hg
      simpa only [hwv] using hw
  refine ⟨ht,?_⟩
  rw [diverges_iff_not_terminates he .empty hν, diverges_iff_not_terminates hE .empty hν]
  simp only [ht]

end LogicalRelation
end LeanSce.Target

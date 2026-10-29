import LeanSce.Target.Abstraction.Infrastructure
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Abstraction / Substitution

Proofs and supporting constructions for substitution.
-/

/-! ## Heterogeneous Renaming -/

section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace LeanSce.Target.Heterogeneous

@[simp] theorem subst_instantiate_zero (θ : Subst) (p : Arg) (k : Kind) :
    θ.instantiate p k 0 = p.openSubst k 0 := by cases k <;> cases p <;> rfl

@[simp] theorem subst_instantiate_succ (θ : Subst) (p : Arg) (k : Kind) (i : Nat) :
    θ.instantiate p k (i+1) = θ k i := by
  simp [Subst.instantiate,Subst.lift,Ty.open_weaken]

def Valuation.reindex (η : Valuation) (ρ : Nat → Nat) : Valuation where
  left := fun k i => η.left k (ρ i)
  right := fun k i => η.right k (ρ i)
  types := fun i => η.types (ρ i)
  fields := fun i => η.fields (ρ i)

@[simp] theorem Valuation.reindex_extend (η : Valuation) (ρ : Nat → Nat) (p : Candidate) :
    (η.extend p).reindex (liftRen ρ) = (η.reindex ρ).extend p := by
  unfold Valuation.reindex Valuation.extend
  congr 1
  · funext k i; cases i <;> simp [liftRen]
  · funext k i; cases i <;> simp [liftRen]
  · funext i; cases i <;> rfl
  · funext i; cases i <;> rfl

@[simp] theorem Valuation.reindex_extend_succ (η : Valuation) (p : Candidate) :
    (η.extend p).reindex Nat.succ = η := by
  unfold Valuation.reindex Valuation.extend
  congr 1
  · funext k i; exact subst_instantiate_succ _ _ _ _
  · funext k i; exact subst_instantiate_succ _ _ _ _

theorem rename_subst_lift (a : Ty s) (ρ : Nat → Nat) (θ : Subst) :
    (a.rename (liftRen ρ)).subst θ.lift =
      a.subst (Subst.lift (fun k i => θ k (ρ i))) := by
  rw [Ty.subst_rename]
  congr 1
  funext k i
  cases i <;> rfl

theorem rename_open (a : Ty s) (p : Arg) (ρ : Nat → Nat) :
    (a.open p).rename ρ = (a.rename (liftRen ρ)).open (p.rename ρ) := by
  rw [Ty.open,Ty.rename_subst,Ty.open,Ty.subst_rename]
  congr 1
  funext k i
  cases i with
  | zero => cases p <;> cases k <;> rfl
  | succ i => cases k <;> rfl

mutual
theorem ExprRel.rename (a : Typ) (ρ : Nat → Nat) (η : Valuation) :
    ExprRel n (a.rename ρ) η q r ↔ ExprRel n a (η.reindex ρ) q r := by
  rw [ExprRel,ExprRel]
  constructor
  · intro h; constructor
    · intro k hk v hv
      obtain ⟨w,hw,hr⟩ := h.1 k hk v hv
      exact ⟨w,hw,(ValRel.rename a ρ η).mp hr⟩
    · intro k hk w hw
      obtain ⟨v,hv,hr⟩ := h.2 k hk w hw
      exact ⟨v,hv,(ValRel.rename a ρ η).mp hr⟩
  · intro h; constructor
    · intro k hk v hv
      obtain ⟨w,hw,hr⟩ := h.1 k hk v hv
      exact ⟨w,hw,(ValRel.rename a ρ η).mpr hr⟩
    · intro k hk w hw
      obtain ⟨v,hv,hr⟩ := h.2 k hk w hw
      exact ⟨v,hv,(ValRel.rename a ρ η).mpr hr⟩
termination_by (n,5 * sizeOf a + 4)
decreasing_by
  all_goals by_cases hz : k = 0
  all_goals first | (subst k; apply Prod.Lex.right; omega) | (apply Prod.Lex.left; omega)

theorem ValRel.rename (a : Typ) (ρ : Nat → Nat) (η : Valuation) :
    ValRel n (a.rename ρ) η v w ↔ ValRel n a (η.reindex ρ) v w := by
  rw [ValRel,ValRel,Ty.subst_rename,Ty.subst_rename]
  exact and_congr Iff.rfl (and_congr Iff.rfl (ShapeRel.rename a ρ η))
termination_by (n,5 * sizeOf a + 3)

theorem ShapeRel.rename (a : Typ) (ρ : Nat → Nat) (η : Valuation) :
    ShapeRel n (a.rename ρ) η v w ↔ ShapeRel n a (η.reindex ρ) v w := by
  cases hcase : a with
  | unit | int | bool | string | tvar => simp only [Ty.rename,ShapeRel,Valuation.reindex]
  | prod a b =>
    have ha := fun (x X : Expr) => ValRel.rename (n:=n) (v:=x) (w:=X) a ρ η
    have hb := fun (x X : Expr) => ValRel.rename (n:=n) (v:=x) (w:=X) b ρ η
    simp only [Ty.rename,ShapeRel,ha,hb]
  | sum a b =>
    have ha := fun (x X : Expr) => ValRel.rename (n:=n) (v:=x) (w:=X) a ρ η
    have hb := fun (x X : Expr) => ValRel.rename (n:=n) (v:=x) (w:=X) b ρ η
    simp only [Ty.rename,ShapeRel,ha,hb]
  | tag l a =>
    have ha := fun (x X : Expr) => ValRel.rename (n:=n) (v:=x) (w:=X) a ρ η
    simp only [Ty.rename,ShapeRel,ha]
  | record r => simpa only [Ty.rename,ShapeRel] using (RowShape.rename (n := n) (v := v) (w := w) r ρ η)
  | arr a b =>
    simp only [Ty.rename,ShapeRel]
    constructor
    · intro h j hj x X hx
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj x X ((ValRel.rename a ρ η).mpr hx)
      exact ⟨q,r,hq,hr,(ExprRel.rename b ρ η).mp hb⟩
    · intro h j hj x X hx
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj x X ((ValRel.rename a ρ η).mp hx)
      exact ⟨q,r,hq,hr,(ExprRel.rename b ρ η).mpr hb⟩
  | all k gs a =>
    simp only [Ty.rename,ShapeRel,rename_subst_lift]
    constructor
    · intro h j hj p hp hl hr
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj p hp hl hr
      refine ⟨q,r,hq,hr,?_⟩
      simpa only [Valuation.reindex_extend] using (ExprRel.rename a (liftRen ρ) (η.extend p)).mp hb
    · intro h j hj p hp hl hr
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj p hp hl hr
      exact ⟨q,r,hq,hr,(ExprRel.rename a (liftRen ρ) (η.extend p)).mpr
        (by simpa only [Valuation.reindex_extend] using hb)⟩
  | ex k gs a =>
    simp only [Ty.rename,ShapeRel,rename_subst_lift]
    constructor
    · rintro ⟨p,t,t',x,X,hv,hw,hp,hl,hr,hb⟩
      refine ⟨p,t,t',x,X,hv,hw,hp,hl,hr,?_⟩
      simpa only [Valuation.reindex_extend] using (ValRel.rename a (liftRen ρ) (η.extend p)).mp hb
    · rintro ⟨p,t,t',x,X,hv,hw,hp,hl,hr,hb⟩
      exact ⟨p,t,t',x,X,hv,hw,hp,hl,hr,(ValRel.rename a (liftRen ρ) (η.extend p)).mpr
        (by simpa only [Valuation.reindex_extend] using hb)⟩
  | mu a =>
    simp only [Ty.rename,ShapeRel]
    constructor
    · rintro ⟨t,t',x,X,hv,hw,hb⟩
      refine ⟨t,t',x,X,hv,hw,fun j hj => ?_⟩
      apply (ValRel.rename (a.open (.type (.mu a))) ρ η).mp
      simpa only [rename_open,Arg.rename,Ty.rename] using hb j hj
    · rintro ⟨t,t',x,X,hv,hw,hb⟩
      refine ⟨t,t',x,X,hv,hw,fun j hj => ?_⟩
      have hh := (ValRel.rename (a.open (.type (.mu a))) ρ η).mpr (hb j hj)
      simpa only [rename_open,Arg.rename,Ty.rename] using hh
termination_by (n,5 * sizeOf a + 2)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  all_goals first | apply Prod.Lex.left; omega | apply Prod.Lex.right; omega

theorem RowShape.rename (r : Row) (ρ : Nat → Nat) (η : Valuation) :
    RowShape n (r.rename ρ) η v w ↔ RowShape n r (η.reindex ρ) v w := by
  have hf := fun (l : String) (x X : Expr) => FieldRel.rename (n:=n) (l:=l) (v:=x) (w:=X) r ρ η
  simp only [RowShape,hf]
termination_by (n,5 * sizeOf r + 1)

theorem FieldRel.rename (r : Row) (ρ : Nat → Nat) (η : Valuation) :
    FieldRel n (r.rename ρ) η l v w ↔ FieldRel n r (η.reindex ρ) l v w := by
  cases hcase : r with
  | rvar i | empty => simp only [Ty.rename,FieldRel,Valuation.reindex]
  | field k a =>
    have ha := fun (x X : Expr) => ValRel.rename (n:=n) (v:=x) (w:=X) a ρ η
    simp only [Ty.rename,FieldRel,ha]
  | union r s =>
    have hr := fun (l : String) (x X : Expr) => FieldRel.rename (n:=n) (l:=l) (v:=x) (w:=X) r ρ η
    have hs := fun (l : String) (x X : Expr) => FieldRel.rename (n:=n) (l:=l) (v:=x) (w:=X) s ρ η
    simp only [Ty.rename,FieldRel,hr,hs]
termination_by (n,5 * sizeOf r)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals omega
end

/-- A fresh abstract witness does not change the interpretation of old types. -/
theorem ValRel.weaken (a : Typ) (η : Valuation) (p : Candidate) :
    ValRel n (a.rename Nat.succ) (η.extend p) v w ↔ ValRel n a η v w := by
  simpa only [Valuation.reindex_extend_succ] using ValRel.rename a Nat.succ (η.extend p)

theorem ExprRel.weaken (a : Typ) (η : Valuation) (p : Candidate) :
    ExprRel n (a.rename Nat.succ) (η.extend p) q r ↔ ExprRel n a η q r := by
  simpa only [Valuation.reindex_extend_succ] using ExprRel.rename a Nat.succ (η.extend p)

end LeanSce.Target.Heterogeneous

end

/-! ## Heterogeneous Equivalence -/

namespace LeanSce.Target.Heterogeneous

/-- Semantic environments may differ outside the typed part of a variable
    candidate. Such pairs cannot enter the interpretation of a typed program. -/
structure Valuation.Equivalent (η ζ : Valuation) : Prop where
  left : η.left = ζ.left
  right : η.right = ζ.right
  types : ∀ i n v w, ValRel n (.tvar i) η v w ↔ ValRel n (.tvar i) ζ v w
  fields : ∀ i n l v w, FieldRel n (.rvar i) η l v w ↔ FieldRel n (.rvar i) ζ l v w

theorem Valuation.Equivalent.refl (η : Valuation) : η.Equivalent η :=
  ⟨rfl,rfl,by intros; rfl,by intros; rfl⟩

theorem Valuation.Equivalent.extend {η ζ : Valuation} (he : η.Equivalent ζ) (p : Candidate) :
    (η.extend p).Equivalent (ζ.extend p) := by
  refine ⟨by simp [Valuation.extend,he.left],by simp [Valuation.extend,he.right],?_,?_⟩
  · intro i n v w
    cases i with
    | zero => simp only [ValRel,ShapeRel,Ty.subst,Valuation.extend,subst_instantiate_zero]
    | succ i => simpa only [ValRel,ShapeRel,Ty.subst,Valuation.extend,subst_instantiate_succ] using he.types i n v w
  · intro i n l v w
    cases i with
    | zero => simp only [FieldRel,Valuation.extend,subst_instantiate_zero]
    | succ i => simpa only [FieldRel,Valuation.extend,subst_instantiate_succ] using he.fields i n l v w

mutual
theorem ExprRel.environment (he : η.Equivalent ζ) (a : Typ) :
    ExprRel n a η q r ↔ ExprRel n a ζ q r := by
  rw [ExprRel,ExprRel]
  constructor
  · intro h; constructor
    · intro k hk v hv
      obtain ⟨w,hw,hr⟩ := h.1 k hk v hv
      exact ⟨w,hw,(ValRel.environment he a).mp hr⟩
    · intro k hk w hw
      obtain ⟨v,hv,hr⟩ := h.2 k hk w hw
      exact ⟨v,hv,(ValRel.environment he a).mp hr⟩
  · intro h; constructor
    · intro k hk v hv
      obtain ⟨w,hw,hr⟩ := h.1 k hk v hv
      exact ⟨w,hw,(ValRel.environment he a).mpr hr⟩
    · intro k hk w hw
      obtain ⟨v,hv,hr⟩ := h.2 k hk w hw
      exact ⟨v,hv,(ValRel.environment he a).mpr hr⟩
termination_by (n,5 * sizeOf a + 4)
decreasing_by
  all_goals by_cases hz : k = 0
  all_goals first | (subst k; apply Prod.Lex.right; omega) | (apply Prod.Lex.left; omega)

theorem ValRel.environment (he : η.Equivalent ζ) (a : Typ) :
    ValRel n a η v w ↔ ValRel n a ζ v w := by
  constructor
  · intro h
    rw [ValRel]
    exact ⟨by simpa only [← he.left] using h.left,by simpa only [← he.right] using h.right,
      (ShapeRel.environment he a h.left h.right).mp h.shape⟩
  · intro h
    have hl : ValueType .empty v (a.subst η.left) := by simpa only [he.left] using h.left
    have hr : ValueType .empty w (a.subst η.right) := by simpa only [he.right] using h.right
    rw [ValRel]
    exact ⟨hl,hr,(ShapeRel.environment he a hl hr).mpr h.shape⟩
termination_by (n,5 * sizeOf a + 3)

theorem ShapeRel.environment (he : η.Equivalent ζ) (a : Typ)
    (hl : ValueType .empty v (a.subst η.left)) (hr : ValueType .empty w (a.subst η.right)) :
    ShapeRel n a η v w ↔ ShapeRel n a ζ v w := by
  cases hcase : a with
  | unit | int | bool | string => simp only [ShapeRel]
  | tvar i =>
    rw [hcase] at hl hr
    constructor
    · intro h
      exact ((he.types i n v w).mp (by rw [ValRel]; exact ⟨hl,hr,h⟩)).shape
    · intro h
      have hl' : ValueType .empty v ((Ty.tvar i).subst ζ.left) := by simpa only [← he.left] using hl
      have hr' : ValueType .empty w ((Ty.tvar i).subst ζ.right) := by simpa only [← he.right] using hr
      exact ((he.types i n v w).mpr (by rw [ValRel]; exact ⟨hl',hr',h⟩)).shape
  | prod a b =>
    have ha := fun (x X : Expr) => ValRel.environment (n:=n) (v:=x) (w:=X) he a
    have hb := fun (x X : Expr) => ValRel.environment (n:=n) (v:=x) (w:=X) he b
    simp only [ShapeRel,ha,hb]
  | sum a b =>
    have ha := fun (x X : Expr) => ValRel.environment (n:=n) (v:=x) (w:=X) he a
    have hb := fun (x X : Expr) => ValRel.environment (n:=n) (v:=x) (w:=X) he b
    simp only [ShapeRel,ha,hb]
  | tag l a =>
    have ha := fun (x X : Expr) => ValRel.environment (n:=n) (v:=x) (w:=X) he a
    simp only [ShapeRel,ha]
  | record r => simpa only [ShapeRel] using (RowShape.environment (n:=n) (v:=v) (w:=w) he r)
  | arr a b =>
    simp only [ShapeRel]
    constructor
    · intro h j hj x X hx
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj x X ((ValRel.environment he a).mpr hx)
      exact ⟨q,r,hq,hr,(ExprRel.environment he b).mp hb⟩
    · intro h j hj x X hx
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj x X ((ValRel.environment he a).mp hx)
      exact ⟨q,r,hq,hr,(ExprRel.environment he b).mpr hb⟩
  | all k gs a =>
    simp only [ShapeRel,he.left,he.right]
    constructor
    · intro h j hj p hp hgl hgr
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj p hp hgl hgr
      exact ⟨q,r,hq,hr,(ExprRel.environment (he.extend p) a).mp hb⟩
    · intro h j hj p hp hgl hgr
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj p hp hgl hgr
      exact ⟨q,r,hq,hr,(ExprRel.environment (he.extend p) a).mpr hb⟩
  | ex k gs a =>
    have hb := fun (p : Candidate) (x X : Expr) => ValRel.environment (n:=n) (v:=x) (w:=X) (he.extend p) a
    simp only [ShapeRel,he.left,he.right,hb]
  | mu a =>
    have hb := fun j (hj : j < n) (x X : Expr) =>
      ValRel.environment (n:=j) (v:=x) (w:=X) he (a.open (.type (.mu a)))
    simp only [ShapeRel]
    constructor
    · rintro ⟨t,t',x,X,hv,hw,hx⟩
      exact ⟨t,t',x,X,hv,hw,fun j hj => (hb j hj x X).mp (hx j hj)⟩
    · rintro ⟨t,t',x,X,hv,hw,hx⟩
      exact ⟨t,t',x,X,hv,hw,fun j hj => (hb j hj x X).mpr (hx j hj)⟩
termination_by (n,5 * sizeOf a + 2)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  all_goals first | apply Prod.Lex.left; omega | apply Prod.Lex.right; omega

theorem RowShape.environment (he : η.Equivalent ζ) (r : Row) :
    RowShape n r η v w ↔ RowShape n r ζ v w := by
  have hf := fun (l : String) (x X : Expr) => FieldRel.environment (n:=n) (l:=l) (v:=x) (w:=X) he r
  simp only [RowShape,hf]
termination_by (n,5 * sizeOf r + 1)

theorem FieldRel.environment (he : η.Equivalent ζ) (r : Row) :
    FieldRel n r η l v w ↔ FieldRel n r ζ l v w := by
  cases hcase : r with
  | rvar i => exact he.fields i n l v w
  | empty => simp only [FieldRel]
  | field k a =>
    have ha := fun (x X : Expr) => ValRel.environment (n:=n) (v:=x) (w:=X) he a
    simp only [FieldRel,ha]
  | union r s =>
    have hr := fun (l : String) (x X : Expr) => FieldRel.environment (n:=n) (l:=l) (v:=x) (w:=X) he r
    have hs := fun (l : String) (x X : Expr) => FieldRel.environment (n:=n) (l:=l) (v:=x) (w:=X) he s
    simp only [FieldRel,hr,hs]
termination_by (n,5 * sizeOf r)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals omega
end

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Substitution -/

section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace LeanSce.Target.Heterogeneous

/-- Interpret a simultaneous syntactic substitution as a substitution of
    semantic type and finite-map row candidates. -/
def Valuation.substitute (η : Valuation) (σ : Subst) : Valuation where
  left := fun k i => (σ k i).subst η.left
  right := fun k i => (σ k i).subst η.right
  types := fun i => (η.typeCandidate (σ .type i)).typeRelation
  fields := fun i => (η.rowCandidate (σ .row i)).fieldRelation

theorem FieldRel.weaken (r : Row) (η : Valuation) (p : Candidate) :
    FieldRel n (r.rename Nat.succ) (η.extend p) l v w ↔ FieldRel n r η l v w := by
  simpa only [Valuation.reindex_extend_succ] using FieldRel.rename r Nat.succ (η.extend p)

theorem Valuation.substitute_lift (η : Valuation) (σ : Subst) (p : Candidate) :
    ((η.extend p).substitute σ.lift).Equivalent ((η.substitute σ).extend p) := by
  refine ⟨?_,?_,?_,?_⟩
  · funext k i
    cases i <;> simp [Valuation.substitute,Valuation.extend,Subst.lift,Ty.subst_var,Ty.subst_instantiate_weaken]
  · funext k i
    cases i <;> simp [Valuation.substitute,Valuation.extend,Subst.lift,Ty.subst_var,Ty.subst_instantiate_weaken]
  · intro i n v w
    cases i with
    | zero =>
      simp [ValRel,ShapeRel,Ty.subst,Valuation.substitute,Valuation.typeCandidate,
        Valuation.extend,Subst.lift,Ty.var]
      intro hv hw
      simp [hv,hw]
    | succ i =>
      simp only [ValRel,ShapeRel,Ty.subst,Valuation.substitute,Valuation.typeCandidate,
        Valuation.extend,Subst.lift,Ty.subst_instantiate_weaken,
        subst_instantiate_succ]
      have hs := ValRel.weaken (n:=n) (v:=v) (w:=w) (σ .type i) η p
      simp only [ValRel,Valuation.extend,Ty.subst_instantiate_weaken] at hs
      exact and_congr Iff.rfl (and_congr Iff.rfl hs)
  · intro i n l v w
    cases i with
    | zero =>
      simp [FieldRel,Ty.subst,Valuation.substitute,Valuation.rowCandidate,
        Valuation.extend,Subst.lift,Ty.var]
      intro hl hr
      simp [hl,hr]
    | succ i =>
      simp only [FieldRel,Valuation.substitute,Valuation.rowCandidate,
        Valuation.extend,Subst.lift,Ty.subst_instantiate_weaken,
        subst_instantiate_succ]
      exact and_congr Iff.rfl (and_congr Iff.rfl (FieldRel.weaken _ η p))

theorem subst_subst_lift (a : Ty s) (σ θ : Subst) :
    (a.subst σ.lift).subst θ.lift =
      a.subst (Subst.lift (fun k i => (σ k i).subst θ)) := by
  rw [Ty.subst_comp,← Subst.lift_comp]

mutual
theorem ExprRel.substitution (a : Typ) (σ : Subst) (η : Valuation) :
    ExprRel n (a.subst σ) η q r ↔ ExprRel n a (η.substitute σ) q r := by
  rw [ExprRel,ExprRel]
  constructor
  · intro h; constructor
    · intro k hk v hv
      obtain ⟨w,hw,hr⟩ := h.1 k hk v hv
      exact ⟨w,hw,(ValRel.substitution a σ η).mp hr⟩
    · intro k hk w hw
      obtain ⟨v,hv,hr⟩ := h.2 k hk w hw
      exact ⟨v,hv,(ValRel.substitution a σ η).mp hr⟩
  · intro h; constructor
    · intro k hk v hv
      obtain ⟨w,hw,hr⟩ := h.1 k hk v hv
      exact ⟨w,hw,(ValRel.substitution a σ η).mpr hr⟩
    · intro k hk w hw
      obtain ⟨v,hv,hr⟩ := h.2 k hk w hw
      exact ⟨v,hv,(ValRel.substitution a σ η).mpr hr⟩
termination_by (n,5 * sizeOf a + 4)
decreasing_by
  all_goals by_cases hz : k = 0
  all_goals first | (subst k; apply Prod.Lex.right; omega) | (apply Prod.Lex.left; omega)

theorem ValRel.substitution (a : Typ) (σ : Subst) (η : Valuation) :
    ValRel n (a.subst σ) η v w ↔ ValRel n a (η.substitute σ) v w := by
  constructor
  · intro h
    rw [ValRel]
    exact ⟨by simpa only [Valuation.substitute,Ty.subst_comp] using h.left,
      by simpa only [Valuation.substitute,Ty.subst_comp] using h.right,
      (ShapeRel.substitution a σ η h.left h.right).mp h.shape⟩
  · intro h
    have hl : ValueType .empty v ((a.subst σ).subst η.left) := by
      simpa only [Valuation.substitute,Ty.subst_comp] using h.left
    have hr : ValueType .empty w ((a.subst σ).subst η.right) := by
      simpa only [Valuation.substitute,Ty.subst_comp] using h.right
    rw [ValRel]
    exact ⟨hl,hr,(ShapeRel.substitution a σ η hl hr).mpr h.shape⟩
termination_by (n,5 * sizeOf a + 3)

theorem ShapeRel.substitution (a : Typ) (σ : Subst) (η : Valuation)
    (hl : ValueType .empty v ((a.subst σ).subst η.left))
    (hr : ValueType .empty w ((a.subst σ).subst η.right)) :
    ShapeRel n (a.subst σ) η v w ↔ ShapeRel n a (η.substitute σ) v w := by
  cases hcase : a with
  | unit | int | bool | string => simp only [Ty.subst,ShapeRel]
  | tvar i =>
    rw [hcase] at hl hr
    simp only [Ty.subst,ShapeRel,Valuation.substitute,Valuation.typeCandidate]
    exact ⟨fun h => by rw [ValRel]; exact ⟨hl,hr,h⟩,fun h => h.shape⟩
  | prod a b =>
    have ha := fun (x X : Expr) => ValRel.substitution (n:=n) (v:=x) (w:=X) a σ η
    have hb := fun (x X : Expr) => ValRel.substitution (n:=n) (v:=x) (w:=X) b σ η
    simp only [Ty.subst,ShapeRel,ha,hb]
  | sum a b =>
    have ha := fun (x X : Expr) => ValRel.substitution (n:=n) (v:=x) (w:=X) a σ η
    have hb := fun (x X : Expr) => ValRel.substitution (n:=n) (v:=x) (w:=X) b σ η
    simp only [Ty.subst,ShapeRel,ha,hb]
  | tag l a =>
    have ha := fun (x X : Expr) => ValRel.substitution (n:=n) (v:=x) (w:=X) a σ η
    simp only [Ty.subst,ShapeRel,ha]
  | record r => simpa only [Ty.subst,ShapeRel] using (RowShape.substitution (n:=n) (v:=v) (w:=w) r σ η)
  | arr a b =>
    simp only [Ty.subst,ShapeRel]
    constructor
    · intro h j hj x X hx
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj x X ((ValRel.substitution a σ η).mpr hx)
      exact ⟨q,r,hq,hr,(ExprRel.substitution b σ η).mp hb⟩
    · intro h j hj x X hx
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj x X ((ValRel.substitution a σ η).mp hx)
      exact ⟨q,r,hq,hr,(ExprRel.substitution b σ η).mpr hb⟩
  | all k gs a =>
    simp only [Ty.subst,ShapeRel,subst_subst_lift]
    constructor
    · intro h j hj p hp hgl hgr
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj p hp hgl hgr
      exact ⟨q,r,hq,hr,(ExprRel.environment (η.substitute_lift σ p) a).mp
        ((ExprRel.substitution a σ.lift (η.extend p)).mp hb)⟩
    · intro h j hj p hp hgl hgr
      obtain ⟨q,r,hq,hr,hb⟩ := h j hj p hp hgl hgr
      exact ⟨q,r,hq,hr,(ExprRel.substitution a σ.lift (η.extend p)).mpr
        ((ExprRel.environment (η.substitute_lift σ p) a).mpr hb)⟩
  | ex k gs a =>
    simp only [Ty.subst,ShapeRel,subst_subst_lift]
    constructor
    · rintro ⟨p,t,t',x,X,hv,hw,hp,hgl,hgr,hb⟩
      exact ⟨p,t,t',x,X,hv,hw,hp,hgl,hgr,(ValRel.environment (η.substitute_lift σ p) a).mp
        ((ValRel.substitution a σ.lift (η.extend p)).mp hb)⟩
    · rintro ⟨p,t,t',x,X,hv,hw,hp,hgl,hgr,hb⟩
      exact ⟨p,t,t',x,X,hv,hw,hp,hgl,hgr,(ValRel.substitution a σ.lift (η.extend p)).mpr
        ((ValRel.environment (η.substitute_lift σ p) a).mpr hb)⟩
  | mu a =>
    simp only [Ty.subst,ShapeRel]
    constructor
    · rintro ⟨t,t',x,X,hv,hw,hb⟩
      refine ⟨t,t',x,X,hv,hw,fun j hj => ?_⟩
      apply (ValRel.substitution (a.open (.type (.mu a))) σ η).mp
      simpa only [Ty.subst_open,Arg.subst,Ty.subst] using hb j hj
    · rintro ⟨t,t',x,X,hv,hw,hb⟩
      refine ⟨t,t',x,X,hv,hw,fun j hj => ?_⟩
      have hh := (ValRel.substitution (a.open (.type (.mu a))) σ η).mpr (hb j hj)
      simpa only [Ty.subst_open,Arg.subst,Ty.subst] using hh
termination_by (n,5 * sizeOf a + 2)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  all_goals first | apply Prod.Lex.left; omega | apply Prod.Lex.right; omega

theorem RowShape.substitution (r : Row) (σ : Subst) (η : Valuation) :
    RowShape n (r.subst σ) η v w ↔ RowShape n r (η.substitute σ) v w := by
  have hf := fun (l : String) (x X : Expr) => FieldRel.substitution (n:=n) (l:=l) (v:=x) (w:=X) r σ η
  simp only [RowShape,hf]
termination_by (n,5 * sizeOf r + 1)

theorem FieldRel.substitution (r : Row) (σ : Subst) (η : Valuation) :
    FieldRel n (r.subst σ) η l v w ↔ FieldRel n r (η.substitute σ) l v w := by
  cases hcase : r with
  | rvar i =>
    simp only [Ty.subst,FieldRel,Valuation.substitute,Valuation.rowCandidate]
    exact ⟨fun h => ⟨h.domain.1,h.domain.2,h⟩,fun h => h.2.2⟩
  | empty => simp only [Ty.subst,FieldRel]
  | field k a =>
    have ha := fun (x X : Expr) => ValRel.substitution (n:=n) (v:=x) (w:=X) a σ η
    simp only [Ty.subst,FieldRel,ha]
  | union r s =>
    have hr := fun (l : String) (x X : Expr) => FieldRel.substitution (n:=n) (l:=l) (v:=x) (w:=X) r σ η
    have hs := fun (l : String) (x X : Expr) => FieldRel.substitution (n:=n) (l:=l) (v:=x) (w:=X) s σ η
    simp only [Ty.subst,FieldRel,hr,hs]
termination_by (n,5 * sizeOf r)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals omega
end

end LeanSce.Target.Heterogeneous

end

/-! ## Heterogeneous Static -/

namespace LeanSce.Target.Heterogeneous

theorem Candidate.type_typed {p : Candidate} (hp : p.Admissible .type) :
    TypedRelation p.typeRelation (p.left.openSubst .type 0) (p.right.openSubst .type 0) := by
  rcases p with ⟨left,right,rt,rf⟩
  cases left <;> cases right <;> simp [Candidate.Admissible,Arg.kind] at hp
  exact hp.2.2

theorem Candidate.row_typed {p : Candidate} (hp : p.Admissible .row) :
    (p.left.openSubst .row 0).knownLabels.Perm (p.right.openSubst .row 0).knownLabels ∧
    ∀ l a b, (p.left.openSubst .row 0).lookup l = some a →
      (p.right.openSubst .row 0).lookup l = some b → TypedRelation (p.fieldRelation l) a b := by
  rcases p with ⟨left,right,rt,rf⟩
  cases left <;> cases right <;> simp [Candidate.Admissible,Arg.kind] at hp
  exact hp.2.2

theorem Valuation.Valid.extend {η : Valuation} (hη : η.Valid Δ)
    (hf : FreshGuards k gs) (hp : p.Admissible k)
    (hgl : Entails .empty ((gs.subst η.left.lift).open p.left))
    (hgr : Entails .empty ((gs.subst η.right.lift).open p.right)) :
    (η.extend p).Valid (Δ.extend k gs) := by
  refine ⟨hη.1.instantiate hf hp.1 hp.2.2.1 hgl,
    hη.2.1.instantiate hf hp.2.1 hp.2.2.2.1 hgr,?_,?_⟩
  · intro i hi
    cases i with
    | zero =>
      have hk : k = .type := by simpa [Context.extend] using hi
      subst k
      simpa [Valuation.extend] using Candidate.type_typed hp
    | succ i =>
      have hi' : Δ.kinds[i]? = some .type := by simpa [Context.extend] using hi
      simpa [Valuation.extend] using hη.2.2.1 i hi'
  · intro i hi
    cases i with
    | zero =>
      have hk : k = .row := by simpa [Context.extend] using hi
      subst k
      simpa [Valuation.extend] using Candidate.row_typed hp
    | succ i =>
      have hi' : Δ.kinds[i]? = some .row := by simpa [Context.extend] using hi
      simpa [Valuation.extend] using hη.2.2.2 i hi'

def Valuation.argument (η : Valuation) : Arg → Candidate
  | .type a => η.typeCandidate a
  | .row r => η.rowCandidate r

@[simp] theorem Valuation.argument_left (η : Valuation) (u : Arg) :
    (η.argument u).left = u.subst η.left := by cases u <;> rfl

@[simp] theorem Valuation.argument_right (η : Valuation) (u : Arg) :
    (η.argument u).right = u.subst η.right := by cases u <;> rfl

theorem Valuation.argument_admissible {η : Valuation} (hη : η.Valid Δ) (hu : u.WellFormed Δ) :
    (η.argument u).Admissible u.kind := by
  cases u with
  | type a => exact η.typeCandidate_admissible (hu.subst hη.1.respects) (hu.subst hη.2.1.respects)
  | row r => exact Valuation.rowCandidate_admissible hη hu

theorem Valuation.Valid.substitute {η : Valuation} (hη : η.Valid Δ) (hσ : Subst.Respects Γ Δ σ) :
    (η.substitute σ).Valid Γ := by
  refine ⟨Closing.of_respects (hσ.comp hη.1.respects),Closing.of_respects (hσ.comp hη.2.1.respects),?_,?_⟩
  · intro i hi n v w h
    exact ⟨h.left,h.right⟩
  · intro i hi
    exact (Valuation.rowCandidate_admissible hη (hσ.1 .row i hi)).2.2.2.2

/-- Semantic opening chooses the interpretation of the actual source witness.
    The two resulting closed witnesses may have unrelated implementations. -/
theorem Valuation.open_argument (η : Valuation) (u : Arg) :
    (η.substitute u.openSubst).Equivalent (η.extend (η.argument u)) := by
  refine ⟨?_,?_,?_,?_⟩
  · funext k i
    cases i with
    | zero => cases u <;> cases k <;> simp [Valuation.substitute,Valuation.extend,Valuation.argument,
        Valuation.typeCandidate,Valuation.rowCandidate,Arg.openSubst,Ty.subst]
    | succ i => simp [Valuation.substitute,Valuation.extend,Arg.openSubst,Ty.subst_var]
  · funext k i
    cases i with
    | zero => cases u <;> cases k <;> simp [Valuation.substitute,Valuation.extend,Valuation.argument,
        Valuation.typeCandidate,Valuation.rowCandidate,Arg.openSubst,Ty.subst]
    | succ i => simp [Valuation.substitute,Valuation.extend,Arg.openSubst,Ty.subst_var]
  · intro i n v w
    cases i with
    | zero =>
      cases u <;> simp only [ValRel,ShapeRel,Ty.subst,Valuation.substitute,Valuation.extend,
        Valuation.argument,Valuation.typeCandidate,Valuation.rowCandidate,subst_instantiate_zero,Arg.openSubst]
    | succ i =>
      simp only [ValRel,ShapeRel,Ty.subst,Valuation.substitute,Valuation.extend,
        Valuation.typeCandidate,subst_instantiate_succ,Arg.openSubst,Ty.var]
      constructor
      · intro h; exact ⟨h.1,h.2.1,h.2.2.2.2⟩
      · intro h; exact ⟨h.1,h.2.1,h⟩
  · intro i n l v w
    cases i with
    | zero =>
      cases u <;> simp only [FieldRel,Ty.subst,Valuation.substitute,Valuation.extend,
        Valuation.argument,Valuation.typeCandidate,Valuation.rowCandidate,subst_instantiate_zero,
        Arg.openSubst,Ty.knownLabels,List.not_mem_nil,false_and,IndexedRelation.empty]
    | succ i =>
      simp only [FieldRel,Ty.subst,Valuation.substitute,Valuation.extend,
        Valuation.rowCandidate,subst_instantiate_succ,Arg.openSubst,Ty.var]
      constructor
      · intro h; exact ⟨h.1,h.2.1,h.2.2.2.2⟩
      · intro h; exact ⟨h.1,h.2.1,h⟩

theorem ValRel.opening (a : Typ) (u : Arg) (η : Valuation) :
    ValRel n (a.open u) η v w ↔ ValRel n a (η.extend (η.argument u)) v w :=
  (ValRel.substitution a u.openSubst η).trans (ValRel.environment (η.open_argument u) a)

theorem ExprRel.opening (a : Typ) (u : Arg) (η : Valuation) :
    ExprRel n (a.open u) η q r ↔ ExprRel n a (η.extend (η.argument u)) q r :=
  (ExprRel.substitution a u.openSubst η).trans (ExprRel.environment (η.open_argument u) a)

end LeanSce.Target.Heterogeneous

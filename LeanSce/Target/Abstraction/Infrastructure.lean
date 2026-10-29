import LeanSce.Target.Abstraction.Definitions
import LeanSce.Target.LogicalRelation.Contexts
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Abstraction / Infrastructure

Proofs and supporting constructions for infrastructure.
-/

/-! ## Heterogeneous Properties -/

namespace LeanSce.Target.Heterogeneous

mutual
theorem ValRel.mono (h : ValRel n a η v w) (hm : m ≤ n) : ValRel m a η v w := by
  rw [ValRel] at h ⊢
  exact ⟨h.1,h.2.1,h.2.2.mono hm⟩
termination_by 4 * sizeOf a + 3

theorem ShapeRel.mono (h : ShapeRel n a η v w) (hm : m ≤ n) : ShapeRel m a η v w := by
  cases a with
  | unit | int | bool | string => rw [ShapeRel] at h ⊢; exact h
  | tvar i => rw [ShapeRel] at h ⊢; exact (η.types i).mono hm h
  | prod a b =>
    rw [ShapeRel] at h ⊢
    obtain ⟨x,y,X,Y,hv,hw,hx,hy⟩ := h
    exact ⟨x,y,X,Y,hv,hw,hx.mono hm,hy.mono hm⟩
  | sum a b =>
    rw [ShapeRel] at h ⊢
    rcases h with ⟨t,t',x,X,hv,hw,hx⟩ | ⟨t,t',y,Y,hv,hw,hy⟩
    · exact .inl ⟨t,t',x,X,hv,hw,hx.mono hm⟩
    · exact .inr ⟨t,t',y,Y,hv,hw,hy.mono hm⟩
  | tag l a =>
    rw [ShapeRel] at h ⊢
    obtain ⟨x,X,hv,hw,hx⟩ := h
    exact ⟨x,X,hv,hw,hx.mono hm⟩
  | record r => rw [ShapeRel] at h ⊢; exact RowShape.mono h hm
  | arr a b =>
    rw [ShapeRel] at h ⊢
    intro j hj x X hx
    exact h j (Nat.lt_of_lt_of_le hj hm) x X hx
  | all k gs a =>
    rw [ShapeRel] at h ⊢
    intro j hj p hp hl hr
    exact h j (Nat.lt_of_lt_of_le hj hm) p hp hl hr
  | ex k gs a =>
    rw [ShapeRel] at h ⊢
    obtain ⟨p,t,t',x,X,hv,hw,hp,hl,hr,hx⟩ := h
    exact ⟨p,t,t',x,X,hv,hw,hp,hl,hr,hx.mono hm⟩
  | mu a =>
    rw [ShapeRel] at h ⊢
    obtain ⟨t,t',x,X,hv,hw,hx⟩ := h
    exact ⟨t,t',x,X,hv,hw,fun j hj => hx j (Nat.lt_of_lt_of_le hj hm)⟩
termination_by 4 * sizeOf a + 2

theorem RowShape.mono (h : RowShape n r η v w) (hm : m ≤ n) : RowShape m r η v w := by
  rw [RowShape] at h ⊢
  obtain ⟨fs,gs,hv,hw,hp,hf⟩ := h
  exact ⟨fs,gs,hv,hw,hp,fun l x X hl hr => (hf l x X hl hr).mono hm⟩
termination_by 4 * sizeOf r + 1

theorem FieldRel.mono (h : FieldRel n r η l v w) (hm : m ≤ n) : FieldRel m r η l v w := by
  cases r with
  | rvar i => rw [FieldRel] at h ⊢; exact ⟨h.1,h.2.1,(η.fields i l).mono hm h.2.2⟩
  | empty => rw [FieldRel] at h ⊢; exact h
  | field k a => rw [FieldRel] at h ⊢; exact ⟨h.1,h.2.mono hm⟩
  | union r s => rw [FieldRel] at h ⊢; exact h.elim (fun hr => .inl (hr.mono hm)) (fun hs => .inr (hs.mono hm))
termination_by 4 * sizeOf r
end

theorem ExprRel.mono (h : ExprRel n a η q r) (hm : m ≤ n) : ExprRel m a η q r := by
  rw [ExprRel] at h ⊢
  constructor
  · intro k hk v hv
    obtain ⟨w,hw,hr⟩ := h.1 k (Nat.lt_of_lt_of_le hk hm) v hv
    exact ⟨w,hw,hr.mono (Nat.sub_le_sub_right hm k)⟩
  · intro k hk w hw
    obtain ⟨v,hv,hr⟩ := h.2 k (Nat.lt_of_lt_of_le hk hm) w hw
    exact ⟨v,hv,hr.mono (Nat.sub_le_sub_right hm k)⟩

theorem ValRel.left (h : ValRel n a η v w) : ValueType .empty v (a.subst η.left) := by
  rw [ValRel] at h; exact h.1

theorem ValRel.right (h : ValRel n a η v w) : ValueType .empty w (a.subst η.right) := by
  rw [ValRel] at h; exact h.2.1

theorem ValRel.shape (h : ValRel n a η v w) : ShapeRel n a η v w := by
  rw [ValRel] at h; exact h.2.2

/-- Any interpreted type supplies an admissible type candidate once its two
    closed witness types are well formed. -/
def Valuation.typeCandidate (η : Valuation) (a : Typ) : Candidate where
  left := .type (a.subst η.left)
  right := .type (a.subst η.right)
  typeRelation := ⟨fun n v w => ValRel n a η v w,fun hm h => h.mono hm⟩
  fieldRelation := fun _ => IndexedRelation.empty

theorem Valuation.typeCandidate_admissible (η : Valuation)
    (wl : WellFormed .empty (a.subst η.left)) (wr : WellFormed .empty (a.subst η.right)) :
    (η.typeCandidate a).Admissible .type := by
  exact ⟨rfl,rfl,wl,wr,fun _ _ _ h => ⟨h.left,h.right⟩⟩

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Evaluation -/

namespace LeanSce.Target.Heterogeneous

theorem ExprRel.zero : ExprRel 0 a η q r := by
  rw [ExprRel]
  exact ⟨by intros; omega,by intros; omega⟩

theorem ValRel.toExpr (hr : ValRel n a η v w) : ExprRel n a η (ν,v) (N,w) := by
  rw [ExprRel]
  have hv := (show ValueType .empty v (a.subst η.left) from (by rw [ValRel] at hr; exact hr.1)).1
  have hw := (show ValueType .empty w (a.subst η.right) from (by rw [ValRel] at hr; exact hr.2.1)).1
  constructor
  · intro k hk v' ht
    obtain ⟨rfl,rfl⟩ := ht.1.value_inv hv
    exact ⟨w,⟨.refl,hw⟩,by simpa using hr⟩
  · intro k hk w' ht
    obtain ⟨rfl,rfl⟩ := ht.1.value_inv hw
    exact ⟨v,⟨.refl,hv⟩,by simpa using hr⟩

/-- A strict computation can be replaced by related computations inside a pair
    of strict frames. The tested computation pays exactly its own prefix cost. -/
theorem ExprRel.bind (he : ExprRel n a η (ν,e) (N,E))
    (hc : StrictFrame ν C) (hd : StrictFrame N D)
    (hk : ∀ i, i < n → ∀ v V, ValRel (n-i) a η v V →
      ExprRel (n-i) b ζ (ν,C v) (N,D V)) : ExprRel n b ζ (ν,C e) (N,D E) := by
  rw [ExprRel] at he ⊢
  constructor
  · intro k hkn w hw
    obtain ⟨v,i,j,hkij,hv,hrest⟩ := hc.decompose_counted hw
    have hin : i < n := by omega
    obtain ⟨V,hV,hrel⟩ := he.1 i hin v hv
    have hcont := hk i hin v V hrel
    rw [ExprRel] at hcont
    obtain ⟨W,hW,hout⟩ := hcont.1 j (by omega) w hrest
    exact ⟨W,hd.terminates hV hW,by simpa [Nat.sub_sub,hkij] using hout⟩
  · intro k hkn W hW
    obtain ⟨V,i,j,hkij,hV,hrest⟩ := hd.decompose_counted hW
    have hin : i < n := by omega
    obtain ⟨v,hv,hrel⟩ := he.2 i hin V hV
    have hcont := hk i hin v V hrel
    rw [ExprRel] at hcont
    obtain ⟨w,hw,hout⟩ := hcont.2 j (by omega) W hrest
    exact ⟨w,hc.terminates hv hw,by simpa [Nat.sub_sub,hkij] using hout⟩

/-- Matching administrative steps consume one unit before testing their bodies. -/
theorem ExprRel.step (hl : Step ν e e') (hr : Step N E E')
    (hb : ExprRel n a η (ν,e') (N,E')) : ExprRel (n+1) a η (ν,e) (N,E) := by
  rw [ExprRel] at hb ⊢
  constructor
  · intro k hk v hv
    cases hv.1 with
    | refl => exact False.elim (value_irreducible hv.2 hl)
    | @next e e₁ k v hs htail =>
      have heq := step_deterministic hs hl
      subst e₁
      obtain ⟨w,hw,hout⟩ := hb.1 k (by omega) v ⟨htail,hv.2⟩
      exact ⟨w,⟨.next hr hw.1,hw.2⟩,by simpa using hout⟩
  · intro k hk w hw
    cases hw.1 with
    | refl => exact False.elim (value_irreducible hw.2 hr)
    | @next E E₁ k w hs htail =>
      have heq := step_deterministic hs hr
      subst E₁
      obtain ⟨v,hv,hout⟩ := hb.2 k (by omega) w ⟨htail,hw.2⟩
      exact ⟨v,⟨.next hl hv.1,hv.2⟩,by simpa using hout⟩

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Rows -/

namespace LeanSce.Target.Heterogeneous

theorem FieldRel.domain (h : FieldRel n r η l v w) :
    l ∈ (r.subst η.left).knownLabels ∧ l ∈ (r.subst η.right).knownLabels := by
  cases r with
  | rvar i => rw [FieldRel] at h; exact ⟨h.1,h.2.1⟩
  | empty => rw [FieldRel] at h; exact False.elim h
  | field k a =>
    rw [FieldRel] at h
    have hl := h.1
    simp only [Ty.subst,Ty.knownLabels,List.mem_singleton]
    exact ⟨hl,hl⟩
  | union r s =>
    simp only [Ty.subst,Ty.knownLabels]
    rw [FieldRel] at h
    rcases h with hr | hs
    · obtain ⟨hl,hR⟩ := hr.domain
      exact ⟨List.mem_append_left _ hl,List.mem_append_left _ hR⟩
    · obtain ⟨hl,hR⟩ := hs.domain
      exact ⟨List.mem_append_right _ hl,List.mem_append_right _ hR⟩

termination_by sizeOf r

theorem FieldRel.typed (h : FieldRel n r η l v w) (wr : WellFormed Δ r)
    (hη : η.Valid Δ) (hl : (r.subst η.left).lookup l = some a)
    (hr : (r.subst η.right).lookup l = some b) :
    ValueType .empty v a ∧ ValueType .empty w b := by
  cases wr with
  | rvar hi => rw [FieldRel] at h; exact hη.2.2.2 _ hi |>.2 l a b hl hr n v w h.2.2
  | empty => rw [FieldRel] at h; exact False.elim h
  | field wa =>
    rw [FieldRel] at h
    obtain ⟨rfl,hv⟩ := h
    have hea : _ = a := Option.some.inj (by simpa [Ty.subst,Ty.lookup] using hl)
    have heb : _ = b := Option.some.inj (by simpa [Ty.subst,Ty.lookup] using hr)
    exact ⟨by simpa only [hea] using hv.left,by simpa only [heb] using hv.right⟩
  | @union _ r s wr ws hd =>
    rw [FieldRel] at h
    rcases h with h | h
    · obtain ⟨A,hA⟩ := Ty.mem_lookup (r.subst η.left) h.domain.1
      obtain ⟨B,hB⟩ := Ty.mem_lookup (r.subst η.right) h.domain.2
      have hea : A = a := Option.some.inj (by simpa [Ty.subst,hA] using hl)
      have heb : B = b := Option.some.inj (by simpa [Ty.subst,hB] using hr)
      subst A; subst B
      exact h.typed wr hη hA hB
    · have hnone : (r.subst η.left).lookup l = none := by
        cases he : (r.subst η.left).lookup l with
        | none => rfl
        | some z => exact False.elim ((hd.subst hη.1.respects).knownLabels l
            (Ty.lookup_mem _ he) h.domain.1)
      have hNone : (r.subst η.right).lookup l = none := by
        cases he : (r.subst η.right).lookup l with
        | none => rfl
        | some z => exact False.elim ((hd.subst hη.2.1.respects).knownLabels l
            (Ty.lookup_mem _ he) h.domain.2)
      exact h.typed ws hη (by simpa [Ty.subst,hnone] using hl) (by simpa [Ty.subst,hNone] using hr)

termination_by sizeOf r

theorem Valuation.row_domains {η : Valuation} (hη : η.Valid Δ) (wr : WellFormed Δ r) :
    (r.subst η.left).knownLabels.Perm (r.subst η.right).knownLabels := by
  cases wr with
  | rvar hi => exact (hη.2.2.2 _ hi).1
  | empty => exact .refl _
  | field => simp [Ty.subst,Ty.knownLabels]
  | union wr ws _ => simpa only [Ty.subst,Ty.knownLabels] using
      (Valuation.row_domains hη wr).append (Valuation.row_domains hη ws)

termination_by sizeOf r

/-- Interpretation of a row witness is its finite map of field candidates. -/
def Valuation.rowCandidate (η : Valuation) (r : Row) : Candidate where
  left := .row (r.subst η.left)
  right := .row (r.subst η.right)
  typeRelation := ⟨fun n v w => ValRel n .unit η v w,fun hm h => h.mono hm⟩
  fieldRelation := fun l => ⟨fun n v w => FieldRel n r η l v w,fun hm h => h.mono hm⟩

theorem Valuation.rowCandidate_admissible {η : Valuation} (hη : η.Valid Δ) (wr : WellFormed Δ r) :
    (η.rowCandidate r).Admissible .row := by
  refine ⟨rfl,rfl,wr.subst hη.1.respects,wr.subst hη.2.1.respects,Valuation.row_domains hη wr,?_⟩
  intro l a b hl hr n v w h
  exact h.typed wr hη hl hr

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Packages -/

namespace LeanSce.Target.Heterogeneous

/-- The empty semantic environment imposes no relation on undeclared names. -/
def Valuation.empty : Valuation where
  left := Subst.id
  right := Subst.id
  types := fun _ => IndexedRelation.empty
  fields := fun _ _ => IndexedRelation.empty

theorem Valuation.empty_valid : Valuation.empty.Valid Context.empty := by
  refine ⟨Closing.empty _,Closing.empty _,?_,?_⟩
  · intro i hi; simp [Context.empty] at hi
  · intro i hi; simp [Context.empty] at hi

/-- An arbitrary downward-closed typed relation is a legal hidden-type
    representation candidate; no equivalence or simulation law is required. -/
def Candidate.type (a b : Typ) (r : IndexedRelation) : Candidate where
  left := .type a
  right := .type b
  typeRelation := r
  fieldRelation := fun _ => IndexedRelation.empty

theorem Candidate.type_admissible (wa : WellFormed .empty a) (wb : WellFormed .empty b)
    (hr : TypedRelation r a b) : (Candidate.type a b r).Admissible .type :=
  ⟨rfl,rfl,wa,wb,hr⟩

/-- The existential clause directly hides two different witnesses behind the
    same public interface, at the unchanged payload index. -/
theorem ValRel.pack
    (hl : ValueType .empty (.pack p.left (.ex k gs a) v) ((Ty.ex k gs a).subst η.left))
    (hr : ValueType .empty (.pack p.right (.ex k gs a) V) ((Ty.ex k gs a).subst η.right))
    (hp : p.Admissible k)
    (hgl : Entails .empty ((gs.subst η.left.lift).open p.left))
    (hgr : Entails .empty ((gs.subst η.right.lift).open p.right))
    (hv : ValRel n a (η.extend p) v V) :
    ValRel n (.ex k gs a) η
      (.pack p.left (.ex k gs a) v) (.pack p.right (.ex k gs a) V) := by
  rw [ValRel,ShapeRel]
  exact ⟨hl,hr,p,_,_,v,V,rfl,rfl,hp,hgl,hgr,hv⟩

/-- The exact logical premise of representation independence gives all-index
    relatedness of the public packages, without identifying the witnesses. -/
theorem packages_related
    (p : Candidate) (hp : p.Admissible .type)
    (hl : ValueType .empty (.pack p.left (.ex .type .gnil a) v) (.ex .type .gnil a))
    (hr : ValueType .empty (.pack p.right (.ex .type .gnil a) V) (.ex .type .gnil a))
    (hv : ∀ n, ValRel n a (Valuation.empty.extend p) v V) :
    ∀ n, ValRel n (.ex .type .gnil a) Valuation.empty
      (.pack p.left (.ex .type .gnil a) v) (.pack p.right (.ex .type .gnil a) V) := by
  intro n
  apply ValRel.pack (η := Valuation.empty)
  · simpa only [Valuation.empty,Ty.subst_id] using hl
  · simpa only [Valuation.empty,Ty.subst_id] using hr
  · exact hp
  · simp [Ty.subst,Ty.open,Ty.guardAtoms,Entails]
  · simp [Ty.subst,Ty.open,Ty.guardAtoms,Entails]
  · exact hv n

end LeanSce.Target.Heterogeneous

/-! ## Representation Independence Statement -/

namespace LeanSce.Target.Goals
open Heterogeneous

/-- T3, with exactly an arbitrary downward-closed typed representation relation
    between the two hidden closed type witnesses and all-index related payloads.
    The conclusion uses every typed target ground observation context. -/
def RepresentationIndependence : Prop :=
  ∀ (body A₁ A₂ : Typ) (v₁ v₂ : Expr) (R : IndexedRelation),
    WellFormed .empty A₁ → WellFormed .empty A₂ →
    WellFormed .empty (.ex .type .gnil body) → TypedRelation R A₁ A₂ →
    ValueType .empty (.pack (.type A₁) (.ex .type .gnil body) v₁) (.ex .type .gnil body) →
    ValueType .empty (.pack (.type A₂) (.ex .type .gnil body) v₂) (.ex .type .gnil body) →
    (∀ n, ValRel n body (Valuation.empty.extend (Candidate.type A₁ A₂ R)) v₁ v₂) →
    ContextualEq .empty .unit (.ex .type .gnil body)
      (.pack (.type A₁) (.ex .type .gnil body) v₁)
      (.pack (.type A₂) (.ex .type .gnil body) v₂)

end LeanSce.Target.Goals

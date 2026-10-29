import LeanSce.Target.Abstraction.Infrastructure
import LeanSce.Target.Abstraction.Substitution
import LeanSce.Target.Adapters.Naturality
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Abstraction / Equality

Proofs and supporting constructions for equality.
-/

/-! ## Heterogeneous Row Decomposition -/

namespace LeanSce.Target.Heterogeneous

/-- Row interpretation consists of its statically named payload relations and
    its opaque summands, independent of the syntax of associative row unions. -/
theorem FieldRel.decompose (r : Row) :
    FieldRel n r η l v w ↔
      (∃ a, (l,a) ∈ r.knownFields ∧ ValRel n a η v w) ∨
      (∃ i, i ∈ r.tails ∧ FieldRel n (.rvar i) η l v w) := by
  cases r with
  | empty => simp [FieldRel,Ty.knownFields,Ty.tails]
  | rvar i => simp [Ty.knownFields,Ty.tails]
  | field k a =>
    simp only [FieldRel,Ty.knownFields,Ty.tails,List.mem_singleton,Prod.mk.injEq,List.not_mem_nil,false_and,exists_false,or_false]
    constructor
    · intro h; exact ⟨a,⟨h.1,rfl⟩,h.2⟩
    · rintro ⟨_,⟨hl,rfl⟩,h⟩; exact ⟨hl,h⟩
  | union r s =>
    rw [FieldRel,FieldRel.decompose r,FieldRel.decompose s]
    simp only [Ty.knownFields,Ty.tails,List.mem_append,or_and_right,exists_or]
    simp only [or_assoc,or_left_comm,or_comm]
termination_by sizeOf r

theorem FieldRel.map (h : FieldRel n r η l v w)
    (ht : r.tails.Perm s.tails)
    (hf : ∀ a, (l,a) ∈ r.knownFields → ValRel n a η v w →
      ∃ b, (l,b) ∈ s.knownFields ∧ ValRel n b η v w) : FieldRel n s η l v w := by
  rw [FieldRel.decompose] at h ⊢
  rcases h with ⟨a,ha,hv⟩ | ⟨i,hi,hv⟩
  · exact .inl (hf a ha hv)
  · exact .inr ⟨i,ht.mem_iff.mp hi,hv⟩

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Equality -/

section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace LeanSce.Target.Heterogeneous

private theorem guard_open_eq (he : g = h ∨ GuardsEq g h) (θ : Subst) (u : Arg) :
    Entails .empty ((g.subst θ.lift).open u) ↔ Entails .empty ((h.subst θ.lift).open u) := by
  rcases he with rfl | he
  · rfl
  · simpa only [← Ty.subst_instantiate] using he.entails_subst (Δ:=.empty) (θ.instantiate u)

private theorem valid_all (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.all k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | all hf hg _ => exact .extend hΔ hf hg

private theorem valid_ex (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.ex k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | ex hf hg _ => exact .extend hΔ hf hg

private theorem fresh_all (hw : WellFormed Δ (.all k gs a)) : FreshGuards k gs := by
  cases hw; assumption

private theorem fresh_ex (hw : WellFormed Δ (.ex k gs a)) : FreshGuards k gs := by
  cases hw; assumption

/-- Structural equality leaves the heterogeneous interpretation invariant.
    Its endpoints may be checked under distinct but simultaneously satisfied
    guard presentations, as happens beneath equivalent universal binders. -/
theorem equal_type (n : Nat) (wa : WellFormed Δ a) (wb : WellFormed Γ b)
    (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ)
    (hη : η.Valid Δ) (hΗ : η.Valid Γ) (he : TyEq a b) :
    (∀ v w, ValRel n a η v w ↔ ValRel n b η v w) ∧
    (∀ q r, ExprRel n a η q r ↔ ExprRel n b η q r) := by
  have hshape : ∀ v w, ShapeRel n a η v w ↔ ShapeRel n b η v w := by
    intro v w
    cases he.shape with
    | tvar | unit | int | bool | string => rfl
    | @prod a b c d ha hb =>
      have hal := (equal_type n wa.prod_left wb.prod_left hΔ hΓ hη hΗ ha).1
      have hbr := (equal_type n wa.prod_right wb.prod_right hΔ hΓ hη hΗ hb).1
      simp only [ShapeRel]
      constructor <;> rintro ⟨x,y,X,Y,hv,hw,hx,hy⟩
      · exact ⟨x,y,X,Y,hv,hw,(hal _ _).mp hx,(hbr _ _).mp hy⟩
      · exact ⟨x,y,X,Y,hv,hw,(hal _ _).mpr hx,(hbr _ _).mpr hy⟩
    | @sum a b c d ha hb =>
      have hal := (equal_type n wa.sum_left wb.sum_left hΔ hΓ hη hΗ ha).1
      have hbr := (equal_type n wa.sum_right wb.sum_right hΔ hΓ hη hΗ hb).1
      simp only [ShapeRel]
      constructor
      · rintro (⟨t,t',x,X,hv,hw,hx⟩ | ⟨t,t',y,Y,hv,hw,hy⟩)
        · exact .inl ⟨t,t',x,X,hv,hw,(hal _ _).mp hx⟩
        · exact .inr ⟨t,t',y,Y,hv,hw,(hbr _ _).mp hy⟩
      · rintro (⟨t,t',x,X,hv,hw,hx⟩ | ⟨t,t',y,Y,hv,hw,hy⟩)
        · exact .inl ⟨t,t',x,X,hv,hw,(hal _ _).mpr hx⟩
        · exact .inr ⟨t,t',y,Y,hv,hw,(hbr _ _).mpr hy⟩
    | @tag a b l ha =>
      have hat := (equal_type n wa.tag_body wb.tag_body hΔ hΓ hη hΗ ha).1
      simp only [ShapeRel]
      constructor <;> rintro ⟨x,X,hv,hw,hx⟩
      · exact ⟨x,X,hv,hw,(hat _ _).mp hx⟩
      · exact ⟨x,X,hv,hw,(hat _ _).mpr hx⟩
    | @record r s hr =>
      have wr := wa.record_row
      have ws := wb.record_row
      rw [ShapeRel,ShapeRel,RowShape,RowShape]
      constructor
      · rintro ⟨fs,gs,hv,hw,hp,hF⟩
        refine ⟨fs,gs,hv,hw,hp,?_⟩
        intro l x X hl hR
        apply (hF l x X hl hR).map hr.tails_perm
        intro A hA hvalues
        have hlA := wr.knownField_lookup hA
        obtain ⟨B,hlB,hAB⟩ := hr.lookup ws hlA
        have hB := Ty.lookup_knownField s hlB
        have hszA := Ty.knownField_size r hA
        have hszB := Ty.knownField_size s hB
        exact ⟨B,hB,((equal_type n (wr.lookup hlA) (ws.lookup hlB) hΔ hΓ hη hΗ hAB).1 x X).mp hvalues⟩
      · rintro ⟨fs,gs,hv,hw,hp,hF⟩
        refine ⟨fs,gs,hv,hw,hp,?_⟩
        intro l x X hl hR
        apply (hF l x X hl hR).map hr.tails_perm.symm
        intro B hB hvalues
        have hlB := ws.knownField_lookup hB
        obtain ⟨A,hlA,hAB⟩ := hr.symm.lookup wr hlB
        have hA := Ty.lookup_knownField r hlA
        have hszA := Ty.knownField_size r hA
        have hszB := Ty.knownField_size s hB
        exact ⟨A,hA,((equal_type n (wr.lookup hlA) (ws.lookup hlB) hΔ hΓ hη hΗ hAB.symm).1 x X).mpr hvalues⟩
    | @arr a b c d ha hb =>
      rw [ShapeRel,ShapeRel]
      constructor
      · intro h j hj x X hx
        have hx' := ((equal_type j wa.arr_left wb.arr_left hΔ hΓ hη hΗ ha).1 x X).mpr hx
        obtain ⟨q,r,hq,hr,hbodies⟩ := h j hj x X hx'
        exact ⟨q,r,hq,hr,((equal_type j wa.arr_right wb.arr_right hΔ hΓ hη hΗ hb).2 q r).mp hbodies⟩
      · intro h j hj x X hx
        have hx' := ((equal_type j wa.arr_left wb.arr_left hΔ hΓ hη hΗ ha).1 x X).mp hx
        obtain ⟨q,r,hq,hr,hbodies⟩ := h j hj x X hx'
        exact ⟨q,r,hq,hr,((equal_type j wa.arr_right wb.arr_right hΔ hΓ hη hΗ hb).2 q r).mpr hbodies⟩
    | @all k gs hs a b hg hab =>
      rw [ShapeRel,ShapeRel]
      constructor
      · intro h j hj p hp hgl hgr
        have hga := (guard_open_eq hg η.left p.left).mpr hgl
        have hgA := (guard_open_eq hg η.right p.right).mpr hgr
        obtain ⟨q,r,hq,hr,hbodies⟩ := h j hj p hp hga hgA
        have hη' := hη.extend (fresh_all wa) hp hga hgA
        have hΗ' := hΗ.extend (fresh_all wb) hp hgl hgr
        exact ⟨q,r,hq,hr,((equal_type j wa.all_body wb.all_body
          (valid_all hΔ wa) (valid_all hΓ wb) hη' hΗ' hab).2 q r).mp hbodies⟩
      · intro h j hj p hp hgl hgr
        have hgb := (guard_open_eq hg η.left p.left).mp hgl
        have hgB := (guard_open_eq hg η.right p.right).mp hgr
        obtain ⟨q,r,hq,hr,hbodies⟩ := h j hj p hp hgb hgB
        have hη' := hη.extend (fresh_all wa) hp hgl hgr
        have hΗ' := hΗ.extend (fresh_all wb) hp hgb hgB
        exact ⟨q,r,hq,hr,((equal_type j wa.all_body wb.all_body
          (valid_all hΔ wa) (valid_all hΓ wb) hη' hΗ' hab).2 q r).mpr hbodies⟩
    | @ex k gs hs a b hg hab =>
      rw [ShapeRel,ShapeRel]
      constructor
      · rintro ⟨p,t,t',x,X,hv,hw,hp,hgl,hgr,hx⟩
        have hgb := (guard_open_eq hg η.left p.left).mp hgl
        have hgB := (guard_open_eq hg η.right p.right).mp hgr
        refine ⟨p,t,t',x,X,hv,hw,hp,hgb,hgB,?_⟩
        exact ((equal_type n wa.ex_body wb.ex_body (valid_ex hΔ wa) (valid_ex hΓ wb)
          (hη.extend (fresh_ex wa) hp hgl hgr) (hΗ.extend (fresh_ex wb) hp hgb hgB) hab).1 x X).mp hx
      · rintro ⟨p,t,t',x,X,hv,hw,hp,hgl,hgr,hx⟩
        have hga := (guard_open_eq hg η.left p.left).mpr hgl
        have hgA := (guard_open_eq hg η.right p.right).mpr hgr
        refine ⟨p,t,t',x,X,hv,hw,hp,hga,hgA,?_⟩
        exact ((equal_type n wa.ex_body wb.ex_body (valid_ex hΔ wa) (valid_ex hΓ wb)
          (hη.extend (fresh_ex wa) hp hga hgA) (hΗ.extend (fresh_ex wb) hp hgl hgr) hab).1 x X).mpr hx
    | @mu a b hab =>
      have hga : Entails Δ (Ty.gnil.open (.type (.mu a))) := by simp [Entails,Ty.open,Ty.subst,Ty.guardAtoms]
      have hgb : Entails Γ (Ty.gnil.open (.type (.mu b))) := by simp [Entails,Ty.open,Ty.subst,Ty.guardAtoms]
      have wa' := wa.mu_body.open (u := .type (.mu a)) hΔ.normal rfl wa hga
      have wb' := wb.mu_body.open (u := .type (.mu b)) hΓ.normal rfl wb hgb
      have he' := hab.open_congr wa.mu_body (ArgEq.type (TyEq.mu hab))
      rw [ShapeRel,ShapeRel]
      constructor <;> rintro ⟨t,t',x,X,hv,hw,hx⟩
      · exact ⟨t,t',x,X,hv,hw,fun j hj => ((equal_type j wa' wb' hΔ hΓ hη hΗ he').1 x X).mp (hx j hj)⟩
      · exact ⟨t,t',x,X,hv,hw,fun j hj => ((equal_type j wa' wb' hΔ hΓ hη hΗ he').1 x X).mpr (hx j hj)⟩
  have hval : ∀ v w, ValRel n a η v w ↔ ValRel n b η v w := by
    intro v w
    rw [ValRel,ValRel]
    constructor
    · rintro ⟨hv,hw,hs⟩
      exact ⟨⟨hv.1,.conv hv.2 (he.subst wa η.left) (wb.subst hΗ.1.respects)⟩,
        ⟨hw.1,.conv hw.2 (he.subst wa η.right) (wb.subst hΗ.2.1.respects)⟩,(hshape v w).mp hs⟩
    · rintro ⟨hv,hw,hs⟩
      exact ⟨⟨hv.1,.conv hv.2 (he.subst wa η.left).symm (wa.subst hη.1.respects)⟩,
        ⟨hw.1,.conv hw.2 (he.subst wa η.right).symm (wa.subst hη.2.1.respects)⟩,(hshape v w).mpr hs⟩
  have hbudget : ∀ m, m ≤ n → ∀ v w, ValRel m a η v w ↔ ValRel m b η v w := by
    intro m hm v w
    by_cases heq : m = n
    · subst m; exact hval v w
    · exact (equal_type m wa wb hΔ hΓ hη hΗ he).1 v w
  refine ⟨hval,?_⟩
  intro q r
  rw [ExprRel,ExprRel]
  constructor
  · rintro ⟨hl,hr⟩
    constructor
    · intro k hk v hv
      obtain ⟨w,hw,hs⟩ := hl k hk v hv
      exact ⟨w,hw,(hbudget (n-k) (Nat.sub_le _ _) v w).mp hs⟩
    · intro k hk w hw
      obtain ⟨v,hv,hs⟩ := hr k hk w hw
      exact ⟨v,hv,(hbudget (n-k) (Nat.sub_le _ _) v w).mp hs⟩
  · rintro ⟨hl,hr⟩
    constructor
    · intro k hk v hv
      obtain ⟨w,hw,hs⟩ := hl k hk v hv
      exact ⟨w,hw,(hbudget (n-k) (Nat.sub_le _ _) v w).mpr hs⟩
    · intro k hk w hw
      obtain ⟨v,hv,hs⟩ := hr k hk w hw
      exact ⟨v,hv,(hbudget (n-k) (Nat.sub_le _ _) v w).mpr hs⟩
termination_by (n,sizeOf a + sizeOf b)
decreasing_by
  all_goals simp_wf
  all_goals first | apply Prod.Lex.left; omega | apply Prod.Lex.right; simp_all; omega

theorem ExprRel.type_convert (hr : ExprRel n a η q r)
    (wa : WellFormed Δ a) (wb : WellFormed Δ b) (he : TyEq a b)
    (hΔ : Context.Valid Δ) (hη : η.Valid Δ) : ExprRel n b η q r :=
  ((equal_type n wa wb hΔ hΔ hη hη he).2 q r).mp hr

end LeanSce.Target.Heterogeneous

end

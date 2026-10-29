import LeanSce.Target.Abstraction.Functions
import LeanSce.Target.Abstraction.Infrastructure
import LeanSce.Target.LogicalRelation.Data
import LeanSce.Target.LogicalRelation.Equality
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Rows

/-!
# Target / Abstraction / Data

Proofs and supporting constructions for data.
-/

/-! ## Heterogeneous Data -/

namespace LeanSce.Target.Heterogeneous

theorem ValRel.inl (hx : ValRel n a η x X) (wb : WellFormed .empty (b.subst η.left)) (wB : WellFormed .empty (b.subst η.right)) :
    ValRel n (.sum a b) η (.inl (b.subst η.left) x) (.inl (b.subst η.right) X) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨hx.left.1,.inl wb hx.left.2⟩,⟨hx.right.1,.inl wB hx.right.2⟩,
    Or.inl ⟨b.subst η.left,b.subst η.right,x,X,rfl,rfl,hx⟩⟩

theorem ValRel.inr (hy : ValRel n b η y Y) (wa : WellFormed .empty (a.subst η.left)) (wA : WellFormed .empty (a.subst η.right)) :
    ValRel n (.sum a b) η (.inr (a.subst η.left) y) (.inr (a.subst η.right) Y) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨hy.left.1,.inr wa hy.left.2⟩,⟨hy.right.1,.inr wA hy.right.2⟩,
    Or.inr ⟨a.subst η.left,a.subst η.right,y,Y,rfl,rfl,hy⟩⟩

theorem ValRel.tag (hx : ValRel n a η x X) : ValRel n (.tag l a) η (.tag l x) (.tag l X) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨hx.left.1,.tag hx.left.2⟩,⟨hx.right.1,.tag hx.right.2⟩,x,X,rfl,rfl,hx⟩

theorem ExprRel.pair (hx : ExprRel n a η (ν,x) (N,X)) (hy : ExprRel n b η (ν,y) (N,Y)) :
    ExprRel n (.prod a b) η (ν,.pair x y) (N,.pair X Y) := by
  apply hx.bind strict_pair_left strict_pair_left
  intro i hi v V hv
  apply (hy.mono (Nat.sub_le _ _)).bind (strict_pair_right hv.left.1) (strict_pair_right hv.right.1)
  intro j hj w W hw
  exact ((hv.mono (Nat.sub_le _ _)).pair hw).toExpr

theorem ExprRel.inl (hx : ExprRel n a η (ν,x) (N,X)) (wb : WellFormed .empty (b.subst η.left)) (wB : WellFormed .empty (b.subst η.right)) :
    ExprRel n (.sum a b) η (ν,.inl (b.subst η.left) x) (N,.inl (b.subst η.right) X) := by
  apply hx.bind (strict_inl (b := b.subst η.left)) (strict_inl (b := b.subst η.right))
  intro i hi v V hv
  exact (hv.inl wb wB).toExpr

theorem ExprRel.inr (hy : ExprRel n b η (ν,y) (N,Y)) (wa : WellFormed .empty (a.subst η.left)) (wA : WellFormed .empty (a.subst η.right)) :
    ExprRel n (.sum a b) η (ν,.inr (a.subst η.left) y) (N,.inr (a.subst η.right) Y) := by
  apply hy.bind (strict_inr (a := a.subst η.left)) (strict_inr (a := a.subst η.right))
  intro i hi v V hv
  exact (hv.inr wa wA).toExpr

theorem ExprRel.tag (hx : ExprRel n a η (ν,x) (N,X)) :
    ExprRel n (.tag l a) η (ν,.tag l x) (N,.tag l X) := by
  apply hx.bind strict_tag strict_tag
  intro i hi v V hv
  exact hv.tag.toExpr

theorem ExprRel.fst (hx : ExprRel n (.prod a b) η (ν,x) (N,X))
    (hν : Value ν) (hN : Value N) : ExprRel n a η (ν,.fst x) (N,.fst X) := by
  apply hx.bind strict_fst strict_fst
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    have hs := hv.shape
    rw [ShapeRel] at hs
    obtain ⟨x,y,X,Y,rfl,rfl,hx,hy⟩ := hs
    apply ExprRel.step (e' := x) (E' := X)
    · exact ⟨hν,by simp [step_fst_eq,(show (Term.pair x y).isValue = true from hv.left.1)]⟩
    · exact ⟨hN,by simp [step_fst_eq,(show (Term.pair X Y).isValue = true from hv.right.1)]⟩
    · exact (hx.mono (by omega)).toExpr

theorem ExprRel.snd (hx : ExprRel n (.prod a b) η (ν,x) (N,X))
    (hν : Value ν) (hN : Value N) : ExprRel n b η (ν,.snd x) (N,.snd X) := by
  apply hx.bind strict_snd strict_snd
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    have hs := hv.shape
    rw [ShapeRel] at hs
    obtain ⟨x,y,X,Y,rfl,rfl,hx,hy⟩ := hs
    apply ExprRel.step (e' := y) (E' := Y)
    · exact ⟨hν,by simp [step_snd_eq,(show (Term.pair x y).isValue = true from hv.left.1)]⟩
    · exact ⟨hN,by simp [step_snd_eq,(show (Term.pair X Y).isValue = true from hv.right.1)]⟩
    · exact (hy.mono (by omega)).toExpr

private theorem binary_prim_rel (hx : ExprRel n a η (ν,x) (N,X))
    (hy : ExprRel n b η (ν,y) (N,Y))
    (hr : ∀ m v V w W, ValRel m a η v V → ValRel m b η w W →
      ExprRel m c η (ν,.prim p (.cons l v (.cons k w .nil)))
        (N,.prim p (.cons l V (.cons k W .nil)))) :
    ExprRel n c η (ν,.prim p (.cons l x (.cons k y .nil)))
      (N,.prim p (.cons l X (.cons k Y .nil))) := by
  apply hx.bind strict_prim_left strict_prim_left
  intro i hi v V hv
  apply (hy.mono (Nat.sub_le _ _)).bind (strict_prim_right hv.left.1) (strict_prim_right hv.right.1)
  intro j hj w W hw
  exact hr _ v V w W (hv.mono (Nat.sub_le _ _)) hw

theorem ExprRel.add (hx : ExprRel n .int η (ν,x) (N,X))
    (hy : ExprRel n .int η (ν,y) (N,Y)) (hν : Value ν) (hN : Value N) :
    ExprRel n .int η (ν,.prim .add (.cons l x (.cons k y .nil)))
      (N,.prim .add (.cons l X (.cons k Y .nil))) := by
  apply binary_prim_rel hx hy
  intro m v V w W hv hw
  cases m with
  | zero => exact ExprRel.zero
  | succ m =>
    have hs := hv.shape
    have ht := hw.shape
    rw [ShapeRel] at hs ht
    obtain ⟨i,rfl,rfl⟩ := hs
    obtain ⟨j,rfl,rfl⟩ := ht
    exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩ ValRel.int.toExpr

theorem ExprRel.eqInt (hx : ExprRel n .int η (ν,x) (N,X))
    (hy : ExprRel n .int η (ν,y) (N,Y)) (hν : Value ν) (hN : Value N) :
    ExprRel n .bool η (ν,.prim .eqInt (.cons l x (.cons k y .nil)))
      (N,.prim .eqInt (.cons l X (.cons k Y .nil))) := by
  apply binary_prim_rel hx hy
  intro m v V w W hv hw
  cases m with
  | zero => exact ExprRel.zero
  | succ m =>
    have hs := hv.shape
    have ht := hw.shape
    rw [ShapeRel] at hs ht
    obtain ⟨i,rfl,rfl⟩ := hs
    obtain ⟨j,rfl,rfl⟩ := ht
    exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩ ValRel.bool.toExpr

theorem ExprRel.concat (hx : ExprRel n .string η (ν,x) (N,X))
    (hy : ExprRel n .string η (ν,y) (N,Y)) (hν : Value ν) (hN : Value N) :
    ExprRel n .string η (ν,.prim .concat (.cons l x (.cons k y .nil)))
      (N,.prim .concat (.cons l X (.cons k Y .nil))) := by
  apply binary_prim_rel hx hy
  intro m v V w W hv hw
  cases m with
  | zero => exact ExprRel.zero
  | succ m =>
    have hs := hv.shape
    have ht := hw.shape
    rw [ShapeRel] at hs ht
    obtain ⟨i,rfl,rfl⟩ := hs
    obtain ⟨j,rfl,rfl⟩ := ht
    exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩ ValRel.string.toExpr

theorem ExprRel.showInt (hx : ExprRel n .int η (ν,x) (N,X))
    (hν : Value ν) (hN : Value N) :
    ExprRel n .string η (ν,.prim .showInt (.cons l x .nil))
      (N,.prim .showInt (.cons l X .nil)) := by
  apply hx.bind strict_prim_one strict_prim_one
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    have hs := hv.shape
    rw [ShapeRel] at hs
    obtain ⟨z,rfl,rfl⟩ := hs
    exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩ ValRel.string.toExpr

theorem ExprRel.ite (hc : ExprRel n .bool η (ν,c) (N,C))
    (hx : ExprRel n a η (ν,x) (N,X)) (hy : ExprRel n a η (ν,y) (N,Y))
    (hν : Value ν) (hN : Value N) :
    ExprRel n a η (ν,.ite c x y) (N,.ite C X Y) := by
  apply hc.bind strict_ite strict_ite
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    have hs := hv.shape
    rw [ShapeRel] at hs
    obtain ⟨b,rfl,rfl⟩ := hs
    cases b with
    | false => exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩ (hy.mono (by omega))
    | true => exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩ (hx.mono (by omega))

theorem ValRel.find (hr : ValRel n a η v V) (hu : Unique l a b) :
    ∃ w W, v.findTags l = [w] ∧ V.findTags l = [W] ∧ ValRel n b η w W := by
  induction hu generalizing v V with
  | here =>
    have hs := hr.shape
    rw [ShapeRel] at hs
    obtain ⟨x,X,rfl,rfl,hx⟩ := hs
    exact ⟨x,X,by simp [Term.findTags],by simp [Term.findTags],hx⟩
  | left hu ha ih =>
    have hs := hr.shape
    rw [ShapeRel] at hs
    obtain ⟨x,y,X,Y,rfl,rfl,hx,hy⟩ := hs
    obtain ⟨w,W,hw,hW,hrel⟩ := ih hx
    have habs := findTags_absent hy.left.2 hy.left.1 (ha.subst η.left)
    have hAbs := findTags_absent hy.right.2 hy.right.1 (ha.subst η.right)
    exact ⟨w,W,by simp [Term.findTags,hw,habs],by simp [Term.findTags,hW,hAbs],hrel⟩
  | right ha hu ih =>
    have hs := hr.shape
    rw [ShapeRel] at hs
    obtain ⟨x,y,X,Y,rfl,rfl,hx,hy⟩ := hs
    obtain ⟨w,W,hw,hW,hrel⟩ := ih hy
    have habs := findTags_absent hx.left.2 hx.left.1 (ha.subst η.left)
    have hAbs := findTags_absent hx.right.2 hx.right.1 (ha.subst η.right)
    exact ⟨w,W,by simp [Term.findTags,hw,habs],by simp [Term.findTags,hW,hAbs],hrel⟩

theorem ExprRel.find (he : ExprRel n a η (ν,e) (N,E)) (hu : Unique l a b)
    (hν : Value ν) (hN : Value N) : ExprRel n b η (ν,.find l e) (N,.find l E) := by
  apply he.bind strict_find strict_find
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨w,W,hw,hW,hrel⟩ := hv.find hu
    exact ExprRel.step
      ⟨hν,by simp [step_find_eq,(show v.isValue = true from hv.left.1),hw]⟩
      ⟨hN,by simp [step_find_eq,(show V.isValue = true from hv.right.1),hW]⟩
      ((hrel.mono (by omega)).toExpr)

theorem ValRel.case {left Left right Right : Expr} (hx : ValRel n (.sum a b) η x X) (hc : ValRel n h η ν N)
    (hl : BodyRel η (.prod h a) c left Left) (hr : BodyRel η (.prod h b) c right Right) :
    ExprRel n c η (ν,.case x left right) (N,.case X Left Right) := by
  have hs := hx.shape
  rw [ShapeRel] at hs
  rcases hs with ⟨t,t',v,V,hxv,hXV,hvals⟩ | ⟨t,t',v,V,hxv,hXV,hvals⟩
  · subst x;subst X
    have hstep : Step ν (.case (.inl t v) left right) (.box (.pair ν v) left) :=
      ⟨hc.left.1,by simp [step_case_eq,(show _ = true from hx.left.1)]⟩
    have Hstep : Step N (.case (.inl t' V) Left Right) (.box (.pair N V) Left) :=
      ⟨hc.right.1,by simp [step_case_eq,(show _ = true from hx.right.1)]⟩
    cases n with
    | zero => exact ExprRel.zero
    | succ m =>
      cases m with
      | zero => exact ExprRel.step hstep Hstep ExprRel.zero
      | succ j =>
        have he := (hc.mono (m := j) (by omega)).pair (hvals.mono (m := j) (by omega))
        exact ExprRel.step hstep Hstep
          ((hl j _ _ he).box_value hc.left.1 hc.right.1 he.left.1 he.right.1)
  · subst x;subst X
    have hstep : Step ν (.case (.inr t v) left right) (.box (.pair ν v) right) :=
      ⟨hc.left.1,by simp [step_case_eq,(show _ = true from hx.left.1)]⟩
    have Hstep : Step N (.case (.inr t' V) Left Right) (.box (.pair N V) Right) :=
      ⟨hc.right.1,by simp [step_case_eq,(show _ = true from hx.right.1)]⟩
    cases n with
    | zero => exact ExprRel.zero
    | succ m =>
      cases m with
      | zero => exact ExprRel.step hstep Hstep ExprRel.zero
      | succ j =>
        have he := (hc.mono (m := j) (by omega)).pair (hvals.mono (m := j) (by omega))
        exact ExprRel.step hstep Hstep
          ((hr j _ _ he).box_value hc.left.1 hc.right.1 he.left.1 he.right.1)

theorem ExprRel.case {left Left right Right : Expr} (hx : ExprRel n (.sum a b) η (ν,x) (N,X)) (hc : ValRel n h η ν N)
    (hl : BodyRel η (.prod h a) c left Left) (hr : BodyRel η (.prod h b) c right Right) :
    ExprRel n c η (ν,.case x left right) (N,.case X Left Right) := by
  apply hx.bind strict_case strict_case
  intro i hi v V hv
  exact hv.case (hc.mono (Nat.sub_le _ _)) hl hr

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Records -/

namespace LeanSce.Target.Heterogeneous

theorem FieldRel.of_lookup (hl : r.lookup l = some a) (hv : ValRel n a η v V) :
    FieldRel n r η l v V := by
  cases r with
  | rvar | empty => simp [Ty.lookup] at hl
  | field k b =>
    by_cases heq : l = k
    · subst k
      have heq : b = a := by simpa [Ty.lookup] using hl
      subst b
      rw [FieldRel]
      exact ⟨rfl,hv⟩
    · simp [Ty.lookup,heq] at hl
  | union r s =>
    rw [FieldRel]
    cases hr : r.lookup l with
    | none => exact .inr (FieldRel.of_lookup (by simpa [Ty.lookup,hr] using hl) hv)
    | some b =>
      have heq : b = a := by simpa [Ty.lookup,hr] using hl
      subst b
      exact .inl (FieldRel.of_lookup hr hv)
termination_by sizeOf r

theorem FieldRel.lookup (h : FieldRel n r η l v V) (wr : WellFormed Δ r)
    (hη : η.Valid Δ) (hl : r.lookup l = some a) : ValRel n a η v V := by
  cases wr with
  | rvar | empty => simp [Ty.lookup] at hl
  | field wb =>
    rw [FieldRel] at h
    obtain ⟨rfl,hv⟩ := h
    have heq := Option.some.inj (by simpa [Ty.lookup] using hl)
    subst a
    exact hv
  | @union _ r s wr ws hd =>
    rw [FieldRel] at h
    cases hr : r.lookup l with
    | none =>
      have hs : s.lookup l = some a := by simpa [Ty.lookup,hr] using hl
      rcases h with h | h
      · exact False.elim ((hd.subst hη.1.respects).knownLabels l h.domain.1
          (Ty.lookup_mem _ (ws.lookup_subst hη.1.respects hs)))
      · exact h.lookup ws hη hs
    | some b =>
      have heq : b = a := by simpa [Ty.lookup,hr] using hl
      subst b
      rcases h with h | h
      · exact h.lookup wr hη hr
      · exact False.elim ((hd.subst hη.1.respects).knownLabels l
          (Ty.lookup_mem _ (wr.lookup_subst hη.1.respects hr)) h.domain.1)
termination_by sizeOf r

theorem FieldRel.select_of_lookup {r : Row} {ls : List String}
    (hl : r.lookup l = some a) (hm : l ∈ ls)
    (hv : ValRel n a η v V) : FieldRel n (r.select ls) η l v V := by
  cases r with
  | rvar | empty => simp [Ty.lookup] at hl
  | field k b =>
    by_cases heq : l = k
    · subst k
      have heq : b = a := by simpa [Ty.lookup] using hl
      subst b
      simpa only [Ty.select,if_pos hm,FieldRel] using And.intro (Eq.refl l) hv
    · simp [Ty.lookup,heq] at hl
  | union r s =>
    simp only [Ty.select,FieldRel]
    cases hr : r.lookup l with
    | none => exact .inr (FieldRel.select_of_lookup (by simpa [Ty.lookup,hr] using hl) hm hv)
    | some b =>
      have heq : b = a := by simpa [Ty.lookup,hr] using hl
      subst b
      exact .inl (FieldRel.select_of_lookup hr hm hv)
termination_by sizeOf r

theorem FieldRel.drop (h : FieldRel n r η l v V) (hm : l ∉ ls) :
    FieldRel n (r.drop ls) η l v V := by
  cases r with
  | rvar => simpa only [Ty.drop] using h
  | empty => simpa only [Ty.drop] using h
  | field k a =>
    rw [FieldRel] at h
    obtain ⟨rfl,hv⟩ := h
    simpa only [Ty.drop,if_neg hm,FieldRel] using And.intro (Eq.refl l) hv
  | union r s =>
    simp only [Ty.drop,FieldRel] at h ⊢
    exact h.elim (fun h => .inl (h.drop hm)) (fun h => .inr (h.drop hm))
termination_by sizeOf r

theorem FieldRel.relabel_other (h : FieldRel n r η l v V) (ho : l ≠ old) (hn : l ≠ new) :
    FieldRel n (r.relabel old new) η l v V := by
  cases r with
  | rvar => simpa only [Ty.relabel] using h
  | empty => simpa only [Ty.relabel] using h
  | field k a =>
    rw [FieldRel] at h
    obtain ⟨rfl,hv⟩ := h
    simpa [Ty.relabel,FieldRel,ho] using And.intro (Eq.refl l) hv
  | union r s =>
    simp only [Ty.relabel,FieldRel] at h ⊢
    exact h.elim (fun h => .inl (h.relabel_other ho hn)) (fun h => .inr (h.relabel_other ho hn))
termination_by sizeOf r

theorem FieldRel.relabel_of_lookup {r : Row} {old new : String}
    (hl : r.lookup old = some a) (hv : ValRel n a η v V) :
    FieldRel n (r.relabel old new) η new v V := by
  cases r with
  | rvar | empty => simp [Ty.lookup] at hl
  | field k b =>
    by_cases heq : old = k
    · subst k
      have heq : b = a := by simpa [Ty.lookup] using hl
      subst b
      simpa only [Ty.relabel,beq_self_eq_true,↓reduceIte,FieldRel] using And.intro (Eq.refl new) hv
    · simp [Ty.lookup,heq] at hl
  | union r s =>
    simp only [Ty.relabel,FieldRel]
    cases hr : r.lookup old with
    | none => exact .inr (FieldRel.relabel_of_lookup (by simpa [Ty.lookup,hr] using hl) hv)
    | some b =>
      have heq : b = a := by simpa [Ty.lookup,hr] using hl
      subst b
      exact .inl (FieldRel.relabel_of_lookup hr hv)
termination_by sizeOf r

theorem ValRel.record_inv (hr : ValRel n (.record r) η v V) :
    ∃ fs gs, v = .record fs ∧ V = .record gs := by
  have hs := hr.shape
  rw [ShapeRel,RowShape] at hs
  obtain ⟨fs,gs,hv,hV,_,_⟩ := hs
  exact ⟨fs,gs,hv,hV⟩

theorem ValRel.field (hr : ValRel n (.record r) η (.record fs) (.record gs))
    (hl : fs.lookup l = some x) (hL : gs.lookup l = some X) : FieldRel n r η l x X := by
  have hs := hr.shape
  rw [ShapeRel,RowShape] at hs
  obtain ⟨_,_,hfs,hgs,_,hf⟩ := hs
  cases hfs; cases hgs
  exact hf l x X hl hL

theorem ValRel.get (hr : ValRel n (.record r) η (.record fs) (.record gs))
    (wr : WellFormed Δ r) (hη : η.Valid Δ) (hl : r.lookup l = some a) :
    ∃ x X, fs.lookup l = some x ∧ gs.lookup l = some X ∧ ValRel n a η x X := by
  have wf := wr.subst hη.1.respects
  have wg := wr.subst hη.2.1.respects
  have hf := hr.left.2.value_record_inv hr.left.1 wf
  have hg := hr.right.2.value_record_inv hr.right.1 wg
  obtain ⟨x,hx,_⟩ := hf.lookup .empty (wr.lookup_subst hη.1.respects hl)
  obtain ⟨X,hX,_⟩ := hg.lookup .empty (wr.lookup_subst hη.2.1.respects hl)
  exact ⟨x,X,hx,hX,(hr.field hx hX).lookup wr hη hl⟩

theorem ValRel.of_record_fields (wr : WellFormed Δ r) (hη : η.Valid Δ)
    (hv : ValueType .empty (.record fs) (.record (r.subst η.left)))
    (hV : ValueType .empty (.record gs) (.record (r.subst η.right)))
    (hf : ∀ l x X, fs.lookup l = some x → gs.lookup l = some X → FieldRel n r η l x X) :
    ValRel n (.record r) η (.record fs) (.record gs) := by
  have hfs := hv.2.value_record_inv hv.1 (wr.subst hη.1.respects)
  have hgs := hV.2.value_record_inv hV.1 (wr.subst hη.2.1.respects)
  rw [ValRel,ShapeRel,RowShape]
  exact ⟨hv,hV,fs,gs,rfl,rfl,
    hfs.labels_perm.trans ((Valuation.row_domains hη wr).trans hgs.labels_perm.symm),hf⟩

theorem ValRel.record_nil : ValRel n (.record .empty) η (.record .nil) (.record .nil) := by
  rw [ValRel,ShapeRel,RowShape]
  refine ⟨⟨rfl,.record (.nil .unit)⟩,⟨rfl,.record (.nil .unit)⟩,.nil,.nil,rfl,rfl,.refl _,?_⟩
  intro l x X hx
  cases hx

theorem ValRel.take (hr : ValRel n (.record r) η (.record fs) (.record gs))
    (wr : WellFormed Δ r) (hη : η.Valid Δ)
    (hsel : ∀ l ∈ ls, ∃ a, r.lookup l = some a) :
    ValRel n (.record (r.select ls)) η
      (.record (fs.filter ls.contains)) (.record (gs.filter ls.contains)) := by
  have wf := wr.subst hη.1.respects
  have wg := wr.subst hη.2.1.respects
  have hf := hr.left.2.value_record_inv hr.left.1 wf
  have hg := hr.right.2.value_record_inv hr.right.1 wg
  apply ValRel.of_record_fields (fs := fs.filter ls.contains) (gs := gs.filter ls.contains) (wr.select ls) hη
    ⟨Term.filter_value fs hr.left.1,.conv (.record (hf.select .empty ls))
      (.record (wr.select_subst hη.1.respects hsel).symm)
      (.record ((wr.select ls).subst hη.1.respects))⟩
    ⟨Term.filter_value gs hr.right.1,.conv (.record (hg.select .empty ls))
      (.record (wr.select_subst hη.2.1.respects hsel).symm)
      (.record ((wr.select ls).subst hη.2.1.respects))⟩
  intro l x X hx hX
  by_cases hm : l ∈ ls
  · have hx' : fs.lookup l = some x := by simpa [Term.lookup_filter,hm] using hx
    have hX' : gs.lookup l = some X := by simpa [Term.lookup_filter,hm] using hX
    obtain ⟨a,ha⟩ := hsel l hm
    exact FieldRel.select_of_lookup ha hm ((hr.field hx' hX').lookup wr hη ha)
  · simp [Term.lookup_filter,hm] at hx

theorem ValRel.drop (hr : ValRel n (.record r) η (.record fs) (.record gs))
    (wr : WellFormed Δ r) (hη : η.Valid Δ)
    (hsel : ∀ l ∈ ls, ∃ a, r.lookup l = some a) :
    ValRel n (.record (r.drop ls)) η
      (.record (fs.filter (fun l => !ls.contains l)))
      (.record (gs.filter (fun l => !ls.contains l))) := by
  have wf := wr.subst hη.1.respects
  have wg := wr.subst hη.2.1.respects
  have hf := hr.left.2.value_record_inv hr.left.1 wf
  have hg := hr.right.2.value_record_inv hr.right.1 wg
  apply ValRel.of_record_fields (fs := fs.filter (fun l => !ls.contains l)) (gs := gs.filter (fun l => !ls.contains l)) (wr.drop ls) hη
    ⟨Term.filter_value fs hr.left.1,by simpa only [wr.drop_subst hη.1.respects hsel]
      using (HasType.record (hf.drop .empty ls))⟩
    ⟨Term.filter_value gs hr.right.1,by simpa only [wr.drop_subst hη.2.1.respects hsel]
      using (HasType.record (hg.drop .empty ls))⟩
  intro l x X hx hX
  by_cases hm : l ∈ ls
  · simp [Term.lookup_filter,hm] at hx
  · have hx' : fs.lookup l = some x := by simpa [Term.lookup_filter,hm] using hx
    have hX' : gs.lookup l = some X := by simpa [Term.lookup_filter,hm] using hX
    exact (hr.field hx' hX').drop hm

private theorem lookup_exists (fs : Fields) (hm : l ∈ fs.labels) :
    ∃ x, fs.lookup l = some x := by
  cases fs with
  | cons k x rest =>
    by_cases h : l = k
    · subst k; exact ⟨x,by simp [Term.lookup]⟩
    · have hm' : l ∈ rest.labels := by simpa [Term.labels,h] using hm
      obtain ⟨x,hx⟩ := lookup_exists rest hm'
      exact ⟨x,by simpa [Term.lookup,h] using hx⟩
  | _ => simp [Term.labels] at hm
termination_by sizeOf fs

theorem ValRel.fields_perm (hr : ValRel n (.record r) η (.record fs) (.record gs)) :
    fs.labels.Perm gs.labels := by
  have hs := hr.shape
  rw [ShapeRel,RowShape] at hs
  obtain ⟨_,_,hfs,hgs,hp,_⟩ := hs
  cases hfs; cases hgs
  exact hp

theorem ValRel.merge (hr : ValRel n (.record r) η (.record fs) (.record Fs))
    (hs : ValRel n (.record s) η (.record gs) (.record Gs))
    (wr : WellFormed Δ r) (ws : WellFormed Δ s) (hη : η.Valid Δ) (hd : Disjoint Δ r s) :
    ValRel n (.record (.union r s)) η (.record (fs.append gs)) (.record (Fs.append Gs)) := by
  have hf := hr.left.2.value_record_inv hr.left.1 (wr.subst hη.1.respects)
  have hF := hr.right.2.value_record_inv hr.right.1 (wr.subst hη.2.1.respects)
  have hg := hs.left.2.value_record_inv hs.left.1 (ws.subst hη.1.respects)
  have hG := hs.right.2.value_record_inv hs.right.1 (ws.subst hη.2.1.respects)
  apply ValRel.of_record_fields (fs := fs.append gs) (gs := Fs.append Gs) (.union wr ws hd) hη
    ⟨Term.append_value fs hr.left.1 hs.left.1,
      .record (hf.append .empty hg (hd.subst hη.1.respects))⟩
    ⟨Term.append_value Fs hr.right.1 hs.right.1,
      .record (hF.append .empty hG (hd.subst hη.2.1.respects))⟩
  intro l x X hx hX
  rw [FieldRel]
  cases he : fs.lookup l with
  | some v =>
    obtain ⟨V,hV⟩ := lookup_exists Fs (hr.fields_perm.mem_iff.mp (Term.lookup_mem_labels fs he))
    have hxEq : v = x := by simpa [Term.lookup_append,he] using hx
    have hXEq : V = X := by simpa [Term.lookup_append,hV] using hX
    subst v; subst V
    exact .inl (hr.field he hV)
  | none =>
    have hnone : Fs.lookup l = none := by
      cases hFlook : Fs.lookup l with
      | none => rfl
      | some V =>
        obtain ⟨v,hv⟩ := lookup_exists fs
          (hr.fields_perm.mem_iff.mpr (Term.lookup_mem_labels Fs hFlook))
        rw [he] at hv
        cases hv
    exact .inr (hs.field (by simpa [Term.lookup_append,he] using hx)
      (by simpa [Term.lookup_append,hnone] using hX))

theorem ValRel.cons (hx : ValRel n a η x X)
    (hf : ValRel n (.record r) η (.record fs) (.record Fs))
    (wa : WellFormed Δ a) (wr : WellFormed Δ r) (hη : η.Valid Δ)
    (hd : Disjoint Δ (.field l a) r) :
    ValRel n (.record (.union (.field l a) r)) η
      (.record (.cons l x fs)) (.record (.cons l X Fs)) := by
  have hfs := hf.left.2.value_record_inv hf.left.1 (wr.subst hη.1.respects)
  have hFs := hf.right.2.value_record_inv hf.right.1 (wr.subst hη.2.1.respects)
  apply ValRel.of_record_fields (fs := .cons l x fs) (gs := .cons l X Fs) (.union (.field wa) wr hd) hη
    ⟨Bool.and_eq_true_iff.mpr ⟨hx.left.1,hf.left.1⟩,
      .record (.cons hx.left.2 hfs (hd.subst hη.1.respects))⟩
    ⟨Bool.and_eq_true_iff.mpr ⟨hx.right.1,hf.right.1⟩,
      .record (.cons hx.right.2 hFs (hd.subst hη.2.1.respects))⟩
  intro q v V hv hV
  rw [FieldRel]
  by_cases he : q = l
  · subst q
    have hvEq : x = v := by simpa [Term.lookup] using hv
    have hVEq : X = V := by simpa [Term.lookup] using hV
    subst v; subst V
    exact .inl (by rw [FieldRel]; exact ⟨rfl,hx⟩)
  · exact .inr (hf.field (by simpa [Term.lookup,he] using hv) (by simpa [Term.lookup,he] using hV))

private theorem lookup_renamed_old (fs : Fields) (hn : old ≠ new) :
    (fs.renameFields old new).lookup old = none := by
  cases fs with
  | nil => rfl
  | cons k e rest =>
    by_cases hk : k = old
    · subst k
      simp [Term.renameFields,Term.lookup,hn,lookup_renamed_old rest hn]
    · simp [Term.renameFields,Term.lookup,hk,Ne.symm hk,lookup_renamed_old rest hn]
termination_by sizeOf fs

theorem ValRel.relabel (hr : ValRel n (.record r) η (.record fs) (.record gs))
    (wr : WellFormed Δ r) (hη : η.Valid Δ) (hl : r.lookup old = some a)
    (hn : old ≠ new) (hd : Disjoint Δ (.field new a) (r.drop [old])) :
    ValRel n (.record (r.relabel old new)) η
      (.record (fs.renameFields old new)) (.record (gs.renameFields old new)) := by
  have wf := wr.subst hη.1.respects
  have wg := wr.subst hη.2.1.respects
  have hf := hr.left.2.value_record_inv hr.left.1 wf
  have hg := hr.right.2.value_record_inv hr.right.1 wg
  have hsel : ∀ l ∈ [old], ∃ a, r.lookup l = some a := by
    intro l hm; simp only [List.mem_singleton] at hm; subst l; exact ⟨a,hl⟩
  have hdL : Disjoint .empty (.field new (a.subst η.left)) ((r.subst η.left).drop [old]) := by
    simpa only [Ty.subst,wr.drop_subst hη.1.respects hsel] using hd.subst hη.1.respects
  have hdR : Disjoint .empty (.field new (a.subst η.right)) ((r.subst η.right).drop [old]) := by
    simpa only [Ty.subst,wr.drop_subst hη.2.1.respects hsel] using hd.subst hη.2.1.respects
  have hfsnew : new ∉ fs.labels := fun hm => hdL.relabel_fresh hn (hf.labels_mem.mp hm)
  have hgsnew : new ∉ gs.labels := fun hm => hdR.relabel_fresh hn (hg.labels_mem.mp hm)
  apply ValRel.of_record_fields (fs := fs.renameFields old new) (gs := gs.renameFields old new)
    (wr.relabel hd) hη
    ⟨Term.renameFields_value fs hr.left.1,by simpa only [wr.relabel_subst hη.1.respects hl]
      using (HasType.record (hf.relabel .empty hdL))⟩
    ⟨Term.renameFields_value gs hr.right.1,by simpa only [wr.relabel_subst hη.2.1.respects hl]
      using (HasType.record (hg.relabel .empty hdR))⟩
  intro q x X hx hX
  by_cases hqn : q = new
  · subst q
    have hx' := hx
    have hX' := hX
    rw [Term.lookup_rename_target fs hn hfsnew] at hx'
    rw [Term.lookup_rename_target gs hn hgsnew] at hX'
    exact FieldRel.relabel_of_lookup hl ((hr.field hx' hX').lookup wr hη hl)
  · by_cases hqo : q = old
    · subst q
      rw [lookup_renamed_old fs hn] at hx
      cases hx
    · rw [Term.lookup_rename_other fs hqo hqn] at hx
      rw [Term.lookup_rename_other gs hqo hqn] at hX
      exact (hr.field hx hX).relabel_other hqo hqn

theorem ExprRel.get (he : ExprRel n (.record r) η (ν,e) (N,E))
    (wr : WellFormed Δ r) (hη : η.Valid Δ) (hl : r.lookup l = some a)
    (hν : Value ν) (hN : Value N) : ExprRel n a η (ν,.get e l) (N,.get E l) := by
  apply he.bind strict_get strict_get
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,gs,rfl,rfl⟩ := hv.record_inv
    obtain ⟨x,X,hx,hX,hrel⟩ := hv.get wr hη hl
    exact ExprRel.step
      ⟨hν,by simp [step_get_eq,(show (Term.record fs).isValue = true from hv.left.1),hx]⟩
      ⟨hN,by simp [step_get_eq,(show (Term.record gs).isValue = true from hv.right.1),hX]⟩
      ((hrel.mono (by omega)).toExpr)

theorem ExprRel.take (he : ExprRel n (.record r) η (ν,e) (N,E))
    (wr : WellFormed Δ r) (hη : η.Valid Δ)
    (hl : ∀ l ∈ ls, ∃ a, r.lookup l = some a) (hν : Value ν) (hN : Value N) :
    ExprRel n (.record (r.select ls)) η (ν,.take ls e) (N,.take ls E) := by
  apply he.bind strict_take strict_take
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,gs,rfl,rfl⟩ := hv.record_inv
    have hf := hv.left.2.value_record_inv hv.left.1 (wr.subst hη.1.respects)
    have hg := hv.right.2.value_record_inv hv.right.1 (wr.subst hη.2.1.respects)
    have hL : ∀ l ∈ ls, ∃ a, (r.subst η.left).lookup l = some a := by
      intro l hm; obtain ⟨a,ha⟩ := hl l hm; exact ⟨a.subst η.left,wr.lookup_subst hη.1.respects ha⟩
    have hR : ∀ l ∈ ls, ∃ a, (r.subst η.right).lookup l = some a := by
      intro l hm; obtain ⟨a,ha⟩ := hl l hm; exact ⟨a.subst η.right,wr.lookup_subst hη.2.1.respects ha⟩
    exact ExprRel.step
      ⟨hν,by simp [step_take_eq,(show (Term.record fs).isValue = true from hv.left.1),hf.selection_check _ hL]⟩
      ⟨hN,by simp [step_take_eq,(show (Term.record gs).isValue = true from hv.right.1),hg.selection_check _ hR]⟩
      (((hv.mono (by omega)).take wr hη hl).toExpr)

theorem ExprRel.drop (he : ExprRel n (.record r) η (ν,e) (N,E))
    (wr : WellFormed Δ r) (hη : η.Valid Δ)
    (hl : ∀ l ∈ ls, ∃ a, r.lookup l = some a) (hν : Value ν) (hN : Value N) :
    ExprRel n (.record (r.drop ls)) η (ν,.drop ls e) (N,.drop ls E) := by
  apply he.bind strict_drop strict_drop
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,gs,rfl,rfl⟩ := hv.record_inv
    have hf := hv.left.2.value_record_inv hv.left.1 (wr.subst hη.1.respects)
    have hg := hv.right.2.value_record_inv hv.right.1 (wr.subst hη.2.1.respects)
    have hL : ∀ l ∈ ls, ∃ a, (r.subst η.left).lookup l = some a := by
      intro l hm; obtain ⟨a,ha⟩ := hl l hm; exact ⟨a.subst η.left,wr.lookup_subst hη.1.respects ha⟩
    have hR : ∀ l ∈ ls, ∃ a, (r.subst η.right).lookup l = some a := by
      intro l hm; obtain ⟨a,ha⟩ := hl l hm; exact ⟨a.subst η.right,wr.lookup_subst hη.2.1.respects ha⟩
    exact ExprRel.step
      ⟨hν,by simp [step_drop_eq,(show (Term.record fs).isValue = true from hv.left.1),hf.selection_check _ hL]⟩
      ⟨hN,by simp [step_drop_eq,(show (Term.record gs).isValue = true from hv.right.1),hg.selection_check _ hR]⟩
      (((hv.mono (by omega)).drop wr hη hl).toExpr)

theorem ExprRel.relabel (he : ExprRel n (.record r) η (ν,e) (N,E))
    (wr : WellFormed Δ r) (hη : η.Valid Δ) (hl : r.lookup old = some a)
    (hne : old ≠ new) (hd : Disjoint Δ (.field new a) (r.drop [old]))
    (hν : Value ν) (hN : Value N) :
    ExprRel n (.record (r.relabel old new)) η (ν,.relabel old new e) (N,.relabel old new E) := by
  apply he.bind strict_relabel strict_relabel
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,gs,rfl,rfl⟩ := hv.record_inv
    have hf := hv.left.2.value_record_inv hv.left.1 (wr.subst hη.1.respects)
    have hg := hv.right.2.value_record_inv hv.right.1 (wr.subst hη.2.1.respects)
    have hsel : ∀ l ∈ [old], ∃ a, r.lookup l = some a := by
      intro l hm; simp only [List.mem_singleton] at hm; subst l; exact ⟨a,hl⟩
    have hdL : Disjoint .empty (.field new (a.subst η.left)) ((r.subst η.left).drop [old]) := by
      simpa only [Ty.subst,wr.drop_subst hη.1.respects hsel] using hd.subst hη.1.respects
    have hdR : Disjoint .empty (.field new (a.subst η.right)) ((r.subst η.right).drop [old]) := by
      simpa only [Ty.subst,wr.drop_subst hη.2.1.respects hsel] using hd.subst hη.2.1.respects
    exact ExprRel.step
      ⟨hν,by simp only [step_relabel_eq,(show (Term.record fs).isValue = true from hv.left.1),
        Bool.not_true,Bool.false_eq_true,↓reduceIte,hf.relabel_check (wr.lookup_subst hη.1.respects hl) hne hdL]⟩
      ⟨hN,by simp only [step_relabel_eq,(show (Term.record gs).isValue = true from hv.right.1),
        Bool.not_true,Bool.false_eq_true,↓reduceIte,hg.relabel_check (wr.lookup_subst hη.2.1.respects hl) hne hdR]⟩
      (((hv.mono (by omega)).relabel wr hη hl hne hd).toExpr)

theorem ExprRel.merge (he : ExprRel n (.record r) η (ν,e) (N,E))
    (hf : ExprRel n (.record s) η (ν,f) (N,F))
    (wr : WellFormed Δ r) (ws : WellFormed Δ s) (hη : η.Valid Δ) (hd : Disjoint Δ r s)
    (hν : Value ν) (hN : Value N) :
    ExprRel n (.record (.union r s)) η (ν,.merge e f) (N,.merge E F) := by
  apply he.bind strict_merge_left strict_merge_left
  intro i hi v V hv
  apply (hf.mono (Nat.sub_le _ _)).bind (strict_merge_right hv.left.1) (strict_merge_right hv.right.1)
  intro j hj w W hw
  cases hn : n-i-j with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,Fs,rfl,rfl⟩ := hv.record_inv
    obtain ⟨gs,Gs,rfl,rfl⟩ := hw.record_inv
    have hfs := hv.left.2.value_record_inv hv.left.1 (wr.subst hη.1.respects)
    have hFs := hv.right.2.value_record_inv hv.right.1 (wr.subst hη.2.1.respects)
    have hgs := hw.left.2.value_record_inv hw.left.1 (ws.subst hη.1.respects)
    have hGs := hw.right.2.value_record_inv hw.right.1 (ws.subst hη.2.1.respects)
    exact ExprRel.step
      ⟨hν,by simp only [step_merge_eq,(show (Term.record fs).isValue = true from hv.left.1),
        (show (Term.record gs).isValue = true from hw.left.1),Bool.not_true,Bool.false_eq_true,↓reduceIte,
        hfs.merge_check hgs (hd.subst hη.1.respects)]⟩
      ⟨hN,by simp only [step_merge_eq,(show (Term.record Fs).isValue = true from hv.right.1),
        (show (Term.record Gs).isValue = true from hw.right.1),Bool.not_true,Bool.false_eq_true,↓reduceIte,
        hFs.merge_check hGs (hd.subst hη.2.1.respects)]⟩
      (((hv.mono (by omega)).merge (hw.mono (by omega)) wr ws hη hd).toExpr)

theorem ExprRel.record_cons_value (hv : ValRel n a η v V)
    (hf : ExprRel n (.record r) η (ν,.record fs) (N,.record Fs))
    (wa : WellFormed Δ a) (wr : WellFormed Δ r) (hη : η.Valid Δ)
    (hd : Disjoint Δ (.field l a) r) :
    ExprRel n (.record (.union (.field l a) r)) η
      (ν,.record (.cons l v fs)) (N,.record (.cons l V Fs)) := by
  rw [ExprRel] at hf ⊢
  constructor
  · intro k hk w hw
    obtain ⟨gs,rfl,hgs⟩ := hw.record_cons_inv hv.left.1
    obtain ⟨W,hW,hrel⟩ := hf.1 k hk (.record gs) hgs
    obtain ⟨gs',Gs,hg,hG⟩ := hrel.record_inv
    cases hg
    cases hG
    exact ⟨.record (.cons l V Gs),hW.record_prepend hv.right.1,
      (hv.mono (Nat.sub_le _ _)).cons hrel wa wr hη hd⟩
  · intro k hk W hW
    obtain ⟨Gs,rfl,hGs⟩ := hW.record_cons_inv hv.right.1
    obtain ⟨v',hv',hrel⟩ := hf.2 k hk (.record Gs) hGs
    obtain ⟨gs,Gs',hg,hG⟩ := hrel.record_inv
    cases hg
    cases hG
    exact ⟨.record (.cons l v gs),hv'.record_prepend hv.left.1,
      (hv.mono (Nat.sub_le _ _)).cons hrel wa wr hη hd⟩

theorem ExprRel.record_cons (hx : ExprRel n a η (ν,x) (N,X))
    (hf : ExprRel n (.record r) η (ν,.record fs) (N,.record Fs))
    (wa : WellFormed Δ a) (wr : WellFormed Δ r) (hη : η.Valid Δ)
    (hd : Disjoint Δ (.field l a) r) :
    ExprRel n (.record (.union (.field l a) r)) η
      (ν,.record (.cons l x fs)) (N,.record (.cons l X Fs)) := by
  apply hx.bind strict_record_head strict_record_head
  intro i hi v V hv
  exact ExprRel.record_cons_value hv (hf.mono (Nat.sub_le _ _)) wa wr hη hd

theorem ExprRel.record_nil : ExprRel n (.record .empty) η (ν,.record .nil) (N,.record .nil) :=
  ValRel.record_nil.toExpr

end LeanSce.Target.Heterogeneous

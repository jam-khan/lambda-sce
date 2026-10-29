import LeanSce.Target.LogicalRelation.Contexts
import LeanSce.Target.LogicalRelation.Equality
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Safety
import LeanSce.Target.Metatheory.Values

/-!
# Target / LogicalRelation / Data

Proofs and supporting constructions for data.
-/

/-! ## Logical Relation Data -/

namespace LeanSce.Target

private theorem isValue_false_of_not_value (hn : ¬ Value e) : e.isValue = false := by
  cases h : e.isValue with
  | false => rfl
  | true => exact False.elim (hn h)

theorem strict_pair_left : StrictFrame ν (fun x => .pair x y) := by
  constructor
  · intro e hv; exact (Bool.and_eq_true_iff.mp hv).1
  · intro e hn; exact step_pair_left (isValue_false_of_not_value hn)

theorem strict_pair_right (hv : Value x) : StrictFrame ν (.pair x) := by
  constructor
  · intro e hw; exact (Bool.and_eq_true_iff.mp hw).2
  · intro e hn; exact step_pair_right hv (isValue_false_of_not_value hn)

theorem strict_fst : StrictFrame ν Term.fst := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_fst_eq,isValue_false_of_not_value hn]

theorem strict_snd : StrictFrame ν Term.snd := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_snd_eq,isValue_false_of_not_value hn]

theorem strict_inl : StrictFrame ν (.inl b) := ⟨fun _ hv => hv,fun _ _ => step_inl_eq⟩
theorem strict_inr : StrictFrame ν (.inr a) := ⟨fun _ hv => hv,fun _ _ => step_inr_eq⟩
theorem strict_tag : StrictFrame ν (.tag l) := ⟨fun _ hv => hv,fun _ _ => step_tag_eq⟩

theorem strict_get : StrictFrame ν (fun x => .get x l) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_get_eq,isValue_false_of_not_value hn]

theorem strict_find : StrictFrame ν (.find l) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_find_eq,isValue_false_of_not_value hn]

theorem strict_take : StrictFrame ν (.take ls) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_take_eq,isValue_false_of_not_value hn]

theorem strict_drop : StrictFrame ν (.drop ls) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_drop_eq,isValue_false_of_not_value hn]

theorem strict_relabel : StrictFrame ν (.relabel old new) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_relabel_eq,isValue_false_of_not_value hn]

theorem strict_merge_left : StrictFrame ν (fun x => .merge x y) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_merge_eq,isValue_false_of_not_value hn]

theorem strict_merge_right (hv : Value x) : StrictFrame ν (.merge x) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn; simp [step_merge_eq,(show x.isValue = true from hv),isValue_false_of_not_value hn]

theorem strict_ite : StrictFrame ν (fun c => .ite c x y) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_ite_eq,isValue_false_of_not_value hn]

theorem strict_case : StrictFrame ν (fun e => .case e l r) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_case_eq,isValue_false_of_not_value hn]

theorem strict_record_head : StrictFrame ν (fun x => .record (.cons l x fs)) := by
  constructor
  · intro e hv; exact (Bool.and_eq_true_iff.mp hv).1
  · intro e hn
    rw [step_record_eq,step_cons_left (isValue_false_of_not_value hn)]
    simp only [Option.map_map,Function.comp_def]

theorem strict_prim_left : StrictFrame ν (fun x => .prim p (.cons l x (.cons k y .nil))) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he := isValue_false_of_not_value hn
    rw [step_prim_eq]
    simp only [Term.isValue,he,Bool.false_and,Bool.not_false,↓reduceIte]
    rw [step_cons_left he]
    simp only [Option.map_map,Function.comp_def]

theorem strict_prim_right (hx : Value x) :
    StrictFrame ν (fun y => .prim p (.cons l x (.cons k y .nil))) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he := isValue_false_of_not_value hn
    rw [step_prim_eq]
    simp only [Term.isValue,(show x.isValue = true from hx),he,
      Bool.true_and,Bool.false_and,Bool.not_false,↓reduceIte]
    rw [step_cons_right hx (by simp [Term.isValue,he]),step_cons_left he]
    simp only [Option.map_map,Function.comp_def]

theorem strict_prim_one : StrictFrame ν (fun x => .prim p (.cons l x .nil)) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he := isValue_false_of_not_value hn
    rw [step_prim_eq]
    simp only [Term.isValue,he,Bool.false_and,Bool.not_false,↓reduceIte]
    rw [step_cons_left he]
    simp only [Option.map_map,Function.comp_def]

namespace LogicalRelation

theorem ValRel.left (hr : ValRel n a v w) : ValueType .empty v a := by rw [ValRel] at hr; exact hr.1
theorem ValRel.right (hr : ValRel n a v w) : ValueType .empty w a := by rw [ValRel] at hr; exact hr.2.1
theorem ValRel.shape (hr : ValRel n a v w) : ShapeRel n a v w := by rw [ValRel] at hr; exact hr.2.2

theorem ValRel.unit : ValRel n .unit .unit .unit := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨rfl,.unit .unit⟩,⟨rfl,.unit .unit⟩,rfl,rfl⟩

theorem ValRel.int : ValRel n .int (.int z) (.int z) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨rfl,.int .unit⟩,⟨rfl,.int .unit⟩,z,rfl,rfl⟩

theorem ValRel.bool : ValRel n .bool (.bool b) (.bool b) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨rfl,.bool .unit⟩,⟨rfl,.bool .unit⟩,b,rfl,rfl⟩

theorem ValRel.string : ValRel n .string (.string s) (.string s) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨rfl,.string .unit⟩,⟨rfl,.string .unit⟩,s,rfl,rfl⟩

theorem ValRel.pair (hx : ValRel n a x X) (hy : ValRel n b y Y) :
    ValRel n (.prod a b) (.pair x y) (.pair X Y) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨Bool.and_eq_true_iff.mpr ⟨hx.left.1,hy.left.1⟩,.pair hx.left.2 hy.left.2⟩,
    ⟨Bool.and_eq_true_iff.mpr ⟨hx.right.1,hy.right.1⟩,.pair hx.right.2 hy.right.2⟩,
    x,y,X,Y,rfl,rfl,hx,hy⟩

theorem ValRel.inl (hx : ValRel n a x X) (wb : WellFormed .empty b) :
    ValRel n (.sum a b) (.inl b x) (.inl b X) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨hx.left.1,.inl wb hx.left.2⟩,⟨hx.right.1,.inl wb hx.right.2⟩,
    Or.inl ⟨b,b,x,X,rfl,rfl,hx⟩⟩

theorem ValRel.inr (hy : ValRel n b y Y) (wa : WellFormed .empty a) :
    ValRel n (.sum a b) (.inr a y) (.inr a Y) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨hy.left.1,.inr wa hy.left.2⟩,⟨hy.right.1,.inr wa hy.right.2⟩,
    Or.inr ⟨a,a,y,Y,rfl,rfl,hy⟩⟩

theorem ValRel.tag (hx : ValRel n a x X) : ValRel n (.tag l a) (.tag l x) (.tag l X) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨hx.left.1,.tag hx.left.2⟩,⟨hx.right.1,.tag hx.right.2⟩,x,X,rfl,rfl,hx⟩

theorem ExprRel.query (hr : ValRel n h ν N) : ExprRel n h (ν,.query) (N,.query) := by
  cases n with
  | zero => exact ExprRel.zero
  | succ n =>
    exact ExprRel.step (query_step hr.left.1) (query_step hr.right.1)
      ((hr.mono (by omega)).toExpr)

theorem ExprRel.pair (hx : ExprRel n a (ν,x) (N,X)) (hy : ExprRel n b (ν,y) (N,Y)) :
    ExprRel n (.prod a b) (ν,.pair x y) (N,.pair X Y) := by
  apply hx.bind strict_pair_left strict_pair_left
  intro i hi v V hv
  apply (hy.mono (Nat.sub_le _ _)).bind (strict_pair_right hv.left.1) (strict_pair_right hv.right.1)
  intro j hj w W hw
  exact ((hv.mono (Nat.sub_le _ _)).pair hw).toExpr

theorem ExprRel.inl (hx : ExprRel n a (ν,x) (N,X)) (wb : WellFormed .empty b) :
    ExprRel n (.sum a b) (ν,.inl b x) (N,.inl b X) := by
  apply hx.bind strict_inl strict_inl
  intro i hi v V hv
  exact (hv.inl wb).toExpr

theorem ExprRel.inr (hy : ExprRel n b (ν,y) (N,Y)) (wa : WellFormed .empty a) :
    ExprRel n (.sum a b) (ν,.inr a y) (N,.inr a Y) := by
  apply hy.bind strict_inr strict_inr
  intro i hi v V hv
  exact (hv.inr wa).toExpr

theorem ExprRel.tag (hx : ExprRel n a (ν,x) (N,X)) :
    ExprRel n (.tag l a) (ν,.tag l x) (N,.tag l X) := by
  apply hx.bind strict_tag strict_tag
  intro i hi v V hv
  exact hv.tag.toExpr

theorem ExprRel.fst (hx : ExprRel n (.prod a b) (ν,x) (N,X))
    (hν : Value ν) (hN : Value N) : ExprRel n a (ν,.fst x) (N,.fst X) := by
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

theorem ExprRel.snd (hx : ExprRel n (.prod a b) (ν,x) (N,X))
    (hν : Value ν) (hN : Value N) : ExprRel n b (ν,.snd x) (N,.snd X) := by
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

private theorem binary_prim_rel (hx : ExprRel n a (ν,x) (N,X))
    (hy : ExprRel n b (ν,y) (N,Y))
    (hr : ∀ m v V w W, ValRel m a v V → ValRel m b w W →
      ExprRel m c (ν,.prim p (.cons l v (.cons k w .nil)))
        (N,.prim p (.cons l V (.cons k W .nil)))) :
    ExprRel n c (ν,.prim p (.cons l x (.cons k y .nil)))
      (N,.prim p (.cons l X (.cons k Y .nil))) := by
  apply hx.bind strict_prim_left strict_prim_left
  intro i hi v V hv
  apply (hy.mono (Nat.sub_le _ _)).bind (strict_prim_right hv.left.1) (strict_prim_right hv.right.1)
  intro j hj w W hw
  exact hr _ v V w W (hv.mono (Nat.sub_le _ _)) hw

theorem ExprRel.add (hx : ExprRel n .int (ν,x) (N,X))
    (hy : ExprRel n .int (ν,y) (N,Y)) (hν : Value ν) (hN : Value N) :
    ExprRel n .int (ν,.prim .add (.cons l x (.cons k y .nil)))
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

theorem ExprRel.eqInt (hx : ExprRel n .int (ν,x) (N,X))
    (hy : ExprRel n .int (ν,y) (N,Y)) (hν : Value ν) (hN : Value N) :
    ExprRel n .bool (ν,.prim .eqInt (.cons l x (.cons k y .nil)))
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

theorem ExprRel.concat (hx : ExprRel n .string (ν,x) (N,X))
    (hy : ExprRel n .string (ν,y) (N,Y)) (hν : Value ν) (hN : Value N) :
    ExprRel n .string (ν,.prim .concat (.cons l x (.cons k y .nil)))
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

theorem ExprRel.showInt (hx : ExprRel n .int (ν,x) (N,X))
    (hν : Value ν) (hN : Value N) :
    ExprRel n .string (ν,.prim .showInt (.cons l x .nil))
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

theorem ExprRel.ite (hc : ExprRel n .bool (ν,c) (N,C))
    (hx : ExprRel n a (ν,x) (N,X)) (hy : ExprRel n a (ν,y) (N,Y))
    (hν : Value ν) (hN : Value N) :
    ExprRel n a (ν,.ite c x y) (N,.ite C X Y) := by
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

theorem ValRel.record_inv (hr : ValRel n (.record r) v w) :
    ∃ fs gs, v = .record fs ∧ w = .record gs := by
  obtain ⟨fs,hfs⟩ := hr.left.2.value_shape hr.left.1
  obtain ⟨gs,hgs⟩ := hr.right.2.value_shape hr.right.1
  exact ⟨fs,gs,hfs,hgs⟩

theorem ValRel.lookup (hr : ValRel n (.record r) v w) (hl : r.lookup l = some a) :
    LookupRel n l a v w := by
  have hw := (hr.left.2.result_wf .empty).record_row
  have hs := hr.shape
  rw [ShapeRel] at hs
  exact (row_fields hw).mp hs l a (Ty.lookup_knownField r hl)

theorem ValRel.get (hr : ValRel n (.record r) (.record fs) (.record gs))
    (hl : r.lookup l = some a) :
    ∃ x X, fs.lookup l = some x ∧ gs.lookup l = some X ∧ ValRel n a x X := by
  obtain ⟨fs',gs',x,X,hf,hg,hl,hr,hx⟩ := hr.lookup hl
  cases hf
  cases hg
  exact ⟨x,X,hl,hr,hx⟩

theorem ValRel.of_record_lookups (hv : ValueType .empty v (.record r))
    (hw : ValueType .empty w (.record r))
    (hh : ∀ l a, (l,a) ∈ r.knownFields → LookupRel n l a v w) :
    ValRel n (.record r) v w := by
  rw [ValRel,ShapeRel]
  exact ⟨hv,hw,(row_fields (hv.2.result_wf .empty).record_row).mpr hh⟩

theorem ValRel.record_nil : ValRel n (.record .empty) (.record .nil) (.record .nil) := by
  rw [ValRel,ShapeRel,ShapeRel]
  exact ⟨⟨rfl,.record (.nil .unit)⟩,⟨rfl,.record (.nil .unit)⟩,True.intro⟩

theorem ValRel.take (hr : ValRel n (.record r) (.record fs) (.record gs)) (ls : List String) :
    ValRel n (.record (r.select ls)) (.record (fs.filter ls.contains)) (.record (gs.filter ls.contains)) := by
  have wr := (hr.left.2.result_wf .empty).record_row
  have hf := hr.left.2.value_record_inv hr.left.1 wr
  have hg := hr.right.2.value_record_inv hr.right.1 wr
  apply ValRel.of_record_lookups
    ⟨Term.filter_value fs hr.left.1,.record (hf.select .empty ls)⟩
    ⟨Term.filter_value gs hr.right.1,.record (hg.select .empty ls)⟩
  intro l a hm
  rw [Ty.knownFields_select] at hm
  obtain ⟨hm,hls⟩ := List.mem_filter.mp hm
  change ls.contains l = true at hls
  obtain ⟨x,X,hx,hX,hrel⟩ := hr.get (wr.knownField_lookup hm)
  exact ⟨_,_,x,X,rfl,rfl,by simp only [Term.lookup_filter,hls,↓reduceIte,hx],
    by simp only [Term.lookup_filter,hls,↓reduceIte,hX],hrel⟩

theorem ValRel.drop (hr : ValRel n (.record r) (.record fs) (.record gs)) (ls : List String) :
    ValRel n (.record (r.drop ls)) (.record (fs.filter (fun l => !ls.contains l)))
      (.record (gs.filter (fun l => !ls.contains l))) := by
  have wr := (hr.left.2.result_wf .empty).record_row
  have hf := hr.left.2.value_record_inv hr.left.1 wr
  have hg := hr.right.2.value_record_inv hr.right.1 wr
  apply ValRel.of_record_lookups
    ⟨Term.filter_value fs hr.left.1,.record (hf.drop .empty ls)⟩
    ⟨Term.filter_value gs hr.right.1,.record (hg.drop .empty ls)⟩
  intro l a hm
  rw [Ty.knownFields_drop] at hm
  obtain ⟨hm,hls⟩ := List.mem_filter.mp hm
  change (!ls.contains l) = true at hls
  obtain ⟨x,X,hx,hX,hrel⟩ := hr.get (wr.knownField_lookup hm)
  exact ⟨_,_,x,X,rfl,rfl,by simp only [Term.lookup_filter,hls,↓reduceIte,hx],
    by simp only [Term.lookup_filter,hls,↓reduceIte,hX],hrel⟩

theorem ValRel.merge (hr : ValRel n (.record r) (.record fs) (.record Fs))
    (hs : ValRel n (.record s) (.record gs) (.record Gs)) (hd : Disjoint .empty r s) :
    ValRel n (.record (.union r s)) (.record (fs.append gs)) (.record (Fs.append Gs)) := by
  have wr := (hr.left.2.result_wf .empty).record_row
  have ws := (hs.left.2.result_wf .empty).record_row
  have hf := hr.left.2.value_record_inv hr.left.1 wr
  have hF := hr.right.2.value_record_inv hr.right.1 wr
  have hg := hs.left.2.value_record_inv hs.left.1 ws
  have hG := hs.right.2.value_record_inv hs.right.1 ws
  apply ValRel.of_record_lookups
    ⟨Term.append_value fs hr.left.1 hs.left.1,.record (hf.append .empty hg hd)⟩
    ⟨Term.append_value Fs hr.right.1 hs.right.1,.record (hF.append .empty hG hd)⟩
  intro l a hm
  simp only [Ty.knownFields,List.mem_append] at hm
  rcases hm with hm | hm
  · obtain ⟨x,X,hx,hX,hrel⟩ := hr.get (wr.knownField_lookup hm)
    exact ⟨_,_,x,X,rfl,rfl,by simp [Term.lookup_append,hx],by simp [Term.lookup_append,hX],hrel⟩
  · have hl := ws.knownField_lookup hm
    obtain ⟨x,X,hx,hX,hrel⟩ := hs.get hl
    have hnone : fs.lookup l = none := Term.lookup_none_of_not_mem fs (by
      intro hm
      exact hd.knownLabels l (hf.labels_mem.mp hm) (Ty.lookup_mem s hl))
    have hNone : Fs.lookup l = none := Term.lookup_none_of_not_mem Fs (by
      intro hm
      exact hd.knownLabels l (hF.labels_mem.mp hm) (Ty.lookup_mem s hl))
    exact ⟨_,_,x,X,rfl,rfl,by simp [Term.lookup_append,hnone,hx],
      by simp [Term.lookup_append,hNone,hX],hrel⟩

theorem ValRel.relabel (hr : ValRel n (.record r) (.record fs) (.record gs))
    (hn : old ≠ new) (hd : Disjoint .empty (.field new b) (r.drop [old])) :
    ValRel n (.record (r.relabel old new)) (.record (fs.renameFields old new))
      (.record (gs.renameFields old new)) := by
  have wr := (hr.left.2.result_wf .empty).record_row
  have hf := hr.left.2.value_record_inv hr.left.1 wr
  have hg := hr.right.2.value_record_inv hr.right.1 wr
  have hnew := hd.relabel_fresh hn
  have hfsnew : new ∉ fs.labels := fun hm => hnew (hf.labels_mem.mp hm)
  have hgsnew : new ∉ gs.labels := fun hm => hnew (hg.labels_mem.mp hm)
  apply ValRel.of_record_lookups
    ⟨Term.renameFields_value fs hr.left.1,.record (hf.relabel .empty hd)⟩
    ⟨Term.renameFields_value gs hr.right.1,.record (hg.relabel .empty hd)⟩
  intro l a hm
  rw [Ty.knownFields_relabel] at hm
  obtain ⟨⟨q,c⟩,hq,heq⟩ := List.mem_map.mp hm
  have hqc : c = a := congrArg Prod.snd heq
  subst c
  have hql : (if q == old then new else q) = l := congrArg Prod.fst heq
  obtain ⟨x,X,hx,hX,hrel⟩ := hr.get (wr.knownField_lookup hq)
  by_cases hqo : q = old
  · subst q
    simp only [beq_self_eq_true,↓reduceIte] at hql
    subst l
    exact ⟨_,_,x,X,rfl,rfl,by rw [Term.lookup_rename_target fs hn hfsnew]; exact hx,
      by rw [Term.lookup_rename_target gs hn hgsnew]; exact hX,hrel⟩
  · have hqn : q ≠ new := by
      intro he
      subst q
      exact hnew (Ty.lookup_mem r (wr.knownField_lookup hq))
    have hql' : q = l := by simpa [hqo] using hql
    rw [← hql']
    exact ⟨_,_,x,X,rfl,rfl,by rw [Term.lookup_rename_other fs hqo hqn]; exact hx,
      by rw [Term.lookup_rename_other gs hqo hqn]; exact hX,hrel⟩

theorem ExprRel.get (he : ExprRel n (.record r) (ν,e) (N,E)) (hl : r.lookup l = some a)
    (hν : Value ν) (hN : Value N) : ExprRel n a (ν,.get e l) (N,.get E l) := by
  apply he.bind strict_get strict_get
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,gs,rfl,rfl⟩ := hv.record_inv
    obtain ⟨x,X,hx,hX,hrel⟩ := hv.get hl
    exact ExprRel.step
      ⟨hν,by simp [step_get_eq,(show (Term.record fs).isValue = true from hv.left.1),hx]⟩
      ⟨hN,by simp [step_get_eq,(show (Term.record gs).isValue = true from hv.right.1),hX]⟩
      ((hrel.mono (by omega)).toExpr)

theorem ExprRel.take (he : ExprRel n (.record r) (ν,e) (N,E))
    (hl : ∀ l ∈ ls, ∃ a, r.lookup l = some a) (hν : Value ν) (hN : Value N) :
    ExprRel n (.record (r.select ls)) (ν,.take ls e) (N,.take ls E) := by
  apply he.bind strict_take strict_take
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,gs,rfl,rfl⟩ := hv.record_inv
    have wr := (hv.left.2.result_wf .empty).record_row
    have hf := hv.left.2.value_record_inv hv.left.1 wr
    have hg := hv.right.2.value_record_inv hv.right.1 wr
    exact ExprRel.step
      ⟨hν,by simp [step_take_eq,(show (Term.record fs).isValue = true from hv.left.1),hf.selection_check _ hl]⟩
      ⟨hN,by simp [step_take_eq,(show (Term.record gs).isValue = true from hv.right.1),hg.selection_check _ hl]⟩
      (((hv.mono (by omega)).take ls).toExpr)

theorem ExprRel.drop (he : ExprRel n (.record r) (ν,e) (N,E))
    (hl : ∀ l ∈ ls, ∃ a, r.lookup l = some a) (hν : Value ν) (hN : Value N) :
    ExprRel n (.record (r.drop ls)) (ν,.drop ls e) (N,.drop ls E) := by
  apply he.bind strict_drop strict_drop
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,gs,rfl,rfl⟩ := hv.record_inv
    have wr := (hv.left.2.result_wf .empty).record_row
    have hf := hv.left.2.value_record_inv hv.left.1 wr
    have hg := hv.right.2.value_record_inv hv.right.1 wr
    exact ExprRel.step
      ⟨hν,by simp [step_drop_eq,(show (Term.record fs).isValue = true from hv.left.1),hf.selection_check _ hl]⟩
      ⟨hN,by simp [step_drop_eq,(show (Term.record gs).isValue = true from hv.right.1),hg.selection_check _ hl]⟩
      (((hv.mono (by omega)).drop ls).toExpr)

theorem ExprRel.relabel (he : ExprRel n (.record r) (ν,e) (N,E))
    (hl : r.lookup old = some a) (hne : old ≠ new)
    (hd : Disjoint .empty (.field new a) (r.drop [old])) (hν : Value ν) (hN : Value N) :
    ExprRel n (.record (r.relabel old new)) (ν,.relabel old new e) (N,.relabel old new E) := by
  apply he.bind strict_relabel strict_relabel
  intro i hi v V hv
  cases hn : n-i with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,gs,rfl,rfl⟩ := hv.record_inv
    have wr := (hv.left.2.result_wf .empty).record_row
    have hf := hv.left.2.value_record_inv hv.left.1 wr
    have hg := hv.right.2.value_record_inv hv.right.1 wr
    exact ExprRel.step
      ⟨hν,by simp only [step_relabel_eq,(show (Term.record fs).isValue = true from hv.left.1),Bool.not_true,Bool.false_eq_true,↓reduceIte,hf.relabel_check hl hne hd]⟩
      ⟨hN,by simp only [step_relabel_eq,(show (Term.record gs).isValue = true from hv.right.1),Bool.not_true,Bool.false_eq_true,↓reduceIte,hg.relabel_check hl hne hd]⟩
      (((hv.mono (by omega)).relabel hne hd).toExpr)

theorem ExprRel.merge (he : ExprRel n (.record r) (ν,e) (N,E))
    (hf : ExprRel n (.record s) (ν,f) (N,F)) (hd : Disjoint .empty r s)
    (hν : Value ν) (hN : Value N) :
    ExprRel n (.record (.union r s)) (ν,.merge e f) (N,.merge E F) := by
  apply he.bind strict_merge_left strict_merge_left
  intro i hi v V hv
  apply (hf.mono (Nat.sub_le _ _)).bind (strict_merge_right hv.left.1) (strict_merge_right hv.right.1)
  intro j hj w W hw
  cases hn : n-i-j with
  | zero => exact ExprRel.zero
  | succ m =>
    obtain ⟨fs,Fs,rfl,rfl⟩ := hv.record_inv
    obtain ⟨gs,Gs,rfl,rfl⟩ := hw.record_inv
    have wr := (hv.left.2.result_wf .empty).record_row
    have ws := (hw.left.2.result_wf .empty).record_row
    have hfs := hv.left.2.value_record_inv hv.left.1 wr
    have hFs := hv.right.2.value_record_inv hv.right.1 wr
    have hgs := hw.left.2.value_record_inv hw.left.1 ws
    have hGs := hw.right.2.value_record_inv hw.right.1 ws
    exact ExprRel.step
      ⟨hν,by simp only [step_merge_eq,(show (Term.record fs).isValue = true from hv.left.1),
        (show (Term.record gs).isValue = true from hw.left.1),Bool.not_true,Bool.false_eq_true,↓reduceIte,hfs.merge_check hgs hd]⟩
      ⟨hN,by simp only [step_merge_eq,(show (Term.record Fs).isValue = true from hv.right.1),
        (show (Term.record Gs).isValue = true from hw.right.1),Bool.not_true,Bool.false_eq_true,↓reduceIte,hFs.merge_check hGs hd]⟩
      (((hv.mono (by omega)).merge (hw.mono (by omega)) hd).toExpr)

theorem ValRel.find (hr : ValRel n a v V) (hu : Unique l a b) :
    ∃ w W, v.findTags l = [w] ∧ V.findTags l = [W] ∧ ValRel n b w W := by
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
    have habs := findTags_absent hy.left.2 hy.left.1 ha
    have hAbs := findTags_absent hy.right.2 hy.right.1 ha
    exact ⟨w,W,by simp [Term.findTags,hw,habs],by simp [Term.findTags,hW,hAbs],hrel⟩
  | right ha hu ih =>
    have hs := hr.shape
    rw [ShapeRel] at hs
    obtain ⟨x,y,X,Y,rfl,rfl,hx,hy⟩ := hs
    obtain ⟨w,W,hw,hW,hrel⟩ := ih hy
    have habs := findTags_absent hx.left.2 hx.left.1 ha
    have hAbs := findTags_absent hx.right.2 hx.right.1 ha
    exact ⟨w,W,by simp [Term.findTags,hw,habs],by simp [Term.findTags,hW,hAbs],hrel⟩

theorem ExprRel.find (he : ExprRel n a (ν,e) (N,E)) (hu : Unique l a b)
    (hν : Value ν) (hN : Value N) : ExprRel n b (ν,.find l e) (N,.find l E) := by
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

theorem ValRel.cons (hx : ValRel n a x X)
    (hf : ValRel n (.record r) (.record fs) (.record Fs))
    (hd : Disjoint .empty (.field l a) r) :
    ValRel n (.record (.union (.field l a) r)) (.record (.cons l x fs)) (.record (.cons l X Fs)) := by
  have wr := (hf.left.2.result_wf .empty).record_row
  have hfs := hf.left.2.value_record_inv hf.left.1 wr
  have hFs := hf.right.2.value_record_inv hf.right.1 wr
  apply ValRel.of_record_lookups
    ⟨(show Value (Term.record (.cons l x fs)) from Bool.and_eq_true_iff.mpr ⟨hx.left.1,hf.left.1⟩),.record (.cons hx.left.2 hfs hd)⟩
    ⟨(show Value (Term.record (.cons l X Fs)) from Bool.and_eq_true_iff.mpr ⟨hx.right.1,hf.right.1⟩),.record (.cons hx.right.2 hFs hd)⟩
  intro q b hm
  simp only [Ty.knownFields,List.mem_append,List.mem_singleton] at hm
  rcases hm with hm | hm
  · have he : q = l ∧ b = a := Prod.mk.inj hm
    rcases he with ⟨rfl,rfl⟩
    exact ⟨_,_,x,X,rfl,rfl,by simp [Term.lookup],by simp [Term.lookup],hx⟩
  · have hl := wr.knownField_lookup hm
    have hn : q ≠ l := by
      intro heq
      subst q
      exact hd.knownLabels l (by simp [Ty.knownLabels]) (Ty.lookup_mem r hl)
    obtain ⟨v,V,hv,hV,hrel⟩ := hf.get hl
    exact ⟨_,_,v,V,rfl,rfl,by simp [Term.lookup,hn,hv],by simp [Term.lookup,hn,hV],hrel⟩

/-- A completed head preserves the exact counted cost of tail initialization. -/
theorem ExprRel.record_cons_value (hv : ValRel n a v V)
    (hf : ExprRel n (.record r) (ν,.record fs) (N,.record Fs))
    (hd : Disjoint .empty (.field l a) r) :
    ExprRel n (.record (.union (.field l a) r))
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
      (hv.mono (Nat.sub_le _ _)).cons hrel hd⟩
  · intro k hk W hW
    obtain ⟨Gs,rfl,hGs⟩ := hW.record_cons_inv hv.right.1
    obtain ⟨v',hv',hrel⟩ := hf.2 k hk (.record Gs) hGs
    obtain ⟨gs,Gs',hg,hG⟩ := hrel.record_inv
    cases hg
    cases hG
    exact ⟨.record (.cons l v gs),hv'.record_prepend hv.left.1,
      (hv.mono (Nat.sub_le _ _)).cons hrel hd⟩

theorem ExprRel.record_cons (hx : ExprRel n a (ν,x) (N,X))
    (hf : ExprRel n (.record r) (ν,.record fs) (N,.record Fs))
    (hd : Disjoint .empty (.field l a) r) :
    ExprRel n (.record (.union (.field l a) r))
      (ν,.record (.cons l x fs)) (N,.record (.cons l X Fs)) := by
  apply hx.bind strict_record_head strict_record_head
  intro i hi v V hv
  exact ExprRel.record_cons_value hv (hf.mono (Nat.sub_le _ _)) hd

theorem ExprRel.record_nil : ExprRel n (.record .empty) (ν,.record .nil) (N,.record .nil) :=
  ValRel.record_nil.toExpr

end LogicalRelation
end LeanSce.Target

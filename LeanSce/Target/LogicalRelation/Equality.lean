import LeanSce.Target.Adapters.Typing
import LeanSce.Target.LogicalRelation.Properties
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Substitution
import LeanSce.Target.Metatheory.Values

/-!
# Target / LogicalRelation / Equality

Proofs and supporting constructions for equality.
-/

/-! ## Adapter Coherence Equality -/

namespace LeanSce.Target

theorem Ty.knownFields_payloads (r : Row) : (l,a) ∈ r.knownFields ↔ a ∈ r.payloads l := by
  cases r with
  | rvar => simp [Ty.knownFields,Ty.payloads]
  | empty => simp [Ty.knownFields,Ty.payloads]
  | field k b =>
    by_cases hl : l = k <;> simp [Ty.knownFields,Ty.payloads,hl]
  | union r s =>
    simp [Ty.knownFields,Ty.payloads,Ty.knownFields_payloads r,Ty.knownFields_payloads s]

theorem WellFormed.knownField_lookup (hw : WellFormed Δ r) (hm : (l,a) ∈ r.knownFields) :
    r.lookup l = some a := hw.payload_lookup ((Ty.knownFields_payloads r).mp hm)

theorem Ty.lookup_knownField (r : Row) (hl : r.lookup l = some a) : (l,a) ∈ r.knownFields :=
  (Ty.knownFields_payloads r).mpr (Ty.lookup_payload r hl)

theorem Ty.knownField_size (r : Row) (hm : (l,a) ∈ r.knownFields) : sizeOf a < sizeOf r := by
  cases r with
  | rvar => simp [Ty.knownFields] at hm
  | empty => simp [Ty.knownFields] at hm
  | field k b =>
    have he : l = k ∧ a = b := by simpa [Ty.knownFields] using hm
    rw [he.2]
    simp
    omega
  | union r s =>
    simp only [Ty.knownFields,List.mem_append] at hm
    rcases hm with hm | hm
    · have hh := Ty.knownField_size r hm; simp; omega
    · have hh := Ty.knownField_size s hm; simp; omega

namespace LogicalRelation

def LookupRel (n : Nat) (l : String) (a : Typ) (v w : Expr) : Prop :=
  ∃ fs gs x X, v = .record fs ∧ w = .record gs ∧
    fs.lookup l = some x ∧ gs.lookup l = some X ∧ ValRel n a x X

theorem row_fields (hw : WellFormed .empty r) :
    ShapeRel n r v w ↔ ∀ l a, (l,a) ∈ r.knownFields → LookupRel n l a v w := by
  cases hw with
  | rvar hi => simp [Context.empty] at hi
  | empty => simp [ShapeRel,Ty.knownFields]
  | field ha => simp [ShapeRel,Ty.knownFields,LookupRel]
  | union hr hs hd =>
    rw [ShapeRel, row_fields hr, row_fields hs]
    simp [Ty.knownFields,or_imp,forall_and]

theorem LookupRel.convert (he : ∀ x X, ValRel n a x X ↔ ValRel n b x X)
    (h : LookupRel n l a v w) : LookupRel n l b v w := by
  obtain ⟨fs,gs,x,X,hv,hw,hl,hr,hx⟩ := h
  exact ⟨fs,gs,x,X,hv,hw,hl,hr,(he x X).mp hx⟩

private theorem entails_open_eq (he : g = h ∨ GuardsEq g h) (u : Arg) :
    Entails .empty (g.open u) ↔ Entails .empty (h.open u) := by
  rcases he with rfl | he
  · rfl
  · exact he.entails_subst u.openSubst

/-- Closed structural type equality leaves the homogeneous relation invariant. -/
theorem equal_type (n : Nat) (wa : WellFormed .empty a) (wb : WellFormed .empty b)
    (he : TyEq a b) :
    (∀ v w, ValRel n a v w ↔ ValRel n b v w) ∧
    (∀ q r, ExprRel n a q r ↔ ExprRel n b q r) := by
  have hshape : ∀ v w, ShapeRel n a v w ↔ ShapeRel n b v w := by
    intro v w
    cases he.shape with
    | tvar => cases wa with | tvar hi => simp [Context.empty] at hi
    | unit | int | bool | string => rfl
    | @prod a b c d ha hb =>
      have hal := (equal_type n wa.prod_left wb.prod_left ha).1
      have hbr := (equal_type n wa.prod_right wb.prod_right hb).1
      simp only [ShapeRel]
      constructor <;> rintro ⟨x,y,X,Y,hv,hw,hx,hy⟩
      · exact ⟨x,y,X,Y,hv,hw,(hal _ _).mp hx,(hbr _ _).mp hy⟩
      · exact ⟨x,y,X,Y,hv,hw,(hal _ _).mpr hx,(hbr _ _).mpr hy⟩
    | @sum a b c d ha hb =>
      have hal := (equal_type n wa.sum_left wb.sum_left ha).1
      have hbr := (equal_type n wa.sum_right wb.sum_right hb).1
      simp only [ShapeRel]
      constructor
      · rintro (⟨t,t',x,X,hv,hw,hx⟩ | ⟨t,t',y,Y,hv,hw,hy⟩)
        · exact .inl ⟨t,t',x,X,hv,hw,(hal _ _).mp hx⟩
        · exact .inr ⟨t,t',y,Y,hv,hw,(hbr _ _).mp hy⟩
      · rintro (⟨t,t',x,X,hv,hw,hx⟩ | ⟨t,t',y,Y,hv,hw,hy⟩)
        · exact .inl ⟨t,t',x,X,hv,hw,(hal _ _).mpr hx⟩
        · exact .inr ⟨t,t',y,Y,hv,hw,(hbr _ _).mpr hy⟩
    | @tag a b l ha =>
      have hat := (equal_type n wa.tag_body wb.tag_body ha).1
      simp only [ShapeRel]
      constructor <;> rintro ⟨x,X,hv,hw,hx⟩
      · exact ⟨x,X,hv,hw,(hat _ _).mp hx⟩
      · exact ⟨x,X,hv,hw,(hat _ _).mpr hx⟩
    | @record r s hr =>
      have wr := wa.record_row
      have ws := wb.record_row
      rw [ShapeRel,ShapeRel,row_fields wr,row_fields ws]
      constructor
      · intro h l B hB
        have hlB := ws.knownField_lookup hB
        obtain ⟨A,hlA,hAB⟩ := hr.symm.lookup wr hlB
        have hA := Ty.lookup_knownField r hlA
        have hszA := Ty.knownField_size r hA
        have hszB := Ty.knownField_size s hB
        exact LookupRel.convert (equal_type n (wr.lookup hlA) (ws.lookup hlB) hAB.symm).1 (h l A hA)
      · intro h l A hA
        have hlA := wr.knownField_lookup hA
        obtain ⟨B,hlB,hAB⟩ := hr.lookup ws hlA
        have hB := Ty.lookup_knownField s hlB
        have hszA := Ty.knownField_size r hA
        have hszB := Ty.knownField_size s hB
        exact LookupRel.convert (fun x X => ((equal_type n (wr.lookup hlA) (ws.lookup hlB) hAB).1 x X).symm)
          (h l B hB)
    | @arr a b c d ha hb =>
      rw [ShapeRel,ShapeRel]
      constructor
      · intro h j hj x X hx
        have hx' := ((equal_type j wa.arr_left wb.arr_left ha).1 x X).mpr hx
        obtain ⟨q,r,hq,hr,hbodies⟩ := h j hj x X hx'
        exact ⟨q,r,hq,hr,((equal_type j wa.arr_right wb.arr_right hb).2 q r).mp hbodies⟩
      · intro h j hj x X hx
        have hx' := ((equal_type j wa.arr_left wb.arr_left ha).1 x X).mp hx
        obtain ⟨q,r,hq,hr,hbodies⟩ := h j hj x X hx'
        exact ⟨q,r,hq,hr,((equal_type j wa.arr_right wb.arr_right hb).2 q r).mpr hbodies⟩
    | @all k gs hs a b hg hab =>
      rw [ShapeRel,ShapeRel]
      constructor
      · intro h j hj u hk hu hgu
        have hga := (entails_open_eq hg u).mpr hgu
        obtain ⟨q,r,hq,hr,hbodies⟩ := h j hj u hk hu hga
        have wa' := wa.all_body.open Context.Valid.empty.normal hk hu hga
        have wb' := wb.all_body.open Context.Valid.empty.normal hk hu hgu
        exact ⟨q,r,hq,hr,((equal_type j wa' wb' (hab.subst wa.all_body u.openSubst)).2 q r).mp hbodies⟩
      · intro h j hj u hk hu hgu
        have hgb := (entails_open_eq hg u).mp hgu
        obtain ⟨q,r,hq,hr,hbodies⟩ := h j hj u hk hu hgb
        have wa' := wa.all_body.open Context.Valid.empty.normal hk hu hgu
        have wb' := wb.all_body.open Context.Valid.empty.normal hk hu hgb
        exact ⟨q,r,hq,hr,((equal_type j wa' wb' (hab.subst wa.all_body u.openSubst)).2 q r).mpr hbodies⟩
    | @ex k gs hs a b hg hab =>
      rw [ShapeRel,ShapeRel]
      constructor
      · rintro ⟨u,t,t',x,X,hv,hw,hk,hu,hgu,hx⟩
        have hgb := (entails_open_eq hg u).mp hgu
        refine ⟨u,t,t',x,X,hv,hw,hk,hu,hgb,?_⟩
        intro j hj
        exact ((equal_type j
          (wa.ex_body.open Context.Valid.empty.normal hk hu hgu)
          (wb.ex_body.open Context.Valid.empty.normal hk hu hgb)
          (hab.subst wa.ex_body u.openSubst)).1 x X).mp (hx j hj)
      · rintro ⟨u,t,t',x,X,hv,hw,hk,hu,hgu,hx⟩
        have hga := (entails_open_eq hg u).mpr hgu
        refine ⟨u,t,t',x,X,hv,hw,hk,hu,hga,?_⟩
        intro j hj
        exact ((equal_type j
          (wa.ex_body.open Context.Valid.empty.normal hk hu hga)
          (wb.ex_body.open Context.Valid.empty.normal hk hu hgu)
          (hab.subst wa.ex_body u.openSubst)).1 x X).mpr (hx j hj)
    | @mu a b hab =>
      have hga : Entails .empty (Ty.gnil.open (.type (.mu a))) := by simp [Entails,Ty.open,Ty.subst,Ty.guardAtoms]
      have hgb : Entails .empty (Ty.gnil.open (.type (.mu b))) := by simp [Entails,Ty.open,Ty.subst,Ty.guardAtoms]
      have wa' := wa.mu_body.open (u := .type (.mu a)) Context.Valid.empty.normal rfl wa hga
      have wb' := wb.mu_body.open (u := .type (.mu b)) Context.Valid.empty.normal rfl wb hgb
      have he' := hab.open_congr wa.mu_body (ArgEq.type (TyEq.mu hab))
      rw [ShapeRel,ShapeRel]
      constructor <;> rintro ⟨t,t',x,X,hv,hw,hx⟩
      · exact ⟨t,t',x,X,hv,hw,fun j hj => ((equal_type j wa' wb' he').1 x X).mp (hx j hj)⟩
      · exact ⟨t,t',x,X,hv,hw,fun j hj => ((equal_type j wa' wb' he').1 x X).mpr (hx j hj)⟩
  have hval : ∀ v w, ValRel n a v w ↔ ValRel n b v w := by
    intro v w
    rw [ValRel,ValRel]
    constructor
    · rintro ⟨hv,hw,hs⟩
      exact ⟨⟨hv.1,.conv hv.2 he wb⟩,⟨hw.1,.conv hw.2 he wb⟩,(hshape v w).mp hs⟩
    · rintro ⟨hv,hw,hs⟩
      exact ⟨⟨hv.1,.conv hv.2 he.symm wa⟩,⟨hw.1,.conv hw.2 he.symm wa⟩,(hshape v w).mpr hs⟩
  have hbudget : ∀ m, m ≤ n → ∀ v w, ValRel m a v w ↔ ValRel m b v w := by
    intro m hm v w
    by_cases heq : m = n
    · subst m; exact hval v w
    · exact (equal_type m wa wb he).1 v w
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

end LogicalRelation
end LeanSce.Target

/-! ## Adapter Antisymmetry -/

namespace LeanSce.Target

@[simp] theorem Ty.knownFields_keys (r : Row) : r.knownFields.map Prod.fst = r.knownLabels := by
  cases r with
  | rvar | empty | field => simp [Ty.knownFields,Ty.knownLabels]
  | union r s => simp [Ty.knownFields,Ty.knownLabels,Ty.knownFields_keys r,Ty.knownFields_keys s]

theorem TyEq.fieldsRow_ext (fs gs : List (String × Typ))
    (hnf : (fs.map Prod.fst).Nodup) (hng : (gs.map Prod.fst).Nodup)
    (hf : ∀ l a, (l,a) ∈ fs → ∃ b, (l,b) ∈ gs ∧ TyEq a b)
    (hg : ∀ l b, (l,b) ∈ gs → ∃ a, (l,a) ∈ fs) :
    TyEq (Ty.fieldsRow fs) (Ty.fieldsRow gs) := by
  induction fs generalizing gs with
  | nil =>
    cases gs with
    | nil => exact .refl
    | cons p gs =>
      obtain ⟨a,ha⟩ := hg p.1 p.2 (by simp)
      simp at ha
  | cons p fs ih =>
    obtain ⟨b,hb,hab⟩ := hf p.1 p.2 (by simp)
    obtain ⟨pre,post,rfl⟩ := List.append_of_mem hb
    let rest := pre ++ post
    have hp : (pre ++ (p.1,b)::post).Perm ((p.1,b)::rest) := List.perm_middle
    have hng' : (((p.1,b)::rest).map Prod.fst).Nodup := (hp.map Prod.fst).nodup_iff.mp hng
    have hnf' : p.1 ∉ fs.map Prod.fst ∧ (fs.map Prod.fst).Nodup := by simpa using hnf
    have hng'' : p.1 ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by simpa using hng'
    have hf' : ∀ l a, (l,a) ∈ fs → ∃ b, (l,b) ∈ rest ∧ TyEq a b := by
      intro l a ha
      obtain ⟨b,hb,hab⟩ := hf l a (by simp [ha])
      rcases List.mem_cons.mp (hp.mem_iff.mp hb) with he | hb
      · have hl : l = p.1 := congrArg Prod.fst he
        exact False.elim (hnf'.1 (hl ▸ List.mem_map.mpr ⟨(l,a),ha,rfl⟩))
      · exact ⟨b,hb,hab⟩
    have hg' : ∀ l b, (l,b) ∈ rest → ∃ a, (l,a) ∈ fs := by
      intro l b hb
      obtain ⟨a,ha⟩ := hg l b (hp.mem_iff.mpr (by simp [hb]))
      rcases List.mem_cons.mp ha with he | ha
      · have hl : l = p.1 := congrArg Prod.fst he
        exact False.elim (hng''.1 (hl ▸ List.mem_map.mpr ⟨(l,b),hb,rfl⟩))
      · exact ⟨a,ha⟩
    have ht := ih rest hnf'.2 hng''.2 hf' hg'
    have hs : TyEq (Ty.fieldsRow (p::fs)) (Ty.fieldsRow ((p.1,b)::rest)) := by
      simpa [Ty.fieldsRow,Ty.joinRows] using TyEq.union (.field hab) ht
    exact hs.trans (Ty.fieldsRow_perm hp.symm)

/-- Exact rows are equal when their explicit fields agree pointwise and their
    opaque tails have the same multiplicities. -/
theorem TyEq.row_ext (wr : WellFormed Δ r) (ws : WellFormed Γ s)
    (hp : r.tails.Perm s.tails)
    (hf : ∀ l a, (l,a) ∈ r.knownFields → ∃ b, (l,b) ∈ s.knownFields ∧ TyEq a b)
    (hg : ∀ l b, (l,b) ∈ s.knownFields → ∃ a, (l,a) ∈ r.knownFields) : TyEq r s := by
  have hfields := TyEq.fieldsRow_ext r.knownFields s.knownFields
    (by simpa using wr.knownLabels_nodup) (by simpa using ws.knownLabels_nodup) hf hg
  exact r.decompose.trans ((TyEq.union hfields (TyEq.joinRows_perm (hp.map Ty.rvar))).trans s.decompose.symm)

theorem AdaptsFields.member (hd : AdaptsFields Δ r fs es) (hm : (l,b) ∈ fs) :
    ∃ a c, r.lookup l = some a ∧ Adapts Δ a b c := by
  cases hd with
  | nil => simp at hm
  | @cons a Δ b c r fs es l hl hc hf =>
    rcases List.mem_cons.mp hm with he | hm
    · cases he; exact ⟨a,c,hl,hc⟩
    · exact AdaptsFields.member hf hm
termination_by fs.length

theorem Adapts.antisymm (hd : Adapts Δ a b c) (hr : Adapts Γ b a d) : TyEq a b := by
  cases hd with
  | equal _ _ he => exact he
  | arrow hn hdown hup =>
    cases hr with
    | equal _ _ he => exact he.symm
    | arrow _ hdown' hup' => exact .arr (Adapts.antisymm hdown hdown').symm (Adapts.antisymm hup hup')
  | sameTail wr ws hn hp hfs =>
    cases hr with
    | equal _ _ he => exact he.symm
    | closed _ _ _ _ hnp _ => exact False.elim (hnp hp.symm)
    | sameTail ws' wr' _ hp' hgs =>
      apply TyEq.record
      apply TyEq.row_ext wr.record_row ws.record_row hp
      · intro l a ha
        obtain ⟨b,cb,hlb,hba⟩ := hgs.member ((Ty.sortedFields_perm _).mem_iff.mpr ha)
        have hb := Ty.lookup_knownField _ hlb
        obtain ⟨a',ca,hla',hab⟩ := hfs.member ((Ty.sortedFields_perm _).mem_iff.mpr hb)
        have hla := wr.record_row.knownField_lookup ha
        have hea : a' = a := Option.some.inj (hla'.symm.trans hla)
        have hsa := Ty.knownField_size _ ha
        have hsb := Ty.knownField_size _ hb
        subst a'
        exact ⟨b,hb,Adapts.antisymm hab hba⟩
      · intro l b hb
        obtain ⟨a,ca,hla,hab⟩ := hfs.member ((Ty.sortedFields_perm _).mem_iff.mpr hb)
        exact ⟨a,Ty.lookup_knownField _ hla⟩
  | closed wr ws hn hs hnp hfs =>
    cases hr with
    | equal _ _ he => exact he.symm
    | sameTail _ _ _ hp _ => exact False.elim (hnp hp.symm)
    | closed _ _ _ ht _ _ =>
      exact False.elim (hnp (by simp [ht,hs]))
  | all wa wb hn hg hbody =>
    cases hr with
    | equal _ _ he => exact he.symm
    | all _ _ _ _ hbody' => exact .all hg (Adapts.antisymm hbody hbody')
termination_by sizeOf a + sizeOf b

decreasing_by
  all_goals simp_wf
  all_goals simp_all
  all_goals omega

end LeanSce.Target

/-! ## Record Lookup Properties -/

namespace LeanSce.Target

theorem Term.lookup_append (fs : Term s) (gs : Fields) (l : String) :
    (fs.append gs).lookup l = (fs.lookup l <|> gs.lookup l) := by
  cases fs with
  | cons k e rest =>
    by_cases hl : l = k <;> simp [Term.append,Term.lookup,hl,Term.lookup_append rest gs l]
  | _ => rfl

theorem Term.lookup_mem_labels (fs : Term s) (hl : fs.lookup l = some v) : l ∈ fs.labels := by
  cases fs with
  | cons k e rest =>
    by_cases he : l = k
    · simp [Term.labels,he]
    · have ht : rest.lookup l = some v := by simpa [Term.lookup,he] using hl
      exact List.mem_cons_of_mem k (Term.lookup_mem_labels rest ht)
  | _ => cases hl

theorem Term.lookup_none_of_not_mem (fs : Term s) (hl : l ∉ fs.labels) : fs.lookup l = none := by
  cases he : fs.lookup l with
  | none => rfl
  | some v => exact False.elim (hl (Term.lookup_mem_labels fs he))

theorem Term.lookup_filter (fs : Term s) (p : String → Bool) (l : String) :
    (fs.filter p).lookup l = if p l then fs.lookup l else none := by
  cases fs with
  | cons k e rest =>
    by_cases hl : l = k
    · subst k; cases hp : p l <;> simp [Term.filter,Term.lookup,hp,Term.lookup_filter rest p l]
    · cases hp : p k <;> simp [Term.filter,Term.lookup,hl,hp,Term.lookup_filter rest p l]
  | _ => cases p l <;> rfl

theorem Term.lookup_rename_target (fs : Term s) (hn : old ≠ new)
    (hfresh : new ∉ fs.labels) : (fs.renameFields old new).lookup new = fs.lookup old := by
  cases fs with
  | cons k e rest =>
    have hf : new ≠ k ∧ new ∉ rest.labels := by simpa [Term.labels] using hfresh
    by_cases hk : k = old
    · subst k; simp [Term.renameFields,Term.lookup]
    · simp [Term.renameFields,Term.lookup,hk,Ne.symm hk,hf.1,
        Term.lookup_rename_target rest hn hf.2]
  | _ => rfl

theorem Term.lookup_rename_other (fs : Term s) (ho : l ≠ old) (hn : l ≠ new) :
    (fs.renameFields old new).lookup l = fs.lookup l := by
  cases fs with
  | cons k e rest =>
    by_cases hk : k = old
    · subst k; simp [Term.renameFields,Term.lookup,ho,hn,Term.lookup_rename_other rest ho hn]
    · simp [Term.renameFields,Term.lookup,hk,Term.lookup_rename_other rest ho hn]
  | _ => rfl

theorem Ty.knownFields_select (r : Row) (ls : List String) :
    (r.select ls).knownFields = r.knownFields.filter (fun p => ls.contains p.1) := by
  cases r with
  | rvar => simp [Ty.select,Ty.knownFields]
  | empty => simp [Ty.select,Ty.knownFields]
  | field l a => by_cases hl : l ∈ ls <;> simp [Ty.select,Ty.knownFields,hl]
  | union r s => simp [Ty.select,Ty.knownFields,Ty.knownFields_select r,Ty.knownFields_select s]

theorem Ty.knownFields_drop (r : Row) (ls : List String) :
    (r.drop ls).knownFields = r.knownFields.filter (fun p => !ls.contains p.1) := by
  cases r with
  | rvar => simp [Ty.drop,Ty.knownFields]
  | empty => simp [Ty.drop,Ty.knownFields]
  | field l a => by_cases hl : l ∈ ls <;> simp [Ty.drop,Ty.knownFields,hl]
  | union r s => simp [Ty.drop,Ty.knownFields,Ty.knownFields_drop r,Ty.knownFields_drop s]

theorem Ty.knownFields_relabel (r : Row) (old new : String) :
    (r.relabel old new).knownFields =
      r.knownFields.map (fun p => (if p.1 == old then new else p.1,p.2)) := by
  cases r with
  | rvar => simp [Ty.relabel,Ty.knownFields]
  | empty => simp [Ty.relabel,Ty.knownFields]
  | field => simp [Ty.relabel,Ty.knownFields]
  | union r s => simp [Ty.relabel,Ty.knownFields,Ty.knownFields_relabel r,Ty.knownFields_relabel s]

theorem Disjoint.relabel_fresh {r : Row} (hd : Disjoint Δ (.field new a) (r.drop [old]))
    (hn : old ≠ new) : new ∉ r.knownLabels := by
  intro hm
  have he : Entry.label new ∈ r.entries := r.label_mem_entries.mpr hm
  have hdrop : Entry.label new ∈ (r.drop [old]).entries :=
    (r.entries_drop_one old).mpr ⟨he,by simpa using Ne.symm hn⟩
  exact hd.knownLabels new (by simp [Ty.knownLabels])
    ((r.drop [old]).label_mem_entries.mp hdrop)

end LeanSce.Target

/-! ## Adapter Cycle -/

namespace LeanSce.Target

private def TailsLift (a : Ty s) : List Nat :=
  match s with
  | .row => a.tails
  | _ => []

private theorem TyEq.tails_perm_aux (he : TyEq a b) :
    (TailsLift a).Perm (TailsLift b) := by
  induction he <;> simp only [TailsLift,Ty.tails] at *
  case refl => exact .refl _
  case symm ih => exact ih.symm
  case trans ih₁ ih₂ => exact ih₁.trans ih₂
  case union ih₁ ih₂ => exact ih₁.append ih₂
  case union_empty => simp
  case union_comm => exact List.perm_append_comm
  case union_assoc => simp [List.append_assoc]
  all_goals exact .refl _

/-- Row equality preserves the multiplicities of all opaque tails. -/
theorem TyEq.tails_perm (he : TyEq r s) : r.tails.Perm s.tails := he.tails_perm_aux

/-- A structural adaptation cycle closes only through equality, even when its
    endpoints use different equal presentations and independent static contexts. -/
theorem Adapts.cycle (h₁ : Adapts Δ a b c₁) (h₂ : Adapts Γ b t c₂)
    (he : TyEq a t) : TyEq a b := by
  cases h₁ with
  | equal _ _ hab => exact hab
  | arrow hn hdown hup =>
    cases h₂ with
    | equal _ _ hbt => exact he.trans hbt.symm
    | arrow _ hdown' hup' =>
      have harg := he.arr_inv.1
      have hres := he.arr_inv.2
      exact .arr (harg.trans (Adapts.cycle hdown' hdown harg.symm))
        (Adapts.cycle hup hup' hres)
  | sameTail wr ws hn hp hfs =>
    cases h₂ with
    | equal _ _ hbt => exact he.trans hbt.symm
    | closed _ _ _ _ hnp _ =>
      exact False.elim (hnp (hp.symm.trans he.record_inv.tails_perm))
    | sameTail ws' wt _ hp' hgs =>
      apply TyEq.record
      apply TyEq.row_ext wr.record_row ws.record_row hp
      · intro l a ha
        have hla := wr.record_row.knownField_lookup ha
        obtain ⟨t,hlt,hat⟩ := he.record_inv.lookup wt.record_row hla
        have ht := Ty.lookup_knownField _ hlt
        obtain ⟨b,cb,hlb,hbt⟩ := hgs.member ((Ty.sortedFields_perm _).mem_iff.mpr ht)
        have hb := Ty.lookup_knownField _ hlb
        obtain ⟨a',ca,hla',hab⟩ := hfs.member ((Ty.sortedFields_perm _).mem_iff.mpr hb)
        have hea : a' = a := Option.some.inj (hla'.symm.trans hla)
        have hsa := Ty.knownField_size _ ha
        have hsb := Ty.knownField_size _ hb
        have hst := Ty.knownField_size _ ht
        subst a'
        exact ⟨b,hb,Adapts.cycle hab hbt hat⟩
      · intro l b hb
        obtain ⟨a,ca,hla,hab⟩ := hfs.member ((Ty.sortedFields_perm _).mem_iff.mpr hb)
        exact ⟨a,Ty.lookup_knownField _ hla⟩
  | closed wr ws hn hs hnp hfs =>
    cases h₂ with
    | equal _ _ hbt => exact he.trans hbt.symm
    | sameTail _ _ _ hp _ =>
      exact False.elim (hnp (he.record_inv.tails_perm.trans hp.symm))
    | closed _ _ _ ht _ _ =>
      have hp := he.record_inv.tails_perm
      exact False.elim (hnp (by simpa only [ht,hs] using hp))
  | all wa wb hn hg hbody =>
    cases h₂ with
    | equal _ _ hbt => exact he.trans hbt.symm
    | all _ _ _ _ hbody' =>
      exact .all hg (Adapts.cycle hbody hbody' he.all_inv.2.2)
termination_by sizeOf a + sizeOf b + sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals simp_all
  all_goals omega

end LeanSce.Target

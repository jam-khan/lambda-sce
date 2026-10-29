import LeanSce.Target.Definitions.Statics
import LeanSce.Target.Definitions.Typing
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Constraints
import LeanSce.Target.Metatheory.Rows

/-!
# Target / Metatheory / Typing

Proofs and supporting constructions for typing.
-/

/-! ## Equality Properties -/

namespace LeanSce.Target

theorem GuardsEq.refl (hg : g.guardAtoms = some atoms) : GuardsEq g g :=
  ⟨atoms, atoms, hg, hg, fun _ => Iff.rfl⟩

theorem GuardsEq.symm (h : GuardsEq g g') : GuardsEq g' g := by
  obtain ⟨xs, ys, hx, hy, hm⟩ := h
  exact ⟨ys, xs, hy, hx, fun a => (hm a).symm⟩

theorem GuardsEq.trans (h₁ : GuardsEq g g') (h₂ : GuardsEq g' g'') : GuardsEq g g'' := by
  obtain ⟨xs, ys, hx, hy, hm⟩ := h₁
  obtain ⟨ys', zs, hy', hz, hn⟩ := h₂
  have he : ys = ys' := Option.some.inj (hy.symm.trans hy')
  subst ys'
  exact ⟨xs, zs, hx, hz, fun a => (hm a).trans (hn a)⟩

/-- The outer constructor of an ordinary type cannot change under row ACU
    conversion. Components retain the original structural equality relation. -/
inductive TypeShapeEq : Typ → Typ → Prop where
  | tvar : TypeShapeEq (.tvar i) (.tvar i)
  | unit : TypeShapeEq .unit .unit
  | int : TypeShapeEq .int .int
  | bool : TypeShapeEq .bool .bool
  | string : TypeShapeEq .string .string
  | prod : TyEq a a' → TyEq b b' → TypeShapeEq (.prod a b) (.prod a' b')
  | sum : TyEq a a' → TyEq b b' → TypeShapeEq (.sum a b) (.sum a' b')
  | arr : TyEq a a' → TyEq b b' → TypeShapeEq (.arr a b) (.arr a' b')
  | tag : TyEq a b → TypeShapeEq (.tag l a) (.tag l b)
  | record : TyEq r s → TypeShapeEq (.record r) (.record s)
  | all : (g = h ∨ GuardsEq g h) → TyEq a b → TypeShapeEq (.all k g a) (.all k h b)
  | ex : (g = h ∨ GuardsEq g h) → TyEq a b → TypeShapeEq (.ex k g a) (.ex k h b)
  | mu : TyEq a b → TypeShapeEq (.mu a) (.mu b)

theorem TypeShapeEq.refl (a : Typ) : TypeShapeEq a a := by
  cases a <;> constructor <;> first | exact TyEq.refl | exact Or.inl rfl

theorem TypeShapeEq.symm (h : TypeShapeEq a b) : TypeShapeEq b a := by
  cases h with
  | tvar => exact .tvar
  | unit => exact .unit
  | int => exact .int
  | bool => exact .bool
  | string => exact .string
  | prod ha hb => exact .prod ha.symm hb.symm
  | sum ha hb => exact .sum ha.symm hb.symm
  | arr ha hb => exact .arr ha.symm hb.symm
  | tag ha => exact .tag ha.symm
  | record ha => exact .record ha.symm
  | all hg ha => exact .all (hg.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)) ha.symm
  | ex hg ha => exact .ex (hg.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)) ha.symm
  | mu ha => exact .mu ha.symm

private theorem guards_trans (h₁ : g = h ∨ GuardsEq g h)
    (h₂ : h = i ∨ GuardsEq h i) : g = i ∨ GuardsEq g i := by
  rcases h₁ with rfl | h₁
  · exact h₂
  · rcases h₂ with rfl | h₂
    · exact Or.inr h₁
    · exact Or.inr (h₁.trans h₂)

theorem TypeShapeEq.trans (h₁ : TypeShapeEq a b) (h₂ : TypeShapeEq b c) : TypeShapeEq a c := by
  cases h₁ <;> cases h₂ <;> constructor
  all_goals first | exact TyEq.trans (by assumption) (by assumption)
                  | exact guards_trans (by assumption) (by assumption)

private def ShapeProperty {s : TySort} (a b : Ty s) : Prop :=
  match s with
  | .type => TypeShapeEq a b
  | _ => True

private theorem shape_property (h : TyEq a b) : ShapeProperty a b := by
  induction h with
  | @refl s a => cases s <;> first | exact TypeShapeEq.refl a | trivial
  | @symm s _ _ _ ih => cases s <;> first | exact TypeShapeEq.symm ih | trivial
  | @trans s _ _ _ _ _ ih₁ ih₂ => cases s <;> first | exact TypeShapeEq.trans ih₁ ih₂ | trivial
  | prod ha hb => exact .prod ha hb
  | sum ha hb => exact .sum ha hb
  | arr ha hb => exact .arr ha hb
  | tag ha => exact .tag ha
  | record hr => exact .record hr
  | all hg ha => exact .all (.inr hg) ha
  | ex hg ha => exact .ex (.inr hg) ha
  | mu ha => exact .mu ha
  | field | union | union_empty | union_comm | union_assoc => trivial

theorem TyEq.shape (h : TyEq (a : Typ) b) : TypeShapeEq a b := shape_property h

theorem TyEq.prod_inv (h : TyEq (.prod a b) (.prod c d)) : TyEq a c ∧ TyEq b d := by
  cases h.shape with | prod ha hb => exact ⟨ha, hb⟩

theorem TyEq.sum_inv (h : TyEq (.sum a b) (.sum c d)) : TyEq a c ∧ TyEq b d := by
  cases h.shape with | sum ha hb => exact ⟨ha, hb⟩

theorem TyEq.arr_inv (h : TyEq (.arr a b) (.arr c d)) : TyEq a c ∧ TyEq b d := by
  cases h.shape with | arr ha hb => exact ⟨ha, hb⟩

theorem TyEq.record_inv (h : TyEq (.record r) (.record s)) : TyEq r s := by
  cases h.shape with | record hr => exact hr

theorem TyEq.mu_inv (h : TyEq (.mu a) (.mu b)) : TyEq a b := by
  cases h.shape with | mu ha => exact ha

theorem TyEq.tag_inv (h : TyEq (.tag l a) (.tag k b)) : l = k ∧ TyEq a b := by
  cases h.shape with | tag ha => exact ⟨rfl, ha⟩

theorem TyEq.all_inv (h : TyEq (.all k g a) (.all k' g' b)) :
    k = k' ∧ (g = g' ∨ GuardsEq g g') ∧ TyEq a b := by
  cases h.shape with | all hg ha => exact ⟨rfl, hg, ha⟩

theorem TyEq.ex_inv (h : TyEq (.ex k g a) (.ex k' g' b)) :
    k = k' ∧ (g = g' ∨ GuardsEq g g') ∧ TyEq a b := by
  cases h.shape with | ex hg ha => exact ⟨rfl, hg, ha⟩

theorem TyEq.head_eq (h : TyEq (a : Typ) b) : a.head = b.head := by
  cases h.shape <;> rfl

end LeanSce.Target

/-! ## Typing Properties -/

namespace LeanSce.Target

theorem WellFormed.prod_left (h : WellFormed Δ (.prod a b)) : WellFormed Δ a := by
  cases h; assumption

theorem WellFormed.prod_right (h : WellFormed Δ (.prod a b)) : WellFormed Δ b := by
  cases h; assumption

theorem WellFormed.sum_left (h : WellFormed Δ (.sum a b)) : WellFormed Δ a := by
  cases h; assumption

theorem WellFormed.sum_right (h : WellFormed Δ (.sum a b)) : WellFormed Δ b := by
  cases h; assumption

theorem WellFormed.arr_left (h : WellFormed Δ (.arr a b)) : WellFormed Δ a := by
  cases h; assumption

theorem WellFormed.arr_right (h : WellFormed Δ (.arr a b)) : WellFormed Δ b := by
  cases h; assumption

theorem WellFormed.record_row (h : WellFormed Δ (.record r)) : WellFormed Δ r := by
  cases h; assumption

theorem WellFormed.tag_body (h : WellFormed Δ (.tag l a)) : WellFormed Δ a := by
  cases h; assumption

theorem WellFormed.all_body (h : WellFormed Δ (.all k gs a)) :
    WellFormed (Δ.extend k gs) a := by
  cases h; assumption

theorem WellFormed.ex_body (h : WellFormed Δ (.ex k gs a)) :
    WellFormed (Δ.extend k gs) a := by
  cases h; assumption

theorem WellFormed.mu_body (h : WellFormed Δ (.mu a)) :
    WellFormed (Δ.extend .type .gnil) a := by
  cases h; assumption

theorem Unique.wellFormed_result (hu : Unique l a b) (ha : WellFormed Δ a) :
    WellFormed Δ b := by
  induction hu with
  | here => exact ha.tag_body
  | left _ _ ih => exact ih ha.prod_left
  | right _ _ ih => exact ih ha.prod_right

/-- A typing derivation always supplies a well-formed native ambient. -/
theorem HasType.ambient_wf (ht : HasType Δ h e a) : WellFormed Δ h := by
  apply HasType.rec
    (motive_1 := fun Δ h _ _ _ => WellFormed Δ h)
    (motive_2 := fun Δ h _ _ _ => WellFormed Δ h)
    (t := ht)
  all_goals intros
  case recfn =>
    rename_i ih
    exact ih.prod_left.prod_left
  all_goals first | assumption | apply WellFormed.prod_left; assumption

end LeanSce.Target

/-! ## Value Typing -/

namespace LeanSce.Target

/-- Ambient independence of values is proved from typing, rather than assumed
    as an extra semantic principle. The mutual field case handles record values. -/
theorem HasType.value_reambient (ht : HasType Δ h e a) :
    Value e → ∀ h', WellFormed Δ h' → HasType Δ h' e a := by
  apply HasType.rec
    (motive_1 := fun Δ _ e a _ => Value e → ∀ h', WellFormed Δ h' → HasType Δ h' e a)
    (motive_2 := fun Δ _ fs r _ => Value fs → ∀ h', WellFormed Δ h' → FieldsType Δ h' fs r)
    (t := ht)
  all_goals intros
  all_goals simp_all only [Value, Term.isValue, Bool.and_eq_true, Bool.false_eq_true, false_implies]
  all_goals intros
  case unit => rename_i hh; exact .unit hh
  case int => rename_i hh; exact .int hh
  case bool => rename_i hh; exact .bool hh
  case string => rename_i hh; exact .string hh
  case pair =>
    rename_i ih₁ ih₂ hv h' hh
    exact .pair (ih₁ hv.1 h' hh) (ih₂ hv.2 h' hh)
  case inl =>
    rename_i wf _ ih hv h' hh
    exact .inl wf (ih hv h' hh)
  case inr =>
    rename_i wf _ ih hv h' hh
    exact .inr wf (ih hv h' hh)
  case tag =>
    rename_i ih hv h' hh
    exact .tag (ih hv h' hh)
  case record =>
    rename_i ih hv h' hh
    exact .record (ih hv h' hh)
  case pack =>
    rename_i wf hk hu hg _ ih hv h' hh
    exact .pack wf hk hu hg (ih hv h' hh)
  case fold =>
    rename_i wf _ ih hv h' hh
    exact .fold wf (ih hv h' hh)
  case clo =>
    rename_i wa vc tc tb _ _ _ _ hh
    exact .clo hh wa vc tc tb
  case rclo =>
    rename_i wa wb vc tc tb _ _ _ _ hh
    exact .rclo hh wa wb vc tc tb
  case tclo =>
    rename_i wa vc tc tb _ _ _ _ hh
    exact .tclo hh wa vc tc tb
  case value => trivial
  case nil => rename_i hh; exact .nil hh
  case cons =>
    rename_i hd ih₁ ih₂ hv h' hh
    exact .cons (ih₁ hv.1 h' hh) (ih₂ hv.2 h' hh) hd
  all_goals
    rename_i eq wf ih hv h' hh
    first | exact HasType.conv (ih hv h' hh) eq wf
          | exact FieldsType.conv (ih hv h' hh) eq wf

theorem valueType_of_typed_value (ht : HasType Δ h e a) (hv : Value e) : ValueType Δ e a :=
  ⟨hv, ht.value_reambient hv .unit .unit⟩

end LeanSce.Target

/-! ## Ambient Conversion -/

namespace LeanSce.Target

/-- Conversion of the native ambient changes query typing, without adding a
    dynamic environment argument or rewriting a program. -/
theorem HasType.ambient_convert (ht : HasType Δ h e a) :
    ∀ h', TyEq h h' → WellFormed Δ h' → HasType Δ h' e a := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ => ∀ h', TyEq h h' → WellFormed Δ h' → HasType Δ h' e a)
    (motive_2 := fun Δ h fs r _ => ∀ h', TyEq h h' → WellFormed Δ h' → FieldsType Δ h' fs r)
    (t := ht)
  all_goals intros
  all_goals intros
  case query => rename_i hh h' he hw; exact .conv (.query hw) he.symm hh
  case unit => rename_i h' he hw; exact .unit hw
  case int => rename_i h' he hw; exact .int hw
  case bool => rename_i h' he hw; exact .bool hw
  case string => rename_i h' he hw; exact .string hw
  case pair => rename_i ix iy h' he hw; exact .pair (ix h' he hw) (iy h' he hw)
  case fst => rename_i ih h' he hw; exact .fst (ih h' he hw)
  case snd => rename_i ih h' he hw; exact .snd (ih h' he hw)
  case box => rename_i hb ix iy h' he hw; exact .box (ix h' he hw) hb
  case lam =>
    rename_i wa hb ih h' he hw
    exact .lam wa (ih _ (.prod he .refl) (.prod hw wa))
  case recfn =>
    rename_i wa wb hb ih h' he hw
    exact .recfn wa wb (ih _ (.prod (.prod he .refl) .refl) (.prod (.prod hw (.arr wa wb)) wa))
  case app => rename_i ix iy h' he hw; exact .app (ix h' he hw) (iy h' he hw)
  case inl => rename_i wb hx ih h' he hw; exact .inl wb (ih h' he hw)
  case inr => rename_i wa hx ih h' he hw; exact .inr wa (ih h' he hw)
  case case =>
    rename_i hx hl hr ix il ir h' he hw
    exact .case (ix h' he hw)
      (il _ (.prod he .refl) (.prod hw hl.ambient_wf.prod_right))
      (ir _ (.prod he .refl) (.prod hw hr.ambient_wf.prod_right))
  case tag => rename_i ih h' he hw; exact .tag (ih h' he hw)
  case find => rename_i hu ih h' he hw; exact .find (ih h' he hw) hu
  case record => rename_i ih h' he hw; exact .record (ih h' he hw)
  case get => rename_i hl ih h' he hw; exact .get (ih h' he hw) hl
  case merge => rename_i hd ix iy h' he hw; exact .merge (ix h' he hw) (iy h' he hw) hd
  case take => rename_i hn hl ih h' he hw; exact .take (ih h' he hw) hn hl
  case drop => rename_i hn hl ih h' he hw; exact .drop (ih h' he hw) hn hl
  case relabel => rename_i hl hn hd ih h' he hw; exact .relabel (ih h' he hw) hl hn hd
  case tlam =>
    rename_i wa wh hb ih h' he hw
    exact .tlam wa hw (ih _ (he.rename Nat.succ) (hw.weaken _ _))
  case tapp => rename_i hk hu hg ih h' he hw; exact .tapp (ih h' he hw) hk hu hg
  case pack => rename_i wt hk hu hg hx ih h' he hw; exact .pack wt hk hu hg (ih h' he hw)
  case unpack =>
    rename_i hp wb hb ip ib h' he hw
    exact .unpack (ip h' he hw) wb
      (ib _ (.prod (he.rename Nat.succ) .refl) (.prod (hw.weaken _ _) hb.ambient_wf.prod_right))
  case fold => rename_i wt hx ih h' he hw; exact .fold wt (ih h' he hw)
  case unfold => rename_i ih h' he hw; exact .unfold (ih h' he hw)
  case add => rename_i ix iy h' he hw; exact .add (ix h' he hw) (iy h' he hw)
  case eqInt => rename_i ix iy h' he hw; exact .eqInt (ix h' he hw) (iy h' he hw)
  case showInt => rename_i ih h' he hw; exact .showInt (ih h' he hw)
  case concat => rename_i ix iy h' he hw; exact .concat (ix h' he hw) (iy h' he hw)
  case ite => rename_i ic ix iy h' he hw; exact .ite (ic h' he hw) (ix h' he hw) (iy h' he hw)
  case clo =>
    rename_i wa vc tc tb _ _ h' he hw
    exact .clo hw wa vc tc tb
  case rclo =>
    rename_i wa wb vc tc tb _ _ h' he hw
    exact .rclo hw wa wb vc tc tb
  case tclo =>
    rename_i wt vc tc tb _ _ h' he hw
    exact .tclo hw wt vc tc tb
  case value => rename_i hv ht wh ih h' he hw; exact .value hv ht hw
  case nil => rename_i h' he hw; exact .nil hw
  case cons => rename_i hd ix iy h' he hw; exact .cons (ix h' he hw) (iy h' he hw) hd
  all_goals
    rename_i eq wf ih h' he hw
    first | exact HasType.conv (ih h' he hw) eq wf
          | exact FieldsType.conv (ih h' he hw) eq wf

end LeanSce.Target

/-! ## Canonical Forms -/

namespace LeanSce.Target

theorem FieldsType.value_reambient (ht : FieldsType Δ h fs r) :
    Value fs → ∀ h', WellFormed Δ h' → FieldsType Δ h' fs r := by
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ _ fs r _ => Value fs → ∀ h', WellFormed Δ h' → FieldsType Δ h' fs r)
    (t := ht)
  all_goals intros
  all_goals try trivial
  case nil => intros _ _ hh; exact .nil hh
  case cons =>
    rename_i he _ hd _ ih
    intro hv h' hh
    simp only [Value, Term.isValue, Bool.and_eq_true] at hv
    exact .cons (he.value_reambient hv.1 h' hh) (ih hv.2 h' hh) hd
  case conv =>
    rename_i _ heq hw ih
    intro hv h' hh
    exact .conv (ih hv h' hh) heq hw

/-- A value's introducing derivation, with conversion collected at the end.
    Saved code keeps its original ambient and annotations. -/
inductive ValueOrigin (Δ : Context) : Expr → Typ → Prop where
  | unit : TyEq .unit a → ValueOrigin Δ .unit a
  | int : TyEq .int a → ValueOrigin Δ (.int n) a
  | bool : TyEq .bool a → ValueOrigin Δ (.bool b) a
  | string : TyEq .string a → ValueOrigin Δ (.string s) a
  | pair : ValueType Δ x ta → ValueType Δ y tb → TyEq (.prod ta tb) a →
      ValueOrigin Δ (.pair x y) a
  | inl : WellFormed Δ b → ValueType Δ x ta → TyEq (.sum ta b) a →
      ValueOrigin Δ (.inl b x) a
  | inr : WellFormed Δ ta → ValueType Δ y tb → TyEq (.sum ta tb) a →
      ValueOrigin Δ (.inr ta y) a
  | tag : ValueType Δ x ta → TyEq (.tag l ta) a → ValueOrigin Δ (.tag l x) a
  | record : Value fs → FieldsType Δ .unit fs r → TyEq (.record r) a →
      ValueOrigin Δ (.record fs) a
  | pack : WellFormed Δ (.ex k gs b) → u.kind = k → u.WellFormed Δ →
      Entails Δ (gs.open u) → ValueType Δ v (b.open u) → TyEq (.ex k gs b) a →
      ValueOrigin Δ (.pack u (.ex k gs b) v) a
  | fold : WellFormed Δ (.mu b) → ValueType Δ v (b.open (.type (.mu b))) →
      TyEq (.mu b) a → ValueOrigin Δ (.fold (.mu b) v) a
  | clo : WellFormed Δ arg → ValueType Δ cap env →
      HasType Δ (.prod env arg) body result → TyEq (.arr arg result) a →
      ValueOrigin Δ (.clo cap arg body) a
  | rclo : WellFormed Δ arg → WellFormed Δ result → ValueType Δ cap env →
      HasType Δ (.prod (.prod env (.arr arg result)) arg) body result →
      TyEq (.arr arg result) a → ValueOrigin Δ (.rclo cap arg result body) a
  | tclo : WellFormed Δ (.all k gs b) → ValueType Δ cap env →
      HasType (Δ.extend k gs) (env.rename Nat.succ) body b → TyEq (.all k gs b) a →
      ValueOrigin Δ (.tclo cap k gs body) a

theorem ValueOrigin.convert (ho : ValueOrigin Δ e a) (he : TyEq a b) : ValueOrigin Δ e b := by
  cases ho <;> constructor <;> first | assumption | exact TyEq.trans (by assumption) he

theorem HasType.value_origin (ht : HasType Δ h e a) : Value e → ValueOrigin Δ e a := by
  apply HasType.rec
    (motive_1 := fun Δ _ e a _ => Value e → ValueOrigin Δ e a)
    (motive_2 := fun _ _ _ _ _ => True)
    (t := ht)
  all_goals intros
  all_goals simp_all only [Value, Term.isValue, Bool.and_eq_true, Bool.false_eq_true, false_implies]
  all_goals intros
  all_goals try trivial
  case unit => exact .unit .refl
  case int => exact .int .refl
  case bool => exact .bool .refl
  case string => exact .string .refl
  case pair =>
    rename_i hx hy _ _ hv
    exact .pair (valueType_of_typed_value hx hv.1) (valueType_of_typed_value hy hv.2) .refl
  case inl =>
    rename_i hw hx _ hv
    exact .inl hw (valueType_of_typed_value hx hv) .refl
  case inr =>
    rename_i hw hx _ hv
    exact .inr hw (valueType_of_typed_value hx hv) .refl
  case tag =>
    rename_i hx _ hv
    exact .tag (valueType_of_typed_value hx hv) .refl
  case record =>
    rename_i hf hv
    exact .record hv (hf.value_reambient hv .unit .unit) .refl
  case pack =>
    rename_i hw hk hu hg hx _ hv
    exact .pack hw hk hu hg (valueType_of_typed_value hx hv) .refl
  case fold =>
    rename_i hw hx _ hv
    exact .fold hw (valueType_of_typed_value hx hv) .refl
  case clo =>
    rename_i wa vc tc tb _ _ hv
    exact .clo wa ⟨vc, tc⟩ tb .refl
  case rclo =>
    rename_i wa wb vc tc tb _ _ hv
    exact .rclo wa wb ⟨vc, tc⟩ tb .refl
  case tclo =>
    rename_i wa vc tc tb _ _ hv
    exact .tclo wa ⟨vc, tc⟩ tb .refl
  case conv =>
    rename_i he _ ih hv
    exact (ih hv).convert he

def ValueShape (e : Expr) : Head → Prop
  | .variable => False
  | .unit => e = .unit
  | .int => ∃ n, e = .int n
  | .bool => ∃ b, e = .bool b
  | .string => ∃ s, e = .string s
  | .prod => ∃ x y, e = .pair x y
  | .sum => ∃ t v, e = .inl t v ∨ e = .inr t v
  | .arr => (∃ c a b, e = .clo c a b) ∨ (∃ c a b body, e = .rclo c a b body)
  | .tag => ∃ l v, e = .tag l v
  | .record => ∃ fs, e = .record fs
  | .all => ∃ c k gs body, e = .tclo c k gs body
  | .ex => ∃ u t v, e = .pack u t v
  | .mu => ∃ t v, e = .fold t v

theorem ValueOrigin.shape (ho : ValueOrigin Δ e a) : ValueShape e a.head := by
  cases ho <;> rename_i heq
  all_goals rw [← heq.head_eq]
  all_goals simp [Ty.head, ValueShape]

theorem HasType.value_shape (ht : HasType Δ h e a) (hv : Value e) : ValueShape e a.head :=
  (ht.value_origin hv).shape

theorem HasType.value_record_inv (ht : HasType Δ h (.record fs) (.record r))
    (hv : Value (.record fs)) (hr : WellFormed Δ r) : FieldsType Δ .unit fs r := by
  cases ht.value_origin hv with
  | record _ hf he => exact .conv hf he.record_inv hr

end LeanSce.Target

/-! ## Regularity -/

namespace LeanSce.Target

/-- Typing supplies a well-formed result, including polymorphic eliminations. -/
theorem HasType.result_wf (ht : HasType Δ h e a) : Context.Valid Δ → WellFormed Δ a := by
  apply HasType.rec
    (motive_1 := fun Δ _ _ a _ => Context.Valid Δ → WellFormed Δ a)
    (motive_2 := fun Δ _ _ r _ => Context.Valid Δ → WellFormed Δ r)
    (t := ht)
  all_goals intros
  all_goals intros
  case query => assumption
  case unit => exact .unit
  case int => exact .int
  case bool => exact .bool
  case string => exact .string
  case pair => rename_i ihx ihy hΔ; exact .prod (ihx hΔ) (ihy hΔ)
  case fst => rename_i ih hΔ; exact (ih hΔ).prod_left
  case snd => rename_i ih hΔ; exact (ih hΔ).prod_right
  case box => rename_i iha ihb hΔ; exact ihb hΔ
  case lam => rename_i wa _ ih hΔ; exact .arr wa (ih hΔ)
  case recfn => rename_i wa wb _ ih hΔ; exact .arr wa wb
  case app => rename_i ihf ihx hΔ; exact (ihf hΔ).arr_right
  case inl => rename_i wb _ ih hΔ; exact .sum (ih hΔ) wb
  case inr => rename_i wa _ ih hΔ; exact .sum wa (ih hΔ)
  case case => rename_i iha ihl ihr hΔ; exact ihl hΔ
  case tag => rename_i ih hΔ; exact .tag (ih hΔ)
  case find => rename_i hu ih hΔ; exact hu.wellFormed_result (ih hΔ)
  case record => rename_i ih hΔ; exact .record (ih hΔ)
  case get => rename_i hl ih hΔ; exact (ih hΔ).record_row.lookup hl
  case merge => rename_i hd ihx ihy hΔ; exact .record (.union (ihx hΔ).record_row (ihy hΔ).record_row hd)
  case take => rename_i ih hΔ; exact .record ((ih hΔ).record_row.select _)
  case drop => rename_i ih hΔ; exact .record ((ih hΔ).record_row.drop _)
  case relabel => rename_i hd ih hΔ; exact .record ((ih hΔ).record_row.relabel hd)
  case tlam => assumption
  case tapp => rename_i hk hu hg ih hΔ; exact (ih hΔ).all_body.open hΔ.normal hk hu hg
  case pack => assumption
  case unpack => assumption
  case fold => assumption
  case unfold =>
    rename_i ih hΔ
    have hw := ih hΔ
    exact hw.mu_body.open hΔ.normal rfl hw (by simp [Entails, Ty.open, Ty.subst, Ty.guardAtoms])
  case add => exact .int
  case eqInt => exact .bool
  case showInt => exact .string
  case concat => exact .string
  case ite => rename_i ihc ihx ihy hΔ; exact ihx hΔ
  case clo => rename_i wa _ _ _ ihc ihb hΔ; exact .arr wa (ihb hΔ)
  case rclo => rename_i wa wb _ _ _ ihc ihb hΔ; exact .arr wa wb
  case tclo => assumption
  case value => rename_i _ ih hΔ; exact ih hΔ
  case nil => exact .empty
  case cons => rename_i hd ihe ihf hΔ; exact .union (.field (ihe hΔ)) (ihf hΔ) hd
  all_goals assumption

/-- Typing supplies a well-formed result, including polymorphic eliminations. -/
theorem FieldsType.result_wf (ht : FieldsType Δ h fs r) : Context.Valid Δ → WellFormed Δ r := by
  apply FieldsType.rec
    (motive_1 := fun Δ _ _ a _ => Context.Valid Δ → WellFormed Δ a)
    (motive_2 := fun Δ _ _ r _ => Context.Valid Δ → WellFormed Δ r)
    (t := ht)
  all_goals intros
  all_goals intros
  case query => assumption
  case unit => exact .unit
  case int => exact .int
  case bool => exact .bool
  case string => exact .string
  case pair => rename_i ihx ihy hΔ; exact .prod (ihx hΔ) (ihy hΔ)
  case fst => rename_i ih hΔ; exact (ih hΔ).prod_left
  case snd => rename_i ih hΔ; exact (ih hΔ).prod_right
  case box => rename_i iha ihb hΔ; exact ihb hΔ
  case lam => rename_i wa _ ih hΔ; exact .arr wa (ih hΔ)
  case recfn => rename_i wa wb _ ih hΔ; exact .arr wa wb
  case app => rename_i ihf ihx hΔ; exact (ihf hΔ).arr_right
  case inl => rename_i wb _ ih hΔ; exact .sum (ih hΔ) wb
  case inr => rename_i wa _ ih hΔ; exact .sum wa (ih hΔ)
  case case => rename_i iha ihl ihr hΔ; exact ihl hΔ
  case tag => rename_i ih hΔ; exact .tag (ih hΔ)
  case find => rename_i hu ih hΔ; exact hu.wellFormed_result (ih hΔ)
  case record => rename_i ih hΔ; exact .record (ih hΔ)
  case get => rename_i hl ih hΔ; exact (ih hΔ).record_row.lookup hl
  case merge => rename_i hd ihx ihy hΔ; exact .record (.union (ihx hΔ).record_row (ihy hΔ).record_row hd)
  case take => rename_i ih hΔ; exact .record ((ih hΔ).record_row.select _)
  case drop => rename_i ih hΔ; exact .record ((ih hΔ).record_row.drop _)
  case relabel => rename_i hd ih hΔ; exact .record ((ih hΔ).record_row.relabel hd)
  case tlam => assumption
  case tapp => rename_i hk hu hg ih hΔ; exact (ih hΔ).all_body.open hΔ.normal hk hu hg
  case pack => assumption
  case unpack => assumption
  case fold => assumption
  case unfold =>
    rename_i ih hΔ
    have hw := ih hΔ
    exact hw.mu_body.open hΔ.normal rfl hw (by simp [Entails, Ty.open, Ty.subst, Ty.guardAtoms])
  case add => exact .int
  case eqInt => exact .bool
  case showInt => exact .string
  case concat => exact .string
  case ite => rename_i ihc ihx ihy hΔ; exact ihx hΔ
  case clo => rename_i wa _ _ _ ihc ihb hΔ; exact .arr wa (ihb hΔ)
  case rclo => rename_i wa wb _ _ _ ihc ihb hΔ; exact .arr wa wb
  case tclo => assumption
  case value => rename_i _ ih hΔ; exact ih hΔ
  case nil => exact .empty
  case cons => rename_i hd ihe ihf hΔ; exact .union (.field (ihe hΔ)) (ihf hΔ) hd
  all_goals assumption

end LeanSce.Target

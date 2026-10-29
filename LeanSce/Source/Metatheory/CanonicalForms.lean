import LeanSce.Source.Definitions.Semantics
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.Substitution
import LeanSce.Source.Metatheory.WellFormedness

/-!
# Source / Metatheory / CanonicalForms

Proofs and supporting constructions for canonical forms.
-/

/-! ## Ambient Conversion -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort)

/-- Conversion of the native ambient changes query typing, without adding a
    dynamic environment argument or rewriting a program. -/
theorem HasType.ambient_convert (ht : HasType Δ h e a) :
    ∀ h', TyEq h h' → WellFormed Δ h' → HasType Δ h' e a := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ => ∀ h', TyEq h h' → WellFormed Δ h' → HasType Δ h' e a)
    (motive_2 := fun Δ h fs r _ => ∀ h', TyEq h h' → WellFormed Δ h' → FieldsType Δ h' fs r)
    (motive_3 := fun _ _ _ _ _ => True)
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
  case letVal => rename_i wa hx hb ix ib h' he hw; exact .letVal wa (ix h' he hw) (ib _ (.prod he .refl) (.prod hw wa))
  case view => rename_i hx hc ix _ h' he hw; exact .view (ix h' he hw) hc
  case module => rename_i hh wi wo hb ib h' he hw; exact .module hw wi wo hb
  case capture => rename_i hc wi wo hd hb ic ib h' he hw; exact .capture (ic h' he hw) wi wo hd hb
  case run => rename_i hm hp hc im ip _ h' he hw; exact .run (im h' he hw) (ip h' he hw) hc
  case link => rename_i hp hm hc hd ip im _ h' he hw; exact .link (ip h' he hw) (im h' he hw) hc hd
  case provide => rename_i hp hm hc wj wk hd ip im _ h' he hw; exact .provide (ip h' he hw) (im h' he hw) hc wj wk hd
  case complete => rename_i hm im h' he hw; exact .complete (im h' he hw)
  case moduleVal => rename_i hh vc hc wi wo hd hb ic ib h' he hw; exact .moduleVal hw vc hc wi wo hd hb
  case resid => rename_i vm hm hs wj wk hd im iss h' he hw; exact .resid vm hm (iss h' he hw) wj wk hd
  case invoke => rename_i hm hp im ip h' he hw; exact .invoke (im h' he hw) (ip h' he hw)
  case closed => trivial
  case value => rename_i hv ht wh ih h' he hw; exact .value hv ht hw
  case nil => rename_i h' he hw; exact .nil hw
  case cons => rename_i hd ix iy h' he hw; exact .cons (ix h' he hw) (iy h' he hw) hd
  all_goals
    rename_i eq wf ih h' he hw
    first | exact HasType.conv (ih h' he hw) eq wf
          | exact FieldsType.conv (ih h' he hw) eq wf

end LeanSce.Source

/-! ## Canonical Forms -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort)

theorem FieldsType.value_reambient (ht : FieldsType Δ h fs r) :
    Value fs → ∀ h', WellFormed Δ h' → FieldsType Δ h' fs r := by
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ _ fs r _ => Value fs → ∀ h', WellFormed Δ h' → FieldsType Δ h' fs r)
    (motive_3 := fun _ _ _ _ _ => True)
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
  | moduleVal : WellFormed Δ i → WellFormed Δ o → Disjoint Δ c i →
      ValueType Δ cap (.record c) → HasType Δ (.record (.union c i)) body (.record o) →
      TyEq (.module i o) a → ValueOrigin Δ (.moduleVal cap c i o body) a
  | resid : ValueType Δ m (.module (.union j k) o) → ValueType Δ saved (.record j) →
      WellFormed Δ j → WellFormed Δ k → Disjoint Δ j k → TyEq (.module k o) a →
      ValueOrigin Δ (.resid m saved j k o) a

theorem ValueOrigin.convert (ho : ValueOrigin Δ e a) (he : TyEq a b) : ValueOrigin Δ e b := by
  cases ho <;> constructor <;> first | assumption | exact TyEq.trans (by assumption) he

theorem HasType.value_origin (ht : HasType Δ h e a) : Value e → ValueOrigin Δ e a := by
  apply HasType.rec
    (motive_1 := fun Δ _ e a _ => Value e → ValueOrigin Δ e a)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
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
  case moduleVal =>
    rename_i vc hc wi wo hd hb ihc ihb hv
    exact .moduleVal wi wo hd ⟨vc,hc⟩ hb .refl
  case resid =>
    rename_i vm hm hs wj wk hd ihm ihs hv
    exact .resid ⟨vm,hm⟩ (valueType_of_typed_value hs hv.2) wj wk hd .refl
  case conv =>
    rename_i he _ ih hv
    exact (ih hv).convert he

def ValueShape (e : Expr) : Head → Prop
  | .module => (∃ cap c i o body, e = .moduleVal cap c i o body) ∨
      (∃ m saved j k o, e = .resid m saved j k o)
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

end LeanSce.Source

/-! ## Activation -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort)

/-- Unfolding a value respects conversion of the recursive type annotation. -/
theorem fold_payload_typed (hΔ : Context.Valid Δ)
    (ht : HasType Δ h (.fold t v) (.mu a)) (hv : Value (.fold t v)) :
    HasType Δ h v (a.open (.type (.mu a))) := by
  cases ht.value_origin hv with
  | fold hw hval he =>
    exact .conv (hval.inclusion ht.ambient_wf)
      (he.mu_inv.open_congr hw.mu_body (.type he))
      ((HasType.unfold ht).result_wf hΔ)

private theorem all_context_valid (hΔ : Context.Valid Δ)
    (hw : WellFormed Δ (.all k gs a)) : Context.Valid (Δ.extend k gs) := by
  cases hw with | all hf hg _ => exact .extend hΔ hf hg

private theorem ex_context_valid (hΔ : Context.Valid Δ)
    (hw : WellFormed Δ (.ex k gs a)) : Context.Valid (Δ.extend k gs) := by
  cases hw with | ex hf hg _ => exact .extend hΔ hf hg

/-- Activating a type closure uses its saved ambient and the instantiated body. -/
theorem tapp_tclo_typed (hΔ : Context.Valid Δ)
    (ht : HasType Δ h (.tclo cap k₀ gs₀ body) (.all k gs a))
    (hv : Value (.tclo cap k₀ gs₀ body))
    (hk : u.kind = k) (hu : u.WellFormed Δ) (hg : Entails Δ (gs.open u)) :
    HasType Δ h (.box cap (body.subst u.openSubst)) (a.open u) := by
  cases ht.value_origin hv with
  | tclo hw hc hb he =>
    obtain ⟨hekind, heguards, hebody⟩ := he.all_inv
    cases hekind
    have hg₀ : Entails Δ (gs₀.open u) := by
      rcases heguards with rfl | heguards
      · exact hg
      · exact (heguards.entails_subst u.openSubst).mpr hg
    have hopened := hb.open (all_context_valid hΔ hw) hΔ.normal hk hu hg₀
    simp only [Ty.open_weaken] at hopened
    exact .box (hc.inclusion ht.ambient_wf)
      (.conv hopened (hebody.subst hw.all_body u.openSubst)
        ((HasType.tapp ht hk hu hg).result_wf hΔ))

private theorem open_prod (a b : Typ) (u : Arg) :
    (Ty.prod a b).open u = .prod (a.open u) (b.open u) := rfl

/-- Existential elimination opens the client once with the package's witness. -/
theorem unpack_pack_typed (hΔ : Context.Valid Δ)
    (hp : HasType Δ h (.pack u t v) (.ex k gs a)) (hv : Value (.pack u t v))
    (hν : ValueType Δ ν h) (_wb : WellFormed Δ b)
    (hb : HasType (Δ.extend k gs) (.prod (h.rename Nat.succ) a) body (b.rename Nat.succ)) :
    HasType Δ h (.box (.pair ν v) (body.subst u.openSubst)) b := by
  cases hp.value_origin hv with
  | pack hw hk hu hg hx he =>
    obtain ⟨hekind, heguards, hebody⟩ := he.ex_inv
    cases hekind
    have hg' : Entails Δ (gs.open u) := by
      rcases heguards with rfl | heguards
      · exact hg
      · exact (heguards.entails_subst u.openSubst).mp hg
    have hrequested := hp.result_wf hΔ
    have hopened := hb.open (ex_context_valid hΔ hrequested) hΔ.normal hk hu hg'
    have hbody : HasType Δ (.prod h (a.open u)) (body.subst u.openSubst) b := by
      simpa only [open_prod, Ty.open_weaken] using hopened
    have hx' : HasType Δ h v (a.open u) :=
      .conv (hx.inclusion hp.ambient_wf) (hebody.subst hw.ex_body u.openSubst)
        (hrequested.ex_body.open hΔ.normal hk hu hg')
    exact .box (.pair (hν.inclusion hp.ambient_wf) hx') hbody

end LeanSce.Source

/-! ## Legacy Properties -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

theorem Absent.of_tyEq (he : TyEq a b) (hb : Absent l b) : Absent l a := by
  induction hb generalizing a with
  | unit => cases he.shape; exact .unit
  | int => cases he.shape; exact .int
  | bool => cases he.shape; exact .bool
  | string => cases he.shape; exact .string
  | arr => cases he.shape; exact .arr
  | module => cases he.shape; exact .module
  | sum => cases he.shape; exact .sum
  | record => cases he.shape; exact .record
  | all => cases he.shape; exact .all
  | ex => cases he.shape; exact .ex
  | mu => cases he.shape; exact .mu
  | tag hn => cases he.shape; exact .tag hn
  | prod _ _ ih₁ ih₂ =>
    cases he.shape with
    | prod hl hr => exact .prod (ih₁ hl) (ih₂ hr)

/-- Equality conversion preserves both uniqueness and the found payload type. -/
theorem Unique.of_tyEq (he : TyEq a b) (hu : Unique l b c) :
    ∃ d, Unique l a d ∧ TyEq d c := by
  induction hu generalizing a with
  | here =>
    cases he.shape with
    | tag hab => exact ⟨_, .here, hab⟩
  | left _ hn ih =>
    cases he.shape with
    | prod hl hr =>
      obtain ⟨d, hd, heq⟩ := ih hl
      exact ⟨d, .left hd (Absent.of_tyEq hr hn), heq⟩
  | right hn _ ih =>
    cases he.shape with
    | prod hl hr =>
      obtain ⟨d, hd, heq⟩ := ih hr
      exact ⟨d, .right (Absent.of_tyEq hl hn) hd, heq⟩

theorem findTags_absent (ht : HasType Δ h v a) (hv : Value v) (ha : Absent l a) :
    v.findTags l = [] := by
  cases v with
  | pair x y =>
    cases ht.value_origin hv with
    | pair hx hy he =>
      cases Absent.of_tyEq he ha with
      | prod hal har =>
        simp only [Term.findTags, findTags_absent hx.2 hx.1 hal,
          findTags_absent hy.2 hy.1 har, List.nil_append]
  | tag k x =>
    cases ht.value_origin hv with
    | tag _ he =>
      cases Absent.of_tyEq he ha with
      | tag hn => simp [Term.findTags, Ne.symm hn]
  | _ => rfl
termination_by sizeOf v

/-- Native tag lookup finds exactly one typed value in the product/tag tree. -/
theorem findTags_unique (ht : HasType Δ h v a) (hv : Value v) (hu : Unique l a b)
    (hb : WellFormed Δ b) (hΔ : Context.Valid Δ) :
    ∃ w, v.findTags l = [w] ∧ ValueType Δ w b := by
  cases v with
  | pair x y =>
    cases ht.value_origin hv with
    | pair hx hy he =>
      obtain ⟨c, hc, heq⟩ := Unique.of_tyEq he hu
      cases hc with
      | left hul har =>
        have hcwf := hul.wellFormed_result (hx.2.result_wf hΔ)
        obtain ⟨w, hw, hwt⟩ := findTags_unique hx.2 hx.1 hul hcwf hΔ
        exact ⟨w, by simp [Term.findTags, hw, findTags_absent hy.2 hy.1 har],
          hwt.1, .conv hwt.2 heq hb⟩
      | right hal hur =>
        have hcwf := hur.wellFormed_result (hy.2.result_wf hΔ)
        obtain ⟨w, hw, hwt⟩ := findTags_unique hy.2 hy.1 hur hcwf hΔ
        exact ⟨w, by simp [Term.findTags, hw, findTags_absent hx.2 hx.1 hal],
          hwt.1, .conv hwt.2 heq hb⟩
  | tag k x =>
    cases ht.value_origin hv with
    | tag hx he =>
      obtain ⟨c, hc, heq⟩ := Unique.of_tyEq he hu
      cases hc with
      | here => exact ⟨x, by simp [Term.findTags], hx.1, .conv hx.2 heq hb⟩
  | _ =>
    have ho := ht.value_origin hv
    cases ho <;> rename_i he
    all_goals obtain ⟨_, hc, _⟩ := Unique.of_tyEq he hu
    all_goals cases hc
termination_by sizeOf v

end LeanSce.Source

/-! ## Module Reductions -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort)

theorem CertType.typed (hc : CertType Δ a b cd) (hh : WellFormed Δ h) :
    HasType Δ h cd (.arr a b) := by
  cases hc with | closed _ ht => exact .box (.unit hh) ht

theorem empty_identity_cert (Δ : Context) :
    CertType Δ (.record .empty) (.record .empty) (.close (.lam (.record .empty) (.ix 0))) := by
  exact .closed rfl (.lam (.record .empty) (.snd (.query (.prod .unit (.record .empty)))))

private theorem empty_union_eq (r : Row) : TyEq r (.union .empty r) :=
  .trans (TyEq.symm TyEq.union_empty) TyEq.union_comm

theorem module_activation (hh : WellFormed Δ h) (wi : WellFormed Δ i) (wo : WellFormed Δ o)
    (hb : HasType Δ (.record i) body (.record o)) :
    HasType Δ h (.moduleVal (.record .nil) .empty i o body) (.module i o) := by
  apply HasType.moduleVal (cap := .record .nil) hh rfl (.record (.nil .unit)) wi wo (disjoint_empty_left _ _)
  exact hb.ambient_convert _ (.record (empty_union_eq i))
    (.record (.union .empty wi (disjoint_empty_left _ _)))

theorem invoke_moduleVal_typed (hm : HasType Δ h (.moduleVal cap c i₀ o₀ body) (.module i o))
    (hv : Value (.moduleVal cap c i₀ o₀ body))
    (hp : HasType Δ h imports (.record i)) (hΔ : Context.Valid Δ) :
    HasType Δ h (.box (.merge cap imports) body) (.record o) := by
  cases hm.value_origin hv with
  | moduleVal wi wo hd hc hb he =>
    have heq := he.module_inv
    apply HasType.box (.merge (hc.inclusion hm.ambient_wf)
      (.conv hp (.record heq.1.symm) (.record wi)) hd)
    exact .conv hb (.record heq.2) (.record (hm.result_wf hΔ).module_exports)

theorem invoke_resid_typed (hm : HasType Δ h (.resid m saved j k o₀) (.module i o))
    (hv : Value (.resid m saved j k o₀))
    (hp : HasType Δ h imports (.record i)) (hΔ : Context.Valid Δ) :
    HasType Δ h (.invoke (.union j k) o m (.merge saved imports)) (.record o) := by
  cases hm.value_origin hv with
  | resid hmod hs wj wk hd he =>
    have heq := he.module_inv
    have hm' : HasType Δ h m (.module (.union j k) o) :=
      .conv (hmod.inclusion hm.ambient_wf) (.module .refl heq.2)
        (.module (.union wj wk hd) (hm.result_wf hΔ).module_exports)
    exact .invoke hm'
      (.merge (hs.inclusion hm.ambient_wf) (.conv hp (.record heq.1.symm) (.record wk)) hd)

end LeanSce.Source

/-! ## Value Reductions -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

theorem fst_activation (ht : HasType Δ h (.pair x y) (.prod a b))
    (hv : Value (.pair x y)) (hΔ : Context.Valid Δ) : HasType Δ h x a := by
  cases ht.value_origin hv with
  | pair hx hy he =>
    exact .conv (hx.inclusion ht.ambient_wf) he.prod_inv.1 (ht.result_wf hΔ).prod_left

theorem snd_activation (ht : HasType Δ h (.pair x y) (.prod a b))
    (hv : Value (.pair x y)) (hΔ : Context.Valid Δ) : HasType Δ h y b := by
  cases ht.value_origin hv with
  | pair hx hy he =>
    exact .conv (hy.inclusion ht.ambient_wf) he.prod_inv.2 (ht.result_wf hΔ).prod_right

theorem app_clo_activation (hf : HasType Δ h (.clo cap arg body) (.arr a b))
    (hv : Value (.clo cap arg body)) (hx : HasType Δ h x a)
    (hΔ : Context.Valid Δ) : HasType Δ h (.box (.pair cap x) body) b := by
  cases hf.value_origin hv with
  | clo wa hc hb he =>
    apply HasType.box (.pair (hc.inclusion hf.ambient_wf) (.conv hx he.arr_inv.1.symm wa))
    exact .conv hb he.arr_inv.2 (hf.result_wf hΔ).arr_right

theorem app_rclo_activation (hf : HasType Δ h (.rclo cap arg result body) (.arr a b))
    (hv : Value (.rclo cap arg result body)) (hx : HasType Δ h x a)
    (hΔ : Context.Valid Δ) :
    HasType Δ h (.box (.pair (.pair cap (.rclo cap arg result body)) x) body) b := by
  cases hf.value_origin hv with
  | rclo wa wb hc hb he =>
    have hself : HasType Δ h (.rclo cap arg result body) (.arr arg result) :=
      .rclo hf.ambient_wf wa wb hc.1 hc.2 hb
    apply HasType.box (.pair (.pair (hc.inclusion hf.ambient_wf) hself)
      (.conv hx he.arr_inv.1.symm wa))
    exact .conv hb he.arr_inv.2 (hf.result_wf hΔ).arr_right

theorem case_inl_activation (hp : HasType Δ h (.inl t v) (.sum a b))
    (hv : Value (.inl t v)) (hν : ValueType Δ ν h)
    (hl : HasType Δ (.prod h a) body c) (hΔ : Context.Valid Δ) :
    HasType Δ h (.box (.pair ν v) body) c := by
  cases hp.value_origin hv with
  | inl _ hx he =>
    exact .box (.pair (hν.inclusion hp.ambient_wf)
      (.conv (hx.inclusion hp.ambient_wf) he.sum_inv.1 (hp.result_wf hΔ).sum_left)) hl

theorem case_inr_activation (hp : HasType Δ h (.inr t v) (.sum a b))
    (hv : Value (.inr t v)) (hν : ValueType Δ ν h)
    (hr : HasType Δ (.prod h b) body c) (hΔ : Context.Valid Δ) :
    HasType Δ h (.box (.pair ν v) body) c := by
  cases hp.value_origin hv with
  | inr _ hx he =>
    exact .box (.pair (hν.inclusion hp.ambient_wf)
      (.conv (hx.inclusion hp.ambient_wf) he.sum_inv.2 (hp.result_wf hΔ).sum_right)) hr

end LeanSce.Source

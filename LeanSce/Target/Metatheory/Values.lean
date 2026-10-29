import LeanSce.Target.Definitions.Semantics
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Rows
import LeanSce.Target.Metatheory.Substitution
import LeanSce.Target.Metatheory.Typing

/-!
# Target / Metatheory / Values

Proofs and supporting constructions for values.
-/

/-! ## Primitive Preservation -/

namespace LeanSce.Target

private theorem binary_prim_preservation
    (build : ∀ {x y}, HasType Δ h x a → HasType Δ h y b →
      HasType Δ h (.prim p (.cons l x (.cons k y .nil))) r)
    (reduce : ∀ {x y z}, HasType Δ h x a → HasType Δ h y b → Value x → Value y →
      evalPrim p (.cons l x (.cons k y .nil)) = some z → HasType Δ h z r)
    (hx : HasType Δ h x a) (hy : HasType Δ h y b)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' a)
    (ihy : ∀ y', step ν y = some y' → HasType Δ h y' b)
    (hs : step ν (.prim p (.cons l x (.cons k y .nil))) = some z) : HasType Δ h z r := by
  rw [step_prim_eq] at hs
  cases hvx : x.isValue with
  | false =>
    simp only [Term.isValue, hvx, Bool.false_and, Bool.not_false, ↓reduceIte] at hs
    rw [step_cons_left hvx, Option.map_map] at hs
    obtain ⟨x',hx',he⟩ := Option.map_eq_some_iff.mp hs
    subst z
    exact build (ihx x' hx') hy
  | true =>
    cases hvy : y.isValue with
    | false =>
      simp only [Term.isValue, hvx, hvy, Bool.true_and, Bool.false_and,
        Bool.not_false, ↓reduceIte] at hs
      rw [step_cons_right hvx (by simp [Term.isValue, hvy]),
        step_cons_left hvy, Option.map_map, Option.map_map] at hs
      obtain ⟨y',hy',he⟩ := Option.map_eq_some_iff.mp hs
      subst z
      exact build hx (ihy y' hy')
    | true =>
      simp only [Term.isValue, hvx, hvy, Bool.true_and, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte] at hs
      exact reduce hx hy hvx hvy hs

theorem prim_add_preservation (hx : HasType Δ h x .int) (hy : HasType Δ h y .int)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' .int)
    (ihy : ∀ y', step ν y = some y' → HasType Δ h y' .int)
    (hs : step ν (.prim .add (.cons l x (.cons k y .nil))) = some z) : HasType Δ h z .int := by
  apply binary_prim_preservation (fun hx hy => .add hx hy) ?_ hx hy ihx ihy hs
  intro x y z hx hy hvx hvy he
  obtain ⟨n,rfl⟩ := hx.value_shape hvx
  obtain ⟨m,rfl⟩ := hy.value_shape hvy
  simp only [evalPrim, Option.some.injEq] at he
  subst z
  exact .int hx.ambient_wf

theorem prim_eqInt_preservation (hx : HasType Δ h x .int) (hy : HasType Δ h y .int)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' .int)
    (ihy : ∀ y', step ν y = some y' → HasType Δ h y' .int)
    (hs : step ν (.prim .eqInt (.cons l x (.cons k y .nil))) = some z) : HasType Δ h z .bool := by
  apply binary_prim_preservation (fun hx hy => .eqInt hx hy) ?_ hx hy ihx ihy hs
  intro x y z hx hy hvx hvy he
  obtain ⟨n,rfl⟩ := hx.value_shape hvx
  obtain ⟨m,rfl⟩ := hy.value_shape hvy
  simp only [evalPrim, Option.some.injEq] at he
  subst z
  exact .bool hx.ambient_wf

theorem prim_concat_preservation (hx : HasType Δ h x .string) (hy : HasType Δ h y .string)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' .string)
    (ihy : ∀ y', step ν y = some y' → HasType Δ h y' .string)
    (hs : step ν (.prim .concat (.cons l x (.cons k y .nil))) = some z) : HasType Δ h z .string := by
  apply binary_prim_preservation (fun hx hy => .concat hx hy) ?_ hx hy ihx ihy hs
  intro x y z hx hy hvx hvy he
  obtain ⟨n,rfl⟩ := hx.value_shape hvx
  obtain ⟨m,rfl⟩ := hy.value_shape hvy
  simp only [evalPrim, Option.some.injEq] at he
  subst z
  exact .string hx.ambient_wf

theorem prim_showInt_preservation (hx : HasType Δ h x .int)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' .int)
    (hs : step ν (.prim .showInt (.cons l x .nil)) = some z) : HasType Δ h z .string := by
  rw [step_prim_eq] at hs
  cases hvx : x.isValue with
  | false =>
    simp only [Term.isValue, hvx, Bool.false_and, Bool.not_false, ↓reduceIte] at hs
    rw [step_cons_left hvx, Option.map_map] at hs
    obtain ⟨x',hx',he⟩ := Option.map_eq_some_iff.mp hs
    subst z
    exact .showInt (ihx x' hx')
  | true =>
    obtain ⟨n,rfl⟩ := hx.value_shape hvx
    simp only [Term.isValue, Bool.true_and, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, evalPrim, Option.some.injEq] at hs
    subst z
    exact .string hx.ambient_wf

end LeanSce.Target

/-! ## Legacy Properties -/

namespace LeanSce.Target

theorem Absent.of_tyEq (he : TyEq a b) (hb : Absent l b) : Absent l a := by
  induction hb generalizing a with
  | unit => cases he.shape; exact .unit
  | int => cases he.shape; exact .int
  | bool => cases he.shape; exact .bool
  | string => cases he.shape; exact .string
  | arr => cases he.shape; exact .arr
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

end LeanSce.Target

/-! ## Record Properties -/

namespace LeanSce.Target

/-- Initializer order is retained; the static row has the same label multiset,
    and field-list typing excludes duplicate labels. -/
theorem FieldsType.shape (hf : FieldsType Δ h fs r) :
    fs.labels.Perm r.knownLabels ∧ fs.labels.Nodup := by
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ fs r _ => fs.labels.Perm r.knownLabels ∧ fs.labels.Nodup)
    (t := hf)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil => simp [Term.labels, Ty.knownLabels]
  case cons =>
    rename_i Δ h e a fs r l ht hf hd ihT ihF
    have hne : l ∉ fs.labels := by
      intro hl
      exact hd.knownLabels l (by simp [Ty.knownLabels]) (ihF.1.mem_iff.mp hl)
    exact ⟨by simpa [Term.labels, Ty.knownLabels] using List.Perm.cons l ihF.1,
      by simpa [Term.labels] using List.nodup_cons.mpr ⟨hne, ihF.2⟩⟩
  case conv =>
    rename_i Δ h fs r s hf he hw ih
    exact ⟨ih.1.trans he.labels_perm, ih.2⟩

theorem FieldsType.labels_perm (hf : FieldsType Δ h fs r) :
    fs.labels.Perm r.knownLabels := hf.shape.1

theorem FieldsType.labels_nodup (hf : FieldsType Δ h fs r) : fs.labels.Nodup := hf.shape.2

theorem FieldsType.labels_mem (hf : FieldsType Δ h fs r) :
    l ∈ fs.labels ↔ l ∈ r.knownLabels := hf.labels_perm.mem_iff

/-- Static disjointness ensures the evaluator's merge collision check succeeds. -/
theorem FieldsType.merge_check (hf : FieldsType Δ h fs r)
    (hg : FieldsType Δ h gs s) (hd : Disjoint Δ r s) :
    fs.labels.all (fun l => !gs.labels.contains l) = true := by
  apply List.all_eq_true.mpr
  intro l hl
  have hne := hd.knownLabels l (hf.labels_mem.mp hl)
  have hne' : l ∉ gs.labels := fun hm => hne (hg.labels_mem.mp hm)
  simp [hne']

/-- Every statically selected known label is present in the concrete record. -/
theorem FieldsType.selection_check (hf : FieldsType Δ h fs r)
    (ls : List String) (hl : ∀ l ∈ ls, ∃ a, r.lookup l = some a) :
    ls.all fs.labels.contains = true := by
  apply List.all_eq_true.mpr
  intro l hm
  obtain ⟨a,ha⟩ := hl l hm
  simpa using hf.labels_mem.mpr (Ty.lookup_mem r ha)

private theorem TyEq.empty_union (r : Row) : TyEq (.union .empty r) r :=
  .trans .union_comm .union_empty

/-- Concatenation preserves the full exact row, with no field loss. -/
theorem FieldsType.append (hf : FieldsType Δ h fs r) (hΔ : Context.Valid Δ) :
    ∀ {gs s}, FieldsType Δ h gs s → Disjoint Δ r s →
      FieldsType Δ h (fs.append gs) (.union r s) := by
  revert hΔ
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ h fs r _ => Context.Valid Δ → ∀ {gs s}, FieldsType Δ h gs s → Disjoint Δ r s →
      FieldsType Δ h (fs.append gs) (.union r s))
    (t := hf)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil =>
    rename_i Δ h hh hΔ gs s hg hd
    simpa [Term.append] using FieldsType.conv hg (TyEq.empty_union s).symm
      (WellFormed.union .empty (hg.result_wf hΔ) hd)
  case cons =>
    rename_i Δ h e a fs r l ht hf hd ihT ihF hΔ gs s hg hdisj
    have hs := disjoint_union_left.mp hdisj
    have hh : Disjoint Δ (.field l a) (.union r s) := disjoint_union_right.mpr ⟨hd,hs.1⟩
    have hw : WellFormed Δ (.union (.union (.field l a) r) s) :=
      .union (.union (.field (ht.result_wf hΔ)) (hf.result_wf hΔ) hd) (hg.result_wf hΔ) hdisj
    simpa [Term.append] using FieldsType.conv
      (FieldsType.cons ht (ihF hΔ hg hs.2) hh) TyEq.union_assoc.symm hw
  case conv =>
    rename_i Δ h fs r s hf he hw ih hΔ gs t hg hd
    exact .conv (ih hΔ hg (he.symm.disjoint_left hd)) (.union he .refl)
      (.union hw (hg.result_wf hΔ) hd)

/-- Selection keeps exactly the requested fields and their original values. -/
theorem FieldsType.select (hf : FieldsType Δ h fs r) (hΔ : Context.Valid Δ) :
    ∀ ls, FieldsType Δ h (fs.filter ls.contains) (r.select ls) := by
  revert hΔ
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ h fs r _ => Context.Valid Δ → ∀ ls,
      FieldsType Δ h (fs.filter ls.contains) (r.select ls))
    (t := hf)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil =>
    rename_i Δ h hh hΔ ls
    simpa [Term.filter, Ty.select] using FieldsType.nil hh
  case cons =>
    rename_i Δ h e a fs r l ht hf hd ihT ihF hΔ ls
    by_cases hl : l ∈ ls
    · have hh : Disjoint Δ (.field l a) (r.select ls) :=
        hd.mono (fun _ hm => hm) (Ty.entries_select_subset r ls)
      simpa [Term.filter, Ty.select, hl] using FieldsType.cons ht (ihF hΔ ls) hh
    · have hw : WellFormed Δ (.union .empty (r.select ls)) :=
        .union .empty ((hf.result_wf hΔ).select ls) (disjoint_empty_left _ _)
      simpa [Term.filter, Ty.select, hl] using FieldsType.conv (ihF hΔ ls)
        (TyEq.empty_union (r.select ls)).symm hw
  case conv =>
    rename_i Δ h fs r s hf he hw ih hΔ ls
    exact .conv (ih hΔ ls) (he.select ls) (hw.select ls)

/-- Removal evaluates no fields and preserves precisely the remaining row. -/
theorem FieldsType.drop (hf : FieldsType Δ h fs r) (hΔ : Context.Valid Δ) :
    ∀ ls, FieldsType Δ h (fs.filter (fun l => !ls.contains l)) (r.drop ls) := by
  revert hΔ
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ h fs r _ => Context.Valid Δ → ∀ ls,
      FieldsType Δ h (fs.filter (fun l => !ls.contains l)) (r.drop ls))
    (t := hf)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil =>
    rename_i Δ h hh hΔ ls
    simpa [Term.filter, Ty.drop] using FieldsType.nil hh
  case cons =>
    rename_i Δ h e a fs r l ht hf hd ihT ihF hΔ ls
    by_cases hl : l ∈ ls
    · have hw : WellFormed Δ (.union .empty (r.drop ls)) :=
        .union .empty ((hf.result_wf hΔ).drop ls) (disjoint_empty_left _ _)
      simpa [Term.filter, Ty.drop, hl] using FieldsType.conv (ihF hΔ ls)
        (TyEq.empty_union (r.drop ls)).symm hw
    · have hh : Disjoint Δ (.field l a) (r.drop ls) :=
        hd.mono (fun _ hm => hm) (Ty.entries_drop_subset r ls)
      simpa [Term.filter, Ty.drop, hl] using FieldsType.cons ht (ihF hΔ ls) hh
  case conv =>
    rename_i Δ h fs r s hf he hw ih hΔ ls
    exact .conv (ih hΔ ls) (he.drop ls) (hw.drop ls)

/-- Static field lookup returns a concrete initializer of the advertised type. -/
theorem FieldsType.lookup (hf : FieldsType Δ h fs r) (hΔ : Context.Valid Δ) :
    ∀ {l a}, r.lookup l = some a → ∃ v, fs.lookup l = some v ∧ HasType Δ h v a := by
  revert hΔ
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ h fs r _ => Context.Valid Δ → ∀ {l a},
      r.lookup l = some a → ∃ v, fs.lookup l = some v ∧ HasType Δ h v a)
    (t := hf)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil =>
    rename_i Δ h hh hΔ l a hl
    simp [Ty.lookup] at hl
  case cons =>
    rename_i Δ h e a fs r l ht hf hd ihT ihF hΔ q b hq
    by_cases heq : q = l
    · have hab : a = b := by simpa [Ty.lookup, heq] using hq
      subst b
      exact ⟨e, by simp [Term.lookup, heq], ht⟩
    · obtain ⟨v,hv,hvt⟩ := ihF hΔ (by simpa [Ty.lookup, heq] using hq)
      exact ⟨v, by simpa [Term.lookup, heq] using hv, hvt⟩
  case conv =>
    rename_i Δ h fs r s hf he hw ih hΔ l a hl
    obtain ⟨b,hb,hab⟩ := he.symm.lookup (hf.result_wf hΔ) hl
    obtain ⟨v,hv,hvt⟩ := ih hΔ hb
    exact ⟨v,hv,.conv hvt hab.symm (hw.lookup hl)⟩

/-- Renaming preserves field values and changes just the advertised label. -/
theorem FieldsType.relabel (hf : FieldsType Δ h fs r) (hΔ : Context.Valid Δ) :
    ∀ {old new a}, Disjoint Δ (.field new a) (r.drop [old]) →
      FieldsType Δ h (fs.renameFields old new) (r.relabel old new) := by
  revert hΔ
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ h fs r _ => Context.Valid Δ → ∀ {old new a},
      Disjoint Δ (.field new a) (r.drop [old]) →
      FieldsType Δ h (fs.renameFields old new) (r.relabel old new))
    (t := hf)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil =>
    rename_i Δ h hh hΔ old new a hfresh
    simpa [Term.renameFields, Ty.relabel] using FieldsType.nil hh
  case cons =>
    rename_i Δ h e b fs r l ht hf hd ihT ihF hΔ old new a hfresh
    have hh : Disjoint Δ (.field new a) ((Ty.field l b).drop [old]) ∧
        Disjoint Δ (.field new a) (r.drop [old]) := by simpa [Ty.drop] using hfresh
    have hd' := hd.relabel hh.1 hh.2
    simpa [Term.renameFields, Ty.relabel] using FieldsType.cons ht (ihF hΔ hh.2)
      (by simpa [Ty.relabel] using hd')
  case conv =>
    rename_i Δ h fs r s hf he hw ih hΔ old new a hfresh
    have hh := (he.drop [old]).symm.disjoint_right hfresh
    exact .conv (ih hΔ hh) (he.relabel old new) (hw.relabel hfresh)

/-- Freshness of a renamed field makes the evaluator's collision check succeed. -/
theorem FieldsType.relabel_check (hf : FieldsType Δ h fs r)
    (hl : r.lookup old = some a) (hne : old ≠ new)
    (hfresh : Disjoint Δ (.field new a) (r.drop [old])) :
    (old != new && fs.labels.contains old && !(fs.labels.contains new)) = true := by
  have hold : old ∈ fs.labels := hf.labels_mem.mpr (Ty.lookup_mem r hl)
  have hnew : new ∉ fs.labels := by
    intro hm
    have hr : Entry.label new ∈ r.entries := (r.label_mem_entries).mpr (hf.labels_mem.mp hm)
    have hdrop : new ∈ (r.drop [old]).knownLabels :=
      ((r.drop [old]).label_mem_entries).mp ((r.entries_drop_one old).mpr
        ⟨hr, by simpa using Ne.symm hne⟩)
    exact hfresh.knownLabels new (by simp [Ty.knownLabels]) hdrop
  simp [hne, hold, hnew]

/-- Lookup in a completed record returns a value. -/
theorem Term.lookup_value (fs : Term s) (hv : Value fs) (hl : fs.lookup l = some v) :
    Value v := by
  cases fs <;> simp only [Term.lookup] at hl
  all_goals try cases hl
  case cons k e rest =>
    simp only [Value, Term.isValue, Bool.and_eq_true] at hv
    split at hl
    · cases Option.some.inj hl; exact hv.1
    · exact Term.lookup_value rest hv.2 hl

theorem Term.append_value (fs : Term s) (hf : Value fs) (hg : Value gs) :
    Value (fs.append gs) := by
  induction fs <;> simp_all [Value, Term.append, Term.isValue]

theorem Term.filter_value (fs : Term s) (hf : Value fs) : Value (fs.filter p) := by
  cases fs <;> simp only [Term.filter]
  all_goals try exact rfl
  case cons l e rest =>
    simp only [Value, Term.isValue, Bool.and_eq_true] at hf
    split
    · exact Bool.and_eq_true_iff.mpr ⟨hf.1, Term.filter_value rest hf.2⟩
    · exact Term.filter_value rest hf.2

theorem Term.renameFields_value (fs : Term s) (hf : Value fs) :
    Value (fs.renameFields old new) := by
  induction fs <;> simp_all [Value, Term.renameFields, Term.isValue]

end LeanSce.Target

/-! ## Value Reductions -/

namespace LeanSce.Target

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

end LeanSce.Target

/-! ## Typing Inversion -/

namespace LeanSce.Target

private theorem record_origin (ht : HasType Δ h e a) :
    ∀ fs, e = .record fs → ∃ r, FieldsType Δ h fs r ∧ TyEq (.record r) a := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ =>
      ∀ fs, e = .record fs → ∃ r, FieldsType Δ h fs r ∧ TyEq (.record r) a)
    (motive_2 := fun _ _ _ _ _ => True)
    (t := ht)
  all_goals intros
  all_goals intros
  all_goals try trivial
  case record => rename_i hf _ fs he; cases he; exact ⟨_,hf,.refl⟩
  case value =>
    rename_i hv _ hh ih fs he
    obtain ⟨r,hf,hr⟩ := ih fs he
    have hvf : Value fs := by cases he; exact hv
    exact ⟨r,hf.value_reambient hvf _ hh,hr⟩
  case conv =>
    rename_i heq _ ih fs he
    obtain ⟨r,hf,hr⟩ := ih fs he
    exact ⟨r,hf,hr.trans heq⟩
  all_goals rename_i fs he; cases he

/-- General record inversion, without requiring completed field values. -/
theorem HasType.fields_inv (ht : HasType Δ h (.record fs) (.record r))
    (hΔ : Context.Valid Δ) : FieldsType Δ h fs r := by
  obtain ⟨s,hf,he⟩ := record_origin ht fs rfl
  exact .conv hf he.record_inv (ht.result_wf hΔ).record_row

theorem FieldsType.cons_origin (hf : FieldsType Δ h fs r) :
    ∀ l e tail, fs = .cons l e tail → ∃ a s,
      HasType Δ h e a ∧ FieldsType Δ h tail s ∧ Disjoint Δ (.field l a) s ∧
      TyEq (.union (.field l a) s) r := by
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ h fs r _ => ∀ l e tail, fs = .cons l e tail → ∃ a s,
      HasType Δ h e a ∧ FieldsType Δ h tail s ∧ Disjoint Δ (.field l a) s ∧
      TyEq (.union (.field l a) s) r)
    (t := hf)
  all_goals intros
  all_goals intros
  all_goals try trivial
  case cons =>
    rename_i ht hf hd _ _ l e tail he
    cases he
    exact ⟨_,_,ht,hf,hd,.refl⟩
  case conv =>
    rename_i heq _ ih l e tail he
    obtain ⟨a,s,ht,hf,hd,hs⟩ := ih l e tail he
    exact ⟨a,s,ht,hf,hd,hs.trans heq⟩

private theorem row_swap (x y r : Row) :
    TyEq (.union y (.union x r)) (.union x (.union y r)) :=
  .trans TyEq.union_assoc.symm
    (.trans (.union TyEq.union_comm .refl) TyEq.union_assoc)

theorem FieldsType.permute_list (hp : xs.Perm ys) (hΔ : Context.Valid Δ) :
    ∀ r, FieldsType Δ h (.ofList xs) r → FieldsType Δ h (.ofList ys) r := by
  induction hp with
  | nil => intro r hf; exact hf
  | cons x hp ih =>
    intro r hf
    obtain ⟨a,s,hx,ht,hd,he⟩ := hf.cons_origin x.1 x.2 (.ofList _) rfl
    exact .conv (.cons hx (ih _ ht) hd) he (hf.result_wf hΔ)
  | swap y x xs =>
    intro r hf
    obtain ⟨a,s,hx,ht,hd,he⟩ := hf.cons_origin x.1 x.2 (.ofList _) rfl
    obtain ⟨b,t,hy,hrest,hdisj,hrow⟩ := ht.cons_origin y.1 y.2 (.ofList xs) rfl
    have hxrest := disjoint_union_right.mp (hrow.symm.disjoint_right hd)
    have hyrest : Disjoint Δ (.field y.1 b) (.union (.field x.1 a) t) :=
      disjoint_union_right.mpr ⟨hxrest.1.symm,hdisj⟩
    exact .conv (.cons hy (.cons hx hrest hxrest.2) hyrest)
      ((row_swap _ _ _).trans ((TyEq.union .refl hrow).trans he)) (hf.result_wf hΔ)
  | trans hp hq ihp ihq => intro r hf; exact ihq _ (ihp _ hf)

@[simp] theorem Term.ofList_toList (fs : Fields) : Term.ofList fs.toList = fs := by
  cases fs with
  | nil => rfl
  | cons l e fs => simp only [Term.toList,Term.ofList,Term.ofList_toList fs]
termination_by sizeOf fs

/-- Permuting field initializers preserves typing and the exact row. -/
theorem FieldsType.permute (hf : FieldsType Δ h fs r)
    (hp : fs.toList.Perm gs.toList) (hΔ : Context.Valid Δ) : FieldsType Δ h gs r := by
  have hh := FieldsType.permute_list (h := h) hp hΔ r
  simpa only [Term.ofList_toList] using hh (by simpa only [Term.ofList_toList] using hf)

end LeanSce.Target

/-! ## Activation -/

namespace LeanSce.Target

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

end LeanSce.Target

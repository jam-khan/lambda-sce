import LeanSce.Source.Definitions.Semantics
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.WellFormedness

/-!
# Source / Metatheory / Records

Proofs and supporting constructions for records.
-/

/-! ## Record Properties -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim Entry)

/-- Initializer order is retained; the static row has the same label multiset,
    and field-list typing excludes duplicate labels. -/
theorem FieldsType.shape (hf : FieldsType Δ h fs r) :
    fs.labels.Perm r.knownLabels ∧ fs.labels.Nodup := by
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ fs r _ => fs.labels.Perm r.knownLabels ∧ fs.labels.Nodup)
    (motive_3 := fun _ _ _ _ _ => True)
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
    (motive_3 := fun _ _ _ _ _ => True)
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
    (motive_3 := fun _ _ _ _ _ => True)
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
    (motive_3 := fun _ _ _ _ _ => True)
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
    (motive_3 := fun _ _ _ _ _ => True)
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
    (motive_3 := fun _ _ _ _ _ => True)
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

end LeanSce.Source

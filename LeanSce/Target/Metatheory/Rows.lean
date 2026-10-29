import LeanSce.Target.Definitions.Statics
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Constraints

/-!
# Target / Metatheory / Rows

Proofs and supporting constructions for rows.
-/

/-! ## Row Properties -/

namespace LeanSce.Target

@[simp] theorem Ty.lookup_union (r s : Row) (l : String) :
    (Ty.union r s).lookup l = (r.lookup l <|> s.lookup l) := by simp [Ty.lookup]

/-- All labels reported by lookup are explicit labels of the row. -/
theorem Ty.lookup_mem (r : Row) (hl : r.lookup l = some a) : l ∈ r.knownLabels := by
  cases r with
  | rvar => simp [Ty.lookup] at hl
  | empty => simp [Ty.lookup] at hl
  | field k b =>
    by_cases h : l = k
    · simp [Ty.knownLabels, h]
    · simp [Ty.lookup, h] at hl
  | union r s =>
    cases hr : r.lookup l with
    | none =>
      have hs : s.lookup l = some a := by simpa [Ty.lookup, hr] using hl
      simpa [Ty.knownLabels] using List.mem_append_right r.knownLabels (Ty.lookup_mem s hs)
    | some b => simpa [Ty.knownLabels] using List.mem_append_left s.knownLabels (Ty.lookup_mem r hr)

/-- Every known label has a lookup result. -/
theorem Ty.mem_lookup (r : Row) (hl : l ∈ r.knownLabels) : ∃ a, r.lookup l = some a := by
  cases r with
  | rvar => simp [Ty.knownLabels] at hl
  | empty => simp [Ty.knownLabels] at hl
  | field k b =>
    have he : l = k := by simpa [Ty.knownLabels] using hl
    exact ⟨b, by simp [Ty.lookup, he]⟩
  | union r s =>
    cases hr : r.lookup l with
    | some b => exact ⟨b, by simp [hr]⟩
    | none =>
      have hs : l ∈ s.knownLabels := by
        rcases List.mem_append.mp (show l ∈ r.knownLabels ++ s.knownLabels by simpa [Ty.knownLabels] using hl) with hl | hl
        · obtain ⟨a, ha⟩ := Ty.mem_lookup r hl
          rw [hr] at ha
          cases ha
        · exact hl
      obtain ⟨a, ha⟩ := Ty.mem_lookup s hs
      exact ⟨a, by simp [hr, ha]⟩

@[simp] theorem Ty.label_mem_entries (r : Row) :
    Entry.label l ∈ r.entries ↔ l ∈ r.knownLabels := by
  cases r with
  | rvar => simp [Ty.entries, Ty.knownLabels]
  | empty => simp [Ty.entries, Ty.knownLabels]
  | field => simp [Ty.entries, Ty.knownLabels]
  | union r s => simp [Ty.entries, Ty.knownLabels, Ty.label_mem_entries r, Ty.label_mem_entries s]

theorem Disjoint.knownLabels (hd : Disjoint Δ r s) :
    ∀ l ∈ r.knownLabels, l ∉ s.knownLabels := by
  intro l hr hs
  have hh := disjoint_iff_entries.mp hd (.label l) ((r.label_mem_entries).mpr hr)
    (.label l) ((s.label_mem_entries).mpr hs)
  exact (entryApart_label_label.mp hh) rfl

theorem WellFormed.lookup (hw : WellFormed Δ r) (hl : r.lookup l = some a) :
    WellFormed Δ a := by
  cases hw with
  | rvar => simp [Ty.lookup] at hl
  | empty => simp [Ty.lookup] at hl
  | field ha =>
    simp only [Ty.lookup] at hl
    split at hl
    · cases hl; exact ha
    · cases hl
  | union hr hs hd =>
    rename_i r s
    cases he : r.lookup l with
    | none => exact hs.lookup (by simpa [Ty.lookup, he] using hl)
    | some b =>
      have hab : b = a := by simpa [Ty.lookup, he] using hl
      subst b
      exact hr.lookup he

/-- Selecting or dropping fields only removes row entries. -/
theorem Ty.entries_select_subset (r : Row) (ls : List String) :
    (r.select ls).entries ⊆ r.entries := by
  cases r with
  | rvar => simp [Ty.select, Ty.entries]
  | empty => simp [Ty.select, Ty.entries]
  | field l a => by_cases h : l ∈ ls <;> simp [Ty.select, Ty.entries, h]
  | union r s =>
    intro e he
    simp only [Ty.select, Ty.entries] at he ⊢
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (Ty.entries_select_subset r ls he)
    · exact List.mem_append_right _ (Ty.entries_select_subset s ls he)

theorem Ty.entries_drop_subset (r : Row) (ls : List String) :
    (r.drop ls).entries ⊆ r.entries := by
  cases r with
  | rvar => simp [Ty.drop, Ty.entries]
  | empty => simp [Ty.drop, Ty.entries]
  | field l a => by_cases h : l ∈ ls <;> simp [Ty.drop, Ty.entries, h]
  | union r s =>
    intro e he
    simp only [Ty.drop, Ty.entries] at he ⊢
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (Ty.entries_drop_subset r ls he)
    · exact List.mem_append_right _ (Ty.entries_drop_subset s ls he)

theorem Disjoint.mono (hd : Disjoint Δ r s) (hr : r'.entries ⊆ r.entries)
    (hs : s'.entries ⊆ s.entries) : Disjoint Δ r' s' := by
  rw [disjoint_iff_entries] at hd ⊢
  intro e he f hf
  exact hd e (hr he) f (hs hf)

theorem Disjoint.select (hd : Disjoint Δ r s) (ls : List String) :
    Disjoint Δ (r.select ls) (s.select ls) :=
  hd.mono (r.entries_select_subset ls) (s.entries_select_subset ls)

theorem Disjoint.drop (hd : Disjoint Δ r s) (ls : List String) :
    Disjoint Δ (r.drop ls) (s.drop ls) :=
  hd.mono (r.entries_drop_subset ls) (s.entries_drop_subset ls)

theorem WellFormed.select (hw : WellFormed Δ r) (ls : List String) :
    WellFormed Δ (r.select ls) := by
  cases hw with
  | rvar => simpa [Ty.select] using (WellFormed.empty : WellFormed Δ .empty)
  | empty => simpa [Ty.select] using (WellFormed.empty : WellFormed Δ .empty)
  | field ha =>
    simp only [Ty.select]
    split
    · exact .field ha
    · exact .empty
  | union hr hs hd => simpa [Ty.select] using WellFormed.union (hr.select ls) (hs.select ls) (hd.select ls)

theorem WellFormed.drop (hw : WellFormed Δ r) (ls : List String) :
    WellFormed Δ (r.drop ls) := by
  cases hw with
  | rvar h => simpa [Ty.drop] using WellFormed.rvar h
  | empty => simpa [Ty.drop] using (WellFormed.empty : WellFormed Δ .empty)
  | field ha =>
    simp only [Ty.drop]
    split
    · exact .empty
    · exact .field ha
  | union hr hs hd => simpa [Ty.drop] using WellFormed.union (hr.drop ls) (hs.drop ls) (hd.drop ls)

private def RowLift (op : Row → Row) (a : Ty s) : Ty s :=
  match s with
  | .row => op a
  | _ => a

private theorem TyEq.select_lift (he : TyEq a b) (ls : List String) :
    TyEq (RowLift (Ty.select ls) a) (RowLift (Ty.select ls) b) := by
  induction he <;> simp only [RowLift, Ty.select] at *
  case refl => exact .refl
  case symm ih => exact .symm ih
  case trans ih₁ ih₂ => exact .trans ih₁ ih₂
  case prod h₁ h₂ _ _ => exact .prod h₁ h₂
  case sum h₁ h₂ _ _ => exact .sum h₁ h₂
  case arr h₁ h₂ _ _ => exact .arr h₁ h₂
  case tag he _ => exact .tag he
  case record he _ => exact .record he
  case all hg he _ => exact .all hg he
  case ex hg he _ => exact .ex hg he
  case mu he _ => exact .mu he
  case field a b l he ih =>
    by_cases hl : l ∈ ls
    · simp [hl]; exact .field he
    · simp [hl]; exact .refl
  case union ih₁ ih₂ => exact .union ih₁ ih₂
  case union_empty => exact .union_empty
  case union_comm => exact .union_comm
  case union_assoc => exact .union_assoc

theorem TyEq.select (he : TyEq r s) (ls : List String) :
    TyEq (r.select ls) (s.select ls) := he.select_lift ls

private theorem TyEq.drop_lift (he : TyEq a b) (ls : List String) :
    TyEq (RowLift (Ty.drop ls) a) (RowLift (Ty.drop ls) b) := by
  induction he <;> simp only [RowLift, Ty.drop] at *
  case refl => exact .refl
  case symm ih => exact .symm ih
  case trans ih₁ ih₂ => exact .trans ih₁ ih₂
  case prod h₁ h₂ _ _ => exact .prod h₁ h₂
  case sum h₁ h₂ _ _ => exact .sum h₁ h₂
  case arr h₁ h₂ _ _ => exact .arr h₁ h₂
  case tag he _ => exact .tag he
  case record he _ => exact .record he
  case all hg he _ => exact .all hg he
  case ex hg he _ => exact .ex hg he
  case mu he _ => exact .mu he
  case field a b l he ih =>
    by_cases hl : l ∈ ls
    · simp [hl]; exact .refl
    · simp [hl]; exact .field he
  case union ih₁ ih₂ => exact .union ih₁ ih₂
  case union_empty => exact .union_empty
  case union_comm => exact .union_comm
  case union_assoc => exact .union_assoc

theorem TyEq.drop (he : TyEq r s) (ls : List String) :
    TyEq (r.drop ls) (s.drop ls) := he.drop_lift ls

private theorem TyEq.relabel_lift (he : TyEq a b) (old new : String) :
    TyEq (RowLift (Ty.relabel old new) a) (RowLift (Ty.relabel old new) b) := by
  induction he <;> simp only [RowLift, Ty.relabel] at *
  case refl => exact .refl
  case symm ih => exact .symm ih
  case trans ih₁ ih₂ => exact .trans ih₁ ih₂
  case prod h₁ h₂ _ _ => exact .prod h₁ h₂
  case sum h₁ h₂ _ _ => exact .sum h₁ h₂
  case arr h₁ h₂ _ _ => exact .arr h₁ h₂
  case tag he _ => exact .tag he
  case record he _ => exact .record he
  case all hg he _ => exact .all hg he
  case ex hg he _ => exact .ex hg he
  case mu he _ => exact .mu he
  case field a b l he ih =>
    exact .field he
  case union ih₁ ih₂ => exact .union ih₁ ih₂
  case union_empty => exact .union_empty
  case union_comm => exact .union_comm
  case union_assoc => exact .union_assoc

theorem TyEq.relabel (he : TyEq r s) (old new : String) :
    TyEq (r.relabel old new) (s.relabel old new) := he.relabel_lift old new

private def EntryLift (a : Ty s) : List Entry :=
  match s with
  | .row => a.entries
  | _ => []

private theorem TyEq.entries_perm_lift (he : TyEq a b) :
    (EntryLift a).Perm (EntryLift b) := by
  induction he <;> simp only [EntryLift, Ty.entries] at *
  case refl => exact .refl _
  case symm ih => exact ih.symm
  case trans ih₁ ih₂ => exact ih₁.trans ih₂
  case union ih₁ ih₂ => exact ih₁.append ih₂
  case union_empty => simp
  case union_comm => exact List.perm_append_comm
  case union_assoc => simp [List.append_assoc]
  all_goals exact .refl _

theorem TyEq.entries_perm (he : TyEq r s) : r.entries.Perm s.entries := he.entries_perm_lift

theorem TyEq.disjoint_left (he : TyEq r s) (hd : Disjoint Δ r t) : Disjoint Δ s t := by
  rw [disjoint_iff_entries] at hd ⊢
  intro e he' f hf
  exact hd e ((he.entries_perm.mem_iff).mpr he') f hf

theorem TyEq.disjoint_right (he : TyEq r s) (hd : Disjoint Δ t r) : Disjoint Δ t s :=
  (he.disjoint_left hd.symm).symm

private def LabelsLift (a : Ty s) : List String :=
  match s with
  | .row => a.knownLabels
  | _ => []

private theorem TyEq.labels_perm_lift (he : TyEq a b) :
    (LabelsLift a).Perm (LabelsLift b) := by
  induction he <;> simp only [LabelsLift, Ty.knownLabels] at *
  case refl => exact .refl _
  case symm ih => exact ih.symm
  case trans ih₁ ih₂ => exact ih₁.trans ih₂
  case union ih₁ ih₂ => exact ih₁.append ih₂
  case union_empty => simp
  case union_comm => exact List.perm_append_comm
  case union_assoc => simp [List.append_assoc]
  all_goals exact .refl _

theorem TyEq.labels_perm (he : TyEq r s) : r.knownLabels.Perm s.knownLabels := he.labels_perm_lift

/-- All payloads at a label. Well-formed rows contain at most one. -/
def Ty.payloads (l : String) : Row → List Typ
  | .rvar _ | .empty => []
  | .field k a => if l == k then [a] else []
  | .union r s => r.payloads l ++ s.payloads l

private def PayloadEq (xs ys : List Typ) : Prop :=
  (∀ a ∈ xs, ∃ b ∈ ys, TyEq a b) ∧ (∀ b ∈ ys, ∃ a ∈ xs, TyEq a b)

private theorem PayloadEq.refl (xs : List Typ) : PayloadEq xs xs :=
  ⟨fun a ha => ⟨a,ha,.refl⟩,fun a ha => ⟨a,ha,.refl⟩⟩

private theorem PayloadEq.symm (h : PayloadEq xs ys) : PayloadEq ys xs := by
  constructor
  · intro b hb; obtain ⟨a,ha,he⟩ := h.2 b hb; exact ⟨a,ha,he.symm⟩
  · intro a ha; obtain ⟨b,hb,he⟩ := h.1 a ha; exact ⟨b,hb,he.symm⟩

private theorem PayloadEq.trans (h : PayloadEq xs ys) (h' : PayloadEq ys zs) :
    PayloadEq xs zs := by
  constructor
  · intro a ha
    obtain ⟨b,hb,hab⟩ := h.1 a ha
    obtain ⟨c,hc,hbc⟩ := h'.1 b hb
    exact ⟨c,hc,hab.trans hbc⟩
  · intro c hc
    obtain ⟨b,hb,hbc⟩ := h'.2 c hc
    obtain ⟨a,ha,hab⟩ := h.2 b hb
    exact ⟨a,ha,hab.trans hbc⟩

private theorem PayloadEq.ofPerm (h : xs.Perm ys) : PayloadEq xs ys :=
  ⟨fun a ha => ⟨a,h.mem_iff.mp ha,.refl⟩,fun b hb => ⟨b,h.mem_iff.mpr hb,.refl⟩⟩

private theorem PayloadEq.append (h : PayloadEq xs ys) (h' : PayloadEq xs' ys') :
    PayloadEq (xs ++ xs') (ys ++ ys') := by
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨b,hb,he⟩ := h.1 a ha; exact ⟨b,List.mem_append_left _ hb,he⟩
    · obtain ⟨b,hb,he⟩ := h'.1 a ha; exact ⟨b,List.mem_append_right _ hb,he⟩
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨a,ha,he⟩ := h.2 b hb; exact ⟨a,List.mem_append_left _ ha,he⟩
    · obtain ⟨a,ha,he⟩ := h'.2 b hb; exact ⟨a,List.mem_append_right _ ha,he⟩

private def PayloadLift (l : String) (a : Ty s) : List Typ :=
  match s with | .row => a.payloads l | _ => []

private theorem TyEq.payloads_lift (he : TyEq a b) (l : String) :
    PayloadEq (PayloadLift l a) (PayloadLift l b) := by
  induction he <;> simp only [PayloadLift, Ty.payloads] at *
  case refl => exact .refl _
  case symm ih => exact ih.symm
  case trans ih₁ ih₂ => exact ih₁.trans ih₂
  case field a b k he ih =>
    by_cases hl : l = k
    · simp only [hl, beq_self_eq_true, ↓reduceIte]
      constructor
      · intro x hx
        have hxa : x = a := by simpa using hx
        subst x
        exact ⟨b, by simp, he⟩
      · intro x hx
        have hxb : x = b := by simpa using hx
        subst x
        exact ⟨a, by simp, he⟩
    · simp [hl]; exact .refl _
  case union ih₁ ih₂ => exact ih₁.append ih₂
  case union_empty => simp; exact .refl _
  case union_comm => exact .ofPerm List.perm_append_comm
  case union_assoc => simp [List.append_assoc]; exact .refl _
  all_goals exact .refl _

/-- Equality preserves all explicit payloads, modulo payload type equality. -/
theorem TyEq.payloads (he : TyEq r s) (hl : a ∈ r.payloads l) :
    ∃ b ∈ s.payloads l, TyEq a b := (he.payloads_lift l).1 a hl

theorem Ty.lookup_payload (r : Row) (hl : r.lookup l = some a) : a ∈ r.payloads l := by
  cases r with
  | rvar => simp [Ty.lookup] at hl
  | empty => simp [Ty.lookup] at hl
  | field k b =>
    by_cases h : l = k
    · simpa [Ty.payloads, Ty.lookup, h] using hl.symm
    · simp [Ty.lookup, h] at hl
  | union r s =>
    cases hr : r.lookup l with
    | none =>
      have hs : s.lookup l = some a := by simpa [Ty.lookup, hr] using hl
      simpa [Ty.payloads] using List.mem_append_right (r.payloads l) (Ty.lookup_payload s hs)
    | some b =>
      have he : b = a := by simpa [Ty.lookup, hr] using hl
      subst b
      simpa [Ty.payloads] using List.mem_append_left (s.payloads l) (Ty.lookup_payload r hr)

/-- A well-formed row's explicit payload is its unique lookup result. -/
theorem WellFormed.payload_lookup (hw : WellFormed Δ r) (hl : a ∈ r.payloads l) :
    r.lookup l = some a := by
  cases hw with
  | rvar => simp [Ty.payloads] at hl
  | empty => simp [Ty.payloads] at hl
  | field ha =>
    rename_i k
    by_cases hk : l = k
    · simpa [Ty.payloads, Ty.lookup, hk, eq_comm] using hl
    · simp [Ty.payloads, hk] at hl
  | union hr hs hd =>
    rename_i r s
    simp only [Ty.payloads, List.mem_append] at hl
    rcases hl with hl | hl
    · simp [hr.payload_lookup hl]
    · have hh := hs.payload_lookup hl
      cases he : r.lookup l with
      | none => simpa [Ty.lookup, he] using hh
      | some b =>
        exact False.elim (hd.knownLabels l (Ty.lookup_mem r he) (Ty.lookup_mem s hh))

/-- Lookup is invariant under row equality, up to payload equality. -/
theorem TyEq.lookup (he : TyEq r s) (hs : WellFormed Δ s) (hl : r.lookup l = some a) :
    ∃ b, s.lookup l = some b ∧ TyEq a b := by
  obtain ⟨b,hb,hab⟩ := he.payloads (Ty.lookup_payload r hl)
  exact ⟨b,hs.payload_lookup hb,hab⟩

/-- Entry-level renaming mirrors the runtime operation on record labels. -/
def Entry.relabel (old new : String) : Entry → Entry
  | .label l => .label (if l == old then new else l)
  | .tail i => .tail i

@[simp] theorem Ty.entries_relabel (r : Row) (old new : String) :
    (r.relabel old new).entries = r.entries.map (Entry.relabel old new) := by
  cases r with
  | rvar => simp [Ty.relabel, Ty.entries, Entry.relabel]
  | empty => simp [Ty.relabel, Ty.entries]
  | field => simp [Ty.relabel, Ty.entries, Entry.relabel]
  | union r s => simp [Ty.relabel, Ty.entries, Ty.entries_relabel r, Ty.entries_relabel s]

@[simp] theorem Ty.entries_drop_one (r : Row) (old : String) :
    e ∈ (r.drop [old]).entries ↔ e ∈ r.entries ∧ e ≠ .label old := by
  cases r with
  | rvar =>
    simp [Ty.drop, Ty.entries]
    intro he; subst e; simp
  | empty => simp [Ty.drop, Ty.entries]
  | field l a =>
    by_cases hl : l = old
    · simp [Ty.drop, Ty.entries, hl]
    · simp only [Ty.drop, List.mem_singleton, hl, ↓reduceIte, Ty.entries, List.mem_singleton]
      constructor
      · intro he; subst e; exact ⟨rfl, by simpa using hl⟩
      · exact And.left
  | union r s =>
    simp only [Ty.drop, Ty.entries, List.mem_append,
      Ty.entries_drop_one r, Ty.entries_drop_one s]
    constructor
    · rintro (⟨he,hne⟩ | ⟨he,hne⟩)
      · exact ⟨Or.inl he,hne⟩
      · exact ⟨Or.inr he,hne⟩
    · rintro ⟨(he | he),hne⟩
      · exact Or.inl ⟨he,hne⟩
      · exact Or.inr ⟨he,hne⟩

private theorem EntryApart.relabel (hxy : EntryApart Δ x y)
    (hx : x ≠ .label old → EntryApart Δ (.label new) x)
    (hy : y ≠ .label old → EntryApart Δ (.label new) y) :
    EntryApart Δ (x.relabel old new) (y.relabel old new) := by
  cases x with
  | label l =>
    cases y with
    | label k =>
      by_cases hl : l = old <;> by_cases hk : k = old
      · subst l; subst k; exact False.elim ((entryApart_label_label.mp hxy) rfl)
      · subst l
        simpa [Entry.relabel, hk] using hy (by simp [hk])
      · subst k
        have hh := (hx (by simp [hl])).symm
        simpa [Entry.relabel, hl] using hh
      · simpa [Entry.relabel, hl, hk] using hxy
    | tail i =>
      by_cases hl : l = old
      · subst l; simpa [Entry.relabel] using hy (by simp)
      · simpa [Entry.relabel, hl] using hxy
  | tail i =>
    cases y with
    | label k =>
      by_cases hk : k = old
      · subst k; simpa [Entry.relabel] using (hx (by simp)).symm
      · simpa [Entry.relabel, hk] using hxy
    | tail j => simpa [Entry.relabel] using hxy

/-- Renaming remains disjoint when the new label is fresh in both remainders. -/
theorem Disjoint.relabel (hd : Disjoint Δ r s)
    (hr : Disjoint Δ (.field new a) (r.drop [old]))
    (hs : Disjoint Δ (.field new a) (s.drop [old])) :
    Disjoint Δ (r.relabel old new) (s.relabel old new) := by
  rw [disjoint_iff_entries] at hd hr hs ⊢
  simp only [Ty.entries_relabel, List.mem_map]
  intro x ⟨u, hu, hux⟩ y ⟨v, hv, hvy⟩
  subst x; subst y
  apply (hd u hu v hv).relabel
  · intro hne
    exact hr (.label new) (by simp [Ty.entries]) u ((r.entries_drop_one old).mpr ⟨hu, hne⟩)
  · intro hne
    exact hs (.label new) (by simp [Ty.entries]) v ((s.entries_drop_one old).mpr ⟨hv, hne⟩)

/-- Capture-free label renaming preserves row well-formedness. -/
theorem WellFormed.relabel (hw : WellFormed Δ r)
    (hf : Disjoint Δ (.field new a) (r.drop [old])) :
    WellFormed Δ (r.relabel old new) := by
  cases hw with
  | rvar hk => simpa [Ty.relabel] using WellFormed.rvar hk
  | empty => simpa [Ty.relabel] using (WellFormed.empty : WellFormed Δ .empty)
  | field ha =>
    rename_i l
    simpa [Ty.relabel] using WellFormed.field (l := if l == old then new else l) ha
  | union hr hs hd =>
    rename_i r s
    have hh : Disjoint Δ (.field new a) (Ty.drop [old] r) ∧
        Disjoint Δ (.field new a) (Ty.drop [old] s) := by
      simpa [Ty.drop] using hf
    simpa [Ty.relabel] using WellFormed.union (hr.relabel hh.1) (hs.relabel hh.2) (hd.relabel hh.1 hh.2)

end LeanSce.Target

/-! ## Row Substitution -/

namespace LeanSce.Target

/-- A known explicit field contributes its disjointness obligation by itself. -/
theorem Disjoint.known_field (hd : Disjoint Δ r s) (hl : r.lookup l = some a) :
    Disjoint Δ (.field l b) s := by
  rw [disjoint_iff_entries] at hd ⊢
  intro e he f hf
  have hel : e = .label l := by simpa [Ty.entries] using he
  subst e
  exact hd (.label l) ((r.label_mem_entries).mpr (Ty.lookup_mem r hl)) f hf

/-- Static substitution retains every explicit field and its payload type. -/
theorem WellFormed.lookup_subst (hw : WellFormed Γ r) (hs : Subst.Respects Γ Δ σ)
    (hl : r.lookup l = some a) : (r.subst σ).lookup l = some (a.subst σ) := by
  cases hw with
  | rvar => simp [Ty.lookup] at hl
  | empty => simp [Ty.lookup] at hl
  | field ha =>
    rename_i b k
    by_cases hk : l = k
    · have he : b = a := by simpa [Ty.lookup, hk] using hl
      subst a
      simp [Ty.subst, Ty.lookup, hk]
    · simp [Ty.lookup, hk] at hl
  | union hr hs' hd =>
    rename_i r s
    cases he : r.lookup l with
    | some b =>
      have hba : b = a := by simpa [Ty.lookup, he] using hl
      subst b
      simp [Ty.subst, hr.lookup_subst hs he]
    | none =>
      have hh : s.lookup l = some a := by simpa [Ty.lookup, he] using hl
      have hh' := hs'.lookup_subst hs hh
      have hdisj := hd.subst hs
      cases he' : (r.subst σ).lookup l with
      | none => simpa [Ty.subst, Ty.lookup, he'] using hh'
      | some b =>
        exact False.elim (hdisj.knownLabels l (Ty.lookup_mem _ he') (Ty.lookup_mem _ hh'))

/-- A selected label is either explicit or known absent, allowing induction
    through a disjoint union without learning anything about an opaque tail. -/
def SelectedSafe (Δ : Context) (r : Row) (ls : List String) : Prop :=
  ∀ l ∈ ls, (∃ a, r.lookup l = some a) ∨ Disjoint Δ (.field l .unit) r

theorem SelectedSafe.left (h : SelectedSafe Δ (.union r s) ls)
    (hd : Disjoint Δ r s) : SelectedSafe Δ r ls := by
  intro l hl
  rcases h l hl with ⟨a,ha⟩ | ha
  · by_cases hm : l ∈ r.knownLabels
    · exact Or.inl (Ty.mem_lookup r hm)
    · have hm' : l ∈ s.knownLabels := by
        have hh := Ty.lookup_mem (.union r s) ha
        simpa [Ty.knownLabels, hm] using hh
      obtain ⟨b,hb⟩ := Ty.mem_lookup s hm'
      exact Or.inr (hd.symm.known_field hb)
  · exact Or.inr (disjoint_union_right.mp ha).1

theorem SelectedSafe.right (h : SelectedSafe Δ (.union r s) ls)
    (hd : Disjoint Δ r s) : SelectedSafe Δ s ls := by
  intro l hl
  rcases h l hl with ⟨a,ha⟩ | ha
  · by_cases hm : l ∈ s.knownLabels
    · exact Or.inl (Ty.mem_lookup s hm)
    · have hm' : l ∈ r.knownLabels := by
        have hh := Ty.lookup_mem (.union r s) ha
        simpa [Ty.knownLabels, hm] using hh
      obtain ⟨b,hb⟩ := Ty.mem_lookup r hm'
      exact Or.inr (hd.known_field hb)
  · exact Or.inr (disjoint_union_right.mp ha).2

private theorem Ty.select_empty (r : Row)
    (h : ∀ l ∈ ls, Disjoint Δ (.field l .unit) r) : TyEq (r.select ls) .empty := by
  cases r with
  | rvar => simpa [Ty.select] using (TyEq.refl : TyEq Ty.empty .empty)
  | empty => simpa [Ty.select] using (TyEq.refl : TyEq Ty.empty .empty)
  | field l a =>
    by_cases hl : l ∈ ls
    · exact False.elim ((h l hl).knownLabels l (by simp [Ty.knownLabels]) (by simp [Ty.knownLabels]))
    · simpa [Ty.select, hl] using (TyEq.refl : TyEq Ty.empty .empty)
  | union r s =>
    have hr : ∀ l ∈ ls, Disjoint Δ (.field l .unit) r := fun l hl =>
      (disjoint_union_right.mp (h l hl)).1
    have hs : ∀ l ∈ ls, Disjoint Δ (.field l .unit) s := fun l hl =>
      (disjoint_union_right.mp (h l hl)).2
    simpa [Ty.select] using TyEq.trans (.union (Ty.select_empty r hr) (Ty.select_empty s hs)) TyEq.union_empty

private theorem Ty.drop_unchanged (r : Row)
    (h : ∀ l ∈ ls, Disjoint Δ (.field l .unit) r) : r.drop ls = r := by
  cases r with
  | rvar => simp [Ty.drop]
  | empty => simp [Ty.drop]
  | field l a =>
    by_cases hl : l ∈ ls
    · exact False.elim ((h l hl).knownLabels l (by simp [Ty.knownLabels]) (by simp [Ty.knownLabels]))
    · simp [Ty.drop, hl]
  | union r s =>
    have hr : ∀ l ∈ ls, Disjoint Δ (.field l .unit) r := fun l hl =>
      (disjoint_union_right.mp (h l hl)).1
    have hs : ∀ l ∈ ls, Disjoint Δ (.field l .unit) s := fun l hl =>
      (disjoint_union_right.mp (h l hl)).2
    simp [Ty.drop, Ty.drop_unchanged r hr, Ty.drop_unchanged s hs]

theorem WellFormed.select_subst_safe (hw : WellFormed Γ r)
    (hs : Subst.Respects Γ Δ σ) (hsel : SelectedSafe Γ r ls) :
    TyEq ((r.select ls).subst σ) ((r.subst σ).select ls) := by
  cases hw with
  | rvar hk =>
    rename_i i
    have hh : ∀ l ∈ ls, Disjoint Δ (.field l .unit) (σ .row i) := by
      intro l hl
      rcases hsel l hl with ⟨a,ha⟩ | ha
      · simp [Ty.lookup] at ha
      · simpa [Ty.subst] using ha.subst hs
    simpa [Ty.select, Ty.subst] using (Ty.select_empty _ hh).symm
  | empty => simp [Ty.select, Ty.subst]; exact .refl
  | field ha =>
    rename_i l
    by_cases hl : l ∈ ls <;> simp [Ty.select, Ty.subst, hl] <;> exact .refl
  | union hr ht hd =>
    simpa [Ty.select, Ty.subst] using TyEq.union
      (hr.select_subst_safe hs (hsel.left hd)) (ht.select_subst_safe hs (hsel.right hd))

theorem WellFormed.drop_subst_safe (hw : WellFormed Γ r)
    (hs : Subst.Respects Γ Δ σ) (hsel : SelectedSafe Γ r ls) :
    (r.drop ls).subst σ = (r.subst σ).drop ls := by
  cases hw with
  | rvar hk =>
    rename_i i
    have hh : ∀ l ∈ ls, Disjoint Δ (.field l .unit) (σ .row i) := by
      intro l hl
      rcases hsel l hl with ⟨a,ha⟩ | ha
      · simp [Ty.lookup] at ha
      · simpa [Ty.subst] using ha.subst hs
    simpa [Ty.drop, Ty.subst] using (Ty.drop_unchanged _ hh).symm
  | empty => simp [Ty.drop, Ty.subst]
  | field ha =>
    rename_i l
    by_cases hl : l ∈ ls <;> simp [Ty.drop, Ty.subst, hl]
  | union hr ht hd =>
    simp [Ty.drop, Ty.subst, hr.drop_subst_safe hs (hsel.left hd), ht.drop_subst_safe hs (hsel.right hd)]

/-- The premises of the source-level selection/removal rules suffice for
    substitution to commute with the operation. -/
theorem WellFormed.select_subst (hw : WellFormed Γ r)
    (hs : Subst.Respects Γ Δ σ) (hsel : ∀ l ∈ ls, ∃ a, r.lookup l = some a) :
    TyEq ((r.select ls).subst σ) ((r.subst σ).select ls) :=
  hw.select_subst_safe hs (fun l hl => Or.inl (hsel l hl))

theorem WellFormed.drop_subst (hw : WellFormed Γ r)
    (hs : Subst.Respects Γ Δ σ) (hsel : ∀ l ∈ ls, ∃ a, r.lookup l = some a) :
    (r.drop ls).subst σ = (r.subst σ).drop ls :=
  hw.drop_subst_safe hs (fun l hl => Or.inl (hsel l hl))

private theorem Ty.relabel_unchanged (r : Row)
    (h : Disjoint Δ (.field old .unit) r) : r.relabel old new = r := by
  cases r with
  | rvar => simp [Ty.relabel]
  | empty => simp [Ty.relabel]
  | field l a =>
    have hl : l ≠ old := by
      intro he
      subst l
      exact h.knownLabels old (by simp [Ty.knownLabels]) (by simp [Ty.knownLabels])
    simp [Ty.relabel, hl]
  | union r s =>
    have hh := disjoint_union_right.mp h
    simp [Ty.relabel, Ty.relabel_unchanged r hh.1, Ty.relabel_unchanged s hh.2]

theorem WellFormed.relabel_subst_safe (hw : WellFormed Γ r)
    (hs : Subst.Respects Γ Δ σ) (hsel : SelectedSafe Γ r [old]) :
    (r.relabel old new).subst σ = (r.subst σ).relabel old new := by
  cases hw with
  | rvar hk =>
    rename_i i
    have hh : Disjoint Δ (.field old .unit) (σ .row i) := by
      rcases hsel old (by simp) with ⟨a,ha⟩ | ha
      · simp [Ty.lookup] at ha
      · simpa [Ty.subst] using ha.subst hs
    simpa [Ty.relabel, Ty.subst] using (Ty.relabel_unchanged _ hh).symm
  | empty => simp [Ty.relabel, Ty.subst]
  | field ha => simp [Ty.relabel, Ty.subst]
  | union hr ht hd =>
    simp [Ty.relabel, Ty.subst, hr.relabel_subst_safe hs (hsel.left hd), ht.relabel_subst_safe hs (hsel.right hd)]

theorem WellFormed.relabel_subst (hw : WellFormed Γ r)
    (hs : Subst.Respects Γ Δ σ) (hl : r.lookup old = some a) :
    (r.relabel old new).subst σ = (r.subst σ).relabel old new := by
  apply hw.relabel_subst_safe hs
  intro l hm
  have he : l = old := by simpa using hm
  subst l
  exact Or.inl ⟨a,hl⟩

end LeanSce.Target

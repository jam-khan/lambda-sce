import LeanSce.Source.Definitions.Elaboration
import LeanSce.Source.Definitions.Statics
import LeanSce.Source.Metatheory.Basic
import LeanSce.Target.Metatheory.Constraints
import LeanSce.Target.Metatheory.Rows

/-!
# Source / Metatheory / WellFormedness

Proofs and supporting constructions for well formedness.
-/

/-! ## Equality Properties -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort)

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
  | module : TyEq i i' → TyEq o o' → TypeShapeEq (.module i o) (.module i' o')
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
  | module hi ho => exact .module hi.symm ho.symm
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
  | module hi ho => exact .module hi ho
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

theorem TyEq.module_inv (h : TyEq (.module i o) (.module i' o')) : TyEq i i' ∧ TyEq o o' := by
  cases h.shape with | module hi ho => exact ⟨hi,ho⟩

end LeanSce.Source

/-! ## Static Well Formed -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort Atom Entry)

theorem Disjoint.of_erase (h : Target.Disjoint Δ.erase r.erase s.erase) : Disjoint Δ r s := by
  simpa [Disjoint, Target.Disjoint, Context.erase] using h

theorem Entails.of_erase (h : Target.Entails Δ.erase g.erase) : Entails Δ g := by
  simpa [Entails, Target.Entails, Context.erase] using h

theorem FreshGuards.of_erase (h : Target.FreshGuards k g.erase) : FreshGuards k g := by
  cases k with
  | type =>
    change g.erase = .gnil at h
    cases g with
    | gnil => rfl
    | gcons => cases h
  | row => simpa [FreshGuards, Target.FreshGuards] using h

theorem WellFormed.of_erase (h : Target.WellFormed Δ.erase a.erase) : WellFormed Δ a := by
  induction a generalizing Δ with
  | tvar i => cases h with | tvar hi => exact .tvar hi
  | rvar i => cases h with | rvar hi => exact .rvar hi
  | unit => exact .unit
  | int => exact .int
  | bool => exact .bool
  | string => exact .string
  | prod a b iha ihb => cases h with | prod ha hb => exact .prod (iha ha) (ihb hb)
  | sum a b iha ihb => cases h with | sum ha hb => exact .sum (iha ha) (ihb hb)
  | arr a b iha ihb => cases h with | arr ha hb => exact .arr (iha ha) (ihb hb)
  | tag l a ih => cases h with | tag ha => exact .tag (ih ha)
  | record r ih => cases h with | record hr => exact .record (ih hr)
  | all k g a ihg iha =>
    cases h with
    | all hf hg ha => exact .all (FreshGuards.of_erase hf) (ihg (by simpa using hg)) (iha (by simpa using ha))
  | ex k g a ihg iha =>
    cases h with
    | ex hf hg ha => exact .ex (FreshGuards.of_erase hf) (ihg (by simpa using hg)) (iha (by simpa using ha))
  | mu a ih => cases h with | mu ha => exact .mu (ih (by simpa using ha))
  | module i o ihi iho =>
    cases h with | arr hi ho =>
      cases hi with | record hi =>
        cases ho with | record ho => exact .module (ihi hi) (iho ho)
  | empty => exact .empty
  | field l a ih => cases h with | field ha => exact .field (ih ha)
  | union r s ihr ihs => cases h with | union hr hs hd => exact .union (ihr hr) (ihs hs) (Disjoint.of_erase hd)
  | gnil => exact .gnil
  | gcons r s g ihr ihs ihg => cases h with | gcons hr hs hg => exact .gcons (ihr hr) (ihs hs) (ihg hg)

theorem Context.Valid.erase (h : Context.Valid Δ) : Target.Context.Valid Δ.erase := by
  induction h with
  | empty => exact .empty
  | extend h hf hg ih => simpa using Target.Context.Valid.extend ih hf.erase (by simpa using hg.erase)

abbrev Context.Normal (Δ : Context) := Δ.erase.Normal

theorem Context.Valid.normal (h : Context.Valid Δ) : Δ.Normal := h.erase.normal

def Subst.Respects (Γ Δ : Context) (σ : Subst) : Prop :=
  Target.Subst.Respects Γ.erase Δ.erase (Subst.erase σ)

theorem WellFormed.subst (h : WellFormed Γ a) (hs : Subst.Respects Γ Δ σ) :
    WellFormed Δ (a.subst σ) := by
  apply WellFormed.of_erase
  simpa using h.erase.subst hs

theorem Disjoint.subst (h : Disjoint Γ r s) (hs : Subst.Respects Γ Δ σ) :
    Disjoint Δ (r.subst σ) (s.subst σ) := by
  apply Disjoint.of_erase
  simpa using h.erase.subst hs

theorem Entails.subst (h : Entails Γ g) (hs : Subst.Respects Γ Δ σ) : Entails Δ (g.subst σ) := by
  apply Entails.of_erase
  simpa using h.erase.subst hs

theorem FreshGuards.subst (h : FreshGuards k g) (σ : Subst) : FreshGuards k (g.subst σ.lift) := by
  apply FreshGuards.of_erase
  simpa using h.erase.subst (Subst.erase σ)

theorem Subst.Respects.lift (hs : Subst.Respects Γ Δ σ) (hf : FreshGuards k g) :
    Subst.Respects (Γ.extend k g) (Δ.extend k (g.subst σ.lift)) σ.lift := by
  simpa [Subst.Respects] using Target.Subst.Respects.lift hs hf.erase

theorem Subst.Respects.open (hn : Δ.Normal) (hk : u.kind = k) (hu : u.WellFormed Δ)
    (hg : Entails Δ (g.open u)) : Subst.Respects (Δ.extend k g) Δ u.openSubst := by
  have hu' : u.erase.WellFormed Δ.erase := by
    cases u <;> exact hu.erase
  have hk' : u.erase.kind = k := by cases u <;> exact hk
  simpa [Subst.Respects] using Target.Subst.Respects.open hn hk' hu' (by simpa using hg.erase)

theorem WellFormed.open (ha : WellFormed (Δ.extend k g) a) (hn : Δ.Normal)
    (hk : u.kind = k) (hu : u.WellFormed Δ) (hg : Entails Δ (g.open u)) :
    WellFormed Δ (a.open u) := ha.subst (Subst.Respects.open hn hk hu hg)

def RenRespects (Γ Δ : Context) (ρ : Nat → Nat) : Prop :=
  Target.RenRespects Γ.erase Δ.erase ρ

theorem WellFormed.rename (h : WellFormed Γ a) (hs : RenRespects Γ Δ ρ) :
    WellFormed Δ (a.rename ρ) := by
  apply WellFormed.of_erase
  simpa using h.erase.rename hs

theorem RenRespects.weaken (Γ : Context) (k : Kind) (g : Guards) :
    RenRespects Γ (Γ.extend k g) Nat.succ := by
  simpa [RenRespects] using Target.RenRespects.weaken Γ.erase k g.erase

theorem WellFormed.weaken (h : WellFormed Γ a) (k : Kind) (g : Guards) :
    WellFormed (Γ.extend k g) (a.rename Nat.succ) := h.rename (RenRespects.weaken Γ k g)

theorem Disjoint.symm (h : Disjoint Δ r s) : Disjoint Δ s r := Disjoint.of_erase (Target.Disjoint.symm h.erase)

@[simp] theorem disjoint_union_left : Disjoint Δ (.union r s) t ↔ Disjoint Δ r t ∧ Disjoint Δ s t := by
  simpa [Disjoint,Target.Disjoint,Context.erase, ← Ty.erase_rowAtoms, Ty.erase] using (Target.disjoint_union_left (Δ := Δ.erase) (r := r.erase) (s := s.erase) (t := t.erase))

@[simp] theorem disjoint_union_right : Disjoint Δ r (.union s t) ↔ Disjoint Δ r s ∧ Disjoint Δ r t := by
  simpa [Disjoint,Target.Disjoint,Context.erase, ← Ty.erase_rowAtoms, Ty.erase] using (Target.disjoint_union_right (Δ := Δ.erase) (r := r.erase) (s := s.erase) (t := t.erase))

@[simp] theorem disjoint_empty_right : Disjoint Δ r .empty := Disjoint.of_erase (Target.disjoint_empty_right (Δ := Δ.erase) (r := r.erase))

def EntryApart (Δ : Context) (e f : Entry) := Target.EntryApart Δ.erase e f

theorem disjoint_iff_entries : Disjoint Δ r s ↔
    ∀ e ∈ r.entries, ∀ f ∈ s.entries, EntryApart Δ e f := by
  simpa [Disjoint,Target.Disjoint,Context.erase,EntryApart] using
    (Target.disjoint_iff_entries (Δ := Δ.erase) (r := r.erase) (s := s.erase))

@[simp] theorem entryApart_label_label : EntryApart Δ (.label l) (.label k) ↔ l ≠ k := Target.entryApart_label_label

@[simp] theorem entryApart_label_tail : EntryApart Δ (.label l) (.tail i) ↔ Atom.labelRow l i ∈ Δ.assumptions := Target.entryApart_label_tail
@[simp] theorem entryApart_tail_label : EntryApart Δ (.tail i) (.label l) ↔ Atom.labelRow l i ∈ Δ.assumptions := Target.entryApart_tail_label
@[simp] theorem entryApart_tail_tail : EntryApart Δ (.tail i) (.tail j) ↔ Atom.rowRow (min i j) (max i j) ∈ Δ.assumptions := Target.entryApart_tail_tail

end LeanSce.Source

/-! ## Row Properties -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort Atom Entry crossAtoms entryAtoms)

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
  case module h₁ h₂ _ _ => exact .module h₁ h₂
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
  case module h₁ h₂ _ _ => exact .module h₁ h₂
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
  case module h₁ h₂ _ _ => exact .module h₁ h₂
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

@[simp] theorem Ty.entries_relabel (r : Row) (old new : String) :
    (r.relabel old new).entries = r.entries.map (Target.Entry.relabel old new) := by
  cases r with
  | rvar => simp [Ty.relabel, Ty.entries, Target.Entry.relabel]
  | empty => simp [Ty.relabel, Ty.entries]
  | field => simp [Ty.relabel, Ty.entries, Target.Entry.relabel]
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
        simpa [Target.Entry.relabel, hk] using hy (by simp [hk])
      · subst k
        have hh := (hx (by simp [hl])).symm
        simpa [Target.Entry.relabel, hl] using hh
      · simpa [Target.Entry.relabel, hl, hk] using hxy
    | tail i =>
      by_cases hl : l = old
      · subst l; simpa [Target.Entry.relabel] using hy (by simp)
      · simpa [Target.Entry.relabel, hl] using hxy
  | tail i =>
    cases y with
    | label k =>
      by_cases hk : k = old
      · subst k; simpa [Target.Entry.relabel] using (hx (by simp)).symm
      · simpa [Target.Entry.relabel, hk] using hxy
    | tail j => simpa [Target.Entry.relabel] using hxy

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

end LeanSce.Source

/-! ## Regularity -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort)

/-- Typing supplies a well-formed result, including polymorphic eliminations. -/
theorem HasType.result_wf (ht : HasType Δ h e a) : Context.Valid Δ → WellFormed Δ a := by
  apply HasType.rec
    (motive_1 := fun Δ _ _ a _ => Context.Valid Δ → WellFormed Δ a)
    (motive_2 := fun Δ _ _ r _ => Context.Valid Δ → WellFormed Δ r)
    (motive_3 := fun Δ a b _ _ => Context.Valid Δ → WellFormed Δ a ∧ WellFormed Δ b)
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
  case letVal => rename_i wa _ _ ihe ihb hΔ; exact ihb hΔ
  case view => rename_i _ _ ihe ihc hΔ; exact (ihc hΔ).2
  case module => rename_i hh wi wo _ ih hΔ; exact .module wi wo
  case capture => rename_i hc wi wo hd hb ihc ihb hΔ; exact .module wi wo
  case run => rename_i hm hp hc ihm ihp ihc hΔ; exact .record (ihm hΔ).module_exports
  case link => rename_i hp hm hc hd ihp ihm ihc hΔ; exact .record (.union (ihp hΔ).record_row (ihm hΔ).module_exports hd)
  case provide => rename_i hp hm hc wj wk hd ihp ihm ihc hΔ; exact .module wk (ihm hΔ).module_exports
  case complete => rename_i hm ih hΔ; exact .record (ih hΔ).module_exports
  case moduleVal => rename_i hh vc hc wi wo hd hb ihc ihb hΔ; exact .module wi wo
  case resid => rename_i vm hm hs wj wk hd ihm ihs hΔ; exact .module wk (ihm hΔ).module_exports
  case invoke => rename_i hm hp ihm ihp hΔ; exact .record (ihm hΔ).module_exports
  case closed => rename_i core hc ih hΔ; exact ⟨(ih hΔ).arr_left, (ih hΔ).arr_right⟩
  case nil => exact .empty
  case cons => rename_i hd ihe ihf hΔ; exact .union (.field (ihe hΔ)) (ihf hΔ) hd
  all_goals assumption

theorem FieldsType.result_wf (ht : FieldsType Δ h fs r) (hΔ : Context.Valid Δ) : WellFormed Δ r :=
  (HasType.record ht).result_wf hΔ |>.record_row

theorem CertType.domain_wf (ht : CertType Δ a b cd) (hΔ : Context.Valid Δ) : WellFormed Δ a := by
  cases ht with | closed _ hc => exact (hc.result_wf hΔ).arr_left

theorem CertType.codomain_wf (ht : CertType Δ a b cd) (hΔ : Context.Valid Δ) : WellFormed Δ b := by
  cases ht with | closed _ hc => exact (hc.result_wf hΔ).arr_right

end LeanSce.Source

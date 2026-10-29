import LeanSce.Target.Definitions.Statics
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Metatheory / Constraints

Proofs and supporting constructions for constraints.
-/

/-! ## Static Constraints -/

namespace LeanSce.Target

def Collects (P : Atom → Prop) (m : Option (List Atom)) : Prop :=
  ∃ xs, m = some xs ∧ ∀ a ∈ xs, P a

@[simp] theorem collects_none : ¬ Collects P none := by simp [Collects]
@[simp] theorem collects_some : Collects P (some xs) ↔ ∀ a ∈ xs, P a := by simp [Collects]

theorem collects_combine (a b : Option (List Atom)) :
    Collects P (do let xs ← a; let ys ← b; pure (xs ++ ys)) ↔
      Collects P a ∧ Collects P b := by
  cases a <;> cases b <;> simp [Collects, List.mem_append, or_imp, forall_and]

theorem collects_flatten_mapM (xs : List α) (f : α → Option (List Atom)) :
    Collects P ((xs.mapM f).map List.flatten) ↔ ∀ x ∈ xs, Collects P (f x) := by
  induction xs with
  | nil => simp [Collects]
  | cons x xs ih =>
    rw [List.mapM_cons]
    cases hx : f x <;> cases hxs : xs.mapM f <;>
      simp_all [Collects, List.mem_append, or_imp, forall_and]

/-- Pairwise presentation of the normalized atomic checker. -/
def EntryApart (Δ : Context) (e f : Entry) : Prop :=
  Collects (· ∈ Δ.assumptions) (entryAtoms e f)

theorem crossAtoms_collects (xs ys : List Entry) :
    Collects P (crossAtoms xs ys) ↔
      ∀ x ∈ xs, ∀ y ∈ ys, Collects P (entryAtoms x y) := by
  induction xs with
  | nil => simp [crossAtoms, Collects]
  | cons x xs ih =>
    change Collects P (do
      let a ← ys.mapM (entryAtoms x)
      let b ← crossAtoms xs ys
      pure (a.flatten ++ b)) ↔ _
    have hh : (do
      let a ← ys.mapM (entryAtoms x)
      let b ← crossAtoms xs ys
      pure (a.flatten ++ b)) =
      (do let a ← (ys.mapM (entryAtoms x)).map List.flatten
          let b ← crossAtoms xs ys
          pure (a ++ b)) := by
      cases ys.mapM (entryAtoms x) <;> rfl
    rw [hh, collects_combine, collects_flatten_mapM, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem disjoint_iff_entries : Disjoint Δ r s ↔
    ∀ e ∈ r.entries, ∀ f ∈ s.entries, EntryApart Δ e f := by
  exact crossAtoms_collects _ _

@[simp] theorem entryApart_label_label :
    EntryApart Δ (.label l) (.label k) ↔ l ≠ k := by
  by_cases h : l = k
  · simp [EntryApart, entryAtoms, Collects, h]
  · simp [EntryApart, entryAtoms, Collects, h]

@[simp] theorem entryApart_label_tail :
    EntryApart Δ (.label l) (.tail i) ↔ Atom.labelRow l i ∈ Δ.assumptions := by
  simp [EntryApart, entryAtoms, Collects]

@[simp] theorem entryApart_tail_label :
    EntryApart Δ (.tail i) (.label l) ↔ Atom.labelRow l i ∈ Δ.assumptions := by
  simp [EntryApart, entryAtoms, Collects]

@[simp] theorem entryApart_tail_tail :
    EntryApart Δ (.tail i) (.tail j) ↔ Atom.rowRow (min i j) (max i j) ∈ Δ.assumptions := by
  simp [EntryApart, entryAtoms, Collects]

@[simp] theorem disjoint_union_left : Disjoint Δ (.union r s) t ↔ Disjoint Δ r t ∧ Disjoint Δ s t := by
  simp [disjoint_iff_entries, Ty.entries, or_imp, forall_and]

@[simp] theorem disjoint_union_right : Disjoint Δ r (.union s t) ↔ Disjoint Δ r s ∧ Disjoint Δ r t := by
  simp [disjoint_iff_entries, Ty.entries, or_imp, forall_and]

@[simp] theorem disjoint_empty_right : Disjoint Δ r .empty := by
  simp [disjoint_iff_entries, Ty.entries]

theorem EntryApart.symm (h : EntryApart Δ x y) : EntryApart Δ y x := by
  cases x <;> cases y <;> simpa [Nat.min_comm, Nat.max_comm, ne_comm] using h

theorem Disjoint.symm (h : Disjoint Δ r s) : Disjoint Δ s r := by
  rw [disjoint_iff_entries] at h ⊢
  intro x hx y hy
  exact (h y hy x hx).symm

def Entry.expand (σ : Subst) : Entry → List Entry
  | .label l => [.label l]
  | .tail i => (σ .row i).entries

@[simp] theorem Ty.entries_subst (r : Row) (σ : Subst) :
    (r.subst σ).entries = r.entries.flatMap (Entry.expand σ) := by
  cases r with
  | rvar i => simp [Ty.subst, Ty.entries, Entry.expand]
  | empty => simp [Ty.subst, Ty.entries]
  | field l a => simp [Ty.subst, Ty.entries, Entry.expand]
  | union r s => simp [Ty.subst, Ty.entries, Ty.entries_subst r, Ty.entries_subst s]

/-- Atomic assumptions are interpreted after a substitution. -/
def Atom.Holds (Δ : Context) (σ : Subst) : Atom → Prop
  | .labelRow l i => Disjoint Δ (.field l .unit) (σ .row i)
  | .rowRow i j => Disjoint Δ (σ .row i) (σ .row j)

/-- Every declaration and every assumed disjointness constraint is respected. -/
def Subst.Respects (Γ Δ : Context) (σ : Subst) : Prop :=
  (∀ k i, Γ.kinds[i]? = some k → WellFormed Δ (σ k i)) ∧
  (∀ a ∈ Γ.assumptions, a.Holds Δ σ)

theorem EntryApart.expand (h : EntryApart Γ e f)
    (hs : ∀ a ∈ Γ.assumptions, a.Holds Δ σ) :
    ∀ x ∈ e.expand σ, ∀ y ∈ f.expand σ, EntryApart Δ x y := by
  cases e with
  | label l =>
    cases f with
    | label k => simpa [Entry.expand] using h
    | tail i =>
      have hd := hs (.labelRow l i) (entryApart_label_tail.mp h)
      simpa [Atom.Holds, disjoint_iff_entries, Ty.entries, Entry.expand] using hd
  | tail i =>
    cases f with
    | label l =>
      have hd := (hs (.labelRow l i) (entryApart_tail_label.mp h)).symm
      simpa [Atom.Holds, disjoint_iff_entries, Ty.entries, Entry.expand] using hd
    | tail j =>
      have hd := hs (.rowRow (min i j) (max i j)) (entryApart_tail_tail.mp h)
      have hh : Disjoint Δ (σ .row i) (σ .row j) := by
        by_cases hij : i ≤ j
        · simpa [Atom.Holds, Nat.min_eq_left hij, Nat.max_eq_right hij] using hd
        · have hji := Nat.le_of_lt (Nat.lt_of_not_ge hij)
          exact (by simpa [Atom.Holds, Nat.min_eq_right hji, Nat.max_eq_left hji] using hd : Disjoint Δ (σ .row j) (σ .row i)).symm
      simpa [disjoint_iff_entries, Entry.expand] using hh

theorem Disjoint.subst (h : Disjoint Γ r s) (hs : Subst.Respects Γ Δ σ) :
    Disjoint Δ (r.subst σ) (s.subst σ) := by
  rw [disjoint_iff_entries] at h ⊢
  simp only [Ty.entries_subst, List.mem_flatMap]
  intro x ⟨e, he, hx⟩ y ⟨f, hf, hy⟩
  exact (h e he f hf).expand hs.2 x hx y hy

end LeanSce.Target

/-! ## Static Renaming -/

namespace LeanSce.Target

def Entry.rename (ρ : Nat → Nat) : Entry → Entry
  | .label l => .label l
  | .tail i => .tail (ρ i)

def Atom.rename (ρ : Nat → Nat) : Atom → Atom
  | .labelRow l i => .labelRow l (ρ i)
  | .rowRow i j => .rowRow (min (ρ i) (ρ j)) (max (ρ i) (ρ j))

private theorem minmax_rename (ρ : Nat → Nat) (i j : Nat) :
    Atom.rowRow (min (ρ (min i j)) (ρ (max i j))) (max (ρ (min i j)) (ρ (max i j))) =
    Atom.rowRow (min (ρ i) (ρ j)) (max (ρ i) (ρ j)) := by
  by_cases h : i ≤ j
  · simp [Nat.min_eq_left h, Nat.max_eq_right h]
  · have h' : j ≤ i := Nat.le_of_lt (Nat.lt_of_not_ge h)
    simp [Nat.min_eq_right h', Nat.max_eq_left h', Nat.min_comm, Nat.max_comm]

@[simp] theorem entryAtoms_rename (ρ : Nat → Nat) (e f : Entry) :
    entryAtoms (e.rename ρ) (f.rename ρ) =
      (entryAtoms e f).map (List.map (Atom.rename ρ)) := by
  cases e <;> cases f <;> simp [Entry.rename, entryAtoms, Atom.rename, minmax_rename]
  split <;> rfl

private theorem mapM_atoms_rename (ρ : Nat → Nat) (x : Entry) (ys : List Entry) :
    ((ys.map (Entry.rename ρ)).mapM (entryAtoms (x.rename ρ))) =
      (ys.mapM (entryAtoms x)).map (List.map (List.map (Atom.rename ρ))) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.mapM_cons, entryAtoms_rename, ih]
    cases entryAtoms x y <;> cases ys.mapM (entryAtoms x) <;> rfl

@[simp] theorem crossAtoms_rename (ρ : Nat → Nat) (xs ys : List Entry) :
    crossAtoms (xs.map (Entry.rename ρ)) (ys.map (Entry.rename ρ)) =
      (crossAtoms xs ys).map (List.map (Atom.rename ρ)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, crossAtoms, mapM_atoms_rename, ih]
    cases ys.mapM (entryAtoms x) <;> cases crossAtoms xs ys <;>
      simp [List.map_flatten, List.map_append]

@[simp] theorem Ty.entries_rename (r : Row) (ρ : Nat → Nat) :
    (r.rename ρ).entries = r.entries.map (Entry.rename ρ) := by
  cases r with
  | rvar => simp [Ty.rename, Ty.entries, Entry.rename]
  | empty => simp [Ty.rename, Ty.entries]
  | field => simp [Ty.rename, Ty.entries, Entry.rename]
  | union r s => simp [Ty.rename, Ty.entries, Ty.entries_rename r, Ty.entries_rename s]

@[simp] theorem Ty.rowAtoms_rename (r s : Row) (ρ : Nat → Nat) :
    (r.rename ρ).rowAtoms (s.rename ρ) =
      (r.rowAtoms s).map (List.map (Atom.rename ρ)) := by
  simp [Ty.rowAtoms]

@[simp] theorem Ty.guardAtoms_rename (g : Guards) (ρ : Nat → Nat) :
    (g.rename ρ).guardAtoms = g.guardAtoms.map (List.map (Atom.rename ρ)) := by
  cases g with
  | gnil => simp [Ty.rename, Ty.guardAtoms]
  | gcons r s g =>
    simp only [Ty.rename, Ty.guardAtoms, Ty.rowAtoms_rename, Ty.guardAtoms_rename g]
    cases r.rowAtoms s <;> cases g.guardAtoms <;> simp [List.map_append]

theorem GuardsEq.rename (h : GuardsEq g h') (ρ : Nat → Nat) :
    GuardsEq (g.rename ρ) (h'.rename ρ) := by
  obtain ⟨xs, ys, hx, hy, he⟩ := h
  refine ⟨xs.map (Atom.rename ρ), ys.map (Atom.rename ρ), ?_, ?_, ?_⟩
  · simp [hx]
  · simp [hy]
  · intro a
    simp only [List.mem_map]
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b,(he b).mp hb,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b,(he b).mpr hb,rfl⟩

theorem TyEq.rename (h : TyEq a b) (ρ : Nat → Nat) : TyEq (a.rename ρ) (b.rename ρ) := by
  induction h generalizing ρ with
  | refl => exact .refl
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | prod _ _ ih₁ ih₂ => exact .prod (ih₁ ρ) (ih₂ ρ)
  | sum _ _ ih₁ ih₂ => exact .sum (ih₁ ρ) (ih₂ ρ)
  | arr _ _ ih₁ ih₂ => exact .arr (ih₁ ρ) (ih₂ ρ)
  | tag _ ih => exact .tag (ih ρ)
  | record _ ih => exact .record (ih ρ)
  | all hg _ ih => exact .all (hg.rename (liftRen ρ)) (ih (liftRen ρ))
  | ex hg _ ih => exact .ex (hg.rename (liftRen ρ)) (ih (liftRen ρ))
  | mu _ ih => exact .mu (ih (liftRen ρ))
  | field _ ih => exact .field (ih ρ)
  | union _ _ ih₁ ih₂ => exact .union (ih₁ ρ) (ih₂ ρ)
  | union_empty => exact .union_empty
  | union_comm => exact .union_comm
  | union_assoc => exact .union_assoc

@[simp] theorem Atom.shift_eq_rename (a : Atom) : a.shift = a.rename Nat.succ := by
  cases a <;> rfl

theorem Atom.rename_comp (a : Atom) (ρ τ : Nat → Nat) :
    (a.rename ρ).rename τ = a.rename (τ ∘ ρ) := by
  cases a with
  | labelRow => rfl
  | rowRow i j => exact minmax_rename τ (ρ i) (ρ j)

@[simp] theorem Atom.rename_shift (a : Atom) (ρ : Nat → Nat) :
    a.shift.rename (liftRen ρ) = (a.rename ρ).shift := by
  rw [Atom.shift_eq_rename, Atom.shift_eq_rename, Atom.rename_comp, Atom.rename_comp]
  rfl

@[simp] theorem Atom.mentions_zero_rename_lift (a : Atom) (ρ : Nat → Nat) :
    (a.rename (liftRen ρ)).mentions 0 = a.mentions 0 := by
  cases a with
  | labelRow l i => cases i <;> simp [Atom.rename, Atom.mentions, liftRen]
  | rowRow i j =>
    cases i <;> cases j <;>
      simp [Atom.rename, Atom.mentions, liftRen, Nat.add_min_add_right, Nat.add_max_add_right]

def RenRespects (Γ Δ : Context) (ρ : Nat → Nat) : Prop :=
  (∀ k i, Γ.kinds[i]? = some k → Δ.kinds[ρ i]? = some k) ∧
  (∀ a ∈ Γ.assumptions, a.rename ρ ∈ Δ.assumptions)

theorem Disjoint.rename (h : Disjoint Γ r s) (hρ : RenRespects Γ Δ ρ) :
    Disjoint Δ (r.rename ρ) (s.rename ρ) := by
  obtain ⟨xs,hx,ha⟩ := h
  refine ⟨xs.map (Atom.rename ρ), by simp [hx], ?_⟩
  intro a hm
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
  exact hρ.2 b (ha b hb)

theorem FreshGuards.rename (h : FreshGuards k g) (ρ : Nat → Nat) :
    FreshGuards k (g.rename (liftRen ρ)) := by
  cases k with
  | type => change g = .gnil at h; subst g; rfl
  | row =>
    obtain ⟨xs,hx,ha⟩ := h
    refine ⟨xs.map (Atom.rename (liftRen ρ)), by simp [hx], ?_⟩
    intro a hm
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
    simpa using ha b hb

theorem RenRespects.lift (hρ : RenRespects Γ Δ ρ) (k : Kind) (g : Guards) :
    RenRespects (Γ.extend k g) (Δ.extend k (g.rename (liftRen ρ))) (liftRen ρ) := by
  constructor
  · intro q i hi
    cases i with
    | zero => simpa [Context.extend, liftRen] using hi
    | succ i => simpa [Context.extend, liftRen] using hρ.1 q i (by simpa [Context.extend] using hi)
  · intro a ha
    simp only [Context.extend, List.mem_append, List.mem_map] at ha
    rcases ha with hg | ⟨b,hb,rfl⟩
    · apply List.mem_append_left
      simp only [Ty.guardAtoms_rename]
      cases hh : g.guardAtoms with
      | none => simp [hh] at hg
      | some xs =>
        simp only [Option.getD_some, Option.map_some]
        exact List.mem_map.mpr ⟨a, by simpa [hh] using hg, rfl⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨b.rename ρ, hρ.2 b hb, by rw [← Atom.rename_shift]⟩

theorem RenRespects.weaken (Γ : Context) (k : Kind) (g : Guards) :
    RenRespects Γ (Γ.extend k g) Nat.succ := by
  constructor
  · intro q i hi
    simpa [Context.extend] using hi
  · intro a ha
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨a, ha, by simp⟩

theorem WellFormed.rename (h : WellFormed Γ a) (hρ : RenRespects Γ Δ ρ) :
    WellFormed Δ (a.rename ρ) := by
  induction h generalizing Δ ρ with
  | tvar h => exact .tvar (hρ.1 _ _ h)
  | rvar h => exact .rvar (hρ.1 _ _ h)
  | unit => exact .unit
  | int => exact .int
  | bool => exact .bool
  | string => exact .string
  | prod _ _ ih₁ ih₂ => exact .prod (ih₁ hρ) (ih₂ hρ)
  | sum _ _ ih₁ ih₂ => exact .sum (ih₁ hρ) (ih₂ hρ)
  | arr _ _ ih₁ ih₂ => exact .arr (ih₁ hρ) (ih₂ hρ)
  | tag _ ih => exact .tag (ih hρ)
  | record _ ih => exact .record (ih hρ)
  | all hf _ _ ihg iha => exact .all (hf.rename ρ) (ihg (hρ.lift _ _)) (iha (hρ.lift _ _))
  | ex hf _ _ ihg iha => exact .ex (hf.rename ρ) (ihg (hρ.lift _ _)) (iha (hρ.lift _ _))
  | mu _ ih => exact .mu (ih (hρ.lift _ _))
  | empty => exact .empty
  | field _ ih => exact .field (ih hρ)
  | union _ _ hd ih₁ ih₂ => exact .union (ih₁ hρ) (ih₂ hρ) (hd.rename hρ)
  | gnil => exact .gnil
  | gcons _ _ _ ih₁ ih₂ ih₃ => exact .gcons (ih₁ hρ) (ih₂ hρ) (ih₃ hρ)

theorem WellFormed.weaken (h : WellFormed Γ a) (k : Kind) (g : Guards) :
    WellFormed (Γ.extend k g) (a.rename Nat.succ) :=
  h.rename (RenRespects.weaken Γ k g)

end LeanSce.Target

/-! ## Static Expansion -/

namespace LeanSce.Target

def RowsCollect (P : Atom → Prop) (r s : Row) : Prop := Collects P (r.rowAtoms s)

def Atom.Interprets (P : Atom → Prop) (σ : Subst) : Atom → Prop
  | .labelRow l i => RowsCollect P (.field l .unit) (σ .row i)
  | .rowRow i j => RowsCollect P (σ .row i) (σ .row j)

private theorem entryAtoms_comm (e f : Entry) : entryAtoms e f = entryAtoms f e := by
  cases e with
  | label l =>
    cases f with
    | label k => by_cases h : l = k <;> simp [entryAtoms, h, ne_comm]
    | tail => rfl
  | tail i =>
    cases f with
    | label => rfl
    | tail j => simp [entryAtoms, Nat.min_comm, Nat.max_comm]

theorem rowsCollect_iff_entries : RowsCollect P r s ↔
    ∀ x ∈ r.entries, ∀ y ∈ s.entries, Collects P (entryAtoms x y) :=
  crossAtoms_collects _ _

theorem rowsCollect_comm : RowsCollect P r s ↔ RowsCollect P s r := by
  simp only [rowsCollect_iff_entries]
  constructor
  · intro h x hx y hy; rw [entryAtoms_comm]; exact h y hy x hx
  · intro h x hx y hy; rw [entryAtoms_comm]; exact h y hy x hx

private theorem entryAtoms_interprets (P : Atom → Prop) (σ : Subst) (e f : Entry) :
    Collects (Atom.Interprets P σ) (entryAtoms e f) ↔
      ∀ x ∈ e.expand σ, ∀ y ∈ f.expand σ, Collects P (entryAtoms x y) := by
  cases e with
  | label l =>
    cases f with
    | label k =>
      by_cases h : l = k <;> simp [entryAtoms, Collects, Entry.expand, h]
    | tail i =>
      change Collects (Atom.Interprets P σ) (some [.labelRow l i]) ↔ _
      rw [collects_some]
      simp only [List.mem_singleton, forall_eq, Atom.Interprets, Entry.expand,
        rowsCollect_iff_entries, Ty.entries]
  | tail i =>
    cases f with
    | label l =>
      change Collects (Atom.Interprets P σ) (some [.labelRow l i]) ↔ _
      rw [collects_some]
      simp only [List.mem_singleton, forall_eq, Atom.Interprets, Entry.expand]
      rw [rowsCollect_comm, rowsCollect_iff_entries]
      simp only [Ty.entries, List.mem_singleton, forall_eq]
    | tail j =>
      change Collects (Atom.Interprets P σ) (some [.rowRow (min i j) (max i j)]) ↔ _
      rw [collects_some]
      simp only [List.mem_singleton, forall_eq, Atom.Interprets, Entry.expand]
      by_cases h : i ≤ j
      · rw [Nat.min_eq_left h, Nat.max_eq_right h]
        exact rowsCollect_iff_entries
      · have h' : j ≤ i := Nat.le_of_lt (Nat.lt_of_not_ge h)
        rw [Nat.min_eq_right h', Nat.max_eq_left h', rowsCollect_comm]
        exact rowsCollect_iff_entries

theorem rowsCollect_subst (P : Atom → Prop) (r s : Row) (σ : Subst) :
    RowsCollect P (r.subst σ) (s.subst σ) ↔
      Collects (Atom.Interprets P σ) (r.rowAtoms s) := by
  rw [rowsCollect_iff_entries]
  change _ ↔ RowsCollect (Atom.Interprets P σ) r s
  rw [rowsCollect_iff_entries]
  simp only [Ty.entries_subst, List.mem_flatMap]
  constructor
  · intro h e he f hf
    apply (entryAtoms_interprets P σ e f).mpr
    intro x hx y hy
    exact h x ⟨e,he,hx⟩ y ⟨f,hf,hy⟩
  · intro h x ⟨e,he,hx⟩ y ⟨f,hf,hy⟩
    exact (entryAtoms_interprets P σ e f).mp (h e he f hf) x hx y hy

@[simp] theorem guardCollects_cons :
    Collects P (Ty.gcons r s g).guardAtoms ↔ RowsCollect P r s ∧ Collects P g.guardAtoms :=
  by simpa only [Ty.guardAtoms, RowsCollect] using (collects_combine (P := P) (r.rowAtoms s) g.guardAtoms)

theorem guardCollects_subst (P : Atom → Prop) (g : Guards) (σ : Subst) :
    Collects P (g.subst σ).guardAtoms ↔ Collects (Atom.Interprets P σ) g.guardAtoms := by
  cases g with
  | gnil => simp [Ty.subst, Ty.guardAtoms, Collects]
  | gcons r s g =>
    simp only [Ty.subst, guardCollects_cons, rowsCollect_subst,
      guardCollects_subst P g σ]
    rfl

theorem Collects.mono (h : Collects P m) (hpq : ∀ a, P a → Q a) : Collects Q m := by
  obtain ⟨xs,hx,ha⟩ := h
  exact ⟨xs,hx,fun a hm => hpq a (ha a hm)⟩

private theorem rowsCollect_fresh_left (r : Row) : RowsCollect (fun a => a.mentions 0 = true) (.rvar 0) r := by
  rw [rowsCollect_iff_entries]
  simp only [Ty.entries, List.mem_singleton, forall_eq]
  intro y hy
  cases y <;> simp [entryAtoms, Collects, Atom.mentions]

private theorem Atom.interprets_fresh {a : Atom} (h : a.mentions 0 = true) (σ : Subst) :
    a.Interprets (fun a => a.mentions 0 = true) σ.lift := by
  cases a with
  | labelRow l i =>
    have hi : i = 0 := by exact (beq_iff_eq.mp h).symm
    subst i
    simp [Atom.Interprets, Subst.lift, Ty.var, RowsCollect,
      Ty.rowAtoms, Ty.entries, crossAtoms, entryAtoms, Collects, Atom.mentions]
  | rowRow i j =>
    have hij : i = 0 ∨ j = 0 := by
      rcases Bool.or_eq_true_iff.mp h with hi | hj
      · exact Or.inl (beq_iff_eq.mp hi).symm
      · exact Or.inr (beq_iff_eq.mp hj).symm
    rcases hij with rfl | rfl
    · exact rowsCollect_fresh_left _
    · exact rowsCollect_comm.mp (rowsCollect_fresh_left _)

theorem FreshGuards.subst (h : FreshGuards k g) (σ : Subst) :
    FreshGuards k (g.subst σ.lift) := by
  cases k with
  | type => change g = .gnil at h; subst g; rfl
  | row =>
    change Collects (fun a => a.mentions 0 = true) (g.subst σ.lift).guardAtoms
    rw [guardCollects_subst]
    exact Collects.mono (h : Collects (fun a => a.mentions 0 = true) g.guardAtoms)
      (fun a ha => Atom.interprets_fresh ha σ)

theorem Entails.subst (h : Entails Γ g) (hs : Subst.Respects Γ Δ σ) :
    Entails Δ (g.subst σ) := by
  change Collects (· ∈ Δ.assumptions) (g.subst σ).guardAtoms
  rw [guardCollects_subst]
  exact Collects.mono (h : Collects (· ∈ Γ.assumptions) g.guardAtoms) (fun a ha => hs.2 a ha)

theorem Atom.holds_of_guard {g : Guards} {a : Atom} (hg : g.guardAtoms = some xs) (ha : a ∈ xs)
    (he : Entails Δ (g.subst σ)) : a.Holds Δ σ := by
  change Collects (· ∈ Δ.assumptions) (g.subst σ).guardAtoms at he
  rw [guardCollects_subst] at he
  obtain ⟨ys,hy,he⟩ := he
  have hxy : xs = ys := Option.some.inj (hg.symm.trans hy)
  subst ys
  exact he a ha

end LeanSce.Target

/-! ## Static Well Formed -/

namespace LeanSce.Target

def Atom.Normal : Atom → Prop
  | .labelRow .. => True
  | .rowRow i j => i ≤ j

def Context.Normal (Δ : Context) : Prop := ∀ a ∈ Δ.assumptions, a.Normal

private theorem entryAtoms_normal (h : Collects (fun _ => True) (entryAtoms e f)) :
    Collects Atom.Normal (entryAtoms e f) := by
  cases e with
  | label l =>
    cases f with
    | label k => by_cases he : l = k <;> simp_all [entryAtoms, Collects]
    | tail i => simp [entryAtoms, Collects, Atom.Normal]
  | tail i =>
    cases f with
    | label l => simp [entryAtoms, Collects, Atom.Normal]
    | tail j =>
      simp only [entryAtoms, collects_some, List.mem_singleton, forall_eq, Atom.Normal]
      omega

private theorem guardAtoms_normal {g : Guards} (h : Collects (fun _ => True) g.guardAtoms) :
    Collects Atom.Normal g.guardAtoms := by
  cases g with
  | gnil => simp [Ty.guardAtoms, Collects]
  | gcons r s g =>
    rw [guardCollects_cons] at h ⊢
    constructor
    · rw [rowsCollect_iff_entries] at h ⊢
      intro e he f hf
      exact entryAtoms_normal (h.1 e he f hf)
    · exact guardAtoms_normal h.2

private theorem guardAtoms_getD_normal (g : Guards) :
    ∀ a ∈ g.guardAtoms.getD [], a.Normal := by
  cases hg : g.guardAtoms with
  | none => simp
  | some xs =>
    have hn := guardAtoms_normal (g := g) (show Collects (fun _ => True) g.guardAtoms from ⟨xs,hg,by simp⟩)
    simpa [Collects, hg] using hn

@[simp] theorem Atom.normal_shift (a : Atom) : a.shift.Normal := by
  cases a <;> simp only [Atom.shift, Atom.Normal]
  omega

theorem Context.Normal.extend (Δ : Context) (k : Kind) (g : Guards) :
    (Δ.extend k g).Normal := by
  intro a ha
  simp only [Context.extend, List.mem_append, List.mem_map] at ha
  rcases ha with hg | ⟨b,hb,rfl⟩
  · exact guardAtoms_getD_normal g a hg
  · exact b.normal_shift

theorem Context.Valid.normal (h : Context.Valid Δ) : Δ.Normal := by
  cases h with
  | empty => simp [Context.Normal, Context.empty]
  | extend => exact Context.Normal.extend _ _ _

theorem Entails.extend_self {Δ : Context} (hf : FreshGuards k g) : Entails (Δ.extend k g) g := by
  cases k with
  | type =>
    change g = .gnil at hf
    subst g
    exact ⟨[], by simp [Ty.guardAtoms], by simp⟩
  | row =>
    obtain ⟨xs,hx,_⟩ := hf
    refine ⟨xs,hx,?_⟩
    intro a ha
    apply List.mem_append_left
    simpa [hx] using ha

private theorem Atom.holds_shift {a : Atom} (h : a.Holds Δ σ) (k : Kind) (g : Guards) :
    a.shift.Holds (Δ.extend k g) σ.lift := by
  cases a with
  | labelRow l i =>
    simpa [Atom.Holds, Atom.shift, Subst.lift, Ty.rename] using
      (h.rename (RenRespects.weaken Δ k g))
  | rowRow i j =>
    by_cases hij : i ≤ j
    · simpa [Atom.Holds, Atom.shift, Nat.add_min_add_right, Nat.add_max_add_right,
        Nat.min_eq_left hij, Nat.max_eq_right hij, Subst.lift] using
        (h.rename (RenRespects.weaken Δ k g))
    · have hji : j ≤ i := Nat.le_of_lt (Nat.lt_of_not_ge hij)
      simpa [Atom.Holds, Atom.shift, Nat.add_min_add_right, Nat.add_max_add_right,
        Nat.min_eq_right hji, Nat.max_eq_left hji, Subst.lift] using
        (h.symm.rename (RenRespects.weaken Δ k g))

theorem Subst.Respects.lift (hs : Subst.Respects Γ Δ σ) (hf : FreshGuards k g) :
    Subst.Respects (Γ.extend k g) (Δ.extend k (g.subst σ.lift)) σ.lift := by
  constructor
  · intro q i hi
    cases i with
    | zero =>
      have hq : q = k := by simpa [Context.extend] using hi.symm
      subst q
      cases k with
      | type => exact .tvar rfl
      | row => exact .rvar rfl
    | succ i =>
      exact (hs.1 q i (by simpa [Context.extend] using hi)).weaken _ _
  · intro a ha
    simp only [Context.extend, List.mem_append, List.mem_map] at ha
    rcases ha with hg | ⟨b,hb,rfl⟩
    · cases hh : g.guardAtoms with
      | none => simp [hh] at hg
      | some xs =>
        exact Atom.holds_of_guard hh (by simpa [hh] using hg)
          (Entails.extend_self (hf.subst σ))
    · exact Atom.holds_shift (hs.2 b hb) _ _

theorem WellFormed.subst (h : WellFormed Γ a) (hs : Subst.Respects Γ Δ σ) :
    WellFormed Δ (a.subst σ) := by
  induction h generalizing Δ σ with
  | tvar h => exact hs.1 _ _ h
  | rvar h => exact hs.1 _ _ h
  | unit => exact .unit
  | int => exact .int
  | bool => exact .bool
  | string => exact .string
  | prod _ _ ih₁ ih₂ => exact .prod (ih₁ hs) (ih₂ hs)
  | sum _ _ ih₁ ih₂ => exact .sum (ih₁ hs) (ih₂ hs)
  | arr _ _ ih₁ ih₂ => exact .arr (ih₁ hs) (ih₂ hs)
  | tag _ ih => exact .tag (ih hs)
  | record _ ih => exact .record (ih hs)
  | all hf _ _ ihg iha => exact .all (hf.subst σ) (ihg (hs.lift hf)) (iha (hs.lift hf))
  | ex hf _ _ ihg iha => exact .ex (hf.subst σ) (ihg (hs.lift hf)) (iha (hs.lift hf))
  | mu _ ih => exact .mu (ih (hs.lift (show FreshGuards .type .gnil from rfl)))
  | empty => exact .empty
  | field _ ih => exact .field (ih hs)
  | union _ _ hd ih₁ ih₂ => exact .union (ih₁ hs) (ih₂ hs) (hd.subst hs)
  | gnil => exact .gnil
  | gcons _ _ _ ih₁ ih₂ ih₃ => exact .gcons (ih₁ hs) (ih₂ hs) (ih₃ hs)

private theorem Atom.holds_id {a : Atom} {Δ : Context} (ha : a ∈ Δ.assumptions) (hn : a.Normal) :
    a.Holds Δ Subst.id := by
  cases a with
  | labelRow l i =>
    refine ⟨[.labelRow l i], ?_, ?_⟩
    · simp [Ty.rowAtoms, Ty.entries, crossAtoms, entryAtoms, Subst.id, Ty.var]
    · simpa using ha
  | rowRow i j =>
    refine ⟨[.rowRow i j], ?_, ?_⟩
    · simp [Ty.rowAtoms, Ty.entries, crossAtoms, entryAtoms, Subst.id, Ty.var,
        Nat.min_eq_left hn, Nat.max_eq_right hn]
    · simpa using ha

private theorem Atom.holds_open_shift {a : Atom} {Δ : Context} (ha : a ∈ Δ.assumptions) (hn : a.Normal) (u : Arg) :
    a.shift.Holds Δ u.openSubst := by
  cases a with
  | labelRow l i =>
    simpa [Atom.shift, Atom.Holds, Arg.openSubst, Subst.id, Ty.var] using
      Atom.holds_id ha hn
  | rowRow i j =>
    simpa [Atom.shift, Atom.Holds, Arg.openSubst, Subst.id, Ty.var,
      Nat.add_min_add_right, Nat.add_max_add_right, Nat.min_eq_left hn, Nat.max_eq_right hn] using
      Atom.holds_id ha hn

theorem Subst.Respects.open (hn : Δ.Normal) (hk : u.kind = k) (hu : u.WellFormed Δ)
    (hg : Entails Δ (g.open u)) : Subst.Respects (Δ.extend k g) Δ u.openSubst := by
  constructor
  · intro q i hi
    cases i with
    | zero =>
      have hq : q = k := by simpa [Context.extend] using hi.symm
      subst q
      cases u <;> cases k <;> simp_all [Arg.kind, Arg.WellFormed, Arg.openSubst]
    | succ i =>
      have hi' : Δ.kinds[i]? = some q := by simpa [Context.extend] using hi
      cases q <;> first | exact .tvar hi' | exact .rvar hi'
  · intro a ha
    simp only [Context.extend, List.mem_append, List.mem_map] at ha
    rcases ha with hg' | ⟨b,hb,rfl⟩
    · cases hh : g.guardAtoms with
      | none => simp [hh] at hg'
      | some xs => exact Atom.holds_of_guard hh (by simpa [hh] using hg') hg
    · exact Atom.holds_open_shift hb (hn b hb) u

theorem WellFormed.open (ha : WellFormed (Δ.extend k g) a) (hn : Δ.Normal)
    (hk : u.kind = k) (hu : u.WellFormed Δ) (hg : Entails Δ (g.open u)) :
    WellFormed Δ (a.open u) :=
  ha.subst (Subst.Respects.open hn hk hu hg)

end LeanSce.Target

/-! ## Static Equality -/

namespace LeanSce.Target

/-- Only binder-local normalized guard sets are needed for equality substitution;
    strict type-binder guard syntax need not hold at raw equality intermediates. -/
def Ty.BinderLocal : Ty s → Prop
  | .prod a b | .sum a b | .arr a b => a.BinderLocal ∧ b.BinderLocal
  | .tag _ a | .record a | .mu a | .field _ a => a.BinderLocal
  | .all _ g a | .ex _ g a => FreshGuards .row g ∧ a.BinderLocal
  | .union r s => r.BinderLocal ∧ s.BinderLocal
  | _ => True

theorem FreshGuards.local (h : FreshGuards k g) : FreshGuards .row g := by
  cases k with
  | row => exact h
  | type => change g = .gnil at h; subst g; exact ⟨[], by simp [Ty.guardAtoms], by simp⟩

theorem GuardsEq.collects_iff (he : GuardsEq g h) :
    Collects P g.guardAtoms ↔ Collects P h.guardAtoms := by
  obtain ⟨xs,ys,hx,hy,he⟩ := he
  simp only [hx,hy,collects_some]
  constructor
  · intro hp a ha; exact hp a ((he a).mpr ha)
  · intro hp a ha; exact hp a ((he a).mp ha)

theorem GuardsEq.local (he : GuardsEq g h) : FreshGuards .row g ↔ FreshGuards .row h :=
  he.collects_iff

private theorem guardsEq_from_collects {g h : Guards} (hx : g.guardAtoms = some xs)
    (he : ∀ P : Atom → Prop, Collects P g.guardAtoms ↔ Collects P h.guardAtoms) : GuardsEq g h := by
  obtain ⟨ys,hy,hyx⟩ := (he (· ∈ xs)).mp ⟨xs,hx,fun _ ha => ha⟩
  obtain ⟨xs',hx',hxy⟩ := (he (· ∈ ys)).mpr ⟨ys,hy,fun _ ha => ha⟩
  have hxx : xs = xs' := Option.some.inj (hx.symm.trans hx')
  subst xs'
  exact ⟨xs,ys,hx,hy,fun a => ⟨hxy a,hyx a⟩⟩

theorem GuardsEq.subst_lift (he : GuardsEq g h) (hg : FreshGuards .row g) (σ : Subst) :
    GuardsEq (g.subst σ.lift) (h.subst σ.lift) := by
  obtain ⟨xs,hx,_⟩ := hg.subst σ
  apply guardsEq_from_collects hx
  intro P
  rw [guardCollects_subst, guardCollects_subst]
  exact he.collects_iff

theorem TyEq.binderLocal (he : TyEq a b) : a.BinderLocal ↔ b.BinderLocal := by
  induction he with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | prod _ _ ih₁ ih₂ | sum _ _ ih₁ ih₂ | arr _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | tag _ ih | record _ ih | mu _ ih | field _ ih => exact ih
  | all hg _ ih | ex hg _ ih => exact and_congr hg.local ih
  | union _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | union_empty => simp [Ty.BinderLocal]
  | union_comm => exact and_comm
  | union_assoc => exact and_assoc

theorem WellFormed.binderLocal (hw : WellFormed Γ a) : a.BinderLocal := by
  induction hw with
  | tvar | rvar | unit | int | bool | string | empty | gnil | gcons => trivial
  | prod _ _ ih₁ ih₂ | sum _ _ ih₁ ih₂ | arr _ _ ih₁ ih₂ => exact ⟨ih₁,ih₂⟩
  | tag _ ih | record _ ih | mu _ ih | field _ ih => exact ih
  | all hg _ _ _ ih | ex hg _ _ _ ih => exact ⟨hg.local,ih⟩
  | union _ _ _ ih₁ ih₂ => exact ⟨ih₁,ih₂⟩

theorem TyEq.subst_of_local (he : TyEq a b) (ha : a.BinderLocal) (σ : Subst) :
    TyEq (a.subst σ) (b.subst σ) := by
  induction he generalizing σ with
  | refl => exact .refl
  | symm he ih => exact .symm (ih (he.binderLocal.mpr ha) σ)
  | trans he₁ _ ih₁ ih₂ => exact .trans (ih₁ ha σ) (ih₂ (he₁.binderLocal.mp ha) σ)
  | prod _ _ ih₁ ih₂ => exact .prod (ih₁ ha.1 σ) (ih₂ ha.2 σ)
  | sum _ _ ih₁ ih₂ => exact .sum (ih₁ ha.1 σ) (ih₂ ha.2 σ)
  | arr _ _ ih₁ ih₂ => exact .arr (ih₁ ha.1 σ) (ih₂ ha.2 σ)
  | tag _ ih => exact .tag (ih ha σ)
  | record _ ih => exact .record (ih ha σ)
  | all hg _ ih => exact .all (hg.subst_lift ha.1 σ) (ih ha.2 σ.lift)
  | ex hg _ ih => exact .ex (hg.subst_lift ha.1 σ) (ih ha.2 σ.lift)
  | mu _ ih => exact .mu (ih ha σ.lift)
  | field _ ih => exact .field (ih ha σ)
  | union _ _ ih₁ ih₂ => exact .union (ih₁ ha.1 σ) (ih₂ ha.2 σ)
  | union_empty => exact .union_empty
  | union_comm => exact .union_comm
  | union_assoc => exact .union_assoc

/-- Equality substitution needs a well-formed source endpoint; raw intermediate
    equality derivations may use noncanonical presentations of binder guards. -/
theorem TyEq.subst (he : TyEq a b) (ha : WellFormed Γ a) (σ : Subst) :
    TyEq (a.subst σ) (b.subst σ) := he.subst_of_local ha.binderLocal σ

end LeanSce.Target

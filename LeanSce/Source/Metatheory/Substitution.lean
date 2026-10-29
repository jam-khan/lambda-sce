import LeanSce.Source.Definitions.Statics
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.WellFormedness
import LeanSce.Target.Metatheory.Constraints
import LeanSce.Target.Metatheory.Substitution

/-!
# Source / Metatheory / Substitution

Proofs and supporting constructions for substitution.
-/

/-! ## Row Substitution -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort Atom Entry)

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

end LeanSce.Source

/-! ## Static Equality -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort)

def Ty.BinderLocal : Ty s → Prop
  | .prod a b | .sum a b | .arr a b | .module a b => a.BinderLocal ∧ b.BinderLocal
  | .tag _ a | .record a | .mu a | .field _ a => a.BinderLocal
  | .all _ g a | .ex _ g a => FreshGuards .row g ∧ a.BinderLocal
  | .union r s => r.BinderLocal ∧ s.BinderLocal
  | _ => True

theorem FreshGuards.local (h : FreshGuards k g) : FreshGuards .row g :=
  FreshGuards.of_erase (Target.FreshGuards.local h.erase)

theorem GuardsEq.local (he : GuardsEq g h) : FreshGuards .row g ↔ FreshGuards .row h := by
  constructor
  · intro hf; exact FreshGuards.of_erase ((Target.GuardsEq.local he.erase).mp hf.erase)
  · intro hf; exact FreshGuards.of_erase ((Target.GuardsEq.local he.erase).mpr hf.erase)

theorem GuardsEq.of_erase (he : Target.GuardsEq g.erase h.erase) : GuardsEq g h := by
  simpa only [GuardsEq,Target.GuardsEq,Ty.erase_guardAtoms] using he

theorem GuardsEq.subst_lift (he : GuardsEq g h) (hg : FreshGuards .row g) (σ : Subst) :
    GuardsEq (g.subst σ.lift) (h.subst σ.lift) := by
  have hh := Target.GuardsEq.subst_lift he.erase hg.erase (Subst.erase σ)
  apply GuardsEq.of_erase
  simpa only [Ty.erase_subst,Subst.erase_lift] using hh

theorem GuardsEq.rename (he : GuardsEq g h) (ρ : Nat → Nat) :
    GuardsEq (g.rename ρ) (h.rename ρ) := by
  have hh := Target.GuardsEq.rename he.erase ρ
  apply GuardsEq.of_erase
  simpa only [Ty.erase_rename] using hh

theorem TyEq.rename (h : TyEq a b) (ρ : Nat → Nat) : TyEq (a.rename ρ) (b.rename ρ) := by
  induction h generalizing ρ
  case refl => exact .refl
  case symm _ ih => exact .symm (ih ρ)
  case trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  case prod ih₁ ih₂ => exact .prod (ih₁ ρ) (ih₂ ρ)
  case sum ih₁ ih₂ => exact .sum (ih₁ ρ) (ih₂ ρ)
  case arr ih₁ ih₂ => exact .arr (ih₁ ρ) (ih₂ ρ)
  case module ih₁ ih₂ => exact .module (ih₁ ρ) (ih₂ ρ)
  case tag ih => exact .tag (ih ρ)
  case record ih => exact .record (ih ρ)
  case all hg _ ih => exact .all (GuardsEq.rename hg _) (ih _)
  case ex hg _ ih => exact .ex (GuardsEq.rename hg _) (ih _)
  case mu ih => exact .mu (ih _)
  case field ih => exact .field (ih ρ)
  case union ih₁ ih₂ => exact .union (ih₁ ρ) (ih₂ ρ)
  case union_empty => exact .union_empty
  case union_comm => exact .union_comm
  case union_assoc => exact .union_assoc

theorem TyEq.binderLocal (he : TyEq a b) : a.BinderLocal ↔ b.BinderLocal := by
  induction he with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | prod _ _ ih₁ ih₂ | sum _ _ ih₁ ih₂ | arr _ _ ih₁ ih₂ | module _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | tag _ ih | record _ ih | mu _ ih | field _ ih => exact ih
  | all hg _ ih | ex hg _ ih => exact and_congr hg.local ih
  | union _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | union_empty => simp [Ty.BinderLocal]
  | union_comm => exact and_comm
  | union_assoc => exact and_assoc

theorem WellFormed.binderLocal (hw : WellFormed Γ a) : a.BinderLocal := by
  induction hw with
  | tvar | rvar | unit | int | bool | string | empty | gnil | gcons => trivial
  | prod _ _ ih₁ ih₂ | sum _ _ ih₁ ih₂ | arr _ _ ih₁ ih₂ | module _ _ ih₁ ih₂ => exact ⟨ih₁,ih₂⟩
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
  | module _ _ ih₁ ih₂ => exact .module (ih₁ ha.1 σ) (ih₂ ha.2 σ)
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

end LeanSce.Source

/-! ## Equality Substitution -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort)

def Subst.PointwiseEq (σ τ : Subst) : Prop := ∀ k i, TyEq (σ k i) (τ k i)

theorem Subst.PointwiseEq.lift (h : Subst.PointwiseEq σ τ) : Subst.PointwiseEq σ.lift τ.lift := by
  intro k i
  cases i with
  | zero => exact .refl
  | succ i => exact (h k i).rename Nat.succ

theorem FreshGuards.subst_congr (hf : FreshGuards k g) (he : Subst.PointwiseEq σ τ) :
    GuardsEq (g.subst σ.lift) (g.subst τ.lift) := by
  apply GuardsEq.of_erase
  have he' : Target.Subst.PointwiseEq (Subst.erase σ) (Subst.erase τ) := fun k i => (he k i).erase
  simpa only [Ty.erase_subst,Subst.erase_lift] using Target.FreshGuards.subst_congr hf.erase he'

private def SubstEqProperty {s : TySort} (a : Ty s) (σ τ : Subst) : Prop :=
  match s with
  | .guards => True
  | _ => TyEq (a.subst σ) (a.subst τ)

private theorem subst_congr_property (hw : WellFormed Γ a)
    (he : Subst.PointwiseEq σ τ) : SubstEqProperty a σ τ := by
  induction hw generalizing σ τ with
  | tvar => exact he .type _
  | rvar => exact he .row _
  | unit => exact .refl
  | int => exact .refl
  | bool => exact .refl
  | string => exact .refl
  | prod _ _ ih₁ ih₂ => exact .prod (ih₁ he) (ih₂ he)
  | sum _ _ ih₁ ih₂ => exact .sum (ih₁ he) (ih₂ he)
  | arr _ _ ih₁ ih₂ => exact .arr (ih₁ he) (ih₂ he)
  | module _ _ ih₁ ih₂ => exact .module (ih₁ he) (ih₂ he)
  | tag _ ih => exact .tag (ih he)
  | record _ ih => exact .record (ih he)
  | all hf _ _ _ ih => exact .all (hf.subst_congr he) (ih he.lift)
  | ex hf _ _ _ ih => exact .ex (hf.subst_congr he) (ih he.lift)
  | mu _ ih => exact .mu (ih he.lift)
  | empty => exact .refl
  | field _ ih => exact .field (ih he)
  | union _ _ _ ih₁ ih₂ => exact .union (ih₁ he) (ih₂ he)
  | gnil | gcons => trivial

/-- Equal witnesses yield equal instantiated well-formed ordinary types. -/
theorem WellFormed.subst_congr (hw : WellFormed Γ (a : Typ))
    (he : Subst.PointwiseEq σ τ) : TyEq (a.subst σ) (a.subst τ) :=
  subst_congr_property hw he

inductive ArgEq : Arg → Arg → Prop where
  | type : TyEq a b → ArgEq (.type a) (.type b)
  | row : TyEq r s → ArgEq (.row r) (.row s)

theorem ArgEq.openSubst (h : ArgEq u v) : Subst.PointwiseEq u.openSubst v.openSubst := by
  intro k i
  cases h <;> cases k <;> cases i <;> simp only [Arg.openSubst] <;>
    first | assumption | exact .refl

theorem WellFormed.open_congr (hw : WellFormed Γ (a : Typ)) (he : ArgEq u v) :
    TyEq (a.open u) (a.open v) := hw.subst_congr he.openSubst

/-- Both the body and witness may change by structural equality. -/
theorem TyEq.open_congr (he : TyEq (a : Typ) b) (ha : WellFormed Γ a)
    (hu : ArgEq u v) : TyEq (a.open u) (b.open v) :=
  (ha.open_congr hu).trans (he.subst ha v.openSubst)

theorem GuardsEq.entails_subst (he : GuardsEq g h) (σ : Subst) :
    Entails Δ (g.subst σ) ↔ Entails Δ (h.subst σ) := by
  have hh := Target.GuardsEq.entails_subst (Δ := Δ.erase) he.erase (Subst.erase σ)
  simpa only [Entails,Target.Entails,Context.erase,← Ty.erase_guardAtoms,Ty.erase_subst] using hh

end LeanSce.Source

/-! ## Static Properties -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort)

@[simp] theorem Ty.subst_lift_weaken (a : Ty s) (σ : Subst) :
    (a.rename Nat.succ).subst σ.lift = (a.subst σ).rename Nat.succ := by
  simp only [Ty.subst_rename, Ty.rename_subst, Subst.lift]

theorem Ty.subst_open (a : Ty s) (σ : Subst) (u : Arg) :
    (a.open u).subst σ = (a.subst σ.lift).open (u.subst σ) := by
  simp only [Ty.open, Ty.subst_comp]
  congr 1
  funext k i
  cases i with
  | zero => cases k <;> cases u <;> rfl
  | succ i =>
    simp only [Arg.openSubst, Subst.lift]
    simpa only [Ty.subst_var, Ty.open] using (Ty.open_weaken (σ k i) (u.subst σ)).symm

@[simp] theorem Arg.kind_subst (u : Arg) (σ : Subst) : (u.subst σ).kind = u.kind := by
  cases u <;> rfl

theorem Arg.WellFormed.subst {u : Arg} (hu : u.WellFormed Γ) (hs : Subst.Respects Γ Δ σ) :
    (u.subst σ).WellFormed Δ := by
  cases u <;> exact LeanSce.Source.WellFormed.subst hu hs

private theorem Context.Valid.all_extend (hΓ : Context.Valid Γ)
    (hw : WellFormed Γ (.all k g a)) : Context.Valid (Γ.extend k g) := by
  cases hw with | all hf hg _ => exact .extend hΓ hf hg

private theorem Context.Valid.ex_extend (hΓ : Context.Valid Γ)
    (hw : WellFormed Γ (.ex k g a)) : Context.Valid (Γ.extend k g) := by
  cases hw with | ex hf hg _ => exact .extend hΓ hf hg

/-- Static substitution preserves every target typing rule. -/
theorem HasType.subst (ht : HasType Γ h e a) (hΓ : Context.Valid Γ)
    (hs : Subst.Respects Γ Δ σ) : HasType Δ (h.subst σ) (e.subst σ) (a.subst σ) := by
  revert hΓ hs
  revert Δ σ
  apply HasType.rec
    (motive_1 := fun Γ h e a _ => ∀ (Δ : Context) (σ : Subst), Context.Valid Γ →
      Subst.Respects Γ Δ σ → HasType Δ (h.subst σ) (e.subst σ) (a.subst σ))
    (motive_2 := fun Γ h fs r _ => ∀ (Δ : Context) (σ : Subst), Context.Valid Γ →
      Subst.Respects Γ Δ σ → FieldsType Δ (h.subst σ) (fs.subst σ) (r.subst σ))
    (motive_3 := fun Γ a b cd _ => ∀ (Δ : Context) (σ : Subst), Context.Valid Γ →
      Subst.Respects Γ Δ σ → CertType Δ (a.subst σ) (b.subst σ) (cd.subst σ))
    (t := ht)
  all_goals intros
  all_goals intros
  case query => rename_i hw Δ σ hΓ hs; exact .query (hw.subst hs)
  case unit => rename_i hw Δ σ hΓ hs; exact .unit (hw.subst hs)
  case int => rename_i hw Δ σ hΓ hs; exact .int (hw.subst hs)
  case bool => rename_i hw Δ σ hΓ hs; exact .bool (hw.subst hs)
  case string => rename_i hw Δ σ hΓ hs; exact .string (hw.subst hs)
  case pair => rename_i ihx ihy Δ σ hΓ hs; exact .pair (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case fst => rename_i ih Δ σ hΓ hs; exact .fst (ih Δ σ hΓ hs)
  case snd => rename_i ih Δ σ hΓ hs; exact .snd (ih Δ σ hΓ hs)
  case box => rename_i ihx ihy Δ σ hΓ hs; exact .box (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case lam => rename_i hw hb ih Δ σ hΓ hs; exact .lam (hw.subst hs) (ih Δ σ hΓ hs)
  case recfn => rename_i wa wb hb ih Δ σ hΓ hs; exact .recfn (wa.subst hs) (wb.subst hs) (ih Δ σ hΓ hs)
  case app => rename_i ihf ihx Δ σ hΓ hs; exact .app (ihf Δ σ hΓ hs) (ihx Δ σ hΓ hs)
  case inl => rename_i wb hx ih Δ σ hΓ hs; exact .inl (wb.subst hs) (ih Δ σ hΓ hs)
  case inr => rename_i wa hx ih Δ σ hΓ hs; exact .inr (wa.subst hs) (ih Δ σ hΓ hs)
  case case => rename_i ihx ihl ihr Δ σ hΓ hs; exact .case (ihx Δ σ hΓ hs) (ihl Δ σ hΓ hs) (ihr Δ σ hΓ hs)
  case tag => rename_i ih Δ σ hΓ hs; exact .tag (ih Δ σ hΓ hs)
  case find => rename_i hx hu ih Δ σ hΓ hs; exact .find (ih Δ σ hΓ hs) (hu.subst σ)
  case record => rename_i ih Δ σ hΓ hs; exact .record (ih Δ σ hΓ hs)
  case get =>
    rename_i hx hl ih Δ σ hΓ hs
    exact .get (ih Δ σ hΓ hs) ((hx.result_wf hΓ).record_row.lookup_subst hs hl)
  case merge => rename_i hx hy hd ihx ihy Δ σ hΓ hs; exact .merge (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs) (hd.subst hs)
  case take =>
    rename_i r ls hx hn hl ih Δ σ hΓ hs
    have hw := (hx.result_wf hΓ).record_row
    have ht := HasType.take (ih Δ σ hΓ hs) hn (fun l hmem => by
      obtain ⟨a,ha⟩ := hl l hmem
      exact ⟨a.subst σ,hw.lookup_subst hs ha⟩)
    exact .conv ht (.record (hw.select_subst hs hl).symm) ((HasType.take hx hn hl).result_wf hΓ |>.subst hs)
  case drop =>
    rename_i r ls hx hn hl ih Δ σ hΓ hs
    have hw := (hx.result_wf hΓ).record_row
    have ht := HasType.drop (ih Δ σ hΓ hs) hn (fun l hmem => by
      obtain ⟨a,ha⟩ := hl l hmem
      exact ⟨a.subst σ,hw.lookup_subst hs ha⟩)
    simpa only [Term.subst, Ty.subst, hw.drop_subst hs hl] using ht
  case relabel =>
    rename_i r l a k hx hl hne hd ih Δ σ hΓ hs
    have hw := (hx.result_wf hΓ).record_row
    have hd' := hd.subst hs
    rw [hw.drop_subst hs (by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact ⟨a,hl⟩)] at hd'
    have ht := HasType.relabel (ih Δ σ hΓ hs) (hw.lookup_subst hs hl) hne hd'
    simpa only [Term.subst, Ty.subst, hw.relabel_subst hs hl] using ht
  case tlam =>
    rename_i hw hh hb ih Δ σ hΓ hs
    have hΓ' := hΓ.all_extend hw
    cases hw with
    | all hf hg ha =>
      apply HasType.tlam ((WellFormed.all hf hg ha).subst hs) (hh.subst hs)
      simpa only [Ty.subst_lift_weaken] using ih _ σ.lift hΓ' (hs.lift hf)
  case tapp =>
    rename_i u hf hk hu hg ih Δ σ hΓ hs
    have ht := HasType.tapp (u := u.subst σ) (ih Δ σ hΓ hs) (by simpa using hk) (hu.subst hs)
      (by simpa only [Ty.subst_open] using hg.subst hs)
    simpa only [Term.subst, Ty.subst_open] using ht
  case pack =>
    rename_i u h e hw hk hu hg hx ih Δ σ hΓ hs
    exact HasType.pack (u := u.subst σ) (hw.subst hs) (by simpa using hk) (hu.subst hs)
      (by simpa only [Ty.subst_open] using hg.subst hs)
      (by simpa only [Ty.subst_open] using ih Δ σ hΓ hs)
  case unpack =>
    rename_i hp wb hb ihp ihb Δ σ hΓ hs
    have hw := hp.result_wf hΓ
    have hΓ' := hΓ.ex_extend hw
    cases hw with
    | ex hf hg ha =>
      apply HasType.unpack (ihp Δ σ hΓ hs) (wb.subst hs)
      simpa only [Ty.subst, Ty.subst_lift_weaken] using ihb _ σ.lift hΓ' (hs.lift hf)
  case fold =>
    rename_i hw hx ih Δ σ hΓ hs
    apply HasType.fold (hw.subst hs)
    simpa only [Ty.subst_open, Arg.subst, Ty.subst] using ih Δ σ hΓ hs
  case unfold =>
    rename_i ih Δ σ hΓ hs
    have ht := HasType.unfold (ih Δ σ hΓ hs)
    simpa only [Term.subst, Ty.subst_open, Arg.subst, Ty.subst] using ht
  case add => rename_i ihx ihy Δ σ hΓ hs; exact .add (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case eqInt => rename_i ihx ihy Δ σ hΓ hs; exact .eqInt (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case showInt => rename_i ih Δ σ hΓ hs; exact .showInt (ih Δ σ hΓ hs)
  case concat => rename_i ihx ihy Δ σ hΓ hs; exact .concat (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case ite => rename_i ihc ihx ihy Δ σ hΓ hs; exact .ite (ihc Δ σ hΓ hs) (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case clo =>
    rename_i hh wa hv hc hb ihc ihb Δ σ hΓ hs
    exact .clo (hh.subst hs) (wa.subst hs)
      (by simpa [Value] using hv) (ihc Δ σ hΓ hs) (ihb Δ σ hΓ hs)
  case rclo =>
    rename_i hh wa wb hv hc hb ihc ihb Δ σ hΓ hs
    exact .rclo (hh.subst hs) (wa.subst hs) (wb.subst hs)
      (by simpa [Value] using hv) (ihc Δ σ hΓ hs) (ihb Δ σ hΓ hs)
  case tclo =>
    rename_i hh hw hv hc hb ihc ihb Δ σ hΓ hs
    have hΓ' := hΓ.all_extend hw
    cases hw with
    | all hf hg ha =>
      apply HasType.tclo (hh.subst hs) ((WellFormed.all hf hg ha).subst hs)
        (by simpa [Value] using hv) (ihc Δ σ hΓ hs)
      simpa only [Ty.subst_lift_weaken] using ihb _ σ.lift hΓ' (hs.lift hf)
  case letVal => rename_i wa hx hb ix ib Δ σ hΓ hs; exact .letVal (wa.subst hs) (ix Δ σ hΓ hs) (ib Δ σ hΓ hs)
  case view => rename_i hx hc ix ic Δ σ hΓ hs; exact .view (ix Δ σ hΓ hs) (ic Δ σ hΓ hs)
  case module => rename_i hh wi wo hb ib Δ σ hΓ hs; exact .module (hh.subst hs) (wi.subst hs) (wo.subst hs) (ib Δ σ hΓ hs)
  case capture => rename_i hc wi wo hd hb ic ib Δ σ hΓ hs; exact .capture (ic Δ σ hΓ hs) (wi.subst hs) (wo.subst hs) (hd.subst hs) (ib Δ σ hΓ hs)
  case run => rename_i hm hp hc im ip ic Δ σ hΓ hs; exact .run (im Δ σ hΓ hs) (ip Δ σ hΓ hs) (ic Δ σ hΓ hs)
  case link => rename_i hp hm hc hd ip im ic Δ σ hΓ hs; exact .link (ip Δ σ hΓ hs) (im Δ σ hΓ hs) (ic Δ σ hΓ hs) (hd.subst hs)
  case provide => rename_i hp hm hc wj wk hd ip im ic Δ σ hΓ hs; exact .provide (ip Δ σ hΓ hs) (im Δ σ hΓ hs) (ic Δ σ hΓ hs) (wj.subst hs) (wk.subst hs) (hd.subst hs)
  case complete => rename_i hm im Δ σ hΓ hs; exact .complete (im Δ σ hΓ hs)
  case moduleVal => rename_i hh vc hc wi wo hd hb ic ib Δ σ hΓ hs; exact .moduleVal (hh.subst hs) (by simpa [Value] using vc) (ic Δ σ hΓ hs) (wi.subst hs) (wo.subst hs) (hd.subst hs) (ib Δ σ hΓ hs)
  case resid => rename_i vm hm saved wj wk hd im iss Δ σ hΓ hs; exact .resid (by simpa [Value] using vm) (im Δ σ hΓ hs) (iss Δ σ hΓ hs) (wj.subst hs) (wk.subst hs) (hd.subst hs)
  case invoke => rename_i hm hp im ip Δ σ hΓ hs; exact .invoke (im Δ σ hΓ hs) (ip Δ σ hΓ hs)
  case closed =>
    rename_i core hc ih Δ σ hΓ hs
    exact .closed (by simpa using core) (ih Δ σ hΓ hs)
  case value => rename_i hv ht hh ih Δ σ hΓ hs; exact .value (by simpa [Value] using hv) (ih Δ σ hΓ hs) (hh.subst hs)
  case nil => rename_i hh Δ σ hΓ hs; exact .nil (hh.subst hs)
  case cons => rename_i hx hf hd ihx ihf Δ σ hΓ hs; exact .cons (ihx Δ σ hΓ hs) (ihf Δ σ hΓ hs) (hd.subst hs)
  all_goals
    rename_i ht he hw ih Δ σ hΓ hs
    exact .conv (ih Δ σ hΓ hs) (he.subst (ht.result_wf hΓ) σ) (hw.subst hs)

/-- Field initializers retain order and disjointness under static substitution. -/
theorem FieldsType.subst (ht : FieldsType Γ h fs r) (hΓ : Context.Valid Γ)
    (hs : Subst.Respects Γ Δ σ) : FieldsType Δ (h.subst σ) (fs.subst σ) (r.subst σ) := by
  revert hΓ hs
  revert Δ σ
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Γ h fs r _ => ∀ (Δ : Context) (σ : Subst), Context.Valid Γ →
      Subst.Respects Γ Δ σ → FieldsType Δ (h.subst σ) (fs.subst σ) (r.subst σ))
    (motive_3 := fun _ _ _ _ _ => True)
    (t := ht)
  all_goals intros
  all_goals intros
  all_goals try trivial
  case nil => rename_i hh Δ σ hΓ hs; exact .nil (hh.subst hs)
  case cons =>
    rename_i hx hf hd ihx ihf Δ σ hΓ hs
    exact .cons (hx.subst hΓ hs) (ihf Δ σ hΓ hs) (hd.subst hs)
  case conv =>
    rename_i ht he hw ih Δ σ hΓ hs
    exact .conv (ih Δ σ hΓ hs) (he.subst (ht.result_wf hΓ) σ) (hw.subst hs)

/-- A kind-preserving renaming satisfying all source atoms is an admissible
    parallel substitution. -/
theorem RenRespects.asSubst (hρ : RenRespects Γ Δ ρ) :
    Subst.Respects Γ Δ (Subst.ofRen ρ) := by
  have hh := Target.RenRespects.asSubst hρ
  have he : Subst.erase (Subst.ofRen ρ) = Target.Subst.ofRen ρ := by
    funext k i
    simp [Subst.erase,Subst.ofRen,Target.Subst.ofRen]
  change Target.Subst.Respects Γ.erase Δ.erase (Subst.erase (Subst.ofRen ρ))
  rw [he]
  exact hh

theorem HasType.rename (ht : HasType Γ h e a) (hΓ : Context.Valid Γ)
    (hρ : RenRespects Γ Δ ρ) : HasType Δ (h.rename ρ) (e.rename ρ) (a.rename ρ) := by
  simpa only [Ty.subst_ofRen, Term.rename] using ht.subst hΓ hρ.asSubst

theorem HasType.weaken (ht : HasType Γ h e a) (hΓ : Context.Valid Γ)
    (k : Kind) (g : Guards) :
    HasType (Γ.extend k g) (h.rename Nat.succ) (e.rename Nat.succ) (a.rename Nat.succ) :=
  ht.rename hΓ (RenRespects.weaken Γ k g)

/-- Opening removes a static binder from expression typing. -/
theorem HasType.open (ht : HasType (Δ.extend k g) h e a)
    (hΓ : Context.Valid (Δ.extend k g)) (hn : Δ.Normal)
    (hk : u.kind = k) (hu : u.WellFormed Δ) (hg : Entails Δ (g.open u)) :
    HasType Δ (h.open u) (e.subst u.openSubst) (a.open u) :=
  ht.subst hΓ (Subst.Respects.open hn hk hu hg)

end LeanSce.Source

/-! ## Closing Properties -/

namespace LeanSce.Source

theorem Closing.erase (hθ : Closing θ Δ) : Target.Closing (Subst.erase θ) Δ.erase := by
  constructor
  · intro k i hi
    exact (hθ.1 k i hi).erase
  · intro atom ha
    have hg := (hθ.2 atom ha).erase
    cases atom <;>
      simpa [substGuard,Target.Atom.substGuard,Subst.erase,Ty.erase] using hg

theorem Closing.respects (hθ : Closing θ Δ) : Subst.Respects Δ .empty θ :=
  hθ.erase.respects

theorem Closing.empty (θ : Subst) : Closing θ .empty := by
  constructor
  · intro k i hi; simp [Context.empty] at hi
  · intro atom ha; simp [Context.empty] at ha

end LeanSce.Source

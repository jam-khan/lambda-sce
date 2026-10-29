import LeanSce.Source.Definitions.Elaboration
import LeanSce.Target.Metatheory.Basic

/-!
# Source / Metatheory / Basic

Proofs and supporting constructions for basic.
-/

/-! ## Binding — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort liftRen)

@[simp] theorem Ty.rename_var (ρ : Nat → Nat) (k : Kind) (i : Nat) :
    (Ty.var k i).rename ρ = Ty.var k (ρ i) := by cases k <;> rfl

@[simp] theorem Ty.subst_var (σ : Subst) (k : Kind) (i : Nat) :
    (Ty.var k i).subst σ = σ k i := by cases k <;> rfl

@[simp] theorem liftRen_id : liftRen id = id := by
  funext i
  cases i <;> rfl

@[simp] theorem liftRen_comp (ρ τ : Nat → Nat) :
    liftRen (ρ ∘ τ) = liftRen ρ ∘ liftRen τ := by
  funext i
  cases i <;> rfl

@[simp] theorem Ty.rename_id (a : Ty s) : a.rename id = a := by
  induction a <;> simp_all [Ty.rename]

theorem Ty.rename_comp (a : Ty s) (ρ τ : Nat → Nat) :
    (a.rename τ).rename ρ = a.rename (ρ ∘ τ) := by
  induction a generalizing ρ τ <;> simp_all [Ty.rename]

@[simp] theorem Subst.lift_id : Subst.id.lift = Subst.id := by
  funext k i
  cases i <;> simp [Subst.id, Subst.lift]

@[simp] theorem Ty.subst_id (a : Ty s) : a.subst Subst.id = a := by
  induction a <;> simp_all [Ty.subst, Subst.id, Ty.var]

@[simp] theorem Subst.lift_ofRen (ρ : Nat → Nat) :
    (Subst.ofRen ρ).lift = Subst.ofRen (liftRen ρ) := by
  funext k i
  cases i <;> simp [Subst.ofRen, Subst.lift, liftRen]

theorem Ty.subst_ofRen (a : Ty s) (ρ : Nat → Nat) :
    a.subst (Subst.ofRen ρ) = a.rename ρ := by
  induction a generalizing ρ <;> simp_all [Ty.subst, Ty.rename, Subst.ofRen, Ty.var]

/-- Substitution after renaming; needed when opening type/row binders. -/
theorem Ty.subst_rename (a : Ty s) (σ : Subst) (ρ : Nat → Nat) :
    (a.rename ρ).subst σ = a.subst (fun k i => σ k (ρ i)) := by
  induction a generalizing σ ρ <;> simp_all only [Ty.rename, Ty.subst]
  all_goals congr 1 <;> (try congr 1) <;>
    first | rfl | (congr 1; funext k i; cases i <;> rfl)

/-- Renaming a substituted type, including substitutions under binders. -/
theorem Ty.rename_subst (a : Ty s) (ρ : Nat → Nat) (σ : Subst) :
    (a.subst σ).rename ρ = a.subst (fun k i => (σ k i).rename ρ) := by
  induction a generalizing ρ σ <;> simp_all only [Ty.subst, Ty.rename]
  all_goals congr 1 <;> (try congr 1) <;>
    first | rfl | (congr 1; funext k i; cases i <;> simp [Subst.lift, Ty.rename_comp, Function.comp_def, liftRen])

theorem Subst.lift_comp (σ τ : Subst) :
    Subst.lift (fun k i => (τ k i).subst σ) = fun k i => (τ.lift k i).subst σ.lift := by
  funext k i
  cases i with
  | zero => simp [Subst.lift]
  | succ i => simp [Subst.lift, Ty.subst_rename, Ty.rename_subst]

theorem Ty.subst_comp (a : Ty s) (σ τ : Subst) :
    (a.subst τ).subst σ = a.subst (fun k i => (τ k i).subst σ) := by
  induction a generalizing σ τ <;> simp_all [Ty.subst, Subst.lift_comp]

/-- A closed substitution cannot capture index zero introduced by a binder. -/
@[simp] theorem Subst.lift_zero (σ : Subst) (k : Kind) :
    σ.lift k 0 = .var k 0 := rfl

@[simp] theorem Ty.open_weaken (a : Ty s) (u : Arg) :
    (a.rename Nat.succ).open u = a := by
  simp only [Ty.open, Ty.subst_rename]
  have h : (fun k i => u.openSubst k i.succ) = Subst.id := by
    funext k i
    cases u <;> cases k <;> rfl
  rw [h]
  exact Ty.subst_id a

end LeanSce.Source

/-! ## Rows — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort Atom Entry entryAtoms crossAtoms)

@[simp] theorem Ty.rowAtoms_empty_left (r : Row) : Ty.rowAtoms .empty r = some [] := by
  simp [Ty.rowAtoms, Ty.entries, crossAtoms]

theorem disjoint_empty_left (Δ : Context) (r : Row) : Disjoint Δ .empty r := by
  exact ⟨[], Ty.rowAtoms_empty_left r, by simp⟩

theorem disjoint_distinct_fields (Δ : Context) (a b : Typ) (h : l ≠ k) :
    Disjoint Δ (.field l a) (.field k b) := by
  refine ⟨[], ?_, by simp⟩
  simp [Ty.rowAtoms, Ty.entries, crossAtoms, entryAtoms, h]

theorem not_disjoint_same_label (Δ : Context) (l : String) (a b : Typ) :
    ¬ Disjoint Δ (.field l a) (.field l b) := by
  simp [Disjoint, Ty.rowAtoms, Ty.entries, crossAtoms, entryAtoms]

end LeanSce.Source

/-! ## Equality — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort)

theorem Absent.subst (h : Absent l a) (σ : Subst) : Absent l (a.subst σ) := by
  induction h <;> simp only [Ty.subst] <;> constructor <;> assumption

theorem Unique.subst (h : Unique l a b) (σ : Subst) :
    Unique l (a.subst σ) (b.subst σ) := by
  induction h with
  | here => exact .here
  | left _ ha ih => exact .left ih (ha.subst σ)
  | right ha _ ih => exact .right (ha.subst σ) ih

end LeanSce.Source

/-! ## Syntax — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

@[simp] theorem Arg.subst_id (u : Arg) : u.subst Subst.id = u := by
  cases u <;> simp [Arg.subst]

@[simp] theorem Term.subst_id (e : Term s) : e.subst Subst.id = e := by
  induction e <;> simp_all [Term.subst]

/-- Substitution changes no value/nonvalue boundary, including captured code. -/
@[simp] theorem Term.isValue_subst (e : Term s) (σ : Subst) :
    (e.subst σ).isValue = e.isValue := by
  induction e generalizing σ <;> simp_all [Term.subst, Term.isValue]
  case moduleVal cap c i o body ihcap ihbody =>
    cases cap <;> simp_all [Term.subst, Term.isValue]

@[simp] theorem Term.isCore_subst (e : Term s) (σ : Subst) :
    (e.subst σ).isCore = e.isCore := by
  induction e generalizing σ <;> simp_all [Term.subst, Term.isCore]

theorem Arg.subst_comp (u : Arg) (σ τ : Subst) :
    (u.subst τ).subst σ = u.subst (fun k i => (τ k i).subst σ) := by
  cases u <;> simp [Arg.subst, Ty.subst_comp]

/-- Composition reaches every annotation and every stored body. In the source
    instantiation of this lemma, that includes retained adapter certificates. -/
theorem Term.subst_comp (e : Term s) (σ τ : Subst) :
    (e.subst τ).subst σ = e.subst (fun k i => (τ k i).subst σ) := by
  induction e generalizing σ τ <;>
    simp_all [Term.subst, Ty.subst_comp, Arg.subst_comp, Subst.lift_comp]

end LeanSce.Source

/-! ## Typing — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

theorem ValueType.inclusion (hv : ValueType Δ v a) (hh : WellFormed Δ h) : HasType Δ h v a :=
  .value hv.1 hv.2 hh

/-- Native query is available at any well-formed ambient type, including scalars. -/
theorem query_typed (hh : WellFormed Δ h) : HasType Δ h .query h := .query hh

/-- No value-binding frame is introduced by a type abstraction. -/
theorem poly_identity_typed : HasType .empty .unit
    (.tlam .type .gnil (.lam (.tvar 0) (.snd .query)))
    (.all .type .gnil (.arr (.tvar 0) (.tvar 0))) := by
  apply HasType.tlam
  · apply WellFormed.all (k := .type) (g := .gnil) rfl WellFormed.gnil
    exact .arr (.tvar rfl) (.tvar rfl)
  · exact .unit
  · apply HasType.lam (.tvar rfl)
    exact .snd (.query (.prod .unit (.tvar rfl)))

end LeanSce.Source

/-! ## Adapters — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

/-- Equality generates a closed function typable at every well-formed ambient. -/
theorem identity_adapter_typed (ha : WellFormed Δ a) (hb : WellFormed Δ b)
    (hab : TyEq a b) (hh : WellFormed Δ h) :
    HasType Δ h (identityAdapter a) (.arr a b) := by
  apply HasType.conv (b := .arr a b) _ (.arr .refl hab) (.arr ha hb)
  apply HasType.box (.unit hh)
  apply HasType.lam ha
  exact .snd (.query (.prod .unit ha))

/-- The arrow template consumes its argument through the contravariant adapter,
    calls the original function, then adapts the result. -/
theorem arrow_adapter_typed
    (ha : WellFormed Δ a) (hb : WellFormed Δ b)
    (hc : WellFormed Δ c) (_hd : WellFormed Δ d)
    (downTyped : ∀ h, WellFormed Δ h → HasType Δ h down (.arr c a))
    (upTyped : ∀ h, WellFormed Δ h → HasType Δ h up (.arr b d))
    (hh : WellFormed Δ h) :
    HasType Δ h (arrowAdapter a b c down up) (.arr (.arr a b) (.arr c d)) := by
  apply HasType.box (.unit hh)
  apply HasType.lam (.arr ha hb)
  apply HasType.lam hc
  have he : WellFormed Δ (.prod (.prod .unit (.arr a b)) c) := .prod (.prod .unit (.arr ha hb)) hc
  apply HasType.app (upTyped _ he)
  apply HasType.app
  · exact .snd (.fst (.query he))
  · exact .app (downTyped _ he) (.snd (.query he))

end LeanSce.Source

/-! ## Semantics — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

/-- S1.3, in the stronger form that does not require a typing premise. -/
theorem step_deterministic (h₁ : Step ν e e₁) (h₂ : Step ν e e₂) : e₁ = e₂ := by
  exact Option.some.inj (h₁.2.symm.trans h₂.2)

theorem value_no_step (hv : Value e) : step ν e = none := by
  cases e <;> simp_all [Value, step, Term.isValue]

theorem value_irreducible (hv : Value e) : ¬ Step ν e e' := by
  intro hs
  have h := hs.2
  rw [value_no_step (ν := ν) hv] at h
  cases h

theorem query_step (hv : Value ν) : Step ν .query ν := ⟨hv, rfl⟩

theorem box_value (hν : Value ν) (hv : Value v) (hw : Value w) :
    Step ν (.box v w) w := by
  refine ⟨hν, ?_⟩
  simp only [Value] at hv hw
  simp [step, Term.isValue, hv, hw]

end LeanSce.Source

/-! ## Type Erasure — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort)

@[simp] theorem Ty.erase_var (k : Kind) (i : Nat) :
    (Ty.var k i).erase = Target.Ty.var k i := by cases k <;> rfl

@[simp] theorem Ty.erase_rename (a : Ty s) (ρ : Nat → Nat) :
    (a.rename ρ).erase = a.erase.rename ρ := by
  induction a generalizing ρ <;> simp_all [Ty.rename, Ty.erase, Target.Ty.rename]

@[simp] theorem Subst.erase_lift (σ : Subst) :
    Subst.erase σ.lift = (Subst.erase σ).lift := by
  funext k i
  cases i <;> simp [Subst.erase, Subst.lift, Target.Subst.lift]

@[simp] theorem Ty.erase_subst (a : Ty s) (σ : Subst) :
    (a.subst σ).erase = a.erase.subst (Subst.erase σ) := by
  induction a generalizing σ <;> simp_all [Ty.subst, Ty.erase, Target.Ty.subst, Subst.erase]

@[simp] theorem Arg.erase_openSubst (u : Arg) :
    Subst.erase u.openSubst = u.erase.openSubst := by
  funext k i
  cases u <;> cases i <;> cases k <;> rfl

@[simp] theorem Ty.erase_open (a : Ty s) (u : Arg) :
    (a.open u).erase = a.erase.open u.erase := by
  simp [Ty.open, Target.Ty.open]

end LeanSce.Source

/-! ## Static Erasure — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort Atom Entry crossAtoms)

@[simp] theorem Ty.erase_entries (r : Row) : r.erase.entries = r.entries := by
  cases r with
  | rvar => simp [Ty.erase, Ty.entries, Target.Ty.entries]
  | empty => simp [Ty.erase, Ty.entries, Target.Ty.entries]
  | field => simp [Ty.erase, Ty.entries, Target.Ty.entries]
  | union r s => simp [Ty.erase, Ty.entries, Target.Ty.entries, Ty.erase_entries r, Ty.erase_entries s]

@[simp] theorem Ty.erase_rowAtoms (r s : Row) : r.erase.rowAtoms s.erase = r.rowAtoms s := by
  simp [Ty.rowAtoms, Target.Ty.rowAtoms]

@[simp] theorem Ty.erase_guardAtoms (g : Guards) : g.erase.guardAtoms = g.guardAtoms := by
  cases g with
  | gnil => simp [Ty.erase, Ty.guardAtoms, Target.Ty.guardAtoms]
  | gcons r s g => simp [Ty.erase, Ty.guardAtoms, Target.Ty.guardAtoms, Ty.erase_guardAtoms g]

@[simp] theorem Context.erase_extend (Δ : Context) (k : Kind) (g : Guards) :
    (Δ.extend k g).erase = Δ.erase.extend k g.erase := by
  simp [Context.erase, Context.extend, Target.Context.extend]

theorem Disjoint.erase (h : Disjoint Δ r s) : Target.Disjoint Δ.erase r.erase s.erase := by
  simpa [Disjoint, Target.Disjoint, Context.erase] using h

theorem Entails.erase (h : Entails Δ g) : Target.Entails Δ.erase g.erase := by
  simpa [Entails, Target.Entails, Context.erase] using h

theorem FreshGuards.erase (h : FreshGuards k g) : Target.FreshGuards k g.erase := by
  cases k with
  | type => change g = .gnil at h; subst g; rfl
  | row => simpa [FreshGuards, Target.FreshGuards] using h

/-- Static erasure preserves well-formed types, rows, and guard syntax. -/
theorem WellFormed.erase (h : WellFormed Δ a) : Target.WellFormed Δ.erase a.erase := by
  induction h with
  | tvar h => exact .tvar h
  | rvar h => exact .rvar h
  | unit => exact .unit
  | int => exact .int
  | bool => exact .bool
  | string => exact .string
  | prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | arr _ _ ih₁ ih₂ => exact .arr ih₁ ih₂
  | tag _ ih => exact .tag ih
  | record _ ih => exact .record ih
  | all hf _ _ ihg iha =>
      exact .all hf.erase (by simpa using ihg) (by simpa using iha)
  | ex hf _ _ ihg iha =>
      exact .ex hf.erase (by simpa using ihg) (by simpa using iha)
  | mu _ ih => exact .mu (by simpa using ih)
  | module _ _ ihi iho => exact .arr (.record ihi) (.record iho)
  | empty => exact .empty
  | field _ ih => exact .field ih
  | union _ _ hd ih₁ ih₂ => exact .union ih₁ ih₂ hd.erase
  | gnil => exact .gnil
  | gcons _ _ _ ihr ihs ihg => exact .gcons ihr ihs ihg

theorem GuardsEq.erase (h : GuardsEq g h') : Target.GuardsEq g.erase h'.erase := by
  simpa [GuardsEq, Target.GuardsEq] using h

/-- Source equality erases soundly. The converse is deliberately false: a
    source module and a source arrow can erase to the same target type. -/
theorem TyEq.erase (h : TyEq a b) : Target.TyEq a.erase b.erase := by
  induction h with
  | refl => exact .refl
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | arr _ _ ih₁ ih₂ => exact .arr ih₁ ih₂
  | tag _ ih => exact .tag ih
  | record _ ih => exact .record ih
  | all hg _ ih => exact .all hg.erase ih
  | ex hg _ ih => exact .ex hg.erase ih
  | mu _ ih => exact .mu ih
  | field _ ih => exact .field ih
  | module _ _ ih₁ ih₂ => exact .arr (.record ih₁) (.record ih₂)
  | union _ _ ih₁ ih₂ => exact .union ih₁ ih₂
  | union_empty => exact .union_empty
  | union_comm => exact .union_comm
  | union_assoc => exact .union_assoc

end LeanSce.Source

/-! ## Elaboration — facts -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)
open LeanSce.Target

@[simp] theorem elaborate_query : Term.erase .query = Target.Term.query := rfl

/-- Polymorphism remains explicit in the target. -/
@[simp] theorem elaborate_tlam (k : Kind) (g : Guards) (e : Expr) :
    (Term.tlam k g e).erase = .tlam k g.erase e.erase := rfl

theorem compilation_deterministic (h₁ : Compiles e E₁) (h₂ : Compiles e E₂) : E₁ = E₂ :=
  h₁.symm.trans h₂

/-- Runtime value translation has priority over the residual-expression helper. -/
theorem Term.erase_value (e : Term s) (hv : Value e) : Target.Value e.erase := by
  induction e <;> simp_all [Value, Term.isValue, Term.erase, Target.Value, Target.Term.isValue]
  case moduleVal cap c i o body ihcap ihbody =>
    cases cap <;> simp_all [Term.isValue, Term.erase, Target.Term.isValue]

@[simp] theorem Arg.erase_subst (u : Arg) (σ : Subst) :
    (u.subst σ).erase = u.erase.subst (Subst.erase σ) := by
  cases u <;> simp [Arg.subst, Arg.erase, Target.Arg.subst]

/-- Compilation commutes with type/row substitution throughout the full source,
    including captures, runtime residuals, and stored certificate code. -/
theorem Term.erase_subst (e : Term s) (σ : Subst) :
    (e.subst σ).erase = e.erase.subst (Subst.erase σ) := by
  induction e generalizing σ <;>
    simp_all [Term.subst, Term.erase, Target.Term.subst, Target.Ty.subst, Templates.sandbox,
      Templates.captured, Templates.run, Templates.link, Templates.provide,
      Templates.residual, Templates.residualBody, Target.Term.close,
      Target.Term.letIn, Target.Term.ix, apply_ite]

end LeanSce.Source

/-! ## Typing Properties -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort)

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

theorem WellFormed.module_imports (h : WellFormed Δ (.module i o)) : WellFormed Δ i := by
  cases h; assumption

theorem WellFormed.module_exports (h : WellFormed Δ (.module i o)) : WellFormed Δ o := by
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
    (motive_3 := fun _ _ _ _ _ => True)
    (t := ht)
  all_goals intros
  case recfn =>
    rename_i ih
    exact ih.prod_left.prod_left
  case closed => trivial
  all_goals first | assumption | apply WellFormed.prod_left; assumption

end LeanSce.Source

/-! ## Value Typing -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

/-- Ambient independence of values is proved from typing, rather than assumed
    as an extra semantic principle. The mutual field case handles record values. -/
theorem HasType.value_reambient (ht : HasType Δ h e a) :
    Value e → ∀ h', WellFormed Δ h' → HasType Δ h' e a := by
  apply HasType.rec
    (motive_1 := fun Δ _ e a _ => Value e → ∀ h', WellFormed Δ h' → HasType Δ h' e a)
    (motive_2 := fun Δ _ fs r _ => Value fs → ∀ h', WellFormed Δ h' → FieldsType Δ h' fs r)
    (motive_3 := fun _ _ _ _ _ => True)
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
  case moduleVal =>
    rename_i vc tc wi wo hd tb _ _ _ _ hh
    exact .moduleVal hh vc tc wi wo hd tb
  case resid =>
    rename_i vm tm _ wj wk hd _ ih hv h' hh
    exact .resid vm tm (ih hv.2 h' hh) wj wk hd
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

end LeanSce.Source

/-! ## Evaluation -/

namespace LeanSce.Source

/-- A successful bounded evaluation witnesses an actual finite reduction. -/
theorem evaluate_sound (hν : Value ν) (he : evaluate fuel ν e = .done v) :
    Terminates ν e v := by
  induction fuel generalizing e with
  | zero =>
    simp only [evaluate] at he
    split at he
    · cases he
      exact ⟨.refl, by assumption⟩
    · cases he
  | succ n ih =>
    simp only [evaluate] at he
    split at he
    · cases he
      exact ⟨.refl, by assumption⟩
    · split at he
      · cases he
      · rename_i e' hs
        obtain ⟨hsteps, hv⟩ := ih he
        exact ⟨.next ⟨hν, hs⟩ hsteps, hv⟩

/-- Every terminating reduction is found with sufficient fuel. -/
theorem evaluate_complete (he : Terminates ν e v) :
    ∃ fuel, evaluate fuel ν e = .done v := by
  obtain ⟨hs, hv⟩ := he
  induction hs with
  | refl => exact ⟨0, by simp [evaluate, Value] at hv ⊢; exact hv⟩
  | @next e e' v hs _ ih =>
    obtain ⟨n, hn⟩ := ih hv
    have hnval : e.isValue = false := by
      cases h : e.isValue with
      | false => rfl
      | true => exact False.elim (value_irreducible h hs)
    exact ⟨n+1, by simp [evaluate, hnval, hs.2, hn]⟩

end LeanSce.Source

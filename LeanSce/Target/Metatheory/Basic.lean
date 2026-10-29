import LeanSce.Target.Definitions.Semantics
import LeanSce.Target.Definitions.Typing

/-!
# Target / Metatheory / Basic

Proofs and supporting constructions for basic.
-/

/-! ## Binding — facts -/

namespace LeanSce.Target

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
  induction a generalizing ρ τ <;> simp_all [Ty.rename, liftRen_comp]

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

end LeanSce.Target

/-! ## Rows — facts -/

namespace LeanSce.Target

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

end LeanSce.Target

/-! ## Equality — facts -/

namespace LeanSce.Target

theorem Absent.subst (h : Absent l a) (σ : Subst) : Absent l (a.subst σ) := by
  induction h <;> simp only [Ty.subst] <;> constructor <;> assumption

theorem Unique.subst (h : Unique l a b) (σ : Subst) :
    Unique l (a.subst σ) (b.subst σ) := by
  induction h with
  | here => exact .here
  | left _ ha ih => exact .left ih (ha.subst σ)
  | right ha _ ih => exact .right (ha.subst σ) ih

end LeanSce.Target

/-! ## Syntax — facts -/

namespace LeanSce.Target

@[simp] theorem Arg.subst_id (u : Arg) : u.subst Subst.id = u := by
  cases u <;> simp [Arg.subst]

@[simp] theorem Term.subst_id (e : Term s) : e.subst Subst.id = e := by
  induction e <;> simp_all [Term.subst]

/-- Substitution changes no value/nonvalue boundary, including captured code. -/
@[simp] theorem Term.isValue_subst (e : Term s) (σ : Subst) :
    (e.subst σ).isValue = e.isValue := by
  induction e generalizing σ <;> simp_all [Term.subst, Term.isValue]

theorem Arg.subst_comp (u : Arg) (σ τ : Subst) :
    (u.subst τ).subst σ = u.subst (fun k i => (τ k i).subst σ) := by
  cases u <;> simp [Arg.subst, Ty.subst_comp]

/-- Composition reaches every annotation and every stored body. In the source
    instantiation of this lemma, that includes retained adapter certificates. -/
theorem Term.subst_comp (e : Term s) (σ τ : Subst) :
    (e.subst τ).subst σ = e.subst (fun k i => (τ k i).subst σ) := by
  induction e generalizing σ τ <;>
    simp_all [Term.subst, Ty.subst_comp, Arg.subst_comp, Subst.lift_comp]

end LeanSce.Target

/-! ## Typing — facts -/

namespace LeanSce.Target

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

end LeanSce.Target

/-! ## Adapters — facts -/

namespace LeanSce.Target

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

end LeanSce.Target

/-! ## Semantics — facts -/

namespace LeanSce.Target

/-- T1.3, in the stronger form that does not require a typing premise. -/
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

end LeanSce.Target

/-! ## Evaluation -/

namespace LeanSce.Target

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

end LeanSce.Target

/-! ## Operational Properties -/

namespace LeanSce.Target

theorem step_isValue_false (hs : step ν e = some e') : e.isValue = false := by
  cases hv : e.isValue with
  | false => rfl
  | true =>
    have hn := value_no_step (ν := ν) hv
    rw [hn] at hs
    cases hs

/-- Progress for either expressions or ordered field initializers. -/
def CanStep (ν : Expr) (e : Term s) : Prop := Value e ∨ ∃ e', step ν e = some e'

theorem canStep_of_value (hv : Value e) : CanStep ν e := Or.inl hv

theorem step_pair_left (hv : a.isValue = false) :
    step ν (.pair a b) = (step ν a).map (fun a' => .pair a' b) := by
  rw [step]
  simp only [Term.isValue, hv, Bool.false_and, Bool.false_eq_true,
    Bool.not_false, ↓reduceIte]

theorem step_pair_right (ha : Value a) (hb : b.isValue = false) :
    step ν (.pair a b) = (step ν b).map (.pair a) := by
  rw [step]
  simp only [Value] at ha
  simp only [Term.isValue, ha, hb, Bool.true_and, Bool.false_eq_true,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem canStep_pair (ha : CanStep ν a) (hb : CanStep ν b) :
    CanStep ν (.pair a b) := by
  rcases ha with ha | ⟨a', hs⟩
  · rcases hb with hb | ⟨b', hs⟩
    · exact .inl (Bool.and_eq_true_iff.mpr ⟨ha, hb⟩)
    · exact .inr ⟨.pair a b', by rw [step_pair_right ha (step_isValue_false hs), hs]; rfl⟩
  · exact .inr ⟨.pair a' b, by rw [step_pair_left (step_isValue_false hs), hs]; rfl⟩

theorem step_cons_left (hv : a.isValue = false) :
    step ν (.cons l a fs) = (step ν a).map (fun a' => .cons l a' fs) := by
  rw [step]
  simp only [Term.isValue, hv, Bool.false_and, Bool.false_eq_true,
    Bool.not_false, ↓reduceIte]

theorem step_cons_right (ha : Value a) (hf : fs.isValue = false) :
    step ν (.cons l a fs) = (step ν fs).map (.cons l a) := by
  rw [step]
  simp only [Value] at ha
  simp only [Term.isValue, ha, hf, Bool.true_and, Bool.false_eq_true,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem canStep_cons (ha : CanStep ν a) (hf : CanStep ν fs) :
    CanStep ν (.cons l a fs) := by
  rcases ha with ha | ⟨a', hs⟩
  · rcases hf with hf | ⟨fs', hs⟩
    · exact .inl (Bool.and_eq_true_iff.mpr ⟨ha, hf⟩)
    · exact .inr ⟨.cons l a fs', by rw [step_cons_right ha (step_isValue_false hs), hs]; rfl⟩
  · exact .inr ⟨.cons l a' fs, by rw [step_cons_left (step_isValue_false hs), hs]; rfl⟩

theorem step_inl_eq : step ν (.inl t a) = (step ν a).map (.inl t) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_inr_eq : step ν (.inr t a) = (step ν a).map (.inr t) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_tag_eq : step ν (.tag l a) = (step ν a).map (.tag l) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_pack_eq : step ν (.pack u t a) = (step ν a).map (.pack u t) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_fold_eq : step ν (.fold t a) = (step ν a).map (.fold t) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_record_eq : step ν (.record fs) = (step ν fs).map .record := by
  cases hv : fs.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_box_eq : step ν (.box a b) =
    (if !a.isValue then (step ν a).map (fun a' => .box a' b)
     else if b.isValue then some b else (step a b).map (.box a)) := rfl

theorem step_fst_eq : step ν (.fst a) =
    (if !a.isValue then (step ν a).map .fst
     else match a with | .pair x _ => some x | _ => none) := rfl

theorem step_snd_eq : step ν (.snd a) =
    (if !a.isValue then (step ν a).map .snd
     else match a with | .pair _ y => some y | _ => none) := rfl

theorem step_app_eq : step ν (.app f x) =
    (if !f.isValue then (step ν f).map (fun f' => .app f' x)
     else if !x.isValue then (step ν x).map (.app f)
     else match f with
       | .clo cap _ body => some (.box (.pair cap x) body)
       | .rclo cap _ _ body => some (.box (.pair (.pair cap f) x) body)
       | _ => none) := rfl

theorem step_case_eq : step ν (.case a l r) =
    (if !a.isValue then (step ν a).map (fun a' => .case a' l r)
     else match a with
       | .inl _ v => some (.box (.pair ν v) l)
       | .inr _ v => some (.box (.pair ν v) r)
       | _ => none) := rfl

theorem step_find_eq : step ν (.find l a) =
    (if !a.isValue then (step ν a).map (.find l)
     else match a.findTags l with | [v] => some v | _ => none) := rfl

theorem step_get_eq : step ν (.get a l) =
    (if !a.isValue then (step ν a).map (fun a' => .get a' l)
     else match a with | .record fs => fs.lookup l | _ => none) := rfl

theorem step_merge_eq : step ν (.merge a b) =
    (if !a.isValue then (step ν a).map (fun a' => .merge a' b)
     else if !b.isValue then (step ν b).map (.merge a)
     else match a,b with
       | .record fs,.record gs =>
           if fs.labels.all (fun l => !gs.labels.contains l) then some (.record (fs.append gs)) else none
       | _,_ => none) := rfl

theorem step_take_eq : step ν (.take ls a) =
    (if !a.isValue then (step ν a).map (.take ls)
     else match a with
       | .record fs => if ls.all fs.labels.contains then some (.record (fs.filter ls.contains)) else none
       | _ => none) := rfl

theorem step_drop_eq : step ν (.drop ls a) =
    (if !a.isValue then (step ν a).map (.drop ls)
     else match a with
       | .record fs => if ls.all fs.labels.contains then some (.record (fs.filter (fun l => !ls.contains l))) else none
       | _ => none) := rfl

theorem step_relabel_eq : step ν (.relabel l k a) =
    (if !a.isValue then (step ν a).map (.relabel l k)
     else match a with
       | .record fs =>
           if l != k && fs.labels.contains l && !fs.labels.contains k then some (.record (fs.renameFields l k)) else none
       | _ => none) := rfl

theorem step_tapp_eq : step ν (.tapp a u) =
    (if !a.isValue then (step ν a).map (fun a' => .tapp a' u)
     else match a with
       | .tclo cap _ _ body => some (.box cap (body.subst u.openSubst))
       | _ => none) := rfl

theorem step_unpack_eq : step ν (.unpack a body) =
    (if !a.isValue then (step ν a).map (fun a' => .unpack a' body)
     else match a with
       | .pack u _ v => some (.box (.pair ν v) (body.subst u.openSubst))
       | _ => none) := rfl

theorem step_unfold_eq : step ν (.unfold a) =
    (if !a.isValue then (step ν a).map .unfold
     else match a with | .fold _ v => some v | _ => none) := rfl

theorem step_prim_eq : step ν (.prim p args) =
    (if !args.isValue then (step ν args).map (.prim p) else evalPrim p args) := rfl

theorem step_ite_eq : step ν (.ite c a b) =
    (if !c.isValue then (step ν c).map (fun c' => .ite c' a b)
     else match c with | .bool true => some a | .bool false => some b | _ => none) := rfl

end LeanSce.Target

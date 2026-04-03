import LeanSce.Core.Syntax
import LeanSce.Core.BigStep
import LeanSce.Core.SmallStep
import LeanSce.Core.Typing
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics
import LeanSce.SCE.Elaboration
import LeanSce.SCE.Theories

open SCE Core

inductive SStep : SCE.Exp → SCE.Exp → SCE.Exp → Prop where
  | placeholder : SStep ρ e e  -- dummy, replace with real rules

def SStuck (ρ : SCE.Exp) (e : SCE.Exp) : Prop :=
  ¬ SCE.Value e ∧ ¬ ∃ e', SStep ρ e e'

inductive CoreSteps : Core.Exp → Core.Exp → Core.Exp → Prop where
  | refl : CoreSteps v e e
  | step : Step v e e' → CoreSteps v e' e'' → CoreSteps v e e''

theorem ebig_to_steps
    {v e v' : Core.Exp}
    (hval : Core.Value v)
    (hbig : EBig v e v')
    : CoreSteps v e v' ∧ Core.Value v' := by
  sorry

-- ============================================================
-- Backward value reflection
-- If ec is a Core value and es elaborates to ec, then es is
-- a source value.
--
-- Proof sketch (by induction on helab):
--   elit    → lit is Core.Value.vint,   source SCE.Value.vint    ✓
--   eunit   → unit is Core.Value.vunit, source SCE.Value.vunit   ✓
--   eclos   → clos is Core.Value.vclos, source SCE.Value.vclos   ✓
--   mclos   → clos is Core.Value.vclos, source SCE.Value.vmclos  ✓
--   edmrg   → mrg is Core.Value.vmrg,  source SCE.Value.vmrg    ✓ (recursive)
--   elrec   → lrec is Core.Value.vrcd, source SCE.Value.vlrec   ✓ (recursive)
--   equery  → query is not a Core value                → vacuous ✓
--   eapp    → app is not a Core value                  → vacuous ✓
--   ebox    → box is not a Core value                  → vacuous ✓
--   elam    → lam is not a Core value                  → vacuous ✓
--   eproj   → proj is not a Core value                 → vacuous ✓
--   erproj  → rproj is not a Core value                → vacuous ✓
--   enmrg   → app (lam ...) query is not a Core value  → vacuous ✓
--   letb    → app (lam ...) ... is not a Core value    → vacuous ✓
--   openm   → app (lam ...) ... is not a Core value    → vacuous ✓
--   mlink   → app (lam ...) query is not a Core value  → vacuous ✓
--   mstruct sandboxed → box unit ... not a Core value  → vacuous ✓
--   mstruct open_     → box query ... not a Core value → vacuous ✓
--   mfunctor sandboxed → box unit (lam ...) not value  → vacuous ✓
--   mfunctor open_     → lam ... not a Core value      → vacuous ✓
--   mapp    → app is not a Core value                  → vacuous ✓
-- ============================================================

theorem backward_value
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    (helab : elabExp Γ es A ec)
    (hcval : Core.Value ec)
    : SCE.Value es := by
  sorry

-- ============================================================
-- Backward simulation
-- If the Core elaboration can step, the source can step
-- (or is already a value).
-- ============================================================

theorem backward_simulation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec ec' : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    (hcval_env : Core.Value ρc)
    (hstep_core : Step ρc ec ec')
    : SCE.Value es ∨ ∃ es', SStep ρs es es' := by
  sorry

-- ============================================================
-- Source preservation
-- ============================================================

theorem source_preservation
    {Γ A : SCE.Typ} {es es' : SCE.Exp} {ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    (hstep : SStep ρs es es')
    : ∃ A' ec', elabExp Γ es' A' ec' := by
  sorry

theorem source_progress
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : SCE.Value es ∨ ∃ es', SStep ρs es es' := by
  have htyp_ec : HasType (elabTyp Γ) ec (elabTyp A) :=
    type_preservation helab
  have htyp_env : HasType .top ρc (elabTyp Γ) :=
    type_preservation henv
  have hcval_env : Core.Value ρc :=
    elab_value henv henv_val
  have hcore_prog : Core.Value ec ∨ ∃ ec', Step ρc ec ec' :=
    @gprogress (elabTyp Γ) (elabTyp A) ec htyp_ec ρc hcval_env htyp_env
  cases hcore_prog with
  | inl hcval =>
    exact Or.inl (backward_value helab hcval)
  | inr hexists =>
    obtain ⟨ec', hstep_core⟩ := hexists
    exact backward_simulation helab henv henv_val hcval_env hstep_core

theorem source_type_safety
    {A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    (helab : elabExp SCE.Typ.top es A ec)
    : ¬ SStuck SCE.Exp.unit es := by
  intro hstuck
  have h := source_progress helab
    (elabExp.eunit SCE.Typ.top) SCE.Value.vunit
  cases h with
  | inl hval => exact hstuck.1 hval
  | inr hexists =>
    obtain ⟨es', hstep⟩ := hexists
    exact hstuck.2 ⟨es', hstep⟩

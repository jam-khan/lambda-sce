import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics
import LeanSce.SCE.Elaboration
import LeanSce.SCE.Equivalence
import LeanSce.SCE.Theories

open SCE S_Sem

/-
  Capability-safety for λSCE via the sandboxed-functor pattern.

  A module written as `functor_■(A) body` and applied to an argument `varg`
  executes `body` under the environment `ε ; varg` regardless of the caller's
  ambient `ρ`. Consequently, the result depends only on `body` and `varg` —
  never on the rest of the ambient. This realises the Wyvern-style capability
  discipline: authority flows through explicit argument passing, not ambient.
-/

/-- **Sandboxed Functor Confinement.**

    A sandboxed functor applied to a value argument produces a result that
    is independent of the ambient environment at the call site. -/
theorem sandboxed_functor_confinement
    {A B : Typ} {body varg v₁ v₂ ρ₁ ρ₂ : Exp} {ec_body ec_varg : Core.Exp}
    (_hρ₁ : Value ρ₁) (_hρ₂ : Value ρ₂) (hvarg : Value varg)
    (hbody_elab : elabExp (Typ.and Typ.top A) body B ec_body)
    (hvarg_elab : elabExp Typ.top varg A ec_varg)
    (h₁ : BStep ρ₁ (Exp.mapp (Exp.mfunctor Sandbox.sandboxed A body) varg) v₁)
    (h₂ : BStep ρ₂ (Exp.mapp (Exp.mfunctor Sandbox.sandboxed A body) varg) v₂)
    : v₁ = v₂ := by
  -- Invert the outer mapp reductions.
  cases h₁ with
  | app_mclos _ hfun₁ harg₁ hbody₁ =>
    cases hfun₁ with
    | mfunctor_sandboxed _ =>
      cases h₂ with
      | app_mclos _ hfun₂ harg₂ hbody₂ =>
        cases hfun₂ with
        | mfunctor_sandboxed _ =>
          -- harg₁ / harg₂ evaluate the value argument `varg`;
          -- by value self-evaluation, both produce `varg` itself.
          have e₁ := sbig_value_eq harg₁ hvarg
          have e₂ := sbig_value_eq harg₂ hvarg
          subst e₁
          subst e₂
          -- Both bodies now execute under `.mrg .unit varg` — the same env.
          -- Build the elaboration witness for that env under the empty context.
          have hvarg_weak : elabExp (Typ.and Typ.top Typ.top) varg A ec_varg :=
            value_typing_weakening hvarg hvarg_elab
          have henv_elab :
              elabExp Typ.top (Exp.mrg Exp.unit varg) (Typ.and Typ.top A)
                (Core.Exp.mrg Core.Exp.unit ec_varg) :=
            elabExp.edmrg Typ.top Typ.top A Exp.unit varg
              Core.Exp.unit ec_varg
              (elabExp.eunit Typ.top) hvarg_weak
          have henv_val : Value (Exp.mrg Exp.unit varg) :=
            Value.vmrg Value.vunit hvarg
          -- Close via big-step determinism.
          exact bigstep_deterministic_gen hbody_elab henv_elab henv_val
            hbody₁ hbody₂

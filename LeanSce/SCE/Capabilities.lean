import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics
import LeanSce.SCE.Equivalence
import LeanSce.SCE.Determinism

open SCE S_Sem

/-
  Capability-safety for λSCE via the sandboxed-functor pattern.

  A module written as `functor_■(A) body` and applied to an argument `varg`
  executes `body` under the environment `ε ; varg` regardless of the caller's
  ambient `ρ`. Consequently, the result depends only on `body` and `varg` —
  never on the rest of the ambient. This realises the Wyvern-style capability
  discipline: authority flows through explicit argument passing, not ambient.
-/

-- **Sandboxed Functor Confinement** (elabSeal-witnessed).  The sandboxed environment
-- ε ; varg rebuilds through evmrg, so no context disjointness is needed at all —
-- sandboxing is exactly the context-free case.

namespace Seal

variable {Δ : SCE.BrandStore}

theorem source_sandboxed_functor_confinement
    {A B : SCE.Typ} {body varg v₁ v₂ ρ₁ ρ₂ : SCE.Exp} {ec_body ec_varg : Seal.Exp}
    (_hρ₁ : SCE.Value ρ₁) (_hρ₂ : SCE.Value ρ₂) (hvarg : SCE.Value varg)
    (hbody_elab : elabSeal Δ (.and .top A) body B ec_body)
    (hvarg_elab : elabSeal Δ .top varg A ec_varg)
    (h₁ : BStep ρ₁ (SCE.Exp.mapp (.mfunctor .sandboxed A body) varg) v₁)
    (h₂ : BStep ρ₂ (SCE.Exp.mapp (.mfunctor .sandboxed A body) varg) v₂)
    : v₁ = v₂ := by
  cases h₁ with
  | app_mclos _ hfun₁ harg₁ hbody₁ =>
    cases hfun₁ with
    | mfunctor_sandboxed _ =>
      cases h₂ with
      | app_mclos _ hfun₂ harg₂ hbody₂ =>
        cases hfun₂ with
        | mfunctor_sandboxed _ =>
          have e₁ := sbig_value_eq harg₁ hvarg
          have e₂ := sbig_value_eq harg₂ hvarg
          subst e₁
          subst e₂
          exact source_bigstep_deterministic_gen hbody₁ hbody_elab
            (elabSeal.evmrg SCE.Value.vunit hvarg (elabSeal.eunit .top) hvarg_elab disj_top)
            (SCE.Value.vmrg SCE.Value.vunit hvarg) hbody₂

end Seal

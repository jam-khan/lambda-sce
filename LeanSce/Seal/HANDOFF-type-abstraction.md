# Handoff: module sealing with type abstraction — state and next steps

Branch: `lambdae-sub` (contains `main` merged in as of 2026-08-19; `main` = SCE with the
linearized `linkedCore`/`nmrgCore`/`wire` combinators). Everything below is committed
and green: `lake build` succeeds, zero `sorry`, every theorem uses at most `propext`.
Nothing is pushed.

Read first: `LeanSce/Seal/DESIGN.md` §(g) (the design, provenance, scope limits) and this
file. The original plan (all phases, challenges, options A/B/C) is in the chat of
2026-08-19; the executed route is C = **static generative brands**.

---

## 1. What exists (Phases 0–3, done)

| file | what it now contains |
|---|---|
| `Syntax.lean` | `Typ.brand n`; `BrandStore := Nat → Option Typ`, `noBrands`; `substBrand n R : Typ → Typ`; `Exp.wrap n e`, `Exp.seal n R S e`, `Exp.unseal n R S e`; `Value.vwrap`; `Ordinary.obrand`; `genVal (brand _) = unit`; `toplike_dec` brand case |
| `Subtyping.lean` | `Sub.sbrand` (reflexive only — never `brand n <: R`); `sub_refl/sub_trans/sub_toplike` cases |
| `Disjointness.lean` | `Cost.cbrand`; `disj_brand_ne`; `BrandIn`, `disj_brand_notin` (α ∗ B iff α ∉ B); `cost_brand_compose`; `sub_sub_cost` brand case |
| `Casting.lean` | `Cast.cwrap : Cast (wrap n v) (brand n) (wrap n v)` — the ONLY new cast rule; `cast_value/cast_toplike_gen` cases |
| `Typing.lean` | `HasType Δ Γ e A` (Δ : BrandStore threaded everywhere); `reservedLabel = "#f"`; `NoRes`; `WfSig n R S` (disjoint in BOTH views, no reserved label); rules `twrap`, `tseal`, `tunseal` (result type guarded by an equation `T = substBrand n R S` — needed for dependent elimination); `StoreLe`, `storele_noBrands`, `hastype_weaken_store` |
| `SmallStep.lean` | `proxyEnv c := mrg unit (lrec "#f" c)`, `proxyFun := rproj (proj query 1) "#f"`; value coercions `SealV n R : Typ → Exp → Exp → Prop` and `UnsealV` (structural on S; arrow ⇒ proxy closure); `Step.swrap/sseal/ssealv/sunseal/sunsealv`; `sealv_value/unsealv_value/sealv_det/unsealv_det` |
| `CastingLemmas.lean` | all Eᵢ lemmas re-established with brands: `cast_brand_cost`, brand cases in `casts_not_disjoint`, `disjoint_consistent`, `value_weaken`, `cast_determinism`, `cast_trans_wrap`, `cast_preservation`, `cast_progress` |
| `Lookup.lean`, `Determinism.lean` | Δ threaded; new non-value alternatives; `gdeterminism` cases for the new steps |
| `Progress.lean` | `sealv_progress`/`unsealv_progress` (canonical forms per type former); `gprogress` cases |
| `Preservation.lean` | `wfsig_nores`, `nores_subst`, `cost_reserved`, `cost_proxyEnv`, `disj_proxyEnv`, `proxyEnv_typed/value`; `sealv_preservation`/`unsealv_preservation` (proxy typed via `tclos`); `gpreservation` cases |
| `Sealing.lean` | `BrandOpen := Option (Nat × Typ × Typ)`; `viewL/viewR` (match on `o` FIRST so `viewL none T ≡ T` definitionally); `WrapRel`, `RawRel`; **`LRg Δ₁ Δ₂ η o`** with `LR := LRg … none`; `OpenAdm`, `openadm_none`; view lemmas `viewL_and/arr/rcd/int/top`; `sub_subst/sub_viewL/R`; `toplike_subst(_inv)`, `toplike_viewL/R(_inv)`; `lr_value`, `lr_typed` (typing at `viewL o T`/`viewR o T`); `toplike_lr_gen`, `cast_lr` (both generic in `o`, take `hadm : OpenAdm η o`); `SemTyp Δ₁ Δ₂ η`; `fundamental : HasType noBrands Γ e A → SemTyp …` (client typing!); `normalization`, `sealing`, `sealing_providers` restated with `noBrands` |
| `Abstraction.lean` (new) | `OpenBrand Δ₁ Δ₂ η n R₁ R₂` (stores agree, `NoRes`, `¬TopLike`, η n cast-closed) + `.adm`; `mstep_seal/unseal`, `proxyFun_run`, `proxyArg_run`, `seal_proxy_run`, `unseal_proxy_run`; **`coe_lr`** (mutual seal/unseal, induction on S); **`representation_independence`** |
| `Elaboration.lean` | Δ-generic (`seal_type_preservation` holds for any Δ); no `mseal` yet |
| `Correctness.lean`, `Linearization.lean` | store instantiated to `noBrands` (`HasType noBrands …`); `genVal_typed (Δ := noBrands)` pinned where needed; otherwise untouched |
| `Examples.lean` | RI instance: `Sig = {mk : Int → α} & {get : α → Int}`, α = brand 0, impls over `Int` and `{v : Int}`, `impl_related`, `client_typed`, `representation_independence` applied |
| `DESIGN.md` | §(g) added; header/§(d) updated |

Commits (newest first): `LeanSce.lean import` · `de14ba2` DESIGN §(g) · `64114fd` example ·
`da801aa` Abstraction · `6e13f3c` brands + type safety + LRg · `b272159` merge main.

## 2. Conventions / gotchas learned (read before editing)

- **Δ threading**: theorem statements say `HasType Δ …` with `variable {Δ : BrandStore}`
  at file top (Lean includes Δ when the statement mentions it). `Σ` cannot be used as a
  name (Sigma notation). Defs like `LRg`, `SemTyp` take stores explicitly.
- **`tunseal`'s result type is an equation-guarded variable** (`T = substBrand n R S`);
  otherwise `cases ht` at a concrete type fails ("dependent elimination failed").
  Same trick as SCE's `eunfold`. When inverting typing on values, add
  `| tseal _ _ _ _ => nomatch hv` and `| tunseal _ _ _ _ _ => nomatch hv` (arities:
  tseal 4 explicit premises, tunseal 5; in `induction ht with` add one more for the IH).
- **Order of `cases`**: for `HasType Δ Γ v (and A B)` do `cases ht` first, then `cases hv`
  inside `tmrg`; doing `cases hv` first leaves value alternatives with no `ht` inversion.
- `substBrand n R (brand n)` reduces with `simp only [substBrand, if_true]`
  (or `hne, if_false`); at `and/rcd/arr` it reduces by whnf (`simp only [substBrand] at ht`).
- **`LRg` at brands** with `o = some (n,…)`: unfold with `simp only [LRg, hm, if_true]`
  (or `if_false`); with `o = none` the `match` reduces definitionally.
- **`viewL/viewR`** match on `o` first: `viewL none T ≡ T` (definitional, so the
  fundamental lemma needs no rewrites); with variable `o` use `rw [viewL_and] at c₁`
  before `cases c₁`, and `by rw [viewL_and]; exact …` for typing components (`▸` picks
  the wrong direction).
- Coercions are **value relations** (`SealV`), not structural term rewriting: an
  intermediate `mrg (seal…) (seal…)` cannot be typed by `tmrg` under arbitrary Γ.
- `WfSig` needs disjointness in **both** views (`α & Int` vs `Int & Int`); `R` needs
  `NoRes` and (for the LR) `¬TopLike`.
- The user's global Lean guardrail hook BLOCKS `git checkout`, `git restore` (even in
  compound commands). Use `git switch <branch>` and `git archive <ref> <path> | tar -x`.
- Build a single module with `lake build LeanSce.Seal.<Name>`; grep errors with
  `2>&1 | grep -E "^error" -A 10`. Full build ≈ 68 jobs.
- Axiom check: `lake env lean file.lean` with `#print axioms Seal.representation_independence`.

## 3. Phase 4 — the SCE source side (NOT done). Instructions

Goal: a source-level sealing construct that elaborates to `Seal.seal`, with the SCE
metatheory extended and `seal_semantic_preservation` covering it, so "sealed
compilation units" exist end to end. Decision already taken (user confirmed): **mirror**
the target — give the source `wrap`/`seal`/`unseal` value forms and the same
structural big-step coercion, so `EVal` (Correctness.lean, elaboration-shaped,
"up to top-like collapse") gets plain clauses `EVal.wrap` etc. Do NOT make the source
`mseal` transparent: then `EVal` would have to relate an unwrapped source value to a
wrapped target value and `eval_cast_self` breaks.

Suggested order (each step: build green, commit):

1. **`SCE/Syntax.lean`**: `Typ.brand : Nat → Typ` (add to `substTyp`, `LabelIn` no case,
   `SRLookup` no case, `Repr`); `Exp.wrap : Nat → Exp → Exp`, `Exp.mseal : Nat → Typ →
   Typ → Exp → Exp` (n, R, S), `Exp.munseal` likewise; `Value.vwrap`. Optionally a
   source `SCE.substBrand`. Keep names parallel to Seal.
2. **`SCE/Semantics.lean`**: source coercion relations `SSealV n R : Typ → Exp → Exp →
   Prop` / `SUnsealV`, mirroring `Seal.SealV/UnsealV` (arrow case builds a source proxy
   `mclos`/`clos`? — choose `clos (mrg unit (lrec "#f" c)) A (mseal n R B (app
   (rproj (proj query 1) "#f") (munseal n R A (proj query 0))))`; SCE lambdas carry only
   the input type, which is fine since SCE has no casts). `BStep.mseal : BStep ρ e v →
   SSealV n R S v w → BStep ρ (mseal n R S e) w`, `BStep.munseal`, `BStep.wrap`
   (congruence). `SCE/SmallStep.lean`: matching small-step rules.
3. **`SCE/Elaboration.lean`** (SCE→Core, λE has no brands): decide and document. Simplest
   sound choice: `elabExp` has NO rule for `mseal` (Core keeps the brand-free fragment,
   like `fold/unfold` are absent from `elabSeal`); or erase `mseal` to `ce` (identity)
   and `Typ.brand` via `elabTyp` to … there is no Core brand. Recommended: no rule
   (out of Core's scope), and state that in `SCE/Elaboration.lean`'s header.
4. **SCE typing/progress/preservation/equivalence** (`SCE/Preservation.lean`,
   `Progress.lean`, `Equivalence.lean`, `SmallStep.lean`, `Theories.lean`): new cases.
   SCE's typing is `elabExp` (Core-targeting) — if `mseal` has no Core rule, source
   type safety for `mseal` must come from `elabSeal` (Seal-targeting) instead: consider
   proving progress/preservation for `mseal` only in the Seal-targeted development
   (`Correctness.lean` uses `elabSeal` + `EVal`), leaving Core-side theorems untouched.
   Check which SCE theorems induct on `Exp`/`BStep` and would need new alternatives
   (`grep -n "| mlinkn" LeanSce/SCE/*.lean` gives the sites).
5. **`Seal/Elaboration.lean`**: `sealTyp (.brand n) = .brand n`; rule
   `elabSeal.emseal : Δ n = some R? …` — `elabSeal` currently has no store; add the
   store as a parameter of `elabSeal` (or a section variable) since `tseal` needs
   `Δ n = some R`, `NoRes (sealTyp R)`, `WfSig n (sealTyp R) (sealTyp S)`; conclusion
   `elabSeal ctx (mseal n R S se) S (Seal.seal n (sealTyp R) (sealTyp S) ce)` with premise
   `elabSeal ctx se (substTyp… S[n:=R]) ce` — you need `sealTyp (substBrand_src n R S)
   = Seal.substBrand n (sealTyp R) (sealTyp S)` (lemma). Extend
   `seal_type_preservation` (needs `HasType Δ`, so thread Δ into `elabSeal`).
   Also `emunseal`, and `ewrap` for values (`Value.vwrap`), needed by `elabSeal_value`.
6. **`Seal/Correctness.lean`**: `EVal.wrap : EVal R v w → EVal (brand n) (wrap n v)
   (wrap n w)` (type index: brand n; think about whether `EVal` needs the store to know
   R — it is elaboration-shaped, so `EVal (.brand n) (.wrap n v) (.wrap n w)` given
   `EVal R v w` for the R the store says; probably parametrize `EVal` by Δ);
   `seal_semantic_preservation` cases for `BStep.mseal/munseal/wrap`: source `SSealV`
   simulates target `SealV` step-by-step (lemma `eval_sealv : EVal (S[R]) v w → SSealV
   n R S v v' → ∃ w', SealV n (sealTyp R) (sealTyp S) w w' ∧ EVal S v' w'`, by induction on
   S; the arrow case relates the two proxies — `EVal` at arrows is closure-shaped, so
   the proxy closures must be `EVal`-related: check `EVal.clos`'s shape and make the
   source proxy match it exactly). Then `Correctness/Linearization` can drop the
   `noBrands` instantiation (thread Δ).
7. **Sealed separate compilation**: a `seal_separate_compilation_sealed` corollary:
   provider unit `mseal n R S p` linked into a client via `mlink`, statement in the style
   of `seal_separate_compilation` (Correctness.lean:1030). And a source-level RI
   corollary if cheap: source clients typed against `S` ⇒ (via semantic preservation +
   `representation_independence`) same integer.
8. **`Examples.lean`**: the RI example written at the source level and elaborated.
9. `DESIGN.md` §(g) "SCE source side" paragraph; remove the "not done" note; update
   the memory file `~/.claude/projects/…/memory/seal_type_abstraction.md`.

Brand allocation: at the mechanization level `Δ` is a hypothesis; document that the
toolchain allocates distinct brands per sealed unit (like symbols).

## 4. Open questions to settle early in Phase 4

- Does `elabSeal` get the store as an index (`elabSeal Δ Γ e A ce`) or as a section
  variable? Index is cleaner for `seal_type_preservation`.
- Source `SSealV` arrow proxy: SCE `clos v A e` has no codomain annotation; the source
  proxy body will be `mseal n R B (…)` — make sure `EVal`'s closure clause can relate it
  to the target proxy `clos (proxyEnv c) A B (seal …)` (target carries B). If `EVal.clos`
  requires the target's B to be `sealTyp` of something, that is B itself — fine.
- Whether SCE's `Typ.brand` should live in `ModTyp`/signatures too (`sig` types): a
  sealed module's signature `S` is an SCE `Typ` (record intersections), so `Typ.brand`
  suffices; functor import interfaces mention brands as ordinary types.

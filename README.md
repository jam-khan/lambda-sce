# lambda-sce

The Lean 4 mechanization of **λSCE** — a merge calculus with first-class
modules — and its elaboration to the core calculus **λE**. Companion to the
implementation in `SCE-Lang` (OCaml toolchain, interpreter, WasmGC backend).

```console
$ lake build        # Lean 4 (see lean-toolchain); no mathlib dependency
```

Zero `sorry`, zero custom axioms; every theorem depends on `propext` at most.

## Claim map

Where each paper claim is discharged. "Impl." rows are deliberately outside the
mechanization; the evidence named there lives in the `SCE-Lang` test suite.

| claim | file | theorem(s) |
|---|---|---|
| elaboration is deterministic (types and terms) | `SCE/Theories.lean` | `inference_uniqueness`, `elaboration_uniqueness` |
| elaborated code is well-typed λE | `SCE/Theories.lean` | `type_preservation` |
| source evaluation is simulated by elaborated evaluation (open terms) | `SCE/Theories.lean` | `semantic_preservation` |
| whole-program correctness | `SCE/Theories.lean` | `whole_program_correctness` |
| λSCE progress / preservation | `SCE/Progress.lean`, `SCE/Preservation.lean` | `sprogress`, `spreservation` |
| big-step ≡ small-step, both calculi | `SCE/Equivalence.lean`, `Core/BigStep.lean` | `sbig…` lemmas, `step_ebig_eq` |
| evaluation is deterministic (elaborated programs) | `SCE/Theories.lean` | `bigstep_deterministic` |
| the linker's composition term is well-typed | `SCE/Theories.lean`, `SCE/Linearization.lean` | `core_link_typed`, `core_linkn_typed`, `linkedCoreLin_typed` |
| **separate compilation** (link/linkall, open/closed) | `SCE/Theories.lean` | `separate_compilation`, `_closed`, `_n`, `_n_closed` |
| separate compilation for the **shipped** (linearized) combinators | `SCE/Linearization.lean` | `separate_compilation_lin`, `_closed`, `_n`, `_n_closed`, `nmrg_lin` |
| the two link spellings compute the same value | `SCE/Linearization.lean` | `linearization_coherent`, `linearization_coherent_n` |
| recursive linking is a derived form; metatheory inherited | `SCE/RecLinking.lean` | `mrec_elab`, `mrec_progress`, `mrec_preservation`, `mrec_deterministic`, `mrec_correctness` |
| sandboxed functors confine ambient authority | `SCE/Capabilities.lean` | `sandboxed_functor_confinement` |
| Impl.: effects as host capabilities, effect-trace agreement interpreter/wasm | — | `SCE-Lang/test/test_runtime.ml` (trace differentials) |
| Impl.: runtime loader, structural check at load time | — | `SCE-Lang/test/test_runtime.ml` (plugins, dynconfig, upgrade, versions) |
| Impl.: linking commutes across whole/linked/wasm paths | — | `SCE-Lang/test/test_commute.ml` (eight-path differentials) |

## λE^≤ (`LeanSce/Seal/`)

An experimental sibling core calculus: λE's de Bruijn binding discipline + Eᵢ's
subtyping, disjointness, and type-directed restriction (ECOOP 2023), making
**sealing** — `(e : A)` that actually discards components — expressible as an
elaboration target for signature ascription. Design rationale and the full rule
provenance (what is λE's, what is ported from Eᵢ, what is new) in
`LeanSce/Seal/DESIGN.md`. SCE continues to elaborate to Core; the λE^≤
retargeting below is a mechanized sibling pipeline, not a replacement.

| claim | file | theorem(s) |
|---|---|---|
| casting lemma layer (Eᵢ L4–L12: determinism, progress, preservation, transitivity, consistency, value closedness) | `Seal/CastingLemmas.lean` | `disjoint_consistent`, `cast_determinism`, `cast_trans`, `cast_preservation`, `cast_progress`, `value_weaken` |
| determinism (selection **and** casting tamed by one typing hypothesis) | `Seal/Determinism.lean` | `gdeterminism`, `determinism` |
| type soundness | `Seal/Progress.lean`, `Seal/Preservation.lean` | `gprogress`, `gpreservation` |
| casting is a coercion between the logical relations | `Seal/Sealing.lean` | `cast_lr` |
| fundamental lemma of the binary logical relation | `Seal/Sealing.lean` | `fundamental` |
| **sealing**: clients typed against the seal cannot distinguish providers that agree at it | `Seal/Sealing.lean` | `sealing`, `sealing_providers` |
| strong normalization (new for a TDOS merge calculus) | `Seal/Sealing.lean` | `normalization` |
| **type-preserving elaboration** of SCE's module/linking fragment into λE^≤ | `Seal/Elaboration.lean` | `seal_type_preservation`, `wireArgSeal_typed`, `elabSeal_value` |
| **semantic preservation** for the λE^≤ target (simulation up to top-like collapse, `EVal`) | `Seal/Correctness.lean` | `seal_semantic_preservation`, `eval_cast_self` |
| whole-program correctness, λE^≤ target | `Seal/Correctness.lean` | `seal_whole_program_correctness` |
| **separate compilation** for the seal-based link combinators (link/linkn, open/closed) | `Seal/Correctness.lean` | `seal_separate_compilation`, `_closed`, `_n`, `_n_closed` |
| evaluation of elaborated programs is deterministic (λE^≤ target) | `Seal/Correctness.lean` | `mstep_value_determinism` |
| **bind-once (linearized) linking** via the fresh-label wrap; well-typed + separate compilation | `Seal/Linearization.lean` | `linkedSealLin_typed`, `seal_separate_compilation_lin`, `_closed` |
| the two link spellings agree (EVal-level coherence; syntactic coherence is provably the wrong statement here) | `Seal/Linearization.lean` | `linearization_coherent_seal` |

`sealing`, `fundamental`, `cast_lr`, and `normalization` are axiom-free; everything
else in `Seal/` (including the full correctness suite) uses `propext` only.

A syntactic simulation (target value = elaboration of the source value, as the Core
target enjoys) is **false** for λE^≤: beta casts the argument and reseals the result,
and casting a closure at a top-like arrow collapses it to the canonical generator.
`Seal/Correctness.lean` therefore relates values by `EVal` — elaboration up to
top-like collapse — whose key lemma is that casting at a value's own type preserves
the relation (`eval_cast_self`).

The `Seal/Elaboration.lean` retargeting covers every SCE construct except
unions/fix/μ (no casting rules exist for those in either source paper) and makes
two forced changes visible: elaboration rules that extend a context now carry
λE^≤'s disjointness premises, and Core's bind-once combinators
(`nmrgCore`/`linkedCore`, the `(λ⟦Γ⟧. …) ?` self-application) are replaced by
sealing itself — `(? : Γ)` restores the ambient environment, which λE^≤ *forces*
because `Disj Γ Γ` fails for any non-top-like Γ.

`SCE/Linearization.lean` also documents, with the elaboration rules side by
side, why the implementation's bind-once combinators exist at all: effects make
operand order and multiplicity observable, and the pure-calculus coherence
proved there is exactly the statement that the choice is invisible until they
do. `f-ing/` vendors the Coq mechanization of F-ing modules (Rossberg et al.)
for comparison.

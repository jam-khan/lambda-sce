# Polymorphic SCE mechanization

The new calculus lives in [`Target/`](Target/All.lean) and [`Source/`](Source/All.lean), under the `LeanSce.Target` and `LeanSce.Source` namespaces. The earlier [`Core/`](Core/Syntax.lean) and [`SCE/`](SCE/Syntax.lean) developments remain separate. The new development is organized into 62 themed modules: 34 target and 28 source, consolidated from 219 files. This follows the earlier Core/SCE division and the [FE source development](../context/PolyFirstClassEnvs-main/mech/fe_calculus/source/README.md): syntax and elaboration are separate from lemmas and preservation proofs.

**The selected main results T1–T3 and S1–S5 are proved.** This includes adapter coherence, heterogeneous representation independence, execution correspondence in both directions, contextual linking laws, and abstract-module replacement. Optional legacy embedding T4 is outside these proof obligations.

## Read the definitions first

| Question | Start here |
| --- | --- |
| What are target types, terms, and binding operations? | [Target/Definitions/Syntax.lean](Target/Definitions/Syntax.lean) |
| What are rows, static contexts, guards, and type equality? | [Target/Definitions/Statics.lean](Target/Definitions/Statics.lean) |
| What are target typing and canonical adapters? | [Target/Definitions/Typing.lean](Target/Definitions/Typing.lean) |
| How does target evaluation work? | [Target/Definitions/Semantics.lean](Target/Definitions/Semantics.lean) |
| What does the source add? | [Source/Definitions/Types.lean](Source/Definitions/Types.lean), [Statics.lean](Source/Definitions/Statics.lean), [Syntax.lean](Source/Definitions/Syntax.lean), [Typing.lean](Source/Definitions/Typing.lean) |
| How do source modules evaluate and compile? | [Source/Definitions/Semantics.lean](Source/Definitions/Semantics.lean), [Elaboration.lean](Source/Definitions/Elaboration.lean) |
| What may an observation context inspect? | [Source/Definitions/Contexts.lean](Source/Definitions/Contexts.lean), [Target/LogicalRelation/Definitions.lean](Target/LogicalRelation/Definitions.lean) |
| What is an admissible representation relation? | [Target/Abstraction/Definitions.lean](Target/Abstraction/Definitions.lean) |

All calculus and logical-relation definition modules import only other definition modules. Supporting facts live in the proof families below.

The checked source carries interfaces and retained adapter certificates. Its `Mod[I⇒O]` type compiles to `Rec I → Rec O`. Source module operations, `let`, and `view` elaborate to target constructs; polymorphism, packages, recursive types, and native `query`/`box` remain explicit. Parsing, name resolution, and inference belong to the implementation layer.

## Follow the proofs by subject

- **Safety:** `Target/Metatheory/` and `Source/Metatheory/` establish row properties, substitution, canonical forms, preservation, progress, and evaluation facts.
- **Adapters:** `Target/Adapters/` proceeds from typing and termination through normalization/naturality to contextual composition coherence.
- **Compilation:** `Source/Elaboration/Typing.lean` proves typing preservation. `ExecutionRelation.lean` and `ModuleExecution.lean` supply finite execution correspondence; `Correctness.lean` exports the complete results and separate compilation. `Contexts.lean` lifts artifact equivalence through source observation contexts.
- **Linking:** `Source/Linking/Laws.lean` proves confinement and exact retention; `Staging.lean` proves staged and commuting linking in full source contexts.
- **Abstraction:** `Target/Abstraction/` builds the heterogeneous relation and proves representation independence. `Source/Abstraction/Contexts.lean` and `Replacement.lean` transfer it to source modules.

The homogeneous relation in `Target/LogicalRelation/` supports adapter coherence; its definitions and downward-closure properties are separate modules. The heterogeneous relation in `Target/Abstraction/Definitions.lean` permits different hidden witnesses and arbitrary downward-closed typed representation relations; `Infrastructure.lean` develops its basic properties and candidate constructions. Both account for actual reduction steps and include stored code, native environments, and value-restricted capture slots.

## Main theorem map

All names below are public declarations. The `Goals.*` definitions state propositions; they are not axioms or assumed proof obligations.

| Paper result | Declaration | Module |
| --- | --- | --- |
| T1.1 preservation | `Target.preservation` | [Target/Metatheory/Safety.lean](Target/Metatheory/Safety.lean) |
| T1.2 progress | `Target.progress` | [Target/Metatheory/Safety.lean](Target/Metatheory/Safety.lean) |
| T1.3 determinism | `Target.step_deterministic` | [Target/Metatheory/Basic.lean](Target/Metatheory/Basic.lean) |
| T2.1 adapter typing | `Target.adapter_typing` | [Target/Adapters/Typing.lean](Target/Adapters/Typing.lean) |
| T2.2 value termination | `Target.adapter_termination` | [Target/Adapters/Termination.lean](Target/Adapters/Termination.lean) |
| T2.3 exact shape | `Target.adapter_exact_shape` | [Target/Adapters/Termination.lean](Target/Adapters/Termination.lean) |
| T2.4 divergence | `Target.adapter_divergence` | [Target/Adapters/Termination.lean](Target/Adapters/Termination.lean) |
| T2.5 contextual coherence | `Target.adapter_coherence` | [Target/Adapters/Coherence.lean](Target/Adapters/Coherence.lean) |
| T3 representation independence | `Target.representation_independence` | [Target/Abstraction/RepresentationIndependence.lean](Target/Abstraction/RepresentationIndependence.lean) |
| S1.1 preservation | `Source.preservation` | [Source/Metatheory/Safety.lean](Source/Metatheory/Safety.lean) |
| S1.2 progress | `Source.progress` | [Source/Metatheory/Safety.lean](Source/Metatheory/Safety.lean) |
| S1.3 determinism | `Source.step_deterministic` | [Source/Metatheory/Basic.lean](Source/Metatheory/Basic.lean) |
| S1.4 elaboration typing | `Source.elaboration_typing` | [Source/Elaboration/Typing.lean](Source/Elaboration/Typing.lean) |
| S1.5 terminating correspondence | `Source.termination_correspondence` | [Source/Elaboration/Correctness.lean](Source/Elaboration/Correctness.lean) |
| S1.6 divergence correspondence | `Source.divergence_correspondence` | [Source/Elaboration/Correctness.lean](Source/Elaboration/Correctness.lean) |
| S2 separate compilation | `Source.run_separate_compilation`, `link_separate_compilation`, `provide_separate_compilation` | [Source/Elaboration/Correctness.lean](Source/Elaboration/Correctness.lean) |
| S3.1 staging | `Source.staging` | [Source/Linking/Staging.lean](Source/Linking/Staging.lean) |
| S3.2 commuting stages | `Source.commuting_stages` | [Source/Linking/Staging.lean](Source/Linking/Staging.lean) |
| S4.1 confinement | `Source.module_confinement`, `provider_confinement` | [Source/Linking/Laws.lean](Source/Linking/Laws.lean) |
| S4.2 exact retention | `Source.link_export_retention`, `merge_export_retention` | [Source/Linking/Laws.lean](Source/Linking/Laws.lean) |
| S5 abstract-module replacement | `Source.abstract_module_replacement` | [Source/Abstraction/Replacement.lean](Source/Abstraction/Replacement.lean) |

Declaration names are relative to `LeanSce`; for example, the fully qualified T3 theorem is `LeanSce.Target.representation_independence`. Execution correspondence covers the full runtime elaboration relation, including permuted completed records and both representations of an empty-capture module. S5 accepts arbitrary corresponding target representatives.

## Build and audit

From the repository root:

```sh
lake build
```

This builds the earlier development, both new calculi, examples, and [`ProofAudit.lean`](ProofAudit.lean). To request the new development and audit explicitly:

```sh
lake build LeanSce.Target.All LeanSce.Source.All LeanSce.ProofAudit
```

The audit checks the exact main statement/proof bridges and traverses theorem dependencies, including private support proofs. It rejects new axioms, `sorryAx`, and native-evaluation proof axioms. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are allowed.

[Source/Examples.lean](Source/Examples.lean) contains typing examples and the exported prototype corpus with kernel-checked evaluator results. Fuel exhaustion is an operational check, not a proof of divergence; the metatheory uses actual infinite reduction traces.

## Size

Measured with `cloc 2.08`. Code lines include definitions, proofs, and examples; comments and blank lines are counted separately. This excludes `context/`, build artifacts, and the ignored Haskell prototype.

| Scope | Lean files | Code | Comments | Blank | Total lines |
| --- | ---: | ---: | ---: | ---: | ---: |
| Target | 34 | 11,836 | 581 | 1,515 | 13,932 |
| Source | 28 | 11,036 | 544 | 1,372 | 12,952 |
| **New calculi subtotal** | 62 | 22,872 | 1,125 | 2,887 | 26,884 |
| Core | 9 | 1,754 | 44 | 73 | 1,871 |
| SCE | 18 | 6,122 | 414 | 307 | 6,843 |
| Audit and entry points | 3 | 76 | 8 | 6 | 90 |
| **Project total** | 92 | 30,824 | 1,591 | 3,273 | 35,688 |

The last category is `LeanSce/ProofAudit.lean`, `LeanSce.lean`, and `Main.lean`. File counts include each calculus’s `All.lean` import module.

Reproduce the complete count from the repository root:

```sh
cloc LeanSce LeanSce.lean Main.lean --include-ext=lean --skip-uniqueness
```

For the new calculi alone:

```sh
cloc LeanSce/Target LeanSce/Source --include-ext=lean --skip-uniqueness
```

# Source proofs

**Goal:** prove source safety, behavioral correctness of elaboration, separate compilation, staged linking, confinement/export preservation, and abstract-module replacement.

**Status:** **all twelve statements S1–S5 are Lean-checked:** [preservation](LeanSce/Source/Metatheory/Safety.lean), [progress](LeanSce/Source/Metatheory/Safety.lean), [determinism](LeanSce/Source/Metatheory/Basic.lean), [elaboration typing](LeanSce/Source/Elaboration/Typing.lean), [execution correspondence](LeanSce/Source/Elaboration/Correctness.lean), [behavioral separate compilation](LeanSce/Source/Elaboration/Correctness.lean), [staged/commuting linking](LeanSce/Source/Linking/Staging.lean), [confinement](LeanSce/Source/Linking/Laws.lean), [export retention](LeanSce/Source/Linking/Laws.lean), and [abstract-module replacement](LeanSce/Source/Abstraction/Replacement.lean). S5 retains arbitrary corresponding target representatives, rather than requiring canonical erasure. Manual proofs and supporting lemmas follow below. See [target-proofs.MD](target-proofs.MD) and the [mechanization status](LeanSce/MECHANIZATION.md).

| Read | Contents |
| --- | --- |
| [U: source safety lemmas](#u-source-static-and-safety-lemmas) | Static substitution, retained certificates, canonical forms, adapters |
| [E: elaboration](#e-elaboration-and-operational-correspondence) | Runtime correspondence, typing, both directions of finite evaluation |
| [L: contexts and linking](#l-compilation-contexts-and-linking-laws) | Observation contexts, staged execution, module entry |
| [Concrete checks](#concrete-source-and-target-checks) | Query scope, delayed execution, discarded initializers |
| [S1](#s1-source-safety-and-elaboration-correctness), [S2](#s2-behavioral-separate-compilation), [S3](#s3-staged-linking-and-commuting-interfaces), [S4](#s4-module-confinement-and-exact-export-retention), [S5](#s5-abstract-module-replacement) | Main statements, meanings, and proofs |

**Dependency order:** `U.1–U.4 → S1.1–S1.3`; `E.1–E.2 → S1.4`; `source/target safety,E.3–E.5 → S1.5–S1.6`; `source safety → U.5`; `S1,target relations → L.1`; `S1,L → S2–S5`. Forward references to the final theorem section follow this order.

**Notation.** `Δ⊢s v:A` is source value typing; `Δ;H⊢s e:A` is checked source expression typing. `e⇝E` is runtime elaboration and `v~V` its value correspondence. `ν⊢s e⇓v` means finite reduction to a value; `⇑` means an infinite reduction. `θ̄(a)=⟦θ(a)⟧` is the translated substitution. `Vₙ,Eₙ` refer to the target logical relations, not to syntactic value correspondence. All unprefixed U/E/L lemmas below are source lemmas; references to target results say **target** explicitly.

At `Δ;H`, `e₁≈s e₂:A` quantifies over satisfying closing substitutions, typed source ambient values, and all well-typed closing source contexts with a ground result. Expression holes retain their local ambient judgment; value slots require value holes. Runtime closure code, module code, and well-typed stored certificate code are included. Both sides must produce the same ground value or both diverge.

**Repairs made during the proofs.** Checked capture/completion annotations and the runtime residual elaboration are explicit. Certificates retain their generated code under substitution and type erasure. The proof accounts for `view`'s different adapter-prefix order and the residual constructor/value boundary; neither is hidden inside a lockstep-simulation claim. Native environments, polymorphism, recursion, and the original linking/abstraction goals are retained.

## U. Source static and safety lemmas

The judgments below concern the **checked runtime source**: lexical names and aliases have been expanded, matching boundaries carry their stored certificates, and capture forms carry their checked row `C`. Common-core runtime forms and equality are inherited from the target, recursively over source types. Write `⊢s v:A` for ambient-independent source value typing.

### U.1. Static substitution, including certificates

Write `σ:Δ⇒Δ′` when `σ` respects kinds and every declared row guard. Then:

```text
Δ ⊢ U:κ                  ⇒ Δ′ ⊢ σU:κ
Δ ⊢ R # S                ⇒ Δ′ ⊢ σR # σS
Δ ⊢ A ≡ B                ⇒ Δ′ ⊢ σA ≡ σB
Δ ⊢cert d:A⇒B            ⇒ Δ′ ⊢cert σd:σA⇒σB
Δ ⊢s v:A                 ⇒ Δ′ ⊢s σv:σA
Δ ; H ⊢s e:A             ⇒ Δ′ ; σH ⊢s σe:σA.
```

Fresh static extension preserves the same judgments without changing `H`. Also:

```text
absentℓ(A) ⇒ absentℓ(σA)
uniqueℓ(A)=B ⇒ uniqueℓ(σA)=σB.
```

**Proof.** Induct first on the static derivations. Empty rows, distinct labels, assumed atomic constraints, symmetry, and union are the complete constraint cases. The substitution's guard premises discharge the assumed cases. Kinding/equality then follow constructorwise; the additional type case is

```text
Δ⊢I:Row, Δ⊢O:Row
  ⇒ Δ′⊢σI:Row, Δ′⊢σO:Row
  ⇒ Δ′⊢Mod[σI⇒σO]:Type.
```

Under a fresh row binder, every newly introduced constraint still mentions that binder after substitution of outer variables. Thus the guard restriction and row well-formedness survive. Under a type binder, alpha-rename first; its guard is empty. For absence, `Mod` remains an opaque outer constructor; tag/product cases retain their labels and lookup path. No absence rule exists for a free type variable.

Now induct simultaneously on certificate, value, and expression typing. A certificate's only case is:

```text
d=(A,B,box () in k),        Δ;Unit ⊢s k:A→B
IH: Δ′;Unit ⊢s σk:σA→σB
σd=(σA,σB,box () in σk)     ⇒ Δ′⊢cert σd:σA⇒σB.
```

Type substitution changes annotations, guards, and witnesses, not term constructors; therefore `σk` remains ordinary core code. This case does **not** rerun matching.

| Source typing case | Substituted premises |
| --- | --- |
| `module[I⇒O]{b}` | Body IH under `Rec(σI)`, result `Rec(σO)` |
| `capture[C] e₀ module[I⇒O]{b}` / module value | Capture IH at `Rec(σC)`; `σC#σI`; body IH under `Rec(σC⊎σI)` |
| `resid(m;e;J,K,O)` / residual value | Saved module IH at `Mod[σJ⊎σK⇒σO]`; supplied-import IH at `Rec(σJ)`; `σJ#σK` |
| Decorated `view`, `run`, `link`, `provide` | Operand IHs and the substituted certificate; substituted disjointness where required |
| `invoke`, `complete`, `let` | Operand/body IHs at the displayed substituted types |
| Ordinary/type closures | Substitute their captures and stored-body derivations |
| Type application, package, unpack | Use `σ(A[U/a])≡(σA)[σU/a]`; retain freshness after alpha-renaming |
| Fold/unfold | Use `σ(A[μa.A/a])≡(σA)[μa.σA/a]` |
| Remaining common rules | Reapply the rule to the component IHs; lookup uses the absence/uniqueness result above |

Unpacking's fresh witness remains absent from the substituted result and caller-ambient types. Static weakening uses the same induction with fresh declarations and retained assumptions. □

### U.2. Generated adapters are certificates

```text
Δ ⊢s A ≤ B ↦ c
  ⇒ c=box () in k,
     k is ordinary core source code,
     Δ;Unit ⊢s k:A→B,
     Δ⊢cert (A,B,c):A⇒B.

Δ⊢cert d:A⇒B, Δ⊢H:Type ⇒ Δ;H ⊢s cˢ_d:A→B.
```

**Proof.** Induct on canonical **source** matching, retaining source constructor heads.

| Matching case | Body derivation under the generated binders |
| --- | --- |
| Equality | `x:A`; conversion yields `x:B` |
| Arrow `A₁→A₂ ≤ B₁→B₂` | IH gives `d:B₁→A₁`, `u:A₂→B₂`; hence `u(f(d x)):B₂` for `f:A₁→A₂`, `x:B₁` |
| Record, same opaque tail | Project each advertised field, apply its IH adapter, and merge the resulting finite map with the unchanged `drop_dom(F) r:Rec ρ` |
| Record, closed target | Build only the advertised finite map using the field IHs |
| Aligned universal | Under its fresh binder, body IH types `c(f[a]):B`; captured `f` has a closed-under-`a` universal type, so universal introduction applies |

Lambda introduction discharges the displayed binders, and the outer unit box closes the value environment. Every template uses only core constructs. A module type has no structural matching case: equal module types use the equality row. These are all source matching rules. The certificate rule gives the first conclusion. For the second, type the box using `H⊢s ():Unit` and the certificate's stored `Unit` derivation. □

### U.3. Source values and canonical module forms

For every well-formed ambient type `H`:

```text
Δ;H ⊢s v:A  ⇔  Δ⊢s v:A.
```

The common-core canonical forms hold with source types and source values. In particular, a closed value at `Rec R` is a finite map with exactly `dom(R)` and the declared field types. The additional case is:

```text
∅⊢s m:Mod[I⇒O]
  ⇒ either
     m=mod(c;C,I,O;b),
     ∅⊢s c:Rec C, C#I, ∅;Rec(C⊎I)⊢s b:Rec O;
  or m=resid(m₀;j;J,I,O),
     ∅⊢s m₀:Mod[J⊎I⇒O], ∅⊢s j:Rec J, J#I.
```

Annotations are compared modulo source type/row equality.

**Proof.** Mutual induction on value typing and expression typing of values. Common data use the value IHs; ordinary/type closures use their stored capture/body rules. A module value's premises refer to its explicit capture and body environment, never the caller's `H`. A residual value's premises type its two saved values. If its expression derivation used the in-progress residual rule, apply the value IH to its now-value import expression and rebuild the residual value rule. Conversely, value inclusion places any value derivation under a well-formed `H`.

For canonical forms, invert the resulting value derivation and strip conversion. Source equality preserves outer constructors, so only the two displayed value rules can yield `Mod`. A module value cannot appear at a source arrow type. At a record type, its value rule gives the exact finite map; closed rows have no remaining opaque variables. The remaining core type heads select the same constructors as in target Lemma S.3. □

### U.4. Source lookup and strict contexts

For closed typed source values, record projection, disjoint merge, finite restriction/removal, and fresh renaming are defined, unique, and preserve their displayed types. Legacy lookup satisfies:

```text
∅⊢s v:A, uniqueℓ(A)=B ⇒ findℓ(v) is defined uniquely and has type B.
```

Every source value is irreducible. Evaluation selects at most one strict operand, then at most one head contraction. Replacing a strict operand by another expression of its type preserves typing; its ambient remains the caller's `H`, except for a box body, which uses the box's saved environment type.

**Proof.** Exact-map inversion from U.3 gives record domains and field types. Closed disjointness is finite-set disjointness; map union, restriction, removal, and renaming retain the corresponding field typings. Induct simultaneously on `absentℓ` and `uniqueℓ`: tag cases inspect only the outer label; product cases inspect the designated component and prove absence in its sibling; all other constructors are opaque. In particular, neither a module's captures/body nor a residual's saved values are searched.

For evaluation, induct on expression syntax. The new strict operand lists are:

```text
let: bound expression          view: operand
capture: capture expression    run: module, provider
link/provide: provider, module  complete: module
invoke: module, imports        resid: saved-import expression.
```

A module literal has its creation contraction; a module value has none. A residual with a value import is already a value. Its saved module is a value slot, not an additional evaluation position. `invoke`'s two head rules have disjoint `mod`/`resid` constructors. No rule enters a suspended body, a stored certificate, or a capture slot. Common-core forms have the target's ordered strict positions and head rules; malformed raw closures with nonvalue captures are untypable and inert.

Finally invert and reapply the enclosing typing rule for each selected position. None of the new strict positions changes ambient type. In the box-right case, U.3 types the saved ambient independently of its caller. This proves context replacement and rules out any overlap between strict and head steps. □

### U.5. Canonical source adaptation of values

Let `D:Δ⊢s A≤B↦c`, let `θ⊨Δ`, and let `∅⊢s v:θA`. There is a unique value `N_D^θ(v):θB`, independent of the caller ambient, such that for every typed source ambient `ν`:

```text
ν ⊢s (θc) v ⇓ N_D^θ(v).
```

If the target type is `Rec R`, this value has exactly `dom(θR)`. If `D` is equality, `N_D^θ(v)=v`.

**Proof.** Induct on `D`. The outer unit box and lambda create a closure capturing unit; its application to `v` activates the body under `pair((),v)`.

| Matching case | Finite resulting construction |
| --- | --- |
| Equality | Project and return `v` |
| Arrow | Return a closure capturing `pair((),v)` with the domain/result adapter code in its delayed body |
| Universal | Return a type closure capturing `pair((),v)` with the body adapter code delayed until instantiation |
| Record | Project the finitely many advertised fields; apply the field IHs; build that finite map; retain the unchanged opaque tail only in the same-tail case |

U.3 guarantees the required projections and exact source domain. U.4 guarantees defined map operations. No case invokes an input function, activates an input type closure, or executes a module merely to construct the result. The construction therefore terminates and does not read the caller's environment. U.2, U.1, and S1.1 give its type; U.3 gives exact shape; S1.3 gives uniqueness. The proof uses the stored substituted code even when `θ` would change a fresh matcher's choice. □

## E. Elaboration and operational correspondence

These lemmas use source U.1–U.4 and target T1.1–T1.3. They do not assume a linking law or source representation independence. Checked aliases have already been expanded; decorated operations carry their stored certificates.

### E.1. Runtime elaboration

Write `e ⇝ E` for elaboration of runtime expressions and `v ~ V` for correspondence of runtime values. This is a **mutual syntactic relation**, with the value clause taking priority. On programmer expressions it is the compiler of source.MD §5. On values it is the componentwise relation in that section, including both permitted representations of an empty-capture module. Closure bodies are related by `⇝`, and captured values by `~`.

Add the closed target constructor

```text
Residual_J,K,O = () ▷
  λm:Rec(J⊎K)→Rec O. λj:Rec J.
    pair(m,j) ▷ λ[Rec K].
      (π₁(π₁ @)) (merge(π₂(π₁ @),π₂ @)).
```

All displayed types are translated source types. Complete runtime elaboration by

```text
v ~ V
───────────────                 value clause first
v ⇝ V

e₁ ⇝ E₁       e₂ ⇝ E₂
────────────────────────────────
invoke(e₁,e₂) ⇝ E₁ E₂

m ~ M       e ⇝ E       e∉Val_s
──────────────────────────────────────────────
resid(m;e;J,K,O) ⇝ (Residual_J,K,O M) E.
```

Thus a completed `resid(m;j)` elaborates directly to its related closure value. The last rule handles only the intermediate saved-import computation. No source body is executed by elaboration.

**Lemma E.1 (Structural properties).**

```text
e ⇝ E              ⇒ (e∈Val_s ⇔ E∈Val)
v ~ V              ⇒ v ⇝ V
ν ~ N, w ~ W        ⇒ pair(ν,w) ~ pair(N,W)
c ~ C, i ~ I, C₀#I₀ ⇒ c⊎i ~ C⊎I
```

The final line assumes the corresponding exact record types. Elaboration is defined on every well-typed runtime expression; related targets need not be unique for runtime values.

**Proof.** Mutual structural induction. Common data preserve their constructors and value children. Common closures retain their constructor, translate annotations, relate captures, and elaborate stored code. The two module-value rules and the residual-value rule yield target closures. Every nonvalue source-only form yields a target box/application; the nonvalue residual rule has an application at its head. All strict common-core constructors use their child induction hypotheses. Map union uses disjointness and fieldwise relatedness. Exhausting these cases proves totality on typed runtime syntax and both directions of valuehood. □

### E.2. Static translation, substitution, and typing

For a source substitution `σ`, let `σ̄(a)=⟦σ(a)⟧`; translate row arguments fieldwise. Translate `Δ` by translating its type annotations and preserving its row guards.

**Lemma E.2 (Static and typed elaboration).**

```text
Δ ⊢s U:κ                ⇒ ⟦Δ⟧ ⊢ ⟦U⟧:κ
Δ ⊢s R#S                ⇒ ⟦Δ⟧ ⊢ ⟦R⟧#⟦S⟧
A≡s B                   ⇒ ⟦A⟧≡⟦B⟧
⟦A[U/a]⟧                ≡ ⟦A⟧[⟦U⟧/a]

e ⇝ E                   ⇒ σe ⇝ σ̄E
v ~ V                   ⇒ σv ~ σ̄V

Δ ⊢s v:A, v~V           ⇒ ⟦Δ⟧ ⊢ V:⟦A⟧
Δ;H ⊢s e:A, e⇝E        ⇒ ⟦Δ⟧;⟦H⟧ ⊢ E:⟦A⟧.
```

Substitution has the U.1 kinding/guard premises. Consequently `θ⊨Δ` implies `θ̄⊨⟦Δ⟧`.

**Proof.** Static assertions: induction on kinding, disjointness, equality, and type syntax. The additional case is

```text
⟦Mod[I⇒O]⟧ = Rec⟦I⟧ → Rec⟦O⟧.
```

This commutes with substitution and preserves well-formedness. Translation does not change row domains or guards. For legacy lookup, source `absentℓ(Mod[I⇒O])` becomes target absence at an arrow; all other absence/unique-lookup cases preserve the same searched path.

Substitution of terms/values: mutual induction on `⇝` and `~`, renaming bound type variables first. Every template substitutes its annotations and stored body. In a certificate, substitute the **stored code** and its endpoints. Neither translation nor substitution reruns matching. The chosen empty-capture representation remains a valid representation. Valuehood depends on expression constructors, so the value-priority side condition is preserved.

Typing: mutual induction on expression/value typing and their elaboration derivations. The common cases reapply the matching target rule to the induction hypotheses, using the static assertions above at type application, unpack, and fold/unfold. The remaining cases are exactly:

| Source form | Target typing obtained from its premises |
| --- | --- |
| `let[A] e₁ in e₂` | `pair(@,E₁):⟦H⟧×⟦A⟧`; box into `E₂:⟦B⟧` |
| Certificate `d:A⇒B` | `C_d=()▷⟦k⟧:⟦A⟧→⟦B⟧` under every ambient |
| `view_d e` | Application of the preceding function to `E:⟦A⟧` |
| Sandboxed module | Under `Unit×Rec⟦I⟧`, `π₂ @:Rec⟦I⟧`; box into the compiled body, then lambda and outer box |
| Captured module | Under `(Unit×Rec⟦C⟧)×Rec⟦I⟧`, the two projections have record types `C,I`; disjoint merge has `Rec⟦C⊎I⟧`; box into the body |
| `mod(c;C,I,O;b)` | The corresponding capture/argument derivation above, using `c~Cᵥ`; V-clo types the stored closure. For the empty-capture alternative use the sandbox derivation |
| `resid(m;j;J,K,O)` | Its capture is `pair(M,Jᵥ)`; under `(⟦Mod[J⊎K⇒O]⟧×Rec⟦J⟧)×Rec⟦K⟧`, project the saved function and merge the supplied/remaining imports |
| Nonvalue `resid(m;e)` | `Residual:⟦Mod[J⊎K⇒O]⟧→Rec⟦J⟧→⟦Mod[K⇒O]⟧`; two applications |
| `invoke(e₁,e₂)` | `E₁:Rec⟦I⟧→Rec⟦O⟧`, `E₂:Rec⟦I⟧`; ordinary application |
| `run`, `complete` | The typed `Run` template, with the stored certificate or the exact empty identity |
| `link` | Adapt `p` to `I`, call `m`, then merge `P` and `O`; the source premise supplies `P#O` |
| `provide` | Adapt `p` to `J`; the preceding residual-closure derivation supplies `Mod[K⇒O]` |

In particular, the closed templates have types

```text
Run_d       : ⟦Mod[I⇒O]⟧ → Rec⟦P⟧ → Rec⟦O⟧
Link_d      : Rec⟦P⟧ → ⟦Mod[I⇒O]⟧ → Rec⟦P⊎O⟧
Provide_d   : Rec⟦P⟧ → ⟦Mod[J⊎K⇒O]⟧ → ⟦Mod[K⇒O]⟧.
```

Their named binders are the specified projection aliases; each displayed projection has the claimed type under the lambda/let frame containing it. Bodies entered through native boxes use their declared source environment, never that compiler frame. This completes every source typing case. □

### E.3. Frozen applications do not depend on the caller

**Lemma E.3 (Caller independence).** Let `u,f` be typed values of suitable types. In either calculus, evaluating an ordinary value application `f u` is independent of the caller's ambient value. In addition:

```text
ν ⊢s cˢ_d u ⇓ w   ⇔   () ⊢s cˢ_d u ⇓ w
N ⊢  C_d U  ⇓ W   ⇔   () ⊢  C_d U  ⇓ W.
```

The same holds for nontermination; when evaluation terminates, its number of steps also agrees. No termination assumption on an arbitrary runtime certificate is made.

**Proof.** A value-function application takes its β step to a box containing only its stored capture, self if recursive, argument, and stored body. That box's body is evaluated under the stored environment; its outer ambient is unused. For a certificate application, `cˢ_d=box () in k` and `C_d=()▷⟦k⟧`. The certificate's function computation always runs under unit. After it returns a closure, use the first assertion. If it or the subsequent call diverges, the identical inner trace occurs under every caller. □

This permits comparison of a generated adapter call inside a compiler frame with the same call under the related unit environments. It does not assert environment independence for an arbitrary expression containing `query`.

### E.4. Finite evaluation decompositions

Write `ν ⊢s e ⇓ v` for the source small-step trace ending in a value. A terminating trace has the following component evaluations, and conversely those finite component evaluations reconstruct a terminating trace. Every listed source operand is evaluated under the original `ν`, except an explicitly displayed body environment.

| Source expression | Source component evaluations; final result |
| --- | --- |
| Runtime value `v` | No steps; `v` |
| `let[A] e₁ in b` | `e₁⇓u`; `b⇓w` under `pair(ν,u)`; result `w` |
| `view_d e` | `e⇓u`; `cˢ_d u⇓w`; result `w` |
| `module[I⇒O]{b}` | No body evaluation; result `mod({};∅,I,O;b)` |
| `capture[C] e₀ module[I⇒O]{b}` | `e₀⇓c`; result `mod(c;C,I,O;b)` |
| `run_d m p` | `m⇓m₀`; `p⇓p₀`; `cˢ_d p₀⇓i`; `invoke(m₀,i)⇓o`; result `o` |
| `link_d p with m` | `p⇓p₀`; `m⇓m₀`; `cˢ_d p₀⇓i`; `invoke(m₀,i)⇓o`; result `p₀⊎o` |
| `provide_d p to m` | `p⇓p₀`; `m⇓m₀`; `cˢ_d p₀⇓j`; result `resid(m₀;j;J,K,O)` |
| `complete[O] m` | `m⇓m₀`; `invoke(m₀,{})⇓o`; result `o` |
| Nonvalue `resid(m;e)` | `e⇓j`; result `resid(m;j;J,K,O)` |
| `invoke(e₁,e₂)` | `e₁⇓m`; `e₂⇓i`; use the module cases below |

The two module-invocation cases are

```text
mod(c;C,I,O;b) on i:       c⊎i ⊢s b ⇓ o;
resid(m;j;J,K,O) on k:     invoke(m,j⊎k) ⇓ o.
```

For `complete`, the fixed empty identity terminates with `{}`. These equations introduce no normalization claim about other certificates or module bodies.

The target template has corresponding component evaluations, with these exact body-entry configurations:

| Related source module / target representation | Target configuration running the compiled body or saved module |
| --- | --- |
| `mod(c;C,I,O;b)` / capture closure | `(Cᵥ⊎Iᵥ, B)`, where `c~Cᵥ`, `i~Iᵥ`, `b⇝B` |
| Empty-capture `mod` / sandbox closure | `(Iᵥ,B)` |
| `resid(m;j;J,K,O)` / residual closure | Ordinary application `M (Jᵥ⊎Kᵥ)`, with the saved `m~M`, `j~Jᵥ` |

For example, the capture representation executes these finite administrative segments:

```text
clo(pair((),Cᵥ), Rec I, merge(π₂(π₁ @),π₂ @)▷B) Iᵥ
  → pair(pair((),Cᵥ),Iᵥ) ▷ (merge(π₂(π₁ @),π₂ @)▷B)
  →* pair(pair((),Cᵥ),Iᵥ) ▷ ((Cᵥ⊎Iᵥ)▷B).
```

The remaining computation is `B` under `Cᵥ⊎Iᵥ`, followed by the two box returns. The sandbox representation similarly projects `Iᵥ` before entering `B`. A residual projects `M,Jᵥ,Kᵥ`, merges the latter two, and invokes the saved `M`; its surrounding activation/return steps are finite.

**Lemma E.4 (Decomposition and budgets).**

1. The source table characterizes terminating source traces.
2. Unfolding a target template yields the corresponding operand, adapter, body and result computations. Every user operand keeps its original ambient value.
3. Each invoked source/target body has strictly fewer evaluation steps than its enclosing invocation. For target `Run`, `Link`, `Provide`, and `Complete`, every extracted user operand, adapter call and module call has strictly fewer steps than the whole template. Capture, lexical let, and nonvalue residual construction likewise spend positive administrative steps outside their extracted operand/body traces. For common data constructors, a child has no more steps and is a smaller source expression.

The whole `C_d V` call in a translated `view_d v`, or the whole `M I` call in `invoke(m,i)`, may equal the enclosing target computation. These two cases instead extract function/argument/body computations; a residual invocation extracts its strictly shorter saved-module subcall.

**Proof.** Invert the first nonvalue strict position, then the head contraction. Source `let`, view, module creation, run, link, provision and invocation use exactly their listed rules; `resid` becomes a value when its saved-import expression does. Repeating this inversion constructs the table's finite evaluation tree. Conversely, concatenate its component traces in the specified strict contexts. A precise induction for the inversion is lexicographic on `(trace length, expression size)`: source-only contractions consume a step, and a zero-overhead data child is a proper subexpression.

For the target, expand the closed lambdas and derived lets. Their construction, projections, β steps, finite record operations and box returns are fixed finite segments. The initial curried application evaluates its first user operand before creating the second lambda; the outer application then evaluates its second user operand under the original ambient. Only generated projection expressions run inside the helper frame. The displayed module cases verify the body environments. Every invocation has a β step and final box return outside its body's trace; a residual adds its own wrapper activation outside the saved invocation. These positive costs prove the strict inequalities in (3).

There is one deliberate order difference: `view_d e` evaluates `e` before the certificate function; target `C_d E` evaluates that closed function before `E`. A terminating run on either side contains **both** computations. E.3 makes the certificate computation independent of the operand and caller, so the two finite traces can be reconstructed in their respective orders. Nothing assumes that an arbitrary certificate terminates. □

### E.5. Bidirectional finite correspondence

**Lemma E.5 (Finite correspondence).** Suppose

```text
∅;H ⊢s e:A       e⇝E       ∅⊢s ν:H       ν~N.
```

Then:

```text
(F) ν ⊢s e ⇓ v  ⇒  ∃V. N ⊢ E ⇓ V ∧ v~V.
(B) N ⊢ E ⇓ V   ⇒  ∃v. ν ⊢s e ⇓ v ∧ v~V.
```

The target result in (B) is arbitrary; it is not assumed in advance to be an image of a source value. Conversely, (F) asserts existence of the target result, not that every representation permitted by `~` is the literal output.

An extracted target adapter or saved-module application may run inside a compiler frame. Before applying an IH, E.3 transfers that **closed adapter call or saved value-function application** to unit or to the target ambient corresponding to its source ambient; afterward it transfers the resulting trace back to the compiler frame. The step count is unchanged. This applies to the saved calls in `Run`, `Link`, and residual invocation; it does not change the environment of a user operand containing `query`.

**Proof of (F).** Strong induction on

```text
(Ns, |e|),       where Ns is the source evaluation's step count.
```

Generalize over related ambient values and every elaboration of the expression. E.4 supplies the finite component evaluations.

- **Value / query / closure creation.** Value-priority gives the displayed target value. Query returns `N`, related to `ν`. A function, recursive function, or type abstraction stores `N` and its elaborated body, exactly the closure-correspondence clause.
- **Common strict data.** Apply the IH to children in their specified order; reconstruct the same data constructor/map. Projection, record operations and tagged lookup select corresponding components. Equal base operands select the same primitive result or conditional branch.
- **Ordinary/recursive application.** The IH supplies related function and argument values. Closure correspondence supplies related captures and stored bodies. Pair the captures with related arguments (and related self closures for recursion); the body IH applies under exactly those environments. The target β/box steps return its related result.
- **Box / case / unpack / type application.** The IH supplies the selected environment, injection, package, or type closure. Box uses related replacements; case pairs the matching payloads with the original environments. For unpack/type application, E.2 relates the substituted bodies and translated witnesses. The freshness/non-escape premises keep the required result type. Reconstruct the matching activation and box steps.
- **Fold/unfold.** Related payloads yield related folds; unfolding selects those same payloads, with E.2 supplying the unfolded type.
- **Let.** Pair `ν~N` with the related bound results, then apply the body IH; both direct let and its target macro enter that pair.
- **View.** The operand IH gives `u~U`. The source adapter application is independent of its caller by E.3, so apply the IH under unit, choosing the value elaboration `u⇝U`. It gives `C_d U⇓W`. Decompose that application into evaluation of `C_d` and its resulting value-function call; insert the already obtained finite evaluation of `E` between them. This constructs `C_d E⇓W` despite the different prefix order.
- **Module creation / capture.** Sandbox creates its permitted empty-capture representation. Capture uses the operand IH and creates the capture representation. Neither body is evaluated.
- **Run / link / provide.** Operand IHs supply related provider and module values. Apply the adapter-call IH under unit using E.3. For run/link, the invocation IH gives related exports; link additionally forms corresponding disjoint unions. Provide creates precisely the related residual closure. E.4 reconstructs the target template in its actual order.
- **Complete / nonvalue residual.** Complete uses the exact empty identity and the invocation IH. A nonvalue residual uses its saved-import IH; `Residual` then constructs the specified related value.
- **Invoke a module.** First apply the operand IHs. For a captured `mod`, union correspondence gives `c⊎i ~ Cᵥ⊎Iᵥ`, so the body IH applies to E.4's first configuration. For its sandbox representation, use `{}⊎i=i`. For a residual, the source invocation of its saved module has strictly fewer source steps; use the IH with the merged related imports and reconstruct the finite wrapper segments.

Every recursive call either has fewer source steps (an activation, adapter call, or source-only contraction has positive surrounding cost), or has the same count and smaller source syntax (a common data child or the saved-import child of nonvalue `resid`). E.3 preserves exact source step counts when moving a closed adapter application to unit, so that changed ambient does not affect the induction measure. These cases cover every source evaluation rule, including arbitrary well-typed runtime certificates. □

**Proof of (B).** Strong induction on

```text
(N, |e|),       where N is the target evaluation's step count.
```

Generalize over source types, ambient values, elaboration derivations and target results. Expression size includes stored certificate code. A source value uses E.1 and zero-step value irreducibility; choose `v=e`. Otherwise invert the target decomposition from E.4.

1. **Common data and eliminators.** Child evaluations have smaller `N`, or equal `N` and smaller source syntax for a constructor with no head step. Apply the IH in evaluation order. It returns source children with related target values. For projection/find/records, correspondence fixes the selected path, label domain and field payload; reconstruct the source rule. For primitives and conditionals, base values agree.
2. **Common function/type activation, case, unpack, and box.** Operand IHs first establish that every target value has a related source value. Invert that correspondence to recover its source capture and body. Source canonical forms U.3 exclude a module value at a source ordinary-arrow type. The target body has fewer steps than the enclosing activation; E.2 supplies its type-substituted elaboration where needed. Apply the body IH under the related environments, then reconstruct the source activation. No source body need be a subexpression of `e`: the strictly smaller target count justifies this call even for recursion.
3. **View.** Invert the target application into `C_d⇓F`, `E₀⇓U`, and the value-function activation of `F U`. Each function/operand/body component has fewer steps than the whole application. Use E.3 to run the certificate under unit and apply the IH to `cˢ_d`; apply the operand IH to `e₀`. The resulting source function corresponds to `F`. Its stored-body IH (as in case 2) yields the source result of calling it on the recovered `u`. Evaluate the source operand first and that closed certificate second, as required by the source rule. **Do not** recursively invoke the theorem on the whole `cˢ_d u`: when `e₀` was already a value, that target trace could have the same `N`.
4. **Module creation / capture / residual construction.** E.4 forces exactly the displayed target closure. In capture/residual cases the extracted operand trace has fewer steps; its IH supplies the source capture/import value. Construct the source module/residual and use the corresponding clause of `~`.
5. **Run / link / provide / complete.** Extract operand evaluations, then the adapter call and (when executed) the module call. All have smaller target counts by E.4. Apply the operand IHs; use E.3 to transfer the adapter call to unit and apply the IH to `cˢ_d p₀`; apply the IH to `invoke(m₀,i)` for the saved-module call. For complete the empty adapter is fixed. Reassemble the source rule and the same record union or residual result.
6. **Invoke.** Operand IHs give `m~M` and `i~I`. Invert their module correspondence. A capture/sandbox closure's target body runs under exactly the environment in E.4; it has fewer steps, so its body IH gives the source result. A residual wrapper reaches the target subcall `M₀(Jᵥ⊎I)` with strictly fewer steps; apply the IH to `invoke(m₀,j⊎i)`. Rebuild the source residual-invocation and merge steps.
7. **Let / query / abstraction.** Let uses its bound-expression and body IHs under the paired environments. Query and each closure-creation form have their uniquely corresponding result, as in (F).

U.1–U.4 and source preservation supply each source subconfiguration's typing; E.2 supplies the target typings. The listed count or syntax decrease justifies every IH use. This proves (B), including the possibility that target results were not known beforehand to correspond to source syntax. □

Typed context compilation is proved separately in L.1. Its program-context equation is exact; runtime contexts are handled modulo target contextual equivalence at the value-priority boundary for `resid`. No restriction on well-typed source observation contexts is needed.

## L. Compilation contexts and linking laws

In this section, target lemmas are prefixed by **target**. Source theorem S1 supplies typed elaboration and bidirectional evaluation correspondence. Write `e ⇝ E` for the runtime elaboration relation and `v ~ V` for its value part; a fixed runtime value may have more than one permitted target representation. All displayed source expressions carry their checked certificates.

### Lemma L.1 — Compilation of contexts and reflection of observations

A typed source context has a typed target context of the translated hole judgment, up to administrative contextual equivalence. For any permitted expression representations `eᵢ⇝Eᵢ`, there are actual elaborations `Fᵢ` and one typed target context `Cₜ` such that:

```text
Cₛ[eᵢ] ⇝ Fᵢ       Fᵢ ≈ Cₜ[Eᵢ]       (i=1,2).
```

Source value holes use corresponding target values `vᵢ~Vᵢ` and value-hole typing. Consequently:

```text
e₁ ⇝ E₁, e₂ ⇝ E₂, E₁ ≈ E₂ at ⟦Δ⟧;⟦H⟧, type ⟦A⟧
─────────────────────────────────────────────────────────
e₁ ≈s e₂ at Δ;H, type A.
```

**Proof.** First establish the sole administrative discrepancy caused by value-priority elaboration. Write `W(M,Jv)` for the residual closure displayed in L.2. For typed target values `M,Jv`, the fixed residual constructor terminates under every ambient at that wrapper:

```text
(Residual M) Jv ⇓ W(M,Jv),       (Residual M) Jv ≈ W(M,Jv).
```

The first assertion follows by beta reduction of its two closed lambdas, the capture box, and creation of the final lambda. It never invokes `M`. For the second, fix any relational valuation and index `n`. Target R.4 relates the two instances of the typed value `W(M,Jv)` at `Vₙ`. On one side the constructor has a finite prefix to that value; on the other side the value takes zero steps. Downward closure verifies both clauses of `Eₙ`; target R.5b gives contextual equivalence.

Now use mutual induction on expression-context and value-context typing.

| Source context constructor | Target context and justification |
| --- | --- |
| Common core, ordinary/recursive/type closures | Same constructor, translated annotations, and recursively compiled capture/code positions |
| `let` | Fixed pair/box template; the body hole keeps its extended ambient type |
| `view`, `run`, `link`, `provide`, `complete` | Insert the operand context into the corresponding argument of the fixed closed combinator |
| `module`, `capture` | Insert the body context after the native box, under exactly the declared import/capture row; compile the capture operand separately |
| Runtime `mod` | Choose its captured representation uniformly; the capture is a value context and the stored body is an expression context after the box |
| Runtime `invoke` | Ordinary application of the two compiled operands |
| Runtime `resid` in an expression position | Use `(Residual M) Cₜ[−]`. If filling the hole makes the source residual a value, its actual compilation is `W`; apply the displayed normalization equivalence |
| Runtime `resid` required to be a value | Its saved-import context must remain a value context; compile directly to the corresponding `W` value context |
| Type binder | Alpha-rename, then use commutation with capture-avoiding substitution; aliases were expanded before this induction |
| Hole in stored certificate code | Retain its common-core grammar and `Δ;Unit` typing premise; translate homomorphically inside the fixed `C_d` position |

For a programmer context, compilation is exact. The runtime residual case explains why exact compilation of arbitrary runtime contexts would be false: a saved-import expression can become a value after filling its hole. The normalization equation repairs precisely that case. Target contextual equivalence is closed under well-typed context composition and transitive, directly from its observation definition; these properties lift and combine the induction hypotheses. No transitivity of the indexed value relation is assumed.

Interfaces and certificate endpoints are fixed by the context's typing. Ordinary matching does not inspect its replacement expressions, and stored code is never rematched after erasure or substitution. A hole in certificate code must obey the existing core-code restriction; no new observer restriction is introduced. Source expression holes retain their declared local ambient type and cannot fill a slot requiring a value. If a hole itself is an empty-capture module value, either permitted target representative can fill the same target value hole.

For observation reflection, fix a closing source context of ground type, a satisfying substitution, and a source ambient value; choose a corresponding target ambient value. The first part gives `F₁≈Cₜ[E₁]≈Cₜ[E₂]≈F₂`. By S1.5–S1.6, the two source instances have exactly their actual elaborations' ground results and divergence. Thus they have the same observation. This quantifies over all typed source contexts, including stored code; it does not assert that every target context is a compiled source context. □

### Lemma L.2 — Administrative decomposition of exact linking

For the first four rows below, let `M:Rec(J⊎K)→Rec O`, `Jv:Rec J`, `Kv:Rec K`, and `Iv:Rec(J⊎K)` be target values, with `J#K`. The final row instead assumes `M:Rec(J⊎K⊎L)→Rec O`, adds `Lv:Rec L`, and requires `J,K,L` pairwise disjoint. Let `id_R` be the source equality certificate translated at row `R`. Define the target residual value:

```text
W(M,Jv) = clo(pair(M,Jv), Rec K,
               (π₁(π₁ @)) (merge(π₂(π₁ @),π₂ @))).
```

The following evaluations have only finite administrative work outside their displayed body computation:

| Target expression/configuration | Its unique possible service computation |
| --- | --- |
| `(Provide_id Jv) M` | None; terminates at `W(M,Jv)` |
| `(Run_id M) Iv` | `act(M,Iv)` |
| `(Run_id ((Provide_id Jv) M)) Kv` | `act(M,Jv⊎Kv)` |
| `(Run_id M) merge(Jv,Kv)` | `act(M,Jv⊎Kv)` |
| Two nested provisions, then execution | `act(M,Jv⊎Kv⊎Lv)` |

Here interfaces on `Run`/`Provide` are their uniquely displayed ones. The notation `act` is target R.1's activated-body configuration, not a zero-cost target application.

**Proof.** Expand each closed combinator and follow its strict positions.

```text
Provide: close the two lambdas; bind Jv and M;
         run the equality adapter on Jv; capture pair(M,Jv);
         return the displayed lambda without entering its body.

Run:     close the two lambdas; bind M and Iv;
         run the equality adapter on Iv; activate M once.

Residual activation:
         project M, Jv, Kv; form the exact union Jv⊎Kv;
         activate M once.
```

An equality adapter returns its argument unchanged. Every projection, lambda creation, equality adaptation, and finite-map union above terminates. Native boxes remove generated frames before the saved service body starts. The remaining boxes only return the body's result; they perform no second invocation or result transformation.

Thus any terminating evaluation decomposes as `p + k + s` steps: finite prefix `p`, exactly one `k`-step evaluation of the listed activated body, and finite return suffix `s`. The reverse concatenation is a valid evaluation. The two-stage row follows by expanding the residual wrapper twice. Row disjointness ensures each union is defined; finite-map associativity/commutativity identifies the final argument independently of staging order. □

### Lemma L.3 — Caller-independent module entry

For closed typed `m:Mod[I⇒O]` and `i:Rec I`, define a source configuration by structural recursion on the module value:

```text
entry(mod(c; C,I,O; b), i) = (c⊎i, b)
entry(resid(m; j; J,K,O), k) = entry(m,j⊎k).
```

Then `entry(m,i)=(r,b)` is well typed with result `Rec O`, and for every typed caller ambient `ν`:

```text
ν ⊢s invoke(m,i) ⇓ w  ⇔  r ⊢s b ⇓ w
ν ⊢s invoke(m,i) ⇑    ⇔  r ⊢s b ⇑.
```

**Proof.** Induction on `m` using the canonical forms for `Mod`.

- **`mod(c;b)`.** Its typing gives `c:Rec C`, `C#I`, and `b:Rec O` under `Rec(C⊎I)`. Invocation steps to `box merge(c,i) in b`; map union terminates at `c⊎i`. Box evaluation is precisely evaluation of `b` under this value, followed by box return. This gives both directions for termination. The same finite prefix/return decomposition gives the divergence equivalence.
- **`resid(m₀;j)`.** Its typing gives `m₀:Mod[J⊎K⇒O]`, `j:Rec J`, `k:Rec K`, and `J#K`. Invocation steps to `invoke(m₀,merge(j,k))`. The union terminates, then the IH for the strict subvalue `m₀` applies.

No row of this definition mentions `ν`; every entry environment consists exactly of saved captures and accumulated exact imports. The recursion decreases the finite residual-value tree, not the service's execution. A service may still diverge. □

## Concrete source and target checks

These instantiate the proved rules; they introduce no additional theorem obligations.

**Query in both link operands.** For the example in source.MD §6:

```text
caller ν = {n=7}
provider ⇓ {x=7}                 capture expression ⇓ {seed=7}
entry environment = {seed=7}⊎{x=7}
module body ⇓ {z=14}             link result = {x=7,z=14}.
```

Source strict evaluation gives this trace directly. E.4 gives the same target body-entry map: both operands run under `ν`, and the generated capture/link frames are removed before the body runs.

**Final provision remains suspended.** Let `m=mod({};∅,I,O;Ω)` where `Ω:Rec O` diverges, and let `i:Rec I` be an exact value. The equality certificate returns `i`:

```text
provide[I;∅] i to m ⇓ resid(m;i;I,∅,O)
complete[O] resid(m;i;I,∅,O) ⇑.
```

E.4 constructs the target residual closure without entering `Ω`; completion invokes the saved module. S1.6 preserves its divergence. A concrete divergent expression at any type `A` is `(rec[Unit,A].(π₂(π₁ query))(π₂ query)) ()`.

**Discarded fields are still initialized.** If `m:Mod[{x:Int}⇒O]` is a value, then `run m {x=1,unused=ΩBool}` diverges even though its canonical adapter drops `unused`. Both evaluators must finish the provider before adapting it. This is the strict-operand case of E.4, not an exception to confinement.

---

## S1. Source safety and elaboration correctness

### S1.1. Source preservation

**Theorem S1.1 (Source preservation).** If `∅⊢s ν:H`, `∅;H⊢s e:A`, and `ν⊢s e→e′`, then `∅;H⊢s e′:A`.

**Meaning.** Each source step preserves the expression's type, including generated adapters and suspended or partially supplied modules.

**Proof.** Induct on the source reduction, generalizing `ν,H,A`. Strip an outer conversion before inversion and restore it afterward.

**Congruence.** Invert the selected strict position. Its operand and ambient meet the IH's premises by U.3/U.4. Apply the IH and rebuild its frame by U.4. For box-right the IH runs under the saved environment, not the caller.

**New head rules.**

| Redex | Typing of its reduct |
| --- | --- |
| `let[A] u in b` | `pair(ν,u):H×A`; the body premise types `box pair(ν,u) in b` |
| `view[A⇒B;d] u` | U.2 gives `cˢ_d:A→B` under `H`; application gives `cˢ_d u:B` |
| `module[I⇒O]{b}` | Empty capture has `Rec ∅`; `∅#I` and `Rec(∅⊎I)≡Rec I` give `mod({};∅,I,O;b):Mod[I⇒O]` |
| `capture[C] c module[I⇒O]{b}` | Capture/body premises are exactly the module-value rule |
| `run[P,I,O;d] m p` | The certificate types `view[Rec P⇒Rec I;d] p:Rec I`; `invoke` then gives `Rec O` |
| `invoke(mod(c;C,I,O;b),i)` | `merge(c,i):Rec(C⊎I)` and the stored-body premise type `box merge(c,i) in b:Rec O` |
| `invoke(resid(m;j;J,K,O),k)` | U.3 gives `m:Mod[J⊎K⇒O]`, `j:Rec J`, `k:Rec K`, `J#K`; hence `invoke(m,merge(j,k)):Rec O` |
| `link[P,I,O;d] p with m` | `run[P,I,O;d] m p:Rec O`; `P#O` gives `merge(p,run m p):Rec(P⊎O)` |
| `provide[P;J;K;O;d] p to m` | The view has `Rec J`; the in-progress residual rule gives `resid(m;view d p;J,K,O):Mod[K⇒O]` |
| `complete[O] m` | The closed equality adapter has certificate `Rec ∅⇒Rec ∅`; the empty record and `run` give `Rec O` |

**Common-core head rules.** Their source typing derivations are as follows; captures, arguments, and stored bodies may themselves contain module values or code.

| Redex family | Reduct derivation |
| --- | --- |
| `query` | Value inclusion of `ν:H` |
| `λ`, `rec`, `Λ` | Corresponding source closure-value rule with captured `ν`; type abstraction retains its freshness premise |
| Ordinary closure application | Captured `c:E`, argument `u:B`, body under `E×B`; pair and box type the reduct |
| Recursive closure application | Self `f:B→C`, capture `c:E`, argument `u:B`; pair twice and box under `(E×(B→C))×B` |
| Type-closure application | U.1 substitutes the checked witness into stored code; freshness leaves the captured ambient type unchanged; box types the result |
| Existential unpack | U.1 substitutes the witness into the body; pair caller and payload; nonescape leaves the result type unchanged |
| Box return | U.3 types the returned value under the caller |
| Product projection / sum case | Value inversion selects a typed component; case pairs caller and payload before boxing its branch |
| Fold/unfold | Value inversion gives the stored unfolded payload type |
| Record operations / tagged lookup | U.4 |
| Conditional / primitive | Equal branch types or the primitive's declared total interpretation |

These exhaust the source reductions. No proof case assumes certificate termination or canonicality after substitution. □

### S1.2. Source progress

**Theorem S1.2 (Source progress).** If `∅⊢s ν:H` and `∅;H⊢s e:A`, then `e∈Val_s` or there exists `e′` such that `ν⊢s e→e′`.

**Meaning.** A well-typed source configuration is a value or can step.

**Proof.** Induct on typing, generalizing over all typed values `ν:H`.

1. A runtime value satisfies the first alternative. A module literal, `query`, ordinary/recursive abstraction, or type abstraction has its creation step.
2. If a strict operand is not a value, apply its IH and lift the step through the selected frame. For box-right, U.3 supplies the saved ambient's typing before applying the IH.
3. Otherwise every strict operand is a value. The new forms conclude as follows:

   ```text
   let, view, capture, run, link, provide, complete: their displayed contraction;
   resid(m;j):                                    already a value;
   invoke(m,i):                                   U.3 selects mod or resid.
   ```

   In `capture`, record canonical forms give a record capture. In `invoke`, the input record and module annotations agree by typing. Every common-core eliminator uses its usual canonical form: functions are ordinary/recursive closures, universals are type closures, sums are injections, packages expose a witness/payload, and recursive data are folds. Records and tagged lookup use U.4; primitive operands have their declared base forms.
4. Conversion uses the premise IH. Aliases and lexical-name notation were expanded before this runtime judgment, so they contribute no missing evaluation case.

Thus no typed nonvalue is stuck. □

### S1.3. Source determinism

**Theorem S1.3 (Source determinism).** If `∅⊢s ν:H`, `∅;H⊢s e:A`, `ν⊢s e→e₁`, and `ν⊢s e→e₂`, then `e₁=e₂`.

**Meaning.** Source evaluation has one next step, including the order of provider evaluation and module execution.

**Proof.** Induct on the first step. U.4 makes both derivations choose the same strict operand or the same head contraction. In an operand case, typing inversion and U.3 provide the IH's typed subconfiguration, including a box's stored ambient; the IH equates the substeps. In a head case, the redex's stored annotations/certificate and value constructors determine the displayed reduct. In particular, checked `capture[C]` supplies `C` directly, `invoke` distinguishes `mod` from `resid`, and `provide` returns a residual without executing its body. Common primitives/maps/lookups are unique by U.4. Rebuilding the common frame gives `e₁=e₂`. □

### S1.4. Elaboration preserves typing

**Theorem S1.4 (Elaboration typing).** If `Δ;H ⊢s e:A ⇝ E`, then `⟦Δ⟧;⟦H⟧ ⊢ E:⟦A⟧`.

**Meaning.** A well-typed source program or runtime expression elaborates to a target expression of its translated type.

**Proof.** E.2. □

### S1.5. Termination and result correspondence

**Theorem S1.5 (Termination and result correspondence).** Suppose `Δ;H ⊢s e:A ⇝ E`, `θ⊨Δ`, `∅⊢s ν:θH`, and `ν~N`. Then:

```text
ν ⊢s θe ⇓ v     ⇒ ∃V. N ⊢ θ̄E ⇓ V ∧ v~V;
N ⊢ θ̄E ⇓ V     ⇒ ∃v. ν ⊢s θe ⇓ v ∧ v~V.
```

**Meaning.** Source and target terminate together and produce corresponding values. At ground types they produce the same constant.

**Proof.** U.1 closes source typing; E.2 gives `θe⇝θ̄E` and target typing. Apply E.5(F,B). For a ground result, its value-correspondence clause is equality of constants. □

### S1.6. Divergence correspondence

**Theorem S1.6 (Divergence correspondence).** Under the hypotheses of S1.5, `ν ⊢s θe ⇑` if and only if `N ⊢ θ̄E ⇑`.

**Meaning.** Elaboration neither introduces nor removes divergence, including divergence in discarded initializers, adapters, or module bodies.

**Proof.** Source S1.1–S1.3 and target T1.1–T1.3 imply for each typed configuration:

```text
e ⇑  ⇔  ¬∃v. e ⇓ v.
```

Preservation and progress supply a next step at every nonvalue prefix, and determinism gives one maximal run. S1.5 equates the two existential termination statements. Negate that equivalence and use the displayed characterization on each side. □

## S2. Behavioral separate compilation

**Theorem S2 (Behavioral separate compilation).** Let `p,m` be independently checked source programs with elaborations `Pᵗ,Mᵗ`. Assume one row of the following table; expression typing is under the same `Δ;H`, and matching/guards are under `Δ`.

| Operation | Component types | Canonical certificate and guards |
| --- | --- | --- |
| `run[d] m p` | `p:Rec P`, `m:Mod[I⇒O]` | `Rec P≤Rec I↦cˢ_d` |
| `link[d] p with m` | `p:Rec P`, `m:Mod[I⇒O]` | `Rec P≤Rec I↦cˢ_d`, `P#O` |
| `provide[d;J;K] p to m` | `p:Rec P`, `m:Mod[J⊎K⇒O]` | `Rec P≤Rec J↦cˢ_d`, `J#K` |

Their compilations compose by these exact equations, modulo bound names and expansion of the fixed templates:

```text
⟦run[d] m p⟧           = (Run_d Mᵗ) Pᵗ
⟦link[d] p with m⟧     = (Link_d Pᵗ) Mᵗ
⟦provide[d;J;K] p to m⟧ = (Provide_d Pᵗ) Mᵗ.
```

For every satisfying closing substitution and corresponding ambient values, each right-hand side has exactly the source operation's terminating observations and divergence. The combinator is determined by the declared source interfaces and their canonical certificate. A sandboxed body checked under `Δ;Rec I` has the same compiled body for every caller ambient type under `Δ`.

**Meaning.** Compile each component against its declared interface, then combine the artifacts without inspecting or recompiling their bodies.

**Proof.** The three equations are the elaboration clauses. Canonical source matching examines only normalized source endpoint types and constraints; its fixed priorities and label order determine `d`. Translation of its stored code determines `C_d`, hence the entire selected combinator. It does not rematch the erased arrow types.

By S1.4 the assembled artifact has the translated result type. Apply S1.5 and S1.6 to each elaboration equation for terminating results and divergence. Each operand remains an argument in its original ambient environment; the curried templates create their private frames only inside their own closures.

For a sandboxed body, the elaboration judgment is always `Δ;Rec I⊢s b:Rec O⇝B`. The body translation recursively reads this fixed judgment and its own annotations/certificates, never the caller's ambient type. Changing that caller therefore leaves `B` unchanged. The native box in `Sandbox` installs precisely the declared imports before entering `B`. □

## S3. Staged linking and commuting interfaces

### S3.1. Staging

**Theorem S3.1 (Staging).** If `Δ⊢s m:Mod[J⊎K⇒O]`, `Δ⊢s j:Rec J`, `Δ⊢s k:Rec K`, and `Δ⊢J#K`, then, at every well-formed ambient `H`:

```text
run (provide[J;K] j to m) k  ≈s  run m (merge(j,k)) : Rec O.
```

All operands displayed as `m,j,k` are values; adaptation at these exact interfaces uses the equality certificate. Taking `Δ=∅` covers every actual value at any closed instance of an abstract row; an unknown row need not have a syntactic inhabitant before instantiation.

**Meaning.** Supplying some already evaluated imports now and the rest later has the same behavior as supplying their union at execution.

**Proof.** Choose target value representatives `M,Jv,Kv` in the static context `⟦Δ⟧`; typed elaboration gives their translated types. Fix any satisfying relational valuation `η` with substitutions `θ₁,θ₂`, any `n`, and related caller environments. Target R.4 gives:

```text
(θ₁M,θ₂M) ∈ Vₙ₊₁(Rec(⟦J⟧⊎⟦K⟧)→Rec⟦O⟧;η)
(θ₁Jv,θ₂Jv) ∈ Vₙ(Rec⟦J⟧;η)
(θ₁Kv,θ₂Kv) ∈ Vₙ(Rec⟦K⟧;η).
```

Set `Ivᵢ=θᵢJv⊎θᵢKv`. Exact-record relatedness gives `(Iv₁,Iv₂)∈Vₙ(Rec(⟦J⟧⊎⟦K⟧);η)`. The arrow clause therefore gives:

```text
(act(θ₁M,Iv₁), act(θ₂M,Iv₂)) ∈ Eₙ(Rec⟦O⟧;η).
```

By L.2, the two source expressions' translations have finite administrative prefixes around these activated-body computations and then return their results. Target A.4, with identity result transformations, relates those translations at `Eₙ`. Type substitution retains the equality certificates and the chosen value-representation clauses. Since `η,n` and the related callers were arbitrary, target R.5b gives contextual equivalence, including higher-order result observations and divergence. L.1 reflects it to every source context. □

### S3.2. Commuting stages

**Theorem S3.2 (Commuting stages).** If `Δ⊢s m:Mod[J⊎K⊎L⇒O]`, `j:Rec J`, `k:Rec K`, `l:Rec L` are source values, and `J,K,L` are pairwise disjoint in `Δ`, then, at every well-formed ambient `H`:

```text
run (provide[K;L] k to (provide[J;K⊎L] j to m)) l
  ≈s run (provide[J;L] j to (provide[K;J⊎L] k to m)) l
  ≈s run m (merge(j,merge(k,l))) : Rec O.
```

**Meaning.** Independent stages commute when they supply disjoint, already evaluated imports with the same shared type witnesses.

**Proof.** Choose target representatives `M,Jv,Kv,Lv` before closing the static context. For each side `i` of an arbitrary relational valuation, L.2 reduces the translation's service computation to activation with the finite map

```text
θᵢJv⊎(θᵢKv⊎θᵢLv) = θᵢKv⊎(θᵢJv⊎θᵢLv)
                    = (θᵢJv⊎θᵢKv)⊎θᵢLv.
```

Target R.4 relates the two instances of each input value; the exact-record clause relates the resulting unions at every index. Repeat S3.1's arrow-clause and administrative-prefix argument for each displayed pair of expressions. Target adequacy and L.1 give the contextual equivalences. Row ACU conversion proves typing of both partitions. No provider expression or field initializer is reordered: only values are permuted. Distinct existential witnesses are not equated. □

## S4. Module confinement and exact export retention

### S4.1. Confinement

**Theorem S4.1 (Module confinement).** If `∅⊢s m:Mod[I⇒O]`, `∅⊢s i:Rec I`, and `∅⊢s νₜ:Hₜ` for `t=1,2`, then:

```text
∀w. (ν₁ ⊢s invoke(m,i) ⇓ w) ⇔ (ν₂ ⊢s invoke(m,i) ⇓ w)
     ν₁ ⊢s invoke(m,i) ⇑     ⇔ ν₂ ⊢s invoke(m,i) ⇑.
```

The same result holds for two already evaluated providers whose retained certificates produce the same exact import value `i`.

**Meaning.** For a fixed module value, execution depends on its declared captures and adapted imports; its caller's environment and unused provider fields do not enter the module's scope.

**Proof.** L.3 rewrites both invocations to the identical configuration `entry(m,i)`. Therefore they have exactly the same terminating values and the same divergence behavior.

For the provider formulation, suppose `pₜ` are values and each `cˢ_dₜ pₜ` terminates at the same `i`. The strict `run` and `view` rules give a finite prefix to `invoke(m,i)` on each side. Apply the first result. This comparison starts after provider evaluation; a divergent discarded initializer still prevents reaching the prefix. Any values reachable through the supplied imports or explicit captures remain available to the body. □

### S4.2. Exact export retention

**Theorem S4.2 (Exact export retention).** Suppose `Δ;H⊢s link[P,I,O;d] p with m:Rec(P⊎O)`, `θ⊨Δ`, `∅⊢s ν:θH`, and `ν⊢s θ(link p with m)⇓w`. Then there are a module value `m₀` and record values `p₀,o` such that:

```text
ν ⊢s θp ⇓ p₀                ν ⊢s θm ⇓ m₀
ν ⊢s run[θd] m₀ p₀ ⇓ o
∅⊢s p₀:Rec(θP)              ∅⊢s o:Rec(θO)
w = p₀⊎o                    dom(w)=dom(θP) ⊎ dom(θO)
w|dom(θP) = p₀.
```

Thus `o` is the evaluated client's export record. The same field-retention property holds for a terminating disjoint extension `merge(p,q)`, with `o` the value of `q`.

**Meaning.** Linking retains every evaluated provider field unchanged and adds exactly the disjoint client exports, including when the provider type contains an unknown row.

**Proof.** Invert the strict evaluation of `link`. It first evaluates `θp` to `p₀`, then `θm` to a module value `m₀`, both under `ν`. Its contraction is:

```text
link[θd] p₀ with m₀  →s  merge(p₀,run[θd] m₀ p₀).
```

Termination therefore supplies the actual client result `o`. Source preservation gives the displayed record types. Exact-record inversion identifies their domains as `dom(θP)` and `dom(θO)`. The link typing premise, preserved by substitution, makes these domains disjoint. The final map-union contraction is exactly `p₀⊎o`; restriction to the first domain returns the original map and its original field values. The provider expression is not reevaluated: its second occurrence is the value `p₀`.

For `merge(p,q)`, the same strict map-union argument evaluates the two operands under the original `ν` and retains both value maps. A closed instance of an abstract row contributes its entire finite map to this argument, so no enumeration or projection from the abstract row is required in source code. □

## S5. Abstract-module replacement

**Theorem S5 (Abstract-module replacement).** Let `pᵢ=pack[Aᵢ,vᵢ]`, with `∅⊢s pᵢ:∃a:Type.T` for `i=1,2` and closed public type `∃a:Type.T`. Choose corresponding target values `vᵢ~Vᵢ`. If there is an admissible target candidate `R` between `⟦A₁⟧` and `⟦A₂⟧` such that:

```text
∀n∈ℕ. (V₁,V₂) ∈ Vₙ(⟦T⟧; a↦R),
```

then `p₁≈s p₂ : ∃a:Type.T`.

**Meaning.** Every well-typed source client observes the same ground result or divergence when one related hidden implementation replaces the other, including clients that unpack, stage, and link modules.

The relation is precisely the target interpretation of the elaborated public interface: `Mod[I⇒O]` uses the function relation at `Rec⟦I⟧→Rec⟦O⟧`. Recursive, polymorphic, row-polymorphic, and module-valued exports are all allowed. The representatives `V₁,V₂` and candidate `R` are fixed before quantifying over `n`.

**Proof.** By typed value elaboration and substitution:

```text
Pᵢ = pack[⟦Aᵢ⟧,Vᵢ] : ∃a:Type.⟦T⟧       pᵢ ~ Pᵢ.
```

The displayed relational premise is exactly target T3's premise. Thus `P₁≈P₂` at their common target existential type. L.1 translates any well-typed source client, up to its proved administrative equivalences, into a single well-typed target context with `P₁` or `P₂` in its hole. Target equivalence gives equal ground observations; S1.5–S1.6 give the corresponding source observations.

Source unpack typing supplies one fresh witness to the entire client scope and prevents it from escaping. Thus the same witness is used in every linked import/export that mentions it. Native query and boxes remain covered by target T3. The argument needs the stated relation on exported implementations, not just equality of their public types. □

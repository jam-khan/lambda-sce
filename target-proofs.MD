# Target proofs

**Goal:** prove target safety, coherent structural adaptation, representation independence, and preservation of the existing λE target.

**Status:** manual proofs of all twelve statements in [target.MD](target.MD), with supporting lemmas below and the main theorems at the end. **All selected target theorems T1–T3 are Lean-checked:** [preservation](LeanSce/Target/Metatheory/Safety.lean), [progress](LeanSce/Target/Metatheory/Safety.lean), [determinism](LeanSce/Target/Metatheory/Basic.lean), [adapter typing](LeanSce/Target/Adapters/Typing.lean), [value termination](LeanSce/Target/Adapters/Termination.lean), [shape/divergence](LeanSce/Target/Adapters/Termination.lean), [contextual coherence](LeanSce/Target/Adapters/Coherence.lean), and [existential representation independence](LeanSce/Target/Abstraction/RepresentationIndependence.lean). Only optional T4 remains unmechanized. Coherence uses a homogeneous logical relation; T3 uses a separate heterogeneous relation with arbitrary admissible witnesses and full context compatibility. See the [mechanization status](LeanSce/MECHANIZATION.md); source proofs are in [source-proofs.MD](source-proofs.MD).

| Read | Contents |
| --- | --- |
| [S: static and operational lemmas](#static-and-operational-lemmas) | Substitution, canonical forms, exact lookup, evaluation contexts |
| [R: logical relations](#r-logical-relations-and-contextual-observation) | Indexed definitions, recursion, compatibility, observation |
| [A: adapters](#a-adapter-lemmas) | Typing, finite construction, higher-order coherence |
| [O: legacy embedding](#legacy-embedding-definitions-needed-by-t4) | Scope, translation, evaluation correspondence |
| [T1](#t1-type-safety-and-determinism), [T2](#t2-correct-and-coherent-structural-adaptation), [T3](#t3-existential-representation-independence), [T4](#t4-legacy-target-preservation) | Main statements, English meanings, and proofs |

**Dependency order:** `S → T1 → R → T3`; `S,T1 → A.1–A.3 → T2.1–T2.4`; `R,A.1–A.4 → A.5 → T2.5`; `S,T1,old safety → O → T4`. Forward references to the final theorem section follow this order; none is circular.

**Notation.** `ν ⊢ e ⇓ᵏ v` means exactly `k` steps to a runtime value; `⇓` omits the count, and `⇑` means an infinite reduction. `θ ⊨ Δ` is a satisfying closing type/row substitution. `≈` observes ground values and divergence in every well-typed closing context. `IH` denotes the induction hypothesis. All configurations and substitutions have the typing premises stated in their judgments.

**Specification repairs.** Function/universal relations test activated bodies, so activation is not counted twice. Runtime closure typing, recursive-relation construction, typed observation holes, and legacy scoping/translation are made explicit. Raw closure syntax also admits malformed captures so legacy translation is total; typing still requires value captures. The main theorem statements and language features are retained.

The step-indexed method follows [Ahmed (2006)](https://people.mpi-sws.org/~dreyer/ats/papers/ahmed06.pdf) and [Dreyer, Ahmed & Birkedal (2011)](https://people.mpi-sws.org/~dreyer/papers/lslr/lmcs.pdf); the definitions and compatibility proof below specialize it to this native-environment calculus.

## Static and operational lemmas

All judgments are modulo `≡`; term equality is modulo bound-type renaming and the finite-map representation of record **values**. No initializer is permuted. A value metavariable includes the assertion that the expression is a runtime value.

### Lemma S.1 — Static weakening and substitution

1. Extending a well-formed static context with fresh declarations preserves kinding, constraint entailment, equality, value typing, and expression typing. The ambient type `H` is unchanged.
2. Write `σ : Δ ⇒ Δ′` when `σ` maps each declaration of `Δ` to a well-kinded type/row in `Δ′` and `Δ′ ⊢ σΦ` for every declared guard. Then:

```text
Δ ⊢ U:κ              ⇒ Δ′ ⊢ σU:κ
Δ ⊢ R # S            ⇒ Δ′ ⊢ σR # σS
Δ ⊢ A ≡ B            ⇒ Δ′ ⊢ σA ≡ σB
Δ ⊢ v:A              ⇒ Δ′ ⊢ σv:σA
Δ ; H ⊢ e:A          ⇒ Δ′ ; σH ⊢ σe:σA.
```

**Proof.** Weakening: induction on the derivation, renaming a bound variable before it could clash with a fresh declaration. The old constraint assumptions remain available. No case changes `H`.

For substitution, first induct on the constraint derivation:

| Last constraint rule | Substituted derivation |
| --- | --- |
| Empty | `∅ # σR` |
| Distinct labels | Labels are unchanged |
| Assumed `ℓ # r` or `r # s` | The corresponding premise of `σ : Δ ⇒ Δ′` |
| Symmetry / union | Reapply the rule to the induction hypotheses |

Induct next on kinding and equality. A union uses the constraint result. Under a fresh binder `b`, extend `σ` by `b↦b`. Every newly declared guard atom still mentions `b`: substituting an earlier row only expands its other operand. Thus the binder restriction is preserved. If `b` itself is eliminated, its instantiated guard is a premise, not a new assumption. Row normalization cannot create duplicate concrete fields because each union's substituted operands remain disjoint. The `μ` case extends substitution by its bound type variable and uses capture avoidance.

Finally use simultaneous induction on value/expression typing. Constructor cases reapply their rule to the induction hypotheses. The cases with additional obligations are:

```text
Λb. e:      b∉FV(H) ⇒ b∉FV(σH), after fresh renaming;
             σ extends under b as above.
e[U]:       σ(A[U/b]) ≡ (σA)[σU/b]; use substituted kind/guard premises.
pack[U,e]:  the same equation and guard premises.
unpack:     b∉FV(B,H) remains true; substitute the extended body derivation.
fold/unfold: σ(A[μb.A/b]) ≡ (σA)[μb.σA/b].
```

For closures, substitute both the stored environment derivation and the stored-body derivation; the result is exactly the same closure rule. The `find` premise is preserved by S.2 below, whose proof depends only on type syntax. This completes the mutual induction. □

### Lemma S.2 — Label absence and unique lookup survive substitution

```text
absentℓ(A)      ⇒ absentℓ(σA)
uniqueℓ(A)=B    ⇒ uniqueℓ(σA)=σB.
```

**Proof.** Induct on the displayed judgments. A known opaque constructor retains its outer constructor under substitution. A tag retains its label; a product uses both induction hypotheses. There is no free-type-variable case for absence. Unique lookup ends at the same tag or descends through the same product component; its sibling remains absent by the first assertion. □

### Lemma S.3 — Values, inversion, and canonical forms

For every well-formed `H`:

```text
Δ ; H ⊢ v:A  ⇔  Δ ⊢ v:A.
```

For a closed typed value, inversion gives:

| Type | Value and inverted premises |
| --- | --- |
| A base type | A constant of that base type |
| `A×B` | `pair(v₁,v₂)`, with `v₁:A`, `v₂:B` |
| `A+B` | `inl[B] v` with `v:A`, or `inr[A] v` with `v:B` |
| `Tag(ℓ,A)` | `tagℓ v` with `v:A` |
| `Rec(R)` | A finite map `m`, `dom(m)=dom(R)`, and `m(ℓ):R(ℓ)` for every label |
| `A→B` | `clo(v₀,A,e)` or `rclo(v₀,A,B,e)`; for some `E`, `v₀:E` and the stored body has type `B` under `E×A` or `(E×(A→B))×A` |
| `∀a:κ[Φ].A` | `tclo(v₀,a:κ[Φ],e)`; for some `E`, `v₀:E`, `a∉FV(E)`, and `a:κ,Φ ; E ⊢ e:A` |
| `∃a:κ[Φ].A` | `pack[U,v]`, with `U:κ`, `Φ[U/a]`, and `v:A[U/a]` |
| `μa.A` | `fold[μa.A] v`, with `v:A[μa.A/a]` |

**Proof.** For ambient independence, induct on the typing of the value, stripping a final conversion. Data constructors use the induction hypotheses on their value children. Each closure rule refers to its stored environment and stored body, not the caller's `H`. Conversely, the value-inclusion rule places `Δ⊢v:A` under any `H`.

For canonical forms, invert that ambient-independent derivation. Only the listed value constructor can have each outer type constructor: `≡` preserves constructor heads. In the record case, literal/value typing introduces exactly its finite label map; conversion only permutes that map and converts field types. A closed row has no opaque variables, so its domain is exactly that map's domain. □

### Lemma S.4 — Typed record and legacy lookup operations

For closed well-typed values, each operation below is defined, unique, and has the displayed type:

```text
m : Rec({ℓ:A}⊎R)                       ⇒ m(ℓ) : A
m : Rec(R), n : Rec(S), ∅ ⊢ R # S      ⇒ m ⊎ n : Rec(R⊎S)
m : Rec(F⊎R), dom(F)=L                 ⇒ m|L : Rec(F), m\L : Rec(R)
m : Rec({ℓ:A}⊎R), {k:A} # R, k≠ℓ      ⇒ renameℓ↦k(m) : Rec({k:A}⊎R)
v : A, uniqueℓ(A)=B                    ⇒ findℓ(v) : B.
```

**Proof.** S.3 gives each record's exact domain and field typing. Closed constraint checking is precisely finite-set disjointness: induction on `#` leaves only empty rows, unequal singleton labels, symmetry, and union. Therefore union has no duplicate key; restriction partitions the domain; and the new name in a renaming is absent. Each retained or renamed field keeps its inverted type.

For legacy lookup, prove simultaneously by induction on `absentℓ(A)` and `uniqueℓ(A)=B`:

```text
v:A ∧ absentℓ(A)    ⇒ no searched tag of v has label ℓ;
v:A ∧ uniqueℓ(A)=B ⇒ exactly one searched tag has label ℓ,
                      and its payload has type B.
```

At a tag, inspect its outer label only. At a pair, use S.3 and the two induction hypotheses. All other known constructors are opaque to the search. Closed values cannot introduce a free-type-variable case. □

### Lemma S.5 — Strict frames and irreducible values

Every runtime value is irreducible. Every nonvalue expression has at most one next strict operand; if none remains, at most one head-contraction form applies.

**Proof.** Structural induction on the expression. The ordered strict-operand lists in target.MD §4 select the first nonvalue. A completed data constructor is already a value. No reduction enters a function/type-closure body. The box alternatives are disjoint:

```text
e₁ nonvalue             : reduce e₁ under ν;
e₁=v, e₂ nonvalue       : reduce e₂ under v;
e₁=v, e₂=w a value      : return w.
```

Every other eliminator first reduces its unique strict operand(s). Its value-headed alternatives have disjoint constructors (`clo`/`rclo`, `inl`/`inr`, `true`/`false`). Primitives are fixed functions; map operations are fixed partial functions; legacy lookup succeeds only at a unique tag. Thus no value has a selected operand or contraction, and no expression has two competing choices. □

A raw closure with a nonvalue capture has neither a selected operand nor a head rule. It is untypable, so it introduces no progress case.

### Lemma S.6 — Typing of strict contexts

An ordinary strict frame has its hole under the caller's `H`; replacing its hole by another expression of the same type preserves its result type. For a box-right frame, the hole is instead checked under the stored environment's type:

```text
Δ⊢v:E, Δ;E⊢e:A  ⇒  Δ;H⊢v▷e:A.
```

**Proof.** Invert and reapply the enclosing typing rule. Ordinary frames are precisely the strict operand positions from §4 excluding box-right: no such position introduces a value or type binder. The box-right equation follows from value inclusion and T-box. Bound case/unpack/lambda bodies are not strict frames. □

## R. Logical relations and contextual observation

These lemmas concern the target kernel alone; none uses adapter coherence. Write `q=(ν,e)` for a typed closed configuration and `q ⇓ᵏ v` for exactly `k` small steps to a value. The two sides of a relation may have different closed types and environments.

### R.1. Indexed interpretation

A **candidate** between closed types `U₁,U₂` is a family `S=(Sₙ)ₙ` satisfying:

```text
Sₙ ⊆ Val(U₁) × Val(U₂)       Sₙ₊₁ ⊆ Sₙ.
```

No reflexivity, symmetry, transitivity, or termination assumption is imposed on a candidate. A valuation `η ⊨ Δ` contains two closing substitutions `θ₁,θ₂ ⊨ Δ` and:

- For each type variable `a`, a candidate between `θ₁a,θ₂a`.
- For each row variable `r`, equal finite label domains on its two sides and, at each label, a candidate between the two field types.

Each side satisfies every declared guard. Interpret a row by disjoint union: known fields use the interpretation of their declared types; opaque fields use their assigned candidates. Repeated opaque summands cause no ambiguity because the guards force their instantiated domains to be disjoint.

All pairs below are required to have the displayed instantiated types. Define activation independently of the caller's ambient environment:

```text
act(clo(c,A,b),w)             = (pair(c,w), b)
act(f,w), f=rclo(c,A,B,b)     = (pair(pair(c,f),w), b)
inst(tclo(c,a:κ[Φ],b),U)     = (c, b[U/a]).
```

Define `Vₙ(A;η)` and `Eₙ(A;η)` as follows. In clauses involving `η[a↦S]`, the candidate includes its two witness types or rows.

| Type `A` | Membership of `(v₁,v₂)` in `Vₙ(A;η)` |
| --- | --- |
| Ground base | `v₁=v₂` |
| `a` | `(v₁,v₂)∈η(a)ₙ` |
| `A×B` | Both are pairs; components belong to `Vₙ(A;η)` and `Vₙ(B;η)` |
| `A+B` | Same injection; payloads belong to its `Vₙ` relation |
| `Tag(ℓ,A)` | Same tag; payloads belong to `Vₙ(A;η)` |
| `Rec(R)` | Both maps have exactly the interpreted row's domain; each field belongs to its interpreted candidate at `n` |
| `A→B` | For every `j<n` and `(w₁,w₂)∈Vⱼ(A;η)`, `(act(v₁,w₁),act(v₂,w₂))∈Eⱼ(B;η)` |
| `∀a:κ[Φ].A` | For every `j<n` and every admissible paired instantiation `S` satisfying `Φ`, `(inst(v₁,U₁),inst(v₂,U₂))∈Eⱼ(A;η[a↦S])` |
| `∃a:κ[Φ].A` | Both are packages `pack[Uᵢ,wᵢ]`; some admissible `S` between their witnesses satisfies `Φ` and `(w₁,w₂)∈Vₙ(A;η[a↦S])` |
| `μa.A` | Both are folds; for every `j<n`, their payloads belong to `Vⱼ(A;η[a↦V(μa.A;η)])` |

```text
(q₁,q₂) ∈ Eₙ(A;η)
  iff ∀k<n.
       (q₁ ⇓ᵏ w₁ ⇒ ∃w₂. q₂ ⇓ w₂ ∧ (w₁,w₂)∈Vₙ₋ₖ(A;η))
   and (q₂ ⇓ᵏ w₂ ⇒ ∃w₁. q₁ ⇓ w₁ ∧ (w₁,w₂)∈Vₙ₋ₖ(A;η)).
```

The arrow and universal clauses test the **activated bodies**, not applications including their activation steps. This repairs the earlier relation sketch: two closures returning different integers would otherwise be related at index `3` because their two-step applications are invisible to `E₂`, although application distinguishes them within the budget of `E₃`. No target rule or representation-independence conclusion is restricted by this correction.

### R.1a. Prefix locality and recursive construction

**Lemma R.1a (Prefix locality).** If valuations `η,η′` have the same two witness substitutions and their candidates agree through index `n`, then:

```text
Vₙ(A;η)=Vₙ(A;η′)       Eₙ(A;η)=Eₙ(A;η′).
```

**Construction and proof.** Construct the interpretations by induction on the index, with structural recursion on types at a fixed index. Establish prefix locality and R.2's downward closure simultaneously. Ground, variable and data clauses are immediate; arrow/universal clauses use only `Eⱼ` with `j<n`. Existential witnesses range over the same candidates on both sides, and the body is a proper type subexpression.

For `μa.A` at index `n`, the lower-index induction has already constructed a downward-closed prefix `V₀(μa.A;η),…,Vₙ₋₁(μa.A;η)`. Extend this prefix by the empty relation at every index `≥n`, obtaining a full admissible candidate `S`. Use `η[a↦S]` in the displayed recursive clause. Lower-index locality makes every test `Vⱼ(A;η[a↦S])`, `j<n`, independent of how the future prefix was extended. The tests for index `n−1` are included among those for `n`, giving downward closure. Thus this construction agrees with the recursive clause using the eventual full family `V(μa.A;η)`, without presupposing that family.

Finally define `Eₙ` from the already constructed `Vₘ`, `m≤n`; its clause preserves prefix locality and downward closure. Impredicative witnesses remain candidates; their syntax is never expanded at the same index. □

### R.2. Downward closure and semantic substitution

**Lemma R.2.** For `m≤n`, `Vₙ(A;η)⊆Vₘ(A;η)` and `Eₙ(A;η)⊆Eₘ(A;η)`. If `Δ⊢U:κ`, then:

```text
Vₙ(A[U/a];η) = Vₙ(A;η[a↦⟦U⟧η])
Eₙ(A[U/a];η) = Eₙ(A;η[a↦⟦U⟧η]).
```

Here `⟦U⟧η` has witnesses `θ₁U,θ₂U`; a type is interpreted by its `V` family, and a row by its interpreted field map. The judgment assumes the substituted guard is satisfied.

**Proof.** Simultaneous induction on the index and type structure.

```text
variable:      candidate downward closure; substitution selects ⟦U⟧η.
base/data:     componentwise IH; row unions use disjoint label domains.
arrow/∀:       {j | j<m} ⊆ {j | j<n}; apply IH to the tested types.
∃:            retain the same witness candidate; apply IH to payloads.
μ:            unfold the defining clause only at j<n; apply lower-index IH.
E:            k<m ⇒ k<n and Vₙ₋ₖ ⊆ Vₘ₋ₖ.
```

For substitution, alpha-rename bound variables first. The variable case is the defining equation for `⟦U⟧η`; every constructor then has identical component clauses on the two sides. A binder extends `η` by the same arbitrary candidate on both sides. In the `μ` substitution case, the lower-index IH equates the recursive candidates through each tested index; R.1a then permits replacing one candidate by the other. Guard preservation and row-disjointness preservation ensure both interpreted rows are defined. This also proves independence from variables absent from the type. □

### R.3. Residual budgets

**Lemma R.3 (Sequential composition).** Suppose `(q₁,q₂)∈Eₙ(A;η)` and, for every `m≤n` and `(v₁,v₂)∈Vₘ(A;η)`, their continuations are in `Eₘ(B;η)`. Then evaluating `qᵢ` and continuing with its value gives configurations related by `Eₙ(B;η)`.

**Proof.** Consider either terminating side, with total cost `k<n`. Unique evaluation decomposition gives:

```text
k = k₀+k₁,       qᵢ ⇓ᵏ⁰ vᵢ,       continuationᵢ(vᵢ) ⇓ᵏ¹ wᵢ.
```

The premise supplies the other `v`, related at `m=n−k₀`. Since `k₁<m`, the continuation premise supplies the other `w`, related at `m−k₁=n−k`. Concatenate the other side's two finite evaluations. Repeat with the sides reversed. □

This lemma applies to strict evaluation frames; a frame's final contraction belongs to its continuation. Previously computed values and ambient environments are lowered to the residual index by R.2.

**Lemma R.3a (Administrative steps).**

```text
v₁ Vₙ(A;η) v₂                         ⇒ (ν₁,v₁) Eₙ(A;η) (ν₂,v₂)
qᵢ→qᵢ′ and q₁′ Eₙ₋₁(A;η) q₂′       ⇒ q₁ Eₙ(A;η) q₂       (n>0)
(c₁,b₁) Eₙ(A;η) (c₂,b₂)             ⇒ (ν₁,c₁▷b₁) Eₙ(A;η) (ν₂,c₂▷b₂).
```

**Proof.** First: the only terminating evaluation of a value has cost `0`. Second: subtract the common first step; `(n−1)−(k−1)=n−k`. Third: a terminating box costs `k+1` when its body costs `k`; apply `Eₙ` to the bodies and lower `Vₙ₋ₖ` to `Vₙ₋ₖ₋₁`. At index `0`, computation claims are vacuous. □

### R.4. Fundamental compatibility

Write `Δ;H ⊨ e₁ ∼ e₂:A` when, for every `η⊨Δ`, index `n`, and `(ν₁,ν₂)∈Vₙ(H;η)`, the configurations `(ν₁,θ₁e₁)` and `(ν₂,θ₂e₂)` belong to `Eₙ(A;η)`.

**Lemma R.4 (Fundamental theorem).**

```text
Δ;H ⊢ e:A   ⇒   Δ;H ⊨ e ∼ e:A.
Δ ⊢ v:A     ⇒   ∀η⊨Δ,n. (θ₁v,θ₂v)∈Vₙ(A;η).
```

Moreover, each typing rule preserves these relations when its premises contain paired, potentially different subexpressions or values. Expression holes assume `∼` at their declared local `Δ;H`; value holes assume `Vₙ` for every `η,n` at their value judgment `Δ⊢v:A`. These are distinct kinds of premises.

**Proof.** Mutual induction on the expression/value typing derivations, proving each semantic claim for all indices. For recursive closure construction, use an additional strong induction on the index with the already established semantic body premise. For paired rules, use the assumed semantic premises in place of the typing induction hypotheses. R.3 evaluates strict premises in their specified order. The following are the resulting value and body cases; all indices are the **remaining** budget after preceding operands.

| Rule | Remaining obligation and justification |
| --- | --- |
| Constant / runtime data value | Equality or componentwise value IH gives `Vₙ` directly. |
| Primitive / `if` | Related base operands are equal; the same total primitive result or branch is selected. Use branch IH and R.3a. |
| `@` | Related ambient values become the results after one step; lower `Vₙ(H)` to `Vₙ₋₁(H)`. |
| `pair`, `tag`, injections, records | After sequential operand IHs, lower earlier components to the final residual index and apply the corresponding value clause. |
| Projection, field lookup, `find` | Related input values have related selected components. For `find`, induction on `uniqueℓ(T)` selects the same tag path on both sides; its absence premises survive substitution. Use R.3a for the contraction. |
| `merge`, `take`, `drop`, `rename` | Apply the identical finite map operation on both sides. Their equal label domains and guards make every operation defined; each retained field keeps its candidate. |
| Box | Operand IH returns related replacement environments `c₁,c₂`. Body IH runs under **those** environments. R.3a accounts for box completion. No ambient weakening is used. |
| Ordinary closure / `λ` | At every `j<n`, related captures and arguments give related `H×A` environments. Body IH yields `Eⱼ(B)` of their activations, hence the arrow clause. Creating a closure additionally uses R.3a. |
| Recursive closure / `rec` | Prove the closure-construction claim by strong induction on `n`. At every `j<n`, lower the captures to `j`; the inner IH gives the two self closures in `Vⱼ(A→B)`. Thus `((capture,self),argument)` is related at `j`; the semantic body premise, supplied by the outer typing IH, proves the arrow obligation. |
| Application | After operand IHs obtain `f₁ Vₘ(A→B) f₂` and `w₁ Vₘ(A) w₂`. For `m>0`, the arrow clause at `j=m−1` relates activated bodies; R.3a supplies their boxes and the application step. For `m=0`, the claim is vacuous. |
| `case` | Related scrutinees have the same injection. Pair their related payloads with the original related ambient environments; branch IH and R.3a apply. |
| Type closure / `Λ` | Fix `j<n` and any guard-satisfying candidate `S`. Freshness makes captured-environment interpretation unchanged by `η[a↦S]`. Body IH in that extended valuation proves the universal clause. Closure creation does not evaluate the body. |
| Type application | Choose the candidate `⟦U⟧η`. The universal clause at the smaller budget, R.2 substitution, and R.3a yield the result. |
| `pack` | Choose witness candidate `⟦U⟧η`; the payload IH and R.2 are exactly the existential clause. |
| `unpack` | The package clause supplies some candidate `S` and related payloads at the residual index. Extend `η` by `S`, pair each payload with the original ambient, and use body IH. Freshness and the nonescaping result type remove `a` from the result interpretation; R.3a accounts for unpacking and its box. |
| `fold` | Payload IH at `m`, lowered to every `j<m`, gives the recursive-type value clause, using R.2. |
| `unfold` | At residual `m>0`, the recursive clause supplies payloads at `m−1`; the one unfolding step spends exactly this index. Use R.2 and R.3a. |
| Conversion | Structural equality, alpha-renaming and disjoint row ACU leave the interpretation unchanged, by the clauses of R.1. |
| Typed expression / value hole | Apply its assumed `E` / `V` judgment. An expression hole has its current local ambient type; a value hole has an environment-independent value judgment. |

In the recursive-closure row the self obligation has strictly smaller index; the body premise comes from a smaller typing derivation and is available at every index. All other recursive proof calls use smaller typing derivations. This justifies the mutual induction, including general recursion and negative occurrences in iso-recursive types. The argument uses neither term substitution nor a variable representing the ambient environment. □

### R.5. Contextual adequacy

**Lemma R.5 (Context compatibility).** Replacing typed expression/value holes by the corresponding related pairs in R.4 yields related enclosing expressions/values, including when a hole occurs under a value binder, type binder, unpack, box, or captured closure.

**Proof.** Mutual induction on expression-context and value-context typing derivations, using the corresponding compatibility row of R.4. Under a type binder, alpha-rename to avoid capture and quantify over its arbitrary extended valuation. Under a value binder or box, use the local ambient type in that typing premise. For a runtime closure, its capture premise is a value judgment and its code premise is an expression judgment under the stored capture type extended by the argument/self types. Apply the value IH to captures and the expression IH to code; R.4's closure-construction case concludes. Fixed captured values use the value fundamental theorem. A type closure additionally uses the declared freshness condition.

This does not infer a rule changing `H` by weakening, nor turn an expression-hole premise into a value-hole premise. A nonvalue expression can occur in stored code but cannot be inserted into a capture slot whose grammar requires a value. Multiple occurrences use the same appropriately typed premise at each occurrence. □

**Lemma R.5a (Ground adequacy).** If `q₁ Eₙ(G;∅) q₂` for every `n` and ground `G`, then the two configurations produce the same ground value or both diverge.

**Proof.** If `q₁⇓ᵏ g₁`, take `n=k+1`; `Eₙ` gives `q₂⇓g₂` and `g₁ V₁(G) g₂`, hence `g₁=g₂`. The reverse implication uses the symmetric clause. If neither terminates, progress, preservation and determinism give an infinite reduction on each side. □

**Corollary R.5b (Logical relation implies contextual equivalence).** If `Δ;H⊨e₁∼e₂:A`, then every closing ground observation context with an expression hole declared at `Δ;H⊢[−]:A` observes the same result or divergence; this is `e₁≈A e₂` at `Δ;H`. Closed values related at every index additionally admit value-hole contexts and have this consequence in every ambient environment.

**Proof.** Fix a closing substitution, a well-typed ambient value and any typed ground observation context with the indicated hole judgment. Interpret each instantiated variable diagonally by the `V` relation of its closed type; R.2 identifies this with closed-type interpretation. The ambient value is related to itself by the value part of R.4. Apply R.5 and then R.5a. For closed values, their all-index `V` premise applies directly to value holes and gives the expression-hole premise by R.3a under every pair of related local environments. Thus the value conclusion also covers insertion into runtime closure captures, whereas arbitrary expressions retain their declared local ambient typing. □

## A. Adapter lemmas

These lemmas use S.1 (static substitution), S.3 (value inversion), and the relation lemmas R.*. In particular, `Vₙ` and `Eₙ` are downward closed, interpret type substitution, and satisfy the fundamental/context-adequacy lemmas. No adapter theorem is assumed by R.*.

Write `D : Δ ⊢ A ≼ B ↝ c`. For a closing substitution `θ`, write `N_D^θ(v)` for the value constructed by applying `θc` to `v`. Lemma A.3 establishes that this notation is defined. For a relational assignment `η`, its left/right closing substitutions are `θ₁,θ₂`; write `N_Dⁱ = N_D^{θᵢ}`.

### Lemma A.1. Canonical matching and antisymmetry

**Statement.**

1. Equal endpoint types give the same matching rule tree and generated adapter, up to bound names and equal type annotations.
2. If `Δ ⊢ A ≼ B ↝ c` and `Δ ⊢ B ≼ A ↝ d`, then `A ≡ B`.

**Proof.**

1. Normalize rows and guards. The equality test and the ordered outer-constructor tests then agree. A record test uses the same finite label subset and opaque remainder. Induction on the endpoint syntax gives the same recursive results; the fixed label order gives the same generated term.
2. Induct on `|A|+|B|`. An equality case gives the conclusion. Otherwise both derivations have the same outer constructor:

   - **Arrow.** The premises give both `A₁≼B₁` and `B₁≼A₁`, and both `A₂≼B₂` and `B₂≼A₂`. The induction hypotheses give equality of the domains and codomains.
   - **Record.** Write the rows `F⊎ρ` and `G⊎σ`. The premises give `dom(G)⊆dom(F)⊆dom(G)`. Also `(σ=ρ ∨ σ=∅)` and `(ρ=σ ∨ ρ=∅)`, hence `ρ=σ`. Corresponding fields are equal by the induction hypotheses.
   - **Universal.** Kinds and guards agree. Apply the induction hypothesis to the bodies under the common extended context.
   - **Other constructor.** There is no nonequality matching rule.

Thus `A≡B` in every case. □

Equal annotations in the generated templates are handled by the case analyses below: matching rule trees coincide, while the supplied argument values and opaque payloads remain untouched. No invariance of an arbitrary witness relation under rewriting its member values is assumed.

### Lemma A.2. Typing the templates

**Statement.** If `D : Δ ⊢ A ≼ B ↝ c`, then `Δ ; H ⊢ c:A→B` for every well-formed `H`.

**Proof.** Induct on `D`. Since `H ⊢ unit:Unit`, it suffices in every case to type the generated lambda under `Unit`.

- **Equality.** Under `Unit×A`, the alias `x` denotes `π₂ @:A`. Conversion gives result type `B`.
- **Arrow.** Under `(Unit×(A₁→A₂))×B₁`, the projection aliases give `f:A₁→A₂` and `x:B₁`. The induction hypotheses, instantiated at this ambient type, give

  ```text
  c₁ : B₁→A₁       c₁ x : A₁
  f(c₁ x) : A₂     c₂(f(c₁ x)) : B₂.
  ```

  Two lambda rules and the outer box give `(A₁→A₂)→(B₁→B₂)`.
- **Record.** Under `Unit×Rec(F⊎ρ)`, `r.ℓ:F(ℓ)` for each `ℓ∈dom(G)`. By induction, `cℓ(r.ℓ):G(ℓ)`. Thus the generated finite map has type `Rec(G)`. In the shared-remainder case, `drop_dom(F) r:Rec(ρ)` and `G#ρ`; merge has type `Rec(G⊎ρ)`. In the closed-target case the finite map itself has the required type.
- **Universal.** Under `Δ,a:κ,Φ ; Unit×(∀a:κ[Φ].A)`, the captured `f` has its universal type, `f[a]:A`, and the induction hypothesis gives `c:A→B`. Hence `c(f[a]):B`. The fresh binder `a` does not occur free in `Unit×(∀a:κ[Φ].A)`, so universal introduction applies. Lambda and box conclude.

All premises are exactly those of the generating rule. □

### Lemma A.3. Total, environment-independent value construction

**Statement.** For every `D`, closing `θ`, and `v:θA`, there is a unique `N_D^θ(v):θB` such that, for every well-typed ambient `ν`,

```text
ν ⊢ (θc) v ⇓ N_D^θ(v).
```

The constructed value is independent of `ν` and has these forms:

| Rule of `D` | Constructed value |
| --- | --- |
| Equality | `v` |
| Arrow, premises `d:B₁≼A₁`, `u:A₂≼B₂` | A closure saving `v`, with body `u(v(d x))` |
| Shared remainder | `{ℓ=N_Dℓ^θ(v.ℓ) \| ℓ∈dom(G)} ⊎ (v \ dom(F))` |
| Closed target | `{ℓ=N_Dℓ^θ(v.ℓ) \| ℓ∈dom(G)}` |
| Universal, body premise `d:A≼B` | A type closure saving `v`, with body `d(v[a])` |

The displayed closure bodies use the specified projection aliases; “saving `v`” means the actual captured value `pair(unit,v)`.

**Proof.** Induct on `D`.

- Every adapter first evaluates `unit ▷ λ[...]...` to a closure capturing `unit`, in finitely many steps independent of `ν`. Applying it to `v` enters its body under `pair(unit,v)`.
- **Equality:** projecting the argument and returning from the box gives `v`.
- **Arrow:** evaluating the inner lambda creates the displayed closure. Its body is not evaluated.
- **Universal:** evaluating `Λa...` creates the displayed type closure. Its body is not evaluated.
- **Record:** value inversion gives a finite map with domain `dom(θF) ⊎ dom(θρ)`. Each required projection terminates. Each field adapter terminates by induction. There are finitely many fields, evaluated in the fixed order. Drop removes exactly `dom(F)`; any merge combines disjoint maps. These steps yield the displayed map.

Lemma A.2, substitution, and preservation give the result type. Determinism gives uniqueness. The construction never calls the input function or activates the input type closure. □

**Operational consequence.** On later activation, these wrappers have the following strict evaluation decompositions:

```text
arrow wrapper on x:
    q := N_d(x);  run the saved v on q;  adapt its result by u

universal wrapper at U:
    instantiate the saved v at U;  adapt its result by d[U/a].
```

Projection, closure-creation, application, and box steps contribute finite administrative work. The displayed invocation is the only possibly diverging part. These are decompositions of evaluation, not zero-step equations. They remain valid when substitutions make endpoint types equal: the stored adapter is used, without rerunning matching.

### Lemma A.4. Lifting total value transformations to computations

**Statement.** Fix `n`. Suppose two strict computations `Pᵢ[eᵢ]` each evaluate their input `eᵢ` once, with finite work before it and a total value transformation `pᵢ` afterward. Suppose, for every `m≤n`,

```text
(v₁,v₂) ∈ Vₘ(A;η)  ⇒  (p₁(v₁),p₂(v₂)) ∈ Vₘ(B;η).
```

Then `(e₁,e₂)∈Eₙ(A;η)` implies `(P₁[e₁],P₂[e₂])∈Eₙ(B;η)`. Inputs may be configurations with different related ambient values. More precisely, each terminating pipeline has the strict decomposition

```text
finite prefix ; eᵢ ⇓ᵏ⁰ vᵢ ; finite suffix returning pᵢ(vᵢ),
k_total = k_prefix + k₀ + k_suffix.
```

Both prefixes terminate before entering their designated input configurations, and both suffixes terminate for every typed input value. A prefix may compute the arguments of a designated activated-body configuration; the relation premise then concerns that resulting configuration. It does not concern an unevaluated argument that the prefix might independently run again.

**Proof.** Suppose the left computation terminates in `k<n` steps. Its strict decomposition gives input termination in `k₀≤k<n` steps. The premise for `Eₙ` supplies a terminating right input and results related by `Vₙ₋ₖ₀(A;η)`. Apply the value premise at `m=n−k₀≤n`, obtaining related transformed values at that index, then lower to `n−k`. The right prefix reaches its designated input, whose matching finite run is now known; its total suffix returns the matching transformed value. This is precisely the first clause of `Eₙ`. Interchange left and right for the second clause. No bound on the other side's runtime is required. □

In particular, this lemma permits additional finite administrative steps on either side. It does not identify their step counts or use transitivity of `Vₙ`.

### Lemma A.5. Relational naturality and path coherence

**Statement.** For every admissible `η` satisfying `Δ`, every `n`, and `(v₁,v₂)∈Vₙ(A;η)`:

```text
(N)  D:A≼B
     ⇒ (N_D¹(v₁), N_D²(v₂)) ∈ Vₙ(B;η).

(C)  D₁:A≼B, D₂:B≼C, D₃:A≼C
     ⇒ (N_D₂¹(N_D₁¹(v₁)), N_D₃²(v₂)) ∈ Vₙ(C;η).
```

More precisely, `(N)` permits separate left/right derivations with equal endpoints and the common rule tree of A.1; its notation suppresses this annotation-only difference. The induction below is on that common tree. The same convention applies to `(C)`. This changes annotations in generated wrappers, never in their supplied values.

**Proof.** Prove `(N)` by structural induction on `D`, for all `n,η`. Then prove `(C)` by induction on `|A|+|B|+|C|`, again for all `n,η`. Neither induction recurses into invariant recursive types or into an instantiated witness type.

**Naturality `(N)`.**

- **Equality:** the output pair is the assumed pair `(v₁,v₂)`.
- **Record:** input record relatedness gives related values at every advertised field. Apply the field induction hypothesis at index `n`. In the shared-remainder case copy the already-related opaque fields. In the closed-target case retain precisely the advertised fields. The domains on both sides agree, so the record clause concludes.
- **Arrow:** let `d:B₁≼A₁` and `u:A₂≼B₂`. Fix `j<n` and `(x₁,x₂)∈Vⱼ(B₁;η)`. By induction on `d`,

  ```text
  (N_d¹(x₁),N_d²(x₂)) ∈ Vⱼ(A₁;η).
  ```

  The input function relation makes the activated bodies of `v₁,v₂` on these arguments `Eⱼ(A₂;η)`-related. Apply induction on `u` and Lemma A.4 to their output adaptations. Lemma A.3 identifies the actual wrapper bodies with these computations plus finite argument-construction and administrative steps. Thus the bodies are `Eⱼ(B₂;η)`-related. This is the arrow clause at `n`.
- **Universal:** fix `j<n` and any two guarded, relationally admissible instantiations. Extend `η` with their witness relation. The input universal relation makes the activated bodies `Eⱼ(A;η′)`-related. The body induction hypothesis and Lemma A.4 give `Eⱼ(B;η′)` after adaptation. Semantic substitution identifies these types with the instantiated result types. Lemma A.3 supplies the finite administrative work. This proves the universal clause.

**Path coherence `(C)`.**

- **First leg is equality:** `N_D₁¹(v₁)=v₁`. Lemma A.1 identifies `D₂,D₃`; apply `(N)` to this common rule tree.
- **Second leg is equality:** similarly use `(N)` for `D₁,D₃`.
- **Direct leg is equality:** `A≡C`, so the first two premises give `A≼B≼A`. Antisymmetry gives `A≡B`. Both preceding equality cases apply. There is no unhandled diamond with an identity direct adapter and two proper structural legs.
- Otherwise all three derivations use the same outer constructor:

  **Arrows.** Write `A=A₁→A₂`, `B=B₁→B₂`, `C=C₁→C₂`. Their premises are

  ```text
  d₁:B₁≼A₁    d₂:C₁≼B₁    d₃:C₁≼A₁
  u₁:A₂≼B₂    u₂:B₂≼C₂    u₃:A₂≼C₂.
  ```

  Fix `j<n` and `(x₁,x₂)∈Vⱼ(C₁;η)`. The domain induction hypothesis, in its contravariant order, gives

  ```text
  (N_d₁¹(N_d₂¹(x₁)), N_d₃²(x₂)) ∈ Vⱼ(A₁;η).
  ```

  Apply the relation for `v₁,v₂` to obtain `Eⱼ(A₂;η)` for their activated bodies. For every `m≤j`, the codomain induction hypothesis relates the transformations `N_u₂¹ ∘ N_u₁¹` and `N_u₃²` at `Vₘ(C₂;η)`. Lemma A.4 therefore gives `Eⱼ(C₂;η)` for the final results. The nested left wrapper and the direct right wrapper have exactly these strict decompositions by A.3. Their finite extra steps are covered by A.4. The arrow clause concludes.

  **Universals.** All three kinds and guards agree. Fix `j<n` and an arbitrary related pair of satisfying instantiations, extending `η` to `η′`. The input universal relation relates the activated `v₁,v₂` bodies at `Eⱼ(A₀;η′)`. Apply the body path induction hypothesis at every `m≤j`, then A.4, to obtain `Eⱼ(C₀;η′)` for the two-stage and direct result adaptations. Semantic substitution and A.3 identify these computations with the two wrapper activations. Thus the universal clause holds, without activating any body when the wrapper is constructed.

  **Records.** Write the three rows `F⊎ρ`, `G⊎σ`, `K⊎τ`. Then

  ```text
  dom(K) ⊆ dom(G) ⊆ dom(F).
  ```

  For each `ℓ∈dom(K)`, all three field adapters exist. Input record relatedness and the field path induction hypothesis give

  ```text
  (N_Gℓ≼Kℓ¹(N_Fℓ≼Gℓ¹(v₁.ℓ)),
   N_Fℓ≼Kℓ²(v₂.ℓ)) ∈ Vₙ(K(ℓ);η).
  ```

  It remains to account for the opaque fields:

  | Remainder choices of the two legs | Final remainder |
  | --- | --- |
  | Both preserve their remainder | `τ=σ=ρ`; both paths copy the original remainder |
  | First preserves, second closes | `τ=∅`; both paths discard the remainder |
  | First closes | `σ=∅`, hence `τ=∅`; both paths discard the original remainder |

  When `τ=∅`, the direct adapter's shared-remainder case is also harmless if `ρ=∅`: it adds an empty map. In every row case the final domains and retained payload relations agree. Intermediate fields outside `dom(K)` may be adapted and discarded; A.3 proves that this finite construction terminates and does not invoke their services. The record clause concludes.

There are no further nonequality cases. This proves both statements. □

## Legacy embedding: definitions needed by T4

`old` is `LeanSce/Core`, including its sequential merge, tagged-tree lookup,
closures, sums, general recursive functions, and iso-recursive types. Write
`∅ ⊢old v:A` for `Valueold(v) ∧ HasTypeold(Unit,v,A)`.

**Scope.** `scoped₍d₎(T)` means that every de Bruijn type index is below its
number of enclosing `μ` binders plus `d`. An old expression is well scoped
when every ordinary annotation is `scoped₍0₎`, every `fold[T]` body is
`scoped₍1₎`, and its children, captures, and stored bodies are well scoped.
Thus `(ν,e)` being well scoped is a syntactic condition, not a termination
assumption. At binder depth `d`, translation maps index `i<d` to its corresponding
bound name and index `i≥d` to the reserved free name `ζᵢ₋d`. Generated
binders avoid the reserved `ζ` namespace. Thus translation is total even
on the arbitrary old values quantified over in T4.2; well-scoped
annotations never use the fallback.

Let `mrg` denote old ordered merge, and set

```text
Pₙ(t)     ≜ π₂(π₁ⁿ t)
M(t,u)    ≜ pair(@,t) ▷ pair(π₂ @,u)
ι(A and B) = ι(A)×ι(B)       ι(rcd ℓ A) = Tag(ℓ,ι(A))
ι(top)     = Unit            ι(int)     = Int.
```

The remaining type constructors and bound indices translate structurally.
The nonhomomorphic expression clauses are

```text
E(proj(e,n))       = Pₙ(E(e))
E(mrg(e₁,e₂))      = M(E(e₁),E(e₂))             when not a value
E(rproj(e,ℓ))      = findℓ E(e)
E(flam[A,B].e)     = rec[ι(A),ι(B)].E(e)
E(fold[T] e)       = fold[ι(μT)] E(e)
E(v)              = V(v)                      value case first
E(clos(e₀,A,b))    = clo(E(e₀),ι(A),E(b))       remaining raw closure case
E(fclos(e₀,A,B,b)) = rclo(E(e₀),ι(A),ι(B),E(b)) remaining raw closure case
V(mrg(v₁,v₂))     = pair(V(v₁),V(v₂))
V(clos(v,A,e))    = clo(V(v),ι(A),E(e))
V(fclos(v,A,B,e)) = rclo(V(v),ι(A),ι(B),E(e)).
```

`lrec` becomes `tag`; the remaining data, program, and value clauses are
homomorphic. Macros are expanded before comparing syntax. No reduction
or η equation is included in syntactic equality.

Raw target closure forms allow arbitrary capture expressions; their value
and typing rules still require value captures. The two raw cases above
therefore define `E` even on malformed code stored inside an arbitrary old
value. Typed old executions never encounter those malformed cases.

### O.1. Scope, unfolding, and lookup

For closed old types and well-scoped old syntax:

```text
(1*) scoped₀(S), scoped₍d+1₎(U), |ā|=d, x fresh
       ⇒ scoped₍d₎(substTyp d S U)
       ∧ ι_ā(substTyp d S U) ≡ ι_(ā,x)(U)[ι_∅(S)/x].

(1) ι(substTyp 0 (μT) T) ≡ (ιₐ(T))[μa.ιₐ(T)/a].
(2) ¬Linℓ(A) ⇔ absentℓ(ι(A)).
(3) RLookup(A,ℓ,B) ⇒ uniqueℓ(ι(A)) = ι(B).
(4) Lookup(A,n,B), ∅;H ⊢ t:ι(A) ⇒ ∅;H ⊢ Pₙ(t):ι(B).
```

In (1*), `ā` lists the names of ambient binders nearest first: free index
`j<d` denotes `ā[j]`, and index `d` denotes `x`. Translation under an
internal `μ` pushes a fresh name. Clause (1) is (1*) at `d=0`, `S=μT`.

Moreover, a well-scoped old term typed under a closed ambient type has a
closed result type; stepping a well-scoped old configuration preserves scope.

**Proof.**

- **(1*):** induction on `U`, generalizing `d,ā`. At `var d`, both sides
  insert `ι(S)`; because `S` is closed, interpreting it under `ā` gives
  `ι_∅(S)`. At `var j`, `j<d`, both retain `ā[j]`. The case `j>d` is
  excluded by `scoped₍d+1₎(U)`. Under `μ`, increment `d`, push a fresh
  name onto `ā`, and apply the IH. All other constructors commute with
  substitution and preserve the indicated scope bound. Derive (1) by
  specialization. Thus no missing shift or index decrement is silently
  assumed: the replacement is closed and there are no indices above the
  removed binder.
- **(2):** induction on `A`. At a product, both sides require absence in
  both children; at a tag, both test `ℓ≠k`; all other closed constructors
  are opaque. A bare free variable cannot occur at this position.
- **(3):** induction on `RLookup`. Its tag case is immediate. Each product
  case uses its recursive premise and (2) for the unselected component.
- **(4):** induction on `Lookup`. Zero uses `π₂`. Successor first types
  `π₁ t`, then uses the induction hypothesis.
- **Closed results:** induction on old typing. Merge first establishes a
  closed left type, then checks its right under the closed extended
  ambient. Closures use their closed captured-value type. Fold/unfold
  use (1). All other rules use their closed annotations and IHs.
- **Scope preservation:** induction on a step. Congruences use the IH;
  query copies scoped `ν`; closure creation stores scoped `ν` and code;
  application/case construct scoped merge values and retain a scoped
  body. Projection, find, box elimination, and unfolding select a scoped
  subterm. These exhaust the old reductions. □

### O.2. Injectivity and value lookup

```text
E(e)=E(e′) ⇒ e=e′;             V(v)=V(v′) ⇒ v=v′.
Valueold(e) ⇔ E(e)∈Val.

LookupV(v,n,u) ⇒ Pₙ(V(v)) ⇓ V(u).

∅⊢old v:A, RLookup(A,ℓ,B), RLookupV(v,ℓ,u)
    ⇒ findℓ V(v) ⇓ V(u).
```

The displayed reductions hold under every target ambient value. The first
uses exactly `n+1` steps; the second uses one. Conversely, successful
projection/find on an embedded, appropriately typed old value selects the
embedding of its old lookup result.

**Proof.** Simultaneous structural induction for injectivity of `ι`, `E`,
and `V`, and preservation/reflection of valuehood. Data and closure valuehood
follow componentwise; a nonvalue merge translates to a box containing `@`,
which is not a value. Raw closures have the same value-capture condition
in both calculi. Constructor images are distinct except the following cases.

1. A bare pair in the image of `E` is necessarily a translated old merge
   **value**, so both children are values. Consequently `pair(@,t)` is
   never an `E` image. The outer box of `M(t,u)` therefore cannot be the
   image of an old box, whose left child must be an `E` image.
2. No `E` image has outer constructor `π₁`. Hence the maximal chain of
   `π₁` immediately below the `π₂` of `Pₙ` uniquely determines `n`.
3. Closure constructors recover their annotations, captured values, and
   bodies by the simultaneous IH. Named binders are compared modulo α;
   the free `ζ` names are never renamed. The binder depth and the
   bound/free distinction recover each original type index uniquely.

For positional lookup, induct on `LookupV`: zero selects the second child;
successor selects the first and repeats. For label lookup, induct on the
typed `RLookup`: O.1(2) excludes every match in the opposite branch,
and the matching branch reduces to the tag case. The same structural
cases establish the converse. □

### O.3. Finite evaluation decomposition

Write `ρ ⊢ t ⇓ⁿ w` for a target reduction of exactly `n` steps to a value.
For a terminating evaluation of an embedded old expression, the following
table lists **all** evaluations of immediate components and the exact
administrative cost. Here `ρ=V(ν)` and the `wᵢ` are initially arbitrary
target values. An application uses the stored target body `b` of its
evaluated closure; after the operand IH establishes that closure is an
image, `b=E(bold)`. A case body is translated directly from its source
branch. The table does not assume that intermediate results are images.

| Old expression | Target component evaluations, in order | Total steps |
| --- | --- | --- |
| old value `v` | none; result `V(v)` | `0` |
| query | none; result `ρ` | `1` |
| `lam[A].b` | none; result `clo(ρ,ι(A),E(b))` | `1` |
| `flam[A,B].b` | none; result `rclo(ρ,ι(A),ι(B),E(b))` | `1` |
| nonvalue `mrg(e₁,e₂)` | `E(e₁)` under `ρ`; `E(e₂)` under `pair(ρ,w₁)`; result `pair(w₁,w₂)` | `n₁+n₂+4` |
| `box(e₁,e₂)` | `E(e₁)` under `ρ`; `E(e₂)` under `w₁` | `n₁+n₂+1` |
| `app(e₁,e₂)` returning ordinary closure | function, argument under `ρ`; stored body `b` under `pair(wcapture,warg)` | `nf+na+nb+2` |
| `app(e₁,e₂)` returning recursive closure `f` | function, argument under `ρ`; stored body `b` under `pair(pair(wcapture,f),warg)` | `nf+na+nb+2` |
| `proj(e,n)` | operand under `ρ`; then follow `π₁ⁿ` and `π₂` | `ne+n+1` |
| `rproj(e,ℓ)` | operand under `ρ`; then select its unique tagged payload | `ne+1` |
| `lrec`, `inl`, `inr`, `fold` | child under `ρ`; reconstruct the same translated constructor | `ne` |
| `case e of b₁,b₂` | scrutinee under `ρ`; chosen body under `pair(ρ,wpayload)` | `ne+nb+2` |
| `unfold e` | operand under `ρ`; return its folded payload | `ne+1` |

**Proof.** Read the strict positions and redex rules in both directions.
The sole nonhomomorphic computation is `M`:

```text
ρ ⊢ pair(@,t) ▷ pair(π₂ @,u)
    → pair(ρ,t) ▷ pair(π₂ @,u)
    →ⁿ¹ pair(ρ,w₁) ▷ pair(π₂ @,u)
    →² pair(ρ,w₁) ▷ pair(w₁,u)
    →ⁿ² pair(ρ,w₁) ▷ pair(w₁,w₂)
    → pair(w₁,w₂).
```

The two middle administrative steps are `@` and `π₂`, evaluated under
`pair(ρ,w₁)`. The right operand `u` is unchanged: its query paths already
expect exactly that extended environment. Application and case contribute
one activation step and one final box-elimination step. Projection uses
O.2. Constructor children contribute no extra step. Strict evaluation
and the fact that values cannot step force these same segments in every
terminating run; there is no omitted alternate evaluation order. □

### O.4. Termination correspondence, with arbitrary target results

Under the T4 hypotheses:

```text
(F) ν ⊢old e ⇓ v  ⇒  V(ν) ⊢ E(e) ⇓ V(v).

(B) V(ν) ⊢ E(e) ⇓ w
      ⇒ ∃v. ν ⊢old e ⇓ v ∧ w=V(v).
```

**Proof of (F).** Induction on the old big-step derivation. Its rules are
exactly the component evaluations in O.3, with old merges supplying
extended environments. Apply the IHs in that order and reconstruct the
corresponding target row. For old merge values use `E(v)=V(v)` and zero
steps; for a nonvalue merge use `M`. At ordinary/recursive application,

```text
V(mrg(capture,arg))                  = pair(V(capture),V(arg)),
V(mrg(mrg(capture,self),arg))        = pair(pair(V(capture),V(self)),V(arg)).
```

Thus the body IH has precisely the ambient required by target activation.
Case and box have the same ambient agreement. Lookup uses O.2; constants,
closures, tags, injections, and folds use their corresponding table rows.
These are all old big-step constructors.

**Proof of (B).** Strong induction on the lexicographic measure
`(N, |e|)`, where `N` is the length of the given target evaluation.
Generalize over the old ambient, result type, and target result `w`.

- If `e` is an old value, `E(e)=V(e)` cannot step; choose `v=e`.
- Otherwise invert the matching row of O.3. Apply the IH successively
  to its component evaluations. Each proper source subexpression has
  `Nchild≤N` and smaller syntax size. An invoked closure body need not
  be a subexpression of `e`, but its count satisfies `Nbody<N`, because
  activation and box elimination consume two steps. Thus every IH use
  strictly decreases the declared measure, including zero-step children.
- Each IH supplies an **old** result. Old preservation makes it well typed,
  and O.1 makes it scoped. For application, invert that old closure's
  typing to obtain the body's typing under exactly the captured/argument
  ambient. For case and merge use the corresponding old extended ambient.
  For box use the old left result's type.
- Rebuild the old big-step rule from those old evaluations. Projection/find
  use the converse in O.2. O.3 identifies the final target constructor
  with `V` of this old result.

For the counts-preserving `lrec`/injection/fold rows, syntax size supplies
the strict decrease. General recursion therefore does not invalidate this
induction. □

Here the old big-step relation equals old `→*` ending in a value: in the
forward direction concatenate the strict component traces; in the reverse
direction induct on the trace, using closure of the big-step rules under
one predecessor step. The only changed ambient cases are box and merge,
whose right-premise ambients are exactly those of the small-step rules.
This is also the existing `step_ebig_eq` theorem in
`LeanSce/Core/Semantics/Equivalence.lean`.

---

## T1. Type safety and determinism

The following three subtheorems cover native query, boxes, polymorphism, records, packages, and recursion.

### T1.1. Preservation

**Theorem T1.1 (Preservation).** If `∅ ⊢ ν : H`, `∅ ; H ⊢ e : A`, and `ν ⊢ e → e′`, then `∅ ; H ⊢ e′ : A`.

**Meaning.** If a well-typed expression takes a step under a well-typed environment, the resulting expression has the same type.

**Proof.** Work under the theorem’s closed static context, generalizing over `H`, `ν`, and `A`:

```text
∅⊢ν:H, ∅;H⊢e:A, ν⊢e→e′  ⇒  ∅;H⊢e′:A.
```

Induct on the reduction derivation. Strip a final type conversion before inversion and restore it afterward.

**Congruence.** For an ordinary strict frame, apply the induction hypothesis at its hole type and rebuild by S.6. For box-right, inversion gives `∅;H⊢v:E` and `∅;E⊢b:A`; S.3 gives `∅⊢v:E`. The induction hypothesis under ambient `v` yields `∅;E⊢b′:A`; T-box gives `∅;H⊢v▷b′:A`.

**Environment and closure rules.**

```text
@:       ∅⊢ν:H  ⇒  ∅;H⊢ν:H.                         [value inclusion]
λ:       ∅;H×B⊢b:C, ∅⊢ν:H
         ⇒ ∅⊢clo(ν,B,b):B→C.                       [V-clo]
rec:     ∅;(H×(B→C))×B⊢b:C, ∅⊢ν:H
         ⇒ ∅⊢rclo(ν,B,C,b):B→C.                    [V-rclo]
Λ:       ∅,a:κ,Φ;H⊢b:B, a∉FV(H), ∅⊢ν:H
         ⇒ ∅⊢tclo(ν,a:κ[Φ],b):∀a:κ[Φ].B.           [V-tclo]
```

Value inclusion gives each reduct its required type under `H`.

**Ordinary application.** Invert the application and closure typing:

```text
∅⊢v₀:E     ∅⊢w:B     ∅;E×B⊢b:C
──────────────────────────────────────────────
∅;H⊢pair(v₀,w)▷b:C.                                [pair, box]
```

**Recursive application.** With `f=rclo(v₀,B,C,b)`, inversion gives `v₀:E`, `f:B→C`, `w:B`, and `b:C` under `(E×(B→C))×B`. Thus `pair(pair(v₀,f),w)` has that environment type; T-box types the reduct.

**Type application.** Inversion gives

```text
∅⊢v₀:E     ∅,a:κ,Φ;E⊢b:B     a∉FV(E)
∅⊢U:κ      ∅⊢Φ[U/a].
```

By S.1, `∅;E⊢b[U/a]:B[U/a]`; T-box types `v₀▷b[U/a]` under `H`.

**Existential elimination.** Inversion gives `ν:H`, `w:B[U/a]`, `U:κ`, `Φ[U/a]`, and `∅,a:κ,Φ;H×B⊢b:A` with `a∉FV(H,A)`. S.1 yields `∅;H×B[U/a]⊢b[U/a]:A`. Pair and box typing give the reduct `pair(ν,w)▷b[U/a]:A`.

**Remaining contractions.**

| Redex | Type of the reduct, by inversion |
| --- | --- |
| `v▷w` | S.3 removes the body's ambient type, then includes `w:A` under `H` |
| `πᵢ pair(v₁,v₂)` | S.3 gives the selected component's type |
| `case (inl w) of b₁\|b₂` | `pair(ν,w):H×B₁`; T-box with the left branch |
| `case (inr w) of b₁\|b₂` | `pair(ν,w):H×B₂`; T-box with the right branch |
| `unfold (fold[μa.B] w)` | `w:B[μa.B/a]` |
| record projection/merge/take/drop/rename | S.4 |
| `findℓ v` | S.4 |
| `if true then b₁ else b₂` / `if false …` | The chosen branch has the declared common type |
| `op(v₁,…,vₖ)` | Typed base arguments, and the fixed primitive table's result type |

These are all head rules; each preserves the stated type. □

### T1.2. Progress

**Theorem T1.2 (Progress).** If `∅ ⊢ ν : H` and `∅ ; H ⊢ e : A`, then `e ∈ Val` or there exists an expression `e′` such that `ν ⊢ e → e′`.

**Meaning.** A well-typed expression under a well-typed environment is either a value or can take a step.

**Proof.** Induct on the typing derivation under `∅;H`, generalizing over every value `ν` with `∅⊢ν:H`. Conversion uses the induction hypothesis for its premise.

1. A runtime value is the first alternative. `@`, `λ`, `rec`, and `Λ` take their closure/query step.
2. In every strict constructor/eliminator, apply the induction hypothesis to its first nonvalue strict operand. For box-right, use S.3 to obtain the newly selected ambient value's type before applying the induction hypothesis under that value.
3. If all strict operands are values, data constructors are values. For eliminators, S.3 and S.4 select the following contraction:

| Typed form | Available head rule |
| --- | --- |
| application at an arrow | ordinary or recursive β |
| type application at a universal | type-closure activation; kind/guard premises already hold |
| box with a value body | box return |
| product projection | selected pair component |
| sum case | the matching injection branch |
| unpack | the package witness/payload rule |
| unfold | fold cancellation |
| record/legacy eliminator | S.4's defined operation |
| conditional / primitive | typed base canonical forms and the fixed total interpretation |

There is no other typing rule. Therefore a closed well-typed nonvalue always steps. □

### T1.3. Determinism

**Theorem T1.3 (Determinism).** If `∅ ⊢ ν : H`, `∅ ; H ⊢ e : A`, `ν ⊢ e → e₁`, and `ν ⊢ e → e₂`, then `e₁ = e₂`.

**Meaning.** If a well-typed expression can take two steps under the same well-typed environment, both steps produce the same expression.

**Proof.** Induct on one of the two reductions. By S.5 both derivations select the same operand or the same head rule. For an operand, typing inversion and S.3 supply its typing and the selected ambient value’s typing. Both reductions use that same ambient, including the stored value in box-right; the induction hypothesis equates the sub-reducts. For a head rule, the rule's displayed reduct is unique. Primitive functions, map operations, and unique legacy lookup each have one result. Rebuilding the same frame yields `e₁=e₂`. □

Together, these guarantee deterministic evaluation without stuck states. Divergence remains allowed.

## T2. Correct and coherent structural adaptation

`θ ⊨ Δ` means that `θ` is a closing type/row substitution satisfying the declarations and guards in `Δ`.

### T2.1. Adapter typing

**Theorem T2.1 (Adapter typing).** If `Δ ⊢ A ≼ B ↝ c` and `Δ ⊢ H : Type`, then `Δ ; H ⊢ c : A → B`.

**Meaning.** An adapter generated from `A` to `B` has type `A→B` under every well-formed ambient type.

**Proof.** Lemma A.2. □

### T2.2. Termination on values

**Theorem T2.2 (Termination on values).** If `Δ ⊢ A ≼ B ↝ c`, `Δ ⊢ H : Type`, `θ ⊨ Δ`, `∅ ⊢ ν : θH`, and `∅ ⊢ v : θA`, then there exists a value `w` such that `ν ⊢ (θc) v ⇓ w` and `∅ ⊢ w : θB`.

**Meaning.** Applying a generated adapter to an already evaluated `A` value terminates at a `B` value. This concerns constructing the adapted value; later calls to an adapted function may still diverge.

**Proof.** Take `w=N_D^θ(v)` from Lemma A.3. □

### T2.3. Exact record shape

**Theorem T2.3 (Exact record shape).** If `Δ ⊢ A ≼ Rec(R) ↝ c`, `Δ ⊢ H : Type`, `θ ⊨ Δ`, `∅ ⊢ ν : θH`, `∅ ⊢ v : θA`, and `ν ⊢ (θc) v ⇓ w`, then `w` is a record value and `dom(w) = dom(θR)`.

**Meaning.** An adapter targeting a record type produces exactly the fields specified by that row, with no hidden extra fields.

**Proof.** T2.1 and substitution type the initial application at `Rec(θR)`. Iterated preservation gives `∅⊢w:Rec(θR)`. Exact-record value inversion (S.3) gives both conclusions. □

### T2.4. Divergence preservation and reflection

**Theorem T2.4 (Divergence preservation and reflection).** If `Δ ⊢ A ≼ B ↝ c`, `Δ ; H ⊢ e : A`, `θ ⊨ Δ`, and `∅ ⊢ ν : θH`, then `ν ⊢ θ(c e) ⇑` if and only if `ν ⊢ θe ⇑`.

**Meaning.** Adapting an expression diverges exactly when evaluating the input expression diverges.

**Proof.**

- **`⇐`.** Lemma A.3's initial closure construction for `θc` terminates. The application then evaluates its argument `θe`. Its infinite reduction lifts through the argument evaluation frame.
- **`⇒`.** Suppose `θe` does not diverge. By safety and determinism its reduction terminates at a value `v:θA`. Lemma A.3 then gives a finite adaptation to `N_D^θ(v)`. Thus `θ(c e)` terminates, contrary to the premise.

Both uses of the argument refer to its single strict evaluation position. □

The specified call-by-value application `c e` evaluates the input `e` once before adapting its resulting value.

### T2.5. Composition coherence

**Theorem T2.5 (Composition coherence).** If `Δ ⊢ A ≼ B ↝ c₁`, `Δ ⊢ B ≼ C ↝ c₂`, `Δ ⊢ A ≼ C ↝ c₃`, and `Δ ; H ⊢ e : A`, then `c₂(c₁ e) ≈C c₃ e` in context `Δ ; H`.

**Meaning.** If all three canonical adapters exist, adapting from `A` through `B` to `C` is contextually equivalent to adapting directly from `A` to `C`.

**Proof.** Fix any satisfying relational assignment `η`, index `n`, and `Vₙ(H;η)`-related ambient values. The fundamental lemma relates the two instances of `e` at `Eₙ(A;η)`. Lemma A.5(C), for every `m≤n`, relates the two total value transformations

```text
N_D₂¹ ∘ N_D₁¹     and     N_D₃².
```

Lemma A.4 therefore relates `θ₁(c₂(c₁ e))` and `θ₂(c₃ e)` at `Eₙ(C;η)`. Both evaluate the input once; all other work before or after it is the total construction of A.3. Since `η,n` and the related ambients were arbitrary, contextual adequacy gives the displayed contextual equivalence. This includes divergence and every permitted observation context. □

Here `≈` quantifies over closing substitutions and well-typed observation contexts, including termination and divergence.

## T3. Existential representation independence

**Theorem T3 (Existential representation independence).** Let `pᵢ = pack[Aᵢ,vᵢ]` for `i = 1,2`. If `∅ ⊢ pᵢ : ∃a:Type.T` for both packages, the public type `∃a:Type.T` is closed, and there exists an admissible representation relation `R` between `A₁` and `A₂` such that `(v₁,v₂) ∈ Vₙ(T; a↦R)` for every `n ∈ ℕ`, then `p₁ ≈ p₂` at type `∃a:Type.T`.

**Meaning.** Every well-typed client observes the same ground result or divergence from the two related implementations, even when it uses native query and boxes.

**Proof.** Fix `n`. Use the stated candidate `R` as the existential witness relation:

```text
R admissible       (v₁,v₂)∈Vₙ(T;a↦R)
───────────────────────────────────────  V-Exists
(p₁,p₂)∈Vₙ(∃a:Type.T;∅).
```

The premise holds for every `n`; therefore R.5b gives `p₁≈p₂`. In particular, R.4's `@` case preserves the relation on a reified environment, and its box case changes to related replacement environments. Thus neither operation exposes an abstract representation through a new observation rule. □

`Vₙ` and admissibility are specified in [target.MD §7](target.MD#7-observation-and-relation-conventions). Matching public types alone is insufficient; the exported implementations must satisfy the relational premise.

## T4. Legacy target preservation

This group concerns translating the existing λE target into the new calculus. Option A is already a fragment of Option B by construction and has no separate compatibility theorem.

The subscript `old` identifies the existing calculus. `ι` translates old types, `E` translates old programs, and `V` translates old runtime values. The value translation `V` is distinct from the indexed relation `Vₙ` in T3.

The legacy embedding is defined in [target.MD §8](target.MD#t4-legacy-target-preservation); it gives priority to `E(v)=V(v)` on runtime values.

### T4.1. Legacy type preservation

**Theorem T4.1 (Legacy type preservation).** If `(ν,e)` is well scoped, `∅ ⊢_old ν : H`, and `H ⊢_old e : A`, then `∅ ⊢ V(ν) : ι(H)` and `∅ ; ι(H) ⊢ E(e) : ι(A)`.

**Meaning.** Translating an old program and its environment preserves their types.

**Proof.** Simultaneous induction on old typing for expressions and values.
O.1 gives well-formed translated types. The distinctive cases are:

```text
Merge, nonvalue:
  ι(H) ⊢ E(e₁):ι(A)                 IH
  ι(H)×ι(A) ⊢ E(e₂):ι(B)            IH
  ι(H) ⊢ pair(@,E(e₁)):ι(H)×ι(A)
  ι(H)×ι(A) ⊢ pair(π₂ @,E(e₂)):ι(A)×ι(B)
  ───────────────────────────────────────────────────── box
  ι(H) ⊢ M(E(e₁),E(e₂)):ι(A)×ι(B).

Merge, value:
  ⊢ V(v₁):ι(A)       ⊢ V(v₂):ι(B)   value IHs
  ───────────────────────────────────────────────────── pair
  ⊢ pair(V(v₁),V(v₂)):ι(A)×ι(B).
```

The value IH discards the old ambient because value typing is independent
of it: induction on a value derivation, with the merge case applying the
two value IHs. In the old rules this is `value_weaken`.

| Old typing rule | Target derivation |
| --- | --- |
| query, literal, unit | native query or matching constant rule |
| ordinary/recursive abstraction | IH under `ι(H)×ι(A)` / `(ι(H)×(ι(A)→ι(B)))×ι(A)`, then abstraction |
| ordinary/recursive captured closure | captured-value IH, body IH, then corresponding value-closure rule |
| application, box | IHs, then the identical target rule |
| positional projection | expression IH, then O.1(4) |
| tagged record, tagged lookup | tag rule / expression IH and O.1(3) |
| injections, case | IHs under the same ambient or translated payload-extended ambients |
| fold, unfold | IH and the unfolding identity O.1(1) |

This table exhausts `HasTypeold`. Apply the value result to `ν`, then the
expression result to `e`. □

### T4.2. Legacy termination and result correspondence

**Theorem T4.2 (Legacy termination and result correspondence).** If `(ν,e)` is well scoped, `∅ ⊢_old ν : H`, and `H ⊢_old e : A`, then, for every old value `v`, `ν ⊢_old e ⇓ v` if and only if `V(ν) ⊢ E(e) ⇓ V(v)`.

**Meaning.** Old and translated programs produce corresponding terminating results. The translation may take extra administrative steps.

**Proof.** Forward: O.4(F). Reverse: O.4(B) produces an old result `u`
with `V(u)=V(v)`. O.2 gives `u=v`. This last injectivity step is necessary
because the theorem fixes the exact old result. □

### T4.3. Legacy divergence correspondence

**Theorem T4.3 (Legacy divergence correspondence).** If `(ν,e)` is well scoped, `∅ ⊢_old ν : H`, and `H ⊢_old e : A`, then `ν ⊢_old e ⇑` if and only if `V(ν) ⊢ E(e) ⇑`.

**Meaning.** Translating an old program neither introduces nor removes divergence.

**Proof.** For a well-typed configuration in either calculus,

```text
e ⇑  ⇔  ¬∃v. e ⇓ v.                                  (†)
```

Indeed, a value has no step; preservation and progress provide a next
step at every nonterminal prefix; determinism makes those prefixes a
single run. It either ends at a value or continues infinitely. For the
new calculus use T1.1–T1.3 and T4.1. For the old calculus these are
`gpreservation`, `gprogress`, and `core_step_deterministic` in
`LeanSce/Core`; their typed-lookup premise excludes ambiguous tag selection.
O.4(F,B) gives equivalence of the two existential termination statements;
negate that equivalence and apply (†). The backward clause excludes a
terminating target value outside the image of `V`; administrative steps
cannot add divergence. □


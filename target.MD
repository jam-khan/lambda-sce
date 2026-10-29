# Target calculus: native environments, polymorphism, and structural adapters

**Status:** concrete Option B specification, with manual proofs in [target-proofs.MD](target-proofs.MD). **All selected target theorems T1–T3 are Lean-checked:** full safety, adapter correctness/coherence, and existential representation independence. Only the optional legacy embedding T4 remains unmechanized. See the [mechanization status](LeanSce/MECHANIZATION.md). This document fixes the rules that [source.MD](source.MD) targets. [Theory.MD](Theory.MD) explains the motivation. Inference is a later frontend feature.

The kernel has native environment reification and replacement, explicit polymorphism, exact records, packages, and recursion. Subtyping generates ordinary kernel terms. There is no module construct, implicit subsumption, runtime type inspection, or extra variable representing the source environment.

## 1. Types, rows, and equality

```text
κ       ::= Type | Row
A,B,H   ::= Unit | Int | Bool | String | a
          | A × B | A + B | A → B | Tag(ℓ,A) | Rec(R)
          | ∀a:κ[Φ].A | ∃a:κ[Φ].A | μa.A
R,S     ::= ∅ | r | {ℓ:A} | R ⊎ S
U       ::= A | R                         argument of the appropriate kind
Φ       ::= finite sets of row-disjointness obligations
```

`Δ` declares kinded variables and assumptions `Φ`. Type variables have kind `Type`; row variables have kind `Row`. A row has unique labels. Its normal form is `F ⊎ ρ`: a finite labeled type map `F` and a multiset `ρ` of opaque row variables. All summands must be pairwise disjoint. The empty multiset denotes a closed row. Fields may contain any well-formed type, including polymorphic functions and existential packages.

Omitted guards mean `∅`. In informal type examples, `{ℓ:A,…}` abbreviates `Rec({ℓ:A,…})`; braces inside a row expression denote the row itself.

**Concrete constraint checking.** Write `Δ ⊢ R # S`. Empty rows are disjoint from every row; two singleton rows are disjoint exactly when their labels differ; disjointness is symmetric and distributes over either union. The remaining atomic obligations are `ℓ # r` and `r # s`, discharged only by assumptions in `Δ`. An assumption with compound rows is expanded into these obligations when introduced; a known same-label contradiction rejects the guard. Do not add semantic implication or guess row substitutions. This finite structural procedure is the entire constraint checker for the annotated calculus. Assumptions such as `r # r` are permitted but can only be instantiated by rows that satisfy that constraint, such as `∅`.

Well-formed `R ⊎ S` requires well-formed operands and `R # S`. All usual type constructors require well-formed constituents. For `∀a:κ[Φ].A` and `∃a:κ[Φ].A`, check the guard and body under `Δ,a:κ,Φ`, with the following guard restriction:

- A `Type` binder has an empty guard.
- Every atomic obligation introduced by a `Row` binder must mention that fresh row variable: `ℓ # a`, `a # r`, or `a # a`, up to symmetry. Earlier facts are already in `Δ` and need not be reintroduced. Compound notation is allowed only when its normalized obligations meet this condition.

Contexts are formed by successive binders with these guards. This restriction matters: a later binder cannot newly assume `r # s` between two earlier rows, because substituting equal rows for those earlier parameters would produce a contradictory latent guard and an ill-formed duplicate-label body. The allowed guards remain well formed under outer substitution; the guarded variable's own application checks its obligations before substituting it.

`μa.A` binds a type variable and is **iso-recursive**; no positivity restriction is needed for the intended safety claim. We already permit divergence.

Type equality `≡` is structural equality modulo binder renaming, row union associativity/commutativity/unit, normalized guard order, and recursively equal field types. It does not unfold `μ`, identify representations of abstract types, or identify an ordered product with a record. A conversion rule using `≡` is available. Transparent aliases are expanded before these rules; no type-level functions or path-dependent type projections occur in the kernel.

## 2. Programs and binding conventions

```text
e ::= constant | op(e₁,…,eₙ) | if e then e₁ else e₂
    | @ | pair(e₁,e₂) | π₁ e | π₂ e | e₁ ▷ e₂
    | λ[A].e | rec[A,B].e | e₁ e₂
    | inl[B] e | inr[A] e | case e of e₁ | e₂
    | tagℓ e | findℓ e
    | {ℓ₁=e₁,…,ℓₙ=eₙ} | e.ℓ | merge(e₁,e₂)
    | take_L e | drop_L e | rename[ℓ↦k] e
    | Λa:κ[Φ].e | e[U]
    | pack[U,e] as ∃a:κ[Φ].A | unpack e as a in e₂
    | fold[μa.A] e | unfold e
```

`L` is an explicit finite set of labels, never an abstract row. Record literals have distinct labels and an ordered initializer list. Their types and resulting value maps ignore field order; evaluation does not reorder initializers.

There are no term variables in this kernel presentation. A function body runs under `H × A`: its argument is `π₂ @`, and its captured environment is `π₁ @`. A recursive body runs under `(H × (A→B)) × A`; the argument is `π₂ @` and self is `π₂(π₁ @)`. Case and unpack bodies add one payload to the current environment.

For readable generated terms we use named binders, such as `λx:A.e`. These are static aliases for the corresponding projection paths, adjusted when entering a binder. They are not additional kernel variables. `@` itself always denotes the entire current environment.

Two useful **defined forms**, with their scope behavior fixed, are:

```text
let e₁ in e₂  ≜ pair(@,e₁) ▷ e₂
e₁ & e₂      ≜ let e₁ in pair(π₂ @,e₂)
```

Thus `pair(e₁,e₂)` evaluates both operands under the original `H`; ordered `e₁ & e₂` evaluates its right operand under `H × A`, where `A` is the left operand's type. `&` preserves old λE sequential-environment behavior. `Tag`/`find` preserve old labeled trees; public `Rec`/`merge` provide separate exact interfaces.

Constants are unit, integers, booleans, and strings. The fixed primitive table is `add:Int×Int→Int`, `eqInt:Int×Int→Bool`, `show:Int→String`, and `concat:String×String→String`, interpreted by their total mathematical functions. Products in this table list separate arguments: for example, `add(e₁,e₂)` is binary. There is no generic equality, pointer equality, field enumeration, typecase, or closure inspection.

## 3. Typing

The judgment is `Δ ; H ⊢ e : A`, with `H` and `A` well formed in `Δ`. `H` can be any value type, including a scalar. All premises below use the displayed `Δ`, except where an extended context is shown.

### Environments, functions, and ordinary data

```text
                         H ⊢ e₁ : H′    H′ ⊢ e₂ : A
H ⊢ @ : H                ───────────────────────────
                         H ⊢ e₁ ▷ e₂ : A

H ⊢ e₁ : A    H ⊢ e₂ : B       H ⊢ e : A₁ × A₂
─────────────────────────       ─────────────────
H ⊢ pair(e₁,e₂) : A × B         H ⊢ πᵢ e : Aᵢ

H × A ⊢ e : B                   H ⊢ f : A→B    H ⊢ x : A
─────────────────               ─────────────────────────
H ⊢ λ[A].e : A→B                H ⊢ f x : B

(H × (A→B)) × A ⊢ e : B
──────────────────────────
H ⊢ rec[A,B].e : A→B
```

Constants have their declared types; `op` checks arguments against its table entry. An `if` has a `Bool` condition and equally typed branches under the original `H`. Injections have `A+B`; case checks its branches under `H×A` and `H×B` with the same result type. `fold[μa.A]` maps `A[μa.A/a]` to `μa.A`; `unfold` reverses this typing.

`tagℓ e : Tag(ℓ,A)` when `e:A`. Define `absentℓ(T)` structurally: it holds for base types and the opaque runtime constructors `→`, `+`, `Rec`, `∀`, `∃`, and `μ`; for `Tag(k,A)` exactly when `k≠ℓ`; and for a product when it holds for both components. There is **no absence rule for a free type variable**. Tag payloads are not searched.

The ordered-tree judgment `uniqueℓ(T)=A` succeeds at `Tag(ℓ,A)`, or in one product component when the other satisfies `absentℓ`. Then `findℓ e:A` when `e:T` and `uniqueℓ(T)=A`. Ordered trees may contain duplicate labels; ambiguous lookup is rejected, while positional projection remains available. In particular, `findℓ` at `Tag(ℓ,Int)×a` is rejected: instantiating `a` could introduce another `ℓ`. Exact public-record lookup instead uses row disjointness.

### Exact records

All record operands and initializers are checked under the same `H`.

| Expression | Premises | Result |
| --- | --- | --- |
| `{ℓᵢ=eᵢ}` | Each `eᵢ:Aᵢ`; labels distinct | `Rec({ℓᵢ:Aᵢ})` |
| `e.ℓ` | `e:Rec({ℓ:A}⊎R)` | `A` |
| `merge(e₁,e₂)` | `e₁:Rec(R)`, `e₂:Rec(S)`, `R # S` | `Rec(R⊎S)` |
| `take_L e` | `e:Rec(F⊎R)`, `F` finite, `dom(F)=L` | `Rec(F)` |
| `drop_L e` | Same premises | `Rec(R)` |
| `rename[ℓ↦k] e` | `e:Rec({ℓ:A}⊎R)`, `k≠ℓ`, `{k:A} # R` | `Rec({k:A}⊎R)` |

Restriction physically removes fields. None of these rules selects labels from an unknown row. In particular, `Rec(r⊎s)→Rec(r)` is not automatically implementable by restriction when both `r` and `s` are abstract.

### Explicit polymorphism and packages

```text
Δ,a:κ,Φ ; H ⊢ e : A               a fresh for Δ,H
─────────────────────────────────────────────────
Δ ; H ⊢ Λa:κ[Φ].e : ∀a:κ[Φ].A

Δ ; H ⊢ e : ∀a:κ[Φ].A     Δ ⊢ U:κ     Δ ⊢ Φ[U/a]
──────────────────────────────────────────────────
Δ ; H ⊢ e[U] : A[U/a]

Δ ⊢ U:κ     Δ ⊢ Φ[U/a]     Δ ; H ⊢ e : A[U/a]
────────────────────────────────────────────────
Δ ; H ⊢ pack[U,e] as ∃a:κ[Φ].A : ∃a:κ[Φ].A

Δ ; H ⊢ p : ∃a:κ[Φ].A      Δ,a:κ,Φ ; H×A ⊢ e : B
a fresh for Δ,H             Δ ⊢ B:Type
──────────────────────────────────────────────────
Δ ; H ⊢ unpack p as a in e : B
```

Type arguments may themselves be polymorphic: this is explicit impredicative polymorphism. Row arguments must have kind `Row` and satisfy the guard. Unpacking introduces one scoped abstract witness and one value binding. A result mentioning that witness must be repackaged; it cannot escape as a free type variable.

## 4. Runtime and evaluation

Runtime values extend constants with pairs, tagged values, record maps, injections, folds, packages `pack[U,v]`, and:

```text
clo(v,A,e)             captured ordinary function
rclo(v,A,B,e)          captured recursive function
tclo(v,a:κ[Φ],e)       captured polymorphic computation
```

Raw runtime expressions are the program constructors with runtime expressions in their expression positions, together with `clo(e₀,A,b)`, `rclo(e₀,A,B,b)`, and `tclo(e₀,a:κ[Φ],b)`. These captured forms are values only when `e₀` is a value, as displayed above. Their typing rules require a value capture, and evaluation never enters a capture slot; malformed forms with nonvalue captures are untypable. Allowing them as raw syntax makes the legacy translation total even on arbitrary malformed stored code.

A record literal whose children are all values is identified with the corresponding finite-map value. Pairs, tags, injections, folds, and packages with value children are likewise values. This runtime grammar includes the intermediate states used by preservation; source programmers cannot write captured closure forms.

Type annotations on injections, packages, and folds are retained in the specification evaluator. Equations below occasionally omit an unchanged annotation for readability; no runtime inspection of it is available to programs.

`λ`, `rec`, and `Λ` are expressions that create closures, not runtime values themselves. Define value typing `Δ ⊢ v:A` independently of the caller's environment. Data values use their constructor rules, with value-typing premises for their children; value typing also admits conversion by `≡`. The closure and value-inclusion rules are:

```text
Δ ⊢ v₀:E       Δ ; E×A ⊢ b:B
──────────────────────────────────── V-clo
Δ ⊢ clo(v₀,A,b):A→B

Δ ⊢ v₀:E       Δ ; (E×(A→B))×A ⊢ b:B
────────────────────────────────────── V-rclo
Δ ⊢ rclo(v₀,A,B,b):A→B

Δ ⊢ v₀:E       Δ,a:κ,Φ ; E ⊢ b:A       a fresh for Δ,E
───────────────────────────────────────────────────── V-tclo
Δ ⊢ tclo(v₀,a:κ[Φ],b):∀a:κ[Φ].A

Δ ⊢ v:A       Δ ⊢ H:Type
──────────────────────── V-inclusion
Δ ; H ⊢ v:A
```

Small steps are `ν ⊢ e → e′`, where the ambient environment `ν` is a value. Evaluation is deterministic call by value, left to right. All strict operands run under the same `ν`, except the body of a box. The strict positions are: primitive arguments; condition; pair operands; projection operands; function then argument; scrutinee; tag/find operand; record initializers; field projection; merge operands; take/drop/rename operand; type-application function; package payload; unpack scrutinee; fold/unfold operand. Do not evaluate lambda, recursive, type-abstraction, case-branch, or unpack bodies early.

```text
ν ⊢ @                          → ν
ν ⊢ λ[A].e                     → clo(ν,A,e)
ν ⊢ rec[A,B].e                 → rclo(ν,A,B,e)
ν ⊢ Λa:κ[Φ].e                 → tclo(ν,a:κ[Φ],e)

ν ⊢ clo(v,A,e) w              → pair(v,w) ▷ e
ν ⊢ f w                       → pair(pair(v,f),w) ▷ e
    where f = rclo(v,A,B,e)
ν ⊢ tclo(v,a:κ[Φ],e)[U]       → v ▷ e[U/a]

ν ⊢ πᵢ pair(v₁,v₂)            → vᵢ
ν ⊢ case (inl v) of e₁ | e₂   → pair(ν,v) ▷ e₁
ν ⊢ case (inr v) of e₁ | e₂   → pair(ν,v) ▷ e₂
ν ⊢ unpack pack[U,v] as a in e → pair(ν,v) ▷ e[U/a]
ν ⊢ unfold (fold[μa.A] v)      → v

ν ⊢ e₁ ▷ e₂ → e₁′ ▷ e₂       if ν ⊢ e₁ → e₁′
ν ⊢ v ▷ e → v ▷ e′           if v ⊢ e → e′
ν ⊢ v ▷ w → w                 when w is a value
```

Record operations reduce on maps: projection returns the field; merge forms their disjoint union; take/drop keep/remove exactly `L`; rename changes the one key. A fully evaluated literal is its record-map value, without sorting its earlier computation. `find` returns the uniquely located tagged payload. A boolean condition selects its branch; primitive operations apply their total interpretation. These equations plus the strict positions above define every reduction; ill-typed operands may be stuck.

Type/row substitution is capture avoiding and acts on all annotations, guards, stored code, and witnesses. No runtime **term** substitution or type environment is needed. An erased implementation may discard type arguments and witnesses, but must retain type-closure delay and activation. Erasure is not an additional theorem promised here.

## 5. Subtyping is a canonical adapter construction

The judgment `Δ ⊢ A ≼ B ↝ c` constructs a closed ordinary term of type `A→B`. “Closed” means independent of the ambient value environment; its free type variables remain in `Δ`. Write `close(e) ≜ unit ▷ e`. The following are the complete cases, in this order:

1. **Equality:** if `A≡B`, return `close(λx:A.x)`.
2. **Functions:** for `A₁→A₂ ≼ B₁→B₂`, require `B₁≼A₁ ↝ c₁` and `A₂≼B₂ ↝ c₂`; return `close(λf:A₁→A₂. λx:B₁. c₂ (f (c₁ x)))`.
3. **Records:** use one of the two cases below, with recursively generated field adapters.
4. **Universals:** for aligned `∀a:κ[Φ].A ≼ ∀a:κ[Φ].B`, require identical normalized kinds/guards and `Δ,a:κ,Φ ⊢ A≼B ↝ c`; return `close(λf:(∀a:κ[Φ].A). Λa:κ[Φ]. c (f[a]))`.
5. Otherwise reject.

There is no subsumption or transitivity rule that introduces other adapters. In particular there is no implicit type instantiation, bounded quantification, or coercion between different abstract identities. Products, sums, tags, recursive types, and existential types are invariant except for equality. Record fields may contain these invariant types.

Normalize the source record row to `F⊎ρ` and the target to `G⊎σ`. Require `dom(G)⊆dom(F)` and `F(ℓ)≼G(ℓ) ↝ cℓ` for every target field. Then:

```text
same opaque remainder, σ=ρ:
  close(λr:Rec(F⊎ρ).
    merge({ℓ = cℓ(r.ℓ) | ℓ∈dom(G)}, drop_dom(F) r))

closed target, σ=∅:
  close(λr:Rec(F⊎ρ). {ℓ = cℓ(r.ℓ) | ℓ∈dom(G)})
```

Use the same-remainder case first if both apply, and a fixed label order for generated fields. Runtime construction order of these adapters is therefore fixed. They never inspect an abstract row or invoke a wrapped service merely to construct its adapter.

`view[B] e` is notation for `c e` when `e:A` and `A≼B ↝ c`; it is not a new runtime construct. Call by value evaluates `e` exactly once **before** restriction or wrapping, including initializers of subsequently discarded fields. This also prevents a function/universal adapter from making a divergent input terminate merely by delaying it.

For example:

```text
{process : {name:String} → {ok:Bool,trace:String}}
  ≼
{process : {name:String,age:Int} → {ok:Bool}}
```

The generated function restricts its argument, calls the original function, and restricts its result. Likewise `view[{x:Int}] {x=1,y=true}` produces an actual one-field record, so extending it with `{y=2}` is safe.

## 6. Design checks and scope

These are derivations the specification must support, not experimental evidence of a proof:

```text
Int ⊢ @ : Int                              7 ▷ @  →* 7
Δ,a:Type ; a ⊢ @ : a                      abstract values can be environments
Unit ⊢ Λa:Type. λ[a].(π₂ @ ▷ @) : ∀a.a→a
Unit ⊢ Λr:Row[health # r]. λ[Rec(r)].
         merge(π₂ @,{health=λ[Unit].true})
       : ∀r:Row[health # r]. Rec(r)→Rec(r⊎{health:Unit→Bool})
```

In the polymorphic box example, applying the type closure and then the value closure returns the argument through a native box. No hidden environment parameter is generated. A divergent body inside `Λa.e` remains delayed until type application.

The design deliberately excludes arbitrary abstract-row splitting, higher-kinded types, recursive module initialization, mutable references, and ML functor identity. Runtime records do not contain type definitions. Public rows commute; ordered environments and initializer evaluation order do not.

## 7. Observation and relation conventions

`ν ⊢ e ⇓ v` (equivalently `e ⇓ν v`) abbreviates `ν ⊢ e →* v` with `v` a value; `ν ⊢ e ⇑` (equivalently `e ⇑ν`) denotes an infinite reduction. Ground observation types are `Unit`, `Int`, `Bool`, and `String`. At the displayed `Δ;H`, contextual equivalence `e≈A e′` quantifies over closing type/row substitutions satisfying `Δ`, well-typed ambient values, and closing well-typed observation contexts: both sides use the same context and ambient value and produce the same ground value or both diverge.

An expression hole retains its declared local `Δ;H` typing judgment. A runtime capture slot instead requires a value hole with ambient-independent value typing. Typed contexts respect this distinction, including holes inside stored closure code.

An admissible relation is a downward-closed family `Rₙ` of pairs of closed, well-typed values at two witness types. The value relation `Vₙ(A;η)` interprets free type variables using such families; a row variable is interpreted by a finite map with the same labels on both sides and an admissible relation for each pair of field types. The paired instantiations must satisfy the declared row guards.

Its clauses are: equal base values; componentwise products, tags, records, and matching sum injections; functions taking `Vⱼ`-related arguments to `Eⱼ`-related **activated bodies** for every `j<n`; universals taking every pair of admissibly related, guard-satisfying instantiations to `Eⱼ`-related **instantiated bodies** for every `j<n`; existential packages whose payloads are `Vₙ`-related under some admissible witness relation; and folds whose unfolded payloads are related at every `j<n`. Interpret recursive unfolding at the smaller index. Records have exactly the labels of their interpreted rows, including the assigned opaque remainder.

For a configuration `(ν,e)`, define activation by:

```text
act(clo(v,A,b),w)          = (pair(v,w), b)
act(f,w), f=rclo(v,A,B,b)  = (pair(pair(v,f),w), b)
inst(tclo(v,a:κ[Φ],b),U)  = (v, b[U/a]).
```

Here `Eₙ` is the symmetric computation relation: for each `k<n`, termination of either configuration in `k` steps must be matched by termination of the other in finitely many steps, with the resulting values in `Vₙ₋ₖ`. The arrow/universal clauses above use `act`/`inst`; actual application and box steps are accounted for by the compatibility proof. Counting these steps inside the clauses as well would invalidate the finite-index argument. Related open code runs under related ambient values.

[target-proofs.MD §R](target-proofs.MD#r-logical-relations-and-contextual-observation) gives the full definitions, guarded construction for recursive types, and proofs of compatibility and contextual adequacy.

## 8. Main theorems

The same statements appear at the end of [target-proofs.MD](target-proofs.MD), each followed by its plain-English meaning and manual proof. Supporting lemmas precede them there.

### T1. Type safety and determinism

The following three subtheorems cover native query, boxes, polymorphism, records, packages, and recursion.

#### T1.1. Preservation

**Theorem T1.1 (Preservation).** If `∅ ⊢ ν : H`, `∅ ; H ⊢ e : A`, and `ν ⊢ e → e′`, then `∅ ; H ⊢ e′ : A`.

**Meaning.** If a well-typed expression takes a step under a well-typed environment, the resulting expression has the same type.

#### T1.2. Progress

**Theorem T1.2 (Progress).** If `∅ ⊢ ν : H` and `∅ ; H ⊢ e : A`, then `e ∈ Val` or there exists an expression `e′` such that `ν ⊢ e → e′`.

**Meaning.** A well-typed expression under a well-typed environment is either a value or can take a step.

#### T1.3. Determinism

**Theorem T1.3 (Determinism).** If `∅ ⊢ ν : H`, `∅ ; H ⊢ e : A`, `ν ⊢ e → e₁`, and `ν ⊢ e → e₂`, then `e₁ = e₂`.

**Meaning.** If a well-typed expression can take two steps under the same well-typed environment, both steps produce the same expression.

Together, these guarantee deterministic evaluation without stuck states. Divergence remains allowed.

### T2. Correct and coherent structural adaptation

`θ ⊨ Δ` means that `θ` is a closing type/row substitution satisfying the declarations and guards in `Δ`.

#### T2.1. Adapter typing

**Theorem T2.1 (Adapter typing).** If `Δ ⊢ A ≼ B ↝ c` and `Δ ⊢ H : Type`, then `Δ ; H ⊢ c : A → B`.

**Meaning.** An adapter generated from `A` to `B` has type `A→B` under every well-formed ambient type.

#### T2.2. Termination on values

**Theorem T2.2 (Termination on values).** If `Δ ⊢ A ≼ B ↝ c`, `Δ ⊢ H : Type`, `θ ⊨ Δ`, `∅ ⊢ ν : θH`, and `∅ ⊢ v : θA`, then there exists a value `w` such that `ν ⊢ (θc) v ⇓ w` and `∅ ⊢ w : θB`.

**Meaning.** Applying a generated adapter to an already evaluated `A` value terminates at a `B` value. This concerns constructing the adapted value; later calls to an adapted function may still diverge.

#### T2.3. Exact record shape

**Theorem T2.3 (Exact record shape).** If `Δ ⊢ A ≼ Rec(R) ↝ c`, `Δ ⊢ H : Type`, `θ ⊨ Δ`, `∅ ⊢ ν : θH`, `∅ ⊢ v : θA`, and `ν ⊢ (θc) v ⇓ w`, then `w` is a record value and `dom(w) = dom(θR)`.

**Meaning.** An adapter targeting a record type produces exactly the fields specified by that row, with no hidden extra fields.

#### T2.4. Divergence preservation and reflection

**Theorem T2.4 (Divergence preservation and reflection).** If `Δ ⊢ A ≼ B ↝ c`, `Δ ; H ⊢ e : A`, `θ ⊨ Δ`, and `∅ ⊢ ν : θH`, then `ν ⊢ θ(c e) ⇑` if and only if `ν ⊢ θe ⇑`.

**Meaning.** Adapting an expression diverges exactly when evaluating the input expression diverges.

The specified call-by-value application `c e` evaluates the input `e` once before adapting its resulting value.

#### T2.5. Composition coherence

**Theorem T2.5 (Composition coherence).** If `Δ ⊢ A ≼ B ↝ c₁`, `Δ ⊢ B ≼ C ↝ c₂`, `Δ ⊢ A ≼ C ↝ c₃`, and `Δ ; H ⊢ e : A`, then `c₂(c₁ e) ≈C c₃ e` in context `Δ ; H`.

**Meaning.** If all three canonical adapters exist, adapting from `A` through `B` to `C` is contextually equivalent to adapting directly from `A` to `C`.

Here `≈` quantifies over closing substitutions and well-typed observation contexts, including termination and divergence.

### T3. Existential representation independence

**Theorem T3 (Existential representation independence).** Let `pᵢ = pack[Aᵢ,vᵢ]` for `i = 1,2`. If `∅ ⊢ pᵢ : ∃a:Type.T` for both packages, the public type `∃a:Type.T` is closed, and there exists an admissible representation relation `R` between `A₁` and `A₂` such that `(v₁,v₂) ∈ Vₙ(T; a↦R)` for every `n ∈ ℕ`, then `p₁ ≈ p₂` at type `∃a:Type.T`.

**Meaning.** Every well-typed client observes the same ground result or divergence from the two related implementations, even when it uses native query and boxes.

`Vₙ` and admissibility are specified in [target.MD §7](target.MD#7-observation-and-relation-conventions). Matching public types alone is insufficient; the exported implementations must satisfy the relational premise.

### T4. Legacy target preservation

This group concerns translating the existing λE target into the new calculus. Option A is already a fragment of Option B by construction and has no separate compatibility theorem.

The subscript `old` identifies the existing calculus. `ι` translates old types, `E` translates old programs, and `V` translates old runtime values. The value translation `V` is distinct from the indexed relation `Vₙ` in T3.

Here `∅ ⊢_old v:A` abbreviates `Value_old(v) ∧ HasType_old(Unit,v,A)`. An old configuration is **well scoped** when each ordinary type annotation is closed, each `fold[T]` annotation is a type body with at most its fold-bound index free, and every child, capture, and stored body satisfies the same condition. Under `d` enclosing recursive binders, a closed annotation uses only indices `<d`. This makes the stated scope condition precise; it is not a termination assumption.

**Legacy embedding.** `ι` maps old unit/integer/function/sum/recursive types structurally, ordered conjunction to `×`, and labeled records to `Tag`. Translate recursive type indices to bound variables capture avoidingly. With a nearest-first binder list `ā` of length `d`, index `i<d` maps to `ā[i]`; an out-of-scope index `i≥d` maps to the reserved free name `ζᵢ₋d`. Generated binders avoid that namespace, and alpha-renaming never changes free `ζ` names. The fallback makes translation total on the arbitrary old values quantified in T4.2; it is never used on well-scoped annotations. For programs, `E` maps positional projection `n` to `π₂(π₁ⁿ E(e))`, nonvalue merge to `E(e₁) & E(e₂)`, old `fold[T]` to `fold[ι(μT)]`, and other program forms homomorphically.

For values, `V` maps old merge values to `pair(V(v₁),V(v₂))`, ordinary closures to `clo(V(capture), translated annotation, E(body))`, recursive closures similarly, and other values componentwise. On runtime syntax, the value case has priority: `E(v)=V(v)`. Thus translated ambient and captured environments remain values. This is an embedding of ordered environments, not their identification with exact public rows.

On a malformed old closure with a nonvalue capture, `E` still translates its capture and code recursively into the corresponding raw target closure form. Such forms have no typing derivation or capture-evaluation rule. This total clause is needed only because T4.2 quantifies over arbitrary old result values, whose stored code need not itself be well typed.

#### T4.1. Legacy type preservation

**Theorem T4.1 (Legacy type preservation).** If `(ν,e)` is well scoped, `∅ ⊢_old ν : H`, and `H ⊢_old e : A`, then `∅ ⊢ V(ν) : ι(H)` and `∅ ; ι(H) ⊢ E(e) : ι(A)`.

**Meaning.** Translating an old program and its environment preserves their types.

#### T4.2. Legacy termination and result correspondence

**Theorem T4.2 (Legacy termination and result correspondence).** If `(ν,e)` is well scoped, `∅ ⊢_old ν : H`, and `H ⊢_old e : A`, then, for every old value `v`, `ν ⊢_old e ⇓ v` if and only if `V(ν) ⊢ E(e) ⇓ V(v)`.

**Meaning.** Old and translated programs produce corresponding terminating results. The translation may take extra administrative steps.

#### T4.3. Legacy divergence correspondence

**Theorem T4.3 (Legacy divergence correspondence).** If `(ν,e)` is well scoped, `∅ ⊢_old ν : H`, and `H ⊢_old e : A`, then `ν ⊢_old e ⇑` if and only if `V(ν) ⊢ E(e) ⇑`.

**Meaning.** Translating an old program neither introduces nor removes divergence.


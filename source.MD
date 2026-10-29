# Annotated SCE: source calculus

**Status:** annotated source specification, with manual proofs in [source-proofs.MD](source-proofs.MD). **All source theorems S1–S5 are Lean-checked:** full safety and elaboration/execution correspondence, behavioral separate compilation, contextual staged/commuting linking, confinement, exact export retention, and abstract-module replacement. See the [mechanization status](LeanSce/MECHANIZATION.md). [Theory.MD](Theory.MD) gives the motivation; [target.MD](target.MD) defines the common computational core.

**Inference policy:** the formal source has explicit type/row binders, type applications, function parameter types, module interfaces, and partial-link partitions. A later frontend may reconstruct these annotations. That frontend is outside the present theorem statements. Polymorphism survives elaboration.

## 1. Source types and notation

Use the target's kinds, type/row variables, finite exact rows, row constraints, equality, base types, functions, ordered products, sums, iso-recursive types, universals, and existentials. Add one source-only constructor:

```text
A,B ::= target type constructors, recursively over source types
      | Mod[I ⇒ O]

I,O,R ::= ∅ | {ℓ:A} | r | R ⊎ R
```

`Rec R` is an already available record of exports; `Mod[I ⇒ O]` is a suspended module awaiting imports `I` and producing exports `O`. These are different types. A module is not callable by ordinary function application. Public records have unique labels; `R ⊎ S` requires `R # S`.

The additional kinding rule is `Δ ⊢ I:Row, Δ ⊢ O:Row ⇒ Δ ⊢ Mod[I⇒O]:Type`. It imposes no disjointness between imports and exports: only operations that retain both rows require that condition.

The judgment is `Δ ; H ⊢s e : A`. As in the target, `H` is the type of the native value environment and may be an arbitrary type. Static types and row constraints live in `Δ`, never as reified type-definition fields. Empty quantifier guards may be omitted in examples.

Names in examples are notation for lexical projections, not another dynamic environment. In `fn (x:A) { e }`, `x` denotes `π₂ query` and the preceding lexical scope denotes `π₁ query`. Existing aliases acquire one `π₁` when a value binder is entered. A type binder adds no value frame; unpacking adds its one value payload. Entering a module body resets value-name aliases to its declared imports and captures; an import name initially denotes `query.ℓ`. Lexical type names remain in `Δ`. This makes name resolution explicit without compiling `query` to an environment variable.

Type equality and subtyping preserve source constructor heads. In particular, `Mod[I⇒O]` is invariant in automatic subtyping and is never equated with `Rec I → Rec O`. Source subtyping otherwise uses the target's canonical structural rules recursively. Equal module-typed fields pass through unchanged. Explicit module wrappers can express more elaborate adaptations.

## 2. Syntax

The common source core is the target's programmer syntax, with source types in annotations and `query` spelling `@`. This includes native boxes, functions and recursion, ordered pairs and projections, sums/case, fold/unfold, exact records, merge, finite-label `take_L`/`drop_L`, renaming, explicit `Λ`/type application, and existential pack/unpack. Legacy sequential products and labeled tags remain available as the target's defined forms.

Add the following forms:

```text
let[A] e₁ in e₂                    ordinary lexical value binding
view[B] e                         structural adaptation to B
module[I ⇒ O] { e }                sandboxed suspended module
capture e₀ module[I ⇒ O] { e }     suspended module with explicit captures
run m p                           execute m with imports selected from p
link p with m                     execute m and retain p's exports
provide[J; K] p to m               supply J now, retain imports K
complete m                        run an import-free module
type α = A in e                    transparent static alias
```

Record extension `p extend q` means `merge(p,q)`. All fields of a record literal are initialized left-to-right in the same ambient environment; field order is not an implicit sequence of bindings. Use `let` when a later initializer needs an earlier result.

`provide[J;K]` states the partition of the required interface, not a runtime search for missing fields. `J` and `K` may themselves be unknown rows, provided their disjointness is established and the provider can be adapted to `J`.

The surface type checker uses canonical matching and decorates `view`, `run`, `link`, and `provide` with an adapter certificate `d=(A,B,cˢ_d)`: its endpoints and generated source adapter **code**. Canonicality is a property of this initial generation, not a runtime typing condition. Type substitution acts on the stored endpoints and code; it does not rerun matching after instantiation. This is deterministic checking of annotated programs, not the deferred inference feature.

The checker also records the capture row: `capture[C] e₀ module[I⇒O]{e}`. The displayed provider/import/export rows on runtime `run`, `link`, `provide`, and `complete[O]` are likewise stored annotations. Names and transparent aliases are expanded before the formal checked-term judgment is used. These annotations make reduction independent of a choice of typing derivation.

## 3. Typing

Every common-core constructor has exactly its target rule, replacing `⊢` with `⊢s`. Source module values are opaque to legacy tagged-tree lookup, so additionally `absentℓ(Mod[I⇒O])` holds. Type/row binders obey the target's guard restriction: new disjointness obligations concern the freshly bound row variable. In particular:

```text
Δ ; H ⊢s query : H

Δ ; H ⊢s e₁ : H′     Δ ; H′ ⊢s e₂ : A
─────────────────────────────────────
Δ ; H ⊢s box e₁ in e₂ : A

Δ ; H ⊢s e₁ : A      Δ ; H × A ⊢s e₂ : B
────────────────────────────────────────
Δ ; H ⊢s let[A] e₁ in e₂ : B
```

There is no unrestricted subsumption rule. Ordinary applications use the declared parameter type; `view` supplies an explicit adaptation boundary. Linking operations insert the required adaptations automatically.

Write `Δ ⊢s A ≤ B ↦ c` for the canonical source adapter judgment. It uses exactly the target's rules with source constructor heads preserved, and constructs a closed ordinary source function `c : A → B`. It does not execute module bodies. Row adaptation supports matching unknown tails or a completely known target row; it does not guess how to select an arbitrary unknown subrow.

```text
Δ ; H ⊢s e : A       Δ ⊢s A ≤ B ↦ c
─────────────────────────────────────
Δ ; H ⊢s view[B] e : B
```

### Module creation

```text
Δ ; Rec I ⊢s e : Rec O
──────────────────────────────────────────────
Δ ; H ⊢s module[I ⇒ O] { e } : Mod[I ⇒ O]

Δ ; H ⊢s e₀ : Rec C     Δ ⊢ C # I
Δ ; Rec(C ⊎ I) ⊢s e : Rec O
────────────────────────────────────────────────────────
Δ ; H ⊢s capture e₀ module[I ⇒ O] { e } : Mod[I ⇒ O]
```

A sandboxed body sees exactly its imports at entry. An open body sees exactly its declared captures and imports. Subsequent user-written functions and lets extend that scope normally. The capture expression is evaluated at module creation; the body is delayed until execution. Captures and imports cannot silently shadow one another.

### Execution, linking, and staging

In these rules `c` adapts records by the canonical source adapter judgment.

```text
Δ ; H ⊢s m : Mod[I ⇒ O]     Δ ; H ⊢s p : Rec P
Δ ⊢s Rec P ≤ Rec I ↦ c
───────────────────────────────────────────────────────
Δ ; H ⊢s run m p : Rec O

Δ ; H ⊢s p : Rec P          Δ ; H ⊢s m : Mod[I ⇒ O]
Δ ⊢s Rec P ≤ Rec I ↦ c      Δ ⊢ P # O
────────────────────────────────────────────────────────
Δ ; H ⊢s link p with m : Rec(P ⊎ O)

Δ ; H ⊢s p : Rec P          Δ ; H ⊢s m : Mod[J ⊎ K ⇒ O]
Δ ⊢ J # K                  Δ ⊢s Rec P ≤ Rec J ↦ c
────────────────────────────────────────────────────────
Δ ; H ⊢s provide[J;K] p to m : Mod[K ⇒ O]

Δ ; H ⊢s m : Mod[∅ ⇒ O]
────────────────────────────────
Δ ; H ⊢s complete m : Rec O
```

`run` returns only the client's exports, so it does not require `P # O`. `link` retains all provider exports and therefore rejects collisions. Resolve collisions with a view, finite-label removal, or renaming before linking, or use `run` when the provider's exports need not be retained.

Supplying all imports with `provide[J;∅]` still produces a suspended module. Only `complete` or `run` executes it. There is no implicit final-stage execution.

### Abstract and transparent types

Use the common existential rules, including the non-escape condition on unpacking. An opaque module is an existential package containing its public record or suspended module:

```text
∃User:Type. Rec{load:Unit→User, render:User→String}
```

Unpacking once makes the same `User` available to every client in that lexical scope. A result mentioning `User` must remain in scope or be repackaged. `Users.User` may later be notation for a witness introduced by a lexical unpack; it is not arbitrary type projection from a runtime expression. Two independent unpacks do not establish equality between their witnesses.

`type α=A in e ≜ e[A/α]` is a capture-avoiding static abbreviation, with `A` well formed in `Δ`. It introduces no value binding and does not change `query`; it is not an extra runtime form.

## 4. Direct source semantics

Use deterministic, left-to-right call-by-value reduction `v ⊢s e → e′`. The common core has the target's operational rules, on source terms and source values. Closure bodies retain their captured source environments; no runtime term substitution is introduced.

Below `⊢s` on checked/runtime syntax uses the retained-certificate rules. The surface matching rules in §3 establish those premises when generating checked code. Common raw closure forms and their value-capture typing conditions are inherited from the target. Legacy `find` treats both module-value forms below as opaque.

Extend the expression grammar with these runtime-only forms:

```text
e ::= … | mod(c; C,I,O; e) | resid(m; e; J,K,O) | invoke(e,e)
v ::= common source values
    | mod(c; C,I,O; e)             c is a record value
    | resid(m; j; J,K,O)           m and j are values
```

Use the common core's ambient-independent value-typing judgment `Δ ⊢s v:A`, extended by the following rules. A typed value may occur under any ambient `H`.

```text
Δ ⊢s c : Rec C       Δ ⊢ C # I
Δ ; Rec(C⊎I) ⊢s e : Rec O
────────────────────────────────────────────────
Δ ⊢s mod(c; C,I,O; e) : Mod[I⇒O]

Δ ⊢s m : Mod[J⊎K⇒O]     Δ ⊢s j : Rec J     Δ ⊢ J # K
─────────────────────────────────────────────────────────
Δ ⊢s resid(m; j; J,K,O) : Mod[K⇒O]
```

The in-progress expression `resid(m; e; J,K,O)` requires a **value** `m` with the displayed module type, `Δ ⊢ J # K`, and `Δ;H ⊢s e:Rec J`; its type is `Mod[K⇒O]`. Internal `invoke(e₁,e₂):Rec O` requires `e₁:Mod[I⇒O]` and `e₂:Rec I` under the same `H`; it performs no further matching. A module closure stores its checked body; a completed residual stores already adapted supplied imports.

Runtime certificates have the following weaker typing rule. Here `k` is ordinary common-core source code, with no `view` or module operations, and `closeˢ(k) ≜ box () in k` makes its value environment independent of the caller.

```text
d = (A,B,closeˢ(k))       Δ ; Unit ⊢s k : A→B
────────────────────────────────────────────
Δ ⊢cert d : A ⇒ B
```

The decorated runtime `view[A⇒B;d] e` requires `e:A` and `Δ ⊢cert d:A⇒B`, and has type `B`. The decorated `run`, `link`, and `provide` use their earlier typing rules with canonical matching replaced by the corresponding certificate premise. These rules may admit arbitrary well-typed closed core adapter code; they do not assert that every such certificate is canonical or terminating. Reachable certificates originate in checked canonical generation and subsequent type/row substitution. All source-level linking laws concern that checked language.

For example, matching `Rec r` to `Rec ∅` initially generates record restriction. Substituting `r=∅` retains that restriction code, even though rerunning the canonical matcher would choose identity. The retained code remains a well-typed certificate, which is the property needed by preservation.

The initially generated `cˢ_d` follows the target's structural recipe, but uses source functions and source types. Its record case physically builds the advertised exact record and carries a matching unknown tail unchanged; its function case creates the prescribed argument/result wrapper; its universal case creates a delayed type abstraction with the same binder and constraints. Equal types use identity. `Mod` has only the equal-type case. Thus source evaluation is defined independently of executing the elaborated target program.

The following are the principal contractions; all displayed operands other than bodies are values:

```text
v ⊢s let[A] u in e
    → box pair(v,u) in e

v ⊢s view[A⇒B;d] u
    → cˢ_d u

v ⊢s module[I⇒O] {e}
    → mod({}; ∅,I,O; e)

v ⊢s capture[C] c module[I⇒O] {e}
    → mod(c; C,I,O; e)

v ⊢s run[P,I,O;d] m p
    → invoke(m, view[Rec P⇒Rec I;d] p)

v ⊢s invoke(mod(c; C,I,O; e), i)
    → box merge(c,i) in e

v ⊢s invoke(resid(m; j; J,K,O), k)
    → invoke(m, merge(j,k))

v ⊢s link[P,I,O;d] p with m
    → merge(p, run[P,I,O;d] m p)

v ⊢s provide[P;J;K;O;d] p to m
    → resid(m; view[Rec P⇒Rec J;d] p; J,K,O)

v ⊢s complete[O] m
    → run[∅,∅,O;id] m {}
```

`type α=A in e` is removed before evaluation. Record merge is a finite-map union after both operands have been evaluated; it does not expose one operand as the environment of the other.

Evaluation positions complete these rules: `let` evaluates its bound expression; `view` its operand; `capture` its capture expression; `run` its module then provider; `link` and `provide` their provider then module; `complete` its module; `invoke` its module then imports; `resid` its saved-import expression. There is no reduction inside a suspended module body. The common-core evaluation contexts apply as usual, with boxes using their own environment when evaluating their bodies.

This order matters. A provider field that will be discarded is still initialized before adaptation. If its initialization diverges, the link diverges. Already evaluated field values may be reordered as a finite map; computations are never reordered by interface equality.

## 5. Elaboration into the target

Write `⟦A⟧` for type translation and `Δ ; H ⊢s e : A ⇝ E` for typed elaboration. It is homomorphic on common types and terms, except:

```text
⟦Mod[I⇒O]⟧ = Rec⟦I⟧ → Rec⟦O⟧
⟦query⟧ = @
⟦let[A] e₁ in e₂⟧ = let ⟦e₁⟧ in ⟦e₂⟧
⟦view[B] e⟧ = C_d ⟦e⟧       when surface matching A ≤ B generated d
⟦type α=A in e⟧ = ⟦e[A/α]⟧
```

On checked programmer syntax this is a deterministic translation, modulo bound names and normalized type annotations. For intermediate expressions, `e ⇝ E` and value correspondence `v ~ V` are defined mutually below; typed elaboration means this relation together with `Δ;H⊢s e:A`. For a type/row substitution `θ`, write `θ̄(a)=⟦θ(a)⟧`; in particular, `⟦θA⟧≡θ̄⟦A⟧`.

Define `C_d = ⟦cˢ_d⟧`, the homomorphic translation of the closed ordinary-core code **stored in the source certificate**. That code contains no `view` or module operations, so the definition is not circular. In particular, an initially equal `Mod` case becomes identity at its translated arrow type. Do not rerun canonical matching on erased or instantiated types: source constructor heads can collapse under erasure, and substitution can change which canonical case would be chosen.

The same compilation clause applies to an intermediate runtime `view[A⇒B;d] e` whenever `Δ ⊢cert d:A⇒B`; the decorated runtime `run`, `link`, and `provide` likewise reuse the stored `C_d` in the templates below. Thus elaboration of intermediate terms requires well-typed adapter code, not a fresh canonical derivation. Type/row abstractions and applications, existential packages, and native boxes remain explicit target constructs.

### Module constructors

Here `E` is the separately compiled body. All target types in these templates are translations of the corresponding source types.

```text
Sandbox_I,O(E) =
  () ▷ λ[Rec I]. (π₂ @ ▷ E)

Capture_C,I,O(E) =
  () ▷ λ[Rec C]. λ[Rec I].
    (merge(π₂(π₁ @), π₂ @) ▷ E)

⟦module[I⇒O] {e}⟧ = Sandbox_I,O(⟦e⟧)
⟦capture[C] e₀ module[I⇒O] {e}⟧ = Capture_C,I,O(⟦e⟧) ⟦e₀⟧
```

The target lambda's capture/argument pair is removed by a native box before entering `E`. Consequently the body sees its specified imports and captures, not a compiler-created lambda frame.

### Closed linking combinators

The following named templates are precise notation for target lambdas and lexical projections. `let x=e in b` is the target's derived lexical let. A name refers to its corresponding binder projection, with the usual shift under subsequent binders. Each template is created inside `() ▷ ...`, so its term environment is closed; it may have free static parameters in `Δ`.

```text
Run_d;P,I,O = () ▷
  λm:Rec I→Rec O. λp:Rec P.
    m (C_d p)

Link_d;P,I,O = () ▷
  λp:Rec P. λm:Rec I→Rec O.
    let i = C_d p in
    let o = m i in
    merge(p,o)

Provide_d;P,J,K,O = () ▷
  λp:Rec P. λm:Rec(J⊎K)→Rec O.
    let j = C_d p in
    pair(m,j) ▷ λ[Rec K].
      (π₁(π₁ @)) (merge(π₂(π₁ @), π₂ @))
```

For `Run` and `Link`, `d` has endpoints `Rec P⇒Rec I`; for `Provide`, its endpoints are `Rec P⇒Rec J`. The box in `Provide` retains exactly the saved module and adapted imports in the new wrapper's capture. Its final lambda is returned without executing the module body.

```text
⟦run m p⟧             = (Run_d;P,I,O ⟦m⟧) ⟦p⟧
⟦link p with m⟧       = (Link_d;P,I,O ⟦p⟧) ⟦m⟧
⟦provide[J;K] p to m⟧ = (Provide_d;P,J,K,O ⟦p⟧) ⟦m⟧
⟦complete m⟧          = (Run_id;∅,∅,O ⟦m⟧) {}
```

Curried application is intentional: each user operand is evaluated under its original ambient environment. Replacing these expressions with `let p=⟦p⟧ in let m=⟦m⟧ in ...` would expose the generated provider binding to a native `query` in the module operand.

### Runtime elaboration and value correspondence

Define `v ~ V` componentwise on constants, pairs, tags, record maps, injections, folds, and packages, translating annotations and witnesses. For captured closures, `c~Cv` and `b⇝B` give:

```text
clo(c,A,b)          ~ clo(Cv,⟦A⟧,B)
rclo(c,A,D,b)       ~ rclo(Cv,⟦A⟧,⟦D⟧,B)
tclo(c,a:κ[Φ],b)   ~ tclo(Cv,a:κ[⟦Φ⟧],B).
```

For module values, with `c~Cv`, `m~M`, `j~Jv`, and the stored body `e⇝E`:

```text
mod(c; C₀,I,O; e)
  ~ clo(pair((),Cv), Rec⟦I⟧,
        merge(π₂(π₁ @),π₂ @) ▷ E)

mod({}; ∅,I,O; e)
  ~ clo((), Rec⟦I⟧, π₂ @ ▷ E)       also permits Sandbox's closure

resid(m; j; J,K,O)
  ~ clo(pair(M,Jv), Rec⟦K⟧,
        (π₁(π₁ @)) (merge(π₂(π₁ @),π₂ @)))
```

The relation permits both representations of an empty-capture module. These are exactly the final closures constructed by the templates, rather than a unique syntactic translation of module values. The correspondence specifies correctness; it does not define source evaluation.

Runtime expressions use the same compilation clauses, with the **value clause first**: `v~V ⇒ v⇝V`. Internal invocation elaborates to application. For a residual whose saved-import expression is still a nonvalue, use this closed constructor (all row/type parameters translated):

```text
Residual_J,K,O = () ▷
  λm:Rec(J⊎K)→Rec O. λj:Rec J.
    pair(m,j) ▷ λ[Rec K].
      (π₁(π₁ @)) (merge(π₂(π₁ @),π₂ @))

e₁⇝E₁, e₂⇝E₂
  ⇒ invoke(e₁,e₂) ⇝ E₁ E₂

m~M, e⇝E, e∉Val_s
  ⇒ resid(m;e;J,K,O) ⇝ (Residual_J,K,O M) E.
```

A completed residual instead corresponds directly to its closure value. This distinction preserves valuehood. It means compilation of arbitrary runtime observation contexts is compositional up to target contextual equivalence: the residual constructor evaluates to that same closure. The exact compilation equations for checked programmer syntax remain as displayed above.

### What elaborates away?

| Source feature | Target result |
| --- | --- |
| `Mod[I⇒O]` distinction | Ordinary `Rec I → Rec O` |
| Module constructors | Ordinary closures plus native boxes |
| `run`, `link`, partial provision, completion | Ordinary applications, record operations, and closures |
| Structural matching at a link | Explicit translation of the stored source adapter |
| Transparent type aliases and lexical name notation | Static substitution and projections |
| Type/row polymorphism and hidden types | Remain as universals, type applications, and existentials |
| `query` and boxes | Remain native `@` and boxes |

No environment-parameter encoding, runtime module primitive, runtime subtype test, or inference engine is needed in the target.

## 6. Concrete checks on the design

### Query in both linking operands

Under ambient environment `{n=7}`, consider:

```text
link {x=query.n} with
  capture {seed=query.n}
  module[{x:Int} ⇒ {z:Int}] {
    {z=add(query.seed,query.x)}
  }
```

Both operand queries read the original `{n=7}`. The module captures `{seed=7}`, receives `{x=7}`, and runs its body under exactly `{seed=7,x=7}`. Its result is `{z=14}`; the link returns `{x=7,z=14}`. The `Link` and `Capture` combinators give this same trace without exposing their own bindings to either operand or the body.

For timing, let `m` be a module value whose body diverges and `i` an exact import value. `provide[I;∅] i to m` terminates with a residual module. `complete` on that residual diverges. Supplying imports is not execution.

### A shared hidden representation

The following uses readable lexical names for the formal projection notation:

```text
Users : ∃User. Rec{load:Unit→User, render:User→String}
Users = pack[Int, {load=fn(_:Unit){7}, render=fn(n:Int){show(n)}}]
        as ∃User. Rec{load:Unit→User, render:User→String}

Report = ΛT:Type.
  module[{load:Unit→T, render:T→String} ⇒ {serve:Unit→String}] {
    {serve = fn(_:Unit){ render(load(())) }}
  }

unpack Users as (User, users) in
  let app = link users with Report[User] in
  app.serve(())
```

The final result is `String`, so the hidden witness does not escape. `users.render(7)` fails: `User` is not definitionally `Int` in this scope. Both imported operations use the same unpacked witness. `show` is the target's integer-to-string primitive.

### Preserve unknown exports and remaining imports

```text
withHealth = Λr:Row[health # r].
  fn(m:Rec r) { m extend {health=fn(_:Unit){true}} }

setLocale = Λr:Row[locale # r]. Λo:Row.
  fn(m:Mod[{locale:String}⊎r ⇒ o]) {
    provide[{locale:String};r] {locale="en"} to m
  }
```

The first has result `Rec(r ⊎ {health:Unit→Bool})`. The second returns `Mod[r⇒o]`; the body is still suspended even when `r=∅`. Field order does not matter in either interface. These examples need no inference and no runtime inspection of the unknown row.

### Structural adaptation

```text
provider.process : Rec{name:String} → Rec{ok:Bool, trace:String}
client imports process : Rec{name:String, age:Int} → Rec{ok:Bool}
```

Linking wraps `process` to restrict its argument and its result. The client receives the advertised exact record shapes. If the provider also contains unused exports, they remain in a `link` result but are absent from the sandboxed client's initial environment.

## 7. Fixed boundaries and legacy compatibility

This source supports first-order type and row parameters, explicit impredicative instantiation, scoped existential abstraction, recursive functions/data, and staged linking. It does not yet include higher-kinded abstract constructors, recursive module initialization, mutable references, arbitrary dependent type-member projection, or applicative/generative functor identities.

Full automatic inference remains implementation work. An optional frontend must eventually respect value/function generalization, annotation-guided adaptation, and public compilation interfaces; silently inserting a delayed `Λ` around an eagerly evaluated computation can change divergence.

The old source is not a literal subgrammar: old `Sig A` can describe arbitrary ordered layouts and duplicate labels, whereas new public rows are exact maps. The concrete compatibility route is to compose the existing old-source elaboration with the target document's legacy-core embedding. This preserves old programs without pretending their ordered layouts are row interfaces. It does not claim full abstraction against every new source context.

## 8. Main theorems

The statements below have manual proofs in [source-proofs.MD](source-proofs.MD). Source contextual equivalence `≈s` observes the same ground result or divergence in every well-typed closing source context, under satisfying type/row substitutions and typed ambient values. Expression holes retain their local `Δ;H` judgment; value slots require value holes. Runtime stored code is included, with certificate code retaining its common-core restriction.

`θ̄` is the translated substitution from §5. `Vₙ` in S5 is the target logical relation defined in [target-proofs.MD](target-proofs.MD#r-logical-relations-and-contextual-observation).

### S1. Source safety and elaboration correctness


#### S1.1. Source preservation

**Theorem S1.1 (Source preservation).** If `∅⊢s ν:H`, `∅;H⊢s e:A`, and `ν⊢s e→e′`, then `∅;H⊢s e′:A`.

**Meaning.** Each source step preserves the expression's type, including generated adapters and suspended or partially supplied modules.

#### S1.2. Source progress

**Theorem S1.2 (Source progress).** If `∅⊢s ν:H` and `∅;H⊢s e:A`, then `e∈Val_s` or there exists `e′` such that `ν⊢s e→e′`.

**Meaning.** A well-typed source configuration is a value or can step.

#### S1.3. Source determinism

**Theorem S1.3 (Source determinism).** If `∅⊢s ν:H`, `∅;H⊢s e:A`, `ν⊢s e→e₁`, and `ν⊢s e→e₂`, then `e₁=e₂`.

**Meaning.** Source evaluation has one next step, including the order of provider evaluation and module execution.

#### S1.4. Elaboration preserves typing

**Theorem S1.4 (Elaboration typing).** If `Δ;H ⊢s e:A ⇝ E`, then `⟦Δ⟧;⟦H⟧ ⊢ E:⟦A⟧`.

**Meaning.** A well-typed source program or runtime expression elaborates to a target expression of its translated type.

#### S1.5. Termination and result correspondence

**Theorem S1.5 (Termination and result correspondence).** Suppose `Δ;H ⊢s e:A ⇝ E`, `θ⊨Δ`, `∅⊢s ν:θH`, and `ν~N`. Then:

```text
ν ⊢s θe ⇓ v     ⇒ ∃V. N ⊢ θ̄E ⇓ V ∧ v~V;
N ⊢ θ̄E ⇓ V     ⇒ ∃v. ν ⊢s θe ⇓ v ∧ v~V.
```

**Meaning.** Source and target terminate together and produce corresponding values. At ground types they produce the same constant.

#### S1.6. Divergence correspondence

**Theorem S1.6 (Divergence correspondence).** Under the hypotheses of S1.5, `ν ⊢s θe ⇑` if and only if `N ⊢ θ̄E ⇑`.

**Meaning.** Elaboration neither introduces nor removes divergence, including divergence in discarded initializers, adapters, or module bodies.

### S2. Behavioral separate compilation

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

### S3. Staged linking and commuting interfaces


#### S3.1. Staging

**Theorem S3.1 (Staging).** If `Δ⊢s m:Mod[J⊎K⇒O]`, `Δ⊢s j:Rec J`, `Δ⊢s k:Rec K`, and `Δ⊢J#K`, then, at every well-formed ambient `H`:

```text
run (provide[J;K] j to m) k  ≈s  run m (merge(j,k)) : Rec O.
```

All operands displayed as `m,j,k` are values; adaptation at these exact interfaces uses the equality certificate. Taking `Δ=∅` covers every actual value at any closed instance of an abstract row; an unknown row need not have a syntactic inhabitant before instantiation.

**Meaning.** Supplying some already evaluated imports now and the rest later has the same behavior as supplying their union at execution.

#### S3.2. Commuting stages

**Theorem S3.2 (Commuting stages).** If `Δ⊢s m:Mod[J⊎K⊎L⇒O]`, `j:Rec J`, `k:Rec K`, `l:Rec L` are source values, and `J,K,L` are pairwise disjoint in `Δ`, then, at every well-formed ambient `H`:

```text
run (provide[K;L] k to (provide[J;K⊎L] j to m)) l
  ≈s run (provide[J;L] j to (provide[K;J⊎L] k to m)) l
  ≈s run m (merge(j,merge(k,l))) : Rec O.
```

**Meaning.** Independent stages commute when they supply disjoint, already evaluated imports with the same shared type witnesses.

### S4. Module confinement and exact export retention


#### S4.1. Confinement

**Theorem S4.1 (Module confinement).** If `∅⊢s m:Mod[I⇒O]`, `∅⊢s i:Rec I`, and `∅⊢s νₜ:Hₜ` for `t=1,2`, then:

```text
∀w. (ν₁ ⊢s invoke(m,i) ⇓ w) ⇔ (ν₂ ⊢s invoke(m,i) ⇓ w)
     ν₁ ⊢s invoke(m,i) ⇑     ⇔ ν₂ ⊢s invoke(m,i) ⇑.
```

The same result holds for two already evaluated providers whose retained certificates produce the same exact import value `i`.

**Meaning.** For a fixed module value, execution depends on its declared captures and adapted imports; its caller's environment and unused provider fields do not enter the module's scope.

#### S4.2. Exact export retention

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

### S5. Abstract-module replacement

**Theorem S5 (Abstract-module replacement).** Let `pᵢ=pack[Aᵢ,vᵢ]`, with `∅⊢s pᵢ:∃a:Type.T` for `i=1,2` and closed public type `∃a:Type.T`. Choose corresponding target values `vᵢ~Vᵢ`. If there is an admissible target candidate `R` between `⟦A₁⟧` and `⟦A₂⟧` such that:

```text
∀n∈ℕ. (V₁,V₂) ∈ Vₙ(⟦T⟧; a↦R),
```

then `p₁≈s p₂ : ∃a:Type.T`.

**Meaning.** Every well-typed source client observes the same ground result or divergence when one related hidden implementation replaces the other, including clients that unpack, stage, and link modules.

The relation is precisely the target interpretation of the elaborated public interface: `Mod[I⇒O]` uses the function relation at `Rec⟦I⟧→Rec⟦O⟧`. Recursive, polymorphic, row-polymorphic, and module-valued exports are all allowed. The representatives `V₁,V₂` and candidate `R` are fixed before quantifying over `n`.

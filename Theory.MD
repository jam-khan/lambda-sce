# SCE: stronger system and publication paths

**Publication paths:** the original simply typed SCE paper is currently submitted to OOPSLA. This design can serve as the main system of a replacement manuscript. If the submitted paper is accepted, it can instead support a separate follow-up focused on coherent linking with extensible and abstract interfaces. That paper must cite SCE as its foundation and distinguish the new design and results. The publication path remains conditional; the Option A/B names below record design decisions.

**Decision:** pursue Option B: native first-class environments, type and row polymorphism, abstract/shared types, staged linking, and structural subtyping. Linking remains ordinary evaluation.

**B includes A by construction.** A is the subtyping-free fragment of the same language and evaluator; its explicit views and other features remain available. This inclusion is a design fact, not a separate theorem goal.

Keep `query`/`@` and boxes native. **Do not compile the current environment into an extra variable.**

**Specifications:** [target.MD](target.MD) and [source.MD](source.MD) fix the target and annotated source; their companion proof files give the manual arguments. **All selected main theorems T1–T3 and S1–S5 are Lean-checked**, including execution correspondence, behavioral separate compilation, contextual linking laws, and target/source representation independence. See the [mechanization status](LeanSce/MECHANIZATION.md). This file remains the short design overview.

**Inference decision:** keep practical inference for implementation. The formal source uses explicit annotations and type/row applications; a later frontend can reconstruct them. The current theory does not promise an inference algorithm, inference completeness, or a verified frontend.

## 1. What would make SCE substantially stronger?

| Capability | What it enables |
| --- | --- |
| Type polymorphism | Compile one component for many element/representation types |
| Abstract types and sharing | Hide implementations while several modules agree on one representation type |
| Row polymorphism | Extend a module while preserving exports whose names/types the transformer does not know |
| Commuting interfaces | Connect modules regardless of value-field declaration order |
| Partial linking | Supply dependencies in stages and retain a module awaiting the rest |
| Structural subtyping | Automatically adapt nested records, functions, and polymorphic services |

All six belong to the selected design. Rows and abstraction provide the major module-composition gains; subtyping adds automatic adaptation. A remains a useful proof-building stage, not a competing final choice.

## 2. Which foundation?

| Foundation | Keep | Avoid inheriting automatically |
| --- | --- | --- |
| λE/SCE | Native reification, boxes, closures, linking as evaluation | Treating every interface as an ordered layout |
| FE | Impredicative polymorphism and the goal of shared/transparent module types | Mixed dependent term/type environments and two-sided equality unless examples require them |
| RTE | Native `@`, labeled environments, projection/restriction, interface permutation | Optional/weak/strong fields and its application/`force` protocol |

Our foundation combines these ideas. FE and RTE support different features; neither simply dominates the other.

The intended simplification is to keep **type scope separate from the reifiable value environment**. Accept ordinary static type substitution if that removes unnecessary machinery. Runtime term substitution remains unnecessary.

This supports useful abstract modules, but does not automatically reproduce FE's arbitrary dependent type entries, dynamic type-member projection, or full ML functor identity. FE’s implicit variant also retains its manifest/box-type machinery, so merely choosing that variant would not accomplish this simplification.

## 3. Native target: the central rules

Use the typing judgment:

```text
Δ ; H ⊢ e : A
```

`Δ` contains type/row variables, transparent aliases, and row constraints. `H` describes the current value environment. Types depend on `Δ`; runtime environments do not contain type-definition entries.

Keep `H` general enough for old SCE environments, including ordered pairs and scalar values. Public module interfaces form a separate labeled-record fragment.

```text
Δ ; H ⊢ @ : H

Δ ; H ⊢ e₁ : H′       Δ ; H′ ⊢ e₂ : A
─────────────────────────────────────
Δ ; H ⊢ e₁ ▷ e₂ : A
```

Runtime behavior stays direct:

```text
v ⊢ @ → v
v₀ ⊢ v₁ ▷ e → v₁ ▷ e′     when v₁ ⊢ e → e′
```

A box replaces value scope and retains lexical type scope. Thus `box 7 in query` still returns `7`; polymorphic boxes do not need an encoded source environment. These are proposed rules for a new calculus, not unchanged FE rules.

### Types and module interfaces

Include ordinary functions/data, explicit universal types, primitive existential packages, and exact record rows:

```text
∀α:Type.A               type polymorphism
∃α:Type.A               hidden representation
∀r:Row.A                row polymorphism
Rec({x:A,y:B} ⊎ r)      known fields plus an unknown remainder
```

Public labels are unique; `⊎` requires disjointness. Reorder value fields under the same type binders, without reordering initializer execution. Preserve ordered lexical environments separately; public row permutation does not permute positional bindings.

The annotated source elaborates to explicit target type abstractions and applications: polymorphism does **not** elaborate away. Type-abstraction bodies remain delayed until application. A future erased evaluator must retain that delay. Static type substitution replaces FE's stronger all-substitution-free objective.

An existential package supplies one shared abstract type when unpacked. Dependent results must remain in that scope or be repackaged. Transparent source type members become aliases in `Δ`.

**Abstraction does not break native query.** It requires producers and consumers to agree on the same hidden type. FE's mixed type/value-environment dependencies are a separate complication, present even with transparent types.

## 4. Small source examples

The examples use readable overview notation; [source.MD](source.MD) fixes binding, explicit annotations, and compilation conventions. Empty-argument functions abbreviate `Unit` arguments.

**Hidden representation, shared imports:**

```text
Users : ∃User. Rec{load:Unit→User, render:User→String}
Users = pack[Int, {load=fn(_:Unit){7}, render=fn(x:Int){show(x)}}]

module Report<T> imports { load:()->T, render:T->String } {
  fn serve() -> String { render(load()) }
}

unpack Users as (User, users) in
  let app = link users with Report[User] in
  app.serve()       // "7"
  // users.render(7) is rejected: User is abstract here
```

One unpack introduces the witness shared by both imported operations. Independent unpacks do not establish type equality. A result mentioning the hidden witness must remain in scope or be repackaged. Convenient `Users.User` syntax may later name a lexically unpacked witness; it is not runtime type projection.

**Extend a module without knowing its other exports:**

```text
fn withHealth<R>(m: Rec<R>) {
  m extend { health = () => true }
}

let server = withHealth[{port:Int}]({ port = 8080 })
server.port      // 8080; original field and type preserved
server.health()  // true
```

Require `health` absent from `R`. The same compiled helper works for unrelated export rows. Row polymorphism preserves the unknown remainder; width subtyping alone does not express that relationship.

## 5. Subtyping in the selected target

Synthesize canonical adapters for record width/depth, function variance, and universals with aligned binders and identical guards. Keep abstract identities, existential packages, recursive types, and source module constructors invariant. Match the specified public type grammar, not arbitrary ordered environment types. The target has no implicit subsumption rule: adapters are ordinary terms.

### Concrete comparison with RTE

RTE uses subsumption to give the same expression `e` another type; its semantics does not insert a coercion function for that step. It supports function variance and other subtyping rules, but deliberately omits ordinary record width subtyping. Programmers can explicitly project the wanted fields before passing an argument. See [RTE §3.2](https://arxiv.org/html/2610.27519v1#S3.SS2) and [§6.2](https://arxiv.org/html/2610.27519v1#S6.SS2).

| Situation | RTE | Selected SCE design |
| --- | --- | --- |
| A permitted subtype step | Same expression, different type | Generate an ordinary adapter `c:A→B` |
| Discard extra required fields | Explicit record projection/removal | Automatically restrict at a declared matching boundary |
| Service needs argument/result width adaptation | Programmer supplies a wrapper | Generate the wrapper from interfaces |
| Native environment query | Native `@` | Native `@`; adapters do not encode the environment |

**Payoff 1: adapt separately compiled services automatically.**

```text
provider.process : {name:String}         -> {ok:Bool, trace:String}
client requires  : {name:String, age:Int} -> {ok:Bool}

// Wrapper generated for the already evaluated provider:
processForClient = fn(input:{name:String, age:Int}) {
  let result = provider.process({name=input.name})
  {ok=result.ok}
}
```

B restricts the argument, calls the existing service, and restricts its result. The linker needs only the interfaces; neither module body needs rewriting or recompilation. The same adapter construction handles nested records and aligned polymorphic services. A requires an explicit wrapper.

RTE can express a wrapper performing these projections. Its subsumption alone does not accept this particular interface mismatch because the required width relationships are absent. The payoff is automatic composition, not a claim that RTE cannot express the behavior.

**Payoff 2: extend an interface safely after narrowing it.**

```text
runFast : Unit -> Int
provider = {run=runFast, debug=true}
public = view[{run:Unit->Int}] provider
merge(public, {debug="custom debugger"})
```

`public` actually contains only `run`, so adding the new `debug` field is disjoint. Merely hiding the old field in its type would violate our exact-record invariant. RTE can perform the removal explicitly; our matching operation generates that computation.

**Payoff 3: preserve linking as ordinary evaluation.** Generated adapters and linkers are ordinary target programs. Our separate-compilation goal covers their behavior as well as that of the independently compiled components; no runtime module-matching primitive is added. This is our proposed compilation architecture, not a claim that RTE prevents separate compilation.

**Why this choice, and its cost:** exact records plus automatic width adaptation motivate physical restriction. Native query itself does not require coercions: RTE already combines `@` and subsumption. Another calculus could support broader subsumption with different record semantics. We pay for record reconstruction/function wrappers and additional correctness/coherence proofs; RTE's subtype steps introduce no corresponding adapter computation.

Generated coercions and coherence proofs are established techniques, not a novelty claim by themselves; see [Inheritance as Implicit Coercion](https://www.sciencedirect.com/science/article/pii/0890540191900557). The design work is their interaction with native environments, rows, abstract types, and SCE linking.

**Boundaries:** evaluate providers once before restriction, including dropped fields. Restriction preserves advertised type equalities; opaque sealing is separate. Restriction takes finite labels; an adapter can preserve an identical unknown remainder or discard it for a closed target interface. Selecting an arbitrary unknown subrow is outside this design. The manual target proofs cover adapter correctness and coherence.

## 6. Source SCE and its linking thesis

The source exposes the features above, explicit views/renaming, residual modules for partial links, and structural adapters generated at declared adaptation boundaries. `Rec(R)` is available exports; `Mod[I⇒O]` is a suspended module. Ordinary calls use exact argument types; `view` and linking request adaptation.

```text
Mod[I ⇒ O]  translates to  Rec(I) → Rec(O)
```

Sandboxed module bodies run in a native box containing exactly their imports; open modules retain their declared lexical capture. Type parameters stay in `Δ`. Compiled source `query` remains native `@`.

Use an ordinary closed linker function:

```text
LinkI = empty ▷ λp. λf.
  let i = adaptToI(p) in
  let o = f i in
  combineExports(p,o)

Compile(link P F) = LinkI Compile(P) Compile(F)
```

Curried application evaluates `P` and `F` in their original ambient environment. Generated linker bindings must not become visible to their native `query`. Export collisions require explicit resolution.

Partial linking captures supplied imports and returns a closure for the explicitly specified remaining row. Even supplying the final import leaves the body suspended: `complete` or `run` executes it. Reordering stages is a theorem for independent, already evaluated imports with fixed shared type witnesses.

One installer can preserve unknown remaining imports and exports:

```text
fn setLocale<R,O>(m: Mod[{locale:String}⊎R => O]) -> Mod[R => O] {
  provide[{locale:String};R] { locale = "en" } to m
}

// Instantiating R with {database:DB} leaves only that import.
// Instantiating R with {encoding:String} leaves only that import.
```

Here `R` excludes `locale`. Explicit completion runs the residual module after its remaining imports are supplied.

## 7. How this compares with ML modules

| Area | Assessment |
| --- | --- |
| Generic flat extension preserving unknown exports | Proposed row-polymorphic SCE advantage; ordinary ML signatures expose fixed components |
| Generic installers preserving unknown residual imports | Proposed SCE advantage; ML can stage dependencies with fixed signatures |
| Native lexical-environment reification and boxes | SCE has these directly; ML requires explicit environment representations |
| Automatic adaptation of record-valued functions | B inserts wrappers; ordinary ML module matching does not generate these adapters |
| Abstract type constructors and functor type identity | ML is stronger; these remain deferred |

This compares direct module-language support, not computability: ML can encode alternatives using nesting, wrappers, or other language features. OCaml already has first-class modules, dynamic provider selection, signature width matching, and object subtyping. Do not claim those as unique SCE advantages. See [OCaml signatures](https://ocaml.org/manual/5.4/modtypes.html), [first-class modules](https://ocaml.org/manual/5.4/firstclassmodules.html), and [objects](https://ocaml.org/docs/objects).

## 8. Paper contribution and proved guarantees

The paper's central contribution is:

> An expressive calculus of first-class modules in which linking is ordinary evaluation, with correct separate compilation and contextual laws for staged composition, interface adaptation, and abstract implementation replacement.

Present one coherent language, compilation architecture, and metatheory. For a replacement manuscript, its examples, rules, theorems, and implementation claims should describe the complete stronger system. For a follow-up, take linking as evaluation and the original separate-compilation result as established background; center the new contribution on open/abstract interfaces, coherent structural adaptation, contextual staging/commutation, and representation independence. Assess novelty against SCE and external related work: rows, records, and polymorphism are established ideas; the contribution concerns their integration with the linking architecture and its proved guarantees.

| Obligation | Proof direction |
| --- | --- |
| Native target safety | Relate runtime environments to `Δ;H`; handle type instantiation and existential scope |
| Source/target correctness | Typed elaboration and simulation, preserving results and divergence |
| Separate compilation | Combine the compile/link equation with behavioral correctness |
| Unknown-export preservation | The specified merge, extension, and linker preserve the untouched fields; no unrestricted free theorem is assumed |
| Interface/staging laws | Unique lookup, disjoint composition, and aligned type witnesses |
| Abstract replacement | Related hidden representations yield equivalent client observations |
| Adapter coherence | Direct/composed adapters agree and maintain exact record shapes |

Keep recursive functions/data and divergence reasoning. Do not claim normalization of the full SCE language.

## 9. Implementation and proof sequence

1. All selected target/source main theorems are mechanized in `LeanSce/Target/` and `LeanSce/Source/`, including contextual linking and abstraction. The repository build checks their proof dependencies for extra axioms or proof holes.
2. Keep specifications, examples, and implementation aligned with the proved rules. The selected language remains B. Legacy embedding is optional.
3. Add practical frontend inference gradually: ordinary local types and omitted type arguments, followed by polymorphic generalization and row constraints. Difficult higher-rank/impredicative uses may retain annotations. This is implementation work outside the present formal results.

The intended implementation pipeline is `convenient source → annotated SCE → explicit target`. Future inference must preserve evaluation timing and query visibility. Initially generalize functions/values rather than delaying arbitrary computations under `Λ`. Compile modules against fixed import contracts and record their export interfaces; a linker uses those interfaces without re-inferring bodies.

Higher-kinded type constructors are a later expressiveness goal: an abstract `F:Type→Type` needs more than `∀α:Type`. Also defer recursive module initialization, mutable references, and applicative/generative functor identity.

References: [SCE](context/SCE-paper.txt), [λE](context/LambdaE.txt), [FE](context/FE.txt), [RTE](context/record-types-everywhere.txt). Related baselines: [row theories](https://doi.org/10.1145/3290325), [extensible rows and ad-hoc polymorphism](https://doi.org/10.1145/3776662), [F-ing Modules](https://people.mpi-sws.org/~rossberg/f-ing/), and [environments with subtyping](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.34).

# λE^≤ — a sealing core calculus (λE binding + Eᵢ restriction)

λE^≤ is the minimum extension of λE (Tan & Oliveira, OOPSLA 2024) needed to make
**sealing** expressible: a compilation unit can hide part of its structure so clients
compile against a declared interface rather than the unit's full inferred type. The
sealing primitive `(e : A)` and everything that supports it (subtyping, disjointness,
casting) is ported from Eᵢ (Tan & Oliveira, ECOOP 2023). Nothing here is claimed as
novel except the combination; every ported rule is credited below. The calculus is
deliberately minimal — it exists to serve the module/linking work in `SCE/`, not as a
general-purpose calculus.

Scope of this version: the paper fragment `Int | ε | A → B | A & B | {l : A}`.
Left out (and why): unions and iso-recursive μ (casting rules for them exist in
*neither* paper — open design); fix (paper-backed via Eᵢ Appendix B, natural next
step); polymorphism/type components (λE §6.3 flags type-level substitution under
environment semantics as open; Eᵢ lists polymorphism as future work — sealing here is
**value-level only**).

Mechanization: `Syntax`, `Subtyping`, `Disjointness`, `Casting`, `Typing`,
`SmallStep`, `CastingLemmas`, `Lookup`, `Determinism`, `Progress`, `Preservation`,
`Sealing` (binary logical relation + fundamental lemma + sealing corollary),
`Examples`. Zero `sorry`, zero custom axioms — `sealing`, `fundamental`,
`cast_lr`, and `normalization` are axiom-free; determinism/preservation use
`propext` only.

---

## (a) Which of Eᵢ's complications are avoidable given de Bruijn indices?

**The ◦ abstraction mode is redundant.** In Eᵢ, `{e}◦ : {l : A} → B` exists for one
purpose: to model a conventional lambda whose parameter name is internal. Its rules
do exactly two things — `Typ-abs` extracts `{l : A}◦ = A` so the *type* is `A → B`
while the body addresses the argument through label `l`, and `Step-beta` wraps the
argument as `{l : A}⟨v⟩◦ = {l = v}` so the label lookup finds it. Both are
name-hiding devices. With de Bruijn binders the argument is addressed *positionally*
(`?.0`, since `lookup(Γ & A, 0) = A` — λE Typ-lam/Typ-proj), no label ever exists,
and the type is `A → B` directly. So λE^≤ has a single abstraction form and drops
the mode annotation, the `Aᵐ` extraction function, and the `A⟨v⟩ᵐ` value
constructor. (A second Eᵢ complication also dies: bidirectional typing. Eᵢ needs
checking mode to give annotations meaning; λE^≤ is fully syntax-directed — see (b)
note on where subtyping enters.)

**The `A ∗ Γ` premise of Typ-dmerge is NOT avoidable.** One might hope positional
lookup removes the ambiguity it guards. It removes the *lookup* ambiguity — `?.0` is
unambiguous, and `?.l` is guarded per-use by λE's containment judgment `l : A ∈ B`.
But it does not remove the *casting* ambiguity, because the sealing primitive
re-imports type-based selection: `(? : A)` reduces by casting the reified
environment. Eᵢ's own counterexample transplants directly: under context `Γ = Int`,
the merge `2 # {l = (? : Int)}` evaluates its right branch under environment
`v # 2`, and casting that environment at `Int` can select either the ambient `Int`
or the freshly merged `2` — two different results. Determinism of casting (Eᵢ
Lemma 6) needs the environment `v # v₁` to be *well-typed*, hence *consistent*, and
after `Step-merger` extends the environment the only source of that consistency is
`Γ ∗ A` via disjointness-implies-consistency (Eᵢ Lemma 4). So the premise stays.
The same reasoning adds `Γ ∗ A` to abstraction typing (beta extends the closure
environment with the cast argument).

## (b) Does merge stay dependent, and what side conditions does it need?

Merge stays dependent: `Γ ⊢ e₁ : A` and `Γ & A ⊢ e₂ : B` — dependent declarations
are the whole point (modules whose later fields use earlier ones), and the SCE
elaboration relies on it. But λE's premise-free `Typ-merge` is no longer tenable
once casting exists. λE happily types `1 # 2 : Int & Int`; sealing it — `(1 # 2 :
Int)` — would cast nondeterministically to `1` or `2`. Two conditions are added,
both ported from Eᵢ Typ-dmerge:

- `A ∗ B` — the branches must be disjoint, or the merged value itself is ambiguous
  under casting.
- `A ∗ Γ` — the left branch must be disjoint from the ambient context, or the
  extended runtime environment `v # v₁` is ambiguous under casting (see (a)).

Additionally, Eᵢ's *runtime* rule `Typ-mergev` (merge of values, premise: the
values are **consistent**, `v₁ ≈ v₂`, defined via casting) is ported. It is not
optional: values must be typeable under *any* context (value closedness, Eᵢ
Lemma 5 — the analogue of the mechanization's `value_weaken`, which preservation of
`Step-box`/`Step-boxv` depends on), and `Typ-dmerge`'s `A ∗ Γ` premise is
context-sensitive, so it cannot type closed value merges under arbitrary contexts.

Where subtyping enters (and nowhere else): (1) the sealing rule
`Γ ⊢ e : B → B <: A → Γ ⊢ (e : A) : A`; (2) two *runtime-only* slacks in closure
typing (input widening `C <: A`, body-result `B' <: B`) which are exactly what
preservation of arrow casting requires — this is our syntax-directed rendering of
Eᵢ's `C <: Aᵐ` premise plus checking-mode subsumption in Typ-abs, which Eᵢ itself
notes is runtime-only; (3) nothing else — application demands the exact argument
type, coercion is written explicitly as `(e₂ : A)`. There is no subsumption rule;
typing stays syntax-directed and inversion-friendly.

## (c) Which determinism route: typed selection or casting?

Both, because they answer different questions and neither subsumes the other.
λE^≤ keeps λE's *direct* selection `e.l` (`sel-mrgl`/`sel-mrgr`), nondeterministic
as a raw relation and tamed by the typing hypothesis through containment (λE
Lemma 4.1) — deliberately not Eᵢ's annotate-cast-project indirection, which the λE
paper explicitly criticizes. And it adds casting, also nondeterministic as a raw
relation (`Casting-mergevl`/`mergevr` overlap) and also tamed by a typing
hypothesis, through consistency (Eᵢ Lemma 6). Generalized determinism then carries
one typing premise (`ε ⊢ v : Γ`, `Γ ⊢ e : A`) that feeds both lemmas.

Implication for *elaborated* terms: the determinism/soundness theorems demand a
core typing derivation, but the witness available downstream is an elaboration
derivation. This is already the repo's pattern: `type_preservation`
(`SCE/Theories.lean`) converts `elabExp Γ es A ec` into `HasType ⟦Γ⟧ ec ⟦A⟧`, and
every determinism-style result for elaborated programs goes through it. The same
discipline transfers — with one new obligation: a future SCE→λE^≤ elaboration must
*establish the disjointness premises*. `edmrg` must carry `A ∗ Γ` and `A ∗ B`
(i.e., the source type system must check disjointness at merges), or elaborated
merges simply will not type in λE^≤ and the conversion theorem cannot exist.
Nothing about the proofs becomes harder; the side conditions just have to flow
from source typing.

## (d) The sealing property

Stated (and mechanized, in `Sealing.lean`) as a **binary, type-indexed logical
relation** — the binary generalization of λE's Fig. 4 semantic typing, defined by
structural recursion on the type:

- `v₁ ≈⟦Int⟧ v₂` — equal literals;
- `v₁ ≈⟦ε⟧ v₂` — both `ε` (degenerate; observations must be at `Int`);
- `≈⟦A & B⟧`, `≈⟦{l:A}⟧` — componentwise on merges / records;
- `v₁ ≈⟦A → B⟧ v₂` — **extensional**: both are closures, and for all arguments
  related at `A`, the *applications* co-evaluate to values related at `B`. (The
  clause is phrased at the application level so the semantics' internal
  argument-cast at the closure's annotation input is absorbed; runs are
  existentially quantified.)
- Open terms: `Γ ⊨ e₁ ≈ e₂ : A` quantifies over environments related at `Γ` —
  and because contexts *are* types, `≈⟦Γ⟧` itself is the environment relation; no
  separate context clauses are needed.

Results:
- **Fundamental lemma**: `Γ ⊢ e : A → Γ ⊨ e ≈ e : A`. (Termination of well-typed
  λE^≤ programs falls out, exactly as in λE §4.2.)
- **Casting respects the relation**: `v₁ ≈⟦B⟧ v₂ → B <: A → v₁ ↪_A v₁' →
  v₂ ↪_A v₂' → v₁' ≈⟦A⟧ v₂'` — the semantic content of sealing: the cast is a
  coercion between the relations. (Proof by induction on the subtyping derivation;
  the arrow case uses cast transitivity + cast determinism to reconcile resealing.)
- **Sealing corollary**: for providers `⊢ vᵢ : Bᵢ` with `Bᵢ <: A`, sealed as
  `vᵢ ↪_A vᵢ'`: if `v₁' ≈⟦A⟧ v₂'`, then for every client `A ⊢ e : Int`, the
  programs `v₁' ▷ e` and `v₂' ▷ e` evaluate to the **same integer literal**.

Precision about what this is and is not:
- It is **equality at base-type observations**, and a **logical relation (not
  syntactic equality) at arrow types** — extensional: the providers' functions may
  be different closures, they need only agree observably at the sealed type.
- It holds for **values/termination behavior only**. The calculus is pure and (by
  the fundamental lemma) strongly normalizing, so there are no effects or traces to
  speak of; nothing is claimed about an effectful extension (that would require a
  ⊤⊤-closed/biorthogonal relation and is **not established** here).
- It is **not representation independence**. There are no type components,
  existentials, or polymorphism; the client can name every type it depends on.
  What is hidden is *width* (components not named in `A`) and *behavior beyond the
  seal at depth* (record fields and function results are resealed recursively).
  Width-hiding is in fact almost trivial in this calculus — the cast **erases**
  discarded components, so the sealed value literally does not contain them
  ("erasure sealing"); the genuine content of the theorem is extensionality at
  arrows and depth.

## (e) What breaks in λE's existing metatheory?

| result | verdict |
|---|---|
| **determinism** | needs a casting premise. Determinism of casting (Eᵢ L6, typing-hypothesis'd via consistency) joins determinism of selection (λE L4.1). Statement shape unchanged. *Mechanized.* |
| **progress** | needs a casting premise: progress of casting (Eᵢ L9) for the new `(v : A)` redex and the argument-cast in beta. Otherwise same structure. *Mechanized.* |
| **preservation** | needs the full casting lemma layer: transitivity (L10), consistency-after-casting (L11), preservation of casting (L12), disjointness⇒consistency (L4), value closedness (L5). Structure survives; the lemma layer is the cost. *Mechanized.* |
| **normalization** (λE Fig. 4 predicate) | statement survives; the proof needs one new semantic lemma — casting preserves the predicate (semantic subsumption). **No precedent**: no TDOS merge calculus has a mechanized normalization proof (Eᵢ's termination is unknown — λE paper Table 1). Here it *falls out of the sealing logical relation*, which is its unary shadow. *Mechanized (via `Sealing.lean`).* |
| **big-step equivalence** | needs cast premises in `Bstep-app` (argument cast + result reseal) and a new `Bstep-anno`; λE Lemma 4.18 (global-as-local) and the proof structure are unaffected. Believed routine. *Not mechanized.* |
| **STLC conservativity** | the *statement* is restored relative to Eᵢ (where it is unknown). The proof needs `S(v,e,k)` extended to annotated closures, the lemma "casting an STLC-image value at its own type is the identity", and the simulation becomes lock-step *up to administrative cast steps* (beta now emits a result annotation). Believed provable, genuinely new work. *Not mechanized.* |
| **SECD machine** | extension is systematic — a `Cast(A)` instruction implementing `↪_A`, `(e : A)` compiles to `⟦e⟧, Cast(A)`, beta's compilation casts the argument — but the machine becomes **type-passing**: types are runtime data. This makes the runtime cost of sealing visible (a cast traverses and rebuilds the sealed prefix). Correctness proof expected routine given big-step. *Not mechanized.* |

## (f) Full rule set with provenance

Provenance key: **(i)** unchanged from λE · **(ii)** ported from Eᵢ · **(iii)** new.

### Syntax

```
Types A, B, Γ ::= Int | ε | A → B | A & B | {l : A}          (i) — Eᵢ's Top ≡ λE's ε
Exprs e ::= ? | e.n | i | ε | e₁ ▷ e₂ | e₁ e₂ | e₁ # e₂       (i)
          | {l = e} | e.l                                     (i)
          | λ(A→B). e | ⟨v, λ(A→B). e⟩                        (iii) — λE's λA.e/⟨v,λA.e⟩
                                                                     with the codomain
                                                                     annotation forced (below)
          | (e : A)                                           (ii) — the sealing primitive
Values v ::= i | ε | ⟨v, λ(A→B). e⟩ | v₁ # v₂ | {l = v}       (i, closure modified)
```

**Why annotated lambdas are forced (the one deviation from design constraint 1).**
Sealing at an arrow type is inherently extensional: `Casting-arrow` must check
`B <: D` and *rewrite* the closure's return annotation, and beta must reseal every
call's result (`… ▷ (e : B)`). A substitution-free small-step semantics can only do
that if the codomain is materialized in the value: with λE's bare `⟨v, λA. e⟩`
there is nothing to check, nothing to rewrite, and the cast result cannot
re-synthesize the target type (there is no subsumption rule to absorb the gap), so
preservation of casting fails. Every escape hatch (typed casting rules; forbidding
arrows under seals; value-level subsumption) either breaks the
consistency/typing stratification, kills the module use-case, or destroys
syntax-directedness. Hence `lam A B e` / `clos v A B e`.

### Subtyping `A <: B` — all (ii), Eᵢ Fig. 1 verbatim (ε plays Top)

```
S-z:    Int <: Int
S-top:  A <: ε
S-arr:  B₁ <: A₁ → A₂ <: B₂ → A₁ → A₂ <: B₁ → B₂
S-andl: A₁ <: A₃ → A₁ & A₂ <: A₃
S-andr: A₂ <: A₃ → A₁ & A₂ <: A₃
S-and:  A₁ <: A₂ → A₁ <: A₃ → A₁ <: A₂ & A₃
S-rcd:  A <: B → {l : A} <: {l : B}
```

### Ordinary, top-like, value generator — all (ii)

`Ordinary A` (casting variant: not ε, not &): `Int`, `A → B`, `{l : A}`.
`⌉A⌈`: `⌉ε⌈`; `⌉A&B⌈` if both; `⌉A→B⌈` if `⌉B⌈`; `⌉{l:B}⌈` if `⌉B⌈`.
Generator: `ε↑ = ε`, `(A&B)↑ = A↑ # B↑`, `{l:A}↑ = {l = A↑}`,
`(C→D)↑ = ⟨ε, λ(C→D). D↑⟩`, and (total-function junk) `Int↑ = ε` — every lemma
about `A↑` is guarded by `⌉A⌈`, so the junk value is never observable.

### Disjointness `A ∗ B` — (ii), Eᵢ Def. 1 / Appendix A.1

Taken *algorithmically* as the definition: `A ∗ B := ¬(A ⊓ B)` where `⊓` is the
COST (Common Ordinary Super Type) relation:

```
Cost-int:   Int ⊓ Int
Cost-andl:  A ⊓ C → A & B ⊓ C          Cost-randl: A ⊓ B → A ⊓ B & C
Cost-andr:  B ⊓ C → A & B ⊓ C          Cost-randr: A ⊓ C → A ⊓ B & C
Cost-arr:   B ⊓ D → A → B ⊓ C → D
Cost-rcd:   A ⊓ B → {l : A} ⊓ {l : B}
```

**It ports cleanly**: the λE^≤ type grammar is exactly Eᵢ's (given ε ≡ Top), so
Def. 1 / A.1 transfer without change. (The spec form — "no common ordinary
supertype" — and the equivalence Eᵢ Thm 22 are not needed by any proof here; we
work with COST directly. `Cost-arr` ignoring input types is load-bearing: it is
what makes `(A→C) ∗ (B→D)` ↔ `C ∗ D` (Eᵢ L2.5) hold, which the closure cases of
consistency depend on.) Note the fragment *without* unions/μ is essential to "ports
cleanly": extending COST to unions or recursive types is exactly where it stops
being a verbatim port.

### Casting `v ↪_A v'` — all (ii), Eᵢ Fig. 3, arrow rules adapted to de Bruijn closures

```
C-int:     i ↪_Int i
C-top:     v ↪_ε ε
C-arrow:   ¬⌉D⌈ → C <: A → B <: D →
           ⟨v, λ(A→B). e⟩ ↪_{C→D} ⟨v, λ(A→D). e⟩
C-arrowtl: ⌉D⌈ → C <: A → B <: D →
           ⟨v, λ(A→B). e⟩ ↪_{C→D} (C→D)↑
C-mrgl:    Ordinary A → v₁ ↪_A v₁' → v₁ # v₂ ↪_A v₁'
C-mrgr:    Ordinary A → v₂ ↪_A v₂' → v₁ # v₂ ↪_A v₂'
C-and:     v ↪_A v₁ → v ↪_B v₂ → v ↪_{A&B} v₁ # v₂
C-rcd:     v ↪_A v' → {l = v} ↪_{l:A} {l = v'}
```

Casting is deliberately **typing-free** — its premises mention only the closure's
own annotations, never a typing derivation. (A "typed cast" would collapse the
stratification between `Consistent` — defined from casting — and `HasType` — whose
`tmergev` rule consumes consistency.) Top-like machinery is unavoidable given
S-top: `(A→ε) ∗ (B→ε)` holds (Cost-arr needs `ε ⊓ ε`, and no COST rule produces
it), so a merge of two ε-codomain closures is well-typed, and casting it at `C→ε`
would fire both C-mrgl and C-mrgr with different results — C-arrowtl collapses
both to the canonical generated value.

`Consistent v₁ v₂ := ∀ A w₁ w₂, v₁ ↪_A w₁ → v₂ ↪_A w₂ → w₁ = w₂` — (ii), Eᵢ Def. 3.

### Typing `Γ ⊢ e : A` — provenance per rule

```
T-query:  Γ ⊢ ? : Γ                                                  (i)
T-int:    Γ ⊢ i : Int                                                (i)
T-unit:   Γ ⊢ ε : ε                                                  (i)
T-app:    Γ ⊢ e₁ : A → B → Γ ⊢ e₂ : A → Γ ⊢ e₁ e₂ : B               (i)  exact arg type
T-box:    Γ ⊢ e₁ : Γ₁ → Γ₁ ⊢ e₂ : A → Γ ⊢ e₁ ▷ e₂ : A               (i)
T-proj:   Γ ⊢ e : B → lookup(B, n) = A → Γ ⊢ e.n : A                (i)
T-rcd:    Γ ⊢ e : A → Γ ⊢ {l = e} : {l : A}                          (i)
T-rproj:  Γ ⊢ e : B → l : A ∈ B → Γ ⊢ e.l : A                        (i)  λE containment
T-mrg:    Γ ⊢ e₁ : A → Γ & A ⊢ e₂ : B → A ∗ Γ → A ∗ B
          → Γ ⊢ e₁ # e₂ : A & B                                      (i) + (ii) premises
T-mrgv:   ε ⊢ v₁ : A → ε ⊢ v₂ : B → v₁ ≈ v₂
          → Γ ⊢ v₁ # v₂ : A & B         (values only)                (ii)
T-lam:    Γ ∗ A → Γ & A ⊢ e : B → Γ ⊢ λ(A→B). e : A → B              (i) + (ii) premise
T-clos:   Value v → ε ⊢ v : Γ₁ → Γ₁ ∗ A → Γ₁ & A ⊢ e : B'
          → B' <: B → C <: A → Γ ⊢ ⟨v, λ(A→B). e⟩ : C → B            (i) + (ii) slacks
T-anno:   Γ ⊢ e : B → B <: A → Γ ⊢ (e : A) : A                       (ii)  THE SEALING RULE
```

Flagged uncertainty (u1): `T-clos`'s double slack is our syntax-directed rendering
of Eᵢ's `Typ-abs` (`C <: Aᵐ` premise) + checking-mode body subsumption. Believed
equivalent on the common fragment; equivalence not proved. A consequence: closure
typing is not functional (a closure inhabits many arrow types) — harmless for the
theorems (all ∀-quantified over a derivation), but inversion lemmas are stated
existentially.

### Small-step `v ⊢ e ↪ e'` — congruence style (as in the mechanization; the paper's frames are equivalent)

```
S-query:  v ⊢ ? ↪ v                                                  (i)
S-proj:   v ⊢ v₁.n ↪ lookupv(v₁, n)                                  (i)
S-mrgr:   v # v₁ ⊢ e₂ ↪ e₂' → v ⊢ v₁ # e₂ ↪ v₁ # e₂'                 (i)
S-box:    v₁ ⊢ e ↪ e' → v ⊢ v₁ ▷ e ↪ v₁ ▷ e'                          (i)
S-boxv:   v ⊢ v₁ ▷ v₂ ↪ v₂                                            (i)
S-clos:   v ⊢ λ(A→B). e ↪ ⟨v, λ(A→B). e⟩                              (i)  carries B now
S-beta:   v₂ ↪_A v₂' →
          v ⊢ ⟨v₁, λ(A→B). e⟩ v₂ ↪ (v₁ # v₂') ▷ (e : B)              (iii) — λE shape,
                                                       Eᵢ cast premise + result reseal
S-sel:    v₁.l ⇝ v₂ → v ⊢ v₁.l ↪ v₂                                   (i)  sel-mrgl/mrgr
S-annov:  v₁ ↪_A v' → v ⊢ (v₁ : A) ↪ v'                               (ii)
+ congruence rules for each frame position, incl. the new (e : A)     (i) + (ii)
```

`S-beta`'s cast is what makes casting and de Bruijn indices *compatible*: the body
addresses the argument at type `A` (positionally and by label), and `C-and`
rebuilds the argument's merge structure to follow `A`'s intersection structure, so
runtime `lookupv` agrees with static `lookup`. Without the cast, an argument passed
at a subtype would have the wrong shape and positional lookup would be unsound.

### Not included (deliberately)

Type components / existentials / polymorphism (see header); unions and μ (no
casting rules exist in either paper); fix (Eᵢ App. B makes it a mechanical
extension); BCD/distributive subtyping (Eᵢ future work; would break the simple
COST story); big-step semantics, STLC conservativity, and the SECD machine for
λE^≤ (statements and expected proof burdens are in (e); out of the minimal
correctness scope).

### Relation to SCE

SCE keeps elaborating to Core (λE) unchanged; λE^≤ is a sibling target — and the
retargeting is now **mechanized** for the module/linking fragment
(`Elaboration.lean`: `elabSeal`, `seal_type_preservation`). It covers
mstruct/mfunctor/mclos/mapp/mlink/mlinkn/letb/openm/nmrg, records, boxes,
lambdas, closures, and dependent merges; unions/fix/μ have no rules (no casting
exists for them in either paper). As predicted in (c): every context-extending
rule carries the `Disj` premises on the `sealTyp` images — the source type
system must check disjointness. Two findings from doing it:

- **The bind-once combinators are dead and sealing replaces them.** Core's
  `nmrgCore`/`linkedCore` use the self-application idiom `(λ⟦Γ⟧. …) ?`, which is
  untypeable in λE^≤ — `tlam` demands `Γ ∗ Γ`, false for any non-top-like `Γ`.
  Instead `(? : Γ)` *restricts the extended environment back to the ambient one*,
  so the non-capturing merge is `e₁ # ((? : Γ) ▷ e₂)` and the link combinators
  are merges of sealed boxes. The construct λE needed combinator machinery for
  is a one-liner once restriction is first-class.
- **n-ary linking needs a disjointness-enriched interface judgment** (`WireOk`):
  SCE's `LinkOk` carries only the import lookups; λE^≤ additionally needs each
  accumulated import package disjoint from the ambient context and from the next
  import (`wireArgSeal_typed`).

Semantic preservation is now **mechanized** too (`Correctness.lean`):
`seal_semantic_preservation` simulates source big-step evaluation by target
`MStep` runs, with values related by `EVal` — *elaboration up to top-like
collapse*.  The syntactic statement used for the Core target is false here: beta
casts the argument and reseals the result, and casting a closure at a top-like
arrow collapses it to the generator; `EVal` mirrors value elaboration, stores
EVal-related closure environments, and admits the generator at any top-like type.
Its key lemma is `eval_cast_self` (casting at a value's own type preserves the
relation); the restriction combinators are handled by `eval_env_restrict`
(cast-of-extended-env = self-cast of the ambient part, via `cast_merge_eq_l` —
the semantic payoff of the `A ∗ Γ` premise).  Corollaries:
`seal_whole_program_correctness`, `seal_separate_compilation` (+`_closed`, `_n`,
`_n_closed`), and `mstep_value_determinism`.

Bind-once (linearized) linking is mechanized in `Linearization.lean`.  Core's
bind-once spelling is untypeable in λE^≤ (binding the module value puts `Γ₁` in
the context, and the body's merge then needs `Γ₁ ∗ (Γ & Γ₁)`, which fails); the
working spelling uses Eᵢ's fresh-label wrap — bind `{x = m}` so the bound copy has
type `{x : Γ₁}` — with freshness premises `¬Lin x ⟦Γ⟧`, `¬Lin x ⟦Γ₁⟧` as the price
of evaluate-once under a sealing discipline (`linkedSealLin_typed`,
`seal_separate_compilation_lin`, `_closed`).  Coherence with the evaluate-twice
seal spelling is `linearization_coherent_seal`, stated at the EVal level — Core's
syntactic-equality coherence is provably the wrong statement here (asymmetric
top-like collapse).  The non-capturing merge needs no linearized variant at all:
`e₁ # ((? : Γ) ▷ e₂)` already evaluates each operand once.  The n-ary bind-once
combinator is the same construction iterated per import (projections from the
bound value under re-sealed environments) and is left as mechanical.

Still open on this path: a source-level signature-ascription construct
elaborating to `(e : A)` (one rule + one BStep case), and fix/unions/μ as before.

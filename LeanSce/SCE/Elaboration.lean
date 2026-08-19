import LeanSce.SCE.Syntax
import LeanSce.Core.Syntax


open SCE

/-!
## Composition combinators: the linearized (bind‑once) spelling

`,,` (`nmrg`), `link` and `linkall` each elaborate to a *composition term* that
combines the elaborations of their operands.  The rules below emit the
**linearized** term — the one the implementation (`Elab.link_step`/`nmrg_core`
in `lib/sce/elab.ml`) emits and the toolchain linker (`lib/sepcomp.ml`) applies
when composing compiled units.  An earlier version of this mechanization emitted
a different, *boxed* term; the concrete diff, and why it was replaced, is at the
end of this file.

Notation: `?` is `query`, `?.n` is `proj query n`, `,,` is the dependent merge
`mrg`, `box ρ in ε` is `Exp.box ρ ε`, `{ℓ = ε}` is `lrec ℓ ε`, `⟦·⟧` is `elabTyp`.

    Γ ⊢ e₁ ⇒ A ⤳ ε₁     Γ ⊢ e₂ ⇒ B ⤳ ε₂
    ─────────────────────────────────────────────────────  E‑NMrg
    Γ ⊢ e₁ ,, e₂ ⇒ A & B  ⤳  (λ⟦A⟧. λ⟦B⟧. ?.1 ,, ?.1) ε₁ ε₂

    Γ ⊢ e₁ ⇒ Γ₁ ⤳ ε₁     Γ ⊢ e₂ ⇒ ⟨D ⇛ B⟩ ⤳ ε₂     Γ₁ ⊨ D
    ─────────────────────────────────────────────────────────────  E‑Link (D = {ℓ:A}), E‑LinkAll
    Γ ⊢ link e₁ e₂ ⇒ Γ₁ & B  ⤳  (λ⟦Γ₁⟧. λ⟦D⟧→⟦B⟧. ?.1 ,, (?.1 (wire₀ ⟦D⟧))) ε₁ ε₂

        wire_k {ℓ:A}       = {ℓ = ?.k.ℓ}
        wire_k (D & {ℓ:A}) = wire_k D ,, {ℓ = ?.(k+1).ℓ}

Every operand is *bound once* on an application spine.  Inside the double lambda,
on the left of the merge `?.1` is the provider; on the right — one slot deeper,
under the freshly merged provider copy — `?.1` is the functor and `?.0` the
provider, which is what the wire projects from.  The wire never mentions `ε₁`;
it projects out of the value the spine bound.  `link` is literally the
single‑import instance of `linkall`.  Typing and evaluation of these terms are
`linkedCore_typed`/`nmrgCore_typed` and `linkStep_eval`/`nmrgCore_eval`/`wire_eval`
in `Theories.lean`.
-/

/-- `λ(x:a). λ(y:b). ?.1 ,, ?.1` — the bind‑once non‑dependent merge step
(OCaml `nmrg_step`).  On the left of the merge `?.1` is `x`; on the right, one
slot deeper under the merged left value, `?.1` is `y`. -/
def nmrgStep (a b : Core.Typ) : Core.Exp :=
  .lam a (.lam b (.mrg (.proj .query 1) (.proj .query 1)))

/-- `(nmrgStep a b) ε₁ ε₂` — the linearized elaboration of `e₁ ,, e₂`
(OCaml `nmrg_core`); also the toolchain's leaf link step. -/
def nmrgCore (a b : Core.Typ) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  .app (.app (nmrgStep a b) ce₁) ce₂

/-- The linearized wire (OCaml `wire`): the import package for the (elaborated)
interface `D`, built by *projection from the bound provider* at de Bruijn index
`shift`.  Each nested dependent merge shifts the provider one slot deeper, hence
`shift + 1` on the right.  Only the labels of `D` matter. -/
def wire (shift : Nat) : Core.Typ → Core.Exp
  | .rcd l _ => .lrec l (.rproj (.proj .query shift) l)
  | .and D (.rcd l _) =>
    .mrg (wire shift D) (.lrec l (.rproj (.proj .query (shift + 1)) l))
  | _ => .unit

/-- `λ(p:g1). λ(f:D→B). ?.1 ,, (?.1 (wire₀ D))` — the bind‑once link step
(OCaml `link_step`).  The provider is bound once; every import label projects
from that binding.  The artifact linker applies this same step term. -/
def linkStep (g1 D B : Core.Typ) : Core.Exp :=
  .lam g1 (.lam (.arr D B) (.mrg (.proj .query 1) (.app (.proj .query 1) (wire 0 D))))

/-- `(linkStep g1 D B) ε₁ ε₂` — the linearized elaboration of `link`/`linkall`
(OCaml `linked_core`); `D := {ℓ:A}` is the binary `link`. -/
def linkedCore (g1 D B : Core.Typ) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  .app (.app (linkStep g1 D B) ce₁) ce₂

mutual
@[simp]
def elabTyp : Typ → Core.Typ
  | Typ.int        => Core.Typ.int
  | Typ.top        => Core.Typ.top
  | Typ.arr t1 t2  => Core.Typ.arr (elabTyp t1) (elabTyp t2)
  | Typ.and t1 t2  => Core.Typ.and (elabTyp t1) (elabTyp t2)
  | Typ.or t1 t2   => Core.Typ.or (elabTyp t1) (elabTyp t2)
  | Typ.rcd str t  => Core.Typ.rcd str (elabTyp t)
  | Typ.sig mty    => elabModTyp mty
  | Typ.var n      => Core.Typ.var n
  | Typ.mu t       => Core.Typ.mu (elabTyp t)
  -- brands have no Core counterpart (λE has no type abstraction); inert junk
  | Typ.brand _    => Core.Typ.top

@[simp]
def elabModTyp : ModTyp → Core.Typ
  | ModTyp.TyIntf t1      => elabTyp t1
  | ModTyp.TyArrM t1 mty  => Core.Typ.arr (elabTyp t1) (elabModTyp mty)
end

mutual
-- elaboration commutes with mu-unfolding substitution
theorem elab_substTyp (d : Nat) (S : Typ)
    : (T : Typ) → elabTyp (substTyp d S T) = Core.substTyp d (elabTyp S) (elabTyp T)
  | .int => rfl
  | .top => rfl
  | .arr A B => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp d S A, elab_substTyp d S B]
  | .and A B => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp d S A, elab_substTyp d S B]
  | .or A B => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp d S A, elab_substTyp d S B]
  | .rcd l A => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp d S A]
  | .sig mt => by
    simp [substTyp, elabTyp, elab_substModTyp d S mt]
  | .var n => by
    by_cases h : n = d <;> simp [substTyp, elabTyp, Core.substTyp, h]
  | .mu T => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp (d + 1) S T]
  | .brand n => by simp [substTyp, elabTyp, Core.substTyp]

theorem elab_substModTyp (d : Nat) (S : Typ)
    : (mt : ModTyp) → elabModTyp (substModTyp d S mt) = Core.substTyp d (elabTyp S) (elabModTyp mt)
  | .TyIntf T => by
    simp [substModTyp, elabModTyp, elab_substTyp d S T]
  | .TyArrM T mt => by
    simp [substModTyp, elabModTyp, Core.substTyp, elab_substTyp d S T, elab_substModTyp d S mt]
end

abbrev TyCtx := Typ

inductive elabExp : TyCtx → Exp → Typ → Core.Exp → Prop
  | equery {ctx}
    : elabExp ctx Exp.query ctx Core.Exp.query
  | elit (ctx : Typ) (n : Nat)
    : elabExp ctx (Exp.lit n) Typ.int (Core.Exp.lit n)
  | eunit (ctx : Typ)
    : elabExp ctx Exp.unit Typ.top Core.Exp.unit
  | eapp (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 (Typ.arr A B) ce1
    → elabExp ctx se2 A ce2
    → elabExp ctx (Exp.app se1 se2) B (Core.Exp.app ce1 ce2)
  | eproj (ctx A B : Typ) (se : Exp) (ce : Core.Exp) (i : Nat)
    : elabExp ctx se A ce
    → SLookup A i B
    → elabExp ctx (Exp.proj se i) B (Core.Exp.proj ce i)
  | ebox (ctx ctx' A : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 ctx' ce1
    → elabExp ctx' se2 A ce2
    → elabExp ctx (Exp.box se1 se2) A (Core.Exp.box ce1 ce2)
  | edmrg (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.mrg se1 se2) (Typ.and A B) (Core.Exp.mrg ce1 ce2)
  /-
    Γ ⊢ eˢ₁ : A ⤳ eᶜ₁
    Γ ⊢ eˢ₂ : B ⤳ eᶜ₂
    ──────────────────────────────────────────────────────────
    Γ ⊢ eˢ₁ ,, eˢ₂ : A & B ⤳ (λ⟦A⟧. λ⟦B⟧. ?.1 ,, ?.1) eᶜ₁ eᶜ₂
  -/
  | enmrg (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp ctx se2 B ce2
    → elabExp ctx (Exp.nmrg se1 se2) (Typ.and A B)
        (nmrgCore (elabTyp A) (elabTyp B) ce1 ce2)
  | elam (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp (Typ.and ctx A) se B ce
    → elabExp ctx (Exp.lam A se) (Typ.arr A B) (Core.Exp.lam (elabTyp A) ce)
  | erproj (ctx A B : Typ) (se : Exp) (ce : Core.Exp) (l : String) :
      elabExp ctx se B ce
      → SRLookup B l A
      → elabExp ctx (Exp.rproj se l) A (Core.Exp.rproj ce l)
  | eclos (ctx ctx' A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : SCE.Value se1
    → elabExp Typ.top se1 ctx' ce1
    → elabExp (Typ.and ctx' A) se2 B ce2
    → elabExp ctx (Exp.clos se1 A se2) (Typ.arr A B) (Core.Exp.clos ce1 (elabTyp A) ce2)
  | elrec (ctx A : Typ) (se : Exp) (ce : Core.Exp) (l : String)
    : elabExp ctx se A ce
    → elabExp ctx (Exp.lrec l se) (Typ.rcd l A) (Core.Exp.lrec l ce)
  | letb (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.letb se1 A se2) B
        (Core.Exp.app (Core.Exp.lam (elabTyp A) ce2) ce1)
  | openm (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp) (l : String)
    : elabExp ctx se1 (Typ.rcd l A) ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.openm se1 se2) B
        (Core.Exp.app (Core.Exp.lam (elabTyp A) ce2) (Core.Exp.rproj ce1 l))
  | mstruct (ctx ctxInner B : Typ) (sb : Sandbox) (se : Exp) (ce envCore : Core.Exp)
    : (sb = Sandbox.sandboxed → ctxInner = Typ.top)
    → (sb = Sandbox.open_     → ctxInner = ctx)
    → elabExp ctxInner se B ce
    → elabExp ctx (Exp.mstruct sb se) B
        (Core.Exp.box
          (match sb with
            | Sandbox.sandboxed => Core.Exp.unit
            | Sandbox.open_     => Core.Exp.query)
          ce)
  | mfunctor (ctx ctxInner A B : Typ) (sb : Sandbox) (se : Exp) (ce : Core.Exp)
    : (sb = Sandbox.sandboxed → ctxInner = Typ.and Typ.top A)
    → (sb = Sandbox.open_     → ctxInner = Typ.and ctx A)
    → elabExp ctxInner se B ce
    → elabExp ctx (Exp.mfunctor sb A se) (Typ.sig (ModTyp.TyArrM A (ModTyp.TyIntf B)))
        (match sb with
          | Sandbox.sandboxed => Core.Exp.box Core.Exp.unit (Core.Exp.lam (elabTyp A) ce)
          | Sandbox.open_     => Core.Exp.lam (elabTyp A) ce)
  | mclos (ctx ctx' A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : SCE.Value se1
    → elabExp Typ.top se1 ctx' ce1
    → elabExp (Typ.and ctx' A) se2 B ce2
    → elabExp ctx (Exp.mclos se1 A se2) (Typ.sig (ModTyp.TyArrM A (ModTyp.TyIntf B)))
        (Core.Exp.clos ce1 (elabTyp A) ce2)
  | mapp (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 (Typ.sig (ModTyp.TyArrM A (ModTyp.TyIntf B))) ce1
    → elabExp ctx se2 A ce2
    → elabExp ctx (Exp.mapp se1 se2) B (Core.Exp.app ce1 ce2)
  | mlink (ctx Γ₁ A B : Typ) (l : String)
      (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 Γ₁ ce1
    → elabExp ctx se2 (Typ.sig (ModTyp.TyArrM (Typ.rcd l A) (ModTyp.TyIntf B))) ce2
    → SRLookup Γ₁ l A
    → elabExp ctx (Exp.mlink se1 se2) (Typ.and Γ₁ B)
        (linkedCore (elabTyp Γ₁) (elabTyp (Typ.rcd l A)) (elabTyp B) ce1 ce2)
  | mlinkn (ctx Γ₁ D B : Typ)
      (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 Γ₁ ce1
    → elabExp ctx se2 (Typ.sig (ModTyp.TyArrM D (ModTyp.TyIntf B))) ce2
    → LinkOk Γ₁ D
    → elabExp ctx (Exp.mlinkn se1 se2) (Typ.and Γ₁ B)
        (linkedCore (elabTyp Γ₁) (elabTyp D) (elabTyp B) ce1 ce2)
  | einl (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp ctx se A ce
    → elabExp ctx (Exp.inl B se) (Typ.or A B) (Core.Exp.inl (elabTyp B) ce)
  | einr (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp ctx se B ce
    → elabExp ctx (Exp.inr A se) (Typ.or A B) (Core.Exp.inr (elabTyp A) ce)
  | ecase (ctx A B C : Typ) (se se1 se2 : Exp) (ce ce1 ce2 : Core.Exp)
    : elabExp ctx se (Typ.or A B) ce
    → elabExp (Typ.and ctx A) se1 C ce1
    → elabExp (Typ.and ctx B) se2 C ce2
    → elabExp ctx (Exp.case se se1 se2) C (Core.Exp.case ce ce1 ce2)
  | eflam (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp (Typ.and (Typ.and ctx (Typ.arr A B)) A) se B ce
    → elabExp ctx (Exp.flam A B se) (Typ.arr A B)
        (Core.Exp.flam (elabTyp A) (elabTyp B) ce)
  | efclos (ctx ctx' A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : SCE.Value se1
    → elabExp Typ.top se1 ctx' ce1
    → elabExp (Typ.and (Typ.and ctx' (Typ.arr A B)) A) se2 B ce2
    → elabExp ctx (Exp.fclos se1 A B se2) (Typ.arr A B)
        (Core.Exp.fclos ce1 (elabTyp A) (elabTyp B) ce2)
  | efold (ctx T : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp ctx se (substTyp 0 (Typ.mu T) T) ce
    → elabExp ctx (Exp.fold T se) (Typ.mu T) (Core.Exp.fold (elabTyp T) ce)
  -- result type is a variable guarded by an equation so that dependent
  -- elimination (cases at a concrete type) does not get stuck on substTyp
  | eunfold (ctx T A : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp ctx se (Typ.mu T) ce
    → A = substTyp 0 (Typ.mu T) T
    → elabExp ctx (Exp.unfold se) A (Core.Exp.unfold ce)

/-!
## Appendix: the previous (boxed) elaboration, and the concrete diff

Before the linearized rules above, `enmrg`/`mlink`/`mlinkn` emitted the
following *boxed* terms.  Premises were identical; only the emitted term differs.

    -- OLD (boxed)
    def nmrgCore (ctx : Core.Typ) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
      .app (.lam ctx (.mrg (.box (.proj .query 0) ce₁)
                           (.box (.proj .query 1) ce₂)))
           .query

    def linkedCore (ctx : Core.Typ) (l : String) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
      .app (.lam ctx (.mrg (.box (.proj .query 0) ce₁)                    -- ε₁, evaluation #1
                           (.box (.proj .query 1)
                             (.app ce₂ (.lrec l (.rproj ce₁ l))))))       -- ε₁ again, evaluation #2
           .query

    def wireArg (ctx : Core.Typ) (ce₁ : Core.Exp) : SCE.Typ → Core.Exp
      | .rcd l _          => .lrec l (.rproj ce₁ l)                       -- ε₁ spliced per import
      | .and D (.rcd l _) => nmrgCore ctx (wireArg ctx ce₁ D) (.lrec l (.rproj ce₁ l))
      | _                 => .unit

    def linkedCoreN (ctx : Core.Typ) (D : SCE.Typ) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
      .app (.lam ctx (.mrg (.box (.proj .query 0) ce₁)                    -- ε₁, evaluation #1
                           (.box (.proj .query 1)
                             (.app ce₂ (wireArg ctx ce₁ D)))))            -- ε₁, evaluations #2..#n+1
           .query

    | enmrg  … → elabExp ctx (nmrg se1 se2)   (and A B)  (nmrgCore   (elabTyp ctx) ce1 ce2)
    | mlink  … → elabExp ctx (mlink se1 se2)  (and Γ₁ B) (linkedCore (elabTyp ctx) l ce1 ce2)
    | mlinkn … → elabExp ctx (mlinkn se1 se2) (and Γ₁ B) (linkedCoreN (elabTyp ctx) D ce1 ce2)

    -- NEW (linearized; the definitions at the top of this file)
    | enmrg  … → … (nmrgCore   (elabTyp A)  (elabTyp B) ce1 ce2)
    | mlink  … → … (linkedCore (elabTyp Γ₁) (elabTyp (rcd l A)) (elabTyp B) ce1 ce2)
    | mlinkn … → … (linkedCore (elabTyp Γ₁) (elabTyp D)         (elabTyp B) ce1 ce2)

In rule notation:

    OLD  e₁ ,, e₂      ⤳ (λ⟦Γ⟧. (box ?.0 in ε₁) ,, (box ?.1 in ε₂)) ?
    NEW  e₁ ,, e₂      ⤳ (λ⟦A⟧. λ⟦B⟧. ?.1 ,, ?.1) ε₁ ε₂

    OLD  link e₁ e₂    ⤳ (λ⟦Γ⟧. (box ?.0 in ε₁) ,, (box ?.1 in ε₂ {ℓ = ε₁.ℓ})) ?
    NEW  link e₁ e₂    ⤳ (λ⟦Γ₁⟧. λ⟦{ℓ:A}⟧→⟦B⟧. ?.1 ,, (?.1 {ℓ = ?.0.ℓ})) ε₁ ε₂

    OLD  linkall e₁ e₂ ⤳ (λ⟦Γ⟧. (box ?.0 in ε₁) ,, (box ?.1 in ε₂ (wireArg ε₁ D))) ?
           wireArg ε₁ {ℓ:A}       = {ℓ = ε₁.ℓ}
           wireArg ε₁ (D & {ℓ:A}) = (λ⟦Γ⟧. (box ?.0 in wireArg ε₁ D) ,, (box ?.1 in {ℓ = ε₁.ℓ})) ?
    NEW  linkall e₁ e₂ ⤳ (λ⟦Γ₁⟧. λ⟦D⟧→⟦B⟧. ?.1 ,, (?.1 (wire₀ ⟦D⟧))) ε₁ ε₂
           wire_k {ℓ:A}       = {ℓ = ?.k.ℓ}
           wire_k (D & {ℓ:A}) = wire_k D ,, {ℓ = ?.(k+1).ℓ}

Point by point:

    ┌────────────────────────┬──────────────────────────────────┬────────────────────────────────────┐
    │                        │ OLD (boxed)                      │ NEW (linearized)                   │
    ├────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
    │ shape                  │ one λ⟦Γ⟧ applied to ?            │ two-λ spine applied to ε₁ ε₂       │
    │ where ε₁ sits          │ spliced into the body: twice for │ once, first spine argument         │
    │                        │ link, n+1 times for linkall      │                                    │
    │ where ε₂ sits          │ spliced under box ?.1            │ once, second spine argument        │
    │ provider inside body   │ recomputed: box ?.0 in ε₁        │ referenced: ?.1 / ?.0              │
    │ wire                   │ {ℓ = ε₁.ℓ}: from a re-evaluation │ {ℓ = ?.k.ℓ}: from the bound value  │
    │ box used               │ yes (box ?.0, box ?.1, per step) │ none                               │
    │ λ annotations          │ ⟦Γ⟧ (ambient context)            │ ⟦Γ₁⟧, ⟦D⟧→⟦B⟧ (operand types)      │
    │ needs ambient context  │ yes                              │ no (CoreLink carries none)         │
    │ ε₁ evaluations         │ 2 (link) / n+1 (linkall)         │ 1                                  │
    │ ε₂ evaluations         │ 1                                │ 1                                  │
    │ order                  │ interleaved with the merge       │ ε₁, then ε₂, once each             │
    │ term size              │ O(n · |ε₁|)                      │ O(|ε₁| + |ε₂| + n)                 │
    └────────────────────────┴──────────────────────────────────┴────────────────────────────────────┘

Why it was replaced.  In the pure calculus the two spellings big‑step to the same
value on every elaborated program (this was mechanized as `linearization_coherent`
/`linearization_coherent_n` — proved via source evaluation and
`elaboration_uniqueness`, not core determinism, since `RLookupV` has no
disjointness premise — and removed together with the boxed definitions once the
switch was made).  The distinction is observable the moment a provider unit can
perform an effect while constructing its exports, which the implementation's host
capabilities `print`, `readfile`, `load` allow: under the boxed spelling a
provider that prints on construction prints twice (`n + 1` times under `linkall`),
a plugin `load` re‑reads and re‑executes its artifact once per wired import, and
rollback logic branching on the loader's answer runs once per copy.  Bind‑once
elaboration pins the documented semantics — every operand of a merge or link is
bound exactly once, so effects fire exactly once, in source order (`--link sys
counter app` is also the effect order) — and makes the verified term and the
shipped term the same term.
-/

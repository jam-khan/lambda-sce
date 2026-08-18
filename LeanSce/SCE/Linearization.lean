import LeanSce.SCE.Elaboration
import LeanSce.SCE.Theories

open SCE Core

/-!
# Linearized link combinators — the implementation's spelling, verified

The mechanization and the implementation each emit a *composition term* when they
elaborate `link`/`linkall` (and the toolchain linker reuses the very same term to
compose compiled units). The two spellings differ, deliberately, and this file
proves that difference harmless where it must be harmless and states precisely
why it exists.

Notation, used throughout this file's documentation:

* `Γ ⊢ e ⇒ A ⤳ ε`  — elaboration (`elabExp Γ e A ε`): source `e` has type `A`
  and elaborates to core term `ε`;
* `?`, `?.n`        — `query` (the current environment as a value) and its n‑th
  projection, counting from the right;
* `box ρ in ε`      — evaluate `ε` under the environment `ρ` (`Exp.box`);
* `ε₁ ,, ε₂`        — the core dependent merge (`Exp.mrg`): `ε₂` evaluates under
  the ambient environment *extended with the value of* `ε₁`;
* `{ℓ = ε}`         — a single‑field record (`Exp.lrec`);
* `⟨{ℓ : A} ⇛ B⟩`   — a functor signature (`sig (TyArrM (rcd ℓ A) (TyIntf B))`);
* `⟦·⟧`             — type elaboration (`elabTyp`).

## The two spellings of `link`

The premises of both rules are identical — only the emitted term differs.

**E‑Link** (this mechanization: rule `elabExp.mlink`, combinator `linkedCore`).
The operands are *spliced* into the emitted term, re‑entered under the ambient
environment through `box`:

    Γ ⊢ e₁ ⇒ Γ₁ ⤳ ε₁      Γ ⊢ e₂ ⇒ ⟨{ℓ : A} ⇛ B⟩ ⤳ ε₂      Γ₁ ∋ ℓ : A
    ──────────────────────────────────────────────────────────────────── E‑Link
    Γ ⊢ link e₁ e₂ ⇒ Γ₁ & B
        ⤳  (λ⟦Γ⟧. (box ?.0 in ε₁) ,, (box ?.1 in ε₂ {ℓ = ε₁.ℓ}))  ?

**E‑Link‑Lin** (the implementation: `Elab.link_step` in `lib/sce/elab.ml`,
reused verbatim by the artifact linker in `lib/sepcomp.ml`; this file's
`linkStep`). The operands are *bound once each* on an application spine, and the
wire record projects from the bound provider:

    Γ ⊢ e₁ ⇒ Γ₁ ⤳ ε₁      Γ ⊢ e₂ ⇒ ⟨{ℓ : A} ⇛ B⟩ ⤳ ε₂      Γ₁ ∋ ℓ : A
    ──────────────────────────────────────────────────────────────── E‑Link‑Lin
    Γ ⊢ link e₁ e₂ ⇒ Γ₁ & B
        ⤳  (λ⟦Γ₁⟧. λ⟦{ℓ:A}⟧→⟦B⟧.  ?.1 ,, (?.1 {ℓ = ?.0.ℓ}))  ε₁  ε₂

Inside the double lambda: on the left of the merge `?.1` is the provider; on the
right — one slot deeper, under the freshly merged provider copy — `?.1` is the
functor and `?.0` the provider. The wire `{ℓ = ?.0.ℓ}` mentions `ε₁` *not at
all*: it projects out of the value the spine bound.

For `linkall` (import interface `D = {ℓ₁:A₁} & ⋯ & {ℓₙ:Aₙ}`) the contrast is
starker. E‑Link's wire (`wireArg`) re‑splices `ε₁` once per import:

    wireArg(D & {ℓ:A}) = wireArg(D) ⊞ {ℓ = ε₁.ℓ}        (⊞ = boxed n‑ary merge)

while the linearized wire (`wireLin`, mirroring the OCaml `wire`) is pure
projection at a de Bruijn shift, `ε₁` still occurring exactly once on the spine:

    wire_k({ℓ:A})     = {ℓ = ?.k.ℓ}
    wire_k(D & {ℓ:A}) = wire_k(D) ,, {ℓ = ?.(k+1).ℓ}

## Occurrence and evaluation multiplicity

| | `ε₁` occurrences | `ε₁` evaluations | `ε₂` evaluations | operand order |
|---|---|---|---|---|
| E‑Link | 2 | 2 | 1 | interleaved with the merge |
| E‑Link (linkall, n imports) | n + 1 | n + 1 | 1 | interleaved |
| E‑Link‑Lin | 1 | 1 | 1 | `ε₁` then `ε₂`, once each |

## Why the pure calculus cannot tell them apart — and why that proof is subtle

On *elaborated programs* both spellings compute the same value; that is exactly
`linearization_coherent`/`linearization_coherent_n` below. The proof is **not**
by raw determinism of core evaluation: `RLookupV` carries no disjointness
premise, so as a relation it selects either field of a duplicated label. Merges
are not required to be label-disjoint, so such a value is well typed — it is the
projection off it that `RLookup` refuses — and this is inherited from λE, not
peculiar to us. λE discharges the ambiguity with a typing hypothesis; here the
statement relates two already elaborated terms, so the two evaluations of `ε₁`
inside an E‑Link term need not agree on arbitrary core terms. Determinism holds
only on the image of elaboration. Accordingly, agreement is proved the same way everything
else in this development is proved: both spellings are related to the *source*
evaluation (`separate_compilation*` here and in `Theories.lean`), and their
result values coincide because both elaborate the same source value
(`elaboration_uniqueness`). The claim "the two linkers agree" is a statement
about elaborated programs — precisely, and only, the terms the toolchain linker
ever composes.

## Why effects force the linearized spelling

In the pure calculus the spelling is a matter of taste. The implementation's
branch adds host capabilities — `print`, `readfile`, and crucially
`load : String → (Sig | {err : String})` — as `Hostfn` values a provider unit
may *call while constructing its exports*. The moment `ε₁` can carry an effect,
the table above is observable:

* under E‑Link, a provider that prints on construction prints **twice**; under
  `linkall` with n imports, **n + 1 times**;
* a provider that `load`s a plugin at construction would re‑read and re‑execute
  the artifact once per wired import;
* rollback logic branching on the loader's `inr` would run once per copy,
  in an environment that already committed to the first copy's answer.

Bind‑once elaboration pins the semantics the toolchain documents: *every operand
of a merge or link is bound exactly once, so effects fire exactly once, in
source order* — the link line `--link sys counter app` is also the effect order.
That is why the implementation elaborates `,,`/`link`/`linkall` with the
linearized combinators, and why the paper's elaboration figure shows
E‑Link‑Lin. The theorems below re‑anchor the separate‑compilation results of
`Theories.lean` on exactly those combinators, so the verified term and the
shipped term are the same term.

Effects themselves stay outside the mechanization (there is no `Hostfn` here);
what is mechanized is everything the pure calculus can say about the choice:
the linearized combinators are well‑typed (`linkedCoreLin_typed` — the check
the OCaml linker replays on every link), they satisfy the same
separate‑compilation theorems (`separate_compilation_lin*`), and they agree
with the mechanized spelling on all elaborated programs
(`linearization_coherent*`).
-/

/-! ## The combinators, mirrored from the implementation

Each definition transcribes its OCaml counterpart from `lib/sce/elab.ml`
(`nmrg_step`, `wire`, `link_step`) and `lib/sepcomp.ml` reuses the same terms as
the artifact linker's step. Lambda annotations are irrelevant to evaluation
(`EBig` ignores them) but are exactly what the typing theorems pin down. -/

/-- `λ(x:a). λ(y:b). ?.1 ,, ?.1` — the bind‑once non‑dependent merge step
(OCaml `nmrg_step`). On the left of the merge `?.1` is `x`; on the right, one
slot deeper under the merged left value, `?.1` is `y`. -/
def nmrgStep (a b : Core.Typ) : Core.Exp :=
  .lam a (.lam b (.mrg (.proj .query 1) (.proj .query 1)))

/-- `(nmrgStep a b) ε₁ ε₂` — the linearized elaboration of `e₁ ,, e₂`
(OCaml `nmrg_core`); also the toolchain's leaf link step (`link_step_leaf`). -/
def nmrgCoreLin (a b : Core.Typ) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  .app (.app (nmrgStep a b) ce₁) ce₂

/-- The linearized wire (OCaml `wire`): the import package for interface `D`,
built by *projection from the bound provider* at de Bruijn index `shift`. Each
nested dependent merge shifts the provider one slot deeper, hence `shift + 1`
on the right. Contrast `wireArg` (Elaboration.lean), which re‑splices the
provider term `ce₁` once per import. -/
def wireLin (shift : Nat) : SCE.Typ → Core.Exp
  | .rcd l _ => .lrec l (.rproj (.proj .query shift) l)
  | .and D (.rcd l _) =>
    .mrg (wireLin shift D) (.lrec l (.rproj (.proj .query (shift + 1)) l))
  | _ => .unit

/-- `λ(p:g1). λ(f:tf). ?.1 ,, (?.1 (wire₀ D))` — the bind‑once link step
(OCaml `link_step`). The provider is bound once; every import label projects
from that binding. The artifact linker applies this same step term. -/
def linkStep (g1 tf : Core.Typ) (D : SCE.Typ) : Core.Exp :=
  .lam g1 (.lam tf (.mrg (.proj .query 1) (.app (.proj .query 1) (wireLin 0 D))))

/-- `(linkStep g1 tf D) ε₁ ε₂` — the linearized elaboration of `link`/`linkall`
(OCaml `linked_core`); `D := {ℓ:A}` is the binary `link`. -/
def linkedCoreLin (g1 tf : Core.Typ) (D : SCE.Typ) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  .app (.app (linkStep g1 tf D) ce₁) ce₂

/-! ## Typing

The OCaml linker re‑typechecks its output on every link ("the linker is only
right if its output is well‑typed λE"). These theorems are that check,
discharged once and for all for the step terms it emits. -/

/-- The linearized wire is well‑typed: under any context that reaches the
provider type `⟦Γ₁⟧` at index `shift`, `wire_shift D` has the interface type
`⟦D⟧`. -/
theorem wireLin_typed {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D)
    : ∀ {C : Core.Typ} {shift : Nat},
      Core.Lookup C shift (elabTyp Γ₁)
      → HasType C (wireLin shift D) (elabTyp D) := by
  induction hok with
  | one hrl =>
    intro C shift hlook
    simp only [wireLin, elabTyp]
    exact HasType.trcd (HasType.trproj (HasType.tproj HasType.tquery hlook)
      (type_safe_record_lookup hrl))
  | more hok' hrl ih =>
    intro C shift hlook
    simp only [wireLin, elabTyp]
    exact HasType.tmrg (ih hlook)
      (HasType.trcd (HasType.trproj
        (HasType.tproj HasType.tquery (Core.Lookup.succ hlook))
        (type_safe_record_lookup hrl)))

/-- The linearized link composition is well‑typed at `⟦Γ₁⟧ & ⟦B⟧` — the
linearized counterpart of `core_link_typed`/`core_linkn_typed`, with the lambda
annotations exactly as the OCaml elaborator writes them. -/
theorem linkedCoreLin_typed
    {Γ₁ D B : SCE.Typ} {Γc : Core.Typ} {ce₁ ce₂ : Core.Exp}
    (hok : LinkOk Γ₁ D)
    (h₁ : HasType Γc ce₁ (elabTyp Γ₁))
    (h₂ : HasType Γc ce₂ (.arr (elabTyp D) (elabTyp B)))
    : HasType Γc
        (linkedCoreLin (elabTyp Γ₁) (.arr (elabTyp D) (elabTyp B)) D ce₁ ce₂)
        (.and (elabTyp Γ₁) (elabTyp B)) := by
  simp only [linkedCoreLin, linkStep]
  apply HasType.tapp (HasType.tapp ?_ h₁) h₂
  apply HasType.tlam
  apply HasType.tlam
  apply HasType.tmrg
  · exact HasType.tproj HasType.tquery (Core.Lookup.succ Core.Lookup.zero)
  · exact HasType.tapp
      (HasType.tproj HasType.tquery (Core.Lookup.succ Core.Lookup.zero))
      (wireLin_typed hok Core.Lookup.zero)

/-- The linearized non‑dependent merge is well‑typed at `a & b`. -/
theorem nmrgCoreLin_typed {Γc a b : Core.Typ} {ce₁ ce₂ : Core.Exp}
    (h₁ : HasType Γc ce₁ a) (h₂ : HasType Γc ce₂ b)
    : HasType Γc (nmrgCoreLin a b ce₁ ce₂) (.and a b) := by
  simp only [nmrgCoreLin, nmrgStep]
  apply HasType.tapp (HasType.tapp ?_ h₁) h₂
  apply HasType.tlam
  apply HasType.tlam
  apply HasType.tmrg
  · exact HasType.tproj HasType.tquery (Core.Lookup.succ Core.Lookup.zero)
  · exact HasType.tproj HasType.tquery (Core.Lookup.succ Core.Lookup.zero)

/-! ## Evaluation

Operational lemmas assembling `EBig` derivations for the linearized terms —
the counterparts of `nmrg_core_eval`, `wireArg_eval`, and
`linkedCore_eval`/`linkedCoreN_eval`. Note the premise shapes: each operand
evaluation appears **once**, mirroring the terms themselves. -/

/-- Bind‑once merge: if each operand evaluates once under `ρ`, the linearized
merge evaluates to the merged values. -/
theorem nmrgCoreLin_eval
    {ρc vc₁ vc₂ : Core.Exp} {a b : Core.Typ} {ce₁ ce₂ : Core.Exp}
    (hρ : Core.Value ρc)
    (hbig1 : EBig ρc ce₁ vc₁)
    (hbig2 : EBig ρc ce₂ vc₂)
    : EBig ρc (nmrgCoreLin a b ce₁ ce₂) (.mrg vc₁ vc₂) := by
  have hv1 := ebig_produces_value hρ hbig1
  have hv2 := ebig_produces_value hρ hbig2
  simp only [nmrgCoreLin, nmrgStep]
  apply EBig.ebapp
  · exact EBig.ebapp (EBig.ebclos hρ) hbig1 (EBig.ebclos (Core.Value.vmrg hρ hv1))
  · exact hbig2
  · apply EBig.ebmrg
    · exact EBig.ebproj
        (EBig.equery (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hv2))
        (Core.LookupV.lvsucc Core.LookupV.lvzero)
    · exact EBig.ebproj
        (EBig.equery
          (Core.Value.vmrg (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hv2) hv1))
        (Core.LookupV.lvsucc Core.LookupV.lvzero)

/-- The linearized wire evaluates by projection alone. Generalized over the
environment: wherever the provider *value* `vc₁` is reachable at index `shift`,
`wire_shift D` evaluates to a package that elaborates the source package.
No re‑evaluation of the provider term occurs — the only premise about `ce₁`'s
evaluation is absent, because the wire never mentions `ce₁`. -/
theorem wireLin_eval {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D)
    : ∀ {v₁ pkg : SCE.Exp} {ρ' vc₁ : Core.Exp} {shift : Nat},
      S_Sem.SelPkg v₁ D pkg
      → SCE.Value v₁
      → elabExp SCE.Typ.top v₁ Γ₁ vc₁
      → Core.Value ρ'
      → Core.LookupV ρ' shift vc₁
      → ∃ cpkg, EBig ρ' (wireLin shift D) cpkg ∧ elabExp SCE.Typ.top pkg D cpkg := by
  induction hok with
  | one hrl =>
    intro v₁ pkg ρ' vc₁ shift hsp hv₁ helab₁ hρ' hlook
    cases hsp with
    | one hsel =>
      obtain ⟨vcl, hrlv, helab_vl⟩ := sel_preservation hv₁ helab₁ hsel hrl
      exact ⟨_,
        EBig.ebrec (EBig.ebsel (EBig.ebproj (EBig.equery hρ') hlook) hrlv),
        elabExp.elrec _ _ _ _ _ helab_vl⟩
  | more hok' hrl ih =>
    intro v₁ pkg ρ' vc₁ shift hsp hv₁ helab₁ hρ' hlook
    cases hsp with
    | more hsp' hsel =>
      obtain ⟨cpkg', hbig', helab'⟩ := ih hsp' hv₁ helab₁ hρ' hlook
      obtain ⟨vcl, hrlv, helab_vl⟩ := sel_preservation hv₁ helab₁ hsel hrl
      have hvl := source_sel_value hv₁ hsel
      have hcpkg' := ebig_produces_value hρ' hbig'
      exact ⟨_,
        EBig.ebmrg hbig'
          (EBig.ebrec (EBig.ebsel
            (EBig.ebproj (EBig.equery (Core.Value.vmrg hρ' hcpkg'))
              (Core.LookupV.lvsucc hlook)) hrlv)),
        elabExp.edmrg _ _ _ _ _ _ _ helab'
          (value_typing_weakening (SCE.Value.vlrec hvl)
            (elabExp.elrec SCE.Typ.top _ _ _ _ helab_vl))⟩

/-- The assembly lemma for the linearized composition: one evaluation of each
operand, one wire evaluation under the spine‑built environment
`((ρ , v₁) , f) , v₁`, one closure‑body evaluation — exactly the derivation
shape of the term. Shared by the binary and n‑ary theorems below. -/
theorem linkStep_eval
    {ρc vc₁ vc₂ cpkg vc₃ : Core.Exp} {g1 tf DT : Core.Typ} {D : SCE.Typ}
    {ce₁ ce₂ body : Core.Exp}
    (hρ : Core.Value ρc)
    (hbig1 : EBig ρc ce₁ vc₁)
    (hbig2 : EBig ρc ce₂ (.clos vc₂ DT body))
    (hbigw : EBig (.mrg (.mrg (.mrg ρc vc₁) (.clos vc₂ DT body)) vc₁)
               (wireLin 0 D) cpkg)
    (hbig3 : EBig (.mrg vc₂ cpkg) body vc₃)
    : EBig ρc (linkedCoreLin g1 tf D ce₁ ce₂) (.mrg vc₁ vc₃) := by
  have hv1 := ebig_produces_value hρ hbig1
  have hvf := ebig_produces_value hρ hbig2
  simp only [linkedCoreLin, linkStep]
  apply EBig.ebapp
  · exact EBig.ebapp (EBig.ebclos hρ) hbig1 (EBig.ebclos (Core.Value.vmrg hρ hv1))
  · exact hbig2
  · apply EBig.ebmrg
    · exact EBig.ebproj
        (EBig.equery (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hvf))
        (Core.LookupV.lvsucc Core.LookupV.lvzero)
    · exact EBig.ebapp
        (EBig.ebproj
          (EBig.equery
            (Core.Value.vmrg (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hvf) hv1))
          (Core.LookupV.lvsucc Core.LookupV.lvzero))
        hbigw
        hbig3

/-! ## Separate compilation, re‑anchored on the shipped combinators

The four theorems below restate `separate_compilation`,
`separate_compilation_closed`, `separate_compilation_n`, and
`separate_compilation_n_closed` (Theories.lean) with the **linearized**
composition term in the conclusion — the term the OCaml elaborator emits and the
artifact linker applies. The proofs mirror the `mlink`/`mlinkn` cases of
`semantic_preservation`, replacing the boxed assembly lemmas with the
linearized ones; each operand's evaluation is consumed exactly once. -/

/-- **Separate compilation, linearized (binary `link`).** Elaborate the provider
and the functor separately, compose the compiled pieces with the implementation's
`link_step`, and the result evaluates in lock‑step with source‑level `link`. -/
theorem separate_compilation_lin
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (heval : S_Sem.BStep ρs (.mlink es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc,
        EBig ρc
          (linkedCoreLin (elabTyp Γ₁)
            (.arr (elabTyp (SCE.Typ.rcd l A)) (elabTyp B)) (.rcd l A) ec₁ ec₂) vc
        ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  cases heval with
  | mlink h1 bstep1 bstep2 sel1 bstep3 =>
    obtain ⟨vc1, hbig1, helab_v1⟩ := semantic_preservation helab₁ bstep1 henv henv_val
    obtain ⟨vc2, hbig2, helab_v2⟩ := semantic_preservation helab₂ bstep2 henv henv_val
    cases helab_v2 with
    | mclos _ ctx_inner _ _ _ _ ce_env ce_body hval_v2 h_env2 h_body =>
      have hρc := elab_value henv henv_val
      have hv1_val := eval_produces_value henv_val bstep1
      have hv1c := ebig_produces_value hρc hbig1
      have hvfc := ebig_produces_value hρc hbig2
      obtain ⟨vc_l, hrlookup_v, helab_vl⟩ :=
        sel_preservation hv1_val helab_v1 sel1 hlookup
      have hvl_val := source_sel_value hv1_val sel1
      have hval_lrec := SCE.Value.vlrec (l := l) hvl_val
      have hval_env := SCE.Value.vmrg hval_v2 hval_lrec
      have helab_lrec := elabExp.elrec SCE.Typ.top _ _ _ l helab_vl
      have helab_env := elabExp.edmrg SCE.Typ.top _ _ _ _ _ _ h_env2
        (value_typing_weakening hval_lrec helab_lrec)
      obtain ⟨vc3, hbig3, helab_v3⟩ :=
        semantic_preservation h_body bstep3 helab_env hval_env
      have hv3_val := eval_produces_value hval_env bstep3
      refine ⟨.mrg vc1 vc3, linkStep_eval hρc hbig1 hbig2 ?_ hbig3,
        elabExp.edmrg SCE.Typ.top _ _ _ _ _ _ helab_v1
          (value_typing_weakening hv3_val helab_v3)⟩
      simp only [wireLin]
      exact EBig.ebrec (EBig.ebsel
        (EBig.ebproj
          (EBig.equery
            (Core.Value.vmrg (Core.Value.vmrg (Core.Value.vmrg hρc hv1c) hvfc) hv1c))
          Core.LookupV.lvzero)
        hrlookup_v)

/-- **Separate compilation, linearized, closed** — the toolchain's actual case:
closed compiled units, empty initial environment. -/
theorem separate_compilation_lin_closed
    {Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp} {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (heval : S_Sem.BStep .unit (.mlink es₁ es₂) vs)
    : ∃ vc,
        EBig .unit
          (linkedCoreLin (elabTyp Γ₁)
            (.arr (elabTyp (SCE.Typ.rcd l A)) (elabTyp B)) (.rcd l A) ec₁ ec₂) vc
        ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc :=
  separate_compilation_lin helab₁ helab₂ hlookup heval
    (elabExp.eunit SCE.Typ.top) SCE.Value.vunit

/-- **Separate compilation, linearized (n‑ary `linkall`).** As above, with a
whole import interface `D` wired by projection from the once‑bound provider. -/
theorem separate_compilation_lin_n
    {Γ Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.sig (.TyArrM D (.TyIntf B))) ec₂)
    (hok : LinkOk Γ₁ D)
    (heval : S_Sem.BStep ρs (.mlinkn es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc,
        EBig ρc
          (linkedCoreLin (elabTyp Γ₁) (.arr (elabTyp D) (elabTyp B)) D ec₁ ec₂) vc
        ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  cases heval with
  | mlinkn h1 bstep1 bstep2 hsp bstep3 =>
    obtain ⟨vc1, hbig1, helab_v1⟩ := semantic_preservation helab₁ bstep1 henv henv_val
    obtain ⟨vc2, hbig2, helab_v2⟩ := semantic_preservation helab₂ bstep2 henv henv_val
    cases helab_v2 with
    | mclos _ ctx_inner _ _ _ _ ce_env ce_body hval_v2 h_env2 h_body =>
      have hρc := elab_value henv henv_val
      have hv1_val := eval_produces_value henv_val bstep1
      have hv1c := ebig_produces_value hρc hbig1
      have hvfc := ebig_produces_value hρc hbig2
      obtain ⟨cpkg, hbigw, helab_pkg⟩ := wireLin_eval hok hsp hv1_val helab_v1
        (Core.Value.vmrg (Core.Value.vmrg (Core.Value.vmrg hρc hv1c) hvfc) hv1c)
        Core.LookupV.lvzero
      have hvpkg := S_Sem.selpkg_value hsp hv1_val
      have hval_env := SCE.Value.vmrg hval_v2 hvpkg
      have helab_env := elabExp.edmrg SCE.Typ.top _ _ _ _ _ _ h_env2
        (value_typing_weakening hvpkg helab_pkg)
      obtain ⟨vc3, hbig3, helab_v3⟩ :=
        semantic_preservation h_body bstep3 helab_env hval_env
      have hv3_val := eval_produces_value hval_env bstep3
      exact ⟨.mrg vc1 vc3, linkStep_eval hρc hbig1 hbig2 hbigw hbig3,
        elabExp.edmrg SCE.Typ.top _ _ _ _ _ _ helab_v1
          (value_typing_weakening hv3_val helab_v3)⟩

/-- **Separate compilation, linearized, n‑ary, closed.** -/
theorem separate_compilation_lin_n_closed
    {Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp} {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.sig (.TyArrM D (.TyIntf B))) ec₂)
    (hok : LinkOk Γ₁ D)
    (heval : S_Sem.BStep .unit (.mlinkn es₁ es₂) vs)
    : ∃ vc,
        EBig .unit
          (linkedCoreLin (elabTyp Γ₁) (.arr (elabTyp D) (elabTyp B)) D ec₁ ec₂) vc
        ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc :=
  separate_compilation_lin_n helab₁ helab₂ hok heval
    (elabExp.eunit SCE.Typ.top) SCE.Value.vunit

/-- The linearized elaboration of a non‑dependent merge `e₁ ,, e₂` agrees with
source evaluation — the leaf case of the toolchain linker (`link_step_leaf`). -/
theorem nmrg_lin
    {Γ A B : SCE.Typ} {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ A ec₁)
    (helab₂ : elabExp Γ es₂ B ec₂)
    (heval : S_Sem.BStep ρs (.nmrg es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc (nmrgCoreLin (elabTyp A) (elabTyp B) ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and A B) vc := by
  cases heval with
  | nmrg h1 bstep1 bstep2 =>
    obtain ⟨vc1, hbig1, helab_v1⟩ := semantic_preservation helab₁ bstep1 henv henv_val
    obtain ⟨vc2, hbig2, helab_v2⟩ := semantic_preservation helab₂ bstep2 henv henv_val
    have hρc := elab_value henv henv_val
    have hv2_val := eval_produces_value henv_val bstep2
    exact ⟨.mrg vc1 vc2, nmrgCoreLin_eval hρc hbig1 hbig2,
      elabExp.edmrg SCE.Typ.top _ _ _ _ _ _ helab_v1
        (value_typing_weakening hv2_val helab_v2)⟩

/-! ## Coherence: the two spellings compute the same value

The headline: on every elaborated program, the mechanized composition term
(`linkedCore`) and the implementation's linearized one (`linkedCoreLin`)
big‑step to the **same** core value. Per the module documentation, the proof
goes through the source: both spellings track the same source evaluation, and
`elaboration_uniqueness` pins their results to the same elaborated value —
raw core determinism is neither available (`RLookupV` relates either field of a
duplicated label) nor needed. -/

/-- **Linearization coherence (binary).** Both spellings of `link` evaluate to
one and the same value, the elaboration of the source result. -/
theorem linearization_coherent
    {Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp} {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (heval : S_Sem.BStep .unit (.mlink es₁ es₂) vs)
    : ∃ vc,
        EBig .unit (linkedCore Core.Typ.top l ec₁ ec₂) vc
        ∧ EBig .unit
            (linkedCoreLin (elabTyp Γ₁)
              (.arr (elabTyp (SCE.Typ.rcd l A)) (elabTyp B)) (.rcd l A) ec₁ ec₂) vc
        ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  obtain ⟨vc, hbox, helab_vs⟩ :=
    separate_compilation_closed helab₁ helab₂ hlookup heval
  obtain ⟨vc', hlin, helab_vs'⟩ :=
    separate_compilation_lin_closed helab₁ helab₂ hlookup heval
  have heq : vc' = vc := elaboration_uniqueness helab_vs' helab_vs
  subst heq
  exact ⟨vc', hbox, hlin, helab_vs'⟩

/-- **Linearization coherence (n‑ary).** As above for `linkall`, where the boxed
wire re‑evaluates the provider once per import and the linearized wire never
re‑evaluates it — and the values still coincide. -/
theorem linearization_coherent_n
    {Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp} {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.sig (.TyArrM D (.TyIntf B))) ec₂)
    (hok : LinkOk Γ₁ D)
    (heval : S_Sem.BStep .unit (.mlinkn es₁ es₂) vs)
    : ∃ vc,
        EBig .unit (linkedCoreN Core.Typ.top D ec₁ ec₂) vc
        ∧ EBig .unit
            (linkedCoreLin (elabTyp Γ₁) (.arr (elabTyp D) (elabTyp B)) D ec₁ ec₂) vc
        ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  obtain ⟨vc, hbox, helab_vs⟩ :=
    separate_compilation_n_closed helab₁ helab₂ hok heval
  obtain ⟨vc', hlin, helab_vs'⟩ :=
    separate_compilation_lin_n_closed helab₁ helab₂ hok heval
  have heq : vc' = vc := elaboration_uniqueness helab_vs' helab_vs
  subst heq
  exact ⟨vc', hbox, hlin, helab_vs'⟩

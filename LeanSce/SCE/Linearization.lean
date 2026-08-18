import LeanSce.SCE.Elaboration
import LeanSce.SCE.Theories

open SCE Core

/-!
# The boxed composition combinators, and coherence with the linearized rule

`Elaboration.lean` elaborates `,,`/`link`/`linkall` with the *linearized*
(bind‑once) combinators — the spelling the implementation emits and the toolchain
linker applies.  This file keeps the *boxed* spelling those rules previously
emitted, re‑proves its metatheory (typing, evaluation, separate compilation), and
proves the headline fact that justified the switch: **on every elaborated program
the two spellings compute the same value**.

Notation, as in `Elaboration.lean`: `?`/`?.n` for `query`/`proj query n`, `,,`
for the dependent merge, `box ρ in ε` for `Exp.box ρ ε`, `{ℓ = ε}` for `lrec`,
`⟦·⟧` for `elabTyp`, `⟨D ⇛ B⟩` for the functor signature
`sig (TyArrM D (TyIntf B))`.

## The two spellings

The premises of the rules are identical — only the emitted term differs.

**Linearized** (the elaboration; `nmrgCore`/`linkedCore` in `Elaboration.lean`):

    Γ ⊢ e₁ ,, e₂   ⇒ A & B   ⤳  (λ⟦A⟧. λ⟦B⟧. ?.1 ,, ?.1) ε₁ ε₂
    Γ ⊢ link e₁ e₂ ⇒ Γ₁ & B  ⤳  (λ⟦Γ₁⟧. λ⟦D⟧→⟦B⟧. ?.1 ,, (?.1 (wire₀ ⟦D⟧))) ε₁ ε₂

**Boxed** (this file; `nmrgCoreBoxed`/`linkedCoreBoxed`/`linkedCoreNBoxed`):

    Γ ⊢ e₁ ,, e₂      ⇒ A & B   ⤳  (λ⟦Γ⟧. (box ?.0 in ε₁) ,, (box ?.1 in ε₂)) ?
    Γ ⊢ link e₁ e₂    ⇒ Γ₁ & B  ⤳  (λ⟦Γ⟧. (box ?.0 in ε₁) ,, (box ?.1 in ε₂ {ℓ = ε₁.ℓ})) ?
    Γ ⊢ linkall e₁ e₂ ⇒ Γ₁ & B  ⤳  (λ⟦Γ⟧. (box ?.0 in ε₁) ,, (box ?.1 in ε₂ (wireArg ε₁ D))) ?

        wireArg ε₁ {ℓ:A}       = {ℓ = ε₁.ℓ}
        wireArg ε₁ (D & {ℓ:A}) = (λ⟦Γ⟧. (box ?.0 in wireArg ε₁ D) ,, (box ?.1 in {ℓ = ε₁.ℓ})) ?

## Why the boxed spelling was replaced

The boxed term *splices* the operand terms into a body that re‑enters the
ambient environment.  Under binary `link`, `ε₁` is spliced twice — once as the
left merge operand and once inside the wire — so the provider is evaluated twice
and the wire projects from a re‑computation, not from the provider that was
merged in.  Under `linkall` with `n` imports, `wireArg` re‑splices `ε₁` per
import and wraps each step in another ambient re‑entry: `ε₁` is evaluated
`n + 1` times and the term is `O(n · |ε₁|)`.

    | | `ε₁` occurrences | `ε₁` evaluations | `ε₂` evaluations | operand order |
    |---|---|---|---|---|
    | boxed `link` | 2 | 2 | 1 | interleaved with the merge |
    | boxed `linkall` (n imports) | n + 1 | n + 1 | 1 | interleaved |
    | linearized `link`/`linkall` | 1 | 1 | 1 | `ε₁` then `ε₂`, once each |

The pure calculus cannot observe the difference — that is exactly
`linearization_coherent`/`linearization_coherent_n` below.  The implementation's
branch adds host capabilities (`print`, `readfile`, `load : String → (Sig | {err})`)
that a provider unit may call *while constructing its exports*, and there the
table is observable: a provider that prints on construction prints twice (`n + 1`
times under `linkall`); a plugin `load` re‑reads and re‑executes the artifact
once per wired import; rollback logic branching on the loader's answer runs once
per copy, in an environment that already committed to the first copy's answer.
Bind‑once elaboration pins the documented semantics — every operand of a merge
or link is bound exactly once, so effects fire exactly once, in source order —
and makes the verified term and the shipped term the same term.  Effects stay
outside the mechanization; what is mechanized here is everything the pure
calculus can say about the choice.

## Why the coherence proof is subtle

The proof is **not** by raw determinism of core evaluation: `RLookupV` carries no
disjointness premise, so as a relation it selects either field of a duplicated
label.  Merges are not required to be label‑disjoint, so such a value is well
typed — it is the projection off it that `RLookup` refuses — and this is inherited
from λE.  Consequently the two evaluations of `ε₁` inside a boxed term need not
agree on arbitrary core terms; determinism holds only on the image of
elaboration.  So agreement is proved the way everything else in this development
is proved: both spellings are related to the *source* evaluation
(`separate_compilation*` in `Theories.lean` for the linearized term,
`separate_compilation_boxed*` here for the boxed one), and their result values
coincide because both elaborate the same source value (`elaboration_uniqueness`).
The claim "the two linkers agree" is a statement about elaborated programs —
precisely, and only, the terms the toolchain linker ever composes.
-/

/-! ## The boxed combinators -/

/-- `(λ⟦Γ⟧. (box ?.0 in ε₁) ,, (box ?.1 in ε₂ {ℓ = ε₁.ℓ})) ?` — the boxed
elaboration of binary `link`.  `ε₁` occurs twice. -/
def linkedCoreBoxed (ctx : Core.Typ) (l : String) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  .app
    (.lam ctx
      (.mrg
        (.box (.proj .query 0) ce₁)
        (.box (.proj .query 1)
          (.app ce₂ (.lrec l (.rproj ce₁ l))))))
    .query

/-- `(λ⟦Γ⟧. (box ?.0 in ε₁) ,, (box ?.1 in ε₂)) ?` — the boxed elaboration of
`e₁ ,, e₂`: both components evaluate under the same ambient environment. -/
def nmrgCoreBoxed (ctx : Core.Typ) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  .app
    (.lam ctx
      (.mrg
        (.box (.proj .query 0) ce₁)
        (.box (.proj .query 1) ce₂)))
    .query

/-- The boxed wire: the import package for `D`, built by projecting each labeled
import out of the *provider term* `ce₁` — re‑spliced once per import. -/
def wireArgBoxed (ctx : Core.Typ) (ce₁ : Core.Exp) : SCE.Typ → Core.Exp
  | .rcd l _ => .lrec l (.rproj ce₁ l)
  | .and D (.rcd l _) =>
    nmrgCoreBoxed ctx (wireArgBoxed ctx ce₁ D) (.lrec l (.rproj ce₁ l))
  | _ => .unit

/-- The boxed elaboration of `linkall`.  `ε₁` occurs `n + 1` times for `n`
imports. -/
def linkedCoreNBoxed (ctx : Core.Typ) (D : SCE.Typ) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  .app
    (.lam ctx
      (.mrg
        (.box (.proj .query 0) ce₁)
        (.box (.proj .query 1)
          (.app ce₂ (wireArgBoxed ctx ce₁ D)))))
    .query

/-! ## Typing -/

theorem nmrgCoreBoxed_typed {Γc a b : Core.Typ} {ce₁ ce₂ : Core.Exp}
    (h₁ : HasType Γc ce₁ a) (h₂ : HasType Γc ce₂ b)
    : HasType Γc (nmrgCoreBoxed Γc ce₁ ce₂) (.and a b) := by
  simp only [nmrgCoreBoxed]
  apply HasType.tapp
  · apply HasType.tlam
    apply HasType.tmrg
    · exact HasType.tbox (HasType.tproj HasType.tquery Lookup.zero) h₁
    · exact HasType.tbox (HasType.tproj HasType.tquery (Lookup.succ Lookup.zero)) h₂
  · exact HasType.tquery

/-- The boxed wire is well-typed at the interface type. -/
theorem wireArgBoxed_typed {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D)
    {Γc : Core.Typ} {ce₁ : Core.Exp}
    (h₁ : HasType Γc ce₁ (elabTyp Γ₁))
    : HasType Γc (wireArgBoxed Γc ce₁ D) (elabTyp D) := by
  induction hok with
  | one hrl =>
    exact HasType.trcd (HasType.trproj h₁ (type_safe_record_lookup hrl))
  | more hok' hrl ih =>
    simp only [wireArgBoxed, elabTyp]
    exact nmrgCoreBoxed_typed ih
      (HasType.trcd (HasType.trproj h₁ (type_safe_record_lookup hrl)))

theorem linkedCoreBoxed_typed
    {Γc A₁ A B : Core.Typ} {l : String} {ce₁ ce₂ : Core.Exp}
    (hrl : Core.RLookup A₁ l A)
    (h₁ : HasType Γc ce₁ A₁)
    (h₂ : HasType Γc ce₂ (.arr (.rcd l A) B))
    : HasType Γc (linkedCoreBoxed Γc l ce₁ ce₂) (.and A₁ B) := by
  simp only [linkedCoreBoxed]
  apply HasType.tapp
  · apply HasType.tlam
    apply HasType.tmrg
    · exact HasType.tbox (HasType.tproj HasType.tquery Lookup.zero) h₁
    · exact HasType.tbox (HasType.tproj HasType.tquery (Lookup.succ Lookup.zero))
        (HasType.tapp h₂ (HasType.trcd (HasType.trproj h₁ hrl)))
  · exact HasType.tquery

theorem linkedCoreNBoxed_typed
    {Γ₁ D : SCE.Typ} {Γc B : Core.Typ} {ce₁ ce₂ : Core.Exp}
    (hok : LinkOk Γ₁ D)
    (h₁ : HasType Γc ce₁ (elabTyp Γ₁))
    (h₂ : HasType Γc ce₂ (.arr (elabTyp D) B))
    : HasType Γc (linkedCoreNBoxed Γc D ce₁ ce₂) (.and (elabTyp Γ₁) B) := by
  simp only [linkedCoreNBoxed]
  apply HasType.tapp
  · apply HasType.tlam
    apply HasType.tmrg
    · exact HasType.tbox (HasType.tproj HasType.tquery Lookup.zero) h₁
    · exact HasType.tbox (HasType.tproj HasType.tquery (Lookup.succ Lookup.zero))
        (HasType.tapp h₂ (wireArgBoxed_typed hok h₁))
  · exact HasType.tquery

/-! ## Evaluation

Note the premise shapes, in contrast to `nmrgCore_eval`/`linkStep_eval`:
`linkedCoreBoxed_eval` consumes `hbig1 : EBig ρc ce₁ vc₁` **twice** (once for the
left operand, once inside the wire), and `wireArgBoxed_eval` needs the provider's
evaluation as a premise because the wire re‑evaluates it. -/

theorem nmrgCoreBoxed_eval
    {ρc vc₁ vc₂ : Core.Exp} {ctx : Core.Typ} {ce₁ ce₂ : Core.Exp}
    (hρ : Core.Value ρc)
    (hbig1 : EBig ρc ce₁ vc₁)
    (hbig2 : EBig ρc ce₂ vc₂)
    : EBig ρc (nmrgCoreBoxed ctx ce₁ ce₂) (.mrg vc₁ vc₂) := by
  have hv1 := ebig_produces_value hρ hbig1
  simp only [nmrgCoreBoxed]
  apply EBig.ebapp
  · exact EBig.ebclos hρ
  · exact EBig.equery hρ
  · apply EBig.ebmrg
    · exact EBig.ebbox
        (EBig.ebproj (EBig.equery (Value.vmrg hρ hρ)) LookupV.lvzero) hbig1
    · exact EBig.ebbox
        (EBig.ebproj (EBig.equery (Value.vmrg (Value.vmrg hρ hρ) hv1))
          (LookupV.lvsucc LookupV.lvzero))
        hbig2

theorem linkedCoreBoxed_eval
    {ρc vc₁ vc₂ vc_l vc₃ : Core.Exp} {ctx : Core.Typ} {l : String}
    {ce₁ ce₂ body : Core.Exp} {A : Core.Typ}
    (hρ : Core.Value ρc)
    (hbig1 : EBig ρc ce₁ vc₁)
    (hbig2 : EBig ρc ce₂ (.clos vc₂ (.rcd l A) body))
    (hsel : Core.RLookupV vc₁ l vc_l)
    (hbig3 : EBig (.mrg vc₂ (.lrec l vc_l)) body vc₃)
    : EBig ρc (linkedCoreBoxed ctx l ce₁ ce₂) (.mrg vc₁ vc₃) := by
  have hv1 := ebig_produces_value hρ hbig1
  simp only [linkedCoreBoxed]
  apply EBig.ebapp
  · exact EBig.ebclos hρ
  · exact EBig.equery hρ
  · apply EBig.ebmrg
    · exact EBig.ebbox
        (EBig.ebproj (EBig.equery (Value.vmrg hρ hρ)) LookupV.lvzero) hbig1
    · exact EBig.ebbox
        (EBig.ebproj (EBig.equery (Value.vmrg (Value.vmrg hρ hρ) hv1))
          (LookupV.lvsucc LookupV.lvzero))
        (EBig.ebapp hbig2 (EBig.ebrec (EBig.ebsel hbig1 hsel)) hbig3)

/-- The boxed wire evaluates to a Core package that elaborates the source
package — given the provider term's evaluation, which it repeats. -/
theorem wireArgBoxed_eval {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D) :
    ∀ {v₁ pkg : SCE.Exp} {Γc : Core.Typ} {ρc ce₁ vc₁ : Core.Exp},
    S_Sem.SelPkg v₁ D pkg
    → SCE.Value v₁
    → elabExp SCE.Typ.top v₁ Γ₁ vc₁
    → Core.Value ρc
    → EBig ρc ce₁ vc₁
    → ∃ cpkg, EBig ρc (wireArgBoxed Γc ce₁ D) cpkg ∧ elabExp SCE.Typ.top pkg D cpkg := by
  induction hok with
  | one hrl =>
    intro v₁ pkg Γc ρc ce₁ vc₁ hsp hv1 helab1 hρ hbig1
    cases hsp with
    | one hsel =>
      obtain ⟨vcl, hrlv, helab_vl⟩ := sel_preservation hv1 helab1 hsel hrl
      exact ⟨_, EBig.ebrec (EBig.ebsel hbig1 hrlv),
             elabExp.elrec _ _ _ _ _ helab_vl⟩
  | more hok' hrl ih =>
    intro v₁ pkg Γc ρc ce₁ vc₁ hsp hv1 helab1 hρ hbig1
    cases hsp with
    | more hsp' hsel =>
      obtain ⟨cpkg', hbig', helab'⟩ := ih (Γc := Γc) hsp' hv1 helab1 hρ hbig1
      obtain ⟨vcl, hrlv, helab_vl⟩ := sel_preservation hv1 helab1 hsel hrl
      have hvl := source_sel_value hv1 hsel
      exact ⟨_, nmrgCoreBoxed_eval hρ hbig' (EBig.ebrec (EBig.ebsel hbig1 hrlv)),
             elabExp.edmrg _ _ _ _ _ _ _ helab'
               (value_typing_weakening (SCE.Value.vlrec hvl)
                 (elabExp.elrec SCE.Typ.top _ _ _ _ helab_vl))⟩

theorem linkedCoreNBoxed_eval
    {ρc vc₁ vc₂ cpkg vc₃ : Core.Exp} {ctx DT : Core.Typ} {D : SCE.Typ}
    {ce₁ ce₂ body : Core.Exp}
    (hρ : Core.Value ρc)
    (hbig1 : EBig ρc ce₁ vc₁)
    (hbig2 : EBig ρc ce₂ (.clos vc₂ DT body))
    (hbigw : EBig ρc (wireArgBoxed ctx ce₁ D) cpkg)
    (hbig3 : EBig (.mrg vc₂ cpkg) body vc₃)
    : EBig ρc (linkedCoreNBoxed ctx D ce₁ ce₂) (.mrg vc₁ vc₃) := by
  have hv1 := ebig_produces_value hρ hbig1
  simp only [linkedCoreNBoxed]
  apply EBig.ebapp
  · exact EBig.ebclos hρ
  · exact EBig.equery hρ
  · apply EBig.ebmrg
    · exact EBig.ebbox
        (EBig.ebproj (EBig.equery (Value.vmrg hρ hρ)) LookupV.lvzero) hbig1
    · exact EBig.ebbox
        (EBig.ebproj (EBig.equery (Value.vmrg (Value.vmrg hρ hρ) hv1))
          (LookupV.lvsucc LookupV.lvzero))
        (EBig.ebapp hbig2 hbigw hbig3)

/-! ## Separate compilation with the boxed combinators

The boxed counterparts of `separate_compilation*` (Theories.lean).  The proofs
mirror the `mlink`/`mlinkn` cases of `semantic_preservation`, with the boxed
assembly lemmas in place of the linearized ones — and, tellingly, `hbig1` is
consumed twice. -/

theorem separate_compilation_boxed
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (heval : S_Sem.BStep ρs (.mlink es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc (linkedCoreBoxed (elabTyp Γ) l ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  cases heval with
  | mlink h1 bstep1 bstep2 sel1 bstep3 =>
    obtain ⟨vc1, hbig1, helab_v1⟩ := semantic_preservation helab₁ bstep1 henv henv_val
    obtain ⟨vc2, hbig2, helab_v2⟩ := semantic_preservation helab₂ bstep2 henv henv_val
    cases helab_v2 with
    | mclos _ ctx_inner _ _ _ _ ce_env ce_body hval_v2 h_env2 h_body =>
      have hρc := elab_value henv henv_val
      have hv1_val := eval_produces_value henv_val bstep1
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
      exact ⟨.mrg vc1 vc3,
        linkedCoreBoxed_eval hρc hbig1 hbig2 hrlookup_v hbig3,
        elabExp.edmrg SCE.Typ.top _ _ _ _ _ _ helab_v1
          (value_typing_weakening hv3_val helab_v3)⟩

theorem separate_compilation_boxed_closed
    {Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp} {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (heval : S_Sem.BStep .unit (.mlink es₁ es₂) vs)
    : ∃ vc, EBig .unit (linkedCoreBoxed Core.Typ.top l ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc :=
  separate_compilation_boxed helab₁ helab₂ hlookup heval
    (elabExp.eunit SCE.Typ.top) SCE.Value.vunit

theorem separate_compilation_boxed_n
    {Γ Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.sig (.TyArrM D (.TyIntf B))) ec₂)
    (hok : LinkOk Γ₁ D)
    (heval : S_Sem.BStep ρs (.mlinkn es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc (linkedCoreNBoxed (elabTyp Γ) D ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  cases heval with
  | mlinkn h1 bstep1 bstep2 hsp bstep3 =>
    obtain ⟨vc1, hbig1, helab_v1⟩ := semantic_preservation helab₁ bstep1 henv henv_val
    obtain ⟨vc2, hbig2, helab_v2⟩ := semantic_preservation helab₂ bstep2 henv henv_val
    cases helab_v2 with
    | mclos _ ctx_inner _ _ _ _ ce_env ce_body hval_v2 h_env2 h_body =>
      have hρc := elab_value henv henv_val
      have hv1_val := eval_produces_value henv_val bstep1
      obtain ⟨cpkg, hbigw, helab_pkg⟩ :=
        wireArgBoxed_eval hok hsp hv1_val helab_v1 hρc hbig1
      have hvpkg := S_Sem.selpkg_value hsp hv1_val
      have hval_env := SCE.Value.vmrg hval_v2 hvpkg
      have helab_env := elabExp.edmrg SCE.Typ.top _ _ _ _ _ _ h_env2
        (value_typing_weakening hvpkg helab_pkg)
      obtain ⟨vc3, hbig3, helab_v3⟩ :=
        semantic_preservation h_body bstep3 helab_env hval_env
      have hv3_val := eval_produces_value hval_env bstep3
      exact ⟨.mrg vc1 vc3,
        linkedCoreNBoxed_eval hρc hbig1 hbig2 hbigw hbig3,
        elabExp.edmrg SCE.Typ.top _ _ _ _ _ _ helab_v1
          (value_typing_weakening hv3_val helab_v3)⟩

theorem separate_compilation_boxed_n_closed
    {Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp} {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.sig (.TyArrM D (.TyIntf B))) ec₂)
    (hok : LinkOk Γ₁ D)
    (heval : S_Sem.BStep .unit (.mlinkn es₁ es₂) vs)
    : ∃ vc, EBig .unit (linkedCoreNBoxed Core.Typ.top D ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc :=
  separate_compilation_boxed_n helab₁ helab₂ hok heval
    (elabExp.eunit SCE.Typ.top) SCE.Value.vunit

/-- The boxed non-dependent merge agrees with source evaluation. -/
theorem nmrg_boxed
    {Γ A B : SCE.Typ} {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ A ec₁)
    (helab₂ : elabExp Γ es₂ B ec₂)
    (heval : S_Sem.BStep ρs (.nmrg es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc (nmrgCoreBoxed (elabTyp Γ) ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and A B) vc := by
  cases heval with
  | nmrg h1 bstep1 bstep2 =>
    obtain ⟨vc1, hbig1, helab_v1⟩ := semantic_preservation helab₁ bstep1 henv henv_val
    obtain ⟨vc2, hbig2, helab_v2⟩ := semantic_preservation helab₂ bstep2 henv henv_val
    have hρc := elab_value henv henv_val
    have hv2_val := eval_produces_value henv_val bstep2
    exact ⟨.mrg vc1 vc2, nmrgCoreBoxed_eval hρc hbig1 hbig2,
      elabExp.edmrg SCE.Typ.top _ _ _ _ _ _ helab_v1
        (value_typing_weakening hv2_val helab_v2)⟩

/-! ## Coherence: the two spellings compute the same value

On every elaborated program, the linearized composition term (the elaboration)
and the boxed one big‑step to the **same** core value.  Per the module
documentation, the proof goes through the source: both spellings track the same
source evaluation, and `elaboration_uniqueness` pins their results to the same
elaborated value — raw core determinism is neither available (`RLookupV` relates
either field of a duplicated label) nor needed. -/

/-- **Linearization coherence (binary).**  Both spellings of `link` evaluate to
one and the same value, the elaboration of the source result. -/
theorem linearization_coherent
    {Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp} {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (heval : S_Sem.BStep .unit (.mlink es₁ es₂) vs)
    : ∃ vc,
        EBig .unit (linkedCore (elabTyp Γ₁) (elabTyp (SCE.Typ.rcd l A)) (elabTyp B) ec₁ ec₂) vc
        ∧ EBig .unit (linkedCoreBoxed Core.Typ.top l ec₁ ec₂) vc
        ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  obtain ⟨vc, hlin, helab_vs⟩ :=
    separate_compilation_closed helab₁ helab₂ hlookup heval
  obtain ⟨vc', hbox, helab_vs'⟩ :=
    separate_compilation_boxed_closed helab₁ helab₂ hlookup heval
  have heq : vc' = vc := elaboration_uniqueness helab_vs' helab_vs
  subst heq
  exact ⟨vc', hlin, hbox, helab_vs'⟩

/-- **Linearization coherence (n‑ary).**  As above for `linkall`, where the boxed
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
        EBig .unit (linkedCore (elabTyp Γ₁) (elabTyp D) (elabTyp B) ec₁ ec₂) vc
        ∧ EBig .unit (linkedCoreNBoxed Core.Typ.top D ec₁ ec₂) vc
        ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  obtain ⟨vc, hlin, helab_vs⟩ :=
    separate_compilation_n_closed helab₁ helab₂ hok heval
  obtain ⟨vc', hbox, helab_vs'⟩ :=
    separate_compilation_boxed_n_closed helab₁ helab₂ hok heval
  have heq : vc' = vc := elaboration_uniqueness helab_vs' helab_vs
  subst heq
  exact ⟨vc', hlin, hbox, helab_vs'⟩

/-- **Merge coherence.**  Both spellings of `,,` evaluate to the same value. -/
theorem nmrg_coherent
    {A B : SCE.Typ} {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp} {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ A ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ B ec₂)
    (heval : S_Sem.BStep .unit (.nmrg es₁ es₂) vs)
    : ∃ vc,
        EBig .unit (nmrgCore (elabTyp A) (elabTyp B) ec₁ ec₂) vc
        ∧ EBig .unit (nmrgCoreBoxed Core.Typ.top ec₁ ec₂) vc
        ∧ elabExp SCE.Typ.top vs (.and A B) vc := by
  obtain ⟨vc, hlin, helab_vs⟩ :=
    semantic_preservation (elabExp.enmrg _ _ _ _ _ _ _ helab₁ helab₂) heval
      (elabExp.eunit SCE.Typ.top) SCE.Value.vunit
  obtain ⟨vc', hbox, helab_vs'⟩ :=
    nmrg_boxed helab₁ helab₂ heval (elabExp.eunit SCE.Typ.top) SCE.Value.vunit
  have heq : vc' = vc := elaboration_uniqueness helab_vs' helab_vs
  subst heq
  exact ⟨vc', hlin, hbox, helab_vs'⟩

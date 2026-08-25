# HANDOFF: LeanSce — the sealing calculus (branch `lambdae-seal`)

**This branch is the self-contained sealing development: one source, one target,
subtyping + merges + sealing/type abstraction, with fix/unions/μ.  There is NO brand
polymorphism here, by design.**  It is Phases 0–2 of the original plan, complete and
sealed off at commit `3b799d9`.

**Brand polymorphism (∀β), its relational layer, and the generic-client
representation-independence results live on `lambdae-sub`** — that branch continues
from this same history and is where all ∀β work belongs.  Nothing on this branch
should acquire brand-variable syntax; if you need it, work on `lambdae-sub`.

**`main` mirrors `origin/main` and must stay clean/untouched until the user says
otherwise.**  Neither branch has been pushed to `origin`; push only when the user says.

Everything here is green: `lake build` succeeds (60 jobs), **zero `sorry`, only
standard axioms** — every flagship result (`source_representation_independence`,
`representation_independence`, `fundamental`, `normalization`,
`seal_semantic_preservation`, `seal_separate_compilation_sealed`) closes over
`propext` ALONE; only `source_bigstep_deterministic` also uses `Quot.sound`, and
nothing uses `Classical.choice`.  Check via `lake env lean` on a scratch file
importing `LeanSce` with `#print axioms …`.

Architecture now: **one source, one target.**  `LeanSce/SCE` (source λSCE) elaborates
via `elabSeal` (`Seal/Elaboration.lean`) into `LeanSce/Seal` (λE^≤, the sealing
target).  `LeanSce/Core` and the SCE→Core elaboration are DELETED (Phase 2e,
commit `1a79fcd`); `grep -rn "Core\." LeanSce` and `grep -rn "elabExp" LeanSce`
are empty.

---

## 1. DONE

### Phase 0 — branch unification ✅ (session 1)
`main` and `lambdae-sub` merged so they share history.  Commits `13a5907`,
`d357355`, `c67ffbb`.  (Session 2 initially continued on `main` by mistake; all
34 unpushed commits were moved to `lambdae-sub` and local `main` was reset to
`origin/main`.  **Work on `lambdae-sub` only.**)

### Phase 1 — fix/unions/μ in λE^≤ + retargeted elaboration ✅ (session 1)
Commits `da5407a` (fixpoints, two-annotation fclos design), `0097e35` (unions,
componentwise-only subtyping + unconditional `Cost.coror`), `7528a65` (iso-recursive μ,
the brand pattern), `975d4ff` (elabSeal end-to-end incl. nine new simulation cases),
`8a881d0` (total source sealing coercions sig/or/μ/var + their simulation).
Relational layer fenced by `Seal.Finitary` / `SCE.SFinitary` (fix/μ break SN;
step-indexed LR = future work).  Full design notes for these are in this file's
git history (`git show f72ccac:HANDOFF.md`) — everything there about Phase 1
remains true.

### Phase 2 — single-target cleanup ✅ (THIS session, commits `7bd7fcc..a379899`)

- **2-pre** (`7bd7fcc`): `elabSeal_weaken`, `value_elab_sig_intf`,
  `elabSeal_lookup_pres`, `elabSeal_sel_absent`, `elabSeal_sel_pres` moved
  Correctness → `Seal/Elaboration.lean` (both SCE/Preservation and Correctness may
  import Elaboration; Correctness imports SCE files, so the reverse would cycle).
- **2a** (`d2ff193`) `SCE/Preservation.lean`: `svalue_not_step`;
  `elabSeal_lookup_prog`/`elabSeal_sel_prog`; `elabSeal_selpkg_prog`/`_pres` over
  **`Seal.WireOk`** (WireOk.more's second Disj is exactly evmrg's obligation for the
  accumulated package merge); `source_ssealv_pres`/`source_sunsealv_pres` (structural
  on SSealV; arr/sig cases re-elaborate the proxies with eclos/emclos — same
  derivations as `eval_sealv`; μ via `sce_substBrand_notin`);
  `source_sgpreservation`/`source_spreservation` with REAL sealing cases.  All
  value-merge rebuilds go through `evmrg` exactly per the session-1 map (§2a of the
  old HANDOFF — consult git history if needed; the map was correct throughout).
- **2b** (`30a2eb5`) `SCE/Progress.lean`: `source_ssealv_prog`/`source_sunsealv_prog`
  (structural on the signature: int/top/brand/and/rcd by inversion; arr / TyArrM-TyIntf
  sig / var / mu immediate; or by tag; bare-TyIntf and nested-TyArrM sig vacuous);
  `source_sgprogress`/`source_sprogress`.
- **2c** (`7b17983`, `6bd14fb`) new `SCE/Determinism.lean`:
  `elabSeal_uniqueness` (inference+elaboration uniqueness MERGED, concluding
  `T₁ = T₂ ∧ ce₁ = ce₂`; generalized over the two contexts — `Γ₁ = Γ₂ ∨ Value e` —
  which is what the mixed edmrg/evmrg inversions of a value merge need);
  `source_sel_labelin`; `source_sel_det`; `source_selpkg_det` (WireOk);
  `source_bigstep_elab_pres` (big-step preservation of elaboration, proved directly
  so determinism does not need the EVal simulation); `source_bigstep_deterministic(_gen)`
  (mseal/munseal via `S_Sem.ssealv_det`/`sunsealv_det`; wrap via `bstep_value_id`).
  Imports `Seal.Correctness` (for `bstep_value_id`; no cycle).
- **2d** (`cf6436e`): `SCE/Capabilities.lean` `source_sandboxed_functor_confinement`
  (sandboxing is the context-free case — evmrg needs no Disj at all);
  `SCE/RecLinking.lean` `source_mrec_elab` + corollaries — the knot carries THREE
  Disj hypotheses on sealTyp images (eletb's extension by the functor type, eflam's
  two); for closed programs the eletb one is `disj_top`.
- **2e** (`1a79fcd`): DELETED `LeanSce/Core/` and `LeanSce/SCE/Elaboration.lean`.
  `SCE/Theories.lean` reduced to pure source metatheory (lookup uniqueness,
  `eval_produces_value`).  `LeanSce.lean` imports fixed.
- **2f partial** (`a379899`): value-lemma triplets deduped into
  `S_Sem.lookupv_value`/`S_Sem.sel_value` (SCE/Semantics.lean).

---

## 2. REMAINING

### 2f — optional simplifications (not blocking anything)
- Collapse `SCE.ModTyp` into `Typ.mfun : Typ → Typ → Typ` (removes the Typ/ModTyp
  mutual and the `sig` cases of LabelIn/SRLookup).  Medium churn; changes inversion
  shapes everywhere — schedule as its own pass if wanted.
- Merge `mlink` into `mlinkn` (it is the singleton `D := rcd l A` instance; keep
  `mlink` as a `def`, drop its elab/BStep/SStep/det/progress cases).
- `innerCtx : Sandbox → Typ → Typ` replacing the paired implication premises in
  mstruct/mfunctor rules (both elabSeal and source relations).
- `letb`/`openm` STAY primitive (letb is annotation-free since `816abed`).

### Brand polymorphism — DELIBERATELY OUT OF SCOPE HERE
∀β types, the conservative disjointness layer they force, and the generic-client
relational results live on **`lambdae-sub`**, which branches from this same history.
Do not port them here: the point of this branch is a sealing calculus whose
disjointness story is entirely label- and brand-driven, with no brand variables
anywhere.  (On `lambdae-sub` see its HANDOFF §3 and `Seal/DESIGN.md` §(h).)

### Other open items
- μ/fix examples in `Seal/Examples.lean` (a sealed-interface factorial via flam;
  a tagged-union run; a μ-stream).
- **`doc/system.tex` is stale w.r.t. Phases 1–2**: it documents the sealing +
  subtyping core only, and is missing the unions, iso-recursive μ, and fixpoints
  that this branch DOES contain.  (A de-staled `system.tex` exists on
  `lambdae-sub`, but it also documents the ∀β layer; porting it here means
  stripping that back out.)
- Step-indexed LR to lift the Finitary/SFinitary fence (future work).
- `origin` has NOT been pushed by either session (guardrail hook blocks
  checkout/restore, not push; push when the user says so).

---

## 3. Gotchas (both sessions; keep these)

- **Lean auto-generalizes and RE-INTRODUCES** hypotheses depending on the major
  premise's indices: after `induction ht` with `hfin : Finitary e` in context, each
  case has `hfin` back (specialized) and the IHs have `Finitary eᵢ →` prepended.  Do
  NOT `intro hfin`.
- **Match-arm `by` blocks auto-intro leading implicit binders** of the remaining
  telescope: writing `fun {Γ} {v} {ce} hv helab => …` in an equation arm over-binds
  (bit in `source_ssealv_prog`); write `fun hv helab => …` only.
- **`nomatch h` failures inside `try`/`first` are UNCATCHABLE** ("Missing cases"
  is logged by the term elaborator, not thrown).  Never `cases x <;> try nomatch h`
  where the nomatch can fail; instead `cases hv` + `case <tag> => …` +
  `all_goals nomatch helab` where nomatch always succeeds, or list all constructors.
- **`case <tag>` selectors break inside `by_cases` bullets** (goal tags get a `pos.`
  hygiene prefix) — use explicit `cases … with` there.
- **`cases`-alternative arity**: inductive PARAMS (e.g. elabSeal's Δ) are NOT
  alternative arguments; `@emstruct` under `cases` takes 6 implicits + 3 premises,
  under `induction` +1 ih.
- **Underscore placeholders in `have h : _ = Γ₂ ∨ …`** are unsolvable if the term
  isn't determined — name case variables via `@`-binders instead.
- **`⟨_, elabSeal.eclos … ?_ …⟩` with refine**: the existential witness (the
  elaborated term) depends on the postponed body derivation and fails to synthesize —
  inline the full derivation as one `exact` term instead.
- sealTyp/substBrand/substTyp defeq DOES unfold through unification (mutual
  structural defs; `exact HasType.tinl ih`-style uses work), so `Disj (sealTyp ctx')
  (.arr (sealTyp A) (sealTyp B))` unifies with `Disj _ (sealTyp (.arr A B))` — no
  simp needed in term position.
- `simp only [SCE.substBrand] at h` BEFORE inverting elabSeal at a substBrand-typed
  index (cases needs the syntactic constructor).
- `sealModTyp (TyIntf B)`-forms block syntactic `rw [← sealTyp_substBrand]` — run
  `simp only [sealTyp, sealModTyp]` first.
- IDE diagnostics during multi-file edits are STALE — trust `lake build` only.
- `git checkout`/`git restore` are BLOCKED by the user's guardrail hook; use
  `git switch` (and `git archive | tar` for file extraction).
- elabSeal constructor premise ORDER (for inversions):
  `edmrg h₁ h₂ hd₁ hd₂`, `evmrg hv₁ hv₂ h₁ h₂ hd`, `enmrg h₁ h₂ hd₁ hd₂`,
  `elam h hd`, `eclos hv h₁ h₂ hd`, `eletb h₁ h₂ hd`, `eopenm h₁ h₂ hd`,
  `emstruct hs1 hs2 h`, `emfunctor hs1 hs2 hdop h`, `emclos hv h₁ h₂ hd`,
  `emapp h₁ h₂`, `emlink h₁ h₂ hl hd₁ hd₂`, `emlinkn h₁ h₂ hw hd₁ hd₂`,
  `ewrap hΔ hv h`, `emseal hΔ hnr hwf h`, `emunseal hΔ hnr hwf h heq`,
  `einl h`, `einr h`, `ecase h h₁ h₂ hd₁ hd₂`, `eflam h hd₁ hd₂`,
  `efclos hv h₁ h₂ hd₁ hd₂`, `efold h`, `eunfold h heq`.
- Build: `lake build` ≈ 60 jobs; single module `lake build LeanSce.SCE.Foo`;
  errors: `lake build 2>&1 | grep -E "^error" -A 6`.

## 4. Commit log (newest first; session 2 above the line)

```
a379899 S_Sem: single lookupv_value/sel_value — dedupe the value-lemma triplets
1a79fcd Delete Core + the SCE→Core elaboration: one source, one target — Phase 2e done
cf6436e SCE: Capabilities + RecLinking re-witnessed by elabSeal — Phase 2d done
6bd14fb SCE/Determinism: big-step preservation + determinism — Phase 2c (ii)
7b17983 SCE/Determinism: elabSeal uniqueness + selection determinism — Phase 2c (i)
30a2eb5 SCE/Progress: elabSeal port — Phase 2b done
d2ff193 SCE/Preservation: elabSeal port — Phase 2a done
7bd7fcc Seal: move elabSeal value/lookup/sel lemmas Correctness → Elaboration
────────
f72ccac HANDOFF.md session-1 takeover doc (full Phase 1 design notes live there)
8a881d0 … da5407a  Phase 1 (see §1)
```

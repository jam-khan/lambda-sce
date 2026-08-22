import LeanSce.SCE.Elaboration
import LeanSce.SCE.SmallStep
import LeanSce.SCE.Syntax
import LeanSce.SCE.Preservation

open SCE S_Sem

-- Generalized progress: well-elaborated expressions are values or can step
theorem sgprogress
    {Γ A : SCE.Typ} {e : SCE.Exp}
    (htyp : ∃ ce, elabExp Γ e A ce) :
    ∀ {v : SCE.Exp},
    SCE.Value v
    → (∃ ρc, elabExp SCE.Typ.top v Γ ρc)
    → SCE.Value e ∨ ∃ e', SStep v e e' := by
  obtain ⟨ce, helab⟩ := htyp
  induction helab with
  | equery =>
    intro v hv _
    right; exact ⟨v, SStep.ssquery hv⟩
  | elit =>
    intro v hv _
    left; exact Value.vint
  | eunit =>
    intro v hv _
    left; exact Value.vunit
  | @eclos _ _ _ _ se1 _ _ _ hval _ _ =>
    intro v hv _; left; exact Value.vclos hval
  | @mclos _ _ _ _ se1 _ _ _ hval _ _ =>
    intro v hv _; left; exact Value.vmclos hval
  | elam => intro v hv _; right; exact ⟨.clos v _ _, SStep.ssclos hv⟩
  | @eapp _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.app e' se2, SStep.ssappl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.app se1 e', SStep.ssappr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        match hve1 with
        | .vclos hvc => match h1 with
          | .eclos _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, SStep.ssbeta hv hve2 hvc⟩
        | .vfclos hvc => match h1 with
          | .efclos _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, SStep.ssfbeta hv hve2 hvc⟩
        | .vint => nomatch h1
        | .vunit => nomatch h1
        | .vmrg _ _ => nomatch h1
        | .vmclos _ => nomatch h1
        | .vlrec _ => nomatch h1
        | .vinl _ => nomatch h1
        | .vinr _ => nomatch h1
  | @ebox _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.box e' se2, SStep.ssboxl hv hstep⟩
    | .inl hve1 =>
      have henv2 : ∃ ρc, elabExp Typ.top se1 _ ρc := ⟨_, elab_value_weaken h1 hve1 _⟩
      have prog2 := ih2 hve1 henv2
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.box se1 e', SStep.ssboxr hv hve1 hstep⟩
      | .inl hve2 => right; exact ⟨_, SStep.ssboxv hv hve1 hve2⟩
  | @edmrg _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    obtain ⟨ρc, henvE⟩ := henv
    have prog1 := ih1 hv ⟨ρc, henvE⟩
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.mrg e' se2, SStep.ssmrgl hv hstep⟩
    | .inl hve1 =>
      have henv' : ∃ ρc', elabExp Typ.top (.mrg v se1) (Typ.and _ _) ρc' :=
        ⟨_, elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henvE hv _) (elab_value_weaken h1 hve1 _)⟩
      have prog2 := ih2 (Value.vmrg hv hve1) henv'
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mrg se1 e', SStep.ssmrgr hv hve1 hstep⟩
      | .inl hve2 => left; exact Value.vmrg hve1 hve2
  | @eproj _ _ _ se _ _ h1 hlook ih =>
    intro v hv henv
    have prog1 := ih hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.proj e' _, SStep.ssproj hv hstep⟩
    | .inl hve1 =>
      right
      have ⟨v', hlv⟩ := elab_lookup_prog hlook (elab_value_weaken h1 hve1 _) hve1
      exact ⟨_, SStep.ssprojv hv hve1 hlv⟩
  | @elrec _ _ se _ l _ ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact Value.vlrec hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨.lrec l e', SStep.sslrec hv hstep⟩
  | @erproj _ _ _ se _ _ h1 hlook ih =>
    intro v hv henv
    have prog1 := ih hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.rproj e' _, SStep.ssrproj hv hstep⟩
    | .inl hve1 =>
      right
      have ⟨v', hsel⟩ := elab_rlookup_prog hlook (elab_value_weaken h1 hve1 _) hve1
      exact ⟨_, SStep.ssrprojv hv hve1 hsel⟩
  | @enmrg _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.nmrg e' se2, SStep.ssnmrgl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.nmrg se1 e', SStep.ssnmrgr hv hve1 hstep⟩
      | .inl hve2 => right; exact ⟨.mrg se1 se2, SStep.ssnmrgv hv hve1 hve2⟩
  | @letb _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.letb e' se2, SStep.ssletbl hv hstep⟩
    | .inl hve1 => right; exact ⟨.box (.mrg v se1) se2, SStep.ssletbv hv hve1⟩
  | @openm _ _ _ se1 se2 _ _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.openm e' se2, SStep.ssopenml hv hstep⟩
    | .inl hve1 =>
      right
      match hve1 with
      | .vlrec hv' => exact ⟨.box (.mrg v _) se2, SStep.ssopenm hv hv'⟩
      | .vint => nomatch h1
      | .vunit => nomatch h1
      | .vmrg _ _ => nomatch h1
      | .vclos _ => nomatch h1
      | .vmclos _ => nomatch h1
      | .vinl _ => nomatch h1
      | .vinr _ => nomatch h1
      | .vfclos _ => nomatch h1
  | @mstruct _ ctxInner _ sb se _ _ hsb_sand hsb_open h ih =>
    intro v hv henv
    cases sb with
    | sandboxed =>
      have heq := hsb_sand rfl; subst heq
      have prog := ih Value.vunit ⟨_, elabExp.eunit _⟩
      match prog with
      | .inl hve => right; exact ⟨_, SStep.ssmstructv_sandboxed hv hve⟩
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mstruct .sandboxed e', SStep.ssmstruct_sandboxed hv hstep⟩
    | open_ =>
      have heq := hsb_open rfl; subst heq
      have prog := ih hv henv
      match prog with
      | .inl hve => right; exact ⟨_, SStep.ssmstructv_open hv hve⟩
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mstruct .open_ e', SStep.ssmstruct_open hv hstep⟩
  | @mfunctor _ ctxInner _ _ sb se _ hsb_sand hsb_open h ih =>
    intro v hv henv
    cases sb with
    | sandboxed => right; exact ⟨_, SStep.ssmfunctor_sandboxed hv⟩
    | open_ => right; exact ⟨_, SStep.ssmfunctor_open hv⟩
  | @mapp _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.mapp e' se2, SStep.ssmappl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mapp se1 e', SStep.ssmappr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        match hve1 with
        | .vmclos hvc => match h1 with
          | .mclos _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, SStep.ssmbeta hv hve2 hvc⟩
        | .vint => nomatch h1
        | .vunit => nomatch h1
        | .vmrg _ _ => nomatch h1
        | .vclos _ => nomatch h1
        | .vlrec _ => nomatch h1
        | .vinl _ => nomatch h1
        | .vinr _ => nomatch h1
        | .vfclos _ => nomatch h1
  | @mlink _ _ _ _ l se1 se2 _ _ h1 h2 hlook ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.mlink e' se2, SStep.ssmlinkl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mlink se1 e', SStep.ssmlinkr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        match hve2 with
        | .vmclos hvc =>
          cases h2 with
          | mclos _ _ _ _ _ _ _ _ _ _ _ =>
            have ⟨vl, hsel⟩ := elab_rlookup_prog hlook (elab_value_weaken h1 hve1 _) hve1
            exact ⟨_, SStep.ssmlinkbeta hv hve1 hvc hsel⟩
        | .vint => nomatch h2
        | .vunit => nomatch h2
        | .vmrg _ _ => nomatch h2
        | .vclos _ => nomatch h2
        | .vlrec _ => nomatch h2
        | .vinl _ => nomatch h2
        | .vinr _ => nomatch h2
        | .vfclos _ => nomatch h2
  | @mlinkn _ _ _ _ se1 se2 _ _ h1 h2 hok ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.mlinkn e' se2, SStep.ssmlinknl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mlinkn se1 e', SStep.ssmlinknr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        match hve2 with
        | .vmclos hvc =>
          cases h2 with
          | mclos _ _ _ _ _ _ _ _ _ _ _ =>
            have ⟨pkg, hsp⟩ := selpkg_prog hok (elab_value_weaken h1 hve1 _) hve1
            exact ⟨_, SStep.ssmlinknbeta hv hve1 hvc hsp⟩
        | .vint => nomatch h2
        | .vunit => nomatch h2
        | .vmrg _ _ => nomatch h2
        | .vclos _ => nomatch h2
        | .vlrec _ => nomatch h2
        | .vinl _ => nomatch h2
        | .vinr _ => nomatch h2
        | .vfclos _ => nomatch h2
        | .vfold _ => nomatch h2
  | @einl _ _ _ se _ h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact Value.vinl hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssinl hv hstep⟩
  | @einr _ _ _ se _ h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact Value.vinr hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssinr hv hstep⟩
  | @ecase _ _ _ _ se se1 se2 _ _ _ h h1 h2 ih ih1 ih2 =>
    intro v hv henv
    right
    have prog := ih hv henv
    match prog with
    | .inr ⟨e', hstep⟩ => exact ⟨_, SStep.sscase hv hstep⟩
    | .inl hve =>
      match hve with
      | .vinl hv1 => exact ⟨_, SStep.sscasel hv hv1⟩
      | .vinr hv1 => exact ⟨_, SStep.sscaser hv hv1⟩
      | .vint => nomatch h
      | .vunit => nomatch h
      | .vclos _ => nomatch h
      | .vmclos _ => nomatch h
      | .vmrg _ _ => nomatch h
      | .vlrec _ => nomatch h
      | .vfclos _ => nomatch h
  | @eflam _ _ _ se _ h ih =>
    intro v hv henv
    right
    exact ⟨_, SStep.ssfclos hv⟩
  | @efclos _ _ _ _ se1 _ _ _ hval _ _ =>
    intro v hv _; left; exact Value.vfclos hval
  | @efold _ _ se _ h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact Value.vfold hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssfold hv hstep⟩
  | @eunfold _ _ _ se _ h heq ih =>
    intro v hv henv
    right
    have prog := ih hv henv
    match prog with
    | .inr ⟨e', hstep⟩ => exact ⟨_, SStep.ssunfold hv hstep⟩
    | .inl hve =>
      match hve with
      | .vfold hv1 => exact ⟨_, SStep.ssunfoldv hv hv1⟩
      | .vint => nomatch h
      | .vunit => nomatch h
      | .vclos _ => nomatch h
      | .vmclos _ => nomatch h
      | .vmrg _ _ => nomatch h
      | .vlrec _ => nomatch h
      | .vinl _ => nomatch h
      | .vinr _ => nomatch h
      | .vfclos _ => nomatch h

-- Whole-program progress
theorem sprogress {e : SCE.Exp} {A : SCE.Typ}
    : (∃ ce, elabExp SCE.Typ.top e A ce)
    → SCE.Value e ∨ ∃ e', SStep SCE.Exp.unit e e' := by
  intro htyp
  exact sgprogress htyp Value.vunit ⟨_, elabExp.eunit _⟩

-- ════════════════════════════════════════════════════════════════════════════════════
-- Phase 2: progress re-witnessed by the sealing elaboration (elabSeal, SCE → λE^≤).
-- The elabExp-witnessed sgprogress above is superseded and will be deleted with Core.
-- ════════════════════════════════════════════════════════════════════════════════════

namespace Seal

variable {Δ : SCE.BrandStore}

-- The source sealing coercion is total on well-elaborated values (mirror of the
-- target's sealv_progress, structural on the signature).  int/top/brand/and/rcd go by
-- elaboration inversion; arr/sig/var/mu are immediate (the coercion is a proxy or the
-- identity there); unions split on the tag.  Bare-interface and nested-arrow signatures
-- are vacuous: no elaboration rule types a value there.
theorem source_ssealv_prog {n : Nat} {R : SCE.Typ} : (S : SCE.Typ) →
    ∀ {Γ : SCE.Typ} {v : SCE.Exp} {ce : Seal.Exp},
    SCE.Value v → elabSeal Δ Γ v (SCE.substBrand n R S) ce
    → ∃ w, S_Sem.SSealV n R S v w
  | .int => fun hv helab => by
    simp only [SCE.substBrand] at helab
    cases hv
    case vint => exact ⟨_, S_Sem.SSealV.int⟩
    all_goals nomatch helab
  | .top => fun _ _ => ⟨_, S_Sem.SSealV.top⟩
  | .brand m => fun _ _ => by
    by_cases hm : m = n
    · subst hm; exact ⟨_, S_Sem.SSealV.brand_eq⟩
    · exact ⟨_, S_Sem.SSealV.brand_ne hm⟩
  | .arr A B => fun _ _ => ⟨_, S_Sem.SSealV.arr⟩
  | .and A B => fun hv helab => by
    simp only [SCE.substBrand] at helab
    cases hv
    case vmrg hv₁ hv₂ =>
      cases helab with
      | edmrg h₁ h₂ _ _ =>
        obtain ⟨w₁, hw₁⟩ := source_ssealv_prog A hv₁ h₁
        obtain ⟨w₂, hw₂⟩ := source_ssealv_prog B hv₂ h₂
        exact ⟨_, S_Sem.SSealV.and hw₁ hw₂⟩
      | evmrg _ _ h₁ h₂ _ =>
        obtain ⟨w₁, hw₁⟩ := source_ssealv_prog A hv₁ h₁
        obtain ⟨w₂, hw₂⟩ := source_ssealv_prog B hv₂ h₂
        exact ⟨_, S_Sem.SSealV.and hw₁ hw₂⟩
    all_goals nomatch helab
  | .rcd l A => fun hv helab => by
    simp only [SCE.substBrand] at helab
    cases hv
    case vlrec hv' =>
      cases helab with
      | elrec h' =>
        obtain ⟨w, hw⟩ := source_ssealv_prog A hv' h'
        exact ⟨_, S_Sem.SSealV.rcd hw⟩
    all_goals nomatch helab
  | .or A B => fun hv helab => by
    simp only [SCE.substBrand] at helab
    cases hv
    case vinl hv' =>
      cases helab with
      | einl h' =>
        obtain ⟨w, hw⟩ := source_ssealv_prog A hv' h'
        exact ⟨_, S_Sem.SSealV.inl hw⟩
    case vinr hv' =>
      cases helab with
      | einr h' =>
        obtain ⟨w, hw⟩ := source_ssealv_prog B hv' h'
        exact ⟨_, S_Sem.SSealV.inr hw⟩
    all_goals nomatch helab
  | .var m => fun _ _ => ⟨_, S_Sem.SSealV.var⟩
  | .mu T => fun _ _ => ⟨_, S_Sem.SSealV.mu⟩
  | .sig (.TyIntf T) => fun hv helab => by
    simp only [SCE.substBrand, SCE.substBrandModTyp] at helab
    exact (value_elab_sig_intf helab hv).elim
  | .sig (.TyArrM A (.TyIntf B)) => fun _ _ => ⟨_, S_Sem.SSealV.sig⟩
  | .sig (.TyArrM A (.TyArrM B mt)) => fun hv helab => by
    simp only [SCE.substBrand, SCE.substBrandModTyp] at helab
    cases hv <;> nomatch helab

-- The converse coercion is total as well (mirror of unsealv_progress).
theorem source_sunsealv_prog {n : Nat} {R : SCE.Typ} : (S : SCE.Typ) →
    ∀ {Γ : SCE.Typ} {v : SCE.Exp} {ce : Seal.Exp},
    SCE.Value v → elabSeal Δ Γ v S ce
    → ∃ w, S_Sem.SUnsealV n R S v w
  | .int => fun hv helab => by
    cases hv
    case vint => exact ⟨_, S_Sem.SUnsealV.int⟩
    all_goals nomatch helab
  | .top => fun _ _ => ⟨_, S_Sem.SUnsealV.top⟩
  | .brand m => fun hv helab => by
    by_cases hm : m = n
    · subst hm
      cases hv with
      | vwrap hv' =>
        cases helab with
        | ewrap _ _ _ => exact ⟨_, S_Sem.SUnsealV.brand_eq⟩
      | vint => nomatch helab
      | vunit => nomatch helab
      | vclos _ => nomatch helab
      | vmclos _ => nomatch helab
      | vmrg _ _ => nomatch helab
      | vlrec _ => nomatch helab
      | vinl _ => nomatch helab
      | vinr _ => nomatch helab
      | vfclos _ => nomatch helab
      | vfold _ => nomatch helab
    · exact ⟨_, S_Sem.SUnsealV.brand_ne hm⟩
  | .arr A B => fun _ _ => ⟨_, S_Sem.SUnsealV.arr⟩
  | .and A B => fun hv helab => by
    cases hv
    case vmrg hv₁ hv₂ =>
      cases helab with
      | edmrg h₁ h₂ _ _ =>
        obtain ⟨w₁, hw₁⟩ := source_sunsealv_prog A hv₁ h₁
        obtain ⟨w₂, hw₂⟩ := source_sunsealv_prog B hv₂ h₂
        exact ⟨_, S_Sem.SUnsealV.and hw₁ hw₂⟩
      | evmrg _ _ h₁ h₂ _ =>
        obtain ⟨w₁, hw₁⟩ := source_sunsealv_prog A hv₁ h₁
        obtain ⟨w₂, hw₂⟩ := source_sunsealv_prog B hv₂ h₂
        exact ⟨_, S_Sem.SUnsealV.and hw₁ hw₂⟩
    all_goals nomatch helab
  | .rcd l A => fun hv helab => by
    cases hv
    case vlrec hv' =>
      cases helab with
      | elrec h' =>
        obtain ⟨w, hw⟩ := source_sunsealv_prog A hv' h'
        exact ⟨_, S_Sem.SUnsealV.rcd hw⟩
    all_goals nomatch helab
  | .or A B => fun hv helab => by
    cases hv
    case vinl hv' =>
      cases helab with
      | einl h' =>
        obtain ⟨w, hw⟩ := source_sunsealv_prog A hv' h'
        exact ⟨_, S_Sem.SUnsealV.inl hw⟩
    case vinr hv' =>
      cases helab with
      | einr h' =>
        obtain ⟨w, hw⟩ := source_sunsealv_prog B hv' h'
        exact ⟨_, S_Sem.SUnsealV.inr hw⟩
    all_goals nomatch helab
  | .var m => fun _ _ => ⟨_, S_Sem.SUnsealV.var⟩
  | .mu T => fun _ _ => ⟨_, S_Sem.SUnsealV.mu⟩
  | .sig (.TyIntf T) => fun hv helab =>
    (value_elab_sig_intf helab hv).elim
  | .sig (.TyArrM A (.TyIntf B)) => fun _ _ => ⟨_, S_Sem.SUnsealV.sig⟩
  | .sig (.TyArrM A (.TyArrM B mt)) => fun hv helab => by
    cases hv <;> nomatch helab

-- ── Generalized progress, elabSeal-witnessed ─────────────────────────────────────────

theorem source_sgprogress {Γ A : SCE.Typ} {e : SCE.Exp}
    (htyp : ∃ ce, elabSeal Δ Γ e A ce) :
    ∀ {v : SCE.Exp},
    SCE.Value v
    → (∃ ρc, elabSeal Δ .top v Γ ρc)
    → SCE.Value e ∨ ∃ e', SStep v e e' := by
  obtain ⟨ce, helab⟩ := htyp
  induction helab with
  | equery =>
    intro v hv _
    right; exact ⟨v, SStep.ssquery hv⟩
  | elit _ _ =>
    intro v hv _
    left; exact SCE.Value.vint
  | eunit _ =>
    intro v hv _
    left; exact SCE.Value.vunit
  | eapp h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssappl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssappr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        cases hve1 with
        | vclos hvc => exact ⟨_, SStep.ssbeta hv hve2 hvc⟩
        | vfclos hvc => exact ⟨_, SStep.ssfbeta hv hve2 hvc⟩
        | vint => nomatch h1
        | vunit => nomatch h1
        | vmrg _ _ => nomatch h1
        | vmclos _ => nomatch h1
        | vlrec _ => nomatch h1
        | vinl _ => nomatch h1
        | vinr _ => nomatch h1
        | vfold _ => nomatch h1
        | vwrap _ => nomatch h1
  | eproj h1 hlook ih =>
    intro v hv henv
    have prog1 := ih hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssproj hv hstep⟩
    | .inl hve1 =>
      right
      have ⟨v', hlv⟩ := elabSeal_lookup_prog hlook h1 hve1
      exact ⟨_, SStep.ssprojv hv hve1 hlv⟩
  | ebox h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssboxl hv hstep⟩
    | .inl hve1 =>
      have prog2 := ih2 hve1 ⟨_, elabSeal_weaken h1 hve1 .top⟩
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssboxr hv hve1 hstep⟩
      | .inl hve2 => right; exact ⟨_, SStep.ssboxv hv hve1 hve2⟩
  | edmrg h1 h2 hd1 hd2 ih1 ih2 =>
    intro v hv henv
    obtain ⟨ρc, henvE⟩ := henv
    have prog1 := ih1 hv ⟨ρc, henvE⟩
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmrgl hv hstep⟩
    | .inl hve1 =>
      have prog2 := ih2 (SCE.Value.vmrg hv hve1)
        ⟨_, elabSeal.evmrg hv hve1 henvE (elabSeal_weaken h1 hve1 .top) (disj_symm hd1)⟩
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmrgr hv hve1 hstep⟩
      | .inl hve2 => left; exact SCE.Value.vmrg hve1 hve2
  | evmrg hv1 hv2 h1 h2 hd ih1 ih2 =>
    intro v hv henv
    left; exact SCE.Value.vmrg hv1 hv2
  | enmrg h1 h2 hd1 hd2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssnmrgl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssnmrgr hv hve1 hstep⟩
      | .inl hve2 => right; exact ⟨_, SStep.ssnmrgv hv hve1 hve2⟩
  | elam h1 hd =>
    intro v hv _
    right; exact ⟨_, SStep.ssclos hv⟩
  | erproj h1 hlook ih =>
    intro v hv henv
    have prog1 := ih hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssrproj hv hstep⟩
    | .inl hve1 =>
      right
      have ⟨v', hsel⟩ := elabSeal_sel_prog hlook h1 hve1
      exact ⟨_, SStep.ssrprojv hv hve1 hsel⟩
  | eclos hval h1 h2 hd ih1 ih2 =>
    intro v hv _
    left; exact SCE.Value.vclos hval
  | elrec h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact SCE.Value.vlrec hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.sslrec hv hstep⟩
  | eletb h1 h2 hd ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssletbl hv hstep⟩
    | .inl hve1 => right; exact ⟨_, SStep.ssletbv hv hve1⟩
  | eopenm h1 h2 hd ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssopenml hv hstep⟩
    | .inl hve1 =>
      right
      cases hve1 with
      | vlrec hv' => exact ⟨_, SStep.ssopenm hv hv'⟩
      | vint => nomatch h1
      | vunit => nomatch h1
      | vmrg _ _ => nomatch h1
      | vclos _ => nomatch h1
      | vmclos _ => nomatch h1
      | vinl _ => nomatch h1
      | vinr _ => nomatch h1
      | vfclos _ => nomatch h1
      | vfold _ => nomatch h1
      | vwrap _ => nomatch h1
  | einl h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact SCE.Value.vinl hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssinl hv hstep⟩
  | einr h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact SCE.Value.vinr hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssinr hv hstep⟩
  | ecase h h1 h2 hd1 hd2 ih ih1 ih2 =>
    intro v hv henv
    right
    have prog := ih hv henv
    match prog with
    | .inr ⟨e', hstep⟩ => exact ⟨_, SStep.sscase hv hstep⟩
    | .inl hve =>
      cases hve with
      | vinl hv1 => exact ⟨_, SStep.sscasel hv hv1⟩
      | vinr hv1 => exact ⟨_, SStep.sscaser hv hv1⟩
      | vint => nomatch h
      | vunit => nomatch h
      | vclos _ => nomatch h
      | vmclos _ => nomatch h
      | vmrg _ _ => nomatch h
      | vlrec _ => nomatch h
      | vfclos _ => nomatch h
      | vfold _ => nomatch h
      | vwrap _ => nomatch h
  | eflam h hd1 hd2 ih =>
    intro v hv _
    right; exact ⟨_, SStep.ssfclos hv⟩
  | efclos hval h1 h2 hd1 hd2 ih1 ih2 =>
    intro v hv _
    left; exact SCE.Value.vfclos hval
  | efold h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact SCE.Value.vfold hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssfold hv hstep⟩
  | eunfold h heq ih =>
    intro v hv henv
    right
    have prog := ih hv henv
    match prog with
    | .inr ⟨e', hstep⟩ => exact ⟨_, SStep.ssunfold hv hstep⟩
    | .inl hve =>
      cases hve with
      | vfold hv1 => exact ⟨_, SStep.ssunfoldv hv hv1⟩
      | vint => nomatch h
      | vunit => nomatch h
      | vclos _ => nomatch h
      | vmclos _ => nomatch h
      | vmrg _ _ => nomatch h
      | vlrec _ => nomatch h
      | vinl _ => nomatch h
      | vinr _ => nomatch h
      | vfclos _ => nomatch h
      | vwrap _ => nomatch h
  | @emstruct _ ctxInner _ sb _ _ hsb hop h ih =>
    intro v hv henv
    cases sb with
    | sandboxed =>
      have heq := hsb rfl; subst heq
      have prog := ih SCE.Value.vunit ⟨_, elabSeal.eunit .top⟩
      match prog with
      | .inl hve => right; exact ⟨_, SStep.ssmstructv_sandboxed hv hve⟩
      | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmstruct_sandboxed hv hstep⟩
    | open_ =>
      have heq := hop rfl; subst heq
      have prog := ih hv henv
      match prog with
      | .inl hve => right; exact ⟨_, SStep.ssmstructv_open hv hve⟩
      | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmstruct_open hv hstep⟩
  | @emfunctor _ ctxInner _ _ sb _ _ hsb hop hdop h ih =>
    intro v hv henv
    cases sb with
    | sandboxed => right; exact ⟨_, SStep.ssmfunctor_sandboxed hv⟩
    | open_ => right; exact ⟨_, SStep.ssmfunctor_open hv⟩
  | emclos hval h1 h2 hd ih1 ih2 =>
    intro v hv _
    left; exact SCE.Value.vmclos hval
  | emapp h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmappl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmappr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        cases hve1 with
        | vmclos hvc => exact ⟨_, SStep.ssmbeta hv hve2 hvc⟩
        | vint => nomatch h1
        | vunit => nomatch h1
        | vmrg _ _ => nomatch h1
        | vclos _ => nomatch h1
        | vlrec _ => nomatch h1
        | vinl _ => nomatch h1
        | vinr _ => nomatch h1
        | vfclos _ => nomatch h1
        | vfold _ => nomatch h1
        | vwrap _ => nomatch h1
  | emlink h1 h2 hlook hd1 hd2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmlinkl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmlinkr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        cases hve2 with
        | vmclos hvc =>
          cases h2 with
          | emclos _ _ _ _ =>
            have ⟨vl, hsel⟩ := elabSeal_sel_prog hlook h1 hve1
            exact ⟨_, SStep.ssmlinkbeta hv hve1 hvc hsel⟩
        | vint => nomatch h2
        | vunit => nomatch h2
        | vmrg _ _ => nomatch h2
        | vclos _ => nomatch h2
        | vlrec _ => nomatch h2
        | vinl _ => nomatch h2
        | vinr _ => nomatch h2
        | vfclos _ => nomatch h2
        | vfold _ => nomatch h2
        | vwrap _ => nomatch h2
  | emlinkn h1 h2 hwire hd1 hd2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmlinknl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssmlinknr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        cases hve2 with
        | vmclos hvc =>
          cases h2 with
          | emclos _ _ _ _ =>
            have ⟨pkg, hsp⟩ := elabSeal_selpkg_prog hwire h1 hve1
            exact ⟨_, SStep.ssmlinknbeta hv hve1 hvc hsp⟩
        | vint => nomatch h2
        | vunit => nomatch h2
        | vmrg _ _ => nomatch h2
        | vclos _ => nomatch h2
        | vlrec _ => nomatch h2
        | vinl _ => nomatch h2
        | vinr _ => nomatch h2
        | vfclos _ => nomatch h2
        | vfold _ => nomatch h2
        | vwrap _ => nomatch h2
  | ewrap hΔ hv' h ih =>
    intro v hv _
    left; exact SCE.Value.vwrap hv'
  | emseal hΔ hnr hwf h ih =>
    intro v hv henv
    right
    have prog := ih hv henv
    match prog with
    | .inr ⟨e', hstep⟩ => exact ⟨_, SStep.ssmseal hv hstep⟩
    | .inl hve =>
      obtain ⟨w, hw⟩ := source_ssealv_prog _ hve h
      exact ⟨_, SStep.ssmsealv hv hve hw⟩
  | emunseal hΔ hnr hwf h heq ih =>
    intro v hv henv
    right
    have prog := ih hv henv
    match prog with
    | .inr ⟨e', hstep⟩ => exact ⟨_, SStep.ssmunseal hv hstep⟩
    | .inl hve =>
      obtain ⟨w, hw⟩ := source_sunsealv_prog _ hve h
      exact ⟨_, SStep.ssmunsealv hv hve hw⟩

-- Whole-program progress, elabSeal-witnessed.
theorem source_sprogress {e : SCE.Exp} {A : SCE.Typ}
    (htyp : ∃ ce, elabSeal Δ .top e A ce)
    : SCE.Value e ∨ ∃ e', SStep SCE.Exp.unit e e' :=
  source_sgprogress htyp SCE.Value.vunit ⟨_, elabSeal.eunit .top⟩

end Seal

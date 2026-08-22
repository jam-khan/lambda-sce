import LeanSce.SCE.Elaboration
import LeanSce.SCE.SmallStep
import LeanSce.SCE.Syntax
import LeanSce.Seal.Elaboration
import LeanSce.Seal.Preservation

open SCE S_Sem

-- Source values do not step (any environment).
theorem svalue_not_step {e : SCE.Exp} (hv : SCE.Value e) : ∀ {v e' : SCE.Exp}, SStep v e e' → False := by
  induction hv with
  | vint => intro v e' hs; nomatch hs
  | vunit => intro v e' hs; nomatch hs
  | vclos _ => intro v e' hs; nomatch hs
  | vmclos _ => intro v e' hs; nomatch hs
  | vmrg _ _ ih₁ ih₂ =>
    intro v e' hs
    cases hs with
    | ssmrgl _ hs₁ => exact ih₁ hs₁
    | ssmrgr _ _ hs₂ => exact ih₂ hs₂
  | vlrec _ ih =>
    intro v e' hs
    cases hs with
    | sslrec _ hs' => exact ih hs'
  | vinl _ ih =>
    intro v e' hs
    cases hs with
    | ssinl _ hs' => exact ih hs'
  | vinr _ ih =>
    intro v e' hs
    cases hs with
    | ssinr _ hs' => exact ih hs'
  | vfclos _ => intro v e' hs; nomatch hs
  | vfold _ ih =>
    intro v e' hs
    cases hs with
    | ssfold _ hs' => exact ih hs'
  | vwrap _ ih =>
    intro v e' hs
    cases hs with
    | sswrap _ hs' => exact ih hs'

-- Value weakening: well-elaborated values can be retyped under any context
theorem elab_value_weaken
    {Γ A : SCE.Typ} {v : SCE.Exp} {ce : Core.Exp}
    (helab : elabExp Γ v A ce)
    (hv : SCE.Value v)
    (Γ' : SCE.Typ) : elabExp Γ' v A ce := by
  induction helab generalizing Γ' with
  | equery => cases hv
  | elit => exact elabExp.elit _ _
  | eunit => exact elabExp.eunit _
  | eapp _ => cases hv
  | eproj _=> cases hv
  | ebox _ => cases hv
  | elam _ => cases hv
  | erproj _ => cases hv
  | letb _ => cases hv
  | openm _ => cases hv
  | mstruct _ => cases hv
  | mfunctor _ => cases hv
  | mapp _ => cases hv
  | mlink _ => cases hv
  | mlinkn _ => cases hv
  | enmrg _ => cases hv
  | ecase _ => cases hv
  | eflam _ => cases hv
  | efclos _ _ _ _ _ _ _ _ hval ht hb ih1 ih2 =>
    cases hv with
    | vfclos hv' => exact elabExp.efclos _ _ _ _ _ _ _ _ hval ht hb
  | eunfold _ => cases hv
  | efold _ _ _ _ _ ih =>
    cases hv with
    | vfold hv' => exact elabExp.efold _ _ _ _ (ih hv' _)
  | einl _ _ _ _ _ _ ih =>
    cases hv with
    | vinl hv' => exact elabExp.einl _ _ _ _ _ (ih hv' _)
  | einr _ _ _ _ _ _ ih =>
    cases hv with
    | vinr hv' => exact elabExp.einr _ _ _ _ _ (ih hv' _)
  | edmrg _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    cases hv with
    | vmrg hv1 hv2 =>
      exact elabExp.edmrg _ _ _ _ _ _ _ (ih1 hv1 _) (ih2 hv2 _)
  | elrec _ _ _ _ _ _ ih =>
    cases hv with
    | vlrec hv' => exact elabExp.elrec _ _ _ _ _ (ih hv' _)
  | eclos _ _ _ _ _ _ _ _ hval ht hb ih1 ih2 =>
    cases hv with
    | vclos hv' => exact elabExp.eclos _ _ _ _ _ _ _ _ hval ht hb
  | mclos _ _ _ _ _ _ _ _ hval ht hb ih1 ih2 =>
    cases hv with
    | vmclos hv' => exact elabExp.mclos _ _ _ _ _ _ _ _ hval ht hb

-- SCE LookupV preserves values
theorem sce_lookupv_value {v v' : SCE.Exp} {n : Nat}
    (hlook : S_Sem.LookupV v n v')
    (hv : SCE.Value v) : SCE.Value v' := by
  induction hlook with
  | dmrg_zero => cases hv; assumption
  | dmrg_succ _ ih => cases hv; exact ih (by assumption)
  | nmrg_zero => cases hv
  | nmrg_succ _ ih => cases hv

-- Lookup preservation for elaboration
theorem elab_lookup_pres {Γ B : SCE.Typ} {n : Nat}
    (hlook : SLookup Γ n B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp} {v' : SCE.Exp},
    S_Sem.LookupV v n v'
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ ce
    → ∃ ce', elabExp Γ v' B ce' := by
  induction hlook with
  | zero =>
    intro v ce v' hlv hv helab
    cases hlv with
    | dmrg_zero =>
      cases hv with
      | vmrg hv1 hv2 =>
        cases helab with
        | edmrg _ _ _ _ _ _ _ h1 h2 =>
          exact ⟨_, elab_value_weaken h2 hv2 _⟩
    | nmrg_zero => cases hv
  | succ _ _ _ _ _ ih =>
    intro v ce v' hlv hv helab
    cases hlv with
    | dmrg_succ hlv' =>
      cases hv with
      | vmrg hv1 hv2 =>
        cases helab with
        | edmrg _ _ _ _ _ _ _ h1 h2 =>
          have ⟨ce', hce'⟩ := ih hlv' hv1 (elab_value_weaken h1 hv1 _)
          have hv' := sce_lookupv_value hlv' hv1
          exact ⟨_, elab_value_weaken hce' hv' _⟩
    | nmrg_succ => cases hv

-- SCE Sel preserves values
theorem sce_sel_value {v v' : SCE.Exp} {l : String}
    (hsel : S_Sem.Sel v l v')
    (hv : SCE.Value v) : SCE.Value v' := by
  induction hsel with
  | rcd => cases hv; assumption
  | dmrg_left _ ih => cases hv; exact ih (by assumption)
  | dmrg_right _ ih => cases hv; exact ih (by assumption)
  | nmrg_left _ ih => cases hv
  | nmrg_right _ ih => cases hv

-- If a value elaborates at type A and label l is not in A, then Sel v l v' is impossible
theorem elab_notin_sel_false
    {l : String} {v v' : SCE.Exp}
    (hsel : S_Sem.Sel v l v')
    (hv : SCE.Value v)
    {A : SCE.Typ}
    (hnotin : ¬LabelIn l A)
    {ce : Core.Exp}
    (helab : elabExp SCE.Typ.top v A ce) : False := by
  induction hsel generalizing A ce with
  | rcd =>
    cases hv with
    | vlrec hv' =>
      cases helab with
      | elrec => exact hnotin (LabelIn.rcd _ _)
  | dmrg_left hsel' ih =>
    cases hv with
    | vmrg hv1 hv2 =>
      cases helab with
      | edmrg _ _ _ _ _ _ _ h1 h2 =>
        exact ih hv1 (fun hlin => hnotin (LabelIn.andl _ _ _ hlin)) (elab_value_weaken h1 hv1 _)
  | dmrg_right hsel' ih =>
    cases hv with
    | vmrg hv1 hv2 =>
      cases helab with
      | edmrg _ _ _ _ _ _ _ h1 h2 =>
        exact ih hv2 (fun hlin => hnotin (LabelIn.andr _ _ _ hlin)) (elab_value_weaken h2 hv2 _)
  | nmrg_left _ ih => cases hv
  | nmrg_right _ ih => cases hv

-- Record lookup preservation for elaboration
theorem elab_rlookup_pres {Γ B : SCE.Typ} {l : String}
    (hlook : SRLookup Γ l B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp} {v' : SCE.Exp},
    S_Sem.Sel v l v'
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ ce
    → ∃ ce', elabExp Γ v' B ce' := by
  induction hlook with
  | zero =>
    intro v ce v' hsel hv helab
    cases helab <;> cases hv
    rename_i v₀ ce₀ h1 hv'
    cases hsel with
    | rcd => exact ⟨_, elab_value_weaken h1 hv' _⟩
  | andl _ _ _ _ _ _ ih =>
    intro v ce v' hsel hv helab
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    cases hsel with
    | dmrg_left hsel' =>
      have ⟨ce', hce'⟩ := ih hsel' hv1 (elab_value_weaken h1 hv1 _)
      exact ⟨_, elab_value_weaken hce' (sce_sel_value hsel' hv1) _⟩
    | dmrg_right hsel' =>
      rename_i hrl hnotin
      exact (elab_notin_sel_false hsel' hv2 hnotin (elab_value_weaken h2 hv2 _)).elim
  | andr _ _ _ _ _ _ ih =>
    intro v ce v' hsel hv helab
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    cases hsel with
    | dmrg_right hsel' =>
      have ⟨ce', hce'⟩ := ih hsel' hv2 (elab_value_weaken h2 hv2 _)
      exact ⟨_, elab_value_weaken hce' (sce_sel_value hsel' hv2) _⟩
    | dmrg_left hsel' =>
      rename_i hrl hnotin
      exact (elab_notin_sel_false hsel' hv1 hnotin (elab_value_weaken h1 hv1 _)).elim
  -- No value elaborates at `sig` over an interface: every module-typed value is
  -- an `mclos`, whose type is a `TyArrM`.  The case is vacuous.
  | sig _ _ _ _ _ih =>
    intro v ce v' hsel hv helab
    cases helab <;> cases hv

-- Lookup progress for elaboration
theorem elab_lookup_prog {A B : SCE.Typ} {n : Nat}
    (hlook : SLookup A n B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp},
    elabExp SCE.Typ.top v A ce
    → SCE.Value v
    → ∃ v', S_Sem.LookupV v n v' := by
  induction hlook with
  | zero =>
    intro v ce helab hv
    cases helab <;> cases hv
    exact ⟨_, LookupV.dmrg_zero⟩
  | succ _ _ _ _ _ ih =>
    intro v ce helab hv
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    have ⟨v', hlv⟩ := ih (elab_value_weaken h1 hv1 _) hv1
    exact ⟨_, LookupV.dmrg_succ hlv⟩

-- Record lookup progress for elaboration
theorem elab_rlookup_prog {A B : SCE.Typ} {l : String}
    (hlook : SRLookup A l B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp},
    elabExp SCE.Typ.top v A ce
    → SCE.Value v
    → ∃ v', S_Sem.Sel v l v' := by
  induction hlook with
  | zero =>
    intro v ce helab hv
    cases helab <;> cases hv
    · exact ⟨_, Sel.rcd⟩
  | andl _ _ _ _ _ _ ih =>
    intro v ce helab hv
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    have ⟨v', hsel⟩ := ih (elab_value_weaken h1 hv1 _) hv1
    exact ⟨_, Sel.dmrg_left hsel⟩
  | andr _ _ _ _ _ _ ih =>
    intro v ce helab hv
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    have ⟨v', hsel⟩ := ih (elab_value_weaken h2 hv2 _) hv2
    exact ⟨_, Sel.dmrg_right hsel⟩
  -- Vacuous, as in `elab_rlookup_pres`.
  | sig _ _ _ _ _ih =>
    intro v ce helab hv
    cases helab <;> cases hv

-- Package extraction progress: every import of D can be selected from a
-- well-elaborated module value
theorem selpkg_prog {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D) :
    ∀ {v : SCE.Exp} {ce : Core.Exp},
    elabExp SCE.Typ.top v Γ₁ ce
    → SCE.Value v
    → ∃ pkg, S_Sem.SelPkg v D pkg := by
  induction hok with
  | one hrl =>
    intro v ce helab hv
    have ⟨vl, hsel⟩ := elab_rlookup_prog hrl helab hv
    exact ⟨_, S_Sem.SelPkg.one hsel⟩
  | more hok' hrl ih =>
    intro v ce helab hv
    have ⟨pkg, hsp⟩ := ih helab hv
    have ⟨vl, hsel⟩ := elab_rlookup_prog hrl helab hv
    exact ⟨_, S_Sem.SelPkg.more hsp hsel⟩

-- Package extraction preservation: the extracted package elaborates at D
theorem selpkg_pres {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D) :
    ∀ {v pkg : SCE.Exp} {ce : Core.Exp},
    S_Sem.SelPkg v D pkg
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ₁ ce
    → ∃ cpkg, elabExp SCE.Typ.top pkg D cpkg := by
  induction hok with
  | one hrl =>
    intro v pkg ce hsp hv helab
    cases hsp with
    | one hsel =>
      have ⟨ce', h⟩ := elab_rlookup_pres hrl hsel hv helab
      have hvl := sce_sel_value hsel hv
      exact ⟨_, elabExp.elrec _ _ _ _ _ (elab_value_weaken h hvl _)⟩
  | more hok' hrl ih =>
    intro v pkg ce hsp hv helab
    cases hsp with
    | more hsp' hsel =>
      have ⟨cpkg, hpkg⟩ := ih hsp' hv helab
      have ⟨ce', h⟩ := elab_rlookup_pres hrl hsel hv helab
      have hvl := sce_sel_value hsel hv
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _ hpkg
        (elab_value_weaken
          (elabExp.elrec SCE.Typ.top _ _ _ _ (elab_value_weaken h hvl SCE.Typ.top))
          (SCE.Value.vlrec hvl) _)⟩

-- Generalized preservation: SCE small steps preserve elaboration types
theorem sgpreservation
    {e e' v : SCE.Exp}
    (hstep : SStep v e e') :
    ∀ {Γ A : SCE.Typ},
    (∃ ce, elabExp Γ e A ce)
    → SCE.Value v
    → (∃ ρc, elabExp SCE.Typ.top v Γ ρc)
    → ∃ ce', elabExp Γ e' A ce' := by
  induction hstep with
  | ssquery hval =>
    intro Γ A ⟨ce, helab⟩ hv ⟨ρc, henv⟩
    cases helab
    exact ⟨ρc, elab_value_weaken henv hv _⟩
  | ssappl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.eapp _ _ _ _ _ _ _ h h2⟩
  | ssboxl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ebox _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.ebox _ _ _ _ _ _ _ h h2⟩
  | ssmrgl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | edmrg _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _ h h2⟩
  | ssappr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.eapp _ _ _ _ _ _ _ h1 h⟩
  | ssboxr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ebox _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hv1 ⟨_, elab_value_weaken h1 hv1 _⟩
      exact ⟨_, elabExp.ebox _ _ _ _ _ _ _ h1 h⟩
  | ssmrgr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval henvex
    obtain ⟨ρc, henv⟩ := henvex
    cases helab with
    | edmrg _ _ _ _ _ _ _ h1 h2 =>
      have h1' := elab_value_weaken h1 hv1 (Typ.and Typ.top Γ)
      have henv' : ∃ ρc, elabExp SCE.Typ.top (.mrg _ _) (Typ.and Γ _) ρc :=
        ⟨_, elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henv hval _) h1'⟩
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ (Value.vmrg hval hv1) henv'
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _ h1 h⟩
  | ssclos hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | elam _ _ _ _ _ h1 =>
      exact ⟨_, elabExp.eclos _ _ _ _ _ _ _ _ hval henv h1⟩
  | ssbeta hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp _ _ _ _ _ _ _ h1 h2 =>
      cases h1 with
      | eclos _ _ _ _ _ _ _ _ hval' ht hb =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken ht hval' _)
            (elab_value_weaken h2 hv1 _))
          hb⟩
  | ssboxv hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ebox _ _ _ _ _ _ _ h1 h2 =>
      exact ⟨_, elab_value_weaken h2 hv2 _⟩
  | ssproj hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eproj _ _ _ _ _ _ h1 hlook =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.eproj _ _ _ _ _ _ h hlook⟩
  | ssprojv hv hv1 hlookv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eproj _ _ _ _ _ _ h1 hlook =>
      have ⟨ce', hce'⟩ := elab_lookup_pres hlook hlookv hv1 (elab_value_weaken h1 hv1 _)
      have hv' := sce_lookupv_value hlookv hv1
      exact ⟨_, elab_value_weaken hce' hv' _⟩
  | sslrec hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | elrec _ _ _ _ _ h1 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.elrec _ _ _ _ _ h⟩
  | ssrproj hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | erproj _ _ _ _ _ _ h1 hlook =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.erproj _ _ _ _ _ _ h hlook⟩
  | ssrprojv hv hv1 hsel =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | erproj _ _ _ _ _ _ h1 hlook =>
      have ⟨ce', hce'⟩ := elab_rlookup_pres hlook hsel hv1 (elab_value_weaken h1 hv1 _)
      have hv' := sce_sel_value hsel hv1
      exact ⟨_, elab_value_weaken hce' hv' _⟩
  | ssmstruct_sandboxed hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab
    rename_i _ _ hsb_sand hsb_open h
    have heq := hsb_sand rfl; subst heq
    have ⟨ce', h'⟩ := ih ⟨_, h⟩ Value.vunit ⟨_, elabExp.eunit _⟩
    exact ⟨_, elabExp.mstruct _ _ _ _ _ _ Core.Exp.unit (fun _ => rfl) hsb_open h'⟩
  | ssmstruct_open hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab
    rename_i _ _ hsb_sand hsb_open h
    have heq := hsb_open rfl; subst heq
    have ⟨ce', h'⟩ := ih ⟨_, h⟩ hval ⟨ρc, henv⟩
    exact ⟨_, elabExp.mstruct _ _ _ _ _ _ Core.Exp.unit hsb_sand (fun _ => rfl) h'⟩
  | ssmstructv_sandboxed hv hv' =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab
    rename_i _ _ _ _ h
    exact ⟨_, elab_value_weaken h hv' _⟩
  | ssmstructv_open hv hv' =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab
    rename_i _ _ _ _ h
    exact ⟨_, elab_value_weaken h hv' _⟩
  | ssmfunctor_sandboxed hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab
    rename_i _ hsb_sand hsb_open h
    have heq := hsb_sand rfl; subst heq
    exact ⟨_, elabExp.mclos _ _ _ _ _ _ _ _ Value.vunit (elabExp.eunit _) h⟩
  | ssmfunctor_open hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab
    rename_i _ hsb_sand hsb_open h
    have heq := hsb_open rfl; subst heq
    exact ⟨_, elabExp.mclos _ _ _ _ _ _ _ _ hval henv h⟩
  | ssmappl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mapp _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mapp _ _ _ _ _ _ _ h h2⟩
  | ssmappr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mapp _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mapp _ _ _ _ _ _ _ h1 h⟩
  | ssmbeta hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mapp _ _ _ _ _ _ _ h1 h2 =>
      cases h1 with
      | mclos _ _ _ _ _ _ _ _ hval' ht hb =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken ht hval' _)
            (elab_value_weaken h2 hv1 _))
          hb⟩
  | ssnmrgl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | enmrg _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.enmrg _ _ _ _ _ _ _ h h2⟩
  | ssnmrgr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | enmrg _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.enmrg _ _ _ _ _ _ _ h1 h⟩
  | ssnmrgv hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | enmrg _ _ _ _ _ _ _ h1 h2 =>
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _
        (elab_value_weaken h1 hv1 _)
        (elab_value_weaken h2 hv2 _)⟩
  | ssletbl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | letb _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.letb _ _ _ _ _ _ _ h h2⟩
  | ssletbv hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | letb _ _ _ _ _ _ _ h1 h2 =>
      exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
        (elabExp.edmrg _ _ _ _ _ _ _
          (elab_value_weaken henv hval _)
          (elab_value_weaken h1 hv1 _))
        h2⟩
  | ssmlinkl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlink _ _ _ _ _ _ _ _ _ h1 h2 hlook =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mlink _ _ _ _ _ _ _ _ _ h h2 hlook⟩
  | ssmlinkr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlink _ _ _ _ _ _ _ _ _ h1 h2 hlook =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mlink _ _ _ _ _ _ _ _ _ h1 h hlook⟩
  | ssmlinkbeta hv hv1 hv2 hsel =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlink _ _ _ _ _ _ _ _ _ h1 h2 hlook =>
      cases h2 with
      | mclos _ _ _ _ _ _ _ _ hval_v2 henv_v2 hbody =>
        have hvl := sce_sel_value hsel hv1
        have ⟨_, helab_vl⟩ := elab_rlookup_pres hlook hsel hv1 (elab_value_weaken h1 hv1 _)
        exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _
          (elab_value_weaken h1 hv1 _)
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _
              (elab_value_weaken henv_v2 hval_v2 _)
              (elabExp.elrec _ _ _ _ _ (elab_value_weaken helab_vl hvl _)))
            hbody)⟩
  | ssopenml hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | openm _ _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.openm _ _ _ _ _ _ _ _ h h2⟩
  | ssopenm hv hv' =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | openm _ _ _ _ _ _ _ _ h1 h2 =>
      cases h1 with
      | elrec _ _ _ _ _ h1_inner =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken henv hval _)
            (elab_value_weaken h1_inner hv' _))
          h2⟩
  | ssinl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | einl _ _ _ _ _ h1 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.einl _ _ _ _ _ h⟩
  | ssinr hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | einr _ _ _ _ _ h1 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.einr _ _ _ _ _ h⟩
  | sscase hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ecase _ _ _ _ _ _ _ _ _ _ h h1 h2 =>
      have ⟨ce', h'⟩ := ih ⟨_, h⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.ecase _ _ _ _ _ _ _ _ _ _ h' h1 h2⟩
  | sscasel hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ecase _ _ _ _ _ _ _ _ _ _ h h1 h2 =>
      cases h with
      | einl _ _ _ _ _ hinner =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken henv hval _)
            (elab_value_weaken hinner hv1 _))
          h1⟩
  | sscaser hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ecase _ _ _ _ _ _ _ _ _ _ h h1 h2 =>
      cases h with
      | einr _ _ _ _ _ hinner =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken henv hval _)
            (elab_value_weaken hinner hv1 _))
          h2⟩
  | ssfclos hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eflam _ _ _ _ _ h1 =>
      exact ⟨_, elabExp.efclos _ _ _ _ _ _ _ _ hval henv h1⟩
  | ssfbeta hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp _ _ _ _ _ _ _ h1 h2 =>
      cases h1 with
      | efclos _ _ _ _ _ _ _ _ hval' ht hb =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _
              (elab_value_weaken ht hval' _)
              (elabExp.efclos _ _ _ _ _ _ _ _ hval' ht hb))
            (elab_value_weaken h2 hv1 _))
          hb⟩
  | ssfold hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | efold _ _ _ _ h1 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.efold _ _ _ _ h⟩
  | ssunfold hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eunfold _ _ _ _ _ h1 heq =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.eunfold _ _ _ _ _ h heq⟩
  | ssunfoldv hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eunfold _ _ _ _ _ h1 heq =>
      subst heq
      cases h1 with
      | efold _ _ _ _ hinner => exact ⟨_, hinner⟩
  -- no Core elaboration rules for the sealing forms (λE has no brands): vacuous
  | sswrap _ _ _ => intro Γ A ⟨ce, helab⟩ _ _; cases helab
  | ssmseal _ _ _ => intro Γ A ⟨ce, helab⟩ _ _; cases helab
  | ssmsealv _ _ _ => intro Γ A ⟨ce, helab⟩ _ _; cases helab
  | ssmunseal _ _ _ => intro Γ A ⟨ce, helab⟩ _ _; cases helab
  | ssmunsealv _ _ _ => intro Γ A ⟨ce, helab⟩ _ _; cases helab
  | ssmlinknl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlinkn _ _ _ _ _ _ _ _ h1 h2 hok =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mlinkn _ _ _ _ _ _ _ _ h h2 hok⟩
  | ssmlinknr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlinkn _ _ _ _ _ _ _ _ h1 h2 hok =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mlinkn _ _ _ _ _ _ _ _ h1 h hok⟩
  | ssmlinknbeta hv hv1 hv2 hsp =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlinkn _ _ _ _ _ _ _ _ h1 h2 hok =>
      cases h2 with
      | mclos _ _ _ _ _ _ _ _ hval_v2 henv_v2 hbody =>
        have ⟨cpkg, hpkg⟩ := selpkg_pres hok hsp hv1 (elab_value_weaken h1 hv1 _)
        have hvpkg := S_Sem.selpkg_value hsp hv1
        exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _
          (elab_value_weaken h1 hv1 _)
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _
              (elab_value_weaken henv_v2 hval_v2 _)
              (elab_value_weaken hpkg hvpkg _))
            hbody)⟩

-- Whole-program preservation
theorem spreservation {e e' : SCE.Exp} {A : SCE.Typ}
    : (∃ ce, elabExp SCE.Typ.top e A ce)
    → SStep SCE.Exp.unit e e'
    → ∃ ce', elabExp SCE.Typ.top e' A ce' := by
  intros htyp hstep
  apply sgpreservation hstep htyp Value.vunit
  exact ⟨_, elabExp.eunit _⟩

-- ════════════════════════════════════════════════════════════════════════════════════
-- Phase 2: the same source metatheory, re-witnessed by the sealing elaboration
-- (elabSeal, SCE → λE^≤).  The elabExp-witnessed results above are superseded by these
-- and will be deleted together with LeanSce/Core once every client is ported.
-- ════════════════════════════════════════════════════════════════════════════════════

namespace Seal

variable {Δ : SCE.BrandStore}

-- Lookup progress: a well-elaborated value at an intersection type has every projection.
theorem elabSeal_lookup_prog {A B : SCE.Typ} {n : Nat} (hl : SCE.SLookup A n B)
    : ∀ {Γ : SCE.Typ} {v : SCE.Exp} {ce : Seal.Exp}, elabSeal Δ Γ v A ce → SCE.Value v
    → ∃ v', S_Sem.LookupV v n v' := by
  induction hl with
  | zero A B =>
    intro Γ v ce helab hv
    cases hv
    case vmrg hv₁ hv₂ => exact ⟨_, S_Sem.LookupV.dmrg_zero⟩
    all_goals nomatch helab
  | succ A B n C _ ih =>
    intro Γ v ce helab hv
    cases hv
    case vmrg hv₁ hv₂ =>
      cases helab with
      | edmrg h₁ h₂ hd₁ hd₂ =>
        obtain ⟨v', hlv⟩ := ih h₁ hv₁
        exact ⟨_, S_Sem.LookupV.dmrg_succ hlv⟩
      | evmrg _ _ h₁ h₂ _ =>
        obtain ⟨v', hlv⟩ := ih h₁ hv₁
        exact ⟨_, S_Sem.LookupV.dmrg_succ hlv⟩
    all_goals nomatch helab

-- Record-lookup progress: every label the type records can be selected.
theorem elabSeal_sel_prog {A B : SCE.Typ} {l : String} (hl : SCE.SRLookup A l B)
    : ∀ {Γ : SCE.Typ} {v : SCE.Exp} {ce : Seal.Exp}, elabSeal Δ Γ v A ce → SCE.Value v
    → ∃ v', S_Sem.Sel v l v' := by
  induction hl with
  | zero label T =>
    intro Γ v ce helab hv
    cases hv
    case vlrec hv' =>
      cases helab with
      | elrec h => exact ⟨_, S_Sem.Sel.rcd⟩
    all_goals nomatch helab
  | andl A' B' label T hl' hnl ih =>
    intro Γ v ce helab hv
    cases hv
    case vmrg hv₁ hv₂ =>
      cases helab with
      | edmrg h₁ h₂ hd₁ hd₂ =>
        obtain ⟨v', hsel⟩ := ih h₁ hv₁
        exact ⟨_, S_Sem.Sel.dmrg_left hsel⟩
      | evmrg _ _ h₁ h₂ _ =>
        obtain ⟨v', hsel⟩ := ih h₁ hv₁
        exact ⟨_, S_Sem.Sel.dmrg_left hsel⟩
    all_goals nomatch helab
  | andr A' B' label T hl' hnl ih =>
    intro Γ v ce helab hv
    cases hv
    case vmrg hv₁ hv₂ =>
      cases helab with
      | edmrg h₁ h₂ hd₁ hd₂ =>
        obtain ⟨v', hsel⟩ := ih h₂ hv₂
        exact ⟨_, S_Sem.Sel.dmrg_right hsel⟩
      | evmrg _ _ h₁ h₂ _ =>
        obtain ⟨v', hsel⟩ := ih h₂ hv₂
        exact ⟨_, S_Sem.Sel.dmrg_right hsel⟩
    all_goals nomatch helab
  -- No value elaborates at a bare interface: vacuous.
  | sig label T A' _ _ =>
    intro Γ v ce helab hv
    exact (value_elab_sig_intf helab hv).elim

-- Package extraction progress, over the disjointness-enriched WireOk (what emlinkn
-- carries; SCE.LinkOk lacks the Disj the elaborated reconstruction needs).
theorem elabSeal_selpkg_prog {Γc : Seal.Typ} {Γ₁ D : SCE.Typ} (hok : WireOk Γc Γ₁ D)
    : ∀ {Γ : SCE.Typ} {v : SCE.Exp} {ce : Seal.Exp}, elabSeal Δ Γ v Γ₁ ce → SCE.Value v
    → ∃ pkg, S_Sem.SelPkg v D pkg := by
  induction hok with
  | one hrl =>
    intro Γ v ce helab hv
    obtain ⟨vl, hsel⟩ := elabSeal_sel_prog hrl helab hv
    exact ⟨_, S_Sem.SelPkg.one hsel⟩
  | more hok' hrl hd₁ hd₂ ih =>
    intro Γ v ce helab hv
    obtain ⟨pkg, hsp⟩ := ih helab hv
    obtain ⟨vl, hsel⟩ := elabSeal_sel_prog hrl helab hv
    exact ⟨_, S_Sem.SelPkg.more hsp hsel⟩

-- Package extraction preservation: the extracted package elaborates at the interface.
-- WireOk.more's second Disj is exactly evmrg's obligation for the accumulated merge.
theorem elabSeal_selpkg_pres {Γc : Seal.Typ} {Γ₁ D : SCE.Typ} (hok : WireOk Γc Γ₁ D)
    : ∀ {Γ : SCE.Typ} {v pkg : SCE.Exp} {ce : Seal.Exp},
    S_Sem.SelPkg v D pkg → SCE.Value v → elabSeal Δ Γ v Γ₁ ce
    → ∃ cpkg, elabSeal Δ .top pkg D cpkg := by
  induction hok with
  | one hrl =>
    intro Γ v pkg ce hsp hv helab
    cases hsp with
    | one hsel =>
      obtain ⟨w, h⟩ := elabSeal_sel_pres hrl helab hv hsel
      exact ⟨_, elabSeal.elrec h⟩
  | more hok' hrl hd₁ hd₂ ih =>
    intro Γ v pkg ce hsp hv helab
    cases hsp with
    | more hsp' hsel =>
      obtain ⟨cpkg, hpkg⟩ := ih hsp' hv helab
      obtain ⟨w, h⟩ := elabSeal_sel_pres hrl helab hv hsel
      have hvl := sce_sel_value hsel hv
      have hvpkg := S_Sem.selpkg_value hsp' hv
      exact ⟨_, elabSeal.evmrg hvpkg (SCE.Value.vlrec hvl) hpkg (elabSeal.elrec h) hd₂⟩

-- ── The source sealing coercions preserve elaboration ────────────────────────────────

-- Sealing a well-elaborated value at signature S re-elaborates at S (mirror of the
-- target's sealv_preservation, at the elabSeal level; structural on SSealV).  The
-- arr/sig cases re-elaborate the source proxies with eclos/emclos — the derivations are
-- exactly the ones eval_sealv builds for its EVal witnesses.
theorem source_ssealv_pres {n : Nat} {R S : SCE.Typ} {v w : SCE.Exp}
    (hs : S_Sem.SSealV n R S v w)
    : ∀ {Γ : SCE.Typ} {ce : Seal.Exp}, Δ n = some R → NoRes (sealTyp R)
    → WfSig n (sealTyp R) (sealTyp S) → SCE.Value v
    → elabSeal Δ Γ v (SCE.substBrand n R S) ce
    → ∃ wc, elabSeal Δ Γ w S wc := by
  induction hs with
  | brand_eq =>
    intro Γ ce hΔ _ _ hv h
    simp only [SCE.substBrand, if_true] at h
    exact ⟨_, elabSeal.ewrap hΔ hv (elabSeal_weaken h hv .top)⟩
  | brand_ne hne =>
    intro Γ ce _ _ _ hv h
    simp only [SCE.substBrand, hne, if_false] at h
    exact ⟨_, h⟩
  | int =>
    intro Γ ce _ _ _ _ _
    exact ⟨_, elabSeal.elit Γ _⟩
  | top =>
    intro Γ ce _ _ _ _ _
    exact ⟨_, elabSeal.eunit Γ⟩
  | @and A B v₁ v₂ w₁ w₂ hs₁ hs₂ ih₁ ih₂ =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | and hwf₁ hwf₂ hd _ =>
      simp only [SCE.substBrand] at h
      cases hv with
      | vmrg hv₁ hv₂ =>
        have hg : ∃ w₁' w₂', elabSeal Δ .top v₁ (SCE.substBrand n R A) w₁'
            ∧ elabSeal Δ .top v₂ (SCE.substBrand n R B) w₂' := by
          cases h with
          | edmrg h₁ h₂ _ _ =>
            exact ⟨_, _, elabSeal_weaken h₁ hv₁ .top, elabSeal_weaken h₂ hv₂ .top⟩
          | evmrg _ _ h₁ h₂ _ => exact ⟨_, _, h₁, h₂⟩
        obtain ⟨w₁', w₂', hw₁, hw₂⟩ := hg
        obtain ⟨wc₁, he₁⟩ := ih₁ hΔ hnr hwf₁ hv₁ hw₁
        obtain ⟨wc₂, he₂⟩ := ih₂ hΔ hnr hwf₂ hv₂ hw₂
        exact ⟨_, elabSeal.evmrg (S_Sem.ssealv_value hv₁ hs₁) (S_Sem.ssealv_value hv₂ hs₂)
          (elabSeal_weaken he₁ (S_Sem.ssealv_value hv₁ hs₁) .top)
          (elabSeal_weaken he₂ (S_Sem.ssealv_value hv₂ hs₂) .top) hd⟩
  | rcd hs' ih =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | rcd _ hwf' =>
      simp only [SCE.substBrand] at h
      cases hv with
      | vlrec hv' =>
        cases h with
        | elrec h' =>
          obtain ⟨wc, he⟩ := ih hΔ hnr hwf' hv' h'
          exact ⟨_, elabSeal.elrec he⟩
  | @arr A B c =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | arr hwfA hwfB =>
      exact ⟨_, elabSeal.eclos (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hv))
        (elabSeal.evmrg SCE.Value.vunit (SCE.Value.vlrec hv) (elabSeal.eunit .top)
          (elabSeal.elrec (elabSeal_weaken h hv .top)) disj_top)
        (elabSeal.emseal hΔ hnr hwfB
          (elabSeal.eapp
            (elabSeal.erproj
              (elabSeal.eproj elabSeal.equery (SCE.SLookup.succ _ _ _ _ (SCE.SLookup.zero _ _)))
              (SCE.SRLookup.zero _ _))
            (elabSeal.emunseal hΔ hnr hwfA
              (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _)) rfl)))
        (disj_proxyEnv (wfsig_nores hwfA))⟩
  | @sig A B c =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | arr hwfA hwfB =>
      exact ⟨_, elabSeal.emclos (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hv))
        (elabSeal.evmrg SCE.Value.vunit (SCE.Value.vlrec hv) (elabSeal.eunit .top)
          (elabSeal.elrec (elabSeal_weaken h hv .top)) disj_top)
        (elabSeal.emseal hΔ hnr hwfB
          (elabSeal.emapp
            (elabSeal.erproj
              (elabSeal.eproj elabSeal.equery (SCE.SLookup.succ _ _ _ _ (SCE.SLookup.zero _ _)))
              (SCE.SRLookup.zero _ _))
            (elabSeal.emunseal hΔ hnr hwfA
              (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _)) rfl)))
        (disj_proxyEnv (wfsig_nores hwfA))⟩
  | @inl A B v' w' _ ih =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | or hwfA hwfB =>
      simp only [SCE.substBrand] at h
      cases hv with
      | vinl hv' =>
        cases h with
        | einl h' =>
          obtain ⟨wc, he⟩ := ih hΔ hnr hwfA hv' h'
          exact ⟨_, elabSeal.einl he⟩
  | @inr A B v' w' _ ih =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | or hwfA hwfB =>
      simp only [SCE.substBrand] at h
      cases hv with
      | vinr hv' =>
        cases h with
        | einr h' =>
          obtain ⟨wc, he⟩ := ih hΔ hnr hwfB hv' h'
          exact ⟨_, elabSeal.einr he⟩
  | var =>
    intro Γ ce _ _ _ _ h
    simp only [SCE.substBrand] at h
    exact ⟨_, h⟩
  | mu =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | mu hnin _ =>
      rw [sce_substBrand_notin hnin] at h
      exact ⟨_, h⟩

-- The converse: unsealing a well-elaborated value at S re-elaborates at the
-- representation view S[n:=R].
theorem source_sunsealv_pres {n : Nat} {R S : SCE.Typ} {v w : SCE.Exp}
    (hs : S_Sem.SUnsealV n R S v w)
    : ∀ {Γ : SCE.Typ} {ce : Seal.Exp}, Δ n = some R → NoRes (sealTyp R)
    → WfSig n (sealTyp R) (sealTyp S) → SCE.Value v
    → elabSeal Δ Γ v S ce
    → ∃ wc, elabSeal Δ Γ w (SCE.substBrand n R S) wc := by
  induction hs with
  | brand_eq =>
    intro Γ ce hΔ _ _ hv h
    cases h with
    | ewrap hΔ' hv' h' =>
      rw [hΔ] at hΔ'
      cases hΔ'
      simp only [SCE.substBrand, if_true]
      exact ⟨_, elabSeal_weaken h' hv' Γ⟩
  | brand_ne hne =>
    intro Γ ce _ _ _ _ h
    simp only [SCE.substBrand, hne, if_false]
    exact ⟨_, h⟩
  | int =>
    intro Γ ce _ _ _ _ _
    exact ⟨_, elabSeal.elit Γ _⟩
  | top =>
    intro Γ ce _ _ _ _ _
    exact ⟨_, elabSeal.eunit Γ⟩
  | @and A B v₁ v₂ w₁ w₂ hs₁ hs₂ ih₁ ih₂ =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | and hwf₁ hwf₂ _ hd =>
      rw [← sealTyp_substBrand, ← sealTyp_substBrand] at hd
      cases hv with
      | vmrg hv₁ hv₂ =>
        have hg : ∃ w₁' w₂', elabSeal Δ .top v₁ A w₁' ∧ elabSeal Δ .top v₂ B w₂' := by
          cases h with
          | edmrg h₁ h₂ _ _ =>
            exact ⟨_, _, elabSeal_weaken h₁ hv₁ .top, elabSeal_weaken h₂ hv₂ .top⟩
          | evmrg _ _ h₁ h₂ _ => exact ⟨_, _, h₁, h₂⟩
        obtain ⟨w₁', w₂', hw₁, hw₂⟩ := hg
        obtain ⟨wc₁, he₁⟩ := ih₁ hΔ hnr hwf₁ hv₁ hw₁
        obtain ⟨wc₂, he₂⟩ := ih₂ hΔ hnr hwf₂ hv₂ hw₂
        simp only [SCE.substBrand]
        exact ⟨_, elabSeal.evmrg (S_Sem.sunsealv_value hv₁ hs₁) (S_Sem.sunsealv_value hv₂ hs₂)
          (elabSeal_weaken he₁ (S_Sem.sunsealv_value hv₁ hs₁) .top)
          (elabSeal_weaken he₂ (S_Sem.sunsealv_value hv₂ hs₂) .top) hd⟩
  | rcd hs' ih =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | rcd _ hwf' =>
      cases hv with
      | vlrec hv' =>
        cases h with
        | elrec h' =>
          obtain ⟨wc, he⟩ := ih hΔ hnr hwf' hv' h'
          simp only [SCE.substBrand]
          exact ⟨_, elabSeal.elrec he⟩
  | @arr A B c =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | arr hwfA hwfB =>
      simp only [SCE.substBrand]
      exact ⟨_, elabSeal.eclos (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hv))
        (elabSeal.evmrg SCE.Value.vunit (SCE.Value.vlrec hv) (elabSeal.eunit .top)
          (elabSeal.elrec (elabSeal_weaken h hv .top)) disj_top)
        (elabSeal.emunseal hΔ hnr hwfB
          (elabSeal.eapp
            (elabSeal.erproj
              (elabSeal.eproj elabSeal.equery (SCE.SLookup.succ _ _ _ _ (SCE.SLookup.zero _ _)))
              (SCE.SRLookup.zero _ _))
            (elabSeal.emseal hΔ hnr hwfA (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _))))
          rfl)
        (by rw [sealTyp_substBrand]
            exact disj_proxyEnv (nores_subst hnr (wfsig_nores hwfA)))⟩
  | @sig A B c =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | arr hwfA hwfB =>
      simp only [SCE.substBrand, SCE.substBrandModTyp]
      exact ⟨_, elabSeal.emclos (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hv))
        (elabSeal.evmrg SCE.Value.vunit (SCE.Value.vlrec hv) (elabSeal.eunit .top)
          (elabSeal.elrec (elabSeal_weaken h hv .top)) disj_top)
        (elabSeal.emunseal hΔ hnr hwfB
          (elabSeal.emapp
            (elabSeal.erproj
              (elabSeal.eproj elabSeal.equery (SCE.SLookup.succ _ _ _ _ (SCE.SLookup.zero _ _)))
              (SCE.SRLookup.zero _ _))
            (elabSeal.emseal hΔ hnr hwfA (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _))))
          rfl)
        (by rw [sealTyp_substBrand]
            exact disj_proxyEnv (nores_subst hnr (wfsig_nores hwfA)))⟩
  | @inl A B v' w' _ ih =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | or hwfA hwfB =>
      cases hv with
      | vinl hv' =>
        cases h with
        | einl h' =>
          obtain ⟨wc, he⟩ := ih hΔ hnr hwfA hv' h'
          simp only [SCE.substBrand]
          exact ⟨_, elabSeal.einl he⟩
  | @inr A B v' w' _ ih =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | or hwfA hwfB =>
      cases hv with
      | vinr hv' =>
        cases h with
        | einr h' =>
          obtain ⟨wc, he⟩ := ih hΔ hnr hwfB hv' h'
          simp only [SCE.substBrand]
          exact ⟨_, elabSeal.einr he⟩
  | var =>
    intro Γ ce _ _ _ _ h
    simp only [SCE.substBrand]
    exact ⟨_, h⟩
  | mu =>
    intro Γ ce hΔ hnr hwf hv h
    cases hwf with
    | mu hnin _ =>
      rw [sce_substBrand_notin hnin]
      exact ⟨_, h⟩

-- ── Generalized preservation: SCE small steps preserve elabSeal types ────────────────

-- The elabSeal port of sgpreservation.  Merge inversions gain the evmrg alternative
-- (discharged by svalue_not_step in congruence cases, used for the value-merge rebuilds
-- everywhere else); the sealing cases are REAL here (the Core elaboration had none).
theorem source_sgpreservation {e e' v : SCE.Exp} (hstep : SStep v e e')
    : ∀ {Γ A : SCE.Typ},
    (∃ ce, elabSeal Δ Γ e A ce)
    → SCE.Value v
    → (∃ ρc, elabSeal Δ .top v Γ ρc)
    → ∃ ce', elabSeal Δ Γ e' A ce' := by
  induction hstep with
  | ssquery hval' =>
    intro Γ A ⟨ce, helab⟩ hv ⟨ρc, henv⟩
    cases helab
    exact ⟨ρc, elabSeal_weaken henv hv Γ⟩
  | ssappl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp h₁ h₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.eapp h h₂⟩
  | ssboxl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ebox h₁ h₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.ebox h h₂⟩
  | ssmrgl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | edmrg h₁ h₂ hd₁ hd₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.edmrg h h₂ hd₁ hd₂⟩
    | evmrg hv₁ _ _ _ _ => exact (svalue_not_step hv₁ hstep).elim
  | ssappr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp h₁ h₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₂⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.eapp h₁ h⟩
  | ssboxr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ebox h₁ h₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₂⟩ hv1 ⟨_, elabSeal_weaken h₁ hv1 .top⟩
      exact ⟨_, elabSeal.ebox h₁ h⟩
  | ssmrgr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | edmrg h₁ h₂ hd₁ hd₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₂⟩ (SCE.Value.vmrg hval hv1)
        ⟨_, elabSeal.evmrg hval hv1 henv (elabSeal_weaken h₁ hv1 .top) (disj_symm hd₁)⟩
      exact ⟨_, elabSeal.edmrg h₁ h hd₁ hd₂⟩
    | evmrg _ hv₂ _ _ _ => exact (svalue_not_step hv₂ hstep).elim
  | ssclos hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | elam h₁ hd => exact ⟨_, elabSeal.eclos hval henv h₁ hd⟩
  | ssbeta hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp h₁ h₂ =>
      cases h₁ with
      | eclos hval' ht hb hd =>
        exact ⟨_, elabSeal.ebox
          (elabSeal.evmrg hval' hv1 ht (elabSeal_weaken h₂ hv1 .top) hd) hb⟩
  | ssboxv hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ebox h₁ h₂ => exact ⟨_, elabSeal_weaken h₂ hv2 Γ⟩
  | ssproj hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eproj h₁ hlook =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.eproj h hlook⟩
  | ssprojv hv hv1 hlookv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eproj h₁ hlook =>
      obtain ⟨w, hw⟩ := elabSeal_lookup_pres hlook h₁ hv1 hlookv
      exact ⟨_, elabSeal_weaken hw (sce_lookupv_value hlookv hv1) Γ⟩
  | sslrec hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | elrec h₁ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.elrec h⟩
  | ssrproj hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | erproj h₁ hlook =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.erproj h hlook⟩
  | ssrprojv hv hv1 hsel =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | erproj h₁ hlook =>
      obtain ⟨w, hw⟩ := elabSeal_sel_pres hlook h₁ hv1 hsel
      exact ⟨_, elabSeal_weaken hw (sce_sel_value hsel hv1) Γ⟩
  | ssmstruct_sandboxed hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emstruct hsb hop h =>
      have heq := hsb rfl; subst heq
      obtain ⟨ce', h'⟩ := ih ⟨_, h⟩ SCE.Value.vunit ⟨_, elabSeal.eunit .top⟩
      exact ⟨_, elabSeal.emstruct (fun _ => rfl) hop h'⟩
  | ssmstruct_open hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emstruct hsb hop h =>
      have heq := hop rfl; subst heq
      obtain ⟨ce', h'⟩ := ih ⟨_, h⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.emstruct hsb (fun _ => rfl) h'⟩
  | ssmstructv_sandboxed hv hv' =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emstruct hsb hop h => exact ⟨_, elabSeal_weaken h hv' Γ⟩
  | ssmstructv_open hv hv' =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emstruct hsb hop h => exact ⟨_, elabSeal_weaken h hv' Γ⟩
  | ssmfunctor_sandboxed hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emfunctor hsb hop hdop h =>
      have heq := hsb rfl; subst heq
      exact ⟨_, elabSeal.emclos SCE.Value.vunit (elabSeal.eunit .top) h disj_top⟩
  | ssmfunctor_open hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emfunctor hsb hop hdop h =>
      have heq := hop rfl; subst heq
      exact ⟨_, elabSeal.emclos hval henv h (hdop rfl)⟩
  | ssmappl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emapp h₁ h₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.emapp h h₂⟩
  | ssmappr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emapp h₁ h₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₂⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.emapp h₁ h⟩
  | ssmbeta hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emapp h₁ h₂ =>
      cases h₁ with
      | emclos hval' ht hb hd =>
        exact ⟨_, elabSeal.ebox
          (elabSeal.evmrg hval' hv1 ht (elabSeal_weaken h₂ hv1 .top) hd) hb⟩
  | ssnmrgl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | enmrg h₁ h₂ hd₁ hd₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.enmrg h h₂ hd₁ hd₂⟩
  | ssnmrgr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | enmrg h₁ h₂ hd₁ hd₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₂⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.enmrg h₁ h hd₁ hd₂⟩
  | ssnmrgv hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | enmrg h₁ h₂ hd₁ hd₂ =>
      exact ⟨_, elabSeal.evmrg hv1 hv2
        (elabSeal_weaken h₁ hv1 .top) (elabSeal_weaken h₂ hv2 .top) hd₂⟩
  | ssletbl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eletb h₁ h₂ hd =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.eletb h h₂ hd⟩
  | ssletbv hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eletb h₁ h₂ hd =>
      exact ⟨_, elabSeal.ebox
        (elabSeal.evmrg hval hv1 henv (elabSeal_weaken h₁ hv1 .top) hd) h₂⟩
  | ssmlinkl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emlink h₁ h₂ hlook hd₁ hd₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.emlink h h₂ hlook hd₁ hd₂⟩
  | ssmlinkr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emlink h₁ h₂ hlook hd₁ hd₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₂⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.emlink h₁ h hlook hd₁ hd₂⟩
  | ssmlinkbeta hv hv1 hv2 hsel =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emlink h₁ h₂ hlook hd₁ hd₂ =>
      cases h₂ with
      | emclos hval_v2 henv_v2 hbody hd_mclos =>
        obtain ⟨wl, helab_vl⟩ := elabSeal_sel_pres hlook h₁ hv1 hsel
        have hvl := sce_sel_value hsel hv1
        exact ⟨_, elabSeal.edmrg h₁
          (elabSeal.ebox
            (elabSeal.evmrg hval_v2 (SCE.Value.vlrec hvl) henv_v2
              (elabSeal.elrec helab_vl) hd_mclos)
            hbody)
          hd₁ hd₂⟩
  | ssopenml hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eopenm h₁ h₂ hd =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.eopenm h h₂ hd⟩
  | ssopenm hv hv' =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eopenm h₁ h₂ hd =>
      cases h₁ with
      | elrec hinner =>
        exact ⟨_, elabSeal.ebox
          (elabSeal.evmrg hval hv' henv (elabSeal_weaken hinner hv' .top) hd) h₂⟩
  | ssinl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | einl h₁ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.einl h⟩
  | ssinr hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | einr h₁ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.einr h⟩
  | sscase hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ecase h h₁ h₂ hd₁ hd₂ =>
      obtain ⟨ce', h'⟩ := ih ⟨_, h⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.ecase h' h₁ h₂ hd₁ hd₂⟩
  | sscasel hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ecase h h₁ h₂ hd₁ hd₂ =>
      cases h with
      | einl hinner =>
        exact ⟨_, elabSeal.ebox
          (elabSeal.evmrg hval hv1 henv (elabSeal_weaken hinner hv1 .top) hd₁) h₁⟩
  | sscaser hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ecase h h₁ h₂ hd₁ hd₂ =>
      cases h with
      | einr hinner =>
        exact ⟨_, elabSeal.ebox
          (elabSeal.evmrg hval hv1 henv (elabSeal_weaken hinner hv1 .top) hd₂) h₂⟩
  | ssfclos hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eflam h₁ hd₁ hd₂ => exact ⟨_, elabSeal.efclos hval henv h₁ hd₁ hd₂⟩
  | ssfbeta hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp h₁ h₂ =>
      cases h₁ with
      | efclos hval' ht hb hd₁ hd₂ =>
        exact ⟨_, elabSeal.ebox
          (elabSeal.evmrg (SCE.Value.vmrg hval' (SCE.Value.vfclos hval')) hv1
            (elabSeal.evmrg hval' (SCE.Value.vfclos hval') ht
              (elabSeal.efclos hval' ht hb hd₁ hd₂) hd₁)
            (elabSeal_weaken h₂ hv1 .top) hd₂)
          hb⟩
  | ssfold hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | efold h₁ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.efold h⟩
  | ssunfold hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eunfold h₁ heq =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.eunfold h heq⟩
  | ssunfoldv hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eunfold h₁ heq =>
      subst heq
      cases h₁ with
      | efold hinner => exact ⟨_, hinner⟩
  -- ── the sealing forms: real cases now (Core had none) ──
  | sswrap hv hstep =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ewrap hΔ hv' h => exact (svalue_not_step hv' hstep).elim
  | ssmseal hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emseal hΔ hnr hwf h =>
      obtain ⟨ce', h'⟩ := ih ⟨_, h⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.emseal hΔ hnr hwf h'⟩
  | ssmsealv hv hv1 hsv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emseal hΔ hnr hwf h => exact source_ssealv_pres hsv hΔ hnr hwf hv1 h
  | ssmunseal hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emunseal hΔ hnr hwf h heq =>
      obtain ⟨ce', h'⟩ := ih ⟨_, h⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.emunseal hΔ hnr hwf h' heq⟩
  | ssmunsealv hv hv1 hsv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emunseal hΔ hnr hwf h heq =>
      subst heq
      exact source_sunsealv_pres hsv hΔ hnr hwf hv1 h
  | ssmlinknl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emlinkn h₁ h₂ hwire hd₁ hd₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₁⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.emlinkn h h₂ hwire hd₁ hd₂⟩
  | ssmlinknr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emlinkn h₁ h₂ hwire hd₁ hd₂ =>
      obtain ⟨ce', h⟩ := ih ⟨_, h₂⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabSeal.emlinkn h₁ h hwire hd₁ hd₂⟩
  | ssmlinknbeta hv hv1 hv2 hsp =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | emlinkn h₁ h₂ hwire hd₁ hd₂ =>
      cases h₂ with
      | emclos hval_v2 henv_v2 hbody hd_mclos =>
        obtain ⟨cpkg, hpkg⟩ := elabSeal_selpkg_pres hwire hsp hv1 h₁
        have hvpkg := S_Sem.selpkg_value hsp hv1
        exact ⟨_, elabSeal.edmrg h₁
          (elabSeal.ebox
            (elabSeal.evmrg hval_v2 hvpkg henv_v2 hpkg hd_mclos)
            hbody)
          hd₁ hd₂⟩

-- Whole-program preservation, elabSeal-witnessed.
theorem source_spreservation {e e' : SCE.Exp} {A : SCE.Typ}
    (htyp : ∃ ce, elabSeal Δ .top e A ce)
    (hstep : SStep SCE.Exp.unit e e')
    : ∃ ce', elabSeal Δ .top e' A ce' :=
  source_sgpreservation hstep htyp SCE.Value.vunit ⟨_, elabSeal.eunit .top⟩

end Seal

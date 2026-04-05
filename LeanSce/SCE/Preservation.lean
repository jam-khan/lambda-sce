import LeanSce.SCE.Elaboration
import LeanSce.SCE.SmallStep
import LeanSce.SCE.Syntax

open SCE S_Sem

-- Value weakening: well-elaborated values can be retyped under any context
theorem elab_value_weaken
    {Γ A : SCE.Typ} {v : SCE.Exp} {ce : Core.Exp}
    (helab : elabExp Γ v A ce)
    (hv : SCE.Value v)
    (Γ' : SCE.Typ) : elabExp Γ' v A ce := by
  sorry

-- Lookup preservation for elaboration
theorem elab_lookup_pres {Γ B : SCE.Typ} {n : Nat}
    (hlook : SLookup Γ n B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp} {v' : SCE.Exp},
    S_Sem.LookupV v n v'
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ ce
    → ∃ ce', elabExp Γ v' B ce' := by
  sorry

-- Record lookup preservation for elaboration
theorem elab_rlookup_pres {Γ B : SCE.Typ} {l : String}
    (hlook : SRLookup Γ l B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp} {v' : SCE.Exp},
    S_Sem.Sel v l v'
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ ce
    → ∃ ce', elabExp Γ v' B ce' := by
  sorry

-- Lookup progress for elaboration
theorem elab_lookup_prog {A B : SCE.Typ} {n : Nat}
    (hlook : SLookup A n B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp},
    elabExp SCE.Typ.top v A ce
    → SCE.Value v
    → ∃ v', S_Sem.LookupV v n v' := by
  sorry

-- Record lookup progress for elaboration
theorem elab_rlookup_prog {A B : SCE.Typ} {l : String}
    (hlook : SRLookup A l B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp},
    elabExp SCE.Typ.top v A ce
    → SCE.Value v
    → ∃ v', S_Sem.Sel v l v' := by
  sorry

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
      sorry
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
      sorry

-- Whole-program preservation
theorem spreservation {e e' : SCE.Exp} {A : SCE.Typ}
    : (∃ ce, elabExp SCE.Typ.top e A ce)
    → SStep SCE.Exp.unit e e'
    → ∃ ce', elabExp SCE.Typ.top e' A ce' := by
  intros htyp hstep
  apply sgpreservation hstep htyp Value.vunit
  exact ⟨_, elabExp.eunit _⟩

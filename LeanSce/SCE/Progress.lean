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
        | .vint => nomatch h1
        | .vunit => nomatch h1
        | .vmrg _ _ => nomatch h1
        | .vmclos _ => nomatch h1
        | .vlrec _ => nomatch h1
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
  | enmrg => sorry
  | letb => sorry
  | openm => sorry
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
  | mapp => sorry
  | mlink => sorry

-- Whole-program progress
theorem sprogress {e : SCE.Exp} {A : SCE.Typ}
    : (∃ ce, elabExp SCE.Typ.top e A ce)
    → SCE.Value e ∨ ∃ e', SStep SCE.Exp.unit e e' := by
  intro htyp
  exact sgprogress htyp Value.vunit ⟨_, elabExp.eunit _⟩

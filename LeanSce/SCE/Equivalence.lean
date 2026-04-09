import LeanSce.SCE.SmallStep
import LeanSce.SCE.Semantics
import LeanSce.SCE.Syntax
import LeanSce.SCE.Theories

open SCE S_Sem

-- Multi-step relation for SCE
inductive SMStep : Exp → Exp → Exp → Prop where
  | refl {v e : Exp}
    : Value v
    → SMStep v e e
  | step {v e e' e'' : Exp}
    : SStep v e e'
    → SMStep v e' e''
    → SMStep v e e''

-- BStep produces values (delegates to existing theorem in Theories)
theorem sbig_produces_value
    {v e v' : Exp}
    (hval : Value v)
    (hbig : BStep v e v')
    : Value v' := eval_produces_value hval hbig

-- BStep env is always a value (every BStep constructor requires Value ρ)
theorem sbig_env_value {env e v : Exp} (h : BStep env e v) : Value env := by
  cases h <;> assumption

-- SStep implies env is a value
theorem sstep_env_value {v e e' : Exp} (h : SStep v e e') : Value v := by
  cases h <;> assumption

-- SMStep implies env is a value
theorem smstep_env_value {v e e' : Exp} (h : SMStep v e e') : Value v := by
  cases h with
  | refl hv => exact hv
  | step hs _ => exact sstep_env_value hs

-- Multi-step transitivity
theorem smstep_trans {v e1 e2 e3 : Exp}
    (h1 : SMStep v e1 e2) (h2 : SMStep v e2 e3) : SMStep v e1 e3 := by
  induction h1 with
  | refl _ => assumption
  | step hs _ ih => exact SMStep.step hs (ih h2)

-- Congruence: mrg left
theorem smstep_mrg_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.mrg e1 e2) (.mrg e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmrgl (sstep_env_value hs) hs) ih

-- Congruence: mrg right
theorem smstep_mrg_right {v v1 e2 e2' : Exp}
    (hv : Value v) (hv1 : Value v1)
    (h : SMStep (.mrg v v1) e2 e2')
    : SMStep v (.mrg v1 e2) (.mrg v1 e2') := by
  induction h with
  | refl _ => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmrgr hv hv1 hs) ih

-- Congruence: app left
theorem smstep_app_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.app e1 e2) (.app e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssappl (sstep_env_value hs) hs) ih

-- Congruence: app right
theorem smstep_app_right {v v1 e2 e2' : Exp}
    (hv1 : Value v1)
    (h : SMStep v e2 e2')
    : SMStep v (.app v1 e2) (.app v1 e2') := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssappr (sstep_env_value hs) hv1 hs) ih

-- Congruence: box left
theorem smstep_box_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.box e1 e2) (.box e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssboxl (sstep_env_value hs) hs) ih

-- Congruence: box right
theorem smstep_box_right {v v1 e2 e2' : Exp}
    (hv : Value v) (hv1 : Value v1)
    (h : SMStep v1 e2 e2')
    : SMStep v (.box v1 e2) (.box v1 e2') := by
  induction h with
  | refl _ => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssboxr hv hv1 hs) ih

-- Box env drop
theorem sbox_mstep_drop_env {e e1 v2 : Exp}
    (hm : SMStep e e1 v2) (hv2 : Value v2)
    {v : Exp} (hv : Value v)
    : SMStep v (.box e e1) v2 := by
  have hve := smstep_env_value hm
  exact smstep_trans
    (smstep_box_right hv hve hm)
    (SMStep.step (SStep.ssboxv hv hve hv2) (SMStep.refl hv))

-- Congruence: proj
theorem smstep_proj {v e1 e2 : Exp} {n : Nat}
    (h : SMStep v e1 e2)
    : SMStep v (.proj e1 n) (.proj e2 n) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssproj (sstep_env_value hs) hs) ih

-- Congruence: lrec
theorem smstep_lrec {v e1 e2 : Exp} {l : String}
    (h : SMStep v e1 e2)
    : SMStep v (.lrec l e1) (.lrec l e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.sslrec (sstep_env_value hs) hs) ih

-- Congruence: rproj
theorem smstep_rproj {v e1 e2 : Exp} {l : String}
    (h : SMStep v e1 e2)
    : SMStep v (.rproj e1 l) (.rproj e2 l) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssrproj (sstep_env_value hs) hs) ih

-- Soundness: big-step → multi-step (simple cases filled)
theorem sbig_sound {env e v : Exp}
    (h : BStep env e v)
    : SMStep env e v := by
  induction h with
  | lit hv => exact SMStep.refl hv
  | unit hv => exact SMStep.refl hv
  | query hv =>
    exact SMStep.step (SStep.ssquery hv) (SMStep.refl hv)
  | clos_val hv hv1 => exact SMStep.refl hv
  | lam hv =>
    exact SMStep.step (SStep.ssclos hv) (SMStep.refl hv)
  | box hv hb1 hb2 ih1 ih2 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value hv1 hb2
    exact smstep_trans (smstep_box_left ih1 _) (sbox_mstep_drop_env ih2 hv2 hv)
  | app_clos hv hb1 hb2 hb3 ih1 ih2 ih3 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value hv hb2
    have hv3 := sbig_produces_value (Value.vmrg (by cases hv1; assumption) hv2) hb3
    cases hv1 with
    | vclos hvc =>
      exact smstep_trans (smstep_app_left ih1 _)
        (smstep_trans (smstep_app_right (.vclos hvc) ih2)
          (smstep_trans
            (SMStep.step (SStep.ssbeta hv hv2 hvc) (SMStep.refl hv))
            (sbox_mstep_drop_env ih3 hv3 hv)))
  | dmrg hv hb1 hb2 ih1 ih2 =>
    have hv1 := sbig_produces_value hv hb1
    exact smstep_trans (smstep_mrg_left ih1 _) (smstep_mrg_right hv hv1 ih2)
  | proj hv hb hlook ih =>
    have hv' := sbig_produces_value hv hb
    exact smstep_trans (smstep_proj ih) (SMStep.step (SStep.ssprojv hv hv' hlook) (SMStep.refl hv))
  | lrec hv hb ih => exact smstep_lrec ih
  | rproj hv hb hsel ih =>
    have hv' := sbig_produces_value hv hb
    exact smstep_trans (smstep_rproj ih) (SMStep.step (SStep.ssrprojv hv hv' hsel) (SMStep.refl hv))
  -- Non-lambdaE cases: no SStep rules yet
  | mclos_val _ _ => sorry
  | app_mclos _ _ _ _ _ _ _ => sorry
  | nmrg _ _ _ _ _ => sorry
  | letb _ _ _ _ _ => sorry
  | openm _ _ _ _ _ => sorry
  | mstruct_sandboxed _ _ _ => sorry
  | mstruct_open _ _ _ => sorry
  | mfunctor_sandboxed _ => sorry
  | mfunctor_open _ => sorry
  | mlink _ _ _ _ _ _ _ _ => sorry

-- Values big-step to themselves
theorem sbig_value_refl {e v : Exp}
    (hve : Value e) (hvv : Value v)
    : BStep v e e := by
  induction hve generalizing v with
  | vint => exact BStep.lit hvv
  | vunit => exact BStep.unit hvv
  | vclos hv' => exact BStep.clos_val hvv hv'
  | vmclos hv' => exact BStep.mclos_val hvv hv'
  | vlrec hv' ih => exact BStep.lrec hvv (ih hvv)
  | vmrg hv1 hv2 ih1 ih2 =>
    have h1 := ih1 hvv
    exact BStep.dmrg hvv h1 (ih2 (Value.vmrg hvv (sbig_produces_value hvv h1)))

-- Determinism for values
theorem sbig_val_det {env e v1 : Exp}
    (h1 : BStep env e v1) (hv : Value e)
    {v2 : Exp} (h2 : BStep env e v2)
    : v1 = v2 := by
  induction h1 generalizing v2 with
  | lit _ => cases h2 <;> rfl
  | unit _ => cases h2 <;> rfl
  | clos_val _ _ => cases h2 <;> rfl
  | mclos_val _ _ => cases h2 <;> rfl
  | query _ => cases hv
  | lam _ => cases hv
  | box _ _ _ _ _ => cases hv
  | app_clos _ _ _ _ _ _ _ => cases hv
  | app_mclos _ _ _ _ _ _ _ => cases hv
  | proj _ _ _ _ => cases hv
  | rproj _ _ _ _ => cases hv
  | letb _ _ _ _ _ => cases hv
  | openm _ _ _ _ _ => cases hv
  | mstruct_sandboxed _ _ _ => cases hv
  | mstruct_open _ _ _ => cases hv
  | mfunctor_sandboxed _ => cases hv
  | mfunctor_open _ => cases hv
  | mlink _ _ _ _ _ _ _ _ => cases hv
  | nmrg _ _ _ _ _ => cases hv
  | lrec _ _ ih1 =>
    cases hv with
    | vlrec hv' =>
      cases h2 with
      | lrec _ hb2 =>
        congr 1
        exact ih1 hv' hb2
  | dmrg _ hb1 hb2 ih1 ih2 =>
    cases hv with
    | vmrg hv1 hv2 =>
      cases h2 with
      | dmrg _ hb1' hb2' =>
        have heq1 := ih1 hv1 hb1'
        subst heq1
        have heq2 := ih2 hv2 hb2'
        subst heq2
        rfl

-- Values big-step to themselves (equality version)
theorem sbig_value_eq {env v e : Exp}
    (h : BStep env v e) (hv : Value v)
    : v = e := by
  have henv := sbig_env_value h
  exact sbig_val_det (sbig_value_refl hv henv) hv h

-- If e steps to e', and e' big-steps to v, then e big-steps to v
theorem sstep_sbig {env e1 e2 v : Exp}
    (hs : SStep env e1 e2) (hb : BStep env e2 v)
    : BStep env e1 v := by
  induction hs generalizing v with
  | ssquery hv =>
    have hvt := sbig_value_eq hb hv
    rw [hvt]
    exact BStep.query (by rw [← hvt]; exact sbig_env_value hb)
  | ssclos hv =>
    cases hb with
    | clos_val hv1 hv2 => exact BStep.lam hv
  | ssappl hv _ ih =>
    cases hb with
    | app_clos _ hb1 hb2 hb3 => exact BStep.app_clos hv (ih hb1) hb2 hb3
  | ssappr hv hv1 _ ih =>
    cases hb with
    | app_clos _ hb1 hb2 hb3 => exact BStep.app_clos hv hb1 (ih hb2) hb3
  | ssbeta hv hv1 hv2 =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 (Value.vmrg hv2 hv1)
      subst heq
      exact BStep.app_clos hv (BStep.clos_val hv hv2) (sbig_value_refl hv1 hv) hb2
  | ssboxl hv _ ih =>
    cases hb with
    | box _ hb1 hb2 => exact BStep.box hv (ih hb1) hb2
  | ssboxr hv hv1 _ ih =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 hv1
      subst heq
      exact BStep.box hv hb1 (ih hb2)
  | ssboxv hv hv1 hv2 =>
    have heq := sbig_value_eq hb hv2
    subst heq
    exact BStep.box hv (sbig_value_refl hv1 hv) (sbig_value_refl hv2 hv1)
  | ssmrgl hv _ ih =>
    cases hb with
    | dmrg _ hb1 hb2 => exact BStep.dmrg hv (ih hb1) hb2
  | ssmrgr hv hv1 _ ih =>
    cases hb with
    | dmrg _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 hv1
      subst heq
      exact BStep.dmrg hv hb1 (ih hb2)
  | ssproj hv _ ih =>
    cases hb with
    | proj _ hb1 hlook => exact BStep.proj hv (ih hb1) hlook
  | ssprojv hv hv1 hlook =>
    have heq := sbig_value_eq hb (source_lookupv_value hv1 hlook)
    subst heq
    exact BStep.proj hv (sbig_value_refl hv1 hv) hlook
  | sslrec hv _ ih =>
    cases hb with
    | lrec _ hb1 => exact BStep.lrec hv (ih hb1)
  | ssrproj hv _ ih =>
    cases hb with
    | rproj _ hb1 hsel => exact BStep.rproj hv (ih hb1) hsel
  | ssrprojv hv hv1 hsel =>
    have heq := sbig_value_eq hb (source_sel_value hv1 hsel)
    subst heq
    exact BStep.rproj hv (sbig_value_refl hv1 hv) hsel

-- Completeness: multi-step + value → big-step
theorem sbig_complete {env e v : Exp}
    (hm : SMStep env e v) (hv : Value v)
    : BStep env e v := by
  induction hm with
  | refl hv_env => exact sbig_value_refl hv hv_env
  | step hs _ ih => exact sstep_sbig hs (ih hv)

-- Equivalence
theorem sstep_sbig_eq {env a v : Exp}
    : BStep env a v ↔ (Value v ∧ SMStep env a v) := by
  constructor
  · intro h; exact ⟨sbig_produces_value (sbig_env_value h) h, sbig_sound h⟩
  · intro ⟨hv, hm⟩; exact sbig_complete hm hv

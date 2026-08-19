import LeanSce.Seal.Determinism
import LeanSce.Seal.Progress
import LeanSce.Seal.Preservation

-- The sealing theorem for λE^≤: a binary, type-indexed logical relation (the binary
-- generalization of λE Figure 4's semantic typing), its fundamental lemma, the lemma that
-- casting is a coercion between the relations, and the sealing corollary — clients typed
-- against a seal cannot distinguish providers that agree at the seal.  Strong
-- normalization of well-typed λE^≤ programs falls out (no TDOS merge calculus had a
-- mechanized normalization result before; Eᵢ's termination is listed as unknown).
--
-- Type abstraction: the relation is indexed by two brand stores Δ₁ Δ₂ (the two providers
-- may use different representations, so left values type under Δ₁ and right values under
-- Δ₂) and by a brand interpretation η : Nat → Exp → Exp → Prop.  At `brand n` two values
-- are related iff both are wrappers whose payloads are η-related — the standard relational
-- interpretation of an abstract type; η is arbitrary.  The fundamental lemma is stated for
-- *client* typing (`HasType noBrands`, every brand opaque): a client cannot wrap, seal or
-- unseal, and everything else it can do respects η by construction.  Provider-side
-- values enter the relation through the sealing coercion (Abstraction.lean: coe_lr).
namespace Seal

variable {Δ Δ₁ Δ₂ : BrandStore} {η : Nat → Exp → Exp → Prop}

-- The relation, by structural recursion on the type.  Every clause that cannot re-derive
-- the values' typing carries it (& needs the consistency baked into the typing; arrows
-- carry their closure typing; brands carry it because the payload's typing lives in the
-- respective store).  The arrow clause is extensional and phrased at the application
-- level with existential runs, over arbitrary value environments: the semantics' internal
-- argument-cast at the closure's annotation input is thereby absorbed.
def LR (Δ₁ Δ₂ : BrandStore) (η : Nat → Exp → Exp → Prop) : Typ → Exp → Exp → Prop
  | .int, v₁, v₂ => ∃ i, v₁ = .lit i ∧ v₂ = .lit i
  | .top, v₁, v₂ => v₁ = .unit ∧ v₂ = .unit
  | .brand n, v₁, v₂ =>
      HasType Δ₁ .top v₁ (.brand n) ∧ HasType Δ₂ .top v₂ (.brand n) ∧
      ∃ w₁ w₂, v₁ = .wrap n w₁ ∧ v₂ = .wrap n w₂ ∧ η n w₁ w₂
  | .and A B, v₁, v₂ =>
      HasType Δ₁ .top v₁ (.and A B) ∧ HasType Δ₂ .top v₂ (.and A B) ∧
      ∃ a₁ b₁ a₂ b₂, v₁ = .mrg a₁ b₁ ∧ v₂ = .mrg a₂ b₂ ∧ LR Δ₁ Δ₂ η A a₁ a₂ ∧ LR Δ₁ Δ₂ η B b₁ b₂
  | .rcd l A, v₁, v₂ =>
      ∃ w₁ w₂, v₁ = .lrec l w₁ ∧ v₂ = .lrec l w₂ ∧ LR Δ₁ Δ₂ η A w₁ w₂
  | .arr A B, v₁, v₂ =>
      Value v₁ ∧ Value v₂ ∧
      HasType Δ₁ .top v₁ (.arr A B) ∧ HasType Δ₂ .top v₂ (.arr A B) ∧
      ∀ u₁ u₂, LR Δ₁ Δ₂ η A u₁ u₂ →
        ∀ ρ₁ ρ₂, Value ρ₁ → Value ρ₂ →
          ∃ w₁ w₂, MStep ρ₁ (.app v₁ u₁) w₁ ∧ MStep ρ₂ (.app v₂ u₂) w₂ ∧ LR Δ₁ Δ₂ η B w₁ w₂

theorem lr_value : {T : Typ} → {v₁ v₂ : Exp} → LR Δ₁ Δ₂ η T v₁ v₂ → Value v₁ ∧ Value v₂
  | .int, _, _, ⟨_, h₁, h₂⟩ => by subst h₁; subst h₂; exact ⟨Value.vint, Value.vint⟩
  | .top, _, _, ⟨h₁, h₂⟩ => by subst h₁; subst h₂; exact ⟨Value.vunit, Value.vunit⟩
  | .brand _, _, _, ⟨ht₁, ht₂, _, _, h₁, h₂, _⟩ => by
    subst h₁; subst h₂
    cases ht₁ with | twrap _ hv₁ _ =>
    cases ht₂ with | twrap _ hv₂ _ =>
    exact ⟨Value.vwrap hv₁, Value.vwrap hv₂⟩
  | .and A B, _, _, ⟨_, _, a₁, b₁, a₂, b₂, h₁, h₂, hA, hB⟩ => by
    subst h₁; subst h₂
    exact ⟨Value.vmrg (lr_value hA).1 (lr_value hB).1,
           Value.vmrg (lr_value hA).2 (lr_value hB).2⟩
  | .rcd l A, _, _, ⟨w₁, w₂, h₁, h₂, hA⟩ => by
    subst h₁; subst h₂
    exact ⟨Value.vrcd (lr_value hA).1, Value.vrcd (lr_value hA).2⟩
  | .arr A B, _, _, ⟨hv₁, hv₂, _, _, _⟩ => ⟨hv₁, hv₂⟩

theorem lr_typed : {T : Typ} → {v₁ v₂ : Exp} → LR Δ₁ Δ₂ η T v₁ v₂
    → HasType Δ₁ .top v₁ T ∧ HasType Δ₂ .top v₂ T
  | .int, _, _, ⟨_, h₁, h₂⟩ => by subst h₁; subst h₂; exact ⟨HasType.tint, HasType.tint⟩
  | .top, _, _, ⟨h₁, h₂⟩ => by subst h₁; subst h₂; exact ⟨HasType.tunit, HasType.tunit⟩
  | .brand _, _, _, ⟨ht₁, ht₂, _⟩ => ⟨ht₁, ht₂⟩
  | .and _ _, _, _, ⟨ht₁, ht₂, _⟩ => ⟨ht₁, ht₂⟩
  | .rcd l A, _, _, ⟨w₁, w₂, h₁, h₂, hA⟩ => by
    subst h₁; subst h₂
    exact ⟨HasType.trcd (lr_typed hA).1, HasType.trcd (lr_typed hA).2⟩
  | .arr _ _, _, _, ⟨_, _, ht₁, ht₂, _⟩ => ⟨ht₁, ht₂⟩

-- ── MStep congruence toolkit ─────────────────────────────────────────────────────────

theorem mstep_appl {v e₁ e₁' e₂ : Exp} (hv : Value v) (h : MStep v e₁ e₁')
    : MStep v (.app e₁ e₂) (.app e₁' e₂) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sappl hv hs) ih

theorem mstep_appr {v v₁ e₂ e₂' : Exp} (hv : Value v) (hv₁ : Value v₁) (h : MStep v e₂ e₂')
    : MStep v (.app v₁ e₂) (.app v₁ e₂') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sappr hv hv₁ hs) ih

theorem mstep_boxl {v e₁ e₁' e₂ : Exp} (hv : Value v) (h : MStep v e₁ e₁')
    : MStep v (.box e₁ e₂) (.box e₁' e₂) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sboxl hv hs) ih

theorem mstep_boxr {v v₁ e₂ e₂' : Exp} (hv : Value v) (hv₁ : Value v₁) (h : MStep v₁ e₂ e₂')
    : MStep v (.box v₁ e₂) (.box v₁ e₂') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sboxr hv hv₁ hs) ih

theorem mstep_mrgl {v e₁ e₁' e₂ : Exp} (hv : Value v) (h : MStep v e₁ e₁')
    : MStep v (.mrg e₁ e₂) (.mrg e₁' e₂) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.smrgl hv hs) ih

theorem mstep_mrgr {v v₁ e₂ e₂' : Exp} (hv : Value v) (hv₁ : Value v₁)
    (h : MStep (.mrg v v₁) e₂ e₂') : MStep v (.mrg v₁ e₂) (.mrg v₁ e₂') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.smrgr hv hv₁ hs) ih

theorem mstep_proj {v e e' : Exp} {n : Nat} (hv : Value v) (h : MStep v e e')
    : MStep v (.proj e n) (.proj e' n) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sproj hv hs) ih

theorem mstep_lrec {v e e' : Exp} {l : String} (hv : Value v) (h : MStep v e e')
    : MStep v (.lrec l e) (.lrec l e') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.slrec hv hs) ih

theorem mstep_rproj {v e e' : Exp} {l : String} (hv : Value v) (h : MStep v e e')
    : MStep v (.rproj e l) (.rproj e' l) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.srproj hv hs) ih

theorem mstep_anno {v e e' : Exp} {A : Typ} (hv : Value v) (h : MStep v e e')
    : MStep v (.anno e A) (.anno e' A) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sanno hv hs) ih

-- ── Run inversions (for the surgery inside cast_lr's arrow case) ─────────────────────

-- The first step of a terminating run of an application of values is beta.
theorem mstep_app_val_inv {ρ u r : Exp} {venv : Exp} {A₀ B₀ : Typ} {e : Exp}
    (h : MStep ρ (.app (.clos venv A₀ B₀ e) u) r) (hvenv : Value venv) (hu : Value u)
    (hr : Value r)
    : ∃ u', Cast u A₀ u' ∧ MStep ρ (.box (.mrg venv u') (.anno e B₀)) r := by
  cases h with
  | refl => nomatch hr
  | step hs h' =>
    cases hs with
    | sappl _ hs' => exact (value_not_step (Value.vclos hvenv) hs').elim
    | sappr _ _ hs' => exact (value_not_step hu hs').elim
    | sbeta _ _ _ hc => exact ⟨_, hc, h'⟩

-- A terminating run of a box with a value environment runs the body under that
-- environment and returns its value.
theorem mstep_box_inv_aux {ρ bx r : Exp} (h : MStep ρ bx r)
    : ∀ {venv e : Exp}, bx = .box venv e → Value venv → Value r
    → ∃ b, MStep venv e b ∧ Value b ∧ r = b := by
  induction h with
  | refl =>
    intro venv e hbx hvenv hr
    subst hbx
    nomatch hr
  | step hs h' ih =>
    intro venv e hbx hvenv hr
    subst hbx
    cases hs with
    | sboxl _ hs' => exact (value_not_step hvenv hs').elim
    | sboxr _ _ hs' =>
      obtain ⟨b, hrun, hvb, hrb⟩ := ih rfl hvenv hr
      exact ⟨b, MStep.step hs' hrun, hvb, hrb⟩
    | sboxv _ _ hv₂ =>
      exact ⟨_, MStep.refl, hv₂, (mstep_value_eq hv₂ h').symm⟩

theorem mstep_box_inv {ρ venv e r : Exp} (h : MStep ρ (.box venv e) r)
    (hvenv : Value venv) (hr : Value r) : ∃ b, MStep venv e b ∧ Value b ∧ r = b :=
  mstep_box_inv_aux h rfl hvenv hr

-- A terminating run of an annotated term runs the term to a value and casts it.
theorem mstep_anno_inv_aux {venv an r : Exp} (h : MStep venv an r)
    : ∀ {e : Exp} {T : Typ}, an = .anno e T → Value r
    → ∃ b, MStep venv e b ∧ Value b ∧ Cast b T r := by
  induction h with
  | refl =>
    intro e T han hr
    subst han
    nomatch hr
  | step hs h' ih =>
    intro e T han hr
    subst han
    cases hs with
    | sanno _ hs' =>
      obtain ⟨b, hrun, hvb, hcb⟩ := ih rfl hr
      exact ⟨b, MStep.step hs' hrun, hvb, hcb⟩
    | sannov _ hv₁ hc =>
      exact ⟨_, MStep.refl, hv₁, (mstep_value_eq (cast_value hv₁ hc) h') ▸ hc⟩

theorem mstep_anno_inv {venv e r : Exp} {T : Typ} (h : MStep venv (.anno e T) r)
    (hr : Value r) : ∃ b, MStep venv e b ∧ Value b ∧ Cast b T r :=
  mstep_anno_inv_aux h rfl hr

-- ── Canonical forms and merge-cast reconciliation ────────────────────────────────────

theorem canonical_arr {Γ C D : Typ} {v : Exp} (hv : Value v) (ht : HasType Δ Γ v (.arr C D))
    : ∃ u A₀ B₀ e, v = .clos u A₀ B₀ e := by
  cases ht with
  | tclos _ _ _ _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | tquery => nomatch hv
  | tapp _ _ => nomatch hv
  | tbox _ _ => nomatch hv
  | tproj _ _ => nomatch hv
  | trproj _ _ => nomatch hv
  | tanno _ _ => nomatch hv
  | tlam _ _ => nomatch hv
  | tseal _ _ _ _ => nomatch hv
  | tunseal _ _ _ _ _ => nomatch hv

-- Casting a well-typed merge at (a supertype of) its left component's type agrees with
-- casting the component directly.  Ordinary targets close by determinism/consistency;
-- only the & case recurses.
theorem cast_merge_eq_l_ord {a b : Exp} {Γ B₁ B₂ T : Typ} {w w' : Exp}
    (hord : Ordinary T) (hv : Value (.mrg a b)) (ht : HasType Δ Γ (.mrg a b) (.and B₁ B₂))
    (hc : Cast (.mrg a b) T w) (hc' : Cast a T w') : w = w' := by
  cases hv with
  | vmrg hva hvb =>
    cases hc with
    | cmrgl _ hx =>
      cases ht with
      | tmrg hp _ _ _ => exact cast_determinism hx hva hp hc'
      | tmergev _ _ hp _ _ => exact cast_determinism hx hva hp hc'
    | cmrgr _ hy =>
      cases ht with
      | tmrg hp hq _ hd₂ =>
        exact (disjoint_consistent hva hvb hp hq hd₂ hc' hy).symm
      | tmergev _ _ _ _ hcons => exact (hcons hc' hy).symm
    | cand _ _ => nomatch hord
    | ctop => nomatch hord

theorem cast_merge_eq_l {a b : Exp} {Γ B₁ B₂ : Typ} : ∀ {T : Typ} {w w' : Exp},
    Value (.mrg a b) → HasType Δ Γ (.mrg a b) (.and B₁ B₂)
    → Cast (.mrg a b) T w → Cast a T w' → w = w' := by
  intro T
  induction T with
  | top =>
    intro w w' _ _ hc hc'
    cases hc with
    | ctop =>
      cases hc' with
      | ctop => rfl
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | and T₁ T₂ ih₁ ih₂ =>
    intro w w' hv ht hc hc'
    cases hc with
    | cand hx₁ hx₂ =>
      cases hc' with
      | cand hy₁ hy₂ => rw [ih₁ hv ht hx₁ hy₁, ih₂ hv ht hx₂ hy₂]
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | int =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.oint hv ht hc hc'
  | arr T₁ T₂ _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.oarr hv ht hc hc'
  | rcd l T' _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.orcd hv ht hc hc'
  | brand _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.obrand hv ht hc hc'

theorem cast_merge_eq_r_ord {a b : Exp} {Γ B₁ B₂ T : Typ} {w w' : Exp}
    (hord : Ordinary T) (hv : Value (.mrg a b)) (ht : HasType Δ Γ (.mrg a b) (.and B₁ B₂))
    (hc : Cast (.mrg a b) T w) (hc' : Cast b T w') : w = w' := by
  cases hv with
  | vmrg hva hvb =>
    cases hc with
    | cmrgr _ hy =>
      cases ht with
      | tmrg _ hq _ _ => exact cast_determinism hy hvb hq hc'
      | tmergev _ _ _ hq _ => exact cast_determinism hy hvb hq hc'
    | cmrgl _ hx =>
      cases ht with
      | tmrg hp hq _ hd₂ => exact disjoint_consistent hva hvb hp hq hd₂ hx hc'
      | tmergev _ _ _ _ hcons => exact hcons hx hc'
    | cand _ _ => nomatch hord
    | ctop => nomatch hord

theorem cast_merge_eq_r {a b : Exp} {Γ B₁ B₂ : Typ} : ∀ {T : Typ} {w w' : Exp},
    Value (.mrg a b) → HasType Δ Γ (.mrg a b) (.and B₁ B₂)
    → Cast (.mrg a b) T w → Cast b T w' → w = w' := by
  intro T
  induction T with
  | top =>
    intro w w' _ _ hc hc'
    cases hc with
    | ctop =>
      cases hc' with
      | ctop => rfl
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | and T₁ T₂ ih₁ ih₂ =>
    intro w w' hv ht hc hc'
    cases hc with
    | cand hx₁ hx₂ =>
      cases hc' with
      | cand hy₁ hy₂ => rw [ih₁ hv ht hx₁ hy₁, ih₂ hv ht hx₂ hy₂]
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | int =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.oint hv ht hc hc'
  | arr T₁ T₂ _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.oarr hv ht hc hc'
  | rcd l T' _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.orcd hv ht hc hc'
  | brand _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.obrand hv ht hc hc'

-- ── The generator is self-related at top-like types ──────────────────────────────────

theorem toplike_lr_gen {D : Typ} (htl : TopLike D) : LR Δ₁ Δ₂ η D (genVal D) (genVal D) := by
  induction htl with
  | tltop => exact ⟨rfl, rfl⟩
  | tland h₁ h₂ ih₁ ih₂ =>
    exact ⟨genVal_typed (TopLike.tland h₁ h₂) .top, genVal_typed (TopLike.tland h₁ h₂) .top,
      _, _, _, _, rfl, rfl, ih₁, ih₂⟩
  | tlrcd h ih => exact ⟨_, _, rfl, rfl, ih⟩
  | tlarr h ih =>
    rename_i A₀ D'
    refine ⟨genVal_value _, genVal_value _,
      genVal_typed (TopLike.tlarr h) .top, genVal_typed (TopLike.tlarr h) .top,
      ?_⟩
    intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
    -- both applications run: beta (cast the argument at A₀), body is the generator of D',
    -- reseal at D' collapses to the generator again
    have hvu := lr_value hu
    have htu := lr_typed hu
    obtain ⟨u₁', hc₁⟩ := cast_progress hvu.1 htu.1 (sub_refl A₀)
    obtain ⟨u₂', hc₂⟩ := cast_progress hvu.2 htu.2 (sub_refl A₀)
    obtain ⟨g', hcg⟩ := cast_progress (genVal_value D') (genVal_typed (Δ := Δ₁) h .top) (sub_refl D')
    have hg' : g' = genVal D' := (toplike_gen_cast h hcg).1
    have hrun : ∀ (ρ u u' : Exp), Value ρ → Value u → Cast u A₀ u' →
        MStep ρ (.app (genVal (.arr A₀ D')) u) g' := by
      intro ρ u u' hρ hvu' hc
      refine MStep.step (Step.sbeta hρ Value.vunit hvu' hc) ?_
      have hvm : Value (.mrg .unit u') := Value.vmrg Value.vunit (cast_value hvu' hc)
      refine MStep.step (Step.sboxr hρ hvm (Step.sannov hvm (genVal_value D') hcg)) ?_
      exact MStep.step (Step.sboxv hρ hvm (cast_value (genVal_value D') hcg)) MStep.refl
    rw [hg'] at hrun
    exact ⟨genVal D', genVal D', hrun ρ₁ u₁ u₁' hρ₁ hvu.1 hc₁,
      hrun ρ₂ u₂ u₂' hρ₂ hvu.2 hc₂, ih⟩

-- ── Casting is a coercion between the relations ──────────────────────────────────────
-- The semantic content of sealing.  Single structural induction on the subtyping
-- derivation: sandl/sandr reconcile the merge-peeling casts via cast_merge_eq;
-- the arrow case rebuilds the applications' runs, using cast transitivity to identify
-- the argument casts and to compose the reseal at the wider codomain.
theorem cast_lr {B A : Typ} (hs : Sub B A) {v₁ v₂ w₁ w₂ : Exp} (hlr : LR Δ₁ Δ₂ η B v₁ v₂)
    (c₁ : Cast v₁ A w₁) (c₂ : Cast v₂ A w₂) : LR Δ₁ Δ₂ η A w₁ w₂ := by
  induction hs generalizing v₁ v₂ w₁ w₂ with
  | sint =>
    obtain ⟨i, e₁, e₂⟩ := hlr
    subst e₁; subst e₂
    cases c₁ with
    | cint =>
      cases c₂ with
      | cint => exact ⟨i, rfl, rfl⟩
  | stop =>
    cases c₁ with
    | ctop =>
      cases c₂ with
      | ctop => exact ⟨rfl, rfl⟩
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | sand hs₁ hs₂ ih₁ ih₂ =>
    have hv := lr_value hlr
    have ht := lr_typed hlr
    cases c₁ with
    | cand c₁ₗ c₁ᵣ =>
      cases c₂ with
      | cand c₂ₗ c₂ᵣ =>
        exact ⟨cast_preservation (Cast.cand c₁ₗ c₁ᵣ) hv.1 ht.1,
          cast_preservation (Cast.cand c₂ₗ c₂ᵣ) hv.2 ht.2,
          _, _, _, _, rfl, rfl, ih₁ hlr c₁ₗ c₂ₗ, ih₂ hlr c₁ᵣ c₂ᵣ⟩
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | sandl hs' ih =>
    obtain ⟨htm₁, htm₂, a₁, b₁, a₂, b₂, e₁, e₂, hA₁, hA₂⟩ := hlr
    subst e₁; subst e₂
    have hva := lr_value hA₁
    have hta := lr_typed hA₁
    have hvb := lr_value hA₂
    obtain ⟨w₁', c₁'⟩ := cast_progress hva.1 hta.1 hs'
    obtain ⟨w₂', c₂'⟩ := cast_progress hva.2 hta.2 hs'
    rw [cast_merge_eq_l (Value.vmrg hva.1 hvb.1) htm₁ c₁ c₁',
        cast_merge_eq_l (Value.vmrg hva.2 hvb.2) htm₂ c₂ c₂']
    exact ih hA₁ c₁' c₂'
  | sandr hs' ih =>
    obtain ⟨htm₁, htm₂, a₁, b₁, a₂, b₂, e₁, e₂, hA₁, hA₂⟩ := hlr
    subst e₁; subst e₂
    have hva := lr_value hA₁
    have hvb := lr_value hA₂
    have htb := lr_typed hA₂
    obtain ⟨w₁', c₁'⟩ := cast_progress hvb.1 htb.1 hs'
    obtain ⟨w₂', c₂'⟩ := cast_progress hvb.2 htb.2 hs'
    rw [cast_merge_eq_r (Value.vmrg hva.1 hvb.1) htm₁ c₁ c₁',
        cast_merge_eq_r (Value.vmrg hva.2 hvb.2) htm₂ c₂ c₂']
    exact ih hA₂ c₁' c₂'
  | srcd hs' ih =>
    obtain ⟨u₁, u₂, e₁, e₂, hInner⟩ := hlr
    subst e₁; subst e₂
    cases c₁ with
    | crcd d₁ =>
      cases c₂ with
      | crcd d₂ => exact ⟨_, _, rfl, rfl, ih hInner d₁ d₂⟩
  | sbrand =>
    obtain ⟨ht₁, ht₂, u₁, u₂, e₁, e₂, hη⟩ := hlr
    subst e₁; subst e₂
    cases c₁ with
    | cwrap =>
      cases c₂ with
      | cwrap => exact ⟨ht₁, ht₂, u₁, u₂, rfl, rfl, hη⟩
  | @sarr C' D' C D hsC hsD ihC ihD =>
    obtain ⟨hv₁, hv₂, ht₁, ht₂, CL⟩ := hlr
    obtain ⟨u₁env, A₁₀, B₁₀, e₁b, hc₁eq⟩ := canonical_arr hv₁ ht₁
    obtain ⟨u₂env, A₂₀, B₂₀, e₂b, hc₂eq⟩ := canonical_arr hv₂ ht₂
    subst hc₁eq; subst hc₂eq
    have hvenv₁ : Value u₁env := by cases hv₁ with | vclos h => exact h
    have hvenv₂ : Value u₂env := by cases hv₂ with | vclos h => exact h
    cases c₁ with
    | carrowtl htlD hsc₁ hsb₁ =>
      cases c₂ with
      | carrow hntlD _ _ => exact absurd htlD hntlD
      | carrowtl _ _ _ => exact toplike_lr_gen (TopLike.tlarr htlD)
    | carrow hntlD hsc₁ hsb₁ =>
      cases c₂ with
      | carrowtl htlD _ _ => exact absurd htlD hntlD
      | carrow _ hsc₂ hsb₂ =>
        refine ⟨Value.vclos hvenv₁, Value.vclos hvenv₂,
          cast_preservation (Cast.carrow hntlD hsc₁ hsb₁) hv₁ ht₁,
          cast_preservation (Cast.carrow hntlD hsc₂ hsb₂) hv₂ ht₂, ?_⟩
        intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
        have hvu := lr_value hu
        have htu := lr_typed hu
        -- cast the arguments at the source domain and relate them there
        obtain ⟨u₁c, cu₁⟩ := cast_progress hvu.1 htu.1 hsC
        obtain ⟨u₂c, cu₂⟩ := cast_progress hvu.2 htu.2 hsC
        have huc : LR Δ₁ Δ₂ η C' u₁c u₂c := ihC hu cu₁ cu₂
        -- the old behavior at the cast arguments
        obtain ⟨r₁, r₂, run₁, run₂, hr⟩ := CL u₁c u₂c huc ρ₁ ρ₂ hρ₁ hρ₂
        have hvr := lr_value hr
        have htr := lr_typed hr
        -- dissect the old runs down to the body runs and their reseals
        obtain ⟨u₁s, cu₁s, runbox₁⟩ :=
          mstep_app_val_inv run₁ hvenv₁ (cast_value hvu.1 cu₁) hvr.1
        obtain ⟨u₂s, cu₂s, runbox₂⟩ :=
          mstep_app_val_inv run₂ hvenv₂ (cast_value hvu.2 cu₂) hvr.2
        have hvu₁s : Value u₁s := cast_value (cast_value hvu.1 cu₁) cu₁s
        have hvu₂s : Value u₂s := cast_value (cast_value hvu.2 cu₂) cu₂s
        have hvm₁ : Value (.mrg u₁env u₁s) := Value.vmrg hvenv₁ hvu₁s
        have hvm₂ : Value (.mrg u₂env u₂s) := Value.vmrg hvenv₂ hvu₂s
        obtain ⟨rr₁, runbody₁, hvrr₁, hreq₁⟩ := mstep_box_inv runbox₁ hvm₁ hvr.1
        obtain ⟨rr₂, runbody₂, hvrr₂, hreq₂⟩ := mstep_box_inv runbox₂ hvm₂ hvr.2
        obtain ⟨b₁, runb₁, hvb₁, hcb₁⟩ := mstep_anno_inv runbody₁ hvrr₁
        obtain ⟨b₂, runb₂, hvb₂, hcb₂⟩ := mstep_anno_inv runbody₂ hvrr₂
        -- reseal the old results at the wider codomain and relate them there
        obtain ⟨s₁, cs₁⟩ := cast_progress hvr.1 htr.1 hsD
        obtain ⟨s₂, cs₂⟩ := cast_progress hvr.2 htr.2 hsD
        have hcs₁' : Cast b₁ D s₁ := cast_trans hcb₁ (hreq₁ ▸ cs₁)
        have hcs₂' : Cast b₂ D s₂ := cast_trans hcb₂ (hreq₂ ▸ cs₂)
        -- rebuild the runs of the recast closures
        have newrun₁ : MStep ρ₁ (.app (.clos u₁env A₁₀ D e₁b) u₁) s₁ := by
          refine MStep.step (Step.sbeta hρ₁ hvenv₁ hvu.1 (cast_trans cu₁ cu₁s)) ?_
          refine mstep_trans (mstep_boxr hρ₁ hvm₁ (mstep_anno hvm₁ runb₁)) ?_
          refine MStep.step (Step.sboxr hρ₁ hvm₁ (Step.sannov hvm₁ hvb₁ hcs₁')) ?_
          exact MStep.step (Step.sboxv hρ₁ hvm₁ (cast_value hvb₁ hcs₁')) MStep.refl
        have newrun₂ : MStep ρ₂ (.app (.clos u₂env A₂₀ D e₂b) u₂) s₂ := by
          refine MStep.step (Step.sbeta hρ₂ hvenv₂ hvu.2 (cast_trans cu₂ cu₂s)) ?_
          refine mstep_trans (mstep_boxr hρ₂ hvm₂ (mstep_anno hvm₂ runb₂)) ?_
          refine MStep.step (Step.sboxr hρ₂ hvm₂ (Step.sannov hvm₂ hvb₂ hcs₂')) ?_
          exact MStep.step (Step.sboxv hρ₂ hvm₂ (cast_value hvb₂ hcs₂')) MStep.refl
        exact ⟨s₁, s₂, newrun₁, newrun₂, ihD hr cs₁ cs₂⟩

-- ── Semantic typing and the fundamental lemma ────────────────────────────────────────

-- Open-term relatedness.  Because contexts are types, LR Δ₁ Δ₂ η Γ *is* the environment
-- relation — no separate context clauses are needed (the λE Fig. 4 unification).
def SemTyp (Δ₁ Δ₂ : BrandStore) (η : Nat → Exp → Exp → Prop) (Γ : Typ) (e₁ e₂ : Exp) (A : Typ) : Prop :=
  ∀ {ρ₁ ρ₂ : Exp}, LR Δ₁ Δ₂ η Γ ρ₁ ρ₂ →
    ∃ w₁ w₂, MStep ρ₁ e₁ w₁ ∧ MStep ρ₂ e₂ w₂ ∧ LR Δ₁ Δ₂ η A w₁ w₂

theorem lr_top_unit : LR Δ₁ Δ₂ η .top .unit .unit := ⟨rfl, rfl⟩

-- A value semantically self-related under the empty context is LR-self-related.
theorem semtyp_value_self {v : Exp} {T : Typ} (h : SemTyp Δ₁ Δ₂ η .top v v T) (hv : Value v)
    : LR Δ₁ Δ₂ η T v v := by
  obtain ⟨w₁, w₂, r₁, r₂, hlr⟩ := h lr_top_unit
  rw [← mstep_value_eq hv r₁, ← mstep_value_eq hv r₂] at hlr
  exact hlr

-- Positional lookup respects the relation.
theorem lr_lookup {B : Typ} {n : Nat} {A : Typ} (hl : Lookup B n A)
    {r₁ r₂ : Exp} (hr : LR Δ₁ Δ₂ η B r₁ r₂)
    : ∃ s₁ s₂, LookupV r₁ n s₁ ∧ LookupV r₂ n s₂ ∧ LR Δ₁ Δ₂ η A s₁ s₂ := by
  induction hl generalizing r₁ r₂ with
  | zero =>
    obtain ⟨_, _, a₁, b₁, a₂, b₂, e₁, e₂, _, hB⟩ := hr
    subst e₁; subst e₂
    exact ⟨b₁, b₂, LookupV.lvzero, LookupV.lvzero, hB⟩
  | succ _ ih =>
    obtain ⟨_, _, a₁, b₁, a₂, b₂, e₁, e₂, hA, _⟩ := hr
    subst e₁; subst e₂
    obtain ⟨s₁, s₂, l₁, l₂, hlr'⟩ := ih hA
    exact ⟨s₁, s₂, LookupV.lvsucc l₁, LookupV.lvsucc l₂, hlr'⟩

-- Selection respects the relation.
theorem lr_rlookup {B : Typ} {l : String} {A : Typ} (hl : RLookup B l A)
    {r₁ r₂ : Exp} (hr : LR Δ₁ Δ₂ η B r₁ r₂)
    : ∃ s₁ s₂, RLookupV r₁ l s₁ ∧ RLookupV r₂ l s₂ ∧ LR Δ₁ Δ₂ η A s₁ s₂ := by
  induction hl generalizing r₁ r₂ with
  | zero =>
    obtain ⟨u₁, u₂, e₁, e₂, hInner⟩ := hr
    subst e₁; subst e₂
    exact ⟨u₁, u₂, RLookupV.rvlzero, RLookupV.rvlzero, hInner⟩
  | landl _ _ ih =>
    obtain ⟨_, _, a₁, b₁, a₂, b₂, e₁, e₂, hA, _⟩ := hr
    subst e₁; subst e₂
    obtain ⟨s₁, s₂, l₁, l₂, hlr'⟩ := ih hA
    exact ⟨s₁, s₂, RLookupV.vlandl l₁, RLookupV.vlandl l₂, hlr'⟩
  | landr _ _ ih =>
    obtain ⟨_, _, a₁, b₁, a₂, b₂, e₁, e₂, _, hB⟩ := hr
    subst e₁; subst e₂
    obtain ⟨s₁, s₂, l₁, l₂, hlr'⟩ := ih hB
    exact ⟨s₁, s₂, RLookupV.vlandr l₁, RLookupV.vlandr l₂, hlr'⟩

-- The fundamental lemma: every well-typed term is semantically self-related.  Strong
-- normalization of λE^≤ is an immediate corollary.
theorem fundamental {Γ : Typ} {e : Exp} {A : Typ} (ht : HasType noBrands Γ e A)
    : SemTyp Δ₁ Δ₂ η Γ e e A := by
  induction ht with
  | tquery =>
    intro ρ₁ ρ₂ hρ
    have hv := lr_value hρ
    exact ⟨ρ₁, ρ₂, mstep_one (Step.squery hv.1), mstep_one (Step.squery hv.2), hρ⟩
  | tint =>
    intro ρ₁ ρ₂ _
    exact ⟨_, _, MStep.refl, MStep.refl, _, rfl, rfl⟩
  | tunit =>
    intro ρ₁ ρ₂ _
    exact ⟨_, _, MStep.refl, MStep.refl, rfl, rfl⟩
  | tapp _ _ ih₁ ih₂ =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨f₁, f₂, rf₁, rf₂, hf⟩ := ih₁ hρ
    obtain ⟨a₁, a₂, ra₁, ra₂, ha⟩ := ih₂ hρ
    obtain ⟨hvf₁, hvf₂, _, _, CL⟩ := hf
    obtain ⟨w₁, w₂, rw₁, rw₂, hw⟩ := CL a₁ a₂ ha ρ₁ ρ₂ hvρ.1 hvρ.2
    refine ⟨w₁, w₂, ?_, ?_, hw⟩
    · exact mstep_trans (mstep_appl hvρ.1 rf₁)
        (mstep_trans (mstep_appr hvρ.1 hvf₁ ra₁) rw₁)
    · exact mstep_trans (mstep_appl hvρ.2 rf₂)
        (mstep_trans (mstep_appr hvρ.2 hvf₂ ra₂) rw₂)
  | tbox _ _ ih₁ ih₂ =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨g₁, g₂, rg₁, rg₂, hg⟩ := ih₁ hρ
    have hvg := lr_value hg
    obtain ⟨w₁, w₂, rw₁, rw₂, hw⟩ := ih₂ hg
    have hvw := lr_value hw
    refine ⟨w₁, w₂, ?_, ?_, hw⟩
    · exact mstep_trans (mstep_boxl hvρ.1 rg₁)
        (mstep_trans (mstep_boxr hvρ.1 hvg.1 rw₁)
          (mstep_one (Step.sboxv hvρ.1 hvg.1 hvw.1)))
    · exact mstep_trans (mstep_boxl hvρ.2 rg₂)
        (mstep_trans (mstep_boxr hvρ.2 hvg.2 rw₂)
          (mstep_one (Step.sboxv hvρ.2 hvg.2 hvw.2)))
  | tproj _ hl ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨r₁, r₂, rr₁, rr₂, hr⟩ := ih hρ
    have hvr := lr_value hr
    obtain ⟨s₁, s₂, l₁, l₂, hs⟩ := lr_lookup hl hr
    refine ⟨s₁, s₂, ?_, ?_, hs⟩
    · exact mstep_trans (mstep_proj hvρ.1 rr₁) (mstep_one (Step.sprojv hvρ.1 hvr.1 l₁))
    · exact mstep_trans (mstep_proj hvρ.2 rr₂) (mstep_one (Step.sprojv hvρ.2 hvr.2 l₂))
  | trcd _ ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨w₁, w₂, rw₁, rw₂, hw⟩ := ih hρ
    exact ⟨_, _, mstep_lrec hvρ.1 rw₁, mstep_lrec hvρ.2 rw₂, _, _, rfl, rfl, hw⟩
  | trproj _ hl ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨r₁, r₂, rr₁, rr₂, hr⟩ := ih hρ
    have hvr := lr_value hr
    obtain ⟨s₁, s₂, l₁, l₂, hs⟩ := lr_rlookup hl hr
    refine ⟨s₁, s₂, ?_, ?_, hs⟩
    · exact mstep_trans (mstep_rproj hvρ.1 rr₁) (mstep_one (Step.srprojv hvρ.1 hvr.1 l₁))
    · exact mstep_trans (mstep_rproj hvρ.2 rr₂) (mstep_one (Step.srprojv hvρ.2 hvr.2 l₂))
  | tmrg _ _ hd₁ hd₂ ih₁ ih₂ =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    have htρ := lr_typed hρ
    obtain ⟨a₁, a₂, ra₁, ra₂, ha⟩ := ih₁ hρ
    have hva := lr_value ha
    have hta := lr_typed ha
    have hρ' : LR Δ₁ Δ₂ η (.and _ _) (.mrg ρ₁ a₁) (.mrg ρ₂ a₂) :=
      ⟨HasType.tmergev hvρ.1 hva.1 htρ.1 hta.1
          (disjoint_consistent hvρ.1 hva.1 htρ.1 hta.1 (disj_symm hd₁)),
        HasType.tmergev hvρ.2 hva.2 htρ.2 hta.2
          (disjoint_consistent hvρ.2 hva.2 htρ.2 hta.2 (disj_symm hd₁)),
        _, _, _, _, rfl, rfl, hρ, ha⟩
    obtain ⟨b₁, b₂, rb₁, rb₂, hb⟩ := ih₂ hρ'
    have hvb := lr_value hb
    have htb := lr_typed hb
    refine ⟨.mrg a₁ b₁, .mrg a₂ b₂, ?_, ?_, ?_⟩
    · exact mstep_trans (mstep_mrgl hvρ.1 ra₁) (mstep_mrgr hvρ.1 hva.1 rb₁)
    · exact mstep_trans (mstep_mrgl hvρ.2 ra₂) (mstep_mrgr hvρ.2 hva.2 rb₂)
    · exact ⟨HasType.tmergev hva.1 hvb.1 hta.1 htb.1
          (disjoint_consistent hva.1 hvb.1 hta.1 htb.1 hd₂),
        HasType.tmergev hva.2 hvb.2 hta.2 htb.2
          (disjoint_consistent hva.2 hvb.2 hta.2 htb.2 hd₂),
        _, _, _, _, rfl, rfl, ha, hb⟩
  | tmergev hv₁ hv₂ hp hq hcons ih₁ ih₂ =>
    intro ρ₁ ρ₂ _
    exact ⟨_, _, MStep.refl, MStep.refl,
      HasType.tmergev hv₁ hv₂ (hastype_weaken_store storele_noBrands hp)
        (hastype_weaken_store storele_noBrands hq) hcons,
      HasType.tmergev hv₁ hv₂ (hastype_weaken_store storele_noBrands hp)
        (hastype_weaken_store storele_noBrands hq) hcons,
      _, _, _, _, rfl, rfl, semtyp_value_self ih₁ hv₁, semtyp_value_self ih₂ hv₂⟩
  | tlam hd hb ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    have htρ := lr_typed hρ
    refine ⟨_, _, mstep_one (Step.sclos hvρ.1), mstep_one (Step.sclos hvρ.2), ?_⟩
    refine ⟨Value.vclos hvρ.1, Value.vclos hvρ.2,
      HasType.tclos hvρ.1 htρ.1 hd (hastype_weaken_store storele_noBrands hb)
        (sub_refl _) (sub_refl _),
      HasType.tclos hvρ.2 htρ.2 hd (hastype_weaken_store storele_noBrands hb)
        (sub_refl _) (sub_refl _), ?_⟩
    intro u₁ u₂ hu σ₁ σ₂ hσ₁ hσ₂
    have hvu := lr_value hu
    have htu := lr_typed hu
    obtain ⟨u₁', cu₁⟩ := cast_progress hvu.1 htu.1 (sub_refl _)
    obtain ⟨u₂', cu₂⟩ := cast_progress hvu.2 htu.2 (sub_refl _)
    have hu' := cast_lr (sub_refl _) hu cu₁ cu₂
    have hvu' := lr_value hu'
    have htu' := lr_typed hu'
    have hρ' : LR Δ₁ Δ₂ η (.and _ _) (.mrg ρ₁ u₁') (.mrg ρ₂ u₂') :=
      ⟨HasType.tmergev hvρ.1 hvu'.1 htρ.1 htu'.1
          (disjoint_consistent hvρ.1 hvu'.1 htρ.1 htu'.1 hd),
        HasType.tmergev hvρ.2 hvu'.2 htρ.2 htu'.2
          (disjoint_consistent hvρ.2 hvu'.2 htρ.2 htu'.2 hd),
        _, _, _, _, rfl, rfl, hρ, hu'⟩
    obtain ⟨b₁, b₂, rb₁, rb₂, hbb⟩ := ih hρ'
    have hvb := lr_value hbb
    have htb := lr_typed hbb
    obtain ⟨s₁, cs₁⟩ := cast_progress hvb.1 htb.1 (sub_refl _)
    obtain ⟨s₂, cs₂⟩ := cast_progress hvb.2 htb.2 (sub_refl _)
    have hvm₁ : Value (.mrg ρ₁ u₁') := Value.vmrg hvρ.1 hvu'.1
    have hvm₂ : Value (.mrg ρ₂ u₂') := Value.vmrg hvρ.2 hvu'.2
    refine ⟨s₁, s₂, ?_, ?_, cast_lr (sub_refl _) hbb cs₁ cs₂⟩
    · refine MStep.step (Step.sbeta hσ₁ hvρ.1 hvu.1 cu₁) ?_
      refine mstep_trans (mstep_boxr hσ₁ hvm₁ (mstep_anno hvm₁ rb₁)) ?_
      refine MStep.step (Step.sboxr hσ₁ hvm₁ (Step.sannov hvm₁ hvb.1 cs₁)) ?_
      exact MStep.step (Step.sboxv hσ₁ hvm₁ (cast_value hvb.1 cs₁)) MStep.refl
    · refine MStep.step (Step.sbeta hσ₂ hvρ.2 hvu.2 cu₂) ?_
      refine mstep_trans (mstep_boxr hσ₂ hvm₂ (mstep_anno hvm₂ rb₂)) ?_
      refine MStep.step (Step.sboxr hσ₂ hvm₂ (Step.sannov hvm₂ hvb.2 cs₂)) ?_
      exact MStep.step (Step.sboxv hσ₂ hvm₂ (cast_value hvb.2 cs₂)) MStep.refl
  | tclos hv henv₁ hd hb hs₁ hs₂ ih_env ih_b =>
    intro ρ₁ ρ₂ _
    have hgg := semtyp_value_self ih_env hv
    refine ⟨_, _, MStep.refl, MStep.refl, ?_⟩
    refine ⟨Value.vclos hv, Value.vclos hv,
      HasType.tclos hv (hastype_weaken_store storele_noBrands henv₁) hd
        (hastype_weaken_store storele_noBrands hb) hs₁ hs₂,
      HasType.tclos hv (hastype_weaken_store storele_noBrands henv₁) hd
        (hastype_weaken_store storele_noBrands hb) hs₁ hs₂, ?_⟩
    intro u₁ u₂ hu σ₁ σ₂ hσ₁ hσ₂
    have hvu := lr_value hu
    have htu := lr_typed hu
    obtain ⟨u₁', cu₁⟩ := cast_progress hvu.1 htu.1 hs₂
    obtain ⟨u₂', cu₂⟩ := cast_progress hvu.2 htu.2 hs₂
    have hu' := cast_lr hs₂ hu cu₁ cu₂
    have hvu' := lr_value hu'
    have htu' := lr_typed hu'
    have hgv := lr_value hgg
    have hgt := lr_typed hgg
    have hρ' : LR Δ₁ Δ₂ η (.and _ _) (.mrg _ u₁') (.mrg _ u₂') :=
      ⟨HasType.tmergev hgv.1 hvu'.1 hgt.1 htu'.1
          (disjoint_consistent hgv.1 hvu'.1 hgt.1 htu'.1 hd),
        HasType.tmergev hgv.2 hvu'.2 hgt.2 htu'.2
          (disjoint_consistent hgv.2 hvu'.2 hgt.2 htu'.2 hd),
        _, _, _, _, rfl, rfl, hgg, hu'⟩
    obtain ⟨b₁, b₂, rb₁, rb₂, hbb⟩ := ih_b hρ'
    have hvb := lr_value hbb
    have htb := lr_typed hbb
    obtain ⟨s₁, cs₁⟩ := cast_progress hvb.1 htb.1 hs₁
    obtain ⟨s₂, cs₂⟩ := cast_progress hvb.2 htb.2 hs₁
    have hvm₁ : Value (.mrg _ u₁') := Value.vmrg hv hvu'.1
    have hvm₂ : Value (.mrg _ u₂') := Value.vmrg hv hvu'.2
    refine ⟨s₁, s₂, ?_, ?_, cast_lr hs₁ hbb cs₁ cs₂⟩
    · refine MStep.step (Step.sbeta hσ₁ hv hvu.1 cu₁) ?_
      refine mstep_trans (mstep_boxr hσ₁ hvm₁ (mstep_anno hvm₁ rb₁)) ?_
      refine MStep.step (Step.sboxr hσ₁ hvm₁ (Step.sannov hvm₁ hvb.1 cs₁)) ?_
      exact MStep.step (Step.sboxv hσ₁ hvm₁ (cast_value hvb.1 cs₁)) MStep.refl
    · refine MStep.step (Step.sbeta hσ₂ hv hvu.2 cu₂) ?_
      refine mstep_trans (mstep_boxr hσ₂ hvm₂ (mstep_anno hvm₂ rb₂)) ?_
      refine MStep.step (Step.sboxr hσ₂ hvm₂ (Step.sannov hvm₂ hvb.2 cs₂)) ?_
      exact MStep.step (Step.sboxv hσ₂ hvm₂ (cast_value hvb.2 cs₂)) MStep.refl
  | tanno _ hsub ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨r₁, r₂, rr₁, rr₂, hr⟩ := ih hρ
    have hvr := lr_value hr
    have htr := lr_typed hr
    obtain ⟨s₁, cs₁⟩ := cast_progress hvr.1 htr.1 hsub
    obtain ⟨s₂, cs₂⟩ := cast_progress hvr.2 htr.2 hsub
    refine ⟨s₁, s₂, ?_, ?_, cast_lr hsub hr cs₁ cs₂⟩
    · exact mstep_trans (mstep_anno hvρ.1 rr₁) (mstep_one (Step.sannov hvρ.1 hvr.1 cs₁))
    · exact mstep_trans (mstep_anno hvρ.2 rr₂) (mstep_one (Step.sannov hvρ.2 hvr.2 cs₂))
  -- Clients cannot brand, seal or unseal: these rules need a known representation.
  | twrap hΔ _ _ _ => nomatch hΔ
  | tseal hΔ _ _ _ _ => nomatch hΔ
  | tunseal hΔ _ _ _ _ _ => nomatch hΔ

-- ── Corollaries ──────────────────────────────────────────────────────────────────────

-- Strong normalization of well-typed λE^≤ programs (λE Theorem 4.16 for the extended
-- calculus; genuinely new for a TDOS merge calculus).
theorem normalization {e : Exp} {A : Typ} (ht : HasType noBrands .top e A)
    : ∃ v, Value v ∧ MStep .unit e v := by
  obtain ⟨w₁, _, r₁, _, hlr⟩ :=
    fundamental (Δ₁ := noBrands) (Δ₂ := noBrands) (η := fun _ _ _ => False) ht lr_top_unit
  exact ⟨w₁, (lr_value hlr).1, r₁⟩

-- THE SEALING THEOREM.  A client typed against the seal A and observing at Int cannot
-- distinguish two sealed values that are related at A: both runs produce the same
-- literal.  Equality holds at base observations; at higher types agreement is the
-- logical relation (extensional at arrows), not syntactic equality.
theorem sealing {A : Typ} {p₁' p₂' : Exp} (hagree : LR Δ₁ Δ₂ η A p₁' p₂')
    {e : Exp} (hcl : HasType noBrands A e .int)
    : ∃ i, MStep p₁' e (.lit i) ∧ MStep p₂' e (.lit i) := by
  obtain ⟨w₁, w₂, r₁, r₂, hlr⟩ := fundamental hcl hagree
  obtain ⟨i, e₁, e₂⟩ := hlr
  subst e₁; subst e₂
  exact ⟨i, r₁, r₂⟩

-- The full narrative form: two providers p₁, p₂ (of possibly different types B₁, B₂ below
-- the seal), sealed by casting at A; if the sealed views agree at A, then a client typed
-- against A, run against either sealed provider via a box, computes the same integer.
theorem sealing_providers {B₁ B₂ A : Typ} {p₁ p₂ p₁' p₂' : Exp}
    (hv₁ : Value p₁) (hv₂ : Value p₂)
    (_ht₁ : HasType Δ₁ .top p₁ B₁) (_ht₂ : HasType Δ₂ .top p₂ B₂)
    (hc₁ : Cast p₁ A p₁') (hc₂ : Cast p₂ A p₂')
    (hagree : LR Δ₁ Δ₂ η A p₁' p₂')
    {e : Exp} (hcl : HasType noBrands A e .int)
    {ρ₁ ρ₂ : Exp} (hρ₁ : Value ρ₁) (hρ₂ : Value ρ₂)
    : ∃ i, MStep ρ₁ (.box p₁' e) (.lit i) ∧ MStep ρ₂ (.box p₂' e) (.lit i) := by
  obtain ⟨i, r₁, r₂⟩ := sealing hagree hcl
  have hvp₁ : Value p₁' := cast_value hv₁ hc₁
  have hvp₂ : Value p₂' := cast_value hv₂ hc₂
  refine ⟨i, ?_, ?_⟩
  · exact mstep_trans (mstep_boxr hρ₁ hvp₁ r₁)
      (mstep_one (Step.sboxv hρ₁ hvp₁ Value.vint))
  · exact mstep_trans (mstep_boxr hρ₂ hvp₂ r₂)
      (mstep_one (Step.sboxv hρ₂ hvp₂ Value.vint))

end Seal

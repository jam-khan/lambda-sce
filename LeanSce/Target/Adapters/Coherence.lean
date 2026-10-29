import LeanSce.Target.Adapters.Evaluation
import LeanSce.Target.Adapters.Naturality
import LeanSce.Target.Adapters.Typing
import LeanSce.Target.Definitions.Typing
import LeanSce.Target.LogicalRelation.Contexts
import LeanSce.Target.LogicalRelation.Definitions
import LeanSce.Target.LogicalRelation.Evaluation
import LeanSce.Target.LogicalRelation.Fundamental
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Substitution

/-!
# Target / Adapters / Coherence

Proofs and supporting constructions for coherence.
-/

/-! ## Adapter Coherence Statement -/

namespace LeanSce.Target.Goals

/-- T2.5: the two canonical paths agree in every typed ground observation
    context, for every satisfying closing substitution and ambient value. -/
def AdapterCoherence : Prop :=
  ∀ (Δ : Context) (a b c h : Typ) (e c₁ c₂ c₃ : Expr),
    Context.Valid Δ → Adapts Δ a b c₁ → Adapts Δ b c c₂ → Adapts Δ a c c₃ →
    HasType Δ h e a → ContextualEq Δ h c (.app c₂ (.app c₁ e)) (.app c₃ e)

end LeanSce.Target.Goals

/-! ## Adapter Composition Binder -/

namespace LeanSce.Target

/-- A well-formed universal supplies its well-formed static binder context. -/
theorem Context.Valid.extend_forall (hΔ : Context.Valid Δ)
    (wa : WellFormed Δ (.all k gs a)) : Context.Valid (Δ.extend k gs) := by
  cases wa
  exact .extend hΔ (by assumption) (by assumption)

/-- A closed witness satisfying the universal's guards closes its binder. -/
theorem Closing.instantiate_forall (hθ : Closing θ Δ)
    (wa : WellFormed Δ (.all k gs a))
    (hk : u.kind = k) (hu : u.WellFormed .empty)
    (hg : Entails .empty ((gs.subst θ.lift).open u)) :
    Closing (θ.instantiate u) (Δ.extend k gs) := by
  have fresh : FreshGuards k gs := by cases wa; assumption
  exact hθ.instantiate fresh hk hu hg

/-- A closed witness satisfying equivalent guards closes the same binder. -/
theorem Closing.instantiate_guardEq (hθ : Closing θ Δ)
    (wa : WellFormed Δ (.all k gs a)) (he : GuardsEq hs gs)
    (hk : u.kind = k) (hu : u.WellFormed .empty)
    (hg : Entails .empty ((hs.subst θ.lift).open u)) :
    Closing (θ.instantiate u) (Δ.extend k gs) := by
  have fresh : FreshGuards k gs := by cases wa; assumption
  have hh := (he.entails_subst (Δ := .empty) (θ.instantiate u)).mp
    (by simpa only [Ty.subst_instantiate] using hg)
  exact hθ.instantiate fresh hk hu (by simpa only [Ty.subst_instantiate] using hh)

/-- The three body matchers share one witness, even though their static
    contexts and the middle interface guards may differ. -/
theorem universal_composition_binders
    (wa₁ : WellFormed Δ (.all k gs a))
    (wa₂ : WellFormed Γ (.all k hs b))
    (wa₃ : WellFormed Ξ (.all k gs a)) (he : GuardsEq gs hs)
    (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ) (hΞ : Context.Valid Ξ)
    (hθ₁ : Closing θ Δ) (hθ₂ : Closing θ Γ) (hθ₃ : Closing θ Ξ)
    (hk : u.kind = k) (hu : u.WellFormed .empty)
    (hg : Entails .empty ((gs.subst θ.lift).open u)) :
    Context.Valid (Δ.extend k gs) ∧ Context.Valid (Γ.extend k hs) ∧
      Context.Valid (Ξ.extend k gs) ∧
      Closing (θ.instantiate u) (Δ.extend k gs) ∧
      Closing (θ.instantiate u) (Γ.extend k hs) ∧
      Closing (θ.instantiate u) (Ξ.extend k gs) := by
  exact ⟨hΔ.extend_forall wa₁,hΓ.extend_forall wa₂,hΞ.extend_forall wa₃,
    hθ₁.instantiate_forall wa₁ hk hu hg,
    hθ₂.instantiate_guardEq wa₂ he hk hu hg,
    hθ₃.instantiate_forall wa₃ hk hu hg⟩

end LeanSce.Target

/-! ## Adapter Arrow Composition -/

namespace LeanSce.Target
open LogicalRelation

/-- Proper arrow paths compose contravariantly on arguments and covariantly on
    results. The saved original function is the only potentially diverging call. -/
theorem adapter_arrow_composition
    (d₁ : Adapts Δ b₁ a₁ down₁) (u₁ : Adapts Δ a₂ b₂ up₁)
    (d₂ : Adapts Γ c₁ b₁ down₂) (u₂ : Adapts Γ b₂ c₂ up₂)
    (d₃ : Adapts Ξ c₁ a₁ down₃) (u₃ : Adapts Ξ a₂ c₂ up₃)
    (hne₁ : ¬ TyEq (.arr a₁ a₂) (.arr b₁ b₂))
    (hne₂ : ¬ TyEq (.arr b₁ b₂) (.arr c₁ c₂))
    (hne₃ : ¬ TyEq (.arr a₁ a₂) (.arr c₁ c₂))
    (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ) (hΞ : Context.Valid Ξ)
    (hθ : Closing θ Δ) (hΘ : Closing θ Γ) (hϑ : Closing θ Ξ)
    (hf : ValRel n ((Ty.arr a₁ a₂).subst θ) f F)
    (hdom : ∀ j, j < n → ∀ x X, ValRel j (c₁.subst θ) x X →
      ValRel j (a₁.subst θ)
        (adaptedValue (down₁.subst θ) (adaptedValue (down₂.subst θ) x))
        (adaptedValue (down₃.subst θ) X))
    (hcod : ∀ m, m < n → ∀ r R, ValRel m (a₂.subst θ) r R →
      ValRel m (c₂.subst θ)
        (adaptedValue (up₂.subst θ) (adaptedValue (up₁.subst θ) r))
        (adaptedValue (up₃.subst θ) R)) :
    ValRel n ((Ty.arr c₁ c₂).subst θ)
      (adaptedValue ((arrowAdapter b₁ b₂ c₁ down₂ up₂).subst θ)
        (adaptedValue ((arrowAdapter a₁ a₂ b₁ down₁ up₁).subst θ) f))
      (adaptedValue ((arrowAdapter a₁ a₂ c₁ down₃ up₃).subst θ) F) := by
  let f₁ := adaptedValue ((arrowAdapter a₁ a₂ b₁ down₁ up₁).subst θ) f
  let left := adaptedValue ((arrowAdapter b₁ b₂ c₁ down₂ up₂).subst θ) f₁
  let right := adaptedValue ((arrowAdapter a₁ a₂ c₁ down₃ up₃).subst θ) F
  let body₁ : Expr := .app (up₁.subst θ) (.app (.ix 1) (.app (down₁.subst θ) (.ix 0)))
  let body₂ : Expr := .app (up₂.subst θ) (.app (.ix 1) (.app (down₂.subst θ) (.ix 0)))
  let body₃ : Expr := .app (up₃.subst θ) (.app (.ix 1) (.app (down₃.subst θ) (.ix 0)))
  have hm₁ := Adapts.arrow hne₁ d₁ u₁
  have hm₂ := Adapts.arrow hne₂ d₂ u₂
  have hm₃ := Adapts.arrow hne₃ d₃ u₃
  have hf₁ : ValueType .empty f₁ ((Ty.arr b₁ b₂).subst θ) := hm₁.adapted_typed hΔ hθ hf.left
  have hl : ValueType .empty left ((Ty.arr c₁ c₂).subst θ) := hm₂.adapted_typed hΓ hΘ hf₁
  have hr : ValueType .empty right ((Ty.arr c₁ c₂).subst θ) := hm₃.adapted_typed hΞ hϑ hf.right
  have he₁ : f₁ = .clo (.pair .unit f) (b₁.subst θ) body₁ := by
    simp only [f₁,arrowAdapter_subst,adapted_arrow hf.left.1]; rfl
  have hel : left = .clo (.pair .unit f₁) (c₁.subst θ) body₂ := by
    simp only [left,arrowAdapter_subst,adapted_arrow hf₁.1]; rfl
  have her : right = .clo (.pair .unit F) (c₁.subst θ) body₃ := by
    simp only [right,arrowAdapter_subst,adapted_arrow hf.right.1]; rfl
  rw [ValRel]
  refine ⟨hl,hr,?_⟩
  change ShapeRel n (.arr (c₁.subst θ) (c₂.subst θ)) left right
  rw [ShapeRel]
  intro j hj x X hx
  let q₂ := adaptedValue (down₂.subst θ) x
  have hq₂ : ValueType .empty q₂ (b₁.subst θ) := d₂.adapted_typed hΓ hΘ hx.left
  have henvl := arrow_env_typed hf₁ hx.left
  have henvi := arrow_env_typed hf.left hq₂
  have henvr := arrow_env_typed hf.right hx.right
  have hact : ApplyBody f₁ q₂ (.pair (.pair .unit f) q₂,body₁) := by rw [he₁]; exact .clo
  refine ⟨(.pair (.pair .unit f₁) x,body₂),(.pair (.pair .unit F) X,body₃),?_,?_,?_⟩
  · rw [hel]; exact .clo
  · rw [her]; exact .clo
  have hbase := (hf.mono (Nat.le_of_lt hj)).app (hdom j hj x X hx) henvi.1 henvr.1
  apply hbase.pipelines
    (P := fun r => adaptedValue (up₂.subst θ) (adaptedValue (up₁.subst θ) r))
    (Q := fun R => adaptedValue (up₃.subst θ) R)
  · intro k hk w hw
    obtain ⟨mid,i,hi,hcall,hew⟩ := arrow_pipeline_inv d₂ u₂ hΓ hΘ hf₁ hx.left hw
    obtain ⟨p,hp,hinner⟩ := hact.counted_inv henvl.1 hf₁.1 hq₂.1 hcall
    obtain ⟨r,t,ht,hvalue,hemid⟩ := arrow_pipeline_inv d₁ u₁ hΔ hθ hf.left hq₂ hinner
    exact ⟨r,t,by omega,hvalue,by rw [hew,hemid]⟩
  · intro k hk W hW
    exact arrow_pipeline_inv d₃ u₃ hΞ hϑ hf.right hx.right hW
  · intro r hvalue
    have hinner := arrow_pipeline_forward d₁ u₁ hΔ hθ hf.left hq₂ hvalue
    have hcall := hact.terminates henvl.1 hf₁.1 hq₂.1 hinner
    exact arrow_pipeline_forward d₂ u₂ hΓ hΘ hf₁ hx.left hcall
  · intro R hvalue
    exact arrow_pipeline_forward d₃ u₃ hΞ hϑ hf.right hx.right hvalue
  · intro m hm r R hvalue
    exact hcod m (Nat.lt_of_le_of_lt hm hj) r R hvalue

end LeanSce.Target

/-! ## Adapter Universal Composition -/

namespace LeanSce.Target
open LogicalRelation

/-- Instantiation activates frozen body code in the adapter's saved input. -/
theorem adapted_universal_body (hf : Value f) (hk : u.kind = k) :
    TypeBody (adaptedValue ((universalAdapter a k gs code).subst θ) f) u
      (.pair .unit f,.app (code.subst (θ.instantiate u)) (.tapp (.ix 0) u)) := by
  rw [universalAdapter_subst,adapted_universal hf]
  have hb := TypeBody.tclo (cap := .pair .unit f) (k := k)
    (gs := gs.subst θ.lift)
    (body := .app (code.subst θ.lift) (.tapp (.ix 0) (Arg.variable k 0))) (u := u)
  simpa only [Term.subst,Arg.variable_open hk,← Term.subst_instantiate] using hb

/-- Composition of proper universal adapters reduces to composition of their
    instantiated body adapters, at the exact residual logical index. -/
theorem universal_composition
    (wa₁ : WellFormed Δ (.all k gs a)) (wb₁ : WellFormed Δ (.all k hs b))
    (hn₁ : ¬ TyEq (.all k gs a) (.all k hs b)) (hg₁ : GuardsEq gs hs)
    (d₁ : Adapts (Δ.extend k gs) a b c₁)
    (wa₂ : WellFormed Γ (.all k hs b)) (wb₂ : WellFormed Γ (.all k is c))
    (hn₂ : ¬ TyEq (.all k hs b) (.all k is c)) (hg₂ : GuardsEq hs is)
    (d₂ : Adapts (Γ.extend k hs) b c c₂)
    (wa₃ : WellFormed Ξ (.all k gs a)) (wb₃ : WellFormed Ξ (.all k is c))
    (hn₃ : ¬ TyEq (.all k gs a) (.all k is c)) (hg₃ : GuardsEq gs is)
    (d₃ : Adapts (Ξ.extend k gs) a c c₃)
    (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ) (hΞ : Context.Valid Ξ)
    (hθ₁ : Closing θ Δ) (hθ₂ : Closing θ Γ) (hθ₃ : Closing θ Ξ)
    (hv : ValRel n ((Ty.all k gs a).subst θ) f F)
    (ih : ∀ j, j < n → ∀ u, u.kind = k → u.WellFormed .empty →
      Entails .empty ((gs.subst θ.lift).open u) →
      ∀ r R, ValRel j (a.subst (θ.instantiate u)) r R →
      ValRel j (c.subst (θ.instantiate u))
        (adaptedValue (c₂.subst (θ.instantiate u))
          (adaptedValue (c₁.subst (θ.instantiate u)) r))
        (adaptedValue (c₃.subst (θ.instantiate u)) R)) :
    ValRel n ((Ty.all k is c).subst θ)
      (adaptedValue ((universalAdapter (.all k hs b) k hs c₂).subst θ)
        (adaptedValue ((universalAdapter (.all k gs a) k gs c₁).subst θ) f))
      (adaptedValue ((universalAdapter (.all k gs a) k gs c₃).subst θ) F) := by
  let D₁ := Adapts.all wa₁ wb₁ hn₁ hg₁ d₁
  let D₂ := Adapts.all wa₂ wb₂ hn₂ hg₂ d₂
  let D₃ := Adapts.all wa₃ wb₃ hn₃ hg₃ d₃
  let f₁ := adaptedValue ((universalAdapter (.all k gs a) k gs c₁).subst θ) f
  have hf₁ : ValueType .empty f₁ ((Ty.all k hs b).subst θ) :=
    D₁.adapted_typed hΔ hθ₁ hv.left
  have hleft := D₂.adapted_typed hΓ hθ₂ hf₁
  have hright := D₃.adapted_typed hΞ hθ₃ hv.right
  have fresh₁ : FreshGuards k gs := by cases wa₁; assumption
  have fresh₂ : FreshGuards k hs := by cases wa₂; assumption
  have fresh₃ : FreshGuards k gs := by cases wa₃; assumption
  have valid₁ : Context.Valid (Δ.extend k gs) := by
    cases wa₁; exact .extend hΔ (by assumption) (by assumption)
  have valid₂ : Context.Valid (Γ.extend k hs) := by
    cases wa₂; exact .extend hΓ (by assumption) (by assumption)
  have valid₃ : Context.Valid (Ξ.extend k gs) := by
    cases wa₃; exact .extend hΞ (by assumption) (by assumption)
  rw [ValRel]
  refine ⟨hleft,hright,?_⟩
  simp only [Ty.subst,ShapeRel]
  intro j hj u hk hu hgu
  have hgs : Entails .empty ((gs.subst θ.lift).open u) := by
    have hh := (hg₃.entails_subst (Δ := .empty) (θ.instantiate u)).mpr
      (by simpa only [Ty.subst_instantiate] using hgu)
    simpa only [Ty.subst_instantiate] using hh
  have hhs : Entails .empty ((hs.subst θ.lift).open u) := by
    have hh := (hg₁.entails_subst (Δ := .empty) (θ.instantiate u)).mp
      (by simpa only [Ty.subst_instantiate] using hgs)
    simpa only [Ty.subst_instantiate] using hh
  have close₁ := hθ₁.instantiate fresh₁ hk hu hgs
  have close₂ := hθ₂.instantiate fresh₂ hk hu hhs
  have close₃ := hθ₃.instantiate fresh₃ hk hu hgs
  let σ := θ.instantiate u
  have envf : ValueType .empty (.pair .unit f) (.prod .unit ((Ty.all k gs a).subst θ)) :=
    ⟨by simpa [Value,Term.isValue] using hv.left.1,.pair (.unit .unit) hv.left.2⟩
  have envF : ValueType .empty (.pair .unit F) (.prod .unit ((Ty.all k gs a).subst θ)) :=
    ⟨by simpa [Value,Term.isValue] using hv.right.1,.pair (.unit .unit) hv.right.2⟩
  have envf₁ : ValueType .empty (.pair .unit f₁) (.prod .unit ((Ty.all k hs b).subst θ)) :=
    ⟨by simpa [Value,Term.isValue] using hf₁.1,.pair (.unit .unit) hf₁.2⟩
  have htf : HasType .empty (.prod .unit ((Ty.all k gs a).subst θ)) (.tapp f u) (a.subst σ) := by
    simpa only [σ,Ty.subst_instantiate,Ty.subst] using
      HasType.tapp (hv.left.2.value_reambient hv.left.1 _
        (.prod .unit (wa₁.subst hθ₁.respects))) hk hu hgs
  have htF : HasType .empty (.prod .unit ((Ty.all k gs a).subst θ)) (.tapp F u) (a.subst σ) := by
    simpa only [σ,Ty.subst_instantiate,Ty.subst] using
      HasType.tapp (hv.right.2.value_reambient hv.right.1 _
        (.prod .unit (wa₁.subst hθ₁.respects))) hk hu hgs
  have htf₁ : HasType .empty (.prod .unit ((Ty.all k hs b).subst θ)) (.tapp f₁ u) (b.subst σ) := by
    simpa only [σ,Ty.subst_instantiate,Ty.subst] using
      HasType.tapp (hf₁.2.value_reambient hf₁.1 _
        (.prod .unit (wa₂.subst hθ₂.respects))) hk hu hhs
  have base : ExprRel j (a.subst σ)
      (.pair .unit f,.tapp f u) (.pair .unit F,.tapp F u) := by
    simpa only [σ,Ty.subst_instantiate,Ty.subst] using
      (hv.mono (Nat.le_of_lt hj)).tapp hk hu hgs envf.1 envF.1
  have body₁ := adapted_universal_body (θ := θ) (a := .all k gs a) (gs := gs)
    (code := c₁) hv.left.1 hk
  have body₂ := adapted_universal_body (θ := θ) (a := .all k hs b) (gs := hs)
    (code := c₂) hf₁.1 hk
  have body₃ := adapted_universal_body (θ := θ) (a := .all k gs a) (gs := gs)
    (code := c₃) hv.right.1 hk
  refine ⟨_,_,body₂,body₃,?_⟩
  change ExprRel j ((c.subst θ.lift).open u)
    (.pair .unit f₁,.app (c₂.subst σ) (.tapp (.ix 0) u))
    (.pair .unit F,.app (c₃.subst σ) (.tapp (.ix 0) u))
  rw [← Ty.subst_instantiate]
  apply base.pipelines
    (P := fun r => adaptedValue (c₂.subst σ) (adaptedValue (c₁.subst σ) r))
    (Q := fun R => adaptedValue (c₃.subst σ) R)
  · intro k' _ w hw
    obtain ⟨s,l,hl,hs,hw⟩ := universal_pipeline_inv d₂ valid₂ close₂ envf₁ htf₁ hw
    obtain ⟨p,hp,hbody⟩ := body₁.counted_inv envf₁.1 hf₁.1 hs
    obtain ⟨r,i,hi,hr,hs⟩ := universal_pipeline_inv d₁ valid₁ close₁ envf htf hbody
    exact ⟨r,i,by omega,hr,by rw [hw,hs]⟩
  · intro k' _ W hW
    exact universal_pipeline_inv d₃ valid₃ close₃ envF htF hW
  · intro r hr
    have ht := universal_pipeline_forward d₁ valid₁ close₁ envf htf hr
    have hcall := body₁.terminates envf₁.1 hf₁.1 ht
    exact universal_pipeline_forward d₂ valid₂ close₂ envf₁ htf₁ hcall
  · intro R hR
    exact universal_pipeline_forward d₃ valid₃ close₃ envF htF hR
  · intro m hm r R hr
    exact ih m (by omega) u hk hu hgs r R hr

end LeanSce.Target

/-! ## Adapter Coherence Lifting -/

namespace LeanSce.Target
open LogicalRelation

/-- Same-index composition on values, before lifting to arbitrary programs and
    all their observation contexts. All adapter code is frozen under θ. -/
def AdapterComposition (Δ : Context) (a c : Typ) (c₁ c₂ c₃ : Expr) : Prop :=
  ∀ n, Context.Valid Δ → ∀ θ, Closing θ Δ → ∀ v V,
    ValRel n (a.subst θ) v V →
    ValRel n (c.subst θ)
      (adaptedValue (c₂.subst θ) (adaptedValue (c₁.subst θ) v))
      (adaptedValue (c₃.subst θ) V)

theorem AdapterComposition.lift (hcomp : AdapterComposition Δ a c c₁ c₂ c₃)
    (h₁ : Adapts Δ a b c₁) (h₂ : Adapts Δ b c c₂) (h₃ : Adapts Δ a c c₃)
    (hΔ : Context.Valid Δ) (hθ : Closing θ Δ)
    (he : ExprRel n (a.subst θ) (ν,e) (N,E)) (hν : Value ν) (hN : Value N) :
    ExprRel n (c.subst θ) (ν,.app (c₂.subst θ) (.app (c₁.subst θ) e))
      (N,.app (c₃.subst θ) E) := by
  rw [ExprRel] at he ⊢
  constructor
  · intro k hk w hw
    obtain ⟨mid,i,hi,hmid,hout⟩ := hw.app_input
    obtain ⟨v,j,hj,hv,hfirst⟩ := hmid.app_input
    obtain ⟨V,hV,hrel⟩ := he.1 j (by omega) v hv
    have hmidEq := h₁.result_eq hΔ hθ hrel.left hν hfirst
    subst mid
    have houtEq := h₂.result_eq hΔ hθ (h₁.adapted_typed hΔ hθ hrel.left) hν hout
    have hright := h₃.adapted_anywhere hΔ hθ hrel.right hN
    refine ⟨_,hV.app_argument hright,?_⟩
    rw [houtEq]
    exact (hcomp (n-j) hΔ θ hθ v V hrel).mono (by omega)
  · intro k hk W hW
    obtain ⟨V,i,hi,hV,hout⟩ := hW.app_input
    obtain ⟨v,hv,hrel⟩ := he.2 i (by omega) V hV
    have houtEq := h₃.result_eq hΔ hθ hrel.right hN hout
    have hfirst := h₁.adapted_anywhere hΔ hθ hrel.left hν
    have hmid := h₁.adapted_typed hΔ hθ hrel.left
    have hsecond := h₂.adapted_anywhere hΔ hθ hmid hν
    refine ⟨_,(hv.app_argument hfirst).app_argument hsecond,?_⟩
    rw [houtEq]
    exact (hcomp (n-i) hΔ θ hθ v V hrel).mono (by omega)

/-- The value theorem entails the paper's full contextual result for arbitrary
    expressions, rather than only agreement on a supplied value. -/
theorem adapter_coherence_of_values
    (h₁ : Adapts Δ a b c₁) (h₂ : Adapts Δ b c c₂) (h₃ : Adapts Δ a c c₃)
    (hcomp : AdapterComposition Δ a c c₁ c₂ c₃)
    (he : HasType Δ h e a) (hΔ : Context.Valid Δ) :
    ContextualEq Δ h c (.app c₂ (.app c₁ e)) (.app c₃ e) := by
  have hh := he.ambient_wf
  have hl : HasType Δ h (.app c₂ (.app c₁ e)) c :=
    .app (h₂.typing.2.2 h hh) (.app (h₁.typing.2.2 h hh) he)
  have hr : HasType Δ h (.app c₃ e) c := .app (h₃.typing.2.2 h hh) he
  apply OpenRel.contextual (he := hl) (hE := hr) (hΔ := hΔ)
  intro θ hθ n ν N hν
  exact hcomp.lift h₁ h₂ h₃ hΔ hθ (he.logical hΔ θ hθ n ν N hν) hν.left.1 hν.right.1

end LeanSce.Target

/-! ## Adapter Coherence Composition -/

section

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace LeanSce.Target
open LogicalRelation

/-- Canonical adapter paths agree at every logical index, including independent
    well-formed guard contexts closed by the same substitution. -/
theorem Adapts.composition_values
    (h₁ : Adapts Δ a b c₁) (h₂ : Adapts Γ b c c₂) (h₃ : Adapts Ξ a c c₃)
    (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ) (hΞ : Context.Valid Ξ)
    (hθ : Closing θ Δ) (hΘ : Closing θ Γ) (hϑ : Closing θ Ξ)
    (hv : ValRel n (a.subst θ) v V) :
    ValRel n (c.subst θ)
      (adaptedValue (c₂.subst θ) (adaptedValue (c₁.subst θ) v))
      (adaptedValue (c₃.subst θ) V) := by
  induction hsize : sizeOf a + sizeOf b + sizeOf c using Nat.strongRecOn
      generalizing Δ Γ Ξ a b c c₁ c₂ c₃ θ n v V with
  | ind m ih =>
    cases h₁ with
    | equal wa wb he =>
      exact adapter_composition_first_equal wa wb he h₂ h₃ hΔ hΓ hΞ hθ hΘ hϑ hv
    | arrow hn₁ d₁ u₁ =>
      cases h₂ with
      | equal wb wc he =>
        exact adapter_composition_second_equal (.arrow hn₁ d₁ u₁) wb wc he h₃ hΔ hΓ hΞ hθ hΘ hϑ hv
      | arrow hn₂ d₂ u₂ =>
        cases h₃ with
        | equal wa wc he => exact False.elim (hn₁ (Adapts.cycle (.arrow hn₁ d₁ u₁) (.arrow hn₂ d₂ u₂) he))
        | arrow hn₃ d₃ u₃ =>
          apply adapter_arrow_composition d₁ u₁ d₂ u₂ d₃ u₃ hn₁ hn₂ hn₃ hΔ hΓ hΞ hθ hΘ hϑ hv
          · intro j hj x X hx
            apply ih _ ?_ d₂ d₁ d₃ hΓ hΔ hΞ hΘ hθ hϑ hx rfl
            simp at hsize
            omega
          · intro j hj x X hx
            apply ih _ ?_ u₁ u₂ u₃ hΔ hΓ hΞ hθ hΘ hϑ hx rfl
            simp at hsize
            omega
    | sameTail wr ws hn hp hf =>
      rename_i r s fields
      obtain ⟨t,rfl⟩ := h₂.record_target
      apply adapter_record_composition (.sameTail wr ws hn hp hf) h₂ h₃ hΔ hΓ hΞ hθ hΘ hϑ hv
      intro l a b c f₁ f₂ f₃ ha hb hc hd₁ hd₂ hd₃ hv
      have hsa := Ty.knownField_size r (Ty.lookup_knownField r ha)
      have hsb := Ty.knownField_size s (Ty.lookup_knownField s hb)
      have hsc := Ty.knownField_size t (Ty.lookup_knownField t hc)
      apply ih _ ?_ hd₁ hd₂ hd₃ hΔ hΓ hΞ hθ hΘ hϑ hv rfl
      simp at hsize
      omega
    | closed wr ws hn hs hp hf =>
      rename_i r s fields
      obtain ⟨t,rfl⟩ := h₂.record_target
      apply adapter_record_composition (.closed wr ws hn hs hp hf) h₂ h₃ hΔ hΓ hΞ hθ hΘ hϑ hv
      intro l a b c f₁ f₂ f₃ ha hb hc hd₁ hd₂ hd₃ hv
      have hsa := Ty.knownField_size r (Ty.lookup_knownField r ha)
      have hsb := Ty.knownField_size s (Ty.lookup_knownField s hb)
      have hsc := Ty.knownField_size t (Ty.lookup_knownField t hc)
      apply ih _ ?_ hd₁ hd₂ hd₃ hΔ hΓ hΞ hθ hΘ hϑ hv rfl
      simp at hsize
      omega
    | all wa₁ wb₁ hn₁ hg₁ d₁ =>
      cases h₂ with
      | equal wb wc he =>
        exact adapter_composition_second_equal (.all wa₁ wb₁ hn₁ hg₁ d₁) wb wc he h₃ hΔ hΓ hΞ hθ hΘ hϑ hv
      | all wa₂ wb₂ hn₂ hg₂ d₂ =>
        cases h₃ with
        | equal wa wc he => exact False.elim (hn₁ (Adapts.cycle (.all wa₁ wb₁ hn₁ hg₁ d₁) (.all wa₂ wb₂ hn₂ hg₂ d₂) he))
        | all wa₃ wb₃ hn₃ hg₃ d₃ =>
          apply universal_composition wa₁ wb₁ hn₁ hg₁ d₁ wa₂ wb₂ hn₂ hg₂ d₂ wa₃ wb₃ hn₃ hg₃ d₃ hΔ hΓ hΞ hθ hΘ hϑ hv
          intro j hj u hk hu hgu r R hr
          obtain ⟨valid₁,valid₂,valid₃,close₁,close₂,close₃⟩ :=
            universal_composition_binders wa₁ wa₂ wa₃ hg₁ hΔ hΓ hΞ hθ hΘ hϑ hk hu hgu
          apply ih _ ?_ d₁ d₂ d₃ valid₁ valid₂ valid₃ close₁ close₂ close₃ hr rfl
          simp at hsize
          omega

/-- The common-context specialization used by contextual path coherence. -/
theorem Adapts.composition
    (h₁ : Adapts Δ a b c₁) (h₂ : Adapts Δ b c c₂) (h₃ : Adapts Δ a c c₃) :
    AdapterComposition Δ a c c₁ c₂ c₃ := by
  intro n hΔ θ hθ v V hv
  exact h₁.composition_values h₂ h₃ hΔ hΔ hΔ hθ hθ hθ hv

end LeanSce.Target

end

/-! ## Adapter Coherence -/

namespace LeanSce.Target

/-- Canonical composed and direct adapters agree in every typed ground
    observation context, for arbitrary input expressions and closing instances. -/
theorem adapter_coherence : Goals.AdapterCoherence := by
  intro Δ a b c h e c₁ c₂ c₃ hΔ h₁ h₂ h₃ he
  exact adapter_coherence_of_values h₁ h₂ h₃ (h₁.composition h₂ h₃) he hΔ

end LeanSce.Target

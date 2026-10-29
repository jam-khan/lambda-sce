import LeanSce.Source.Abstraction.Contexts
import LeanSce.Source.Definitions.Contexts
import LeanSce.Source.Definitions.Elaboration
import LeanSce.Source.Elaboration.Contexts
import LeanSce.Source.Elaboration.Correctness
import LeanSce.Source.Elaboration.Representations
import LeanSce.Source.Metatheory.Basic
import LeanSce.Target.Abstraction.Infrastructure
import LeanSce.Target.Abstraction.RepresentationIndependence

/-!
# Source / Abstraction / Replacement

Proofs and supporting constructions for replacement.
-/

/-! ## Abstract Module Replacement Statement -/

namespace LeanSce.Source.Goals

/-- S5 exactly: the runtime representatives are chosen by the complete Related
    relation before quantifying over observation indices. The representation
    candidate is an arbitrary downward-closed typed target value relation. -/
def AbstractModuleReplacement : Prop :=
  ∀ (body A₁ A₂ : Typ) (v₁ v₂ : Expr) (V₁ V₂ : Target.Expr)
    (R : Target.Heterogeneous.IndexedRelation),
    HasType .empty .unit (.pack (.type A₁) (.ex .type .gnil body) v₁) (.ex .type .gnil body) →
    HasType .empty .unit (.pack (.type A₂) (.ex .type .gnil body) v₂) (.ex .type .gnil body) →
    Related v₁ V₁ → Related v₂ V₂ →
    Target.Heterogeneous.TypedRelation R A₁.erase A₂.erase →
    (∀ n, Target.Heterogeneous.ValRel n body.erase
      (Target.Heterogeneous.Valuation.empty.extend
        (Target.Heterogeneous.Candidate.type A₁.erase A₂.erase R)) V₁ V₂) →
    ContextualEq .empty .unit (.ex .type .gnil body)
      (.pack (.type A₁) (.ex .type .gnil body) v₁)
      (.pack (.type A₂) (.ex .type .gnil body) v₂)

end LeanSce.Source.Goals

/-! ## Representation Observation -/

namespace LeanSce.Source

private theorem erased_identity : Subst.erase Subst.id = Target.Subst.id := by
  funext k i
  cases k <;> rfl

/-- Ground observations are reflected for the actual chosen artifacts, including
    arbitrary permitted runtime representations and stored-code elaborations. -/
theorem observation_reflection_elaborates_of_correspondence
    (hterm : Goals.TerminationCorrespondence) (hdiv : Goals.DivergenceCorrespondence)
    (hg : GroundType g) (hν : ValueType .empty ν h)
    (he : HasType .empty h e g) (hE : HasType .empty h E g)
    (hF : Elaborates e F) (hG : Elaborates E G)
    (hr : Target.ObservationEq ν.erase F G) : ObservationEq ν e E := by
  have hl := hterm .empty h g e ν F ν.erase Subst.id .empty he hF
    (Closing.empty Subst.id) (by simpa only [Ty.subst_id] using hν) (Related.erase ν hν.1)
  have hright := hterm .empty h g E ν G ν.erase Subst.id .empty hE hG
    (Closing.empty Subst.id) (by simpa only [Ty.subst_id] using hν) (Related.erase ν hν.1)
  simp only [Term.subst_id,erased_identity,Target.Term.subst_id] at hl hright
  refine ⟨?_,?_⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨V,hV,hrel⟩ := hl.1 v hv
      obtain ⟨w,hw,hwrel⟩ := hright.2 V ((hr.1 V).mp hV)
      have hvtyped := hv.1.preservation hν he .empty
      have hwtyped := hw.1.preservation hν hE .empty
      have heq := hrel.ground_unique hwrel hvtyped hwtyped hg
      simpa only [heq] using hw
    · intro hv
      obtain ⟨V,hV,hrel⟩ := hright.1 v hv
      obtain ⟨w,hw,hwrel⟩ := hl.2 V ((hr.1 V).mpr hV)
      have hvtyped := hv.1.preservation hν hE .empty
      have hwtyped := hw.1.preservation hν he .empty
      have heq := hrel.ground_unique hwrel hvtyped hwtyped hg
      simpa only [heq] using hw
  · have dl := hdiv .empty h g e ν F ν.erase Subst.id .empty he hF
      (Closing.empty Subst.id) (by simpa only [Ty.subst_id] using hν) (Related.erase ν hν.1)
    have dr := hdiv .empty h g E ν G ν.erase Subst.id .empty hE hG
      (Closing.empty Subst.id) (by simpa only [Ty.subst_id] using hν) (Related.erase ν hν.1)
    simp only [Term.subst_id,erased_identity,Target.Term.subst_id] at dl dr
    exact dl.trans (hr.2.trans dr.symm)

theorem observation_reflection_elaborates
    (hg : GroundType g) (hν : ValueType .empty ν h)
    (he : HasType .empty h e g) (hE : HasType .empty h E g)
    (hF : Elaborates e F) (hG : Elaborates E G)
    (hr : Target.ObservationEq ν.erase F G) : ObservationEq ν e E :=
  observation_reflection_elaborates_of_correspondence termination_correspondence
    divergence_correspondence hg hν he hE hF hG hr

end LeanSce.Source

/-! ## Representation Reflection -/

namespace LeanSce.Source

/-- The fixed pair of representatives may occur at any native ambient. Value
    compatibility later factors each occurrence through the unit-ambient hole. -/
def RepresentationHole (a : Target.Typ) (F G : Target.Expr) : TargetRelation :=
  fun _ _ x X b => b = a ∧ x = F ∧ X = G

/-- Actual runtime artifacts, rather than just canonical erasures, reflect
    contextual equivalence back through every typed source observation context. -/
theorem chosen_representatives_contextual_of_correspondence
    (hterm : Goals.TerminationCorrespondence) (hdiv : Goals.DivergenceCorrespondence)
    (_he : HasType Δ .unit e a) (_hE : HasType Δ .unit E a) (_hΔ : Context.Valid Δ)
    (hv : Value e) (hV : Value E) (hF : Elaborates e F) (hG : Elaborates E G)
    (hctx : Target.ContextualEq Δ.erase .unit a.erase F G) : ContextualEq Δ .unit a e E := by
  intro θ hθ H g ν c C hg hν hc
  let A := (a.subst θ).erase
  let P := F.subst (Subst.erase θ)
  let Q := G.subst (Subst.erase θ)
  have hP : Target.Value P := by simpa [P,Target.Value] using hF.value_preservation hv
  have hQ : Target.Value Q := by simpa [Q,Target.Value] using hG.value_preservation hV
  have hholes : ∀ Γ H x X b, Context.Valid Γ → HasType Γ H x b → HasType Γ H X b →
      HoleAt (Ty.unit.subst θ) (a.subst θ) (e.subst θ) (E.subst θ) Γ H x X b →
      ContextArtifacts (RepresentationHole A P Q) Γ H x X b := by
    intro Γ H x X b hΓ hx hX hh
    obtain ⟨rfl,rfl,rfl,rfl⟩ := hh
    exact ⟨P,Q,hF.subst θ,hG.subst θ,.hole
      (hx.elaborates hΓ (hF.subst θ)) (hX.elaborates hΓ (hG.subst θ)) ⟨rfl,rfl,rfl⟩⟩
  have hvalues : ∀ Γ H x X b,
      HoleAt (Ty.unit.subst θ) (a.subst θ) (e.subst θ) (E.subst θ) Γ H x X b →
      x.isValue = X.isValue := by
    intro Γ H x X b hh
    obtain ⟨rfl,rfl,rfl,rfl⟩ := hh
    simpa only [Term.isValue_subst] using hv.trans hV.symm
  have hstable : ∀ Γ H x X b, RepresentationHole A P Q Γ H x X b →
      ∀ K, Target.WellFormed Γ K → RepresentationHole A P Q Γ K x X b := by
    intros Γ H x X b hh K hK; exact hh
  obtain ⟨cT,CT,hcT,hCT,hcomp⟩ := hc.representation_context hholes hvalues hstable .empty
  have hfixed : Target.Compatible (Target.HoleAt .unit A P Q) .empty H.erase cT CT g.erase := by
    apply hcomp.bind
    intro Γ K x X b hx hX hh
    obtain ⟨rfl,rfl,rfl⟩ := hh
    exact .value hP hQ (.hole (hx.value_reambient hP .unit .unit)
      (hX.value_reambient hQ .unit .unit) ⟨rfl,rfl,rfl,rfl⟩) hx.ambient_wf
  have hνT : Target.ValueType .empty ν.erase H.erase :=
    ⟨Term.erase_value ν hν.1,hν.2.erase .empty⟩
  have hob : Target.ObservationEq ν.erase cT CT := by
    apply hctx (Subst.erase θ) hθ.erase H.erase g.erase ν.erase cT CT hg.erase hνT
    simpa only [A,P,Q,← Ty.erase_subst,Ty.erase,Target.Ty.subst] using hfixed
  exact observation_reflection_elaborates_of_correspondence hterm hdiv hg hν
    hc.left_typed hc.right_typed hcT hCT hob

theorem chosen_representatives_contextual
    (he : HasType Δ .unit e a) (hE : HasType Δ .unit E a) (hΔ : Context.Valid Δ)
    (hv : Value e) (hV : Value E) (hF : Elaborates e F) (hG : Elaborates E G)
    (hctx : Target.ContextualEq Δ.erase .unit a.erase F G) : ContextualEq Δ .unit a e E :=
  chosen_representatives_contextual_of_correspondence termination_correspondence divergence_correspondence
    he hE hΔ hv hV hF hG hctx

end LeanSce.Source

/-! ## Abstract Module Replacement -/

namespace LeanSce.Source

private theorem package_witness_wf
    (ht : HasType Δ h (.pack (.type A) (.ex .type .gnil body) v) (.ex .type .gnil body))
    (hv : Value v) : WellFormed Δ A := by
  cases ht.value_origin (show Value (.pack (.type A) (.ex .type .gnil body) v) from hv) with
  | pack _ _ hu _ _ _ => exact hu

/-- S5: arbitrary corresponding target representations may implement the two
    existential packages. No canonical-erasure restriction is imposed. -/
theorem abstract_module_replacement : Goals.AbstractModuleReplacement := by
  intro body A₁ A₂ v₁ v₂ V₁ V₂ R hp₁ hp₂ hrel₁ hrel₂ hR hrep
  have vp₁ : Value (.pack (.type A₁) (.ex .type .gnil body) v₁) := hrel₁.values.1
  have vp₂ : Value (.pack (.type A₂) (.ex .type .gnil body) v₂) := hrel₂.values.1
  have wA₁ := package_witness_wf hp₁ hrel₁.values.1
  have wA₂ := package_witness_wf hp₂ hrel₂.values.1
  have wpublic := hp₁.result_wf .empty
  have e₁ : Elaborates (.pack (.type A₁) (.ex .type .gnil body) v₁)
      (.pack (.type A₁.erase) (.ex .type .gnil body.erase) V₁) := .value (.pack hrel₁)
  have e₂ : Elaborates (.pack (.type A₂) (.ex .type .gnil body) v₂)
      (.pack (.type A₂.erase) (.ex .type .gnil body.erase) V₂) := .value (.pack hrel₂)
  have t₁ : Target.ValueType .empty
      (.pack (.type A₁.erase) (.ex .type .gnil body.erase) V₁) (.ex .type .gnil body.erase) :=
    ⟨e₁.value_preservation vp₁,hp₁.elaborates .empty e₁⟩
  have t₂ : Target.ValueType .empty
      (.pack (.type A₂.erase) (.ex .type .gnil body.erase) V₂) (.ex .type .gnil body.erase) :=
    ⟨e₂.value_preservation vp₂,hp₂.elaborates .empty e₂⟩
  have htarget := Target.representation_independence body.erase A₁.erase A₂.erase V₁ V₂ R
    wA₁.erase wA₂.erase wpublic.erase hR t₁ t₂ hrep
  exact chosen_representatives_contextual hp₁ hp₂ .empty vp₁ vp₂ e₁ e₂ htarget

end LeanSce.Source

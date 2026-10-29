import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.CanonicalForms
import LeanSce.Source.Metatheory.Records
import LeanSce.Source.Metatheory.Safety
import LeanSce.Target.LogicalRelation.Data
import LeanSce.Target.Semantics.Templates

/-!
# Source / Metatheory / Evaluation

Proofs and supporting constructions for evaluation.
-/

/-! ## Evaluation Properties -/

namespace LeanSce.Source

theorem Steps.single (hs : Step ν e e') : Steps ν e e' := .next hs .refl

theorem Steps.trans (h₁ : Steps ν e f) (h₂ : Steps ν f g) : Steps ν e g := by
  induction h₁ with
  | refl => exact h₂
  | next hs _ ih => exact .next hs (ih h₂)

theorem Steps.lift (hs : Steps ν e e') (C : Expr → Expr)
    (hc : ∀ {x y}, Step ν x y → Step μ (C x) (C y)) : Steps μ (C e) (C e') := by
  induction hs with
  | refl => exact .refl
  | next hs _ ih => exact .next (hc hs) ih

theorem Steps.app_left (hs : Steps ν e e') : Steps ν (.app e x) (.app e' x) := by
  apply hs.lift (fun e => .app e x)
  intro a b hab
  exact ⟨hab.1, by simp [step_app_eq, step_isValue_false hab.2, hab.2]⟩

theorem Steps.app_right (hs : Steps ν e e') (hf : Value f) :
    Steps ν (.app f e) (.app f e') := by
  apply hs.lift (.app f)
  intro a b hab
  exact ⟨hab.1, by simp [step_app_eq, (show f.isValue = true from hf),
    step_isValue_false hab.2, hab.2]⟩

theorem Steps.box_left (hs : Steps ν e e') : Steps ν (.box e body) (.box e' body) := by
  apply hs.lift (fun e => .box e body)
  intro a b hab
  exact ⟨hab.1, by simp [step_box_eq, step_isValue_false hab.2, hab.2]⟩

theorem Steps.box_body (hs : Steps env e e') (hν : Value ν) (he : Value env) :
    Steps ν (.box env e) (.box env e') := by
  apply hs.lift (.box env)
  intro a b hab
  exact ⟨hν, by simp [step_box_eq, (show env.isValue = true from he),
    step_isValue_false hab.2, hab.2]⟩

theorem Terminates.box (hs : Terminates env e v) (hν : Value ν) (he : Value env) :
    Terminates ν (.box env e) v :=
  ⟨(hs.1.box_body hν he).trans (.single (box_value hν he hs.2)), hs.2⟩

theorem Steps.preservation (hs : Steps ν e e') (hν : ValueType Δ ν h)
    (ht : HasType Δ h e a) (hΔ : Context.Valid Δ) : HasType Δ h e' a := by
  induction hs with
  | refl => exact ht
  | next hs _ ih => exact ih (ht.preservation hΔ ν hν _ hs.2)

/-- A strict frame evaluates its hole before any final result is returned. -/
structure StrictFrame (ν : Expr) (C : Expr → Expr) : Prop where
  value : ∀ e, Value (C e) → Value e
  step : ∀ e, ¬ Value e → step ν (C e) = (step ν e).map C

theorem StrictFrame.decompose_steps (hc : StrictFrame ν C) (hs : Steps ν start w) :
    Value w → ∀ e, start = C e →
      ∃ v, Terminates ν e v ∧ Terminates ν (C v) w := by
  induction hs with
  | refl =>
    intro hw e heq
    cases heq
    exact ⟨e, ⟨.refl, hc.value e hw⟩, .refl, hw⟩
  | @next start next finish hstep htail ih =>
    intro hw e heq
    subst start
    by_cases hv : Value e
    · exact ⟨e, ⟨.refl, hv⟩, .next hstep htail, hw⟩
    · have hh := hstep.2
      rw [hc.step e hv] at hh
      obtain ⟨e',he',heq⟩ := Option.map_eq_some_iff.mp hh
      obtain ⟨v,hv₁,hv₂⟩ := ih hw e' heq.symm
      exact ⟨v, ⟨.next ⟨hstep.1,he'⟩ hv₁.1, hv₁.2⟩, hv₂⟩

theorem StrictFrame.decompose (hc : StrictFrame ν C) (he : Terminates ν (C e) w) :
    ∃ v, Terminates ν e v ∧ Terminates ν (C v) w :=
  hc.decompose_steps he.1 he.2 e rfl

theorem strict_app_left : StrictFrame ν (fun f => .app f x) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have hf : e.isValue = false := by cases he : e.isValue <;> first | rfl | exact False.elim (hn he)
    simp [step_app_eq, hf]

theorem strict_app_right (hf : Value f) : StrictFrame ν (.app f) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases he : e.isValue <;> first | rfl | exact False.elim (hn he)
    simp [step_app_eq, (show f.isValue = true from hf), he]

theorem Terminates.app_decompose (he : Terminates ν (.app f x) w) :
    ∃ F X, Terminates ν f F ∧ Terminates ν x X ∧ Terminates ν (.app F X) w := by
  obtain ⟨F,hF,hrest⟩ := strict_app_left.decompose he
  obtain ⟨X,hX,hrest⟩ := (strict_app_right hF.2).decompose hrest
  exact ⟨F,X,hF,hX,hrest⟩

end LeanSce.Source

/-! ## Behaviour -/

namespace LeanSce.Source

theorem Steps.value_result (hs : Steps ν v w) (hv : Value v) : w = v := by
  cases hs with
  | refl => rfl
  | next hs _ => exact False.elim (value_irreducible hv hs)

theorem Diverges.next (hd : Diverges ν e) (hs : Step ν e e') : Diverges ν e' := by
  obtain ⟨trace,hzero,htrace⟩ := hd
  refine ⟨fun n => trace (n+1), ?_, fun n => htrace (n+1)⟩
  exact step_deterministic (by simpa only [hzero] using htrace 0) hs

theorem Diverges.after_steps (hd : Diverges ν e) (hs : Steps ν e e') : Diverges ν e' := by
  induction hs with
  | refl => exact hd
  | next hs _ ih => exact ih (hd.next hs)

theorem Diverges.not_value (hd : Diverges ν e) : ¬ Value e := by
  obtain ⟨trace,hzero,htrace⟩ := hd
  intro hv
  exact value_irreducible hv (by simpa only [hzero] using htrace 0)

theorem Diverges.not_terminates (hd : Diverges ν e) : ¬ ∃ v, Terminates ν e v := by
  rintro ⟨v,hv⟩
  exact (hd.after_steps hv.1).not_value hv.2

/-- Safety supplies an actual infinite trace whenever a typed execution has no
    finite result. This is not a definition of divergence as nontermination. -/
theorem diverges_of_not_terminates (ht : HasType Δ h e a) (hΔ : Context.Valid Δ)
    (hν : ValueType Δ ν h) (hn : ¬ ∃ v, Terminates ν e v) : Diverges ν e := by
  let trace : Nat → Expr := fun n => Nat.rec e (fun _ x => (step ν x).getD x) n
  have hsteps : ∀ n, Steps ν e (trace n) := by
    intro n
    induction n with
    | zero => exact .refl
    | succ n ih =>
      have ht' := ih.preservation hν ht hΔ
      rcases ht'.canStep hΔ ν hν with hv | ⟨v,hs⟩
      · exact False.elim (hn ⟨trace n, ih, hv⟩)
      · have he : trace (n+1) = v := by simp only [trace, hs, Option.getD_some]
        rw [he]
        exact ih.trans (.single ⟨hν.1,hs⟩)
  refine ⟨trace, rfl, ?_⟩
  intro n
  have ht' := (hsteps n).preservation hν ht hΔ
  rcases ht'.canStep hΔ ν hν with hv | ⟨v,hs⟩
  · exact False.elim (hn ⟨trace n, hsteps n, hv⟩)
  · have he : trace (n+1) = v := by simp only [trace, hs, Option.getD_some]
    rw [he]
    exact ⟨hν.1,hs⟩

theorem diverges_iff_not_terminates (ht : HasType Δ h e a) (hΔ : Context.Valid Δ)
    (hν : ValueType Δ ν h) : Diverges ν e ↔ ¬ ∃ v, Terminates ν e v :=
  ⟨Diverges.not_terminates, diverges_of_not_terminates ht hΔ hν⟩

/-- Replacing a terminating argument by its result preserves application
    termination; the function is still evaluated in its original position. -/
theorem Terminates.app_argument (hx : Terminates ν x v)
    (hcv : Terminates ν (.app c v) w) : Terminates ν (.app c x) w := by
  obtain ⟨C,V,hC,hV,hrest⟩ := hcv.app_decompose
  have hv : V = v := hV.1.value_result hx.2
  subst V
  exact ⟨hC.1.app_left.trans ((hx.1.app_right hC.2).trans hrest.1), hrest.2⟩

/-- Every strict application of a total value adapter terminates exactly when
    its argument terminates. The adapter itself is evaluated before the input. -/
theorem total_application_terminates_iff (he : HasType Δ h e a)
    (hΔ : Context.Valid Δ) (hν : ValueType Δ ν h)
    (htotal : ∀ v, ValueType Δ v a → ∃ w, Terminates ν (.app c v) w) :
    (∃ w, Terminates ν (.app c e) w) ↔ ∃ v, Terminates ν e v := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨_,v,_,hv,_⟩ := hw.app_decompose
    exact ⟨v,hv⟩
  · rintro ⟨v,hv⟩
    have hvt := valueType_of_typed_value (hv.1.preservation hν he hΔ) hv.2
    obtain ⟨w,hw⟩ := htotal v hvt
    exact ⟨w,hv.app_argument hw⟩

theorem total_application_diverges_iff (he : HasType Δ h e a)
    (hc : HasType Δ h c (.arr a b)) (hΔ : Context.Valid Δ) (hν : ValueType Δ ν h)
    (htotal : ∀ v, ValueType Δ v a → ∃ w, Terminates ν (.app c v) w) :
    Diverges ν (.app c e) ↔ Diverges ν e := by
  rw [diverges_iff_not_terminates (.app hc he) hΔ hν,
    diverges_iff_not_terminates he hΔ hν,
    total_application_terminates_iff he hΔ hν htotal]

theorem Diverges.before_step (hs : Step ν e e') (hd : Diverges ν e') : Diverges ν e := by
  obtain ⟨trace,hzero,htrace⟩ := hd
  refine ⟨fun n => match n with | 0 => e | n+1 => trace n,rfl,?_⟩
  intro n
  cases n with
  | zero => simpa only [hzero] using hs
  | succ n => exact htrace n

theorem Diverges.before_steps (hs : Steps ν e e') (hd : Diverges ν e') : Diverges ν e := by
  induction hs with
  | refl => exact hd
  | next hs _ ih => exact Diverges.before_step hs (ih hd)

theorem Steps.diverges_iff (hs : Steps ν e e') : Diverges ν e ↔ Diverges ν e' :=
  ⟨fun hd => hd.after_steps hs,fun hd => hd.before_steps hs⟩

end LeanSce.Source

/-! ## Counted Evaluation -/

namespace LeanSce.Source

abbrev Configuration := Expr × Expr

/-- Exactly n reductions in one native ambient. -/
inductive StepsN (ν : Expr) : Nat → Expr → Expr → Prop where
  | refl : StepsN ν 0 e e
  | next : Step ν e e' → StepsN ν n e' v → StepsN ν (n+1) e v

def TerminatesIn (ν e : Expr) (n : Nat) (v : Expr) : Prop :=
  StepsN ν n e v ∧ Value v

theorem StepsN.toSteps (hs : StepsN ν n e v) : Steps ν e v := by
  induction hs with
  | refl => exact .refl
  | next hs _ ih => exact .next hs ih

theorem Steps.counted (hs : Steps ν e v) : ∃ n, StepsN ν n e v := by
  induction hs with
  | refl => exact ⟨0,.refl⟩
  | next hs _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,.next hs hn⟩

theorem TerminatesIn.toTerminates (hs : TerminatesIn ν e n v) : Terminates ν e v :=
  ⟨hs.1.toSteps,hs.2⟩

theorem Terminates.counted (hs : Terminates ν e v) : ∃ n, TerminatesIn ν e n v := by
  obtain ⟨n,hn⟩ := hs.1.counted
  exact ⟨n,hn,hs.2⟩

theorem StepsN.trans (h₁ : StepsN ν n e f) (h₂ : StepsN ν m f g) :
    StepsN ν (n+m) e g := by
  induction h₁ with
  | refl => simpa only [Nat.zero_add] using h₂
  | @next x y n z hs _ ih =>
    simpa only [Nat.add_right_comm n 1 m] using StepsN.next hs (ih h₂)

theorem StepsN.value_inv (hs : StepsN ν n v w) (hv : Value v) : n = 0 ∧ w = v := by
  cases hs with
  | refl => exact ⟨rfl,rfl⟩
  | next hs _ => exact False.elim (value_irreducible hv hs)

theorem StepsN.lift (hs : StepsN ν n e e') (C : Expr → Expr)
    (hc : ∀ {x y}, Step ν x y → Step μ (C x) (C y)) : StepsN μ n (C e) (C e') := by
  induction hs with
  | refl => exact .refl
  | next hs _ ih => exact .next (hc hs) ih

theorem StepsN.app_left (hs : StepsN ν n e e') : StepsN ν n (.app e x) (.app e' x) := by
  apply hs.lift (fun e => .app e x)
  intro a b hab
  exact ⟨hab.1, by simp [step_app_eq, step_isValue_false hab.2, hab.2]⟩

theorem StepsN.app_right (hs : StepsN ν n e e') (hf : Value f) :
    StepsN ν n (.app f e) (.app f e') := by
  apply hs.lift (.app f)
  intro a b hab
  exact ⟨hab.1, by simp [step_app_eq, (show f.isValue = true from hf),
    step_isValue_false hab.2, hab.2]⟩

theorem StepsN.box_body (hs : StepsN env n e e') (hν : Value ν) (he : Value env) :
    StepsN ν n (.box env e) (.box env e') := by
  apply hs.lift (.box env)
  intro a b hab
  exact ⟨hν, by simp [step_box_eq, (show env.isValue = true from he),
    step_isValue_false hab.2, hab.2]⟩

theorem TerminatesIn.box (hs : TerminatesIn env e n v) (hν : Value ν) (he : Value env) :
    TerminatesIn ν (.box env e) (n+1) v :=
  ⟨hs.1.box_body hν he |>.trans (.next (box_value hν he hs.2) .refl),hs.2⟩

/-- Counted strict-frame decomposition accounts for every administrative step. -/
theorem StrictFrame.decompose_counted_steps (hc : StrictFrame ν C)
    (hs : StepsN ν n start w) : Value w → ∀ e, start = C e →
    ∃ v i j, n = i+j ∧ TerminatesIn ν e i v ∧ TerminatesIn ν (C v) j w := by
  induction hs with
  | refl =>
    intro hw e heq
    cases heq
    exact ⟨e,0,0,rfl,⟨.refl,hc.value e hw⟩,.refl,hw⟩
  | @next start next n finish hstep htail ih =>
    intro hw e heq
    subst start
    by_cases hv : Value e
    · exact ⟨e,0,n+1,by omega,⟨.refl,hv⟩,.next hstep htail,hw⟩
    · have hh := hstep.2
      rw [hc.step e hv] at hh
      obtain ⟨e',he',heq⟩ := Option.map_eq_some_iff.mp hh
      obtain ⟨v,i,j,hn,hv₁,hv₂⟩ := ih hw e' heq.symm
      exact ⟨v,i+1,j,by omega,⟨.next ⟨hstep.1,he'⟩ hv₁.1,hv₁.2⟩,hv₂⟩

theorem StrictFrame.decompose_counted (hc : StrictFrame ν C)
    (he : TerminatesIn ν (C e) n w) :
    ∃ v i j, n = i+j ∧ TerminatesIn ν e i v ∧ TerminatesIn ν (C v) j w :=
  hc.decompose_counted_steps he.1 he.2 e rfl

end LeanSce.Source

/-! ## Evaluation Inversion -/

namespace LeanSce.Source

theorem Terminates.unique (h₁ : Terminates ν e v) (h₂ : Terminates ν e w) : v = w := by
  obtain ⟨hs,hv⟩ := h₁
  induction hs generalizing w with
  | refl => exact (h₂.1.value_result hv).symm
  | next hs htail ih =>
    cases h₂.1 with
    | refl => exact False.elim (value_irreducible h₂.2 hs)
    | next hs' htail' =>
      have he := step_deterministic hs hs'
      cases he
      exact ih ⟨htail',h₂.2⟩ hv

theorem Terminates.after_step (ht : Terminates ν e w) (hs : Step ν e e') :
    Terminates ν e' w := by
  cases ht.1 with
  | refl => exact False.elim (value_irreducible ht.2 hs)
  | next hfirst htail =>
    have he := step_deterministic hs hfirst
    cases he
    exact ⟨htail,ht.2⟩

theorem Terminates.after_steps (ht : Terminates ν e w) (hs : Steps ν e e') :
    Terminates ν e' w := by
  induction hs with
  | refl => exact ht
  | next hs _ ih => exact ih (ht.after_step hs)

theorem Terminates.prepend (ht : Terminates ν e' w) (hs : Steps ν e e') :
    Terminates ν e w := ⟨hs.trans ht.1,ht.2⟩

private theorem box_inverse_steps (hs : StepsN ν k start w) :
    ∀ env body, start = .box env body → Value env → Value w →
      ∃ j, k = j+1 ∧ TerminatesIn env body j w := by
  induction hs with
  | refl =>
    intro env body he henv hw
    rw [he] at hw
    simp [Value,Term.isValue] at hw
  | @next start next k finish hs htail ih =>
    intro env body he henv hw
    subst start
    have hstep := hs.2
    rw [step_box_eq] at hstep
    simp only [(show env.isValue = true from henv),Bool.not_true,Bool.false_eq_true,↓reduceIte] at hstep
    cases hb : body.isValue with
    | true =>
      simp only [hb,↓reduceIte,Option.some.injEq] at hstep
      subst next
      obtain ⟨rfl,rfl⟩ := htail.value_inv hb
      exact ⟨0,rfl,.refl,hb⟩
    | false =>
      simp only [hb,Bool.false_eq_true,↓reduceIte] at hstep
      obtain ⟨body',hbody,heq⟩ := Option.map_eq_some_iff.mp hstep
      obtain ⟨j,hj,ht⟩ := ih env body' heq.symm henv hw
      exact ⟨j+1,by omega,.next ⟨henv,hbody⟩ ht.1,ht.2⟩

/-- A box contributes exactly its final removal step to a terminating body run. -/
theorem TerminatesIn.box_inv (_hν : Value ν) (henv : Value env)
    (hs : TerminatesIn ν (.box env body) k w) :
    ∃ j, k = j+1 ∧ TerminatesIn env body j w :=
  box_inverse_steps hs.1 env body rfl henv hs.2

theorem TerminatesIn.after_step (ht : TerminatesIn ν e k w) (hs : Step ν e e') :
    ∃ j, k = j+1 ∧ TerminatesIn ν e' j w := by
  cases ht.1 with
  | refl => exact False.elim (value_irreducible ht.2 hs)
  | next hfirst htail =>
    have he := step_deterministic hs hfirst
    cases he
    exact ⟨_,rfl,htail,ht.2⟩

theorem Terminates.box_inv (henv : Value env) (hs : Terminates ν (.box env body) w) :
    Terminates env body w := by
  obtain ⟨n,hn⟩ := hs.counted
  obtain ⟨_,_,ht⟩ := hn.box_inv (by
    cases hs.1 with
    | refl => cases hs.2
    | next hs _ => exact hs.1) henv
  exact ht.toTerminates

private theorem nonvalue_false (hn : ¬ Value e) : e.isValue = false := by
  cases h : e.isValue with
  | false => rfl
  | true => exact False.elim (hn h)

theorem strict_merge_left : StrictFrame ν (fun e => .merge e f) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_merge_eq,nonvalue_false hn]

theorem strict_merge_right (hv : Value f) : StrictFrame ν (.merge f) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_merge_eq,nonvalue_false hn, (show f.isValue = true from hv)]

theorem strict_box_left : StrictFrame ν (fun e => .box e body) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_box_eq,nonvalue_false hn]

theorem strict_link_provider : StrictFrame ν (fun e => .link p i o cd e m) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_link_eq,nonvalue_false hn]

theorem strict_link_module (hv : Value provider) : StrictFrame ν (.link p i o cd provider) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_link_eq,nonvalue_false hn, (show provider.isValue = true from hv)]

theorem strict_run_module : StrictFrame ν (fun e => .run p i o cd e provider) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_run_eq,nonvalue_false hn]

theorem strict_run_provider (hv : Value m) : StrictFrame ν (.run p i o cd m) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_run_eq,nonvalue_false hn, (show m.isValue = true from hv)]

theorem strict_provide_provider : StrictFrame ν (fun e => .provide p j k o cd e m) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_provide_eq,nonvalue_false hn]

theorem strict_provide_module (hv : Value provider) : StrictFrame ν (.provide p j k o cd provider) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_provide_eq,nonvalue_false hn, (show provider.isValue = true from hv)]

theorem strict_invoke_module : StrictFrame ν (fun e => .invoke i o e imports) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_invoke_eq,nonvalue_false hn]

theorem strict_invoke_imports (hv : Value m) : StrictFrame ν (.invoke i o m) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_invoke_eq,nonvalue_false hn, (show m.isValue = true from hv)]

theorem strict_view : StrictFrame ν (.view a b cd) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_view_eq,nonvalue_false hn]

theorem strict_resid_saved (hv : Value m) : StrictFrame ν (fun e => .resid m e j k o) := by
  constructor
  · intro _ hw
    simp only [Value,Term.isValue,Bool.and_eq_true] at hw
    exact hw.2
  · intro e hn
    simp [step_resid_eq, (show m.isValue = true from hv)]

theorem strict_capture : StrictFrame ν (fun e => .capture c i o e body) := by
  constructor
  · intro _ hw; cases hw
  · intro e hn
    simp [step_capture_eq,nonvalue_false hn]

theorem StrictFrame.lift_steps (hc : StrictFrame ν C) (hs : Steps ν e e') :
    Steps ν (C e) (C e') := by
  apply hs.lift C
  intro x y hxy
  refine ⟨hxy.1,?_⟩
  rw [hc.step x (fun hv => value_irreducible hv hxy),hxy.2]
  rfl

theorem StrictFrame.terminates (hc : StrictFrame ν C) (he : Terminates ν e v)
    (hrest : Terminates ν (C v) w) : Terminates ν (C e) w :=
  hrest.prepend (hc.lift_steps he.1)

theorem StrictFrame.lift_counted (hc : StrictFrame ν C) (hs : StepsN ν n e e') :
    StepsN ν n (C e) (C e') := by
  apply hs.lift C
  intro x y hxy
  refine ⟨hxy.1,?_⟩
  rw [hc.step x (fun hv => value_irreducible hv hxy),hxy.2]
  rfl

theorem TerminatesIn.after_prefix (ht : TerminatesIn ν e k w) (hs : StepsN ν p e base) :
    ∃ i, k = p+i ∧ TerminatesIn ν base i w := by
  induction hs generalizing k with
  | refl => exact ⟨k,by omega,ht⟩
  | next hs htail ih =>
    obtain ⟨j,hj,hjterm⟩ := ht.after_step hs
    obtain ⟨i,hi,hiterm⟩ := ih hjterm
    exact ⟨i,by omega,hiterm⟩

theorem TerminatesIn.after_steps (ht : TerminatesIn ν e k w) (hs : Steps ν e base) :
    ∃ i, i ≤ k ∧ TerminatesIn ν base i w := by
  obtain ⟨p,hp⟩ := hs.counted
  obtain ⟨i,hi,hiterm⟩ := ht.after_prefix hp
  exact ⟨i,by omega,hiterm⟩

end LeanSce.Source

/-! ## Record Counted Evaluation -/

namespace LeanSce.Source

theorem step_record_cons_value (hv : Value v) :
    step ν (.record (.cons l v fs)) = (step ν fs).map (fun fs' => .record (.cons l v fs')) := by
  rw [step_record_eq]
  cases hf : fs.isValue with
  | false =>
    rw [step_cons_right hv hf,Option.map_map]
    rfl
  | true =>
    rw [value_no_step (e := .cons l v fs) (Bool.and_eq_true_iff.mpr ⟨hv,hf⟩),value_no_step hf]
    rfl

/-- Adding a completed head field charges no steps while the tail evaluates. -/
theorem StepsN.record_prepend (hs : StepsN ν k (.record fs) (.record gs)) (hv : Value v) :
    StepsN ν k (.record (.cons l v fs)) (.record (.cons l v gs)) := by
  induction k generalizing fs with
  | zero => cases hs; exact .refl
  | succ k ih =>
    cases hs with
    | next hs ht =>
      have hs' := hs.2
      rw [step_record_eq] at hs'
      obtain ⟨fs',hfs',heq⟩ := Option.map_eq_some_iff.mp hs'
      cases heq
      exact .next ⟨hs.1,by rw [step_record_cons_value hv,hfs']; rfl⟩ (ih ht)

/-- Every bounded run with a completed head is precisely a tail run. -/
theorem TerminatesIn.record_cons_inv (ht : TerminatesIn ν (.record (.cons l v fs)) k w)
    (hv : Value v) :
    ∃ gs, w = .record (.cons l v gs) ∧ TerminatesIn ν (.record fs) k (.record gs) := by
  obtain ⟨hs,hw⟩ := ht
  induction k generalizing fs with
  | zero =>
    cases hs
    exact ⟨fs,rfl,.refl,(Bool.and_eq_true_iff.mp hw).2⟩
  | succ k ih =>
    cases hs with
    | next hs ht =>
      have hs' := hs.2
      rw [step_record_cons_value hv] at hs'
      obtain ⟨fs',hfs',heq⟩ := Option.map_eq_some_iff.mp hs'
      cases heq
      obtain ⟨gs,heq,hterm⟩ := ih ht
      exact ⟨gs,heq,.next ⟨hs.1,by rw [step_record_eq,hfs']; rfl⟩ hterm.1,hterm.2⟩

theorem Terminates.record_prepend (ht : Terminates ν (.record fs) (.record gs)) (hv : Value v) :
    Terminates ν (.record (.cons l v fs)) (.record (.cons l v gs)) := by
  obtain ⟨k,hk⟩ := ht.counted
  exact ⟨(hk.1.record_prepend hv).toSteps,Bool.and_eq_true_iff.mpr ⟨hv,ht.2⟩⟩

end LeanSce.Source

/-! ## Caller Independence -/

namespace LeanSce.Source

theorem TerminatesIn.box_caller (ht : TerminatesIn ν (.box env body) n w)
    (hν : Value ν) (hμ : Value μ) (he : Value env) :
    TerminatesIn μ (.box env body) n w := by
  obtain ⟨j,rfl,hbody⟩ := ht.box_inv hν he
  exact hbody.box hμ he

private theorem value_app_step (hf : Value f) (hx : Value x)
    (hs : Step ν (.app f x) e') :
    ∃ env body, e' = .box env body ∧ Value env ∧
      ∀ μ, Value μ → Step μ (.app f x) (.box env body) := by
  have hh := hs.2
  simp only [step_app_eq,(show f.isValue = true from hf),
    (show x.isValue = true from hx),Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases f <;> simp only [reduceCtorEq,Option.some.injEq] at hh
  case clo cap a body =>
    subst e'
    refine ⟨.pair cap x,body,rfl,Bool.and_eq_true_iff.mpr ⟨hf,hx⟩,?_⟩
    intro μ hμ
    exact ⟨hμ,by simp [step_app_eq,Term.isValue,(show cap.isValue = true from hf),
      (show x.isValue = true from hx)]⟩
  case rclo cap a b body =>
    subst e'
    refine ⟨.pair (.pair cap (.rclo cap a b body)) x,body,rfl,
      Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hf,hf⟩,hx⟩,?_⟩
    intro μ hμ
    exact ⟨hμ,by simp [step_app_eq,Term.isValue,(show cap.isValue = true from hf),
      (show x.isValue = true from hx)]⟩

/-- A saved value-function call has exactly the same reductions under any
    caller: activation installs its own captured environment. -/
theorem TerminatesIn.app_caller (ht : TerminatesIn ν (.app f x) n w)
    (hμ : Value μ) (hf : Value f) (hx : Value x) :
    TerminatesIn μ (.app f x) n w := by
  cases ht.1 with
  | refl => cases ht.2
  | next hs htail =>
    obtain ⟨env,body,rfl,he,hstep⟩ := value_app_step hf hx hs
    exact ⟨.next (hstep μ hμ)
      (TerminatesIn.box_caller ⟨htail,ht.2⟩ hs.1 hμ he).1,ht.2⟩

/-- A closed certificate is evaluated under unit, with its original reduction
    count retained, even if its stored code is an arbitrary computation. -/
theorem TerminatesIn.certificate_caller
    (ht : TerminatesIn ν (.app (.box .unit code) x) n w)
    (hν : Value ν) (hμ : Value μ) (hx : Value x) :
    TerminatesIn μ (.app (.box .unit code) x) n w := by
  obtain ⟨f,i,j,rfl,hf,hrest⟩ := strict_app_left.decompose_counted ht
  have hf' := hf.box_caller hν hμ (show Value .unit from rfl)
  have hrest' := hrest.app_caller hμ hf.2 hx
  exact ⟨hf'.1.app_left.trans hrest'.1,ht.2⟩

theorem Terminates.app_caller (ht : Terminates ν (.app f x) w)
    (hμ : Value μ) (hf : Value f) (hx : Value x) :
    Terminates μ (.app f x) w := by
  obtain ⟨n,hn⟩ := ht.counted
  exact (hn.app_caller hμ hf hx).toTerminates

theorem Terminates.certificate_caller
    (ht : Terminates ν (.app (.box .unit code) x) w)
    (hν : Value ν) (hμ : Value μ) (hx : Value x) :
    Terminates μ (.app (.box .unit code) x) w := by
  obtain ⟨n,hn⟩ := ht.counted
  exact (hn.certificate_caller hν hμ hx).toTerminates

theorem TerminatesIn.merge_caller (ht : TerminatesIn ν (.merge a b) n w)
    (hμ : Value μ) (ha : Value a) (hb : Value b) :
    TerminatesIn μ (.merge a b) n w := by
  cases ht.1 with
  | refl => cases ht.2
  | next hs htail =>
    have hh := hs.2
    simp only [step_merge_eq,(show a.isValue = true from ha),
      (show b.isValue = true from hb),Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
    cases a <;> try simp only [reduceCtorEq] at hh
    case record fs =>
      cases b <;> try simp only [reduceCtorEq] at hh
      case record gs =>
        split at hh
        · rename_i hd
          simp only [Option.some.injEq] at hh
          subst_vars
          have hv : Value (.record (fs.append gs)) := Term.append_value fs ha hb
          obtain ⟨rfl,rfl⟩ := htail.value_inv hv
          exact ⟨.next ⟨hμ,by simpa only [step_merge_eq,Term.isValue,
            (show fs.isValue = true from ha),(show gs.isValue = true from hb),
            Bool.not_true,Bool.false_eq_true,↓reduceIte] using hs.2⟩ .refl,hv⟩
        · cases hh

theorem Terminates.merge_caller (ht : Terminates ν (.merge a b) w)
    (hμ : Value μ) (ha : Value a) (hb : Value b) :
    Terminates μ (.merge a b) w := by
  obtain ⟨n,hn⟩ := ht.counted
  exact (hn.merge_caller hμ ha hb).toTerminates

end LeanSce.Source

/-! ## Common Evaluation -/

namespace LeanSce.Source

private theorem isValue_false_of_not_value (hn : ¬ Value e) : e.isValue = false := by
  cases h : e.isValue with
  | false => rfl
  | true => exact False.elim (hn h)

theorem strict_pair_left : StrictFrame ν (fun x => .pair x y) := by
  constructor
  · intro e hv; exact (Bool.and_eq_true_iff.mp hv).1
  · intro e hn; exact step_pair_left (isValue_false_of_not_value hn)

theorem strict_pair_right (hv : Value x) : StrictFrame ν (.pair x) := by
  constructor
  · intro e hw; exact (Bool.and_eq_true_iff.mp hw).2
  · intro e hn; exact step_pair_right hv (isValue_false_of_not_value hn)

theorem strict_fst : StrictFrame ν Term.fst := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_fst_eq,isValue_false_of_not_value hn]

theorem strict_snd : StrictFrame ν Term.snd := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_snd_eq,isValue_false_of_not_value hn]

theorem strict_inl : StrictFrame ν (.inl b) := ⟨fun _ hv => hv,fun _ _ => step_inl_eq⟩
theorem strict_inr : StrictFrame ν (.inr a) := ⟨fun _ hv => hv,fun _ _ => step_inr_eq⟩
theorem strict_tag : StrictFrame ν (.tag l) := ⟨fun _ hv => hv,fun _ _ => step_tag_eq⟩

theorem strict_get : StrictFrame ν (fun x => .get x l) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_get_eq,isValue_false_of_not_value hn]

theorem strict_find : StrictFrame ν (.find l) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_find_eq,isValue_false_of_not_value hn]

theorem strict_take : StrictFrame ν (.take ls) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_take_eq,isValue_false_of_not_value hn]

theorem strict_drop : StrictFrame ν (.drop ls) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_drop_eq,isValue_false_of_not_value hn]

theorem strict_relabel : StrictFrame ν (.relabel old new) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_relabel_eq,isValue_false_of_not_value hn]

theorem strict_ite : StrictFrame ν (fun c => .ite c x y) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_ite_eq,isValue_false_of_not_value hn]

theorem strict_case : StrictFrame ν (fun e => .case e l r) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn; simp [step_case_eq,isValue_false_of_not_value hn]

theorem strict_record_head : StrictFrame ν (fun x => .record (.cons l x fs)) := by
  constructor
  · intro e hv; exact (Bool.and_eq_true_iff.mp hv).1
  · intro e hn
    rw [step_record_eq,step_cons_left (isValue_false_of_not_value hn)]
    simp only [Option.map_map,Function.comp_def]

theorem strict_prim_left : StrictFrame ν (fun x => .prim p (.cons l x (.cons k y .nil))) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he := isValue_false_of_not_value hn
    rw [step_prim_eq]
    simp only [Term.isValue,he,Bool.false_and,Bool.not_false,↓reduceIte]
    rw [step_cons_left he]
    simp only [Option.map_map,Function.comp_def]

theorem strict_prim_right (hx : Value x) :
    StrictFrame ν (fun y => .prim p (.cons l x (.cons k y .nil))) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he := isValue_false_of_not_value hn
    rw [step_prim_eq]
    simp only [Term.isValue,(show x.isValue = true from hx),he,
      Bool.true_and,Bool.false_and,Bool.not_false,↓reduceIte]
    rw [step_cons_right hx (by simp [Term.isValue,he]),step_cons_left he]
    simp only [Option.map_map,Function.comp_def]

theorem strict_prim_one : StrictFrame ν (fun x => .prim p (.cons l x .nil)) := by
  constructor
  · intro _ hv; cases hv
  · intro e hn
    have he := isValue_false_of_not_value hn
    rw [step_prim_eq]
    simp only [Term.isValue,he,Bool.false_and,Bool.not_false,↓reduceIte]
    rw [step_cons_left he]
    simp only [Option.map_map,Function.comp_def]

theorem strict_tapp : StrictFrame ν (fun f => .tapp f u) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_tapp_eq,he]

theorem strict_pack : StrictFrame ν (.pack u t) :=
  ⟨fun _ hv => hv,fun _ _ => step_pack_eq⟩

theorem strict_fold : StrictFrame ν (.fold t) :=
  ⟨fun _ hv => hv,fun _ _ => step_fold_eq⟩

theorem strict_unfold : StrictFrame ν Term.unfold := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_unfold_eq,he]

theorem strict_unpack : StrictFrame ν (fun p => .unpack p body) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_unpack_eq,he]

end LeanSce.Source

namespace LeanSce.Target

theorem strict_tapp : StrictFrame ν (fun f => .tapp f u) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_tapp_eq,he]

theorem strict_pack : StrictFrame ν (.pack u t) :=
  ⟨fun _ hv => hv,fun _ _ => step_pack_eq⟩

theorem strict_fold : StrictFrame ν (.fold t) :=
  ⟨fun _ hv => hv,fun _ _ => step_fold_eq⟩

theorem strict_unfold : StrictFrame ν Term.unfold := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_unfold_eq,he]

theorem strict_unpack : StrictFrame ν (fun p => .unpack p body) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_unpack_eq,he]

end LeanSce.Target

/-! ## Linking Evaluation -/

namespace LeanSce.Source

theorem Terminates.merge_decompose (he : Terminates ν (.merge e f) w) :
    ∃ E F, Terminates ν e E ∧ Terminates ν f F ∧ Terminates ν (.merge E F) w := by
  obtain ⟨E,hE,hr⟩ := strict_merge_left.decompose he
  obtain ⟨F,hF,hr⟩ := (strict_merge_right hE.2).decompose hr
  exact ⟨E,F,hE,hF,hr⟩

theorem Terminates.link_decompose (hν : Value ν)
    (he : Terminates ν (.link p i o cd provider m) w) :
    ∃ P M, Terminates ν provider P ∧ Terminates ν m M ∧
      Terminates ν (.merge P (.run p i o cd M P)) w := by
  obtain ⟨P,hP,hr⟩ := strict_link_provider.decompose he
  obtain ⟨M,hM,hr⟩ := (strict_link_module hP.2).decompose hr
  exact ⟨P,M,hP,hM,hr.after_step ⟨hν,by
    simp [step_link_eq,(show P.isValue = true from hP.2),(show M.isValue = true from hM.2)]⟩⟩

theorem Terminates.run_decompose (hν : Value ν)
    (he : Terminates ν (.run p i o cd m provider) w) :
    ∃ M P, Terminates ν m M ∧ Terminates ν provider P ∧
      Terminates ν (.invoke i o M (.view (.record p) (.record i) cd P)) w := by
  obtain ⟨M,hM,hr⟩ := strict_run_module.decompose he
  obtain ⟨P,hP,hr⟩ := (strict_run_provider hM.2).decompose hr
  exact ⟨M,P,hM,hP,hr.after_step ⟨hν,by
    simp [step_run_eq,(show P.isValue = true from hP.2),(show M.isValue = true from hM.2)]⟩⟩

theorem Terminates.invoke_decompose
    (he : Terminates ν (.invoke i o m imports) w) :
    ∃ M I, Terminates ν m M ∧ Terminates ν imports I ∧
      Terminates ν (.invoke i o M I) w := by
  obtain ⟨M,hM,hr⟩ := strict_invoke_module.decompose he
  obtain ⟨I,hI,hr⟩ := (strict_invoke_imports hM.2).decompose hr
  exact ⟨M,I,hM,hI,hr⟩

theorem merge_records_step (hν : Value ν) (hf : Value fs) (hg : Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true) :
    Step ν (.merge (.record fs) (.record gs)) (.record (fs.append gs)) := by
  refine ⟨hν,?_⟩
  rw [step_merge_eq]
  simp only [Term.isValue,(show fs.isValue = true from hf),(show gs.isValue = true from hg),
    Bool.not_true,Bool.false_eq_true,↓reduceIte,hd]

theorem Terminates.merge_records (hν : Value ν) (hf : Value fs) (hg : Value gs)
    (hd : fs.labels.all (fun l => !gs.labels.contains l) = true) :
    Terminates ν (.merge (.record fs) (.record gs)) w ↔ w = .record (fs.append gs) := by
  have hval : Value (.record (fs.append gs)) := Term.append_value fs hf hg
  constructor
  · intro ht
    exact (ht.after_step (merge_records_step hν hf hg hd)).1.value_result hval
  · intro hw
    subst w
    exact ⟨.single (merge_records_step hν hf hg hd),hval⟩

theorem Term.labels_append (fs gs : Fields) :
    (fs.append gs).labels = fs.labels ++ gs.labels := by
  cases fs with
  | nil => rfl
  | cons l e rest => simp [Term.append,Term.labels,Term.labels_append rest gs]

theorem Term.append_assoc (fs gs hs : Fields) :
    (fs.append gs).append hs = fs.append (gs.append hs) := by
  cases fs with
  | nil => rfl
  | cons l e rest => simp [Term.append,Term.append_assoc rest gs hs]

theorem Term.append_nil (fs : Fields) : fs.append .nil = fs := by
  cases fs with
  | nil => rfl
  | cons l e rest => simp [Term.append,Term.append_nil rest]

theorem Term.filter_append (fs gs : Fields) :
    (fs.append gs).filter p = (fs.filter p).append (gs.filter p) := by
  cases fs with
  | nil => rfl
  | cons l e rest =>
    simp only [Term.append,Term.filter]
    split <;> simp [Term.append,Term.filter_append rest gs]

theorem Term.filter_all (fs : Fields) (hp : ∀ l ∈ fs.labels, p l = true) :
    fs.filter p = fs := by
  cases fs with
  | nil => rfl
  | cons l e rest =>
    simp only [Term.labels,List.mem_cons] at hp
    simp [Term.filter,hp l (Or.inl rfl),
      Term.filter_all rest (fun l hl => hp l (Or.inr hl))]

theorem Term.filter_none (fs : Fields) (hp : ∀ l ∈ fs.labels, p l = false) :
    fs.filter p = .nil := by
  cases fs with
  | nil => rfl
  | cons l e rest =>
    simp only [Term.labels,List.mem_cons] at hp
    simp [Term.filter,hp l (Or.inl rfl),
      Term.filter_none rest (fun l hl => hp l (Or.inr hl))]

theorem Term.append_restrict_left (fs gs : Fields)
    (hd : ∀ l ∈ gs.labels, l ∉ fs.labels) :
    (fs.append gs).filter fs.labels.contains = fs := by
  rw [Term.filter_append,
    Term.filter_all fs (fun l hl => by simpa using hl),
    Term.filter_none gs (fun l hl => by simp [hd l hl]),Term.append_nil]

end LeanSce.Source

/-! ## Module Entry -/

namespace LeanSce.Source

/-- Module entry installs only saved captures and exact accumulated imports. -/
inductive ModuleEntry : Expr → Expr → Expr → Expr → Prop where
  | module (hf : Value fs) (hg : Value gs)
      (hd : fs.labels.all (fun l => !gs.labels.contains l) = true) :
      ModuleEntry (.moduleVal (.record fs) c i o body) (.record gs)
        (.record (fs.append gs)) body
  | residual (hm : Value m) (hf : Value fs) (hg : Value gs)
      (hd : fs.labels.all (fun l => !gs.labels.contains l) = true)
      (he : ModuleEntry m (.record (fs.append gs)) env body) :
      ModuleEntry (.resid m (.record fs) j k o) (.record gs) env body

theorem ModuleEntry.environment_value (he : ModuleEntry m imports env body) : Value env := by
  induction he with
  | module hf hg => exact Term.append_value _ hf hg
  | residual _ _ _ _ _ ih => exact ih

/-- Each invocation has a finite, caller-independent entry prefix. -/
theorem ModuleEntry.prefix (he : ModuleEntry m imports env body)
    (hν : Value ν) (i o : Row) : Steps ν (.invoke i o m imports) (.box env body) := by
  induction he generalizing i o ν with
  | @module fs gs c i₀ o₀ body hf hg hd =>
    apply Steps.next (e' := .box (.merge (.record fs) (.record gs)) body)
    · exact ⟨hν,by simp [step_invoke_eq,Term.isValue,(show fs.isValue = true from hf),
        (show gs.isValue = true from hg)]⟩
    · exact strict_box_left.lift_steps (.single (merge_records_step hν hf hg hd))
  | @residual m fs gs env body j k o₀ hm hf hg hd he ih =>
    apply Steps.next (e' := .invoke (.union j k) o m (.merge (.record fs) (.record gs)))
    · exact ⟨hν,by simp [step_invoke_eq,Term.isValue,(show m.isValue = true from hm),
        (show fs.isValue = true from hf),(show gs.isValue = true from hg)]⟩
    · exact ((strict_invoke_imports hm).lift_steps
        (.single (merge_records_step hν hf hg hd))).trans (ih hν _ _)

theorem ModuleEntry.terminates_iff (he : ModuleEntry m imports env body) (hν : Value ν) :
    Terminates ν (.invoke i o m imports) w ↔ Terminates env body w := by
  constructor
  · intro ht
    exact (ht.after_steps (he.prefix hν i o)).box_inv he.environment_value
  · intro ht
    exact (ht.box hν he.environment_value).prepend (he.prefix hν i o)

/-- Typed module values always have an entry configuration; its body remains
    checked under exactly the installed record environment. -/
theorem module_entry_exists (hm : ValueType Δ m (.module i o))
    (hi : ValueType Δ imports (.record i)) (hΔ : Context.Valid Δ) :
    ∃ env body r, ModuleEntry m imports env body ∧ ValueType Δ env (.record r) ∧
      HasType Δ (.record r) body (.record o) := by
  rcases hm.2.value_shape hm.1 with hmod | hres
  · obtain ⟨cap,c,i₀,o₀,body,rfl⟩ := hmod
    cases hm.2.value_origin hm.1 with
    | moduleVal wi wo hd hc hb he =>
      have heq := he.module_inv
      have hir : ValueType Δ imports (.record _) :=
        ⟨hi.1,.conv hi.2 (.record heq.1.symm) (.record wi)⟩
      obtain ⟨fs,hfs⟩ := hc.2.value_shape hc.1
      obtain ⟨gs,hgs⟩ := hir.2.value_shape hir.1
      subst hfs
      subst hgs
      have hft := hc.2.value_record_inv hc.1 (hc.2.result_wf hΔ).record_row
      have hgt := hir.2.value_record_inv hir.1 wi
      refine ⟨_,_,(.union c i₀),.module hc.1 hir.1 (hft.merge_check hgt hd),?_,?_⟩
      · exact ⟨Term.append_value fs hc.1 hir.1,.record (hft.append hΔ hgt hd)⟩
      · exact .conv hb (.record heq.2) (.record (hm.2.result_wf hΔ).module_exports)
  · obtain ⟨original,saved,j,k,o₀,rfl⟩ := hres
    cases hm.2.value_origin hm.1 with
    | resid hm₀ hs wj wk hd he =>
      have heq := he.module_inv
      have hir : ValueType Δ imports (.record _) :=
        ⟨hi.1,.conv hi.2 (.record heq.1.symm) (.record wk)⟩
      obtain ⟨fs,hfs⟩ := hs.2.value_shape hs.1
      obtain ⟨gs,hgs⟩ := hir.2.value_shape hir.1
      subst hfs
      subst hgs
      have hft := hs.2.value_record_inv hs.1 wj
      have hgt := hir.2.value_record_inv hir.1 wk
      have hjoined : ValueType Δ (.record (fs.append gs)) (.record (.union _ _)) :=
        ⟨Term.append_value fs hs.1 hir.1,.record (hft.append hΔ hgt hd)⟩
      have hm' : ValueType Δ _ (.module (.union _ _) o) :=
        ⟨hm₀.1,.conv hm₀.2 (.module .refl heq.2)
          (.module (.union wj wk hd) (hm.2.result_wf hΔ).module_exports)⟩
      obtain ⟨env,body,r,hentry,henv,hbody⟩ := module_entry_exists hm' hjoined hΔ
      exact ⟨env,body,r,.residual hm₀.1 hs.1 hir.1 (hft.merge_check hgt hd) hentry,henv,hbody⟩
termination_by sizeOf m

/-- Invocation of fixed values uses its own saved environment under any caller. -/
theorem Terminates.invoke_caller (ht : Terminates ν (.invoke i o m imports) w)
    (hm : ValueType Δ m (.module i o)) (hi : ValueType Δ imports (.record i))
    (hΔ : Context.Valid Δ) (hν : Value ν) (hμ : Value μ) :
    Terminates μ (.invoke i o m imports) w := by
  obtain ⟨env,body,r,he,henv,hbody⟩ := module_entry_exists hm hi hΔ
  exact (he.terminates_iff hμ).mpr ((he.terminates_iff hν).mp ht)

end LeanSce.Source

/-! ## Native Evaluation -/

namespace LeanSce.Source

theorem TerminatesIn.pair_inv (ht : TerminatesIn ν (.pair e f) n w) :
    ∃ x y i j, n = i+j ∧ TerminatesIn ν e i x ∧ TerminatesIn ν f j y ∧ w = .pair x y := by
  obtain ⟨x,i,p,hip,hx,hrest⟩ := strict_pair_left.decompose_counted ht
  obtain ⟨y,j,q,hjq,hy,hpair⟩ := (strict_pair_right hx.2).decompose_counted hrest
  have hv : Value (.pair x y) := Bool.and_eq_true_iff.mpr ⟨hx.2,hy.2⟩
  obtain ⟨rfl,rfl⟩ := hpair.1.value_inv hv
  exact ⟨x,y,i,j,by omega,hx,hy,rfl⟩

theorem Terminates.pair (he : Terminates ν e x) (hf : Terminates ν f y) :
    Terminates ν (.pair e f) (.pair x y) :=
  strict_pair_left.terminates he ((strict_pair_right he.2).terminates hf
    ⟨.refl,Bool.and_eq_true_iff.mpr ⟨he.2,hf.2⟩⟩)

theorem TerminatesIn.query_inv (ht : TerminatesIn ν .query n w) (hν : Value ν) :
    n = 1 ∧ w = ν := by
  obtain ⟨i,hi,ht⟩ := ht.after_step (query_step hν)
  obtain ⟨rfl,rfl⟩ := ht.1.value_inv hν
  exact ⟨by omega,rfl⟩

/-- Entering a native box retains precisely the evaluated replacement ambient. -/
theorem TerminatesIn.native_box_inv (ht : TerminatesIn ν (.box e body) n w)
    (hν : Value ν) :
    ∃ cap i j, n = i+j+1 ∧ TerminatesIn ν e i cap ∧ TerminatesIn cap body j w := by
  obtain ⟨cap,i,k,hik,hcap,hrest⟩ := strict_box_left.decompose_counted ht
  obtain ⟨j,hj,hbody⟩ := hrest.box_inv hν hcap.2
  exact ⟨cap,i,j,by omega,hcap,hbody⟩

theorem Terminates.native_box (hν : Value ν) (he : Terminates ν e cap)
    (hb : Terminates cap body w) : Terminates ν (.box e body) w :=
  strict_box_left.terminates he (hb.box hν he.2)

theorem TerminatesIn.letIn_inv (ht : TerminatesIn ν (.letIn e body) n w)
    (hν : Value ν) :
    ∃ x i j, n = i+j+2 ∧ TerminatesIn ν e i x ∧
      TerminatesIn (.pair ν x) body j w := by
  obtain ⟨cap,p,j,hpj,hcap,hbody⟩ := ht.native_box_inv hν
  obtain ⟨v,x,i,q,hiq,hν',hx,rfl⟩ := hcap.pair_inv
  obtain ⟨rfl,rfl⟩ := hν'.query_inv hν
  exact ⟨x,q,j,by omega,hx,hbody⟩

theorem Terminates.letIn (hν : Value ν) (he : Terminates ν e x)
    (hb : Terminates (.pair ν x) body w) : Terminates ν (.letIn e body) w :=
  Terminates.native_box hν ((show Terminates ν .query ν from ⟨.single (query_step hν),hν⟩).pair he) hb

end LeanSce.Source

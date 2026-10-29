import LeanSce.Target.Abstraction.Data
import LeanSce.Target.Abstraction.Equality
import LeanSce.Target.Abstraction.Functions
import LeanSce.Target.Abstraction.Infrastructure
import LeanSce.Target.LogicalRelation.Contexts
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Abstraction / RepresentationIndependence

Proofs and supporting constructions for representation independence.
-/

/-! ## Heterogeneous Open -/

namespace LeanSce.Target.Heterogeneous

def OpenRel (Δ : Context) (h : Typ) (e E : Expr) (a : Typ) : Prop :=
  ∀ η : Valuation, η.Valid Δ → ∀ n ν N, ValRel n h η ν N →
    ExprRel n a η (ν,e.subst η.left) (N,E.subst η.right)

theorem OpenRel.body (he : OpenRel Δ h e E a) (hη : η.Valid Δ) :
    BodyRel η h a (e.subst η.left) (E.subst η.right) := he η hη

theorem OpenRel.polybody {h : Typ}
    (he : OpenRel (Δ.extend k gs) (h.rename Nat.succ) e E a)
    (hη : η.Valid Δ) (hf : FreshGuards k gs) :
    PolyBodyRel η k gs a h (e.subst η.left.lift) (E.subst η.right.lift) := by
  intro p hp hl hr n ν N hcap
  have hη' := hη.extend hf hp hl hr
  have hrel := he (η.extend p) hη' n ν N hcap
  simpa only [Valuation.extend,Term.subst_instantiate] using hrel

theorem OpenRel.unpack_body {h b : Typ}
    (he : OpenRel (Δ.extend k gs) (.prod (h.rename Nat.succ) a) e E (b.rename Nat.succ))
    (hη : η.Valid Δ) (hf : FreshGuards k gs) :
    UnpackBodyRel η k gs a h b (e.subst η.left.lift) (E.subst η.right.lift) := by
  intro p hp hl hr n ν N hcap
  have hη' := hη.extend hf hp hl hr
  have hrel := he (η.extend p) hη' n ν N hcap
  simpa only [Valuation.extend,Term.subst_instantiate] using hrel

theorem OpenRel.values (he : OpenRel Δ .unit e E a) (hv : Value e) (hV : Value E)
    (hη : η.Valid Δ) : ValRel n a η (e.subst η.left) (E.subst η.right) := by
  have hrel := he η hη (n+1) .unit .unit ValRel.unit
  rw [ExprRel] at hrel
  have hvθ : Value (e.subst η.left) := by simpa [Value] using hv
  have hVθ : Value (E.subst η.right) := by simpa [Value] using hV
  obtain ⟨w,hw,hr⟩ := hrel.1 0 (by omega) (e.subst η.left) ⟨.refl,hvθ⟩
  have heq := hw.1.value_result hVθ
  subst w
  exact hr.mono (by omega)

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Closed -/

namespace LeanSce.Target.Heterogeneous

def dummySubst : Subst := fun k _ => match k with | .type => .unit | .row => .empty

theorem Valuation.closed_interpretations (η ζ : Valuation) :
    (η.substitute dummySubst).Equivalent (ζ.substitute dummySubst) := by
  refine ⟨?_,?_,?_,?_⟩
  · funext k i; cases k <;> rfl
  · funext k i; cases k <;> rfl
  · intro i n v w
    simp only [ValRel,ShapeRel,Valuation.substitute,Valuation.typeCandidate,dummySubst,Ty.subst]
  · intro i n l v w
    simp [FieldRel,Valuation.substitute,Valuation.rowCandidate,dummySubst,Ty.subst,Ty.knownLabels]

/-- A closed public type has no dependency on an unrelated semantic valuation,
    even when later clients introduce more abstract type and row binders. -/
theorem ValRel.closed (wa : WellFormed .empty a) (η ζ : Valuation) :
    ValRel n a η v w ↔ ValRel n a ζ v w := by
  have hl := ValRel.substitution (n:=n) (v:=v) (w:=w) a dummySubst η
  have hr := ValRel.substitution (n:=n) (v:=v) (w:=w) a dummySubst ζ
  rw [wa.closed_subst] at hl hr
  exact hl.trans ((ValRel.environment (η.closed_interpretations ζ) a).trans hr.symm)

theorem ExprRel.closed (wa : WellFormed .empty a) (η ζ : Valuation) :
    ExprRel n a η q r ↔ ExprRel n a ζ q r := by
  have hl := ExprRel.substitution (n:=n) (q:=q) (r:=r) a dummySubst η
  have hr := ExprRel.substitution (n:=n) (q:=q) (r:=r) a dummySubst ζ
  rw [wa.closed_subst] at hl hr
  exact hl.trans ((ExprRel.environment (η.closed_interpretations ζ) a).trans hr.symm)

/-- A closed hole keeps its full heterogeneous meaning under every later type
    or row binder in an actual observation context. -/
theorem closed_hole_logical (he : HasType .empty h e a) (hE : HasType .empty h E a)
    (hr : ∀ n ν N, ValRel n h Valuation.empty ν N →
      ExprRel n a Valuation.empty (ν,e) (N,E)) :
    ∀ Δ H x X b, HoleAt h a e E Δ H x X b → OpenRel Δ H x X b := by
  intro Δ H x X b hhole
  obtain ⟨rfl,rfl,rfl,rfl⟩ := hhole
  intro η _ n ν N hν
  have hh := he.ambient_wf
  have ha := he.result_wf .empty
  have henv := (ValRel.closed hh η Valuation.empty).mp hν
  have hout := (ExprRel.closed ha Valuation.empty η).mp (hr n ν N henv)
  simpa only [he.closed_subst η.left,hE.closed_subst η.right] using hout

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Adequacy -/

namespace LeanSce.Target.Heterogeneous

theorem ValRel.ground_eq (h : ValRel n a η v w) (hg : GroundType a) : v = w := by
  rw [ValRel] at h
  have hs := h.2.2
  cases hg with
  | unit => rw [ShapeRel] at hs; obtain ⟨rfl,rfl⟩ := hs; rfl
  | int => rw [ShapeRel] at hs; obtain ⟨_,rfl,rfl⟩ := hs; rfl
  | bool => rw [ShapeRel] at hs; obtain ⟨_,rfl,rfl⟩ := hs; rfl
  | string => rw [ShapeRel] at hs; obtain ⟨_,rfl,rfl⟩ := hs; rfl

/-- All-index logical relatedness gives the actual ground observation, including
    an infinite reduction when no finite result exists. -/
theorem ground_adequacy (hr : ∀ n, ExprRel n g η (ν,e) (ν,E)) (hg : GroundType g)
    (hν : ValueType .empty ν H) (he : HasType .empty H e g)
    (hE : HasType .empty H E g) : ObservationEq ν e E := by
  have ht : ∀ v, Terminates ν e v ↔ Terminates ν E v := by
    intro v
    constructor
    · intro hv
      obtain ⟨k,hk⟩ := hv.counted
      have hrk := hr (k+1)
      rw [ExprRel] at hrk
      obtain ⟨w,hw,heq⟩ := hrk.1 k (by omega) v hk
      have hvw := heq.ground_eq hg
      simpa only [hvw] using hw
    · intro hv
      obtain ⟨k,hk⟩ := hv.counted
      have hrk := hr (k+1)
      rw [ExprRel] at hrk
      obtain ⟨w,hw,heq⟩ := hrk.2 k (by omega) v hk
      have hwv := heq.ground_eq hg
      simpa only [hwv] using hw
  refine ⟨ht,?_⟩
  rw [diverges_iff_not_terminates he .empty hν, diverges_iff_not_terminates hE .empty hν]
  simp only [ht]

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Fundamental -/

namespace LeanSce.Target.Heterogeneous

private theorem valid_all (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.all k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | all hf hg _ => exact .extend hΔ hf hg

private theorem valid_ex (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.ex k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | ex hf hg _ => exact .extend hΔ hf hg

/-- Every syntactic context rule preserves the logical relation. The hole
    hypothesis is the semantic premise for its declared local typing judgment. -/
theorem compatible_logical (hc : Compatible R Δ h e E a)
    (hR : ∀ Δ h e E a, R Δ h e E a → OpenRel Δ h e E a) :
    Context.Valid Δ → OpenRel Δ h e E a := by
  apply Compatible.rec
    (motive_1 := fun Δ h e E a _ => Context.Valid Δ → OpenRel Δ h e E a)
    (motive_2 := fun Δ h fs Fs r _ => Context.Valid Δ →
      OpenRel Δ h (.record fs) (.record Fs) (.record r))
    (t := hc)
  all_goals intros
  all_goals intros
  all_goals intros
  case hole =>
    rename_i Δ h e a E he hE hh hΔ
    exact hR Δ h e E a hh
  all_goals unfold OpenRel
  all_goals intros
  case query => rename_i hΔ η hη n ν N hν; exact ExprRel.query hν
  case unit => exact ValRel.unit.toExpr
  case int => exact ValRel.int.toExpr
  case bool => exact ValRel.bool.toExpr
  case string => exact ValRel.string.toExpr
  case pair =>
    rename_i hx hy ihx ihy hΔ η hη n ν N hν
    exact ExprRel.pair (ihx hΔ η hη n ν N hν) (ihy hΔ η hη n ν N hν)
  case fst =>
    rename_i hx ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).fst hν.left.1 hν.right.1
  case snd =>
    rename_i hx ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).snd hν.left.1 hν.right.1
  case box =>
    rename_i hx hb ihx ihb hΔ η hη n ν N hν
    exact ExprRel.box (ihx hΔ η hη n ν N hν) ((ihb hΔ).body hη) hν.left.1 hν.right.1
  case lam =>
    rename_i wa hb ih hΔ η hη n ν N hν
    exact ExprRel.lam (wa.subst hη.1.respects) (wa.subst hη.2.1.respects)
      (hb.left_typed.subst hΔ hη.1.respects) (hb.right_typed.subst hΔ hη.2.1.respects)
      ((ih hΔ).body hη) hν
  case recfn =>
    rename_i wa wb hb ih hΔ η hη n ν N hν
    exact ExprRel.recfn (wa.subst hη.1.respects) (wa.subst hη.2.1.respects) (wb.subst hη.1.respects) (wb.subst hη.2.1.respects)
      (hb.left_typed.subst hΔ hη.1.respects) (hb.right_typed.subst hΔ hη.2.1.respects)
      ((ih hΔ).body hη) hν
  case app =>
    rename_i hf hx ihf ihx hΔ η hη n ν N hν
    exact ExprRel.app (ihf hΔ η hη n ν N hν) (ihx hΔ η hη n ν N hν) hν.left.1 hν.right.1
  case inl =>
    rename_i wb hx ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).inl (wb.subst hη.1.respects) (wb.subst hη.2.1.respects)
  case inr =>
    rename_i wa hx ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).inr (wa.subst hη.1.respects) (wa.subst hη.2.1.respects)
  case case =>
    rename_i hx hl hr ihx ihl ihr hΔ η hη n ν N hν
    exact ExprRel.case (ihx hΔ η hη n ν N hν) hν
      ((ihl hΔ).body hη) ((ihr hΔ).body hη)
  case tag =>
    rename_i hx ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).tag
  case record =>
    rename_i hf ih hΔ η hη n ν N hν
    exact ih hΔ η hη n ν N hν
  case find =>
    rename_i hx hu ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).find (hu) hν.left.1 hν.right.1
  case get =>
    rename_i hx hl ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).get (hx.left_typed.result_wf hΔ).record_row hη hl hν.left.1 hν.right.1
  case merge =>
    rename_i hx hy hd ihx ihy hΔ η hη n ν N hν
    exact ExprRel.merge (ihx hΔ η hη n ν N hν) (ihy hΔ η hη n ν N hν)
      (hx.left_typed.result_wf hΔ).record_row (hy.left_typed.result_wf hΔ).record_row
      hη hd hν.left.1 hν.right.1
  case take =>
    rename_i hx hn hl ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).take (hx.left_typed.result_wf hΔ).record_row hη hl hν.left.1 hν.right.1
  case drop =>
    rename_i hx hn hl ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).drop (hx.left_typed.result_wf hΔ).record_row hη hl hν.left.1 hν.right.1
  case relabel =>
    rename_i hx hl hn hd ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).relabel (hx.left_typed.result_wf hΔ).record_row
      hη hl hn hd hν.left.1 hν.right.1
  case nil => exact ValRel.record_nil.toExpr
  case tapp =>
    rename_i Δ h x X k gs a u hx hk hu hg ih hΔ η hη n ν N hν
    have hp : (η.argument u).Admissible k := by
      simpa only [hk] using Valuation.argument_admissible hη hu
    have hgl : Entails .empty ((gs.subst η.left.lift).open (η.argument u).left) := by
      rw [Valuation.argument_left]
      simpa only [Ty.subst_open] using hg.subst hη.1.respects
    have hgr : Entails .empty ((gs.subst η.right.lift).open (η.argument u).right) := by
      rw [Valuation.argument_right]
      simpa only [Ty.subst_open] using hg.subst hη.2.1.respects
    have hr := (ih hΔ η hη n ν N hν).tapp hp hgl hgr hν.left.1 hν.right.1
    simpa only [Term.subst,Valuation.argument_left,Valuation.argument_right] using
      (ExprRel.opening a u η).mpr hr
  case pack =>
    rename_i Δ k gs a u h x X hw hk hu hg hx ih hΔ η hη n ν N hν
    have hp : (η.argument u).Admissible k := by
      simpa only [hk] using Valuation.argument_admissible hη hu
    have hgl : Entails .empty ((gs.subst η.left.lift).open (η.argument u).left) := by
      rw [Valuation.argument_left]
      simpa only [Ty.subst_open] using hg.subst hη.1.respects
    have hgr : Entails .empty ((gs.subst η.right.lift).open (η.argument u).right) := by
      rw [Valuation.argument_right]
      simpa only [Ty.subst_open] using hg.subst hη.2.1.respects
    have hr := ExprRel.pack_candidate (hw.subst hη.1.respects) (hw.subst hη.2.1.respects)
      hp hgl hgr ((ExprRel.opening a u η).mp (ih hΔ η hη n ν N hν))
    simpa only [Term.subst,Valuation.argument_left,Valuation.argument_right] using hr
  case unfold =>
    rename_i hx ih hΔ η hη n ν N hν
    exact (ih hΔ η hη n ν N hν).unfold hν.left.1 hν.right.1
  case add =>
    rename_i hx hy ihx ihy hΔ η hη n ν N hν
    exact ExprRel.add (ihx hΔ η hη n ν N hν) (ihy hΔ η hη n ν N hν) hν.left.1 hν.right.1
  case eqInt =>
    rename_i hx hy ihx ihy hΔ η hη n ν N hν
    exact ExprRel.eqInt (ihx hΔ η hη n ν N hν) (ihy hΔ η hη n ν N hν) hν.left.1 hν.right.1
  case showInt =>
    rename_i hx ih hΔ η hη n ν N hν
    exact ExprRel.showInt (ih hΔ η hη n ν N hν) hν.left.1 hν.right.1
  case concat =>
    rename_i hx hy ihx ihy hΔ η hη n ν N hν
    exact ExprRel.concat (ihx hΔ η hη n ν N hν) (ihy hΔ η hη n ν N hν) hν.left.1 hν.right.1
  case ite =>
    rename_i hc hx hy ihc ihx ihy hΔ η hη n ν N hν
    exact ExprRel.ite (ihc hΔ η hη n ν N hν) (ihx hΔ η hη n ν N hν)
      (ihy hΔ η hη n ν N hν) hν.left.1 hν.right.1
  case clo =>
    rename_i hh wa hv hV hcap hb ihcap ihb hΔ η hη n ν N hν
    exact (ValRel.clo (wa.subst hη.1.respects) (wa.subst hη.2.1.respects)
      (hb.left_typed.subst hΔ hη.1.respects) (hb.right_typed.subst hΔ hη.2.1.respects)
      ((ihb hΔ).body hη) ((ihcap hΔ).values hv hV hη)).toExpr
  case rclo =>
    rename_i hh wa wb hv hV hcap hb ihcap ihb hΔ η hη n ν N hν
    exact (ValRel.rclo (wa.subst hη.1.respects) (wa.subst hη.2.1.respects) (wb.subst hη.1.respects) (wb.subst hη.2.1.respects)
      (hb.left_typed.subst hΔ hη.1.respects) (hb.right_typed.subst hΔ hη.2.1.respects)
      ((ihb hΔ).body hη) ((ihcap hΔ).values hv hV hη)).toExpr
  case tlam =>
    rename_i Δ k gs a h x X hw hh hb ih hΔ η hη n ν N hν
    have hvalid := valid_all hΔ hw
    cases hw with
    | all hf wg wa =>
      have hw : WellFormed Δ (.all k gs a) := .all hf wg wa
      apply ExprRel.tlam (hw.subst hη.1.respects) (hw.subst hη.2.1.respects)
      · simpa only [Ty.subst_lift_weaken] using hb.left_typed.subst hvalid (hη.1.respects.lift hf)
      · simpa only [Ty.subst_lift_weaken] using hb.right_typed.subst hvalid (hη.2.1.respects.lift hf)
      · exact (ih hvalid).polybody hη hf
      · exact hν
  case unpack =>
    rename_i hx wb hb ihx ihb hΔ η hη n ν N hν
    have hw := hx.left_typed.result_wf hΔ
    have hvalid := valid_ex hΔ hw
    cases hw with
    | ex hf wg wa =>
      exact ExprRel.unpack (ihx hΔ η hη n ν N hν) hν ((ihb hvalid).unpack_body hη hf)
  case fold =>
    rename_i hw hx ih hΔ η hη n ν N hν
    exact ExprRel.fold (hw.subst hη.1.respects) (hw.subst hη.2.1.respects) (ih hΔ η hη n ν N hν)
  case tclo =>
    rename_i Δ h k gs a cap CAP env x X hh hw hv hV hcap hb ihcap ihb hΔ η hη n ν N hν
    have hvalid := valid_all hΔ hw
    cases hw with
    | all hf wg wa =>
      have hw : WellFormed Δ (.all k gs a) := .all hf wg wa
      apply ValRel.toExpr
      apply ValRel.tclo (hw.subst hη.1.respects) (hw.subst hη.2.1.respects)
      · simpa only [Ty.subst_lift_weaken] using hb.left_typed.subst hvalid (hη.1.respects.lift hf)
      · simpa only [Ty.subst_lift_weaken] using hb.right_typed.subst hvalid (hη.2.1.respects.lift hf)
      · exact (ihb hvalid).polybody hη hf
      · exact (ihcap hΔ).values hv hV hη
  case value =>
    rename_i hv hV ht hh ih hΔ η hη n ν N hν
    exact ((ih hΔ).values hv hV hη).toExpr
  case cons =>
    rename_i hx hf hd ihx ihf hΔ η hη n ν N hν
    exact ExprRel.record_cons (ihx hΔ η hη n ν N hν) (ihf hΔ η hη n ν N hν)
      (hx.left_typed.result_wf hΔ) ((HasType.record (hf.left_typed hΔ)).result_wf hΔ).record_row hη hd
  all_goals first
    | (rename_i hx he wb ih hΔ η hη n ν N hν
       exact (ih hΔ η hη n ν N hν).type_convert (hx.left_typed.result_wf hΔ) wb he hΔ hη)
    | (rename_i hf he wb ih hΔ η hη n ν N hν
       exact (ih hΔ η hη n ν N hν).type_convert
         (HasType.record (hf.left_typed hΔ) |>.result_wf hΔ) (.record wb) (.record he) hΔ hη)

/-- Every target typing derivation preserves arbitrary admissible heterogeneous
    valuations and related native environments. -/
theorem fundamental (ht : HasType Δ h e a) (hΔ : Context.Valid Δ) :
    OpenRel Δ h e e a := by
  let holes : Context → Typ → Expr → Expr → Typ → Prop := fun _ _ _ _ _ => False
  have hc : Compatible holes Δ h e e a := Compatible.same ht
  exact compatible_logical hc (by intros; contradiction) hΔ

/-- Every closed typed value relates to itself at every index. -/
theorem value_fundamental (hv : ValueType .empty v a) (n : Nat) :
    ValRel n a Valuation.empty v v := by
  have hr := (fundamental hv.2 .empty).values hv.1 hv.1 Valuation.empty_valid (n:=n)
  simpa only [Valuation.empty,Term.subst_id] using hr

/-- All typed observation contexts, including stored code and holes beneath
    static binders, respect the heterogeneous interpretation of closed programs. -/
theorem closed_contextual (he : HasType .empty h e a) (hE : HasType .empty h E a)
    (hr : ∀ n ν N, ValRel n h Valuation.empty ν N →
      ExprRel n a Valuation.empty (ν,e) (N,E)) : ContextualEq .empty h a e E := by
  intro θ hθ H g ν c C hg hν hc
  have hh := he.ambient_wf
  have ha := he.result_wf .empty
  have hc' : Compatible (HoleAt h a e E) .empty H c C g := by
    simpa only [hh.closed_subst θ,ha.closed_subst θ,he.closed_subst θ,hE.closed_subst θ] using hc
  have hcontext := compatible_logical hc' (closed_hole_logical he hE hr) .empty
  apply ground_adequacy (η:=Valuation.empty) (hg:=hg) (hν:=hν)
    (he:=hc'.left_typed) (hE:=hc'.right_typed)
  intro n
  have hout := hcontext Valuation.empty Valuation.empty_valid n ν ν (value_fundamental hν n)
  simpa only [Valuation.empty,Term.subst_id] using hout

end LeanSce.Target.Heterogeneous

/-! ## Representation Independence -/

namespace LeanSce.Target
open Heterogeneous

/-- T3: arbitrary admissible hidden representations are indistinguishable by
    the full target language whenever their public payloads are logically related. -/
theorem representation_independence : Goals.RepresentationIndependence := by
  intro body A₁ A₂ v₁ v₂ R wA₁ wA₂ _wpublic hR hp₁ hp₂ hrep
  let p := Candidate.type A₁ A₂ R
  have hp : p.Admissible .type := Candidate.type_admissible wA₁ wA₂ hR
  have hr := packages_related p hp hp₁ hp₂ hrep
  apply closed_contextual hp₁.2 hp₂.2
  intro n ν N hν
  exact (hr n).toExpr

end LeanSce.Target

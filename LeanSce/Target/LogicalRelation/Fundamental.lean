import LeanSce.Target.LogicalRelation.Contexts
import LeanSce.Target.LogicalRelation.Equality
import LeanSce.Target.LogicalRelation.Functions
import LeanSce.Target.Metatheory.Basic

/-!
# Target / LogicalRelation / Fundamental

Proofs and supporting constructions for fundamental.
-/

/-! ## Logical Relation Conversion -/

namespace LeanSce.Target.LogicalRelation

theorem ExprRel.type_convert (hr : ExprRel n a q r) (wa : WellFormed .empty a)
    (wb : WellFormed .empty b) (he : TyEq a b) : ExprRel n b q r :=
  ((equal_type n wa wb he).2 q r).mp hr

theorem OpenRel.convert (hr : OpenRel Δ h e E a) (wa : WellFormed Δ a)
    (wb : WellFormed Δ b) (he : TyEq a b) : OpenRel Δ h e E b := by
  intro θ hθ n ν N hν
  exact ((equal_type n (wa.subst hθ.respects) (wb.subst hθ.respects)
    (he.subst wa θ)).2 _ _).mp (hr θ hθ n ν N hν)

end LeanSce.Target.LogicalRelation

/-! ## Logical Relation Fundamental -/

namespace LeanSce.Target
open LogicalRelation

private theorem valid_all (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.all k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | all hf hg _ => exact .extend hΔ hf hg

private theorem valid_ex (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.ex k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | ex hf hg _ => exact .extend hΔ hf hg

/-- Every syntactic context rule preserves the logical relation. The hole
    hypothesis is the semantic premise for its declared local typing judgment. -/
theorem Compatible.logical (hc : Compatible R Δ h e E a)
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
  case query => rename_i hΔ θ hθ n ν N hν; exact ExprRel.query hν
  case unit => exact ValRel.unit.toExpr
  case int => exact ValRel.int.toExpr
  case bool => exact ValRel.bool.toExpr
  case string => exact ValRel.string.toExpr
  case pair =>
    rename_i hx hy ihx ihy hΔ θ hθ n ν N hν
    exact ExprRel.pair (ihx hΔ θ hθ n ν N hν) (ihy hΔ θ hθ n ν N hν)
  case fst =>
    rename_i hx ih hΔ θ hθ n ν N hν
    exact (ih hΔ θ hθ n ν N hν).fst hν.left.1 hν.right.1
  case snd =>
    rename_i hx ih hΔ θ hθ n ν N hν
    exact (ih hΔ θ hθ n ν N hν).snd hν.left.1 hν.right.1
  case box =>
    rename_i hx hb ihx ihb hΔ θ hθ n ν N hν
    exact ExprRel.box (ihx hΔ θ hθ n ν N hν) ((ihb hΔ).body hθ) hν.left.1 hν.right.1
  case lam =>
    rename_i wa hb ih hΔ θ hθ n ν N hν
    exact ExprRel.lam (wa.subst hθ.respects)
      (hb.left_typed.subst hΔ hθ.respects) (hb.right_typed.subst hΔ hθ.respects)
      ((ih hΔ).body hθ) hν
  case recfn =>
    rename_i wa wb hb ih hΔ θ hθ n ν N hν
    exact ExprRel.recfn (wa.subst hθ.respects) (wb.subst hθ.respects)
      (hb.left_typed.subst hΔ hθ.respects) (hb.right_typed.subst hΔ hθ.respects)
      ((ih hΔ).body hθ) hν
  case app =>
    rename_i hf hx ihf ihx hΔ θ hθ n ν N hν
    exact ExprRel.app (ihf hΔ θ hθ n ν N hν) (ihx hΔ θ hθ n ν N hν) hν.left.1 hν.right.1
  case inl =>
    rename_i wb hx ih hΔ θ hθ n ν N hν
    exact (ih hΔ θ hθ n ν N hν).inl (wb.subst hθ.respects)
  case inr =>
    rename_i wa hx ih hΔ θ hθ n ν N hν
    exact (ih hΔ θ hθ n ν N hν).inr (wa.subst hθ.respects)
  case case =>
    rename_i hx hl hr ihx ihl ihr hΔ θ hθ n ν N hν
    exact ExprRel.case (ihx hΔ θ hθ n ν N hν) hν
      ((ihl hΔ).body hθ) ((ihr hΔ).body hθ)
  case tag =>
    rename_i hx ih hΔ θ hθ n ν N hν
    exact (ih hΔ θ hθ n ν N hν).tag
  case record =>
    rename_i hf ih hΔ θ hθ n ν N hν
    exact ih hΔ θ hθ n ν N hν
  case find =>
    rename_i hx hu ih hΔ θ hθ n ν N hν
    exact (ih hΔ θ hθ n ν N hν).find (hu.subst θ) hν.left.1 hν.right.1
  case get =>
    rename_i hx hl ih hΔ θ hθ n ν N hν
    have hw := (hx.left_typed.result_wf hΔ).record_row
    exact (ih hΔ θ hθ n ν N hν).get (hw.lookup_subst hθ.respects hl) hν.left.1 hν.right.1
  case merge =>
    rename_i hx hy hd ihx ihy hΔ θ hθ n ν N hν
    exact (ihx hΔ θ hθ n ν N hν).merge (ihy hΔ θ hθ n ν N hν)
      (hd.subst hθ.respects) hν.left.1 hν.right.1
  case take =>
    rename_i Δ h x X r ls hx hn hl ih hΔ θ hθ n ν N hν
    have hw := (hx.left_typed.result_wf hΔ).record_row
    have hlabels : ∀ l ∈ ls, ∃ a, (r.subst θ).lookup l = some a := by
      intro l hmem
      obtain ⟨a,ha⟩ := hl l hmem
      exact ⟨a.subst θ,hw.lookup_subst hθ.respects ha⟩
    have hr := (ih hΔ θ hθ n ν N hν).take hlabels hν.left.1 hν.right.1
    exact hr.type_convert (.record ((hw.subst hθ.respects).select ls))
      (.record ((hw.select ls).subst hθ.respects)) (.record (hw.select_subst hθ.respects hl).symm)
  case drop =>
    rename_i Δ h x X r ls hx hn hl ih hΔ θ hθ n ν N hν
    have hw := (hx.left_typed.result_wf hΔ).record_row
    have hlabels : ∀ l ∈ ls, ∃ a, (r.subst θ).lookup l = some a := by
      intro l hmem
      obtain ⟨a,ha⟩ := hl l hmem
      exact ⟨a.subst θ,hw.lookup_subst hθ.respects ha⟩
    simpa only [Term.subst,Ty.subst,hw.drop_subst hθ.respects hl] using
      (ih hΔ θ hθ n ν N hν).drop hlabels hν.left.1 hν.right.1
  case relabel =>
    rename_i Δ h x X r l a k hx hl hn hd ih hΔ θ hθ n ν N hν
    have hw := (hx.left_typed.result_wf hΔ).record_row
    have hdθ := hd.subst hθ.respects
    rw [hw.drop_subst hθ.respects (by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact ⟨a,hl⟩)] at hdθ
    simpa only [Term.subst,Ty.subst,hw.relabel_subst hθ.respects hl] using
      (ih hΔ θ hθ n ν N hν).relabel (hw.lookup_subst hθ.respects hl) hn hdθ hν.left.1 hν.right.1
  case nil => exact ValRel.record_nil.toExpr
  case tapp =>
    rename_i Δ h x X k gs a u hx hk hu hg ih hΔ θ hθ n ν N hν
    have hkθ : (u.subst θ).kind = k := by simpa using hk
    have hguards : Entails .empty ((gs.subst θ.lift).open (u.subst θ)) := by
      simpa only [Ty.subst_open] using hg.subst hθ.respects
    simpa only [Term.subst,Ty.subst_open] using
      (ih hΔ θ hθ n ν N hν).tapp hkθ (hu.subst hθ.respects) hguards hν.left.1 hν.right.1
  case pack =>
    rename_i Δ k gs a u h x X hw hk hu hg hx ih hΔ θ hθ n ν N hν
    have hkθ : (u.subst θ).kind = k := by simpa using hk
    have hguards : Entails .empty ((gs.subst θ.lift).open (u.subst θ)) := by
      simpa only [Ty.subst_open] using hg.subst hθ.respects
    have hval := ExprRel.pack (hw.subst hθ.respects) hkθ (hu.subst hθ.respects) hguards
      (by simpa only [Ty.subst_open] using ih hΔ θ hθ n ν N hν)
    exact hval
  case unfold =>
    rename_i hx ih hΔ θ hθ n ν N hν
    simpa only [Term.subst,Ty.subst_open,Ty.subst,Arg.subst] using
      (ih hΔ θ hθ n ν N hν).unfold hν.left.1 hν.right.1
  case add =>
    rename_i hx hy ihx ihy hΔ θ hθ n ν N hν
    exact ExprRel.add (ihx hΔ θ hθ n ν N hν) (ihy hΔ θ hθ n ν N hν) hν.left.1 hν.right.1
  case eqInt =>
    rename_i hx hy ihx ihy hΔ θ hθ n ν N hν
    exact ExprRel.eqInt (ihx hΔ θ hθ n ν N hν) (ihy hΔ θ hθ n ν N hν) hν.left.1 hν.right.1
  case showInt =>
    rename_i hx ih hΔ θ hθ n ν N hν
    exact ExprRel.showInt (ih hΔ θ hθ n ν N hν) hν.left.1 hν.right.1
  case concat =>
    rename_i hx hy ihx ihy hΔ θ hθ n ν N hν
    exact ExprRel.concat (ihx hΔ θ hθ n ν N hν) (ihy hΔ θ hθ n ν N hν) hν.left.1 hν.right.1
  case ite =>
    rename_i hc hx hy ihc ihx ihy hΔ θ hθ n ν N hν
    exact ExprRel.ite (ihc hΔ θ hθ n ν N hν) (ihx hΔ θ hθ n ν N hν)
      (ihy hΔ θ hθ n ν N hν) hν.left.1 hν.right.1
  case clo =>
    rename_i hh wa hv hV hcap hb ihcap ihb hΔ θ hθ n ν N hν
    exact (ValRel.clo (wa.subst hθ.respects)
      (hb.left_typed.subst hΔ hθ.respects) (hb.right_typed.subst hΔ hθ.respects)
      ((ihb hΔ).body hθ) ((ihcap hΔ).values hv hV hθ)).toExpr
  case rclo =>
    rename_i hh wa wb hv hV hcap hb ihcap ihb hΔ θ hθ n ν N hν
    exact (ValRel.rclo (wa.subst hθ.respects) (wb.subst hθ.respects)
      (hb.left_typed.subst hΔ hθ.respects) (hb.right_typed.subst hΔ hθ.respects)
      ((ihb hΔ).body hθ) ((ihcap hΔ).values hv hV hθ)).toExpr
  case tlam =>
    rename_i Δ k gs a h x X hw hh hb ih hΔ θ hθ n ν N hν
    have hvalid := valid_all hΔ hw
    cases hw with
    | all hf wg wa =>
      have hw : WellFormed Δ (.all k gs a) := .all hf wg wa
      apply ExprRel.tlam (hw.subst hθ.respects)
      · simpa only [Ty.subst_lift_weaken] using hb.left_typed.subst hvalid (hθ.respects.lift hf)
      · simpa only [Ty.subst_lift_weaken] using hb.right_typed.subst hvalid (hθ.respects.lift hf)
      · exact (ih hvalid).polybody hθ hf
      · exact hν
  case unpack =>
    rename_i hx wb hb ihx ihb hΔ θ hθ n ν N hν
    have hw := hx.left_typed.result_wf hΔ
    have hvalid := valid_ex hΔ hw
    cases hw with
    | ex hf wg wa =>
      exact ExprRel.unpack (ihx hΔ θ hθ n ν N hν) hν ((ihb hvalid).unpack_body hθ hf)
  case fold =>
    rename_i hw hx ih hΔ θ hθ n ν N hν
    have hval := ExprRel.fold (hw.subst hθ.respects)
      (by simpa only [Ty.subst_open,Ty.subst,Arg.subst] using ih hΔ θ hθ n ν N hν)
    exact hval
  case tclo =>
    rename_i Δ h k gs a cap CAP env x X hh hw hv hV hcap hb ihcap ihb hΔ θ hθ n ν N hν
    have hvalid := valid_all hΔ hw
    cases hw with
    | all hf wg wa =>
      have hw : WellFormed Δ (.all k gs a) := .all hf wg wa
      apply ValRel.toExpr
      apply ValRel.tclo (hw.subst hθ.respects)
      · simpa only [Ty.subst_lift_weaken] using hb.left_typed.subst hvalid (hθ.respects.lift hf)
      · simpa only [Ty.subst_lift_weaken] using hb.right_typed.subst hvalid (hθ.respects.lift hf)
      · exact (ihb hvalid).polybody hθ hf
      · exact (ihcap hΔ).values hv hV hθ
  case value =>
    rename_i hv hV ht hh ih hΔ θ hθ n ν N hν
    exact ((ih hΔ).values hv hV hθ).toExpr
  case cons =>
    rename_i hx hf hd ihx ihf hΔ θ hθ n ν N hν
    exact ExprRel.record_cons (ihx hΔ θ hθ n ν N hν) (ihf hΔ θ hθ n ν N hν)
      (hd.subst hθ.respects)
  all_goals first
    | (rename_i hx he wb ih hΔ θ hθ n ν N hν
       exact ((ih hΔ).convert (hx.left_typed.result_wf hΔ) wb he) θ hθ n ν N hν)
    | (rename_i hf he wb ih hΔ θ hθ n ν N hν
       exact ((ih hΔ).convert (HasType.record (hf.left_typed hΔ) |>.result_wf hΔ)
         (.record wb) (.record he)) θ hθ n ν N hν)

/-- Fundamental theorem for every target term, under satisfying closing static
    substitutions and related native environments. -/
theorem HasType.logical (ht : HasType Δ h e a) (hΔ : Context.Valid Δ) :
    OpenRel Δ h e e a := by
  let holes : Context → Typ → Expr → Expr → Typ → Prop := fun _ _ _ _ _ => False
  have hc : Compatible holes Δ h e e a := Compatible.same ht
  exact hc.logical (by intros; contradiction) hΔ

/-- Closed typed values relate to themselves at every observation index. -/
theorem ValueType.logical (hv : ValueType .empty v a) (n : Nat) : ValRel n a v v := by
  have hr : ValRel n (a.subst Subst.id) (v.subst Subst.id) (v.subst Subst.id) :=
    (hv.2.logical .empty).values hv.1 hv.1 (Closing.empty Subst.id)
  simpa only [Ty.subst_id,Term.subst_id] using hr

namespace LogicalRelation

/-- Logical compatibility implies actual contextual equivalence. This closes
    over all typed contexts, not only a selected list of evaluation examples. -/
theorem OpenRel.contextual (hr : OpenRel Δ h e E a)
    (he : HasType Δ h e a) (hE : HasType Δ h E a) (hΔ : Context.Valid Δ) :
    ContextualEq Δ h a e E := by
  intro θ hθ H g ν c C hg hν hc
  have hl := he.subst hΔ hθ.respects
  have hright := hE.subst hΔ hθ.respects
  have hholes := closed_hole_logical hl hright (hr θ hθ)
  have hcontext := hc.logical hholes .empty
  apply ground_adequacy (hg := hg) (hν := hν) (he := hc.left_typed) (hE := hc.right_typed)
  intro n
  have hout := hcontext Subst.id (Closing.empty Subst.id) n ν ν
    (by simpa only [Ty.subst_id] using hν.logical n)
  simpa only [Ty.subst_id,Term.subst_id] using hout

end LogicalRelation

end LeanSce.Target

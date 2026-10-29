import LeanSce.Target.Definitions.Semantics
import LeanSce.Target.Definitions.Statics
import LeanSce.Target.Definitions.Typing
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Typing
import LeanSce.Target.Metatheory.Values

/-!
# Target / Metatheory / Safety

Proofs and supporting constructions for safety.
-/

/-! ## Goals -/

/-! Paper statements as propositions, never axioms or proof assumptions.
    Safety and the adapter results below are proved in their corresponding
    modules; determinism is `step_deterministic` in Metatheory.Basic. Keeping statements
    here avoids importing their proofs into syntax. -/
namespace LeanSce.Target.Goals

/-- T1.1, for the full closed calculus. -/
def Preservation : Prop :=
  ∀ (ν e e' : Expr) (h a : Typ), ValueType .empty ν h → HasType .empty h e a →
    Step ν e e' → HasType .empty h e' a

/-- T1.2, including polymorphism, packages, records and recursion. -/
def Progress : Prop :=
  ∀ (ν e : Expr) (h a : Typ), ValueType .empty ν h → HasType .empty h e a →
    Value e ∨ ∃ e', Step ν e e'

/-- T2.1: every canonical adapter is typed in any well-formed caller ambient. -/
def AdapterTyping : Prop :=
  ∀ (Δ : Context) (a b h : Typ) (c : Expr), Context.Valid Δ → Adapts Δ a b c →
    WellFormed Δ h → HasType Δ h c (.arr a b)

/-- T2.2: constructing an adapted value terminates, even for function-valued fields. -/
def AdapterTermination : Prop :=
  ∀ (Δ : Context) (a b h : Typ) (c ν v : Expr) (θ : Subst),
    Context.Valid Δ → Adapts Δ a b c → WellFormed Δ h → Closing θ Δ →
    ValueType .empty ν (h.subst θ) → ValueType .empty v (a.subst θ) →
    ∃ w, Terminates ν (.app (c.subst θ) v) w ∧ ValueType .empty w (b.subst θ)

/-- T2.3: record results have precisely the instantiated advertised domain. -/
def AdapterExactShape : Prop :=
  ∀ (Δ : Context) (a h : Typ) (r : Row) (c ν v w : Expr) (θ : Subst),
    Context.Valid Δ → Adapts Δ a (.record r) c → WellFormed Δ h → Closing θ Δ →
    ValueType .empty ν (h.subst θ) → ValueType .empty v (a.subst θ) →
    Terminates ν (.app (c.subst θ) v) w →
    ∃ fs, w = .record fs ∧ ∀ l, l ∈ fs.labels ↔ l ∈ (r.subst θ).knownLabels

/-- T2.4: adaptation preserves and reflects divergence of its input. -/
def AdapterDivergence : Prop :=
  ∀ (Δ : Context) (a b h : Typ) (c ν e : Expr) (θ : Subst),
    Context.Valid Δ → Adapts Δ a b c → HasType Δ h e a → Closing θ Δ →
    ValueType .empty ν (h.subst θ) →
    (Diverges ν (.app (c.subst θ) (e.subst θ)) ↔ Diverges ν (e.subst θ))

end LeanSce.Target.Goals

/-! ## Progress -/

namespace LeanSce.Target

private theorem canStep_map {a : Term s} (ha : CanStep ν a) (f : Term s → Term t)
    (hv : Value a → Value (f a)) (hs : step ν (f a) = (step ν a).map f) :
    CanStep ν (f a) := by
  rcases ha with ha | ⟨a',ha⟩
  · exact .inl (hv ha)
  · exact .inr ⟨f a', by rw [hs,ha]; rfl⟩

private theorem canStep_prim (ha : CanStep ν args)
    (hv : Value args → ∃ v, evalPrim p args = some v) : CanStep ν (.prim p args) := by
  rcases ha with ha | ⟨args',ha⟩
  · obtain ⟨v,heval⟩ := hv ha
    exact .inr ⟨v, by simp [step_prim_eq,(show _ = true from ha),heval]⟩
  · exact .inr ⟨.prim p args', by simp [step_prim_eq,step_isValue_false ha,ha] <;> first | rfl | exact ⟨rfl,rfl⟩⟩

/-- Progress for the full target in any valid static context. Type/row variables
    need not be closed: their opaque values cannot acquire an ill-shaped type. -/
theorem HasType.canStep (ht : HasType Δ h e a) :
    Context.Valid Δ → ∀ ν, ValueType Δ ν h → CanStep ν e := by
  apply HasType.rec
    (motive_1 := fun Δ h e _ _ => Context.Valid Δ → ∀ ν, ValueType Δ ν h → CanStep ν e)
    (motive_2 := fun Δ h fs _ _ => Context.Valid Δ → ∀ ν, ValueType Δ ν h → CanStep ν fs)
    (t := ht)
  all_goals intros
  all_goals intros
  case query =>
    rename_i _ hΔ ν hν
    exact .inr ⟨ν,rfl⟩
  case unit => exact .inl rfl
  case int => exact .inl rfl
  case bool => exact .inl rfl
  case string => exact .inl rfl
  case pair =>
    rename_i _ _ ihx ihy hΔ ν hν
    exact canStep_pair (ihx hΔ ν hν) (ihy hΔ ν hν)
  case fst =>
    rename_i hx ih hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨x,y,rfl⟩ := hx.value_shape hv
      exact .inr ⟨x, by simp [Value] at hv; simp [step_fst_eq,(show _ = true from hv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.fst x', by simp [step_fst_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case snd =>
    rename_i hx ih hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨x,y,rfl⟩ := hx.value_shape hv
      exact .inr ⟨y, by simp [Value] at hv; simp [step_snd_eq,(show _ = true from hv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.snd x', by simp [step_snd_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case box =>
    rename_i ha hb iha ihb hΔ ν hν
    rcases iha hΔ ν hν with hav | ⟨a',hs⟩
    · rcases ihb hΔ _ (valueType_of_typed_value ha hav) with hbv | ⟨b',hs⟩
      · exact .inr ⟨_,by simp [step_box_eq,(show _ = true from hav),(show _ = true from hbv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
      · exact .inr ⟨.box _ b',by simp [step_box_eq,(show _ = true from hav),step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.box a' _,by simp [step_box_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case lam =>
    rename_i _ _ _ hΔ ν hν
    exact .inr ⟨_,rfl⟩
  case recfn =>
    rename_i _ _ _ _ hΔ ν hν
    exact .inr ⟨_,rfl⟩
  case app =>
    rename_i hf hx ihf ihx hΔ ν hν
    rcases ihf hΔ ν hν with hfv | ⟨f',hs⟩
    · rcases ihx hΔ ν hν with hxv | ⟨x',hs⟩
      · rcases hf.value_shape hfv with ⟨cap,arg,body,rfl⟩ | ⟨cap,arg,result,body,rfl⟩
        · exact .inr ⟨_,by simp [Value] at hfv hxv; simp [step_app_eq,(show _ = true from hfv),(show _ = true from hxv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
        · exact .inr ⟨_,by simp [Value] at hfv hxv; simp [step_app_eq,(show _ = true from hfv),(show _ = true from hxv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
      · exact .inr ⟨.app _ x',by simp [step_app_eq,(show _ = true from hfv),step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.app f' _,by simp [step_app_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case inl =>
    rename_i _ _ ih hΔ ν hν
    exact canStep_map (ih hΔ ν hν) _ (fun hv => hv) step_inl_eq
  case inr =>
    rename_i _ _ ih hΔ ν hν
    exact canStep_map (ih hΔ ν hν) _ (fun hv => hv) step_inr_eq
  case case =>
    rename_i hx _ _ ihx _ _ hΔ ν hν
    rcases ihx hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨t,v,(rfl | rfl)⟩ := hx.value_shape hv
      · exact .inr ⟨_,by simp [Value] at hv; simp [step_case_eq,(show _ = true from hv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
      · exact .inr ⟨_,by simp [Value] at hv; simp [step_case_eq,(show _ = true from hv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.case x' _ _,by simp [step_case_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case tag =>
    rename_i _ ih hΔ ν hν
    exact canStep_map (ih hΔ ν hν) _ (fun hv => hv) step_tag_eq
  case find =>
    rename_i hx hu ih hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨v,hs,_⟩ := findTags_unique hx hv hu
        (hu.wellFormed_result (hx.result_wf hΔ)) hΔ
      exact .inr ⟨v,by simp [step_find_eq,(show _ = true from hv),hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.find _ x',by simp [step_find_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case record =>
    rename_i _ ih hΔ ν hν
    exact canStep_map (ih hΔ ν hν) _ (fun hv => hv) step_record_eq
  case get =>
    rename_i hx hl ih hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨fs,rfl⟩ := hx.value_shape hv
      have hf := hx.value_record_inv hv (hx.result_wf hΔ).record_row
      obtain ⟨v,hs,_⟩ := hf.lookup hΔ hl
      exact .inr ⟨v,by simp [step_get_eq,(show _ = true from hv),hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.get x' _,by simp [step_get_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case merge =>
    rename_i hx hy hd ihx ihy hΔ ν hν
    rcases ihx hΔ ν hν with hxv | ⟨x',hs⟩
    · rcases ihy hΔ ν hν with hyv | ⟨y',hs⟩
      · obtain ⟨fs,rfl⟩ := hx.value_shape hxv
        obtain ⟨gs,rfl⟩ := hy.value_shape hyv
        have hf := hx.value_record_inv hxv (hx.result_wf hΔ).record_row
        have hg := hy.value_record_inv hyv (hy.result_wf hΔ).record_row
        exact .inr ⟨_,by
          simp only [step_merge_eq,(show _ = true from hxv),(show _ = true from hyv),
            Bool.not_true,Bool.false_eq_true,↓reduceIte,hf.merge_check hg hd]
          rfl⟩
      · exact .inr ⟨.merge _ y',by simp [step_merge_eq,(show _ = true from hxv),step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.merge x' _,by simp [step_merge_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case take =>
    rename_i hx _ hl ih hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨fs,rfl⟩ := hx.value_shape hv
      have hf := hx.value_record_inv hv (hx.result_wf hΔ).record_row
      exact .inr ⟨_,by simp [step_take_eq,(show _ = true from hv),hf.selection_check _ hl] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.take _ x',by simp [step_take_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case drop =>
    rename_i hx _ hl ih hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨fs,rfl⟩ := hx.value_shape hv
      have hf := hx.value_record_inv hv (hx.result_wf hΔ).record_row
      exact .inr ⟨_,by simp [step_drop_eq,(show _ = true from hv),hf.selection_check _ hl] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.drop _ x',by simp [step_drop_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case relabel =>
    rename_i hx hl hne hd ih hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨fs,rfl⟩ := hx.value_shape hv
      have hf := hx.value_record_inv hv (hx.result_wf hΔ).record_row
      exact .inr ⟨_,by
        simp only [step_relabel_eq,(show _ = true from hv),Bool.not_true,
          Bool.false_eq_true,↓reduceIte,hf.relabel_check hl hne hd]
        rfl⟩
    · exact .inr ⟨.relabel _ _ x',by simp [step_relabel_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case tlam =>
    rename_i _ _ _ _ hΔ ν hν
    exact .inr ⟨_,rfl⟩
  case tapp =>
    rename_i hx _ _ _ ih hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨cap,k,gs,body,rfl⟩ := hx.value_shape hv
      exact .inr ⟨_,by simp [step_tapp_eq,(show _ = true from hv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.tapp x' _,by simp [step_tapp_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case pack =>
    rename_i _ _ _ _ _ ih hΔ ν hν
    exact canStep_map (ih hΔ ν hν) _ (fun hv => hv) step_pack_eq
  case unpack =>
    rename_i hx _ _ ih _ hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨u,t,v,rfl⟩ := hx.value_shape hv
      exact .inr ⟨_,by simp [step_unpack_eq,(show _ = true from hv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.unpack x' _,by simp [step_unpack_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case fold =>
    rename_i _ _ ih hΔ ν hν
    exact canStep_map (ih hΔ ν hν) _ (fun hv => hv) step_fold_eq
  case unfold =>
    rename_i hx ih hΔ ν hν
    rcases ih hΔ ν hν with hv | ⟨x',hs⟩
    · obtain ⟨t,v,rfl⟩ := hx.value_shape hv
      exact .inr ⟨v,by simp [step_unfold_eq,(show _ = true from hv)] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
    · exact .inr ⟨.unfold x',by simp [step_unfold_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case add =>
    rename_i hx hy ihx ihy hΔ ν hν
    apply canStep_prim (canStep_cons (ihx hΔ ν hν) (canStep_cons (ihy hΔ ν hν) (.inl (show Value (Term.nil) from rfl))))
    intro hv
    simp only [Value,Term.isValue,Bool.and_eq_true,Bool.and_true] at hv
    obtain ⟨x,rfl⟩ := hx.value_shape hv.1
    obtain ⟨y,rfl⟩ := hy.value_shape hv.2
    exact ⟨_,rfl⟩
  case eqInt =>
    rename_i hx hy ihx ihy hΔ ν hν
    apply canStep_prim (canStep_cons (ihx hΔ ν hν) (canStep_cons (ihy hΔ ν hν) (.inl (show Value (Term.nil) from rfl))))
    intro hv
    simp only [Value,Term.isValue,Bool.and_eq_true,Bool.and_true] at hv
    obtain ⟨x,rfl⟩ := hx.value_shape hv.1
    obtain ⟨y,rfl⟩ := hy.value_shape hv.2
    exact ⟨_,rfl⟩
  case showInt =>
    rename_i hx ih hΔ ν hν
    apply canStep_prim (canStep_cons (ih hΔ ν hν) (.inl (show Value (Term.nil) from rfl)))
    intro hv
    simp only [Value,Term.isValue,Bool.and_true] at hv
    obtain ⟨x,rfl⟩ := hx.value_shape hv
    exact ⟨_,rfl⟩
  case concat =>
    rename_i hx hy ihx ihy hΔ ν hν
    apply canStep_prim (canStep_cons (ihx hΔ ν hν) (canStep_cons (ihy hΔ ν hν) (.inl (show Value (Term.nil) from rfl))))
    intro hv
    simp only [Value,Term.isValue,Bool.and_eq_true,Bool.and_true] at hv
    obtain ⟨x,rfl⟩ := hx.value_shape hv.1
    obtain ⟨y,rfl⟩ := hy.value_shape hv.2
    exact ⟨_,rfl⟩
  case ite =>
    rename_i hc _ _ ihc _ _ hΔ ν hν
    rcases ihc hΔ ν hν with hv | ⟨c',hs⟩
    · obtain ⟨b,rfl⟩ := hc.value_shape hv
      cases b <;> exact .inr ⟨_,rfl⟩
    · exact .inr ⟨.ite c' _ _,by simp [step_ite_eq,step_isValue_false hs,hs] <;> first | rfl | exact ⟨rfl,rfl⟩⟩
  case clo =>
    rename_i _ _ hv _ _ _ _ hΔ ν hν
    exact .inl hv
  case rclo =>
    rename_i _ _ _ hv _ _ _ _ hΔ ν hν
    exact .inl hv
  case tclo =>
    rename_i _ _ hv _ _ _ _ hΔ ν hν
    exact .inl hv
  case value =>
    rename_i hv _ _ _ hΔ ν hν
    exact .inl hv
  case nil => exact .inl rfl
  case cons =>
    rename_i _ _ _ ihx ihf hΔ ν hν
    exact canStep_cons (ihx hΔ ν hν) (ihf hΔ ν hν)
  all_goals
    rename_i _ _ _ ih hΔ ν hν
    exact ih hΔ ν hν

/-- T1.2: every well-typed closed configuration is a value or can reduce. -/
theorem progress (hν : ValueType .empty ν h) (ht : HasType .empty h e a) :
    Value e ∨ ∃ e', Step ν e e' := by
  rcases ht.canStep .empty ν hν with hv | ⟨e',hs⟩
  · exact .inl hv
  · exact .inr ⟨e',hν.1,hs⟩

end LeanSce.Target

/-! ## Preservation -/

namespace LeanSce.Target

/-- Preservation for every valid static context. The paper's closed statement
    is obtained by specializing the context to empty. -/
theorem HasType.preservation (ht : HasType Δ h e a) :
    Context.Valid Δ → ∀ ν, ValueType Δ ν h → ∀ e', step ν e = some e' →
      HasType Δ h e' a := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ => Context.Valid Δ → ∀ ν, ValueType Δ ν h →
      ∀ e', step ν e = some e' → HasType Δ h e' a)
    (motive_2 := fun Δ h fs r _ => Context.Valid Δ → ∀ ν, ValueType Δ ν h →
      ∀ fs', step ν fs = some fs' → FieldsType Δ h fs' r)
    (t := ht)
  all_goals intros
  all_goals intros
  case query =>
    rename_i hw hΔ ν hν e' hs
    have he : ν = e' := Option.some.inj hs
    subst e'
    exact hν.inclusion hw
  case unit => rename_i _ _ _ _ hs; cases hs
  case int => rename_i _ _ _ _ hs; cases hs
  case bool => rename_i _ _ _ _ hs; cases hs
  case string => rename_i _ _ _ _ hs; cases hs
  case pair =>
    rename_i Δ h x a y b hx hy ihx ihy hΔ ν hν e' hs
    cases hvx : x.isValue with
    | false =>
      rw [step_pair_left hvx] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .pair (ihx hΔ ν hν _ hx') hy
    | true =>
      cases hvy : y.isValue with
      | false =>
        rw [step_pair_right hvx hvy] at hs
        obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.mp hs
        exact .pair hx (ihy hΔ ν hν _ hy')
      | true =>
        rw [value_no_step (e := .pair x y) (Bool.and_eq_true_iff.mpr ⟨hvx,hvy⟩)] at hs
        cases hs
  case fst =>
    rename_i Δ h x a b hx ih hΔ ν hν e' hs
    rw [step_fst_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .fst (ih hΔ ν hν _ hx')
    | true =>
      obtain ⟨x₁,x₂,rfl⟩ := hx.value_shape hv
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
      subst e'
      exact fst_activation hx hv hΔ
  case snd =>
    rename_i Δ h x a b hx ih hΔ ν hν e' hs
    rw [step_snd_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .snd (ih hΔ ν hν _ hx')
    | true =>
      obtain ⟨x₁,x₂,rfl⟩ := hx.value_shape hv
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
      subst e'
      exact snd_activation hx hv hΔ
  case box =>
    rename_i Δ h x env body a hx hb ihx ihb hΔ ν hν e' hs
    rw [step_box_eq] at hs
    cases hvx : x.isValue with
    | false =>
      simp only [hvx, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .box (ihx hΔ ν hν _ hx') hb
    | true =>
      simp only [hvx, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
      cases hvb : body.isValue with
      | false =>
        simp only [hvb, Bool.false_eq_true, ↓reduceIte] at hs
        obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hs
        exact .box hx (ihb hΔ x (valueType_of_typed_value hx hvx) _ hb')
      | true =>
        simp only [hvb, ↓reduceIte, Option.some.injEq] at hs
        subst e'
        exact hb.value_reambient hvb _ hx.ambient_wf
  case lam =>
    rename_i Δ arg h body a wa hb ih hΔ ν hν e' hs
    have he : Term.clo ν arg body = e' := Option.some.inj hs
    subst e'
    exact .clo hb.ambient_wf.prod_left wa hν.1 hν.2 hb
  case recfn =>
    rename_i Δ arg result h body wa wb hb ih hΔ ν hν e' hs
    have he : Term.rclo ν arg result body = e' := Option.some.inj hs
    subst e'
    exact .rclo hb.ambient_wf.prod_left.prod_left wa wb hν.1 hν.2 hb
  case app =>
    rename_i Δ h f a b x hf hx ihf ihx hΔ ν hν e' hs
    rw [step_app_eq] at hs
    cases hvf : f.isValue with
    | false =>
      simp only [hvf, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .app (ihf hΔ ν hν _ hf') hx
    | true =>
      simp only [hvf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
      cases hvx : x.isValue with
      | false =>
        simp only [hvx, Bool.not_false, ↓reduceIte] at hs
        obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
        exact .app hf (ihx hΔ ν hν _ hx')
      | true =>
        simp only [hvx, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
        rcases hf.value_shape hvf with ⟨cap,arg,body,rfl⟩ | ⟨cap,arg,result,body,rfl⟩
        · cases hs
          exact app_clo_activation hf hvf hx hΔ
        · cases hs
          exact app_rclo_activation hf hvf hx hΔ
  case inl =>
    rename_i wb hx ih hΔ ν hν e' hs
    rw [step_inl_eq] at hs
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
    exact .inl wb (ih hΔ ν hν _ hx')
  case inr =>
    rename_i wa hx ih hΔ ν hν e' hs
    rw [step_inr_eq] at hs
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
    exact .inr wa (ih hΔ ν hν _ hx')
  case case =>
    rename_i Δ h x a b left c right hx hl hr ihx ihl ihr hΔ ν hν e' hs
    rw [step_case_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .case (ihx hΔ ν hν _ hx') hl hr
    | true =>
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
      obtain ⟨t,v,he | he⟩ := hx.value_shape hv
      · subst x
        cases hs
        exact case_inl_activation hx hv hν hl hΔ
      · subst x
        cases hs
        exact case_inr_activation hx hv hν hr hΔ
  case tag =>
    rename_i hx ih hΔ ν hν e' hs
    rw [step_tag_eq] at hs
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
    exact .tag (ih hΔ ν hν _ hx')
  case find =>
    rename_i Δ h x a l b hx hu ih hΔ ν hν e' hs
    rw [step_find_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .find (ih hΔ ν hν _ hx') hu
    | true =>
      obtain ⟨v,hvfind,hvt⟩ := findTags_unique hx hv hu (hu.wellFormed_result (hx.result_wf hΔ)) hΔ
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hvfind, Option.some.injEq] at hs
      subst e'
      exact hvt.inclusion hx.ambient_wf
  case record =>
    rename_i hf ih hΔ ν hν e' hs
    rw [step_record_eq] at hs
    obtain ⟨fs', hfs', rfl⟩ := Option.map_eq_some_iff.mp hs
    exact .record (ih hΔ ν hν _ hfs')
  case get =>
    rename_i Δ h x r l a hx hl ih hΔ ν hν e' hs
    rw [step_get_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .get (ih hΔ ν hν _ hx') hl
    | true =>
      obtain ⟨fs,rfl⟩ := hx.value_shape hv
      have hf := hx.value_record_inv hv (hx.result_wf hΔ).record_row
      obtain ⟨v,hlv,hvt⟩ := hf.lookup hΔ hl
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlv, Option.some.injEq] at hs
      subst e'
      exact hvt.value_reambient (Term.lookup_value fs hv hlv) _ hx.ambient_wf
  case merge =>
    rename_i Δ h x r y s hx hy hd ihx ihy hΔ ν hν e' hs
    rw [step_merge_eq] at hs
    cases hvx : x.isValue with
    | false =>
      simp only [hvx, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .merge (ihx hΔ ν hν _ hx') hy hd
    | true =>
      simp only [hvx, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
      cases hvy : y.isValue with
      | false =>
        simp only [hvy, Bool.not_false, ↓reduceIte] at hs
        obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.mp hs
        exact .merge hx (ihy hΔ ν hν _ hy') hd
      | true =>
        obtain ⟨fs,rfl⟩ := hx.value_shape hvx
        obtain ⟨gs,rfl⟩ := hy.value_shape hvy
        have hf := hx.value_record_inv hvx (hx.result_wf hΔ).record_row
        have hg := hy.value_record_inv hvy (hy.result_wf hΔ).record_row
        simp only [hvy, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hf.merge_check hg hd,
          Option.some.injEq] at hs
        subst e'
        exact .record ((hf.append hΔ hg hd).value_reambient
          (Term.append_value fs hvx hvy) _ hx.ambient_wf)
  case take =>
    rename_i Δ h x r ls hx hn hl ih hΔ ν hν e' hs
    rw [step_take_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .take (ih hΔ ν hν _ hx') hn hl
    | true =>
      obtain ⟨fs,rfl⟩ := hx.value_shape hv
      have hf := hx.value_record_inv hv (hx.result_wf hΔ).record_row
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        hf.selection_check ls hl, Option.some.injEq] at hs
      subst e'
      exact .record ((hf.select hΔ ls).value_reambient
        (Term.filter_value fs hv) _ hx.ambient_wf)
  case drop =>
    rename_i Δ h x r ls hx hn hl ih hΔ ν hν e' hs
    rw [step_drop_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .drop (ih hΔ ν hν _ hx') hn hl
    | true =>
      obtain ⟨fs,rfl⟩ := hx.value_shape hv
      have hf := hx.value_record_inv hv (hx.result_wf hΔ).record_row
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        hf.selection_check ls hl, Option.some.injEq] at hs
      subst e'
      exact .record ((hf.drop hΔ ls).value_reambient
        (Term.filter_value fs hv) _ hx.ambient_wf)
  case relabel =>
    rename_i Δ h x r old a new hx hl hn hd ih hΔ ν hν e' hs
    rw [step_relabel_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .relabel (ih hΔ ν hν _ hx') hl hn hd
    | true =>
      obtain ⟨fs,rfl⟩ := hx.value_shape hv
      have hf := hx.value_record_inv hv (hx.result_wf hΔ).record_row
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        hf.relabel_check hl hn hd, Option.some.injEq] at hs
      subst e'
      exact .record ((hf.relabel hΔ hd).value_reambient
        (Term.renameFields_value fs hv) _ hx.ambient_wf)
  case tapp =>
    rename_i Δ h x k gs a u hx hk hu hg ih hΔ ν hν e' hs
    rw [step_tapp_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .tapp (ih hΔ ν hν _ hx') hk hu hg
    | true =>
      obtain ⟨cap,k₀,gs₀,body,rfl⟩ := hx.value_shape hv
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
      subst e'
      exact tapp_tclo_typed hΔ hx hv hk hu hg
  case pack =>
    rename_i hw hk hu hg hx ih hΔ ν hν e' hs
    rw [step_pack_eq] at hs
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
    exact .pack hw hk hu hg (ih hΔ ν hν _ hx')
  case unpack =>
    rename_i Δ h x k gs a b body hx wb hb ihx ihb hΔ ν hν e' hs
    rw [step_unpack_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .unpack (ihx hΔ ν hν _ hx') wb hb
    | true =>
      obtain ⟨u,t,v,rfl⟩ := hx.value_shape hv
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
      subst e'
      exact unpack_pack_typed hΔ hx hv hν wb hb
  case fold =>
    rename_i hw hx ih hΔ ν hν e' hs
    rw [step_fold_eq] at hs
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
    exact .fold hw (ih hΔ ν hν _ hx')
  case unfold =>
    rename_i Δ h x a hx ih hΔ ν hν e' hs
    rw [step_unfold_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .unfold (ih hΔ ν hν _ hx')
    | true =>
      obtain ⟨t,v,rfl⟩ := hx.value_shape hv
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
      subst e'
      exact fold_payload_typed hΔ hx hv
  case ite =>
    rename_i Δ h cond x a y hc hx hy ihc ihx ihy hΔ ν hν e' hs
    rw [step_ite_eq] at hs
    cases hv : cond.isValue with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at hs
      obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .ite (ihc hΔ ν hν _ hc') hx hy
    | true =>
      obtain ⟨b,rfl⟩ := hc.value_shape hv
      cases b <;> simp only [Term.isValue, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, Option.some.injEq] at hs <;> subst e'
      · exact hy
      · exact hx
  case add =>
    rename_i hx hy ihx ihy hΔ ν hν e' hs
    exact prim_add_preservation hx hy (ihx hΔ ν hν) (ihy hΔ ν hν) hs
  case eqInt =>
    rename_i hx hy ihx ihy hΔ ν hν e' hs
    exact prim_eqInt_preservation hx hy (ihx hΔ ν hν) (ihy hΔ ν hν) hs
  case concat =>
    rename_i hx hy ihx ihy hΔ ν hν e' hs
    exact prim_concat_preservation hx hy (ihx hΔ ν hν) (ihy hΔ ν hν) hs
  case showInt =>
    rename_i hx ih hΔ ν hν e' hs
    exact prim_showInt_preservation hx (ih hΔ ν hν) hs
  case tlam =>
    rename_i hw hh hb ih hΔ ν hν e' hs
    cases hs
    exact .tclo hh hw hν.1 hν.2 hb
  case clo =>
    rename_i hh wa vc hc hb ihc ihb hΔ ν hν e' hs
    have hfalse := step_isValue_false hs
    have bad : true = false := vc.symm.trans hfalse
    cases bad
  case rclo =>
    rename_i hh wa wb vc hc hb ihc ihb hΔ ν hν e' hs
    have hfalse := step_isValue_false hs
    have bad : true = false := vc.symm.trans hfalse
    cases bad
  case tclo =>
    rename_i hh wa vc hc hb ihc ihb hΔ ν hν e' hs
    have hfalse := step_isValue_false hs
    have bad : true = false := vc.symm.trans hfalse
    cases bad
  case value =>
    rename_i hv ht hh ih hΔ ν hν e' hs
    rw [value_no_step hv] at hs
    cases hs
  case nil => rename_i _ _ _ _ hs; cases hs
  case cons =>
    rename_i Δ h x a fs r l hx hf hd ihx ihf hΔ ν hν fs' hs
    cases hvx : x.isValue with
    | false =>
      rw [step_cons_left hvx] at hs
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .cons (ihx hΔ ν hν _ hx') hf hd
    | true =>
      cases hvf : fs.isValue with
      | false =>
        rw [step_cons_right hvx hvf] at hs
        obtain ⟨fs', hf', rfl⟩ := Option.map_eq_some_iff.mp hs
        exact .cons hx (ihf hΔ ν hν _ hf') hd
      | true =>
        rw [value_no_step (e := .cons l x fs) (Bool.and_eq_true_iff.mpr ⟨hvx,hvf⟩)] at hs
        cases hs
  all_goals
    rename_i heq hw ih hΔ ν hν e' hs
    exact .conv (ih hΔ ν hν _ hs) heq hw

/-- T1.1: the exact closed preservation statement from Goals.lean. -/
theorem preservation : Goals.Preservation := by
  intro ν e e' h a hν ht hs
  exact ht.preservation .empty ν hν e' hs.2

end LeanSce.Target

/-! ## Evaluation Properties -/

namespace LeanSce.Target

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

end LeanSce.Target

/-! ## Behaviour -/

namespace LeanSce.Target

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

end LeanSce.Target

/-! ## Record Result -/

namespace LeanSce.Target

/-- Any terminating, typed record computation has exactly its advertised labels. -/
theorem typed_record_result (ht : HasType Δ h e (.record r)) (hΔ : Context.Valid Δ)
    (hν : ValueType Δ ν h) (he : Terminates ν e w) :
    ∃ fs, w = .record fs ∧ ∀ l, l ∈ fs.labels ↔ l ∈ r.knownLabels := by
  have hw := he.1.preservation hν ht hΔ
  obtain ⟨fs,rfl⟩ := hw.value_shape he.2
  have hf := hw.value_record_inv he.2 (ht.result_wf hΔ).record_row
  exact ⟨fs,rfl,fun _ => hf.labels_mem⟩

end LeanSce.Target

/-! ## Counted Evaluation -/

namespace LeanSce.Target

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

end LeanSce.Target

/-! ## Record Counted Evaluation -/

namespace LeanSce.Target

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

end LeanSce.Target

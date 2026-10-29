import LeanSce.Source.Definitions.Elaboration
import LeanSce.Source.Definitions.Semantics
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.CanonicalForms
import LeanSce.Source.Metatheory.Records

/-!
# Source / Metatheory / Safety

Proofs and supporting constructions for safety.
-/

/-! ## Operational Properties -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

theorem step_isValue_false (hs : step ν e = some e') : e.isValue = false := by
  cases hv : e.isValue with
  | false => rfl
  | true =>
    have hn := value_no_step (ν := ν) hv
    rw [hn] at hs
    cases hs

/-- Progress for either expressions or ordered field initializers. -/
def CanStep (ν : Expr) (e : Term s) : Prop := Value e ∨ ∃ e', step ν e = some e'

theorem canStep_of_value (hv : Value e) : CanStep ν e := Or.inl hv

theorem step_pair_left (hv : a.isValue = false) :
    step ν (.pair a b) = (step ν a).map (fun a' => .pair a' b) := by
  rw [step]
  simp only [Term.isValue, hv, Bool.false_and, Bool.false_eq_true,
    Bool.not_false, ↓reduceIte]

theorem step_pair_right (ha : Value a) (hb : b.isValue = false) :
    step ν (.pair a b) = (step ν b).map (.pair a) := by
  rw [step]
  simp only [Value] at ha
  simp only [Term.isValue, ha, hb, Bool.true_and, Bool.false_eq_true,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem canStep_pair (ha : CanStep ν a) (hb : CanStep ν b) :
    CanStep ν (.pair a b) := by
  rcases ha with ha | ⟨a', hs⟩
  · rcases hb with hb | ⟨b', hs⟩
    · exact .inl (Bool.and_eq_true_iff.mpr ⟨ha, hb⟩)
    · exact .inr ⟨.pair a b', by rw [step_pair_right ha (step_isValue_false hs), hs]; rfl⟩
  · exact .inr ⟨.pair a' b, by rw [step_pair_left (step_isValue_false hs), hs]; rfl⟩

theorem step_cons_left (hv : a.isValue = false) :
    step ν (.cons l a fs) = (step ν a).map (fun a' => .cons l a' fs) := by
  rw [step]
  simp only [Term.isValue, hv, Bool.false_and, Bool.false_eq_true,
    Bool.not_false, ↓reduceIte]

theorem step_cons_right (ha : Value a) (hf : fs.isValue = false) :
    step ν (.cons l a fs) = (step ν fs).map (.cons l a) := by
  rw [step]
  simp only [Value] at ha
  simp only [Term.isValue, ha, hf, Bool.true_and, Bool.false_eq_true,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem canStep_cons (ha : CanStep ν a) (hf : CanStep ν fs) :
    CanStep ν (.cons l a fs) := by
  rcases ha with ha | ⟨a', hs⟩
  · rcases hf with hf | ⟨fs', hs⟩
    · exact .inl (Bool.and_eq_true_iff.mpr ⟨ha, hf⟩)
    · exact .inr ⟨.cons l a fs', by rw [step_cons_right ha (step_isValue_false hs), hs]; rfl⟩
  · exact .inr ⟨.cons l a' fs, by rw [step_cons_left (step_isValue_false hs), hs]; rfl⟩

theorem step_inl_eq : step ν (.inl t a) = (step ν a).map (.inl t) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_inr_eq : step ν (.inr t a) = (step ν a).map (.inr t) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_tag_eq : step ν (.tag l a) = (step ν a).map (.tag l) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_pack_eq : step ν (.pack u t a) = (step ν a).map (.pack u t) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_fold_eq : step ν (.fold t a) = (step ν a).map (.fold t) := by
  cases hv : a.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_record_eq : step ν (.record fs) = (step ν fs).map .record := by
  cases hv : fs.isValue with
  | false => rw [step]; simp [Term.isValue, hv]
  | true => rw [value_no_step (ν := ν) hv]; rw [step]; simp [Term.isValue, hv]

theorem step_box_eq : step ν (.box a b) =
    (if !a.isValue then (step ν a).map (fun a' => .box a' b)
     else if b.isValue then some b else (step a b).map (.box a)) := rfl

theorem step_fst_eq : step ν (.fst a) =
    (if !a.isValue then (step ν a).map .fst
     else match a with | .pair x _ => some x | _ => none) := rfl

theorem step_snd_eq : step ν (.snd a) =
    (if !a.isValue then (step ν a).map .snd
     else match a with | .pair _ y => some y | _ => none) := rfl

theorem step_app_eq : step ν (.app f x) =
    (if !f.isValue then (step ν f).map (fun f' => .app f' x)
     else if !x.isValue then (step ν x).map (.app f)
     else match f with
       | .clo cap _ body => some (.box (.pair cap x) body)
       | .rclo cap _ _ body => some (.box (.pair (.pair cap f) x) body)
       | _ => none) := rfl

theorem step_case_eq : step ν (.case a l r) =
    (if !a.isValue then (step ν a).map (fun a' => .case a' l r)
     else match a with
       | .inl _ v => some (.box (.pair ν v) l)
       | .inr _ v => some (.box (.pair ν v) r)
       | _ => none) := rfl

theorem step_find_eq : step ν (.find l a) =
    (if !a.isValue then (step ν a).map (.find l)
     else match a.findTags l with | [v] => some v | _ => none) := rfl

theorem step_get_eq : step ν (.get a l) =
    (if !a.isValue then (step ν a).map (fun a' => .get a' l)
     else match a with | .record fs => fs.lookup l | _ => none) := rfl

theorem step_merge_eq : step ν (.merge a b) =
    (if !a.isValue then (step ν a).map (fun a' => .merge a' b)
     else if !b.isValue then (step ν b).map (.merge a)
     else match a,b with
       | .record fs,.record gs =>
           if fs.labels.all (fun l => !gs.labels.contains l) then some (.record (fs.append gs)) else none
       | _,_ => none) := rfl

theorem step_take_eq : step ν (.take ls a) =
    (if !a.isValue then (step ν a).map (.take ls)
     else match a with
       | .record fs => if ls.all fs.labels.contains then some (.record (fs.filter ls.contains)) else none
       | _ => none) := rfl

theorem step_drop_eq : step ν (.drop ls a) =
    (if !a.isValue then (step ν a).map (.drop ls)
     else match a with
       | .record fs => if ls.all fs.labels.contains then some (.record (fs.filter (fun l => !ls.contains l))) else none
       | _ => none) := rfl

theorem step_relabel_eq : step ν (.relabel l k a) =
    (if !a.isValue then (step ν a).map (.relabel l k)
     else match a with
       | .record fs =>
           if l != k && fs.labels.contains l && !fs.labels.contains k then some (.record (fs.renameFields l k)) else none
       | _ => none) := rfl

theorem step_tapp_eq : step ν (.tapp a u) =
    (if !a.isValue then (step ν a).map (fun a' => .tapp a' u)
     else match a with
       | .tclo cap _ _ body => some (.box cap (body.subst u.openSubst))
       | _ => none) := rfl

theorem step_unpack_eq : step ν (.unpack a body) =
    (if !a.isValue then (step ν a).map (fun a' => .unpack a' body)
     else match a with
       | .pack u _ v => some (.box (.pair ν v) (body.subst u.openSubst))
       | _ => none) := rfl

theorem step_unfold_eq : step ν (.unfold a) =
    (if !a.isValue then (step ν a).map .unfold
     else match a with | .fold _ v => some v | _ => none) := rfl

theorem step_prim_eq : step ν (.prim p args) =
    (if !args.isValue then (step ν args).map (.prim p) else evalPrim p args) := rfl

theorem step_ite_eq : step ν (.ite c a b) =
    (if !c.isValue then (step ν c).map (fun c' => .ite c' a b)
     else match c with | .bool true => some a | .bool false => some b | _ => none) := rfl

theorem step_letVal_eq : step ν (.letVal t e body) =
    (if !e.isValue then (step ν e).map (fun e' => .letVal t e' body)
     else some (.box (.pair ν e) body)) := rfl

theorem step_view_eq : step ν (.view a b cd e) =
    (if !e.isValue then (step ν e).map (.view a b cd) else some (.app cd e)) := rfl

theorem step_capture_eq : step ν (.capture c i o cap body) =
    (if !cap.isValue then (step ν cap).map (fun cap' => .capture c i o cap' body)
     else some (.moduleVal cap c i o body)) := rfl

theorem step_run_eq : step ν (.run p i o cd m provider) =
    (if !m.isValue then (step ν m).map (fun m' => .run p i o cd m' provider)
     else if !provider.isValue then (step ν provider).map (.run p i o cd m)
     else some (.invoke i o m (.view (.record p) (.record i) cd provider))) := rfl

theorem step_link_eq : step ν (.link p i o cd provider m) =
    (if !provider.isValue then (step ν provider).map (fun p' => .link p i o cd p' m)
     else if !m.isValue then (step ν m).map (.link p i o cd provider)
     else some (.merge provider (.run p i o cd m provider))) := rfl

theorem step_provide_eq : step ν (.provide p j k o cd provider m) =
    (if !provider.isValue then (step ν provider).map (fun p' => .provide p j k o cd p' m)
     else if !m.isValue then (step ν m).map (.provide p j k o cd provider)
     else some (.resid m (.view (.record p) (.record j) cd provider) j k o)) := rfl

theorem step_complete_eq : step ν (.complete o m) =
    (if !m.isValue then (step ν m).map (.complete o)
     else some (.run .empty .empty o (.close (.lam (.record .empty) (.ix 0))) m (.record .nil))) := rfl

theorem step_resid_eq : step ν (.resid m saved j k o) =
    (if m.isValue then (step ν saved).map (fun saved' => .resid m saved' j k o) else none) := by
  cases hm : m.isValue <;> cases hs : saved.isValue
  all_goals rw [step]; simp only [Term.isValue,hm,hs,Bool.and_true,Bool.and_false,↓reduceIte]
  all_goals try rw [value_no_step hs]
  all_goals rfl

theorem step_invoke_eq : step ν (.invoke i o m imports) =
    (if !m.isValue then (step ν m).map (fun m' => .invoke i o m' imports)
     else if !imports.isValue then (step ν imports).map (.invoke i o m)
     else match m with
       | .moduleVal cap _ _ _ body => some (.box (.merge cap imports) body)
       | .resid original saved j k _ => some (.invoke (.union j k) o original (.merge saved imports))
       | _ => none) := rfl

end LeanSce.Source

/-! ## Primitive Preservation -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

private theorem binary_prim_preservation
    (build : ∀ {x y}, HasType Δ h x a → HasType Δ h y b →
      HasType Δ h (.prim p (.cons l x (.cons k y .nil))) r)
    (reduce : ∀ {x y z}, HasType Δ h x a → HasType Δ h y b → Value x → Value y →
      evalPrim p (.cons l x (.cons k y .nil)) = some z → HasType Δ h z r)
    (hx : HasType Δ h x a) (hy : HasType Δ h y b)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' a)
    (ihy : ∀ y', step ν y = some y' → HasType Δ h y' b)
    (hs : step ν (.prim p (.cons l x (.cons k y .nil))) = some z) : HasType Δ h z r := by
  rw [step_prim_eq] at hs
  cases hvx : x.isValue with
  | false =>
    simp only [Term.isValue, hvx, Bool.false_and, Bool.not_false, ↓reduceIte] at hs
    rw [step_cons_left hvx, Option.map_map] at hs
    obtain ⟨x',hx',he⟩ := Option.map_eq_some_iff.mp hs
    subst z
    exact build (ihx x' hx') hy
  | true =>
    cases hvy : y.isValue with
    | false =>
      simp only [Term.isValue, hvx, hvy, Bool.true_and, Bool.false_and,
        Bool.not_false, ↓reduceIte] at hs
      rw [step_cons_right hvx (by simp [Term.isValue, hvy]),
        step_cons_left hvy, Option.map_map, Option.map_map] at hs
      obtain ⟨y',hy',he⟩ := Option.map_eq_some_iff.mp hs
      subst z
      exact build hx (ihy y' hy')
    | true =>
      simp only [Term.isValue, hvx, hvy, Bool.true_and, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte] at hs
      exact reduce hx hy hvx hvy hs

theorem prim_add_preservation (hx : HasType Δ h x .int) (hy : HasType Δ h y .int)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' .int)
    (ihy : ∀ y', step ν y = some y' → HasType Δ h y' .int)
    (hs : step ν (.prim .add (.cons l x (.cons k y .nil))) = some z) : HasType Δ h z .int := by
  apply binary_prim_preservation (fun hx hy => .add hx hy) ?_ hx hy ihx ihy hs
  intro x y z hx hy hvx hvy he
  obtain ⟨n,rfl⟩ := hx.value_shape hvx
  obtain ⟨m,rfl⟩ := hy.value_shape hvy
  simp only [evalPrim, Option.some.injEq] at he
  subst z
  exact .int hx.ambient_wf

theorem prim_eqInt_preservation (hx : HasType Δ h x .int) (hy : HasType Δ h y .int)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' .int)
    (ihy : ∀ y', step ν y = some y' → HasType Δ h y' .int)
    (hs : step ν (.prim .eqInt (.cons l x (.cons k y .nil))) = some z) : HasType Δ h z .bool := by
  apply binary_prim_preservation (fun hx hy => .eqInt hx hy) ?_ hx hy ihx ihy hs
  intro x y z hx hy hvx hvy he
  obtain ⟨n,rfl⟩ := hx.value_shape hvx
  obtain ⟨m,rfl⟩ := hy.value_shape hvy
  simp only [evalPrim, Option.some.injEq] at he
  subst z
  exact .bool hx.ambient_wf

theorem prim_concat_preservation (hx : HasType Δ h x .string) (hy : HasType Δ h y .string)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' .string)
    (ihy : ∀ y', step ν y = some y' → HasType Δ h y' .string)
    (hs : step ν (.prim .concat (.cons l x (.cons k y .nil))) = some z) : HasType Δ h z .string := by
  apply binary_prim_preservation (fun hx hy => .concat hx hy) ?_ hx hy ihx ihy hs
  intro x y z hx hy hvx hvy he
  obtain ⟨n,rfl⟩ := hx.value_shape hvx
  obtain ⟨m,rfl⟩ := hy.value_shape hvy
  simp only [evalPrim, Option.some.injEq] at he
  subst z
  exact .string hx.ambient_wf

theorem prim_showInt_preservation (hx : HasType Δ h x .int)
    (ihx : ∀ x', step ν x = some x' → HasType Δ h x' .int)
    (hs : step ν (.prim .showInt (.cons l x .nil)) = some z) : HasType Δ h z .string := by
  rw [step_prim_eq] at hs
  cases hvx : x.isValue with
  | false =>
    simp only [Term.isValue, hvx, Bool.false_and, Bool.not_false, ↓reduceIte] at hs
    rw [step_cons_left hvx, Option.map_map] at hs
    obtain ⟨x',hx',he⟩ := Option.map_eq_some_iff.mp hs
    subst z
    exact .showInt (ihx x' hx')
  | true =>
    obtain ⟨n,rfl⟩ := hx.value_shape hvx
    simp only [Term.isValue, Bool.true_and, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, evalPrim, Option.some.injEq] at hs
    subst z
    exact .string hx.ambient_wf

end LeanSce.Source

/-! ## Progress -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

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
    (motive_3 := fun _ _ _ _ _ => True)
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
  case letVal =>
    rename_i hx hb ihx ihb hΔ ν hν
    rcases ihx hΔ ν hν with hv | ⟨x',hs⟩
    · exact .inr ⟨_,by simp [step_letVal_eq,(show _ = true from hv)] <;> repeat' constructor⟩
    · exact .inr ⟨.letVal _ x' _,by simp [step_letVal_eq,step_isValue_false hs,hs] <;> repeat' constructor⟩
  case view =>
    rename_i hx hc ihx ihc hΔ ν hν
    rcases ihx hΔ ν hν with hv | ⟨x',hs⟩
    · exact .inr ⟨_,by simp [step_view_eq,(show _ = true from hv)] <;> repeat' constructor⟩
    · exact .inr ⟨.view _ _ _ x',by simp [step_view_eq,step_isValue_false hs,hs] <;> repeat' constructor⟩
  case module => exact .inr ⟨_,rfl⟩
  case capture =>
    rename_i hc wi wo hd hb ihc ihb hΔ ν hν
    rcases ihc hΔ ν hν with hv | ⟨cap',hs⟩
    · exact .inr ⟨_,by simp [step_capture_eq,(show _ = true from hv)] <;> repeat' constructor⟩
    · exact .inr ⟨.capture _ _ _ cap' _,by simp [step_capture_eq,step_isValue_false hs,hs] <;> repeat' constructor⟩
  case run =>
    rename_i hm hp hc ihm ihp ihc hΔ ν hν
    rcases ihm hΔ ν hν with hvm | ⟨m',hs⟩
    · rcases ihp hΔ ν hν with hvp | ⟨p',hs⟩
      · exact .inr ⟨_,by simp [step_run_eq,(show _ = true from hvm),(show _ = true from hvp)] <;> repeat' constructor⟩
      · exact .inr ⟨.run _ _ _ _ _ p',by simp [step_run_eq,(show _ = true from hvm),step_isValue_false hs,hs] <;> repeat' constructor⟩
    · exact .inr ⟨.run _ _ _ _ m' _,by simp [step_run_eq,step_isValue_false hs,hs] <;> repeat' constructor⟩
  case link =>
    rename_i hp hm hc hd ihp ihm ihc hΔ ν hν
    rcases ihp hΔ ν hν with hvp | ⟨p',hs⟩
    · rcases ihm hΔ ν hν with hvm | ⟨m',hs⟩
      · exact .inr ⟨_,by simp [step_link_eq,(show _ = true from hvp),(show _ = true from hvm)] <;> repeat' constructor⟩
      · exact .inr ⟨.link _ _ _ _ _ m',by simp [step_link_eq,(show _ = true from hvp),step_isValue_false hs,hs] <;> repeat' constructor⟩
    · exact .inr ⟨.link _ _ _ _ p' _,by simp [step_link_eq,step_isValue_false hs,hs] <;> repeat' constructor⟩
  case provide =>
    rename_i hp hm hc wj wk hd ihp ihm ihc hΔ ν hν
    rcases ihp hΔ ν hν with hvp | ⟨p',hs⟩
    · rcases ihm hΔ ν hν with hvm | ⟨m',hs⟩
      · exact .inr ⟨_,by simp [step_provide_eq,(show _ = true from hvp),(show _ = true from hvm)] <;> repeat' constructor⟩
      · exact .inr ⟨.provide _ _ _ _ _ _ m',by simp [step_provide_eq,(show _ = true from hvp),step_isValue_false hs,hs] <;> repeat' constructor⟩
    · exact .inr ⟨.provide _ _ _ _ _ p' _,by simp [step_provide_eq,step_isValue_false hs,hs] <;> repeat' constructor⟩
  case complete =>
    rename_i hm ihm hΔ ν hν
    rcases ihm hΔ ν hν with hv | ⟨m',hs⟩
    · exact .inr ⟨_,by simp [step_complete_eq,(show _ = true from hv)] <;> repeat' constructor⟩
    · exact .inr ⟨.complete _ m',by simp [step_complete_eq,step_isValue_false hs,hs] <;> repeat' constructor⟩
  case moduleVal =>
    rename_i hh vc hc wi wo hd hb ihc ihb hΔ ν hν
    obtain ⟨fs,rfl⟩ := hc.value_shape vc
    exact .inl vc
  case resid =>
    rename_i vm hm saved wj wk hd ihm ihs hΔ ν hν
    rcases ihs hΔ ν hν with hv | ⟨saved',hs⟩
    · exact .inl (Bool.and_eq_true_iff.mpr ⟨vm,hv⟩)
    · exact .inr ⟨.resid _ saved' _ _ _,by simp [step_resid_eq,(show _ = true from vm),hs] <;> repeat' constructor⟩
  case invoke =>
    rename_i hm hp ihm ihp hΔ ν hν
    rcases ihm hΔ ν hν with hvm | ⟨m',hs⟩
    · rcases ihp hΔ ν hν with hvp | ⟨p',hs⟩
      · rcases hm.value_shape hvm with ⟨cap,c,i,o,body,rfl⟩ | ⟨m,saved,j,k,o,rfl⟩
        · exact .inr ⟨_,by simp [step_invoke_eq,(show _ = true from hvm),(show _ = true from hvp)] <;> repeat' constructor⟩
        · exact .inr ⟨_,by simp [step_invoke_eq,(show _ = true from hvm),(show _ = true from hvp)] <;> repeat' constructor⟩
      · exact .inr ⟨.invoke _ _ _ p',by simp [step_invoke_eq,(show _ = true from hvm),step_isValue_false hs,hs] <;> repeat' constructor⟩
    · exact .inr ⟨.invoke _ _ m' _,by simp [step_invoke_eq,step_isValue_false hs,hs] <;> repeat' constructor⟩
  case closed => trivial
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

/-- S1.2: every well-typed closed configuration is a value or can reduce. -/
theorem progress (hν : ValueType .empty ν h) (ht : HasType .empty h e a) :
    Value e ∨ ∃ e', Step ν e e' := by
  rcases ht.canStep .empty ν hν with hv | ⟨e',hs⟩
  · exact .inl hv
  · exact .inr ⟨e',hν.1,hs⟩

end LeanSce.Source

/-! ## Preservation -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

/-- Preservation for every valid static context. The paper's closed source statement
    is obtained by specializing the context to empty. -/
theorem HasType.preservation (ht : HasType Δ h e a) :
    Context.Valid Δ → ∀ ν, ValueType Δ ν h → ∀ e', step ν e = some e' →
      HasType Δ h e' a := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ => Context.Valid Δ → ∀ ν, ValueType Δ ν h →
      ∀ e', step ν e = some e' → HasType Δ h e' a)
    (motive_2 := fun Δ h fs r _ => Context.Valid Δ → ∀ ν, ValueType Δ ν h →
      ∀ fs', step ν fs = some fs' → FieldsType Δ h fs' r)
    (motive_3 := fun _ _ _ _ _ => True)
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
  case letVal =>
    rename_i Δ a h x body b wa hx hb ihx ihb hΔ ν hν e' hs
    rw [step_letVal_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv,Bool.not_false,↓reduceIte] at hs
      obtain ⟨x',hx',rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .letVal wa (ihx hΔ ν hν _ hx') hb
    | true =>
      simp only [hv,Bool.not_true,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at hs
      subst e'
      exact .box (.pair (hν.inclusion hx.ambient_wf) hx) hb
  case view =>
    rename_i Δ h x a b cd hx hc ihx ihc hΔ ν hν e' hs
    rw [step_view_eq] at hs
    cases hv : x.isValue with
    | false =>
      simp only [hv,Bool.not_false,↓reduceIte] at hs
      obtain ⟨x',hx',rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .view (ihx hΔ ν hν _ hx') hc
    | true =>
      simp only [hv,Bool.not_true,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at hs
      subst e'
      exact .app (hc.typed hx.ambient_wf) hx
  case module =>
    rename_i hh wi wo hb ih hΔ ν hν e' hs
    cases hs
    exact module_activation hh wi wo hb
  case capture =>
    rename_i Δ h cap c i o body hc wi wo hd hb ihc ihb hΔ ν hν e' hs
    rw [step_capture_eq] at hs
    cases hv : cap.isValue with
    | false =>
      simp only [hv,Bool.not_false,↓reduceIte] at hs
      obtain ⟨cap',hc',rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .capture (ihc hΔ ν hν _ hc') wi wo hd hb
    | true =>
      simp only [hv,Bool.not_true,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at hs
      subst e'
      exact .moduleVal hc.ambient_wf hv (hc.value_reambient hv .unit .unit) wi wo hd hb
  case run =>
    rename_i Δ h m i o provider p cd hm hp hc ihm ihp ihc hΔ ν hν e' hs
    rw [step_run_eq] at hs
    cases hvm : m.isValue with
    | false =>
      simp only [hvm,Bool.not_false,↓reduceIte] at hs
      obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .run (ihm hΔ ν hν _ hm') hp hc
    | true =>
      simp only [hvm,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hs
      cases hvp : provider.isValue with
      | false =>
        simp only [hvp,Bool.not_false,↓reduceIte] at hs
        obtain ⟨p',hp',rfl⟩ := Option.map_eq_some_iff.mp hs
        exact .run hm (ihp hΔ ν hν _ hp') hc
      | true =>
        simp only [hvp,Bool.not_true,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at hs
        subst e'
        exact .invoke hm (.view hp hc)
  case link =>
    rename_i Δ h provider p m i o cd hp hm hc hd ihp ihm ihc hΔ ν hν e' hs
    rw [step_link_eq] at hs
    cases hvp : provider.isValue with
    | false =>
      simp only [hvp,Bool.not_false,↓reduceIte] at hs
      obtain ⟨p',hp',rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .link (ihp hΔ ν hν _ hp') hm hc hd
    | true =>
      simp only [hvp,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hs
      cases hvm : m.isValue with
      | false =>
        simp only [hvm,Bool.not_false,↓reduceIte] at hs
        obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hs
        exact .link hp (ihm hΔ ν hν _ hm') hc hd
      | true =>
        simp only [hvm,Bool.not_true,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at hs
        subst e'
        exact .merge hp (.run hm hp hc) hd
  case provide =>
    rename_i Δ h provider p m j k o cd hp hm hc wj wk hd ihp ihm ihc hΔ ν hν e' hs
    rw [step_provide_eq] at hs
    cases hvp : provider.isValue with
    | false =>
      simp only [hvp,Bool.not_false,↓reduceIte] at hs
      obtain ⟨p',hp',rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .provide (ihp hΔ ν hν _ hp') hm hc wj wk hd
    | true =>
      simp only [hvp,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hs
      cases hvm : m.isValue with
      | false =>
        simp only [hvm,Bool.not_false,↓reduceIte] at hs
        obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hs
        exact .provide hp (ihm hΔ ν hν _ hm') hc wj wk hd
      | true =>
        simp only [hvm,Bool.not_true,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at hs
        subst e'
        exact .resid hvm (hm.value_reambient hvm .unit .unit) (.view hp hc) wj wk hd
  case complete =>
    rename_i Δ h m o hm ihm hΔ ν hν e' hs
    rw [step_complete_eq] at hs
    cases hv : m.isValue with
    | false =>
      simp only [hv,Bool.not_false,↓reduceIte] at hs
      obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .complete (ihm hΔ ν hν _ hm')
    | true =>
      simp only [hv,Bool.not_true,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at hs
      subst e'
      exact .run hm (.record (.nil hm.ambient_wf)) (empty_identity_cert _)
  case moduleVal =>
    rename_i hh vc hc wi wo hd hb ihc ihb hΔ ν hν e' hs
    rw [step] at hs
    split at hs <;> cases hs
  case resid =>
    rename_i vm hm saved wj wk hd ihm ihs hΔ ν hν e' hs
    rw [step_resid_eq] at hs
    simp only [show _ = true from vm,↓reduceIte] at hs
    obtain ⟨saved',hsaved',rfl⟩ := Option.map_eq_some_iff.mp hs
    exact .resid vm hm (ihs hΔ ν hν _ hsaved') wj wk hd
  case invoke =>
    rename_i Δ h m i o imports hm hp ihm ihp hΔ ν hν e' hs
    rw [step_invoke_eq] at hs
    cases hvm : m.isValue with
    | false =>
      simp only [hvm,Bool.not_false,↓reduceIte] at hs
      obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hs
      exact .invoke (ihm hΔ ν hν _ hm') hp
    | true =>
      simp only [hvm,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hs
      cases hvp : imports.isValue with
      | false =>
        simp only [hvp,Bool.not_false,↓reduceIte] at hs
        obtain ⟨p',hp',rfl⟩ := Option.map_eq_some_iff.mp hs
        exact .invoke hm (ihp hΔ ν hν _ hp')
      | true =>
        simp only [hvp,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hs
        rcases hm.value_shape hvm with ⟨cap,c,i₀,o₀,body,rfl⟩ | ⟨m,saved,j,k,o₀,rfl⟩
        · cases hs
          exact invoke_moduleVal_typed hm hvm hp hΔ
        · cases hs
          exact invoke_resid_typed hm hvm hp hΔ
  case closed => trivial
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

/-- S1.1: the exact closed preservation statement from Goals.lean. -/
theorem preservation : Goals.Preservation := by
  intro ν e e' h a hν ht hs
  exact ht.preservation .empty ν hν e' hs.2

end LeanSce.Source

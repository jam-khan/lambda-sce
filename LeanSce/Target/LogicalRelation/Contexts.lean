import LeanSce.Target.Adapters.Typing
import LeanSce.Target.LogicalRelation.Definitions
import LeanSce.Target.LogicalRelation.Properties
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Typing
import LeanSce.Target.Metatheory.Values

/-!
# Target / LogicalRelation / Contexts

Proofs and supporting constructions for contexts.
-/

/-! ## Logical Relation Evaluation -/

namespace LeanSce.Target

theorem StrictFrame.lift_steps (hc : StrictFrame ν C) (hs : Steps ν e v) :
    Steps ν (C e) (C v) := by
  apply hs.lift C
  intro x y hxy
  refine ⟨hxy.1,?_⟩
  rw [hc.step x (fun hx => value_irreducible hx hxy)]
  rw [hxy.2]
  rfl

theorem StrictFrame.terminates (hc : StrictFrame ν C)
    (he : Terminates ν e v) (hv : Terminates ν (C v) w) : Terminates ν (C e) w :=
  ⟨(hc.lift_steps he.1).trans hv.1,hv.2⟩

namespace LogicalRelation

theorem ExprRel.zero : ExprRel 0 a q r := by
  rw [ExprRel]
  exact ⟨by intros; omega,by intros; omega⟩

theorem ValRel.toExpr (hr : ValRel n a v w) : ExprRel n a (ν,v) (N,w) := by
  rw [ExprRel]
  have hv := (show ValueType .empty v a from (by rw [ValRel] at hr; exact hr.1)).1
  have hw := (show ValueType .empty w a from (by rw [ValRel] at hr; exact hr.2.1)).1
  constructor
  · intro k hk v' ht
    obtain ⟨rfl,rfl⟩ := ht.1.value_inv hv
    exact ⟨w,⟨.refl,hw⟩,by simpa using hr⟩
  · intro k hk w' ht
    obtain ⟨rfl,rfl⟩ := ht.1.value_inv hw
    exact ⟨v,⟨.refl,hv⟩,by simpa using hr⟩

/-- A strict computation can be replaced by related computations inside a pair
    of strict frames. The tested computation pays exactly its own prefix cost. -/
theorem ExprRel.bind (he : ExprRel n a (ν,e) (N,E))
    (hc : StrictFrame ν C) (hd : StrictFrame N D)
    (hk : ∀ i, i < n → ∀ v V, ValRel (n-i) a v V →
      ExprRel (n-i) b (ν,C v) (N,D V)) : ExprRel n b (ν,C e) (N,D E) := by
  rw [ExprRel] at he ⊢
  constructor
  · intro k hkn w hw
    obtain ⟨v,i,j,hkij,hv,hrest⟩ := hc.decompose_counted hw
    have hin : i < n := by omega
    obtain ⟨V,hV,hrel⟩ := he.1 i hin v hv
    have hcont := hk i hin v V hrel
    rw [ExprRel] at hcont
    obtain ⟨W,hW,hout⟩ := hcont.1 j (by omega) w hrest
    exact ⟨W,hd.terminates hV hW,by simpa [Nat.sub_sub,hkij] using hout⟩
  · intro k hkn W hW
    obtain ⟨V,i,j,hkij,hV,hrest⟩ := hd.decompose_counted hW
    have hin : i < n := by omega
    obtain ⟨v,hv,hrel⟩ := he.2 i hin V hV
    have hcont := hk i hin v V hrel
    rw [ExprRel] at hcont
    obtain ⟨w,hw,hout⟩ := hcont.2 j (by omega) W hrest
    exact ⟨w,hc.terminates hv hw,by simpa [Nat.sub_sub,hkij] using hout⟩

/-- Matching administrative steps consume one unit before testing their bodies. -/
theorem ExprRel.step (hl : Step ν e e') (hr : Step N E E')
    (hb : ExprRel n a (ν,e') (N,E')) : ExprRel (n+1) a (ν,e) (N,E) := by
  rw [ExprRel] at hb ⊢
  constructor
  · intro k hk v hv
    cases hv.1 with
    | refl => exact False.elim (value_irreducible hv.2 hl)
    | @next e e₁ k v hs htail =>
      have heq := step_deterministic hs hl
      subst e₁
      obtain ⟨w,hw,hout⟩ := hb.1 k (by omega) v ⟨htail,hv.2⟩
      exact ⟨w,⟨.next hr hw.1,hw.2⟩,by simpa using hout⟩
  · intro k hk w hw
    cases hw.1 with
    | refl => exact False.elim (value_irreducible hw.2 hr)
    | @next E E₁ k w hs htail =>
      have heq := step_deterministic hs hr
      subst E₁
      obtain ⟨v,hv,hout⟩ := hb.2 k (by omega) w ⟨htail,hw.2⟩
      exact ⟨v,⟨.next hl hv.1,hv.2⟩,by simpa using hout⟩

end LogicalRelation
end LeanSce.Target

/-! ## Compatible Values -/

namespace LeanSce.Target

/-- Value contexts may be checked under any well-formed ambient when their
    holes have the same ambient independence. Stored code keeps its own scope. -/
theorem Compatible.value_reambient (hc : Compatible S Δ h e E a)
    (hv : Value e) (hV : Value E)
    (hS : ∀ Δ h e E a, S Δ h e E a →
      ∀ K, WellFormed Δ K → S Δ K e E a) :
    ∀ K, WellFormed Δ K → Compatible S Δ K e E a := by
  revert hv hV
  apply Compatible.rec
    (motive_1 := fun Δ _ e E a _ => Value e → Value E →
      ∀ K, WellFormed Δ K → Compatible S Δ K e E a)
    (motive_2 := fun Δ _ fs Fs r _ => Value fs → Value Fs →
      ∀ K, WellFormed Δ K → CompatibleFields S Δ K fs Fs r)
    (t := hc)
  all_goals intros
  all_goals simp_all only [Value,Term.isValue,Bool.and_eq_true,Bool.false_eq_true,false_implies]
  all_goals intros
  case hole =>
    rename_i Δ h e a E he hE hr hv hV K hK
    exact .hole (he.value_reambient hv K hK) (hE.value_reambient hV K hK)
      (hS Δ h e E a hr K hK)
  case unit => rename_i hK; exact .unit hK
  case int => rename_i hK; exact .int hK
  case bool => rename_i hK; exact .bool hK
  case string => rename_i hK; exact .string hK
  case pair =>
    rename_i hx hy ihx ihy hv hV K hK
    exact .pair (ihx hv.1 hV.1 K hK) (ihy hv.2 hV.2 K hK)
  case inl =>
    rename_i hw hx ih hv hV K hK
    exact .inl hw (ih hv hV K hK)
  case inr =>
    rename_i hw hx ih hv hV K hK
    exact .inr hw (ih hv hV K hK)
  case tag =>
    rename_i hx ih hv hV K hK
    exact .tag (ih hv hV K hK)
  case record =>
    rename_i hf ih hv hV K hK
    exact .record (ih hv hV K hK)
  case pack =>
    rename_i hw hk hu hg hx ih hv hV K hK
    exact .pack hw hk hu hg (ih hv hV K hK)
  case fold =>
    rename_i hw hx ih hv hV K hK
    exact .fold hw (ih hv hV K hK)
  case clo =>
    rename_i hh wa vc vC hc hb ihc ihb hv hV K hK
    exact .clo hK wa vc vC hc hb
  case rclo =>
    rename_i hh wa wb vc vC hc hb ihc ihb hv hV K hK
    exact .rclo hK wa wb vc vC hc hb
  case tclo =>
    rename_i hh wa vc vC hc hb ihc ihb hv hV K hK
    exact .tclo hK wa vc vC hc hb
  case value => trivial
  case nil => rename_i K hK; exact .nil hK
  case cons =>
    rename_i hx hf hd ihx ihf hv hV K hK
    exact .cons (ihx hv.1 hV.1 K hK) (ihf hv.2 hV.2 K hK) hd
  all_goals
    rename_i he hw ih hv hV K hK
    first | exact Compatible.conv (ih hv hV K hK) he hw
          | exact CompatibleFields.conv (ih hv hV K hK) he hw

/-- Replace each typed hole by its compatible implementation. The surrounding
    context retains every constructor, binder, annotation, and value premise. -/
theorem Compatible.bind (hc : Compatible R Δ h e E a)
    (hR : ∀ Δ h e E a, HasType Δ h e a → HasType Δ h E a → R Δ h e E a →
      Compatible S Δ h e E a) : Compatible S Δ h e E a := by
  apply Compatible.rec
    (motive_1 := fun Δ h e E a _ => Compatible S Δ h e E a)
    (motive_2 := fun Δ h fs Fs r _ => CompatibleFields S Δ h fs Fs r)
    (t := hc)
  all_goals intros
  case hole => exact hR _ _ _ _ _ (by assumption) (by assumption) (by assumption)
  case query => apply Compatible.query <;> assumption
  case unit => apply Compatible.unit <;> assumption
  case int => apply Compatible.int <;> assumption
  case bool => apply Compatible.bool <;> assumption
  case string => apply Compatible.string <;> assumption
  case pair => apply Compatible.pair <;> assumption
  case fst => apply Compatible.fst <;> assumption
  case snd => apply Compatible.snd <;> assumption
  case box => apply Compatible.box <;> assumption
  case lam => apply Compatible.lam <;> assumption
  case recfn => apply Compatible.recfn <;> assumption
  case app => apply Compatible.app <;> assumption
  case inl => apply Compatible.inl <;> assumption
  case inr => apply Compatible.inr <;> assumption
  case case => apply Compatible.case <;> assumption
  case tag => apply Compatible.tag <;> assumption
  case find => apply Compatible.find <;> assumption
  case record => apply Compatible.record <;> assumption
  case get => apply Compatible.get <;> assumption
  case merge => apply Compatible.merge <;> assumption
  case take => apply Compatible.take <;> assumption
  case drop => apply Compatible.drop <;> assumption
  case relabel => apply Compatible.relabel <;> assumption
  case tlam => apply Compatible.tlam <;> assumption
  case tapp => apply Compatible.tapp <;> assumption
  case pack => apply Compatible.pack <;> assumption
  case unpack => apply Compatible.unpack <;> assumption
  case fold => apply Compatible.fold <;> assumption
  case unfold => apply Compatible.unfold <;> assumption
  case add => apply Compatible.add <;> assumption
  case eqInt => apply Compatible.eqInt <;> assumption
  case showInt => apply Compatible.showInt <;> assumption
  case concat => apply Compatible.concat <;> assumption
  case ite => apply Compatible.ite <;> assumption
  case clo => apply Compatible.clo <;> assumption
  case rclo => apply Compatible.rclo <;> assumption
  case tclo => apply Compatible.tclo <;> assumption
  case value => apply Compatible.value <;> assumption
  case nil => apply CompatibleFields.nil <;> assumption
  case cons => apply CompatibleFields.cons <;> assumption
  all_goals first
    | (apply Compatible.conv <;> assumption)
    | (apply CompatibleFields.conv <;> assumption)

end LeanSce.Target

/-! ## Context Properties -/

namespace LeanSce.Target

/-- Every fixed typed context fragment has a compatible reflexive derivation.
    This is derived from typing, avoiding a circular fundamental-theorem rule. -/
theorem Compatible.same (ht : HasType Δ h e a) : Compatible R Δ h e e a := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ => Compatible R Δ h e e a)
    (motive_2 := fun Δ h fs r _ => CompatibleFields R Δ h fs fs r)
    (t := ht)
  all_goals intros
  case query => rename_i hh; exact .query hh
  case unit => rename_i hh; exact .unit hh
  case int => rename_i hh; exact .int hh
  case bool => rename_i hh; exact .bool hh
  case string => rename_i hh; exact .string hh
  case pair => rename_i ihx ihy; exact .pair ihx ihy
  case fst => rename_i ih; exact .fst ih
  case snd => rename_i ih; exact .snd ih
  case box => rename_i ihx ihy; exact .box ihx ihy
  case lam => rename_i wa hb ih; exact .lam wa ih
  case recfn => rename_i wa wb hb ih; exact .recfn wa wb ih
  case app => rename_i ihf ihx; exact .app ihf ihx
  case inl => rename_i wb hx ih; exact .inl wb ih
  case inr => rename_i wa hx ih; exact .inr wa ih
  case case => rename_i ihx ihl ihr; exact .case ihx ihl ihr
  case tag => rename_i ih; exact .tag ih
  case find => rename_i hu ih; exact .find ih hu
  case record => rename_i ih; exact .record ih
  case get => rename_i hl ih; exact .get ih hl
  case merge => rename_i hd ihx ihy; exact .merge ihx ihy hd
  case take => rename_i hn hl ih; exact .take ih hn hl
  case drop => rename_i hn hl ih; exact .drop ih hn hl
  case relabel => rename_i hl hn hd ih; exact .relabel ih hl hn hd
  case tlam => rename_i hw hh hb ih; exact .tlam hw hh ih
  case tapp => rename_i hk hu hg ih; exact .tapp ih hk hu hg
  case pack => rename_i hw hk hu hg hx ih; exact .pack hw hk hu hg ih
  case unpack => rename_i wb hb ihx ihb; exact .unpack ihx wb ihb
  case fold => rename_i hw hx ih; exact .fold hw ih
  case unfold => rename_i ih; exact .unfold ih
  case add => rename_i ihx ihy; exact .add ihx ihy
  case eqInt => rename_i ihx ihy; exact .eqInt ihx ihy
  case showInt => rename_i ih; exact .showInt ih
  case concat => rename_i ihx ihy; exact .concat ihx ihy
  case ite => rename_i ihc ihx ihy; exact .ite ihc ihx ihy
  case clo => rename_i hh wa vc hc hb ihc ihb; exact .clo hh wa vc vc ihc ihb
  case rclo => rename_i hh wa wb vc hc hb ihc ihb; exact .rclo hh wa wb vc vc ihc ihb
  case tclo => rename_i hh hw vc hc hb ihc ihb; exact .tclo hh hw vc vc ihc ihb
  case value => rename_i hv ht hh ih; exact .value hv hv ih hh
  case nil => rename_i hh; exact .nil hh
  case cons => rename_i hd ihx ihf; exact .cons ihx ihf hd
  all_goals rename_i he hw ih; exact .conv ih he hw

theorem Compatible.left_typed (hc : Compatible R Δ h e E a) : HasType Δ h e a := by
  apply Compatible.rec
    (motive_1 := fun Δ h e _ a _ => HasType Δ h e a)
    (motive_2 := fun Δ h fs _ r _ => FieldsType Δ h fs r)
    (t := hc)
  all_goals intros
  case hole => assumption
  all_goals first
    | (rename_i heq hw ih; exact HasType.conv ih heq hw)
    | (rename_i heq hw ih; exact FieldsType.conv ih heq hw)
    | (constructor <;> assumption)

theorem Compatible.right_typed (hc : Compatible R Δ h e E a) : HasType Δ h E a := by
  apply Compatible.rec
    (motive_1 := fun Δ h _ E a _ => HasType Δ h E a)
    (motive_2 := fun Δ h _ Fs r _ => FieldsType Δ h Fs r)
    (t := hc)
  all_goals intros
  case hole => assumption
  all_goals first
    | (rename_i heq hw ih; exact HasType.conv ih heq hw)
    | (rename_i heq hw ih; exact FieldsType.conv ih heq hw)
    | (constructor <;> assumption)

theorem CompatibleFields.left_typed (hc : CompatibleFields R Δ h fs Fs r)
    (hΔ : Context.Valid Δ) : FieldsType Δ h fs r :=
  (Compatible.record hc).left_typed.fields_inv hΔ

theorem CompatibleFields.right_typed (hc : CompatibleFields R Δ h fs Fs r)
    (hΔ : Context.Valid Δ) : FieldsType Δ h Fs r :=
  (Compatible.record hc).right_typed.fields_inv hΔ

namespace LogicalRelation

/-- Closed hole code remains valid under every later binder and substitution.
    The premise is the actual all-index relation of the two closed computations. -/
theorem closed_hole_logical (he : HasType .empty h e a) (hE : HasType .empty h E a)
    (hr : ∀ n ν N, ValRel n h ν N → ExprRel n a (ν,e) (N,E)) :
    ∀ Δ H x X b, HoleAt h a e E Δ H x X b → OpenRel Δ H x X b := by
  intro Δ H x X b hhole
  obtain ⟨rfl,rfl,rfl,rfl⟩ := hhole
  intro θ _ n ν N hν
  have hh := he.ambient_wf
  have ha := he.result_wf .empty
  simpa only [hh.closed_subst θ,ha.closed_subst θ,he.closed_subst θ,hE.closed_subst θ]
    using hr n ν N (by simpa only [hh.closed_subst θ] using hν)

end LogicalRelation
end LeanSce.Target

/-! ## Logical Relation Static -/

namespace LeanSce.Target

theorem Closing.of_respects (hc : Subst.Respects Δ .empty θ) : Closing θ Δ := by
  refine ⟨hc.1,?_⟩
  intro a ha
  have he := hc.2 a ha
  cases a with
  | labelRow l i =>
    change Collects (· ∈ Context.empty.assumptions)
      (Ty.gcons (.field l .unit) (θ .row i) .gnil).guardAtoms
    rw [guardCollects_cons]
    exact ⟨he,by simp [Collects,Ty.guardAtoms]⟩
  | rowRow i j =>
    change Collects (· ∈ Context.empty.assumptions)
      (Ty.gcons (θ .row i) (θ .row j) .gnil).guardAtoms
    rw [guardCollects_cons]
    exact ⟨he,by simp [Collects,Ty.guardAtoms]⟩

theorem Subst.Respects.comp (hσ : Subst.Respects Γ Δ σ) (hτ : Subst.Respects Δ Ξ τ) :
    Subst.Respects Γ Ξ (fun k i => (σ k i).subst τ) := by
  constructor
  · intro k i hi
    exact (hσ.1 k i hi).subst hτ
  · intro a ha
    have hh := hσ.2 a ha
    cases a with
    | labelRow l i => simpa [Atom.Holds,Ty.subst] using hh.subst hτ
    | rowRow i j => exact hh.subst hτ

theorem Closing.instantiate (hθ : Closing θ Δ) (hf : FreshGuards k gs)
    (hk : u.kind = k) (hu : u.WellFormed .empty)
    (hg : Entails .empty ((gs.subst θ.lift).open u)) :
    Closing (θ.instantiate u) (Δ.extend k gs) := by
  have hs := hθ.respects.lift hf
  have ho : Subst.Respects (Context.empty.extend k (gs.subst θ.lift)) .empty u.openSubst :=
    .open (by simp [Context.Normal,Context.empty]) hk hu hg
  exact Closing.of_respects (hs.comp ho)

@[simp] theorem Ty.subst_instantiate_weaken (a : Ty s) (θ : Subst) (u : Arg) :
    (a.rename Nat.succ).subst (θ.instantiate u) = a.subst θ := by
  have he : (a.rename Nat.succ).subst (θ.instantiate u) =
      ((a.rename Nat.succ).subst θ.lift).open u := by
    exact (Ty.subst_comp (a.rename Nat.succ) u.openSubst θ.lift).symm
  rw [he,Ty.subst_lift_weaken,Ty.open_weaken]

theorem Ty.subst_instantiate (a : Ty s) (θ : Subst) (u : Arg) :
    a.subst (θ.instantiate u) = (a.subst θ.lift).open u := by
  exact (Ty.subst_comp a u.openSubst θ.lift).symm

theorem Term.subst_instantiate (e : Term s) (θ : Subst) (u : Arg) :
    e.subst (θ.instantiate u) = (e.subst θ.lift).subst u.openSubst := by
  exact (Term.subst_comp e u.openSubst θ.lift).symm

end LeanSce.Target

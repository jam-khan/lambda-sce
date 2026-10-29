import LeanSce.Source.Definitions.Contexts
import LeanSce.Source.Definitions.Elaboration
import LeanSce.Source.Elaboration.Correctness
import LeanSce.Source.Elaboration.Representations
import LeanSce.Source.Elaboration.Templates
import LeanSce.Source.Elaboration.Typing
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.CanonicalForms
import LeanSce.Source.Metatheory.Evaluation
import LeanSce.Source.Metatheory.Substitution
import LeanSce.Target.LogicalRelation.Contexts
import LeanSce.Target.LogicalRelation.Evaluation
import LeanSce.Target.LogicalRelation.Fundamental
import LeanSce.Target.Metatheory.Typing
import LeanSce.Target.Metatheory.Values

/-!
# Source / Elaboration / Contexts

Proofs and supporting constructions for contexts.
-/

/-! ## Context Properties -/

namespace LeanSce.Source

/-- Every fixed typed context fragment has a compatible reflexive derivation.
    This is derived from typing, avoiding a circular fundamental-theorem rule. -/
theorem Compatible.same (ht : HasType Δ h e a) : Compatible R Δ h e e a := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ => Compatible R Δ h e e a)
    (motive_2 := fun Δ h fs r _ => CompatibleFields R Δ h fs fs r)
    (motive_3 := fun Δ a b cd _ => CompatibleCert R Δ a b cd cd)
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
  case letVal => rename_i wa hx hb ihx ihb; exact .letVal wa ihx ihb
  case view => rename_i hx hc ihx ihc; exact .view ihx ihc
  case module => rename_i hh hi ho hb ih; exact .module hh hi ho ih
  case capture => rename_i hc hi ho hd hb ihc ihb; exact .capture ihc hi ho hd ihb
  case run => rename_i hm hp hc ihm ihp ihc; exact .run ihm ihp ihc
  case link => rename_i hp hm hc hd ihp ihm ihc; exact .link ihp ihm ihc hd
  case provide => rename_i hp hm hc hj hk hd ihp ihm ihc; exact .provide ihp ihm ihc hj hk hd
  case complete => rename_i ih; exact .complete ih
  case moduleVal => rename_i hh vc hc hi ho hd hb ihc ihb; exact .moduleVal hh vc vc ihc hi ho hd ihb
  case resid => rename_i vm hm hs hj hk hd ihm ihs; exact .resid vm vm ihm ihs hj hk hd
  case invoke => rename_i ihm ihp; exact .invoke ihm ihp
  case closed => rename_i hcore ht ih; exact .closed hcore hcore ih
  case value => rename_i hv ht hh ih; exact .value hv hv ih hh
  case nil => rename_i hh; exact .nil hh
  case cons => rename_i hd ihx ihf; exact .cons ihx ihf hd
  all_goals rename_i he hw ih; exact .conv ih he hw

theorem Compatible.left_typed (hc : Compatible R Δ h e E a) : HasType Δ h e a := by
  apply Compatible.rec
    (motive_1 := fun Δ h e _ a _ => HasType Δ h e a)
    (motive_2 := fun Δ h fs _ r _ => FieldsType Δ h fs r)
    (motive_3 := fun Δ a b cd _ _ => CertType Δ a b cd)
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
    (motive_3 := fun Δ a b _ CD _ => CertType Δ a b CD)
    (t := hc)
  all_goals intros
  case hole => assumption
  all_goals first
    | (rename_i heq hw ih; exact HasType.conv ih heq hw)
    | (rename_i heq hw ih; exact FieldsType.conv ih heq hw)
    | (constructor <;> assumption)

theorem CompatibleFields.left_typed (hc : CompatibleFields R Δ h fs Fs r) :
    FieldsType Δ h fs r := by
  apply CompatibleFields.rec
    (motive_1 := fun Δ h e _ a _ => HasType Δ h e a)
    (motive_2 := fun Δ h fs _ r _ => FieldsType Δ h fs r)
    (motive_3 := fun Δ a b cd _ _ => CertType Δ a b cd)
    (t := hc)
  all_goals intros
  case hole => assumption
  all_goals first
    | (rename_i heq hw ih; exact HasType.conv ih heq hw)
    | (rename_i heq hw ih; exact FieldsType.conv ih heq hw)
    | (constructor <;> assumption)

theorem CompatibleFields.right_typed (hc : CompatibleFields R Δ h fs Fs r) :
    FieldsType Δ h Fs r := by
  apply CompatibleFields.rec
    (motive_1 := fun Δ h _ E a _ => HasType Δ h E a)
    (motive_2 := fun Δ h _ Fs r _ => FieldsType Δ h Fs r)
    (motive_3 := fun Δ a b _ CD _ => CertType Δ a b CD)
    (t := hc)
  all_goals intros
  case hole => assumption
  all_goals first
    | (rename_i heq hw ih; exact HasType.conv ih heq hw)
    | (rename_i heq hw ih; exact FieldsType.conv ih heq hw)
    | (constructor <;> assumption)

end LeanSce.Source

/-! ## Residual Compatibility -/

namespace LeanSce.Source.Templates
open LeanSce.Target
open LeanSce.Target.LogicalRelation

/-- Expression and value representations of the same suspended residual. -/
def residualForm (isVal : Bool) (j k o : Target.Row) (m saved : Target.Expr) : Target.Expr :=
  if isVal then .clo (.pair m saved) (.record k) residualBody
  else .app (.app (residual j k o) m) saved

private theorem residual_form_inv (hν : Target.Value ν) (hm : Target.Value m)
    (hs : isVal = true → Target.Value saved)
    (ht : Target.TerminatesIn ν (residualForm isVal j k o m saved) n w) :
    ∃ s i, i ≤ n ∧ Target.TerminatesIn ν saved i s ∧
      w = .clo (.pair m s) (.record k) residualBody := by
  cases isVal with
  | false => exact residual_counted_inv hν hm ht
  | true =>
    have hv : Target.Value (.clo (.pair m saved) (.record k) residualBody) :=
      Bool.and_eq_true_iff.mpr ⟨hm,hs rfl⟩
    obtain ⟨rfl,rfl⟩ := ht.1.value_inv hv
    exact ⟨saved,0,Nat.le_refl _,⟨.refl,hs rfl⟩,rfl⟩

private theorem residual_form_forward (hν : Target.Value ν) (hm : Target.Value m)
    (hs : isVal = true → Target.Value saved) (ht : Target.Terminates ν saved s) :
    Target.Terminates ν (residualForm isVal j k o m saved)
      (.clo (.pair m s) (.record k) residualBody) := by
  cases isVal with
  | false => exact residual_forward hν hm ht
  | true =>
    cases ht.1.from_value (hs rfl)
    exact ⟨.refl,Bool.and_eq_true_iff.mpr ⟨hm,hs rfl⟩⟩

/-- Residual construction is compatible even when only one filling is already
    a value and canonical compilation consequently chooses different forms. -/
theorem residual_form_logical
    (hj : Target.WellFormed .empty j) (hk : Target.WellFormed .empty k)
    (ho : Target.WellFormed .empty o) (hd : Target.Disjoint .empty j k)
    (hm : ValRel n (.arr (.record (.union j k)) (.record o)) m M)
    (hs : ExprRel n (.record j) (ν,saved) (N,SAVED))
    (hν : Target.Value ν) (hN : Target.Value N)
    (hv : isVal = true → Target.Value saved) (hV : isVAL = true → Target.Value SAVED) :
    ExprRel n (.arr (.record k) (.record o))
      (ν,residualForm isVal j k o m saved) (N,residualForm isVAL j k o M SAVED) := by
  have hb := residualBody_typed hj hk ho hd
  have hbody : BodyRel
      (.prod (.prod (.arr (.record (.union j k)) (.record o)) (.record j)) (.record k))
      (.record o) residualBody residualBody := by
    intro i μ Μ hμ
    simpa only [Target.Ty.subst_id,Target.Term.subst_id] using
      (hb.logical .empty) Target.Subst.id (Target.Closing.empty Target.Subst.id) i μ Μ
        (by simpa only [Target.Ty.subst_id] using hμ)
  apply ExprRel.pipelines (P := fun v => .clo (.pair m v) (.record k) residualBody)
    (Q := fun V => .clo (.pair M V) (.record k) residualBody) hs
  · intro i _ w hw
    exact residual_form_inv hν hm.left.1 hv hw
  · intro i _ W hW
    exact residual_form_inv hN hm.right.1 hV hW
  · intro v hv'
    exact residual_form_forward hν hm.left.1 hv hv'
  · intro V hV'
    exact residual_form_forward hN hm.right.1 hV hV'
  · intro i hi v V hv'
    exact ValRel.clo (.record hk) hb hb hbody (ValRel.pair (hm.mono hi) hv')

end LeanSce.Source.Templates

/-! ## Template Compatibility -/

namespace LeanSce.Source.Templates
open LeanSce.Target

theorem letIn_compatible (he : Target.Compatible R Δ h e E a)
    (hb : Target.Compatible R Δ (.prod h a) body BODY b) :
    Target.Compatible R Δ h (.letIn e body) (.letIn E BODY) b :=
  .box (.pair (.query he.left_typed.ambient_wf) he) hb

theorem sandbox_compatible (hh : Target.WellFormed Δ h) (hi : Target.WellFormed Δ i)
    (hb : Target.Compatible R Δ (.record i) body BODY (.record o)) :
    Target.Compatible R Δ h (sandbox i body) (sandbox i BODY) (.arr (.record i) (.record o)) := by
  apply Target.Compatible.box (.unit hh)
  apply Target.Compatible.lam (.record hi)
  exact .box (.snd (.query (.prod .unit (.record hi)))) hb

theorem captured_compatible (hh : Target.WellFormed Δ h)
    (hc : Target.WellFormed Δ c) (hi : Target.WellFormed Δ i)
    (hd : Target.Disjoint Δ c i)
    (hb : Target.Compatible R Δ (.record (.union c i)) body BODY (.record o)) :
    Target.Compatible R Δ h (captured c i body) (captured c i BODY)
      (.arr (.record c) (.arr (.record i) (.record o))) := by
  apply Target.Compatible.box (.unit hh)
  apply Target.Compatible.lam (.record hc)
  apply Target.Compatible.lam (.record hi)
  have hw : Target.WellFormed Δ (.prod (.prod .unit (.record c)) (.record i)) :=
    .prod (.prod .unit (.record hc)) (.record hi)
  exact .box (.merge (.snd (.fst (.query hw))) (.snd (.query hw)) hd) hb

theorem run_compatible (hh : Target.WellFormed Δ h)
    (hp : Target.WellFormed Δ p) (hi : Target.WellFormed Δ i)
    (ho : Target.WellFormed Δ o)
    (hc : ∀ h, Target.WellFormed Δ h →
      Target.Compatible R Δ h cd CD (.arr (.record p) (.record i))) :
    Target.Compatible R Δ h (run p i o cd) (run p i o CD)
      (.arr (.arr (.record i) (.record o)) (.arr (.record p) (.record o))) := by
  apply Target.Compatible.box (.unit hh)
  apply Target.Compatible.lam (.arr (.record hi) (.record ho))
  apply Target.Compatible.lam (.record hp)
  have hw : Target.WellFormed Δ (.prod (.prod .unit (.arr (.record i) (.record o))) (.record p)) :=
    .prod (.prod .unit (.arr (.record hi) (.record ho))) (.record hp)
  exact .app (.snd (.fst (.query hw))) (.app (hc _ hw) (.snd (.query hw)))

theorem residualBody_compatible (hj : Target.WellFormed Δ j)
    (hk : Target.WellFormed Δ k) (ho : Target.WellFormed Δ o)
    (hd : Target.Disjoint Δ j k) :
    Target.Compatible R Δ
      (.prod (.prod (.arr (.record (.union j k)) (.record o)) (.record j)) (.record k))
      residualBody residualBody (.record o) := by
  have hw : Target.WellFormed Δ
      (.prod (.prod (.arr (.record (.union j k)) (.record o)) (.record j)) (.record k)) :=
    .prod (.prod (.arr (.record (.union hj hk hd)) (.record ho)) (.record hj)) (.record hk)
  exact .app (.fst (.fst (.query hw)))
    (.merge (.snd (.fst (.query hw))) (.snd (.query hw)) hd)

theorem residual_compatible (hh : Target.WellFormed Δ h)
    (hj : Target.WellFormed Δ j) (hk : Target.WellFormed Δ k)
    (ho : Target.WellFormed Δ o) (hd : Target.Disjoint Δ j k) :
    Target.Compatible R Δ h (residual j k o) (residual j k o)
      (.arr (.arr (.record (.union j k)) (.record o))
        (.arr (.record j) (.arr (.record k) (.record o)))) := by
  apply Target.Compatible.box (.unit hh)
  apply Target.Compatible.lam (.arr (.record (.union hj hk hd)) (.record ho))
  apply Target.Compatible.lam (.record hj)
  have hw : Target.WellFormed Δ
      (.prod (.prod .unit (.arr (.record (.union j k)) (.record o))) (.record j)) :=
    .prod (.prod .unit (.arr (.record (.union hj hk hd)) (.record ho))) (.record hj)
  apply Target.Compatible.box (.pair (.snd (.fst (.query hw))) (.snd (.query hw)))
  exact .lam (.record hk) (residualBody_compatible hj hk ho hd)

theorem provide_compatible (hh : Target.WellFormed Δ h)
    (hp : Target.WellFormed Δ p) (hj : Target.WellFormed Δ j)
    (hk : Target.WellFormed Δ k) (ho : Target.WellFormed Δ o)
    (hd : Target.Disjoint Δ j k)
    (hc : ∀ h, Target.WellFormed Δ h →
      Target.Compatible R Δ h cd CD (.arr (.record p) (.record j))) :
    Target.Compatible R Δ h (provide p j k o cd) (provide p j k o CD)
      (.arr (.record p) (.arr (.arr (.record (.union j k)) (.record o))
        (.arr (.record k) (.record o)))) := by
  apply Target.Compatible.box (.unit hh)
  apply Target.Compatible.lam (.record hp)
  apply Target.Compatible.lam (.arr (.record (.union hj hk hd)) (.record ho))
  have hw : Target.WellFormed Δ
      (.prod (.prod .unit (.record p)) (.arr (.record (.union j k)) (.record o))) :=
    .prod (.prod .unit (.record hp)) (.arr (.record (.union hj hk hd)) (.record ho))
  apply letIn_compatible (.app (hc _ hw) (.snd (.fst (.query hw))))
  have hw' : Target.WellFormed Δ
      (.prod (.prod (.prod .unit (.record p)) (.arr (.record (.union j k)) (.record o))) (.record j)) :=
    .prod hw (.record hj)
  apply Target.Compatible.box (.pair (.snd (.fst (.query hw'))) (.snd (.query hw')))
  exact .lam (.record hk) (residualBody_compatible hj hk ho hd)

theorem link_compatible (hh : Target.WellFormed Δ h)
    (hp : Target.WellFormed Δ p) (hi : Target.WellFormed Δ i)
    (ho : Target.WellFormed Δ o) (hd : Target.Disjoint Δ p o)
    (hc : ∀ h, Target.WellFormed Δ h →
      Target.Compatible R Δ h cd CD (.arr (.record p) (.record i))) :
    Target.Compatible R Δ h (link p i o cd) (link p i o CD)
      (.arr (.record p) (.arr (.arr (.record i) (.record o)) (.record (.union p o)))) := by
  apply Target.Compatible.box (.unit hh)
  apply Target.Compatible.lam (.record hp)
  apply Target.Compatible.lam (.arr (.record hi) (.record ho))
  have hw : Target.WellFormed Δ
      (.prod (.prod .unit (.record p)) (.arr (.record i) (.record o))) :=
    .prod (.prod .unit (.record hp)) (.arr (.record hi) (.record ho))
  apply letIn_compatible (.app (hc _ hw) (.snd (.fst (.query hw))))
  have hw' : Target.WellFormed Δ
      (.prod (.prod (.prod .unit (.record p)) (.arr (.record i) (.record o))) (.record i)) :=
    .prod hw (.record hi)
  apply letIn_compatible (.app (.snd (.fst (.query hw'))) (.snd (.query hw')))
  have hw'' : Target.WellFormed Δ
      (.prod (.prod (.prod (.prod .unit (.record p)) (.arr (.record i) (.record o))) (.record i)) (.record o)) :=
    .prod hw' (.record ho)
  exact .merge (.snd (.fst (.fst (.fst (.query hw''))))) (.snd (.query hw'')) hd

theorem module_value_compatible (hh : Target.WellFormed Δ h)
    (hi : Target.WellFormed Δ i) (hc : Target.Compatible R Δ .unit cap CAP (.record c))
    (hvc : Target.Value cap) (hvC : Target.Value CAP) (hd : Target.Disjoint Δ c i)
    (hb : Target.Compatible R Δ (.record (.union c i)) body BODY (.record o))
    (hΔ : Target.Context.Valid Δ) :
    Target.Compatible R Δ h
      (.clo (.pair .unit cap) (.record i) (.box (.merge (.ix 1) (.ix 0)) body))
      (.clo (.pair .unit CAP) (.record i) (.box (.merge (.ix 1) (.ix 0)) BODY))
      (.arr (.record i) (.record o)) := by
  have wc := (hc.left_typed.result_wf hΔ).record_row
  apply Target.Compatible.clo hh (.record hi) (show Target.Value (.pair .unit cap) from by
    simpa [Target.Value,Target.Term.isValue] using hvc)
    (show Target.Value (.pair .unit CAP) from by simpa [Target.Value,Target.Term.isValue] using hvC)
    (.pair (.unit .unit) hc)
  have hw : Target.WellFormed Δ (.prod (.prod .unit (.record c)) (.record i)) :=
    .prod (.prod .unit (.record wc)) (.record hi)
  exact .box (.merge (.snd (.fst (.query hw))) (.snd (.query hw)) hd) hb

theorem residual_value_compatible (hh : Target.WellFormed Δ h)
    (hj : Target.WellFormed Δ j) (hk : Target.WellFormed Δ k)
    (ho : Target.WellFormed Δ o) (hd : Target.Disjoint Δ j k)
    (hm : Target.Compatible R Δ .unit m M (.arr (.record (.union j k)) (.record o)))
    (hs : Target.Compatible R Δ .unit saved SAVED (.record j))
    (hvm : Target.Value m) (hvM : Target.Value M) (hvs : Target.Value saved) (hvS : Target.Value SAVED) :
    Target.Compatible R Δ h (.clo (.pair m saved) (.record k) residualBody)
      (.clo (.pair M SAVED) (.record k) residualBody)
      (.arr (.record k) (.record o)) := by
  apply Target.Compatible.clo hh (.record hk)
    (show Target.Value (.pair m saved) from Bool.and_eq_true_iff.mpr ⟨hvm,hvs⟩)
    (show Target.Value (.pair M SAVED) from Bool.and_eq_true_iff.mpr ⟨hvM,hvS⟩)
    (.pair hm hs)
  exact residualBody_compatible hj hk ho hd

end LeanSce.Source.Templates

/-! ## Context Erasure -/

namespace LeanSce.Source

private theorem validAll (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.all k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | all hf hg _ => exact .extend hΔ hf hg

private theorem validEx (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.ex k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | ex hf hg _ => exact .extend hΔ hf hg

/-- The canonical compiler preserves typing throughout checked and runtime syntax. -/
theorem Compatible.erase_context (hc : Compatible R Δ h e E a)
    (hR : ∀ Δ h e E a, R Δ h e E a →
      Target.LogicalRelation.OpenRel Δ.erase h.erase e.erase E.erase a.erase) :
    Context.Valid Δ → Target.Compatible Target.LogicalRelation.OpenRel
      Δ.erase h.erase e.erase E.erase a.erase := by
  apply Compatible.rec
    (motive_1 := fun Δ h e E a _ => Context.Valid Δ → Target.Compatible Target.LogicalRelation.OpenRel Δ.erase h.erase e.erase E.erase a.erase)
    (motive_2 := fun Δ h fs Fs r _ => Context.Valid Δ → Target.CompatibleFields Target.LogicalRelation.OpenRel Δ.erase h.erase fs.erase Fs.erase r.erase)
    (motive_3 := fun Δ a b cd CD _ => Context.Valid Δ → ∀ h, Target.WellFormed Δ.erase h →
      Target.Compatible Target.LogicalRelation.OpenRel Δ.erase h cd.erase CD.erase (.arr a.erase b.erase))
    (t := hc)
  all_goals intros
  all_goals intros
  case hole =>
    rename_i Δ h e a E he hE hh hΔ
    exact .hole (he.erase hΔ) (hE.erase hΔ) (hR Δ h e E a hh)
  case query => rename_i hw hΔ; exact .query hw.erase
  case unit => rename_i hw hΔ; exact .unit hw.erase
  case int => rename_i hw hΔ; exact .int hw.erase
  case bool => rename_i hw hΔ; exact .bool hw.erase
  case string => rename_i hw hΔ; exact .string hw.erase
  case pair => rename_i ihx ihy hΔ; exact .pair (ihx hΔ) (ihy hΔ)
  case fst => rename_i ih hΔ; exact .fst (ih hΔ)
  case snd => rename_i ih hΔ; exact .snd (ih hΔ)
  case box => rename_i ihx ihy hΔ; exact .box (ihx hΔ) (ihy hΔ)
  case lam => rename_i wa hb ih hΔ; exact .lam wa.erase (ih hΔ)
  case recfn => rename_i wa wb hb ih hΔ; exact .recfn wa.erase wb.erase (ih hΔ)
  case app => rename_i ihf ihx hΔ; exact .app (ihf hΔ) (ihx hΔ)
  case inl => rename_i wb hx ih hΔ; exact .inl wb.erase (ih hΔ)
  case inr => rename_i wa hx ih hΔ; exact .inr wa.erase (ih hΔ)
  case case => rename_i ihx ihl ihr hΔ; exact .case (ihx hΔ) (ihl hΔ) (ihr hΔ)
  case tag => rename_i ih hΔ; exact .tag (ih hΔ)
  case find => rename_i hx hu ih hΔ; exact .find (ih hΔ) hu.erase
  case record => rename_i ih hΔ; exact .record (ih hΔ)
  case get =>
    rename_i hx hl ih hΔ
    exact .get (ih hΔ) (by simp [hl])
  case merge => rename_i hx hy hd ihx ihy hΔ; exact .merge (ihx hΔ) (ihy hΔ) hd.erase
  case take =>
    rename_i hx hn hl ih hΔ
    have hsel := Target.Compatible.take (ih hΔ) hn (fun l hm => by
      obtain ⟨a,ha⟩ := hl l hm
      exact ⟨a.erase,by simp [ha]⟩)
    simpa only [Term.erase,Ty.erase,Ty.erase_select] using hsel
  case drop =>
    rename_i hx hn hl ih hΔ
    have hdrop := Target.Compatible.drop (ih hΔ) hn (fun l hm => by
      obtain ⟨a,ha⟩ := hl l hm
      exact ⟨a.erase,by simp [ha]⟩)
    simpa only [Term.erase,Ty.erase,Ty.erase_drop] using hdrop
  case relabel =>
    rename_i Δ h x X r l a k hx hl hn hd ih hΔ
    have hr := Target.Compatible.relabel (a := a.erase) (ih hΔ) (by simp [hl]) hn
      (by simpa only [Ty.erase,Ty.erase_drop] using hd.erase)
    simpa only [Term.erase,Ty.erase,Ty.erase_relabel] using hr
  case tlam =>
    rename_i hw hh hb ih hΔ
    have hvalid := validAll hΔ hw
    apply Target.Compatible.tlam hw.erase hh.erase
    simpa using ih hvalid
  case tapp =>
    rename_i hx hk hu hg ih hΔ
    simpa only [Term.erase,Ty.erase_open] using Target.Compatible.tapp (ih hΔ)
      (by simpa using hk) hu.erase (by simpa using hg.erase)
  case pack =>
    rename_i hw hk hu hg hx ih hΔ
    exact .pack hw.erase (by simpa using hk) hu.erase (by simpa using hg.erase)
      (by simpa using ih hΔ)
  case unpack =>
    rename_i hx wb hb ihx ihb hΔ
    have hw := hx.left_typed.result_wf hΔ
    have hvalid := validEx hΔ hw
    exact .unpack (ihx hΔ) wb.erase (by simpa only [Context.erase_extend,Ty.erase,Ty.erase_rename] using ihb hvalid)
  case fold =>
    rename_i hw hx ih hΔ
    exact .fold hw.erase (by simpa using ih hΔ)
  case unfold =>
    rename_i hx ih hΔ
    simpa only [Term.erase,Ty.erase_open,Ty.erase,Arg.erase] using Target.Compatible.unfold (ih hΔ)
  case add => rename_i ihx ihy hΔ; exact .add (ihx hΔ) (ihy hΔ)
  case eqInt => rename_i ihx ihy hΔ; exact .eqInt (ihx hΔ) (ihy hΔ)
  case showInt => rename_i ih hΔ; exact .showInt (ih hΔ)
  case concat => rename_i ihx ihy hΔ; exact .concat (ihx hΔ) (ihy hΔ)
  case ite => rename_i ihc ihx ihy hΔ; exact .ite (ihc hΔ) (ihx hΔ) (ihy hΔ)
  case clo =>
    rename_i hh wa vc vC hc hb ihc ihb hΔ
    exact .clo hh.erase wa.erase (Term.erase_value _ vc) (Term.erase_value _ vC) (ihc hΔ) (ihb hΔ)
  case rclo =>
    rename_i hh wa wb vc vC hc hb ihc ihb hΔ
    exact .rclo hh.erase wa.erase wb.erase (Term.erase_value _ vc) (Term.erase_value _ vC) (ihc hΔ) (ihb hΔ)
  case tclo =>
    rename_i hh hw vc vC hc hb ihc ihb hΔ
    have hvalid := validAll hΔ hw
    exact .tclo hh.erase hw.erase (Term.erase_value _ vc) (Term.erase_value _ vC) (ihc hΔ) (by simpa using ihb hvalid)
  case letVal =>
    rename_i wa he hb ihe ihb hΔ
    exact Templates.letIn_compatible (ihe hΔ) (ihb hΔ)
  case view =>
    rename_i he hc ihe ihc hΔ
    exact .app (ihc hΔ _ he.left_typed.ambient_wf.erase) (ihe hΔ)
  case module =>
    rename_i hh hi ho hb ihb hΔ
    exact Templates.sandbox_compatible hh.erase hi.erase (ihb hΔ)
  case capture =>
    rename_i hc hi ho hd hb ihc ihb hΔ
    exact .app (Templates.captured_compatible hc.left_typed.ambient_wf.erase
      (hc.left_typed.result_wf hΔ).record_row.erase hi.erase hd.erase (ihb hΔ)) (ihc hΔ)
  case run =>
    rename_i hm hp hc ihm ihp ihc hΔ
    have hw := hm.left_typed.result_wf hΔ
    exact .app (.app (Templates.run_compatible hm.left_typed.ambient_wf.erase
      (hp.left_typed.result_wf hΔ).record_row.erase hw.module_imports.erase hw.module_exports.erase
      (ihc hΔ)) (ihm hΔ)) (ihp hΔ)
  case link =>
    rename_i hp hm hc hd ihp ihm ihc hΔ
    have hw := hm.left_typed.result_wf hΔ
    exact .app (.app (Templates.link_compatible hp.left_typed.ambient_wf.erase
      (hp.left_typed.result_wf hΔ).record_row.erase hw.module_imports.erase hw.module_exports.erase
      hd.erase (ihc hΔ)) (ihp hΔ)) (ihm hΔ)
  case provide =>
    rename_i hp hm hc hj hk hd ihp ihm ihc hΔ
    exact .app (.app (Templates.provide_compatible hp.left_typed.ambient_wf.erase
      (hp.left_typed.result_wf hΔ).record_row.erase hj.erase hk.erase
      (hm.left_typed.result_wf hΔ).module_exports.erase hd.erase (ihc hΔ)) (ihp hΔ)) (ihm hΔ)
  case complete =>
    rename_i Δ h m M o hm ihm hΔ
    have hc : ∀ h, Target.WellFormed Δ.erase h →
        Target.Compatible Target.LogicalRelation.OpenRel Δ.erase h (.close (.lam (.record .empty) (.ix 0))) (.close (.lam (.record .empty) (.ix 0)))
          (.arr (.record .empty) (.record .empty)) := by
      intro h hh
      exact .box (.unit hh) (.lam (.record .empty)
        (.snd (.query (.prod .unit (.record .empty)))))
    exact .app (.app (Templates.run_compatible hm.left_typed.ambient_wf.erase .empty .empty
      (hm.left_typed.result_wf hΔ).module_exports.erase hc) (ihm hΔ)) (.record (.nil hm.left_typed.ambient_wf.erase))
  case moduleVal =>
    rename_i hh vc vC hc hi ho hd hb ihc ihb hΔ
    exact Templates.module_value_compatible hh.erase hi.erase (ihc hΔ)
      (Term.erase_value _ vc) (Term.erase_value _ vC) hd.erase (ihb hΔ) hΔ.erase
  case resid =>
    rename_i m M Δ j k o h saved SAVED vm vM hm hs hj hk hd ihm ihs hΔ
    apply Target.Compatible.hole
      (HasType.erase (Compatible.left_typed (.resid vm vM hm hs hj hk hd)) hΔ)
      (HasType.erase (Compatible.right_typed (.resid vm vM hm hs hj hk hd)) hΔ)
    intro θ hθ n ν N hν
    have hmrel := (ihm hΔ).logical (by intros; assumption) hΔ.erase
    have hsrel := (ihs hΔ).logical (by intros; assumption) hΔ.erase
    have hmv := Term.erase_value _ vm
    have hMv := Term.erase_value _ vM
    have hmods := hmrel.values hmv hMv hθ (n := n)
    have hargs := hsrel θ hθ n ν N hν
    have hres := Templates.residual_form_logical
      (hj.erase.subst hθ.respects) (hk.erase.subst hθ.respects)
      ((hm.left_typed.result_wf hΔ).module_exports.erase.subst hθ.respects)
      (hd.erase.subst hθ.respects) hmods hargs hν.left.1 hν.right.1
      (by intro hv; simpa only [Target.Value,Target.Term.isValue_subst] using Term.erase_value _ hv)
      (by intro hv; simpa only [Target.Value,Target.Term.isValue_subst] using Term.erase_value _ hv)
    simpa only [Templates.residualForm,Term.erase,show m.isValue = true from vm,
      show M.isValue = true from vM,Bool.true_and,apply_ite,Target.Term.subst,
      Ty.erase,Target.Ty.subst,Templates.residual,Templates.residualBody,
      Target.Term.close,Target.Term.ix] using hres
  case invoke => rename_i hm hp ihm ihp hΔ; exact .app (ihm hΔ) (ihp hΔ)
  case value =>
    rename_i hv hV he hh ih hΔ
    exact .value (Term.erase_value _ hv) (Term.erase_value _ hV) (ih hΔ) hh.erase
  case nil => rename_i hh hΔ; exact .nil hh.erase
  case cons => rename_i he hf hd ihe ihf hΔ; exact .cons (ihe hΔ) (ihf hΔ) hd.erase
  case closed => rename_i _ _ hc ih hΔ h hh; exact .box (.unit hh) (ih hΔ)
  all_goals
    rename_i heq hw ih hΔ
    exact .conv (ih hΔ) heq.erase hw.erase

end LeanSce.Source

/-! ## Context Observation -/

namespace LeanSce.Source
open LeanSce.Target.LogicalRelation

private theorem erased_identity : Subst.erase Subst.id = Target.Subst.id := by
  funext k i
  cases k <;> rfl

theorem GroundType.erase (hg : GroundType g) : Target.GroundType g.erase := by
  cases hg <;> constructor

theorem Related.ground_erase (hr : Related v V) (ht : HasType Δ h v g)
    (hg : GroundType g) : V = v.erase := by
  have hs := ht.value_shape hr.values.1
  cases hg with
  | unit => cases hs; cases hr; rfl
  | int => obtain ⟨_,rfl⟩ := hs; cases hr; rfl
  | bool => obtain ⟨_,rfl⟩ := hs; cases hr; rfl
  | string => obtain ⟨_,rfl⟩ := hs; cases hr; rfl

theorem Related.ground_unique (hr : Related v V) (hR : Related w V)
    (ht : HasType Δ h v g) (hT : HasType Δ h w g) (hg : GroundType g) : v = w := by
  have hs := ht.value_shape hr.values.1
  have hS := hT.value_shape hR.values.1
  cases hg with
  | unit => cases hs; cases hS; rfl
  | int => obtain ⟨_,rfl⟩ := hs; obtain ⟨_,rfl⟩ := hS; cases hr; cases hR; rfl
  | bool => obtain ⟨_,rfl⟩ := hs; obtain ⟨_,rfl⟩ := hS; cases hr; cases hR; rfl
  | string => obtain ⟨_,rfl⟩ := hs; obtain ⟨_,rfl⟩ := hS; cases hr; cases hR; rfl

/-- Ground observation reflection, parameterized only by the exact execution
    theorems. The public wrapper supplies their proved instances. -/
theorem observation_reflection_of_correspondence
    (hterm : Goals.TerminationCorrespondence) (hdiv : Goals.DivergenceCorrespondence)
    (hg : GroundType g) (hν : ValueType .empty ν h)
    (he : HasType .empty h e g) (hE : HasType .empty h E g)
    (hr : Target.ObservationEq ν.erase e.erase E.erase) : ObservationEq ν e E := by
  have hcorr (e : Expr) (he : HasType .empty h e g) :=
    hterm .empty h g e ν e.erase ν.erase Subst.id .empty he .canonical
      (Closing.empty Subst.id) (by simpa only [Ty.subst_id] using hν) (Related.erase ν hν.1)
  have hl := hcorr e he
  have hright := hcorr E hE
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
  · have dl := hdiv .empty h g e ν e.erase ν.erase Subst.id .empty he .canonical
      (Closing.empty Subst.id) (by simpa only [Ty.subst_id] using hν) (Related.erase ν hν.1)
    have dr := hdiv .empty h g E ν E.erase ν.erase Subst.id .empty hE .canonical
      (Closing.empty Subst.id) (by simpa only [Ty.subst_id] using hν) (Related.erase ν hν.1)
    simp only [Term.subst_id,erased_identity,Target.Term.subst_id] at dl dr
    exact dl.trans (hr.2.trans dr.symm)

/-- Logical equivalence of the canonical artifacts covers every source context,
    including stored certificates and residuals crossing the value boundary. -/
theorem erasure_logical_contextual_of_correspondence
    (hterm : Goals.TerminationCorrespondence) (hdiv : Goals.DivergenceCorrespondence)
    (he : HasType Δ h e a) (hE : HasType Δ h E a) (hΔ : Context.Valid Δ)
    (hr : Target.LogicalRelation.OpenRel Δ.erase h.erase e.erase E.erase a.erase) :
    ContextualEq Δ h a e E := by
  intro θ hθ H g ν c C hg hν hc
  have heθ := he.subst hΔ hθ.respects
  have hEθ := hE.subst hΔ hθ.respects
  have hclosed : ∀ n μ Μ, ValRel n (h.subst θ).erase μ Μ →
      ExprRel n (a.subst θ).erase (μ,(e.subst θ).erase) (Μ,(E.subst θ).erase) := by
    simpa only [Ty.erase_subst,Term.erase_subst] using hr (Subst.erase θ) hθ.erase
  have hholes : ∀ Δ H x X b,
      HoleAt (h.subst θ) (a.subst θ) (e.subst θ) (E.subst θ) Δ H x X b →
      Target.LogicalRelation.OpenRel Δ.erase H.erase x.erase X.erase b.erase := by
    intro Δ H x X b hh
    obtain ⟨rfl,rfl,rfl,rfl⟩ := hh
    exact Target.LogicalRelation.closed_hole_logical (heθ.erase .empty) (hEθ.erase .empty)
      hclosed _ _ _ _ _ ⟨rfl,rfl,rfl,rfl⟩
  have hctx := (hc.erase_context hholes .empty).logical (by intros; assumption) .empty
  have hνt : Target.ValueType .empty ν.erase H.erase :=
    ⟨Term.erase_value ν hν.1,hν.2.erase .empty⟩
  have hob : Target.ObservationEq ν.erase c.erase C.erase := by
    apply Target.LogicalRelation.ground_adequacy (hg := hg.erase) (hν := hνt)
      (he := hc.left_typed.erase .empty) (hE := hc.right_typed.erase .empty)
    intro n
    simpa only [Target.Ty.subst_id,Target.Term.subst_id] using
      hctx Target.Subst.id (Target.Closing.empty Target.Subst.id) n ν.erase ν.erase
        (by simpa only [Target.Ty.subst_id] using hνt.logical n)
  exact observation_reflection_of_correspondence hterm hdiv hg hν hc.left_typed hc.right_typed hob

end LeanSce.Source

/-! ## Context Correctness -/

namespace LeanSce.Source

/-- Logical equivalence of compiled artifacts reflects to every typed source
    observation context, including runtime code and value-restricted positions. -/
theorem erasure_logical_contextual
    (he : HasType Δ h e a) (hE : HasType Δ h E a) (hΔ : Context.Valid Δ)
    (hr : Target.LogicalRelation.OpenRel Δ.erase h.erase e.erase E.erase a.erase) :
    ContextualEq Δ h a e E :=
  erasure_logical_contextual_of_correspondence termination_correspondence divergence_correspondence
    he hE hΔ hr

end LeanSce.Source

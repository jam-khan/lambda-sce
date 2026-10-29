import LeanSce.Source.Definitions.Elaboration
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.CanonicalForms
import LeanSce.Source.Metatheory.WellFormedness
import LeanSce.Target.Metatheory.Typing
import LeanSce.Target.Metatheory.Values

/-!
# Source / Elaboration / Typing

Proofs and supporting constructions for typing.
-/

/-! ## Correspondence Values -/

namespace LeanSce.Source
open LeanSce.Target (TermSort)

private theorem target_fields_value_iff (fs : Target.Fields) :
    Target.Value fs ↔ ∀ p ∈ fs.toList, Target.Value p.2 := by
  cases fs with
  | nil => simp [Target.Value,Target.Term.isValue,Target.Term.toList]
  | cons l v rest =>
    simp only [Target.Value,Target.Term.isValue,Bool.and_eq_true,Target.Term.toList,List.mem_cons,
      forall_eq_or_imp]
    exact and_congr Iff.rfl (target_fields_value_iff rest)
termination_by sizeOf fs

private theorem target_fields_value_perm {fs gs : Target.Fields} (hv : Target.Value fs)
    (hp : fs.toList.Perm gs.toList) : Target.Value gs := by
  apply (target_fields_value_iff gs).mpr
  intro p hm
  exact (target_fields_value_iff fs).mp hv p (hp.mem_iff.mpr hm)

/-- Runtime correspondence relates values; stored code is related separately. -/
theorem Related.values (hr : Related v V) : Value v ∧ Target.Value V := by
  apply Related.rec
    (motive_1 := fun e E _ => Value e → Target.Value E)
    (motive_2 := fun v V _ => Value v ∧ Target.Value V)
    (t := hr)
  all_goals intros
  all_goals intros
  all_goals try simp_all only [Value,Term.isValue,Target.Value,Target.Term.isValue,
    Bool.and_eq_true,Bool.false_eq_true,false_implies]
  case canonical => rename_i hv; exact Term.erase_value _ hv
  case record =>
    rename_i fs gs hs hr hp ih
    exact ⟨True.intro,target_fields_value_perm ih.2 hp⟩
  all_goals simp_all

/-- A value's runtime elaboration is a target value. -/
theorem Elaborates.value_preservation (he : Elaborates e E) (hv : Value e) : Target.Value E := by
  apply Elaborates.rec
    (motive_1 := fun e E _ => Value e → Target.Value E)
    (motive_2 := fun v V _ => Value v ∧ Target.Value V)
    (t := he)
  all_goals intros
  all_goals intros
  all_goals try simp_all only [Value,Term.isValue,Target.Value,Target.Term.isValue,
    Bool.and_eq_true,Bool.false_eq_true,false_implies]
  case canonical => rename_i hv; exact Term.erase_value _ hv
  case record =>
    rename_i fs gs hs hr hp ih
    exact ⟨True.intro,target_fields_value_perm ih.2 hp⟩
  all_goals simp_all

end LeanSce.Source

/-! ## Elaboration Inversion -/

namespace LeanSce.Source

theorem Elaborates.unit_inv (he : Elaborates .unit E) : E = .unit := by
  cases he with
  | canonical => rfl
  | value hr => cases hr; rfl

theorem Elaborates.nil_inv (he : Elaborates .nil E) : E = .nil := by
  cases he with
  | canonical => rfl
  | value hr => cases hr; rfl

theorem Elaborates.cons_inv (he : Elaborates (.cons l e fs) E) :
    ∃ e' fs', E = .cons l e' fs' ∧ Elaborates e e' ∧ Elaborates fs fs' := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr with | cons hx hf => exact ⟨_,_,rfl,.value hx,.value hf⟩
  | cons hx hf => exact ⟨_,_,rfl,hx,hf⟩

end LeanSce.Source

/-! ## Template Typing -/

namespace LeanSce.Source.Templates
open LeanSce.Target

theorem letIn_typed (he : Target.HasType Δ h e a)
    (hb : Target.HasType Δ (.prod h a) body b) :
    Target.HasType Δ h (.letIn e body) b :=
  .box (.pair (.query he.ambient_wf) he) hb

theorem sandbox_typed (hh : Target.WellFormed Δ h) (hi : Target.WellFormed Δ i)
    (hb : Target.HasType Δ (.record i) body (.record o)) :
    Target.HasType Δ h (sandbox i body) (.arr (.record i) (.record o)) := by
  apply Target.HasType.box (.unit hh)
  apply Target.HasType.lam (.record hi)
  exact .box (.snd (.query (.prod .unit (.record hi)))) hb

theorem captured_typed (hh : Target.WellFormed Δ h)
    (hc : Target.WellFormed Δ c) (hi : Target.WellFormed Δ i)
    (hd : Target.Disjoint Δ c i)
    (hb : Target.HasType Δ (.record (.union c i)) body (.record o)) :
    Target.HasType Δ h (captured c i body)
      (.arr (.record c) (.arr (.record i) (.record o))) := by
  apply Target.HasType.box (.unit hh)
  apply Target.HasType.lam (.record hc)
  apply Target.HasType.lam (.record hi)
  have hw : Target.WellFormed Δ (.prod (.prod .unit (.record c)) (.record i)) :=
    .prod (.prod .unit (.record hc)) (.record hi)
  exact .box (.merge (.snd (.fst (.query hw))) (.snd (.query hw)) hd) hb

theorem run_typed (hh : Target.WellFormed Δ h)
    (hp : Target.WellFormed Δ p) (hi : Target.WellFormed Δ i)
    (ho : Target.WellFormed Δ o)
    (hc : ∀ h, Target.WellFormed Δ h →
      Target.HasType Δ h cd (.arr (.record p) (.record i))) :
    Target.HasType Δ h (run p i o cd)
      (.arr (.arr (.record i) (.record o)) (.arr (.record p) (.record o))) := by
  apply Target.HasType.box (.unit hh)
  apply Target.HasType.lam (.arr (.record hi) (.record ho))
  apply Target.HasType.lam (.record hp)
  have hw : Target.WellFormed Δ (.prod (.prod .unit (.arr (.record i) (.record o))) (.record p)) :=
    .prod (.prod .unit (.arr (.record hi) (.record ho))) (.record hp)
  exact .app (.snd (.fst (.query hw))) (.app (hc _ hw) (.snd (.query hw)))

theorem residualBody_typed (hj : Target.WellFormed Δ j)
    (hk : Target.WellFormed Δ k) (ho : Target.WellFormed Δ o)
    (hd : Target.Disjoint Δ j k) :
    Target.HasType Δ
      (.prod (.prod (.arr (.record (.union j k)) (.record o)) (.record j)) (.record k))
      residualBody (.record o) := by
  have hw : Target.WellFormed Δ
      (.prod (.prod (.arr (.record (.union j k)) (.record o)) (.record j)) (.record k)) :=
    .prod (.prod (.arr (.record (.union hj hk hd)) (.record ho)) (.record hj)) (.record hk)
  exact .app (.fst (.fst (.query hw)))
    (.merge (.snd (.fst (.query hw))) (.snd (.query hw)) hd)

theorem residual_typed (hh : Target.WellFormed Δ h)
    (hj : Target.WellFormed Δ j) (hk : Target.WellFormed Δ k)
    (ho : Target.WellFormed Δ o) (hd : Target.Disjoint Δ j k) :
    Target.HasType Δ h (residual j k o)
      (.arr (.arr (.record (.union j k)) (.record o))
        (.arr (.record j) (.arr (.record k) (.record o)))) := by
  apply Target.HasType.box (.unit hh)
  apply Target.HasType.lam (.arr (.record (.union hj hk hd)) (.record ho))
  apply Target.HasType.lam (.record hj)
  have hw : Target.WellFormed Δ
      (.prod (.prod .unit (.arr (.record (.union j k)) (.record o))) (.record j)) :=
    .prod (.prod .unit (.arr (.record (.union hj hk hd)) (.record ho))) (.record hj)
  apply Target.HasType.box (.pair (.snd (.fst (.query hw))) (.snd (.query hw)))
  exact .lam (.record hk) (residualBody_typed hj hk ho hd)

theorem provide_typed (hh : Target.WellFormed Δ h)
    (hp : Target.WellFormed Δ p) (hj : Target.WellFormed Δ j)
    (hk : Target.WellFormed Δ k) (ho : Target.WellFormed Δ o)
    (hd : Target.Disjoint Δ j k)
    (hc : ∀ h, Target.WellFormed Δ h →
      Target.HasType Δ h cd (.arr (.record p) (.record j))) :
    Target.HasType Δ h (provide p j k o cd)
      (.arr (.record p) (.arr (.arr (.record (.union j k)) (.record o))
        (.arr (.record k) (.record o)))) := by
  apply Target.HasType.box (.unit hh)
  apply Target.HasType.lam (.record hp)
  apply Target.HasType.lam (.arr (.record (.union hj hk hd)) (.record ho))
  have hw : Target.WellFormed Δ
      (.prod (.prod .unit (.record p)) (.arr (.record (.union j k)) (.record o))) :=
    .prod (.prod .unit (.record hp)) (.arr (.record (.union hj hk hd)) (.record ho))
  apply letIn_typed (.app (hc _ hw) (.snd (.fst (.query hw))))
  have hw' : Target.WellFormed Δ
      (.prod (.prod (.prod .unit (.record p)) (.arr (.record (.union j k)) (.record o))) (.record j)) :=
    .prod hw (.record hj)
  apply Target.HasType.box (.pair (.snd (.fst (.query hw'))) (.snd (.query hw')))
  exact .lam (.record hk) (residualBody_typed hj hk ho hd)

theorem link_typed (hh : Target.WellFormed Δ h)
    (hp : Target.WellFormed Δ p) (hi : Target.WellFormed Δ i)
    (ho : Target.WellFormed Δ o) (hd : Target.Disjoint Δ p o)
    (hc : ∀ h, Target.WellFormed Δ h →
      Target.HasType Δ h cd (.arr (.record p) (.record i))) :
    Target.HasType Δ h (link p i o cd)
      (.arr (.record p) (.arr (.arr (.record i) (.record o)) (.record (.union p o)))) := by
  apply Target.HasType.box (.unit hh)
  apply Target.HasType.lam (.record hp)
  apply Target.HasType.lam (.arr (.record hi) (.record ho))
  have hw : Target.WellFormed Δ
      (.prod (.prod .unit (.record p)) (.arr (.record i) (.record o))) :=
    .prod (.prod .unit (.record hp)) (.arr (.record hi) (.record ho))
  apply letIn_typed (.app (hc _ hw) (.snd (.fst (.query hw))))
  have hw' : Target.WellFormed Δ
      (.prod (.prod (.prod .unit (.record p)) (.arr (.record i) (.record o))) (.record i)) :=
    .prod hw (.record hi)
  apply letIn_typed (.app (.snd (.fst (.query hw'))) (.snd (.query hw')))
  have hw'' : Target.WellFormed Δ
      (.prod (.prod (.prod (.prod .unit (.record p)) (.arr (.record i) (.record o))) (.record i)) (.record o)) :=
    .prod hw' (.record ho)
  exact .merge (.snd (.fst (.fst (.fst (.query hw''))))) (.snd (.query hw'')) hd

theorem module_value_typed (hh : Target.WellFormed Δ h)
    (hi : Target.WellFormed Δ i) (hc : Target.HasType Δ .unit cap (.record c))
    (hvc : Target.Value cap) (hd : Target.Disjoint Δ c i)
    (hb : Target.HasType Δ (.record (.union c i)) body (.record o))
    (hΔ : Target.Context.Valid Δ) :
    Target.HasType Δ h
      (.clo (.pair .unit cap) (.record i) (.box (.merge (.ix 1) (.ix 0)) body))
      (.arr (.record i) (.record o)) := by
  have wc := (hc.result_wf hΔ).record_row
  apply Target.HasType.clo hh (.record hi) (show Target.Value (.pair .unit cap) from by
    simpa [Target.Value,Target.Term.isValue] using hvc)
    (.pair (.unit .unit) hc)
  have hw : Target.WellFormed Δ (.prod (.prod .unit (.record c)) (.record i)) :=
    .prod (.prod .unit (.record wc)) (.record hi)
  exact .box (.merge (.snd (.fst (.query hw))) (.snd (.query hw)) hd) hb

theorem residual_value_typed (hh : Target.WellFormed Δ h)
    (hj : Target.WellFormed Δ j) (hk : Target.WellFormed Δ k)
    (ho : Target.WellFormed Δ o) (hd : Target.Disjoint Δ j k)
    (hm : Target.HasType Δ .unit m (.arr (.record (.union j k)) (.record o)))
    (hs : Target.HasType Δ .unit saved (.record j))
    (hvm : Target.Value m) (hvs : Target.Value saved) :
    Target.HasType Δ h (.clo (.pair m saved) (.record k) residualBody)
      (.arr (.record k) (.record o)) := by
  apply Target.HasType.clo hh (.record hk)
    (show Target.Value (.pair m saved) from Bool.and_eq_true_iff.mpr ⟨hvm,hvs⟩)
    (.pair hm hs)
  exact residualBody_typed hj hk ho hd

end LeanSce.Source.Templates

/-! ## Typing Erasure Properties -/

namespace LeanSce.Source

@[simp] theorem Arg.erase_kind (u : Arg) : u.erase.kind = u.kind := by cases u <;> rfl

theorem Arg.WellFormed.erase {u : Arg} (hu : u.WellFormed Δ) : u.erase.WellFormed Δ.erase := by
  cases u <;> exact LeanSce.Source.WellFormed.erase hu

@[simp] theorem Ty.erase_lookup (r : Row) (l : String) :
    r.erase.lookup l = (r.lookup l).map Ty.erase := by
  cases r with
  | rvar => simp [Ty.erase,Ty.lookup,Target.Ty.lookup]
  | empty => simp [Ty.erase,Ty.lookup,Target.Ty.lookup]
  | field k a => by_cases h : l = k <;> simp [Ty.erase,Ty.lookup,Target.Ty.lookup,h]
  | union r s =>
    simp only [Ty.erase,Ty.lookup,Target.Ty.lookup,Ty.erase_lookup r,Ty.erase_lookup s]
    cases r.lookup l <;> rfl

@[simp] theorem Ty.erase_select (r : Row) (ls : List String) :
    (r.select ls).erase = r.erase.select ls := by
  cases r with
  | rvar => simp [Ty.select,Ty.erase,Target.Ty.select]
  | empty => simp [Ty.select,Ty.erase,Target.Ty.select]
  | field l a => by_cases hl : l ∈ ls <;> simp [Ty.select,Ty.erase,Target.Ty.select,hl]
  | union r s => simp only [Ty.select,Ty.erase,Target.Ty.select,Ty.erase_select r,Ty.erase_select s]

@[simp] theorem Ty.erase_drop (r : Row) (ls : List String) :
    (r.drop ls).erase = r.erase.drop ls := by
  cases r with
  | rvar => simp [Ty.drop,Ty.erase,Target.Ty.drop]
  | empty => simp [Ty.drop,Ty.erase,Target.Ty.drop]
  | field l a => by_cases hl : l ∈ ls <;> simp [Ty.drop,Ty.erase,Target.Ty.drop,hl]
  | union r s => simp only [Ty.drop,Ty.erase,Target.Ty.drop,Ty.erase_drop r,Ty.erase_drop s]

@[simp] theorem Ty.erase_relabel (r : Row) (old new : String) :
    (r.relabel old new).erase = r.erase.relabel old new := by
  cases r with
  | rvar => simp [Ty.relabel,Ty.erase,Target.Ty.relabel]
  | empty => simp [Ty.relabel,Ty.erase,Target.Ty.relabel]
  | field => simp [Ty.relabel,Ty.erase,Target.Ty.relabel]
  | union r s => simp only [Ty.relabel,Ty.erase,Target.Ty.relabel,Ty.erase_relabel r,Ty.erase_relabel s]

theorem Absent.erase (ha : Absent l a) : Target.Absent l a.erase := by
  induction ha <;> simp only [Ty.erase] <;> constructor <;> assumption

theorem Unique.erase (hu : Unique l a b) : Target.Unique l a.erase b.erase := by
  induction hu with
  | here => exact .here
  | left _ ha ih => exact .left ih ha.erase
  | right ha _ ih => exact .right ha.erase ih

end LeanSce.Source

/-! ## Erasure Typing -/

namespace LeanSce.Source

private theorem erasureTyping_validAll (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.all k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | all hf hg _ => exact .extend hΔ hf hg

private theorem erasureTyping_validEx (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.ex k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | ex hf hg _ => exact .extend hΔ hf hg

/-- The canonical compiler preserves typing throughout checked and runtime syntax. -/
theorem HasType.erase (ht : HasType Δ h e a) : Context.Valid Δ →
    Target.HasType Δ.erase h.erase e.erase a.erase := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ => Context.Valid Δ → Target.HasType Δ.erase h.erase e.erase a.erase)
    (motive_2 := fun Δ h fs r _ => Context.Valid Δ → Target.FieldsType Δ.erase h.erase fs.erase r.erase)
    (motive_3 := fun Δ a b cd _ => Context.Valid Δ → ∀ h, Target.WellFormed Δ.erase h →
      Target.HasType Δ.erase h cd.erase (.arr a.erase b.erase))
    (t := ht)
  all_goals intros
  all_goals intros
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
    have hsel := Target.HasType.take (ih hΔ) hn (fun l hm => by
      obtain ⟨a,ha⟩ := hl l hm
      exact ⟨a.erase,by simp [ha]⟩)
    simpa only [Term.erase,Ty.erase,Ty.erase_select] using hsel
  case drop =>
    rename_i hx hn hl ih hΔ
    have hdrop := Target.HasType.drop (ih hΔ) hn (fun l hm => by
      obtain ⟨a,ha⟩ := hl l hm
      exact ⟨a.erase,by simp [ha]⟩)
    simpa only [Term.erase,Ty.erase,Ty.erase_drop] using hdrop
  case relabel =>
    rename_i Δ h x r l a k hx hl hn hd ih hΔ
    have hr := Target.HasType.relabel (a := a.erase) (ih hΔ) (by simp [hl]) hn
      (by simpa only [Ty.erase,Ty.erase_drop] using hd.erase)
    simpa only [Term.erase,Ty.erase,Ty.erase_relabel] using hr
  case tlam =>
    rename_i hw hh hb ih hΔ
    have hvalid := erasureTyping_validAll hΔ hw
    apply Target.HasType.tlam hw.erase hh.erase
    simpa using ih hvalid
  case tapp =>
    rename_i hx hk hu hg ih hΔ
    simpa only [Term.erase,Ty.erase_open] using Target.HasType.tapp (ih hΔ)
      (by simpa using hk) hu.erase (by simpa using hg.erase)
  case pack =>
    rename_i hw hk hu hg hx ih hΔ
    exact .pack hw.erase (by simpa using hk) hu.erase (by simpa using hg.erase)
      (by simpa using ih hΔ)
  case unpack =>
    rename_i hx wb hb ihx ihb hΔ
    have hw := hx.result_wf hΔ
    have hvalid := erasureTyping_validEx hΔ hw
    exact .unpack (ihx hΔ) wb.erase (by simpa only [Context.erase_extend,Ty.erase,Ty.erase_rename] using ihb hvalid)
  case fold =>
    rename_i hw hx ih hΔ
    exact .fold hw.erase (by simpa using ih hΔ)
  case unfold =>
    rename_i hx ih hΔ
    simpa only [Term.erase,Ty.erase_open,Ty.erase,Arg.erase] using Target.HasType.unfold (ih hΔ)
  case add => rename_i ihx ihy hΔ; exact .add (ihx hΔ) (ihy hΔ)
  case eqInt => rename_i ihx ihy hΔ; exact .eqInt (ihx hΔ) (ihy hΔ)
  case showInt => rename_i ih hΔ; exact .showInt (ih hΔ)
  case concat => rename_i ihx ihy hΔ; exact .concat (ihx hΔ) (ihy hΔ)
  case ite => rename_i ihc ihx ihy hΔ; exact .ite (ihc hΔ) (ihx hΔ) (ihy hΔ)
  case clo =>
    rename_i hh wa vc hc hb ihc ihb hΔ
    exact .clo hh.erase wa.erase (Term.erase_value _ vc) (ihc hΔ) (ihb hΔ)
  case rclo =>
    rename_i hh wa wb vc hc hb ihc ihb hΔ
    exact .rclo hh.erase wa.erase wb.erase (Term.erase_value _ vc) (ihc hΔ) (ihb hΔ)
  case tclo =>
    rename_i hh hw vc hc hb ihc ihb hΔ
    have hvalid := erasureTyping_validAll hΔ hw
    exact .tclo hh.erase hw.erase (Term.erase_value _ vc) (ihc hΔ) (by simpa using ihb hvalid)
  case letVal =>
    rename_i wa he hb ihe ihb hΔ
    exact Templates.letIn_typed (ihe hΔ) (ihb hΔ)
  case view =>
    rename_i he hc ihe ihc hΔ
    exact .app (ihc hΔ _ he.ambient_wf.erase) (ihe hΔ)
  case module =>
    rename_i hh hi ho hb ihb hΔ
    exact Templates.sandbox_typed hh.erase hi.erase (ihb hΔ)
  case capture =>
    rename_i hc hi ho hd hb ihc ihb hΔ
    exact .app (Templates.captured_typed hc.ambient_wf.erase
      (hc.result_wf hΔ).record_row.erase hi.erase hd.erase (ihb hΔ)) (ihc hΔ)
  case run =>
    rename_i hm hp hc ihm ihp ihc hΔ
    have hw := hm.result_wf hΔ
    exact .app (.app (Templates.run_typed hm.ambient_wf.erase
      (hp.result_wf hΔ).record_row.erase hw.module_imports.erase hw.module_exports.erase
      (ihc hΔ)) (ihm hΔ)) (ihp hΔ)
  case link =>
    rename_i hp hm hc hd ihp ihm ihc hΔ
    have hw := hm.result_wf hΔ
    exact .app (.app (Templates.link_typed hp.ambient_wf.erase
      (hp.result_wf hΔ).record_row.erase hw.module_imports.erase hw.module_exports.erase
      hd.erase (ihc hΔ)) (ihp hΔ)) (ihm hΔ)
  case provide =>
    rename_i hp hm hc hj hk hd ihp ihm ihc hΔ
    exact .app (.app (Templates.provide_typed hp.ambient_wf.erase
      (hp.result_wf hΔ).record_row.erase hj.erase hk.erase
      (hm.result_wf hΔ).module_exports.erase hd.erase (ihc hΔ)) (ihp hΔ)) (ihm hΔ)
  case complete =>
    rename_i Δ h m o hm ihm hΔ
    have hc : ∀ h, Target.WellFormed Δ.erase h →
        Target.HasType Δ.erase h (.close (.lam (.record .empty) (.ix 0)))
          (.arr (.record .empty) (.record .empty)) := by
      intro h hh
      exact .box (.unit hh) (.lam (.record .empty)
        (.snd (.query (.prod .unit (.record .empty)))))
    exact .app (.app (Templates.run_typed hm.ambient_wf.erase .empty .empty
      (hm.result_wf hΔ).module_exports.erase hc) (ihm hΔ)) (.record (.nil hm.ambient_wf.erase))
  case moduleVal =>
    rename_i hh vc hc hi ho hd hb ihc ihb hΔ
    exact Templates.module_value_typed hh.erase hi.erase (ihc hΔ)
      (Term.erase_value _ vc) hd.erase (ihb hΔ) hΔ.erase
  case resid =>
    rename_i m Δ j k o h saved vm hm hs hj hk hd ihm ihs hΔ
    have ho := (hm.result_wf hΔ).module_exports.erase
    cases hvs : saved.isValue with
    | false =>
      simp only [Term.erase,show m.isValue = true from vm,hvs,Bool.true_and]
      exact .app (.app (Templates.residual_typed hs.ambient_wf.erase hj.erase hk.erase ho hd.erase)
        ((ihm hΔ).value_reambient (Term.erase_value _ vm) _ hs.ambient_wf.erase)) (ihs hΔ)
    | true =>
      simp only [Term.erase,show m.isValue = true from vm,hvs,Bool.true_and,↓reduceIte]
      exact Templates.residual_value_typed hs.ambient_wf.erase hj.erase hk.erase ho hd.erase
        (ihm hΔ) ((ihs hΔ).value_reambient (Term.erase_value _ hvs) _ .unit)
        (Term.erase_value _ vm) (Term.erase_value _ hvs)
  case invoke => rename_i hm hp ihm ihp hΔ; exact .app (ihm hΔ) (ihp hΔ)
  case value =>
    rename_i hv he hh ih hΔ
    exact .value (Term.erase_value _ hv) (ih hΔ) hh.erase
  case nil => rename_i hh hΔ; exact .nil hh.erase
  case cons => rename_i he hf hd ihe ihf hΔ; exact .cons (ihe hΔ) (ihf hΔ) hd.erase
  case closed => rename_i _ hc ih hΔ h hh; exact .box (.unit hh) (ih hΔ)
  all_goals
    rename_i heq hw ih hΔ
    exact .conv (ih hΔ) heq.erase hw.erase

/-- Erasing a stored closed certificate is valid under every caller ambient. -/
theorem CertType.erase (hc : CertType Δ a b cd) (hΔ : Context.Valid Δ)
    (hh : Target.WellFormed Δ.erase h) :
    Target.HasType Δ.erase h cd.erase (.arr a.erase b.erase) := by
  cases hc with
  | closed _ ht => exact .box (.unit hh) (ht.erase hΔ)

/-- The field-list component of canonical elaboration typing. -/
theorem FieldsType.erase (hf : FieldsType Δ h fs r) (hΔ : Context.Valid Δ) :
    Target.FieldsType Δ.erase h.erase fs.erase r.erase :=
  ((HasType.record hf).erase hΔ).fields_inv hΔ.erase

end LeanSce.Source

/-! ## Elaboration Typing -/

namespace LeanSce.Source

private theorem elaborationTyping_validAll (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.all k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | all hf hg _ => exact .extend hΔ hf hg

private theorem elaborationTyping_validEx (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.ex k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | ex hf hg _ => exact .extend hΔ hf hg

/- The duplicate derivation parameter permits the canonical branch to reuse the
   independently proved compiler theorem. The wrapper supplies that same proof. -/
private theorem HasType.elaborates_aux (ht : HasType Δ h e a) :
    Context.Valid Δ → HasType Δ h e a → ∀ E, Elaborates e E →
      Target.HasType Δ.erase h.erase E a.erase := by
  apply HasType.rec
    (motive_1 := fun Δ h e a _ => Context.Valid Δ → HasType Δ h e a →
      ∀ E, Elaborates e E → Target.HasType Δ.erase h.erase E a.erase)
    (motive_2 := fun Δ h fs r _ => Context.Valid Δ → FieldsType Δ h fs r →
      ∀ Fs, Elaborates fs Fs → Target.FieldsType Δ.erase h.erase Fs r.erase)
    (motive_3 := fun Δ a b cd _ => Context.Valid Δ → CertType Δ a b cd →
      ∀ C, Elaborates cd C → ∀ h, Target.WellFormed Δ.erase h →
        Target.HasType Δ.erase h C (.arr a.erase b.erase))
    (t := ht)
  all_goals intros
  all_goals intros
  case query =>
    rename_i hh hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
  case unit =>
    rename_i hh hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr; exact .unit hh.erase
  case int =>
    rename_i hh hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr; exact .int hh.erase
  case bool =>
    rename_i hh hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr; exact .bool hh.erase
  case string =>
    rename_i hh hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr; exact .string hh.erase
  case pair =>
    rename_i hx hy ihx ihy hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr =>
      cases hr with | pair hX hY => exact .pair (ihx hΔ hx _ (.value hX)) (ihy hΔ hy _ (.value hY))
    | pair hX hY => exact .pair (ihx hΔ hx _ hX) (ihy hΔ hy _ hY)
  case fst =>
    rename_i hx ihx hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr =>
      cases hr
    | fst hX => exact .fst (ihx hΔ hx _ hX)
  case snd =>
    rename_i hx ihx hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr =>
      cases hr
    | snd hX => exact .snd (ihx hΔ hx _ hX)
  case box =>
    rename_i hx hy ihx ihy hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr =>
      cases hr
    | box hX hY => exact .box (ihx hΔ hx _ hX) (ihy hΔ hy _ hY)
  case app =>
    rename_i hx hy ihx ihy hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr =>
      cases hr
    | app hX hY => exact .app (ihx hΔ hx _ hX) (ihy hΔ hy _ hY)
  case tag =>
    rename_i hx ihx hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr =>
      cases hr with | tag hX => exact .tag (ihx hΔ hx _ (.value hX))
    | tag hX => exact .tag (ihx hΔ hx _ hX)
  case lam =>
    rename_i wa hb ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | lam hB => exact .lam wa.erase (ih hΔ hb _ hB)
  case recfn =>
    rename_i wa wb hb ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | recfn hB => exact .recfn wa.erase wb.erase (ih hΔ hb _ hB)
  case inl =>
    rename_i wb hx ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with | inl hX => exact .inl wb.erase (ih hΔ hx _ (.value hX))
    | inl hX => exact .inl wb.erase (ih hΔ hx _ hX)
  case inr =>
    rename_i wa hx ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with | inr hX => exact .inr wa.erase (ih hΔ hx _ (.value hX))
    | inr hX => exact .inr wa.erase (ih hΔ hx _ hX)
  case case =>
    rename_i hx hl hr ihx ihl ihr hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hv => cases hv
    | case hX hL hR => exact .case (ihx hΔ hx _ hX) (ihl hΔ hl _ hL) (ihr hΔ hr _ hR)
  case find =>
    rename_i hx hu ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | find hX => exact .find (ih hΔ hx _ hX) hu.erase
  case record =>
    rename_i hf ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with
      | record hF hp => exact .record ((ih hΔ hf _ (.value hF)).permute hp hΔ.erase)
    | record hF => exact .record (ih hΔ hf _ hF)
  case get =>
    rename_i hx hl ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | get hX => exact .get (ih hΔ hx _ hX) (by simp [hl])
  case merge =>
    rename_i hx hy hd ihx ihy hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | merge hX hY => exact .merge (ihx hΔ hx _ hX) (ihy hΔ hy _ hY) hd.erase
  case take =>
    rename_i hx hn hl ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | take hX =>
      have hh := Target.HasType.take (ih hΔ hx _ hX) hn (fun l hm => by
        obtain ⟨a,ha⟩ := hl l hm
        exact ⟨a.erase,by simp [ha]⟩)
      simpa only [Ty.erase,Ty.erase_select] using hh
  case drop =>
    rename_i hx hn hl ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | drop hX =>
      have hh := Target.HasType.drop (ih hΔ hx _ hX) hn (fun l hm => by
        obtain ⟨a,ha⟩ := hl l hm
        exact ⟨a.erase,by simp [ha]⟩)
      simpa only [Ty.erase,Ty.erase_drop] using hh
  case relabel =>
    rename_i Δ h x r l a k hx hl hn hd ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | relabel hX =>
      have hh := Target.HasType.relabel (a := a.erase) (ih hΔ hx _ hX) (by simp [hl]) hn
        (by simpa only [Ty.erase,Ty.erase_drop] using hd.erase)
      simpa only [Ty.erase,Ty.erase_relabel] using hh
  case tlam =>
    rename_i hw hh hb ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | tlam hB =>
      apply Target.HasType.tlam hw.erase hh.erase
      simpa using ih (elaborationTyping_validAll hΔ hw) hb _ hB
  case tapp =>
    rename_i hx hk hu hg ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | tapp hX =>
      simpa only [Ty.erase_open] using Target.HasType.tapp (ih hΔ hx _ hX)
        (by simpa using hk) hu.erase (by simpa using hg.erase)
  case pack =>
    rename_i hw hk hu hg hx ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with
      | pack hX => exact .pack hw.erase (by simpa using hk) hu.erase (by simpa using hg.erase) (by simpa using ih hΔ hx _ (.value hX))
    | pack hX => exact .pack hw.erase (by simpa using hk) hu.erase (by simpa using hg.erase) (by simpa using ih hΔ hx _ hX)
  case unpack =>
    rename_i hx wb hb ihx ihb hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | unpack hX hB =>
      exact .unpack (ihx hΔ hx _ hX) wb.erase
        (by simpa only [Context.erase_extend,Ty.erase,Ty.erase_rename] using
          ihb (elaborationTyping_validEx hΔ (hx.result_wf hΔ)) hb _ hB)
  case fold =>
    rename_i hw hx ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with
      | fold hX => exact .fold hw.erase (by simpa using ih hΔ hx _ (.value hX))
    | fold hX => exact .fold hw.erase (by simpa using ih hΔ hx _ hX)
  case unfold =>
    rename_i hx ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | unfold hX => simpa only [Ty.erase_open,Ty.erase,Arg.erase] using
        Target.HasType.unfold (ih hΔ hx _ hX)
  case add =>
    rename_i hx hy ihx ihy hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | prim hF =>
      obtain ⟨X,Fs,rfl,hX,hFs⟩ := hF.cons_inv
      obtain ⟨Y,Nil,rfl,hY,hNil⟩ := hFs.cons_inv
      cases hNil.nil_inv
      exact .add (ihx hΔ hx _ hX) (ihy hΔ hy _ hY)
  case eqInt =>
    rename_i hx hy ihx ihy hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | prim hF =>
      obtain ⟨X,Fs,rfl,hX,hFs⟩ := hF.cons_inv
      obtain ⟨Y,Nil,rfl,hY,hNil⟩ := hFs.cons_inv
      cases hNil.nil_inv
      exact .eqInt (ihx hΔ hx _ hX) (ihy hΔ hy _ hY)
  case concat =>
    rename_i hx hy ihx ihy hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | prim hF =>
      obtain ⟨X,Fs,rfl,hX,hFs⟩ := hF.cons_inv
      obtain ⟨Y,Nil,rfl,hY,hNil⟩ := hFs.cons_inv
      cases hNil.nil_inv
      exact .concat (ihx hΔ hx _ hX) (ihy hΔ hy _ hY)
  case showInt =>
    rename_i hx ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | prim hF =>
      obtain ⟨X,Nil,rfl,hX,hNil⟩ := hF.cons_inv
      cases hNil.nil_inv
      exact .showInt (ih hΔ hx _ hX)
  case ite =>
    rename_i hc hx hy ihc ihx ihy hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | ite hC hX hY => exact .ite (ihc hΔ hc _ hC) (ihx hΔ hx _ hX) (ihy hΔ hy _ hY)
  case clo =>
    rename_i hh wa vc hc hb ihc ihb hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with
      | clo hC hB => exact .clo hh.erase wa.erase hC.values.2 (ihc hΔ hc _ (.value hC)) (ihb hΔ hb _ hB)
  case rclo =>
    rename_i hh wa wb vc hc hb ihc ihb hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with
      | rclo hC hB => exact .rclo hh.erase wa.erase wb.erase hC.values.2 (ihc hΔ hc _ (.value hC)) (ihb hΔ hb _ hB)
  case tclo =>
    rename_i hh hw vc hc hb ihc ihb hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with
      | tclo hC hB => exact .tclo hh.erase hw.erase hC.values.2 (ihc hΔ hc _ (.value hC)) (by simpa using ihb (elaborationTyping_validAll hΔ hw) hb _ hB)
  case letVal =>
    rename_i wa hx hb ihx ihb hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | letVal hX hB => exact Templates.letIn_typed (ihx hΔ hx _ hX) (ihb hΔ hb _ hB)
  case view =>
    rename_i hx hc ihx ihc hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | view hC hX => exact .app (ihc hΔ hc _ hC _ hx.ambient_wf.erase) (ihx hΔ hx _ hX)
  case module =>
    rename_i hh hi ho hb ih hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | module hB => exact Templates.sandbox_typed hh.erase hi.erase (ih hΔ hb _ hB)
  case capture =>
    rename_i hc hi ho hd hb ihc ihb hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | capture hC hB =>
      exact .app (Templates.captured_typed hc.ambient_wf.erase
        (hc.result_wf hΔ).record_row.erase hi.erase hd.erase (ihb hΔ hb _ hB)) (ihc hΔ hc _ hC)
  case run =>
    rename_i hm hp hc ihm ihp ihc hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | run hC hM hP =>
      have hw := hm.result_wf hΔ
      exact .app (.app (Templates.run_typed hm.ambient_wf.erase
        (hp.result_wf hΔ).record_row.erase hw.module_imports.erase hw.module_exports.erase
        (ihc hΔ hc _ hC)) (ihm hΔ hm _ hM)) (ihp hΔ hp _ hP)
  case link =>
    rename_i hp hm hc hd ihp ihm ihc hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | link hC hP hM =>
      have hw := hm.result_wf hΔ
      exact .app (.app (Templates.link_typed hp.ambient_wf.erase
        (hp.result_wf hΔ).record_row.erase hw.module_imports.erase hw.module_exports.erase
        hd.erase (ihc hΔ hc _ hC)) (ihp hΔ hp _ hP)) (ihm hΔ hm _ hM)
  case provide =>
    rename_i hp hm hc hj hk hd ihp ihm ihc hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | provide hC hP hM =>
      exact .app (.app (Templates.provide_typed hp.ambient_wf.erase
        (hp.result_wf hΔ).record_row.erase hj.erase hk.erase
        (hm.result_wf hΔ).module_exports.erase hd.erase (ihc hΔ hc _ hC))
        (ihp hΔ hp _ hP)) (ihm hΔ hm _ hM)
  case complete =>
    rename_i Δ h m o hm ihm hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | complete hM =>
      have hc : ∀ h, Target.WellFormed Δ.erase h →
          Target.HasType Δ.erase h (.close (.lam (.record .empty) (.ix 0)))
            (.arr (.record .empty) (.record .empty)) := by
        intro h hh
        exact .box (.unit hh) (.lam (.record .empty)
          (.snd (.query (.prod .unit (.record .empty)))))
      exact .app (.app (Templates.run_typed hm.ambient_wf.erase .empty .empty
        (hm.result_wf hΔ).module_exports.erase hc) (ihm hΔ hm _ hM))
        (.record (.nil hm.ambient_wf.erase))
  case moduleVal =>
    rename_i hh vc hc hi ho hd hb ihc ihb hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with
      | moduleCaptured hC hB =>
        exact Templates.module_value_typed hh.erase hi.erase (ihc hΔ hc _ (.value hC))
          hC.values.2 hd.erase (ihb hΔ hb _ hB) hΔ.erase
      | moduleSandbox hB =>
        apply Target.HasType.clo (cap := .unit) hh.erase (.record hi.erase) rfl (.unit .unit)
        apply Target.HasType.box (.snd (.query (.prod .unit (.record hi.erase))))
        exact (ihb hΔ hb _ hB).ambient_convert _
          (.record (.trans .union_comm .union_empty)) (.record hi.erase)
  case resid =>
    rename_i m Δ j k o h saved vm hm hs hj hk hd ihm ihs hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr with
      | resid hM hS =>
        exact Templates.residual_value_typed hs.ambient_wf.erase hj.erase hk.erase
          (hm.result_wf hΔ).module_exports.erase hd.erase (ihm hΔ hm _ (.value hM))
          ((ihs hΔ hs _ (.value hS)).value_reambient hS.values.2 _ .unit)
          hM.values.2 hS.values.2
    | resid hM hnot hS =>
      exact .app (.app (Templates.residual_typed hs.ambient_wf.erase hj.erase hk.erase
        (hm.result_wf hΔ).module_exports.erase hd.erase)
        ((ihm hΔ hm _ (.value hM)).value_reambient hM.values.2 _ hs.ambient_wf.erase))
        (ihs hΔ hs _ hS)
  case invoke =>
    rename_i hm hp ihm ihp hΔ hself E hE
    cases hE with
    | canonical => exact hself.erase hΔ
    | value hr => cases hr
    | invoke hM hP => exact .app (ihm hΔ hm _ hM) (ihp hΔ hp _ hP)
  case value =>
    rename_i hv he hh ih hΔ hself E hE
    exact .value (hE.value_preservation hv) (ih hΔ he _ hE) hh.erase
  case nil =>
    rename_i hh hΔ hself E hE
    cases hE.nil_inv
    exact .nil hh.erase
  case cons =>
    rename_i he hf hd ihe ihf hΔ hself E hE
    obtain ⟨E,Fs,rfl,hE,hF⟩ := hE.cons_inv
    exact .cons (ihe hΔ he _ hE) (ihf hΔ hf _ hF) hd.erase
  case closed =>
    rename_i hcore hc ih hΔ hself C hE h hh
    cases hE with
    | canonical => exact hself.erase hΔ hh
    | value hr => cases hr
    | box hU hC =>
      cases hU.unit_inv
      exact .box (.unit hh) (ih hΔ hc _ hC)
  all_goals
    rename_i heq hw ih hΔ hself E hE
    exact .conv (ih hΔ (by assumption) _ hE) heq.erase hw.erase

/-- S1.4: every permitted runtime elaboration preserves typing. -/
theorem HasType.elaborates (ht : HasType Δ h e a) (hΔ : Context.Valid Δ)
    (he : Elaborates e E) : Target.HasType Δ.erase h.erase E a.erase :=
  ht.elaborates_aux hΔ ht E he

/-- Field-list elaboration preserves its full exact row. -/
theorem FieldsType.elaborates (hf : FieldsType Δ h fs r) (hΔ : Context.Valid Δ)
    (he : Elaborates fs Fs) : Target.FieldsType Δ.erase h.erase Fs r.erase :=
  ((HasType.record hf).elaborates hΔ (.record he)).fields_inv hΔ.erase

/-- Stored certificates remain typed under every well-formed caller ambient. -/
theorem CertType.elaborates (hc : CertType Δ a b cd) (hΔ : Context.Valid Δ)
    (he : Elaborates cd C) (hh : WellFormed Δ h) :
    Target.HasType Δ.erase h.erase C (.arr a.erase b.erase) :=
  (hc.typed hh).elaborates hΔ he

/-- The full open-context statement fixed in Goals.lean. -/
theorem elaboration_typing : Goals.ElaborationTyping := by
  intro Δ h a e E hΔ ht he
  exact ht.elaborates hΔ he

end LeanSce.Source

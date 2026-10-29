import LeanSce.Source.Elaboration.Representations
import LeanSce.Source.Elaboration.Templates
import LeanSce.Source.Elaboration.Typing
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.CanonicalForms
import LeanSce.Source.Metatheory.Evaluation

/-!
# Source / Elaboration / ExecutionRelation

Proofs and supporting constructions for execution relation.
-/

/-! ## Atomic Correspondence -/

namespace LeanSce.Source

theorem Related.app_step (hf : Related f F) (hx : Related x X)
    (hν : Related ν N) (hs : Step ν (.app f x) e') :
    ∃ E', Target.Step N (.app F X) E' ∧ Elaborates e' E' := by
  have hxv := hx.values
  have hνv := hν.values
  have hfv := hf.values
  have hh := hs.2
  simp only [step_app_eq,(show x.isValue = true from hxv.1),
    (show f.isValue = true from hfv.1),Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases hf
  all_goals try simp only [reduceCtorEq] at hh
  all_goals try contradiction
  case clo hc hb =>
    cases hh
    exact ⟨_,⟨hνv.2,by simp [Target.step_app_eq,(show X.isValue = true from hxv.2),
      Target.Term.isValue,(show _ = true from hc.values.2)]⟩,.box (.value (.pair hc hx)) hb⟩
  case rclo hc hb =>
    cases hh
    exact ⟨_,⟨hνv.2,by simp [Target.step_app_eq,(show X.isValue = true from hxv.2),
      Target.Term.isValue,(show _ = true from hc.values.2)]⟩,
      .box (.value (.pair (.pair hc (.rclo hc hb)) hx)) hb⟩

theorem Related.tapp_step (hf : Related f F) (hν : Related ν N)
    (hs : Step ν (.tapp f u) e') :
    ∃ E', Target.Step N (.tapp F u.erase) E' ∧ Elaborates e' E' := by
  have hfv := hf.values
  have hνv := hν.values
  have hh := hs.2
  simp only [step_tapp_eq,(show f.isValue = true from hfv.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases hf
  all_goals try simp only [reduceCtorEq] at hh
  all_goals try contradiction
  case tclo hc hb =>
    cases hh
    have hb' := hb.subst u.openSubst
    simp only [Arg.erase_openSubst] at hb'
    refine ⟨_,⟨hνv.2,?_⟩,.box (.value hc) hb'⟩
    simp [Target.step_tapp_eq,Target.Term.isValue,(show _ = true from hc.values.2)]

theorem Related.fst_step (hx : Related x X) (hν : Related ν N)
    (hs : Step ν (.fst x) e') :
    ∃ E', Target.Step N (.fst X) E' ∧ Elaborates e' E' := by
  have hv := hx.values
  have hh := hs.2
  simp only [step_fst_eq,(show x.isValue = true from hv.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases hx
  all_goals try simp only [reduceCtorEq] at hh
  all_goals try contradiction
  case pair ha hb =>
    cases hh
    exact ⟨_,⟨hν.values.2,by simp [Target.step_fst_eq,Target.Term.isValue,
      (show _ = true from ha.values.2),(show _ = true from hb.values.2)]⟩,.value ha⟩

theorem Related.snd_step (hx : Related x X) (hν : Related ν N)
    (hs : Step ν (.snd x) e') :
    ∃ E', Target.Step N (.snd X) E' ∧ Elaborates e' E' := by
  have hv := hx.values
  have hh := hs.2
  simp only [step_snd_eq,(show x.isValue = true from hv.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases hx
  all_goals try simp only [reduceCtorEq] at hh
  all_goals try contradiction
  case pair ha hb =>
    cases hh
    exact ⟨_,⟨hν.values.2,by simp [Target.step_snd_eq,Target.Term.isValue,
      (show _ = true from ha.values.2),(show _ = true from hb.values.2)]⟩,.value hb⟩

theorem Related.unfold_step (hx : Related x X) (hν : Related ν N)
    (hs : Step ν (.unfold x) e') :
    ∃ E', Target.Step N (.unfold X) E' ∧ Elaborates e' E' := by
  have hv := hx.values
  have hh := hs.2
  simp only [step_unfold_eq,(show x.isValue = true from hv.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases hx
  all_goals try simp only [reduceCtorEq] at hh
  all_goals try contradiction
  case fold hr =>
    cases hh
    exact ⟨_,⟨hν.values.2,by simp [Target.step_unfold_eq,Target.Term.isValue,
      (show _ = true from hr.values.2)]⟩,.value hr⟩

theorem Related.case_step (hx : Related x X) (hν : Related ν N)
    (hl : Elaborates l L) (hr : Elaborates r R) (hs : Step ν (.case x l r) e') :
    ∃ E', Target.Step N (.case X L R) E' ∧ Elaborates e' E' := by
  have hv := hx.values
  have hh := hs.2
  simp only [step_case_eq,(show x.isValue = true from hv.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases hx
  all_goals try simp only [reduceCtorEq] at hh
  all_goals try contradiction
  case inl hx =>
    cases hh
    exact ⟨_,⟨hν.values.2,by simp [Target.step_case_eq,Target.Term.isValue,
      (show _ = true from hx.values.2)]⟩,.box (.value (.pair hν hx)) hl⟩
  case inr hx =>
    cases hh
    exact ⟨_,⟨hν.values.2,by simp [Target.step_case_eq,Target.Term.isValue,
      (show _ = true from hx.values.2)]⟩,.box (.value (.pair hν hx)) hr⟩

theorem Related.unpack_step (hx : Related x X) (hν : Related ν N)
    (hb : Elaborates body BODY) (hs : Step ν (.unpack x body) e') :
    ∃ E', Target.Step N (.unpack X BODY) E' ∧ Elaborates e' E' := by
  have hv := hx.values
  have hh := hs.2
  simp only [step_unpack_eq,(show x.isValue = true from hv.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases hx
  all_goals try simp only [reduceCtorEq] at hh
  all_goals try contradiction
  case pack =>
    rename_i v V u a hx
    cases hh
    have hb' := hb.subst u.openSubst
    simp only [Arg.erase_openSubst] at hb'
    exact ⟨_,⟨hν.values.2,by simp [Target.step_unpack_eq,Target.Term.isValue,
      (show _ = true from hx.values.2)]⟩,.box (.value (.pair hν hx)) hb'⟩

theorem Related.ite_step (hx : Related x X) (hν : Related ν N)
    (hl : Elaborates l L) (hr : Elaborates r R) (hs : Step ν (.ite x l r) e') :
    ∃ E', Target.Step N (.ite X L R) E' ∧ Elaborates e' E' := by
  have hv := hx.values
  have hh := hs.2
  simp only [step_ite_eq,(show x.isValue = true from hv.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  cases hx
  all_goals try simp only [reduceCtorEq] at hh
  all_goals try contradiction
  case bool b =>
    cases b
    · cases hh; exact ⟨_,⟨hν.values.2,rfl⟩,hr⟩
    · cases hh; exact ⟨_,⟨hν.values.2,rfl⟩,hl⟩

theorem Related.get_step (hx : Related (.record fs) (.record Fs))
    (hn : fs.labels.Nodup) (hν : Related ν N) (hs : Step ν (.get (.record fs) l) e') :
    ∃ E', Target.Step N (.get (.record Fs) l) E' ∧ Elaborates e' E' := by
  have hl : fs.lookup l = some e' := by
    simpa only [step_get_eq,Term.isValue,(show fs.isValue = true from hx.values.1),
      Bool.not_true,Bool.false_eq_true,↓reduceIte] using hs.2
  obtain ⟨V,hV,hr⟩ := hx.record_lookup hn hl
  exact ⟨V,⟨hν.values.2,by simpa only [Target.step_get_eq,Target.Term.isValue,
    (show Fs.isValue = true from hx.values.2),Bool.not_true,Bool.false_eq_true,↓reduceIte] using hV⟩,.value hr⟩

theorem Related.find_step (hx : Related x X) (hν : Related ν N)
    (hs : Step ν (.find l x) e') :
    ∃ E', Target.Step N (.find l X) E' ∧ Elaborates e' E' := by
  have hh := hs.2
  simp only [step_find_eq,(show x.isValue = true from hx.values.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  have hfind : x.findTags l = [e'] := by
    cases htags : x.findTags l with
    | nil => simp only [htags,reduceCtorEq] at hh
    | cons v vs =>
      cases vs with
      | nil => simp only [htags,Option.some.injEq] at hh; cases hh; rfl
      | cons => simp only [htags,reduceCtorEq] at hh
  obtain ⟨V,hV,hr⟩ := hx.find_singleton hfind
  exact ⟨V,⟨hν.values.2,by simp only [Target.step_find_eq,
    (show X.isValue = true from hx.values.2),Bool.not_true,Bool.false_eq_true,↓reduceIte,hV]⟩,.value hr⟩

theorem Related.record_contains (hx : Related (.record fs) (.record Fs)) (l : String) :
    Fs.labels.contains l = fs.labels.contains l := by
  apply Bool.coe_iff_coe.mp
  simpa using hx.record_labels.mem_iff.symm

theorem Related.merge_step (hx : Related (.record fs) (.record Fs))
    (hy : Related (.record gs) (.record Gs)) (hν : Related ν N)
    (hs : Step ν (.merge (.record fs) (.record gs)) e') :
    ∃ E', Target.Step N (.merge (.record Fs) (.record Gs)) E' ∧ Elaborates e' E' := by
  have hh := hs.2
  simp only [step_merge_eq,Term.isValue,(show fs.isValue = true from hx.values.1),
    (show gs.isValue = true from hy.values.1),Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  split at hh
  next hd =>
    have hD : Fs.labels.all (fun l => !Gs.labels.contains l) = true := by
      apply List.all_eq_true.mpr
      intro l hl
      rw [hy.record_contains]
      exact List.all_eq_true.mp hd l (hx.record_labels.mem_iff.mpr hl)
    cases hh
    exact ⟨_,⟨hν.values.2,by simp only [Target.step_merge_eq,Target.Term.isValue,
      (show Fs.isValue = true from hx.values.2),(show Gs.isValue = true from hy.values.2),
      Bool.not_true,Bool.false_eq_true,↓reduceIte,hD]⟩,.value (hx.records_append hy)⟩
  next => contradiction

theorem Related.take_step (hx : Related (.record fs) (.record Fs))
    (hν : Related ν N) (hs : Step ν (.take ls (.record fs)) e') :
    ∃ E', Target.Step N (.take ls (.record Fs)) E' ∧ Elaborates e' E' := by
  have hh := hs.2
  simp only [step_take_eq,Term.isValue,(show fs.isValue = true from hx.values.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  split at hh
  next hd =>
    have hD : ls.all Fs.labels.contains = true := by
      have hcontains : Fs.labels.contains = fs.labels.contains := funext hx.record_contains
      rw [hcontains]
      exact hd
    cases hh
    exact ⟨_,⟨hν.values.2,by simp only [Target.step_take_eq,Target.Term.isValue,
      (show Fs.isValue = true from hx.values.2),Bool.not_true,Bool.false_eq_true,
      ↓reduceIte,hD]⟩,.value (hx.records_filter _)⟩
  next => contradiction

theorem Related.drop_step (hx : Related (.record fs) (.record Fs))
    (hν : Related ν N) (hs : Step ν (.drop ls (.record fs)) e') :
    ∃ E', Target.Step N (.drop ls (.record Fs)) E' ∧ Elaborates e' E' := by
  have hh := hs.2
  simp only [step_drop_eq,Term.isValue,(show fs.isValue = true from hx.values.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  split at hh
  next hd =>
    have hD : ls.all Fs.labels.contains = true := by
      have hcontains : Fs.labels.contains = fs.labels.contains := funext hx.record_contains
      rw [hcontains]
      exact hd
    cases hh
    exact ⟨_,⟨hν.values.2,by simp only [Target.step_drop_eq,Target.Term.isValue,
      (show Fs.isValue = true from hx.values.2),Bool.not_true,Bool.false_eq_true,
      ↓reduceIte,hD]⟩,.value (hx.records_filter _)⟩
  next => contradiction

theorem Related.relabel_step (hx : Related (.record fs) (.record Fs))
    (hν : Related ν N) (hs : Step ν (.relabel l k (.record fs)) e') :
    ∃ E', Target.Step N (.relabel l k (.record Fs)) E' ∧ Elaborates e' E' := by
  have hh := hs.2
  simp only [step_relabel_eq,Term.isValue,(show fs.isValue = true from hx.values.1),
    Bool.not_true,Bool.false_eq_true,↓reduceIte] at hh
  split at hh
  next hd =>
    have hD : (l != k && Fs.labels.contains l && !Fs.labels.contains k) = true := by
      simpa only [hx.record_contains] using hd
    cases hh
    exact ⟨_,⟨hν.values.2,by simp only [Target.step_relabel_eq,Target.Term.isValue,
      (show Fs.isValue = true from hx.values.2),Bool.not_true,Bool.false_eq_true,
      ↓reduceIte,hD]⟩,.value hx.records_relabel⟩
  next => contradiction

theorem Related.prim_step {fs : Fields} {Fs : Target.Fields}
    (hf : Related fs Fs) (hν : Related ν N) (hs : Step ν (.prim p fs) e') :
    ∃ E', Target.Step N (.prim p Fs) E' ∧ Elaborates e' E' := by
  have he : LeanSce.Source.evalPrim p fs = some e' := by
    simpa only [step_prim_eq,(show fs.isValue = true from hf.values.1),
      Bool.not_true,Bool.false_eq_true,↓reduceIte] using hs.2
  obtain ⟨V,hV,hrel⟩ := hf.evalPrim he
  exact ⟨V,⟨hν.values.2,by simpa only [Target.step_prim_eq,
    (show Fs.isValue = true from hf.values.2),Bool.not_true,Bool.false_eq_true,
    ↓reduceIte] using hV⟩,.value hrel⟩

end LeanSce.Source

/-! ## Finite Correspondence -/

namespace LeanSce.Source

/-- Each direction charges only its own bounded execution. The corresponding
    execution is an actual finite reduction with its actual related result. -/
def FiniteCorrespondence (n : Nat) (ν e : Expr) (N E : Target.Expr) : Prop :=
  (∀ k, k ≤ n → ∀ v, TerminatesIn ν e k v →
    ∃ V, Target.Terminates N E V ∧ Related v V) ∧
  (∀ k, k ≤ n → ∀ V, Target.TerminatesIn N E k V →
    ∃ v, Terminates ν e v ∧ Related v V)

def SmallCorrespondence (n : Nat) : Prop :=
  ∀ m, m < n → ∀ (Δ : Context) (h a : Typ) (e : Expr) (E : Target.Expr)
    (ν : Expr) (N : Target.Expr), Context.Valid Δ → HasType Δ h e a →
    Elaborates e E → ValueType Δ ν h → Related ν N →
    FiniteCorrespondence m ν e N E

def ElaborationComputes (n : Nat) (Δ : Context) (h : Typ) (e : Expr) : Prop :=
  ∀ (E : Target.Expr) (ν : Expr) (N : Target.Expr), Elaborates e E →
    ValueType Δ ν h → Related ν N → FiniteCorrespondence n ν e N E

/-- Immediate source constructs which spend positive administrative work on
    either side. Runtime residual construction is handled structurally instead. -/
def Term.sourceHead : Term s → Bool
  | .letVal .. | .view .. | .module .. | .capture .. | .run .. | .link ..
  | .provide .. | .complete .. | .invoke .. => true
  | _ => false

def SourceHeadCorrespondence (n : Nat) : Prop :=
  ∀ (Δ : Context) (h a : Typ) (e : Expr), Context.Valid Δ → HasType Δ h e a →
    e.sourceHead = true → ElaborationComputes n Δ h e

theorem Term.sourceHead_not_value (hh : e.sourceHead = true) : ¬ Value e := by
  cases e <;> simp_all [Term.sourceHead,Value,Term.isValue]

theorem FiniteCorrespondence.value (he : Elaborates e E) (hv : Value e) :
    FiniteCorrespondence n ν e N E := by
  have hr := he.value_related hv
  constructor
  · intro k _ v ht
    obtain ⟨rfl,rfl⟩ := ht.1.value_inv hv
    exact ⟨E,⟨.refl,hr.values.2⟩,hr⟩
  · intro k _ V ht
    obtain ⟨rfl,rfl⟩ := ht.1.value_inv hr.values.2
    exact ⟨e,⟨.refl,hv⟩,hr⟩

theorem FiniteCorrespondence.bind (he : FiniteCorrespondence n ν e N E)
    (hc : StrictFrame ν C) (hd : Target.StrictFrame N D)
    (hk : ∀ v V, Terminates ν e v → Related v V →
      FiniteCorrespondence n ν (C v) N (D V)) :
    FiniteCorrespondence n ν (C e) N (D E) := by
  constructor
  · intro k hk' w hw
    obtain ⟨v,i,j,hij,hv,hrest⟩ := hc.decompose_counted hw
    obtain ⟨V,hV,hr⟩ := he.1 i (by omega) v hv
    obtain ⟨W,hW,hrW⟩ := (hk v V hv.toTerminates hr).1 j (by omega) w hrest
    exact ⟨W,hd.terminates hV hW,hrW⟩
  · intro k hk' W hW
    obtain ⟨V,i,j,hij,hV,hrest⟩ := hd.decompose_counted hW
    obtain ⟨v,hv,hr⟩ := he.2 i (by omega) V hV
    obtain ⟨w,hw,hrw⟩ := (hk v V hv hr).2 j (by omega) W hrest
    exact ⟨w,hc.terminates hv hw,hrw⟩

/-- Fixed finite creation prefixes can differ in length. Their literal final
    values still determine both directions of finite correspondence. -/
theorem FiniteCorrespondence.creation (hs : Terminates ν e v)
    (ht : Target.Terminates N E V) (hr : Related v V) :
    FiniteCorrespondence n ν e N E := by
  constructor
  · intro _ _ w hw
    have heq := hw.toTerminates.unique hs
    cases heq
    exact ⟨V,ht,hr⟩
  · intro _ _ W hW
    have heq := hW.toTerminates.unique ht
    cases heq
    exact ⟨v,hs,hr⟩

theorem FiniteCorrespondence.atomic (small : SmallCorrespondence n)
    (hΔ : Context.Valid Δ) (ht : HasType Δ h e a)
    (hν : ValueType Δ ν h) (henv : Related ν N) (hn : ¬ Value e)
    (hsim : ∀ e', Step ν e e' →
      ∃ E', Target.Step N E E' ∧ Elaborates e' E') :
    FiniteCorrespondence n ν e N E := by
  obtain hv | ⟨e',hs⟩ := ht.canStep hΔ ν hν
  · exact False.elim (hn hv)
  obtain ⟨E',hS,he⟩ := hsim e' ⟨hν.1,hs⟩
  have htyped := ht.preservation hΔ ν hν e' hs
  constructor
  · intro k hk w hw
    obtain ⟨j,hj,hbody⟩ := hw.after_step ⟨hν.1,hs⟩
    obtain ⟨W,hW,hr⟩ := (small j (by omega) Δ h a e' E' ν N hΔ htyped he hν henv).1
      j (Nat.le_refl _) w hbody
    exact ⟨W,⟨.next hS hW.1,hW.2⟩,hr⟩
  · intro k hk W hW
    obtain ⟨j,hj,hbody⟩ := hW.after_step hS
    obtain ⟨w,hw,hr⟩ := (small j (by omega) Δ h a e' E' ν N hΔ htyped he hν henv).2
      j (Nat.le_refl _) W hbody
    exact ⟨w,⟨.next ⟨hν.1,hs⟩ hw.1,hw.2⟩,hr⟩

/-- A nonvalue continuation guarantees that a successful enclosing run has a
    strictly smaller operand budget on each side. -/
theorem FiniteCorrespondence.bind_strict
    (he : ∀ m, m < n → FiniteCorrespondence m ν e N E)
    (hc : StrictFrame ν C) (hd : Target.StrictFrame N D)
    (hn : ∀ v, Value v → ¬ Value (C v))
    (hN : ∀ V, Target.Value V → ¬ Target.Value (D V))
    (hk : ∀ v V, Terminates ν e v → Related v V →
      FiniteCorrespondence n ν (C v) N (D V)) :
    FiniteCorrespondence n ν (C e) N (D E) := by
  constructor
  · intro k hk' w hw
    obtain ⟨v,i,j,hij,hv,hrest⟩ := hc.decompose_counted hw
    have hj : j ≠ 0 := by
      intro heq
      subst j
      cases hrest.1
      exact hn v hv.2 hrest.2
    obtain ⟨V,hV,hr⟩ := (he i (by omega)).1 i (Nat.le_refl _) v hv
    obtain ⟨W,hW,hrW⟩ := (hk v V hv.toTerminates hr).1 j (by omega) w hrest
    exact ⟨W,hd.terminates hV hW,hrW⟩
  · intro k hk' W hW
    obtain ⟨V,i,j,hij,hV,hrest⟩ := hd.decompose_counted hW
    have hj : j ≠ 0 := by
      intro heq
      subst j
      cases hrest.1
      exact hN V hV.2 hrest.2
    obtain ⟨v,hv,hr⟩ := (he i (by omega)).2 i (Nat.le_refl _) V hV
    obtain ⟨w,hw,hrw⟩ := (hk v V hv hr).2 j (by omega) W hrest
    exact ⟨w,hc.terminates hv hw,hrw⟩

/-- Value constructors charge no administrative step and preserve their
    payload's complete evaluation budget. -/
theorem FiniteCorrespondence.constructor (he : FiniteCorrespondence n ν e N E)
    (hc : StrictFrame ν C) (hd : Target.StrictFrame N D)
    (hcv : ∀ v, Value v → Value (C v))
    (hdv : ∀ V, Target.Value V → Target.Value (D V))
    (hrel : ∀ v V, Related v V → Related (C v) (D V)) :
    FiniteCorrespondence n ν (C e) N (D E) := by
  constructor
  · intro k hk w hw
    obtain ⟨v,i,j,hij,hv,hrest⟩ := hc.decompose_counted hw
    obtain ⟨rfl,rfl⟩ := hrest.1.value_inv (hcv v hv.2)
    obtain ⟨V,hV,hr⟩ := he.1 i (by omega) v hv
    exact ⟨D V,hd.terminates hV ⟨.refl,hdv V hV.2⟩,hrel v V hr⟩
  · intro k hk W hW
    obtain ⟨V,i,j,hij,hV,hrest⟩ := hd.decompose_counted hW
    obtain ⟨rfl,rfl⟩ := hrest.1.value_inv (hdv V hV.2)
    obtain ⟨v,hv,hr⟩ := he.2 i (by omega) V hV
    exact ⟨C v,hc.terminates hv ⟨.refl,hcv v hv.2⟩,hrel v V hr⟩

/-- Once a strict operand has returned, a genuine source head reduction and
    its corresponding target head reduction expose a smaller execution. -/
theorem FiniteCorrespondence.eliminator (small : SmallCorrespondence n)
    (hΔ : Context.Valid Δ) (ht : HasType Δ h (C e) a)
    (hν : ValueType Δ ν h) (henv : Related ν N)
    (he : FiniteCorrespondence n ν e N E)
    (hc : StrictFrame ν C) (hd : Target.StrictFrame N D)
    (hn : ∀ v, Value v → ¬ Value (C v))
    (hsim : ∀ v V, Terminates ν e v → Related v V → ∀ e', Step ν (C v) e' →
      ∃ E', Target.Step N (D V) E' ∧ Elaborates e' E') :
    FiniteCorrespondence n ν (C e) N (D E) := by
  constructor
  · intro k hk w hw
    obtain ⟨v,i,j,hij,hv,hrest⟩ := hc.decompose_counted hw
    obtain ⟨V,hV,hr⟩ := he.1 i (by omega) v hv
    have ht' := (hc.lift_steps hv.1.toSteps).preservation hν ht hΔ
    obtain hv' | ⟨e',hs⟩ := ht'.canStep hΔ ν hν
    · exact False.elim (hn v hv.2 hv')
    obtain ⟨E',hS,hElab⟩ := hsim v V hv.toTerminates hr e' ⟨hν.1,hs⟩
    obtain ⟨p,hp,hbody⟩ := hrest.after_step ⟨hν.1,hs⟩
    have hsmall := small p (by omega) Δ h a e' E' ν N hΔ
      (ht'.preservation hΔ ν hν e' hs) hElab hν henv
    obtain ⟨W,hW,hrelated⟩ := hsmall.1 p (Nat.le_refl _) w hbody
    exact ⟨W,hd.terminates hV ⟨.next hS hW.1,hW.2⟩,hrelated⟩
  · intro k hk W hW
    obtain ⟨V,i,j,hij,hV,hrest⟩ := hd.decompose_counted hW
    obtain ⟨v,hv,hr⟩ := he.2 i (by omega) V hV
    have ht' := (hc.lift_steps hv.1).preservation hν ht hΔ
    obtain hv' | ⟨e',hs⟩ := ht'.canStep hΔ ν hν
    · exact False.elim (hn v hv.2 hv')
    obtain ⟨E',hS,hElab⟩ := hsim v V hv hr e' ⟨hν.1,hs⟩
    obtain ⟨p,hp,hbody⟩ := hrest.after_step hS
    have hsmall := small p (by omega) Δ h a e' E' ν N hΔ
      (ht'.preservation hΔ ν hν e' hs) hElab hν henv
    obtain ⟨w,hw,hrelated⟩ := hsmall.2 p (Nat.le_refl _) W hbody
    exact ⟨w,hc.terminates hv ⟨.next ⟨hν.1,hs⟩ hw.1,hw.2⟩,hrelated⟩

end LeanSce.Source

/-! ## Finite Data Correspondence -/

namespace LeanSce.Source

theorem FiniteCorrespondence.pair (hx : FiniteCorrespondence n ν x N X)
    (hy : FiniteCorrespondence n ν y N Y) :
    FiniteCorrespondence n ν (.pair x y) N (.pair X Y) := by
  apply hx.bind strict_pair_left Target.strict_pair_left
  intro v V _ hr
  exact hy.constructor (strict_pair_right hr.values.1) (Target.strict_pair_right hr.values.2)
    (fun _ hv => Bool.and_eq_true_iff.mpr ⟨hr.values.1,hv⟩)
    (fun _ hv => Bool.and_eq_true_iff.mpr ⟨hr.values.2,hv⟩)
    (fun _ _ hrel => .pair hr hrel)

theorem FiniteCorrespondence.native_box (hν : Related ν N)
    (he : FiniteCorrespondence n ν e N E)
    (hb : ∀ cap Cap, Terminates ν e cap → Related cap Cap →
      FiniteCorrespondence n cap body Cap BODY) :
    FiniteCorrespondence n ν (.box e body) N (.box E BODY) := by
  constructor
  · intro k hk w hw
    obtain ⟨cap,i,j,hij,hcap,hbody⟩ := hw.native_box_inv hν.values.1
    obtain ⟨Cap,hCap,hr⟩ := he.1 i (by omega) cap hcap
    obtain ⟨W,hW,hrel⟩ := (hb cap Cap hcap.toTerminates hr).1 j (by omega) w hbody
    exact ⟨W,Target.Terminates.native_box hν.values.2 hCap hW,hrel⟩
  · intro k hk W hW
    obtain ⟨Cap,i,j,hij,hCap,hbody⟩ := hW.native_box_inv hν.values.2
    obtain ⟨cap,hcap,hr⟩ := he.2 i (by omega) Cap hCap
    obtain ⟨w,hw,hrel⟩ := (hb cap Cap hcap hr).2 j (by omega) W hbody
    exact ⟨w,Terminates.native_box hν.values.1 hcap hw,hrel⟩

theorem FiniteCorrespondence.record_cons (hx : FiniteCorrespondence n ν x N X)
    (hf : FiniteCorrespondence n ν (.record fs) N (.record Fs)) :
    FiniteCorrespondence n ν (.record (.cons l x fs)) N (.record (.cons l X Fs)) := by
  constructor
  · intro k hk w hw
    obtain ⟨v,i,j,hij,hv,hrest⟩ := strict_record_head.decompose_counted hw
    obtain ⟨gs,rfl,htail⟩ := hrest.record_cons_inv hv.2
    obtain ⟨V,hV,hrelv⟩ := hx.1 i (by omega) v hv
    obtain ⟨Tail,hTail,hrelTail⟩ := hf.1 j (by omega) (.record gs) htail
    cases hrelTail with
    | record hfields hp =>
      exact ⟨_,Target.strict_record_head.terminates hV (hTail.record_prepend hV.2),
        hrelv.record_prepend (.record hfields hp)⟩
  · intro k hk W hW
    obtain ⟨V,i,j,hij,hV,hrest⟩ := Target.strict_record_head.decompose_counted hW
    obtain ⟨Gs,rfl,htail⟩ := hrest.record_cons_inv hV.2
    obtain ⟨v,hv,hrelv⟩ := hx.2 i (by omega) V hV
    obtain ⟨tail,htail,hrelTail⟩ := hf.2 j (by omega) (.record Gs) htail
    cases hrelTail with
    | record hfields hp =>
      exact ⟨_,strict_record_head.terminates hv (htail.record_prepend hv.2),
        hrelv.record_prepend (.record hfields hp)⟩

theorem FiniteCorrespondence.residual (hm : Value m)
    (he : Elaborates (.resid m saved j k o) E) (hν : Related ν N)
    (hs : ∀ S, Elaborates saved S → FiniteCorrespondence n ν saved N S) :
    FiniteCorrespondence n ν (.resid m saved j k o) N E := by
  by_cases hv : Value saved
  · exact .value he (Bool.and_eq_true_iff.mpr ⟨hm,hv⟩)
  obtain ⟨M,S,rfl,hrm,helab⟩ := he.resid_nonvalue_inv hm hv
  have hsaved := hs S helab
  constructor
  · intro q hq w hw
    obtain ⟨v,i,p,hip,hv,hrest⟩ := (strict_resid_saved hm).decompose_counted hw
    have hres : Value (.resid m v j k o) := Bool.and_eq_true_iff.mpr ⟨hm,hv.2⟩
    obtain ⟨rfl,rfl⟩ := hrest.1.value_inv hres
    obtain ⟨V,hV,hrv⟩ := hsaved.1 i (by omega) v hv
    exact ⟨_,Templates.residual_forward hν.values.2 hrm.values.2 hV,.resid hrm hrv⟩
  · intro q hq W hW
    obtain ⟨V,i,hi,hV,rfl⟩ := Templates.residual_counted_inv hν.values.2 hrm.values.2 hW
    obtain ⟨v,hv,hrv⟩ := hsaved.2 i (by omega) V hV
    exact ⟨_,(strict_resid_saved hm).terminates hv
      ⟨.refl,Bool.and_eq_true_iff.mpr ⟨hm,hv.2⟩⟩,.resid hrm hrv⟩

end LeanSce.Source

/-! ## Finite Core Correspondence -/

namespace LeanSce.Source

/-- Application's function, argument and activated body all have a smaller
    enclosing execution budget. This also handles the call exposed by view. -/
theorem finite_app (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (hf : HasType Δ h f (.arr a b)) (hx : HasType Δ h x a)
    (hef : Elaborates f F) (hex : Elaborates x X)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.app f x) N (.app F X) := by
  apply FiniteCorrespondence.bind_strict
    (fun m hm => small m hm Δ h (.arr a b) f F ν N hΔ hf hef hν henv)
    strict_app_left Target.strict_app_left
    (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
  intro v V hv hrel
  have hf' := hv.1.preservation hν hf hΔ
  have ht' : HasType Δ h (.app v x) b := .app hf' hx
  apply FiniteCorrespondence.bind_strict
    (fun m hm => small m hm Δ h a x X ν N hΔ hx hex hν henv)
    (strict_app_right hrel.values.1) (Target.strict_app_right hrel.values.2)
    (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
  intro w W hw harg
  have hx' := hw.1.preservation hν hx hΔ
  exact FiniteCorrespondence.atomic small hΔ (.app hf' hx') hν henv
    (by intro hv; cases hv) (fun e' hs => hrel.app_step harg henv hs)

/-- The strict operand of a common eliminator is smaller on either bounded
    side; its selected head step then exposes the smaller continuation. -/
theorem finite_unary (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (ht : HasType Δ h (C e) a) (he : HasType Δ h e b) (helab : Elaborates e E)
    (hν : ValueType Δ ν h) (henv : Related ν N)
    (hc : StrictFrame ν C) (hd : Target.StrictFrame N D)
    (hn : ∀ v, Value v → ¬ Value (C v))
    (hN : ∀ V, Target.Value V → ¬ Target.Value (D V))
    (hsim : ∀ v V, Terminates ν e v → Related v V → ∀ e', Step ν (C v) e' →
      ∃ E', Target.Step N (D V) E' ∧ Elaborates e' E') :
    FiniteCorrespondence n ν (C e) N (D E) := by
  apply FiniteCorrespondence.bind_strict
    (fun m hm => small m hm Δ h b e E ν N hΔ he helab hν henv) hc hd hn hN
  intro v V hv hr
  have htyped := (hc.lift_steps hv.1).preservation hν ht hΔ
  exact FiniteCorrespondence.atomic small hΔ htyped hν henv (hn v hv.2)
    (hsim v V hv hr)

theorem finite_binary {B : Expr → Expr → Expr} {D : Target.Expr → Target.Expr → Target.Expr}
    (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (ht : HasType Δ h (B e f) a) (he : HasType Δ h e b) (hf : HasType Δ h f c)
    (helab : Elaborates e E) (hflab : Elaborates f F)
    (hν : ValueType Δ ν h) (henv : Related ν N)
    (hl : StrictFrame ν (fun x => B x f))
    (hL : Target.StrictFrame N (fun X => D X F))
    (hr : ∀ v, Value v → StrictFrame ν (B v))
    (hR : ∀ V, Target.Value V → Target.StrictFrame N (D V))
    (hn : ∀ v w, ¬ Value (B v w)) (hN : ∀ V W, ¬ Target.Value (D V W))
    (hsim : ∀ v V w W, Terminates ν e v → Terminates ν f w →
      Related v V → Related w W → ∀ e', Step ν (B v w) e' →
      ∃ E', Target.Step N (D V W) E' ∧ Elaborates e' E') :
    FiniteCorrespondence n ν (B e f) N (D E F) := by
  apply FiniteCorrespondence.bind_strict
    (fun m hm => small m hm Δ h b e E ν N hΔ he helab hν henv) hl hL
    (fun v _ => hn v f) (fun V _ => hN V F)
  intro v V hv hvV
  have htyped := (hl.lift_steps hv.1).preservation hν ht hΔ
  exact finite_unary small hΔ htyped hf hflab hν henv
    (hr v hv.2) (hR V hvV.values.2) (fun w _ => hn v w) (fun W _ => hN V W)
    (fun w W hw hwW e' hs => hsim v V w W hv hw hvV hwW e' hs)

end LeanSce.Source

/-! ## View Evaluation -/

namespace LeanSce.Source

theorem TerminatesIn.app_argument (hx : TerminatesIn ν x i v)
    (ht : TerminatesIn ν (.app c v) k w) :
    TerminatesIn ν (.app c x) (i+k) w := by
  obtain ⟨F,p,q,hpq,hF,hrest⟩ := strict_app_left.decompose_counted ht
  obtain ⟨v',j,r,hjr,hv',hcall⟩ := (strict_app_right hF.2).decompose_counted hrest
  obtain ⟨rfl,rfl⟩ := hv'.1.value_inv hx.2
  have hs := hF.1.app_left.trans ((hx.1.app_right hF.2).trans hcall.1)
  have hcount : i+k = p+(i+r) := by omega
  exact ⟨hcount ▸ hs,hcall.2⟩

theorem TerminatesIn.view_to_app (hν : Value ν)
    (ht : TerminatesIn ν (.view a b cd e) k w) :
    ∃ j, k = j+1 ∧ TerminatesIn ν (.app cd e) j w := by
  obtain ⟨v,i,p,hip,hv,hrest⟩ := strict_view.decompose_counted ht
  obtain ⟨q,hq,hcall⟩ := hrest.after_step (e' := .app cd v) ⟨hν,by
    simp only [step_view_eq,(show v.isValue = true from hv.2),Bool.not_true,
      Bool.false_eq_true,↓reduceIte]⟩
  exact ⟨i+q,by omega,hv.app_argument hcall⟩

theorem Terminates.app_to_view (hν : Value ν) (ht : Terminates ν (.app cd e) w) :
    Terminates ν (.view a b cd e) w := by
  obtain ⟨F,v,hF,hv,hcall⟩ := ht.app_decompose
  have hcv : Terminates ν (.app cd v) w :=
    ⟨hF.1.app_left.trans hcall.1,hcall.2⟩
  exact strict_view.terminates hv ⟨.next ⟨hν,by
    simp only [step_view_eq,(show v.isValue = true from hv.2),Bool.not_true,
      Bool.false_eq_true,↓reduceIte]⟩ hcv.1,hcv.2⟩

theorem finite_view (small : SmallCorrespondence n) (hΔ : Context.Valid Δ)
    (he : HasType Δ h e a) (hcd : CertType Δ a b cd)
    (helab : Elaborates (.view a b cd e) E)
    (hν : ValueType Δ ν h) (henv : Related ν N) :
    FiniteCorrespondence n ν (.view a b cd e) N E := by
  obtain ⟨C,E₀,rfl,hC,hE⟩ := helab.view_inv
  have happ := finite_app small hΔ (hcd.typed he.ambient_wf) he hC hE hν henv
  constructor
  · intro k hk w hw
    obtain ⟨j,hj,happ'⟩ := hw.view_to_app hν.1
    exact happ.1 j (by omega) w happ'
  · intro k hk W hW
    obtain ⟨w,hw,hr⟩ := happ.2 k hk W hW
    exact ⟨w,hw.app_to_view hν.1,hr⟩

end LeanSce.Source

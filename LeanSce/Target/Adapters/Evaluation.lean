import LeanSce.Target.LogicalRelation.Data
import LeanSce.Target.LogicalRelation.Equality
import LeanSce.Target.LogicalRelation.Evaluation
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Adapters / Evaluation

Proofs and supporting constructions for evaluation.
-/

/-! ## Adapter Coherence Results -/

namespace LeanSce.Target

/-- The unique value produced by frozen adapter code, when it terminates. -/
noncomputable def adaptedValue (code v : Expr) : Expr := by
  classical
  exact if h : ∃ w, Terminates .unit (.app code v) w then Classical.choose h else .unit

theorem adaptedValue_spec (ht : ∃ w, Terminates .unit (.app code v) w) :
    Terminates .unit (.app code v) (adaptedValue code v) := by
  classical
  rw [adaptedValue,dif_pos ht]
  exact Classical.choose_spec ht

theorem Terminates.frozen_body (ht : Terminates ν (.app (.close (.lam a body)) v) w)
    (hν : Value ν) (hv : Value v) : Terminates (.pair .unit v) body w := by
  obtain ⟨F,V,hF,hV,hcall⟩ := ht.app_decompose
  have hf : F = .clo .unit a body := hF.unique ⟨close_lam_steps hν,rfl⟩
  have hv' : V = v := hV.1.value_result hv
  subst F
  subst V
  obtain ⟨k,hk⟩ := hcall.counted
  obtain ⟨j,_,hj⟩ := (LogicalRelation.ApplyBody.clo (cap := .unit) (a := a) (body := body) (x := v)).counted_inv
    hν rfl hv hk
  exact hj.toTerminates

theorem Adapts.closed_lambda (hd : Adapts Δ a b code) :
    ∃ arg body, code = .close (.lam arg body) := by
  cases hd <;> exact ⟨_,_,rfl⟩

theorem Adapts.adapted_spec (hd : Adapts Δ a b code) (hΔ : Context.Valid Δ)
    (hc : Closing θ Δ) (hv : ValueType .empty v (a.subst θ)) :
    Terminates .unit (.app (code.subst θ) v) (adaptedValue (code.subst θ) v) :=
  adaptedValue_spec (hd.terminates hΔ θ hc .unit rfl v hv)

theorem Adapts.adapted_typed (hd : Adapts Δ a b code) (hΔ : Context.Valid Δ)
    (hc : Closing θ Δ) (hv : ValueType .empty v (a.subst θ)) :
    ValueType .empty (adaptedValue (code.subst θ) v) (b.subst θ) := by
  have hs := hd.adapted_spec hΔ hc hv
  have ht : HasType .empty .unit (.app (code.subst θ) v) (b.subst θ) :=
    .app ((hd.typing.2.2 .unit .unit).subst hΔ hc.respects) hv.2
  exact valueType_of_typed_value (hs.1.preservation ⟨rfl,.unit .unit⟩ ht .empty) hs.2

/-- The outer caller is discarded before any saved input is inspected. -/
theorem Adapts.adapted_anywhere (hd : Adapts Δ a b code) (hΔ : Context.Valid Δ)
    (hc : Closing θ Δ) (hv : ValueType .empty v (a.subst θ)) (hν : Value ν) :
    Terminates ν (.app (code.subst θ) v) (adaptedValue (code.subst θ) v) := by
  obtain ⟨arg,body,rfl⟩ := hd.closed_lambda
  have ht := hd.adapted_spec hΔ hc hv
  have hb := ht.frozen_body rfl hv.1
  exact Terminates.close_lam_app hν hv.1 hb

theorem Adapts.result_eq (hd : Adapts Δ a b code) (hΔ : Context.Valid Δ)
    (hc : Closing θ Δ) (hv : ValueType .empty v (a.subst θ)) (hν : Value ν)
    (ht : Terminates ν (.app (code.subst θ) v) w) : w = adaptedValue (code.subst θ) v :=
  ht.unique (hd.adapted_anywhere hΔ hc hv hν)

theorem adapted_identity (hv : Value v) : adaptedValue (identityAdapter a) v = v := by
  have ht : Terminates .unit (.app (identityAdapter a) v) v := by
    exact Terminates.close_lam_app rfl hv (ix_zero_terminates hv)
  exact (adaptedValue_spec ⟨v,ht⟩).unique ht

theorem adapted_arrow (hv : Value v) :
    adaptedValue (arrowAdapter a b c down up) v =
      .clo (.pair .unit v) c (.app up (.app (.ix 1) (.app down (.ix 0)))) := by
  have he : Value (.pair .unit v) := by simpa [Value,Term.isValue] using hv
  have ht : Terminates .unit (.app (arrowAdapter a b c down up) v)
      (.clo (.pair .unit v) c (.app up (.app (.ix 1) (.app down (.ix 0))))) :=
    Terminates.close_lam_app rfl hv ⟨.single ⟨he,rfl⟩,he⟩
  exact (adaptedValue_spec ⟨_,ht⟩).unique ht

theorem adapted_universal (hv : Value v) :
    adaptedValue (universalAdapter a k gs code) v =
      .tclo (.pair .unit v) k gs (.app code (.tapp (.ix 0) (Arg.variable k 0))) := by
  have he : Value (.pair .unit v) := by simpa [Value,Term.isValue] using hv
  have ht : Terminates .unit (.app (universalAdapter a k gs code) v)
      (.tclo (.pair .unit v) k gs (.app code (.tapp (.ix 0) (Arg.variable k 0)))) :=
    Terminates.close_lam_app rfl hv ⟨.single ⟨he,rfl⟩,he⟩
  exact (adaptedValue_spec ⟨_,ht⟩).unique ht

def fieldValue (v : Expr) (l : String) : Expr :=
  match v with
  | .record fs => (fs.lookup l).getD .unit
  | _ => .unit

noncomputable def adaptedFields (θ : Subst) (v : Expr) : Fields → Fields
  | .nil => .nil
  | .cons l (.app c (.get _ k)) es =>
      .cons l (adaptedValue (c.subst θ) (fieldValue v k)) (adaptedFields θ v es)
  | .cons l _ es => .cons l .unit (adaptedFields θ v es)

theorem AdaptsFields.adapted_steps (hf : AdaptsFields Δ r fs es) :
    Context.Valid Δ → ∀ θ, Closing θ Δ → WellFormed Δ r →
      ∀ v, ValueType .empty v (.record (r.subst θ)) →
      FieldSteps (.pair .unit v) (es.subst θ) (adaptedFields θ v es) ∧
        Value (adaptedFields θ v es) := by
  apply AdaptsFields.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ r _ es _ => Context.Valid Δ → ∀ θ, Closing θ Δ → WellFormed Δ r →
      ∀ v, ValueType .empty v (.record (r.subst θ)) →
      FieldSteps (.pair .unit v) (es.subst θ) (adaptedFields θ v es) ∧
        Value (adaptedFields θ v es))
    (t := hf)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil => simp [adaptedFields,Term.subst,show Value (Term.nil) from rfl]; exact .refl
  case cons =>
    rename_i a Δ b code r fs es l hl hd hf _ ih hΔ θ hc wr v hv
    obtain ⟨vs,rfl⟩ := hv.2.value_shape hv.1
    have hsource := hv.2.value_record_inv hv.1 ((WellFormed.record wr).subst hc.respects).record_row
    obtain ⟨x,hx,hxt⟩ := hsource.lookup .empty (wr.lookup_subst hc.respects hl)
    have hxv : ValueType .empty x (a.subst θ) := ⟨Term.lookup_value vs hv.1 hx,hxt⟩
    have hν : Value (.pair .unit (.record vs)) := by simpa [Value,Term.isValue] using hv.1
    have hchild := hd.adapted_anywhere hΔ hc hxv hν
    have hhead := hchild.replace_argument (get_ix_terminates hv.1 hx)
    obtain ⟨htail,hvtail⟩ := ih hΔ θ hc wr (.record vs) hv
    constructor
    · simpa [Term.subst,Term.ix,adaptedFields,fieldValue,hx] using
        (FieldSteps.cons_left hhead.1).trans (htail.cons_right hhead.2)
    · simpa [Value,Term.isValue,adaptedFields,fieldValue,hx] using
        (Bool.and_eq_true_iff.mpr ⟨hhead.2,hvtail⟩)

theorem adapted_closed_record (wr : WellFormed Δ r) (hΔ : Context.Valid Δ)
    (hc : Closing θ Δ) (hf : AdaptsFields Δ r fs es)
    (hv : ValueType .empty v (.record (r.subst θ))) :
    adaptedValue ((closedRecordAdapter r es).subst θ) v = .record (adaptedFields θ v es) := by
  have hfields := hf.adapted_steps hΔ θ hc wr v hv
  have ht : Terminates .unit (.app ((closedRecordAdapter r es).subst θ) v)
      (.record (adaptedFields θ v es)) :=
    Terminates.close_lam_app rfl hv.1 ⟨hfields.1.record,hfields.2⟩
  exact (adaptedValue_spec ⟨_,ht⟩).unique ht

theorem adapted_sameTail_record (wr : WellFormed Δ r) (ws : WellFormed Δ s)
    (hp : r.tails.Perm s.tails) (hΔ : Context.Valid Δ) (hc : Closing θ Δ)
    (hf : AdaptsFields Δ r s.sortedFields es)
    (hv : ValueType .empty (.record vs) (.record (r.subst θ))) :
    adaptedValue ((sameTailAdapter r es).subst θ) (.record vs) =
      .record ((adaptedFields θ (.record vs) es).append
        (vs.filter (fun l => !r.knownLabels.contains l))) := by
  have hfields := hf.adapted_steps hΔ θ hc wr (.record vs) hv
  have wenv : WellFormed Δ (.prod .unit (.record r)) := .prod .unit (.record wr)
  have henv : ValueType .empty (.pair .unit (.record vs))
      (.prod .unit (.record (r.subst θ))) :=
    ⟨by simpa [Value,Term.isValue] using hv.1,.pair (.unit .unit) hv.2⟩
  have hsource := hv.2.value_record_inv hv.1 ((WellFormed.record wr).subst hc.respects).record_row
  have hall : ∀ l ∈ r.knownLabels, ∃ a, (r.subst θ).lookup l = some a := by
    intro l hl
    obtain ⟨a,ha⟩ := r.mem_lookup hl
    exact ⟨a.subst θ,wr.lookup_subst hc.respects ha⟩
  have hdrop := drop_ix_terminates hv.1 (hsource.selection_check _ hall)
  have hfcode := (HasType.record (hf.typing .unit wr ws.sortedFields .unit)).subst hΔ hc.respects
  have hftyped := hfields.1.record.preservation henv hfcode .empty
  have hft := hftyped.value_record_inv hfields.2 (ws.sortedFields.subst hc.respects)
  have hdcode : HasType Δ (.prod .unit (.record r)) (.drop r.knownLabels (.ix 0))
      (.record (r.drop r.knownLabels)) :=
    .drop (.snd (.query wenv)) wr.knownLabels_nodup (fun l hl => r.mem_lookup hl)
  have hdtyped := hdrop.1.preservation henv (hdcode.subst hΔ hc.respects) .empty
  have hdt := hdtyped.value_record_inv hdrop.2 ((wr.drop _).subst hc.respects)
  have hcheck := hft.merge_check hdt ((sameTail_disjoint ws hp).subst hc.respects)
  have hbody : Terminates (.pair .unit (.record vs))
      (.merge (.record (es.subst θ)) (.drop r.knownLabels (.ix 0)))
      (.record ((adaptedFields θ (.record vs) es).append
        (vs.filter (fun l => !r.knownLabels.contains l)))) := by
    refine ⟨(hfields.1.record.merge_left.trans (hdrop.1.merge_right hfields.2)).trans
      (.single ⟨henv.1,?_⟩),Term.append_value _ hfields.2 hdrop.2⟩
    have hv₁ : (Term.record (adaptedFields θ (.record vs) es)).isValue = true := hfields.2
    have hv₂ : (Term.record (vs.filter (fun l => !r.knownLabels.contains l))).isValue = true := hdrop.2
    simp only [step_merge_eq,hv₁,hv₂,Bool.not_true,Bool.false_eq_true,↓reduceIte,hcheck]
  have ht : Terminates .unit (.app ((sameTailAdapter r es).subst θ) (.record vs))
      (.record ((adaptedFields θ (.record vs) es).append
        (vs.filter (fun l => !r.knownLabels.contains l)))) :=
    Terminates.close_lam_app rfl hv.1 hbody
  exact (adaptedValue_spec ⟨_,ht⟩).unique ht

theorem AdaptsFields.adapted_typed (hf : AdaptsFields Δ r fs es) (hΔ : Context.Valid Δ)
    (hc : Closing θ Δ) (wr : WellFormed Δ r) (wf : WellFormed Δ (Ty.fieldsRow fs))
    (hv : ValueType .empty v (.record (r.subst θ))) :
    ValueType .empty (.record (adaptedFields θ v es)) (.record ((Ty.fieldsRow fs).subst θ)) := by
  have hs := hf.adapted_steps hΔ θ hc wr v hv
  have henv : ValueType .empty (.pair .unit v) (.prod .unit (.record (r.subst θ))) :=
    ⟨by simpa [Value,Term.isValue] using hv.1,.pair (.unit .unit) hv.2⟩
  have ht := (HasType.record (hf.typing .unit wr wf .unit)).subst hΔ hc.respects
  exact valueType_of_typed_value (hs.1.record.preservation henv ht .empty) hs.2

@[simp] theorem identityAdapter_subst :
    (identityAdapter a).subst θ = identityAdapter (a.subst θ) := rfl

@[simp] theorem arrowAdapter_subst :
    (arrowAdapter a b c down up).subst θ =
      arrowAdapter (a.subst θ) (b.subst θ) (c.subst θ) (down.subst θ) (up.subst θ) := rfl

@[simp] theorem universalAdapter_subst :
    (universalAdapter a k gs code).subst θ =
      universalAdapter (a.subst θ) k (gs.subst θ.lift) (code.subst θ.lift) := by
  cases k <;> rfl

end LeanSce.Target

/-! ## Adapter Coherence Fields -/

namespace LeanSce.Target

@[simp] theorem Ty.knownFields_fieldsRow (fs : List (String × Typ)) :
    (Ty.fieldsRow fs).knownFields = fs := by
  induction fs with
  | nil => simp [Ty.fieldsRow,Ty.joinRows,Ty.knownFields]
  | cons x fs ih =>
    rcases x with ⟨l,a⟩
    simpa [Ty.fieldsRow,Ty.joinRows,Ty.knownFields] using congrArg (List.cons (l,a)) ih

@[simp] theorem Ty.fieldsRow_subst (fs : List (String × Typ)) (θ : Subst) :
    (Ty.fieldsRow fs).subst θ = Ty.fieldsRow (fs.map fun (l,a) => (l,a.subst θ)) := by
  induction fs with
  | nil => simp [Ty.fieldsRow,Ty.joinRows,Ty.subst]
  | cons x fs ih =>
    rcases x with ⟨l,a⟩
    simpa [Ty.fieldsRow,Ty.joinRows,Ty.subst] using congrArg (Ty.union (.field l (a.subst θ))) ih

namespace LogicalRelation

inductive FieldValRel (n : Nat) : List (String × Typ) → Fields → Fields → Prop where
  | nil : FieldValRel n [] .nil .nil
  | cons : ValRel n a v V → FieldValRel n fs vs Vs →
      FieldValRel n ((l,a)::fs) (.cons l v vs) (.cons l V Vs)

theorem FieldValRel.lookup (hf : FieldValRel n fs vs Vs)
    (hl : (Ty.fieldsRow fs).lookup l = some wanted) :
    ∃ v V, vs.lookup l = some v ∧ Vs.lookup l = some V ∧ ValRel n wanted v V := by
  induction hf with
  | nil => simp [Ty.fieldsRow,Ty.joinRows,Ty.lookup] at hl
  | @cons a v V fs vs Vs k hv hf ih =>
    by_cases he : l = k
    · have ha : a = wanted := by simpa [Ty.fieldsRow,Ty.joinRows,Ty.lookup,he] using hl
      subst wanted
      exact ⟨v,V,by simp [Term.lookup,he],by simp [Term.lookup,he],hv⟩
    · have hl' : (Ty.fieldsRow fs).lookup l = some wanted := by
        simpa [Ty.fieldsRow,Ty.joinRows,Ty.lookup,he] using hl
      obtain ⟨w,W,hw,hW,hr⟩ := ih hl'
      exact ⟨w,W,by simpa [Term.lookup,he] using hw,by simpa [Term.lookup,he] using hW,hr⟩

theorem FieldValRel.shape (hf : FieldValRel n fs vs Vs)
    (hw : WellFormed .empty (Ty.fieldsRow fs)) :
    ShapeRel n (Ty.fieldsRow fs) (.record vs) (.record Vs) := by
  rw [row_fields hw]
  intro l a hm
  obtain ⟨v,V,hl,hr,hrel⟩ := hf.lookup (hw.knownField_lookup hm)
  exact ⟨vs,Vs,v,V,rfl,rfl,hl,hr,hrel⟩

theorem ValRel.fieldValue (hv : ValRel n (.record r) v V)
    (hl : r.lookup l = some a) : ValRel n a (fieldValue v l) (fieldValue V l) := by
  have wr := (hv.left.2.result_wf Context.Valid.empty).record_row
  have hs := hv.shape
  rw [ShapeRel,row_fields wr] at hs
  obtain ⟨vs,Vs,x,X,hv,hV,hlv,hlV,hx⟩ := hs l a (Ty.lookup_knownField r hl)
  subst v
  subst V
  simpa [LeanSce.Target.fieldValue,hlv,hlV] using hx

end LogicalRelation
end LeanSce.Target

/-! ## Adapter Pipeline -/

namespace LeanSce.Target

/-- Deterministic cancellation keeps the actual remaining evaluation budget. -/
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

/-- Inverting a total adapter after a fixed administrative prefix exposes the
    underlying computation and cannot increase its bounded evaluation cost. -/
theorem Adapts.pipeline_inv (hd : Adapts Γ a b code) (hΓ : Context.Valid Γ)
    (hc : Closing θ Γ) (hν : ValueType .empty ν h)
    (hbase : HasType .empty h base (a.subst θ)) (hprefix : Steps ν input base)
    (ht : TerminatesIn ν (.app (code.subst θ) input) k w) :
    ∃ r i, i ≤ k ∧ TerminatesIn ν base i r ∧ w = adaptedValue (code.subst θ) r := by
  obtain ⟨r,j,hj,hinput,hcall⟩ := ht.app_input
  obtain ⟨i,hi,hbaseval⟩ := hinput.after_steps hprefix
  have hrt : ValueType .empty r (a.subst θ) := valueType_of_typed_value
    (hbaseval.1.toSteps.preservation hν hbase .empty) hbaseval.2
  exact ⟨r,i,Nat.le_trans hi hj,hbaseval,hd.result_eq hΓ hc hrt hν.1 hcall⟩

/-- A terminating underlying computation may be preceded by that same fixed
    prefix and followed by the canonical total value transformation. -/
theorem Adapts.pipeline_forward (hd : Adapts Γ a b code) (hΓ : Context.Valid Γ)
    (hc : Closing θ Γ) (hν : ValueType .empty ν h)
    (hbase : HasType .empty h base (a.subst θ)) (hprefix : Steps ν input base)
    (ht : Terminates ν base r) :
    Terminates ν (.app (code.subst θ) input) (adaptedValue (code.subst θ) r) := by
  have hrt := valueType_of_typed_value (ht.1.preservation hν hbase .empty) ht.2
  exact (show Terminates ν input r from ⟨hprefix.trans ht.1,ht.2⟩).app_argument
    (hd.adapted_anywhere hΓ hc hrt hν.1)

end LeanSce.Target

/-! ## Adapter Arrow Pipeline -/

namespace LeanSce.Target

theorem arrow_env_typed (hf : ValueType .empty f tf) (hx : ValueType .empty x tx) :
    ValueType .empty (.pair (.pair .unit f) x) (.prod (.prod .unit tf) tx) :=
  ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl,hf.1⟩,hx.1⟩,
    .pair (.pair (.unit .unit) hf.2) hx.2⟩

/-- The original function is projected from the two saved argument frames. -/
theorem arrow_function_projection (hf : Value f) (hx : Value x) :
    StepsN (.pair (.pair .unit f) x) 3 (.ix 1) f := by
  have henv : Value (.pair (.pair .unit f) x) :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl,hf⟩,hx⟩
  apply StepsN.next (e' := .snd (.fst (.pair (.pair .unit f) x))) ⟨henv,rfl⟩
  apply StepsN.next (e' := .snd (.pair .unit f)) ⟨henv,?_⟩
  · apply StepsN.next (e' := f) ⟨henv,?_⟩ .refl
    simp [step_snd_eq,Term.isValue,(show f.isValue = true from hf)]
  · simp [step_snd_eq,step_fst_eq,Term.isValue,
      (show f.isValue = true from hf),(show x.isValue = true from hx)]

theorem arrow_argument_projection (hf : Value f) (hx : Value x) :
    Terminates (.pair (.pair .unit f) x) (.ix 0) x := by
  have henv : Value (.pair (.pair .unit f) x) :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl,hf⟩,hx⟩
  exact ⟨.next ⟨henv,rfl⟩ (.next ⟨henv,by
    simp [step_snd_eq,Term.isValue,(show f.isValue = true from hf),(show x.isValue = true from hx)]⟩ .refl),hx⟩

/-- All work before calling the original function is a finite fixed prefix. -/
theorem arrow_pipeline_prefix (hdown : Adapts Γ c a down) (hΓ : Context.Valid Γ)
    (hc : Closing θ Γ) (hf : ValueType .empty f ((Ty.arr a b).subst θ))
    (hx : ValueType .empty x (c.subst θ)) :
    Steps (.pair (.pair .unit f) x) (.app (.ix 1) (.app (down.subst θ) (.ix 0)))
      (.app f (adaptedValue (down.subst θ) x)) := by
  have henv := arrow_env_typed hf hx
  have harg := (hdown.adapted_anywhere hΓ hc hx henv.1).replace_argument
    (arrow_argument_projection hf.1 hx.1)
  exact (arrow_function_projection hf.1 hx.1).toSteps.app_left.trans (harg.1.app_right hf.1)

theorem arrow_pipeline_base_typed (hdown : Adapts Γ c a down) (hΓ : Context.Valid Γ)
    (hc : Closing θ Γ) (hf : ValueType .empty f ((Ty.arr a b).subst θ))
    (hx : ValueType .empty x (c.subst θ)) :
    HasType .empty (.prod (.prod .unit ((Ty.arr a b).subst θ)) (c.subst θ))
      (.app f (adaptedValue (down.subst θ) x)) (b.subst θ) := by
  have henv := arrow_env_typed hf hx
  have wh := henv.2.result_wf .empty
  exact .app (hf.inclusion wh) ((hdown.adapted_typed hΓ hc hx).inclusion wh)

/-- The wrapper's bounded result exposes an original function application using
    the adapted argument, with no increase to its tested evaluation budget. -/
theorem arrow_pipeline_inv (hdown : Adapts Γ c a down) (hup : Adapts Γ b d up)
    (hΓ : Context.Valid Γ) (hc : Closing θ Γ)
    (hf : ValueType .empty f ((Ty.arr a b).subst θ)) (hx : ValueType .empty x (c.subst θ))
    (ht : TerminatesIn (.pair (.pair .unit f) x)
      (.app (up.subst θ) (.app (.ix 1) (.app (down.subst θ) (.ix 0)))) k w) :
    ∃ r i, i ≤ k ∧ TerminatesIn (.pair (.pair .unit f) x)
      (.app f (adaptedValue (down.subst θ) x)) i r ∧ w = adaptedValue (up.subst θ) r :=
  hup.pipeline_inv hΓ hc (arrow_env_typed hf hx)
    (arrow_pipeline_base_typed hdown hΓ hc hf hx) (arrow_pipeline_prefix hdown hΓ hc hf hx) ht

/-- Termination of the original call reconstructs the complete wrapper pipeline. -/
theorem arrow_pipeline_forward (hdown : Adapts Γ c a down) (hup : Adapts Γ b d up)
    (hΓ : Context.Valid Γ) (hc : Closing θ Γ)
    (hf : ValueType .empty f ((Ty.arr a b).subst θ)) (hx : ValueType .empty x (c.subst θ))
    (ht : Terminates (.pair (.pair .unit f) x) (.app f (adaptedValue (down.subst θ) x)) r) :
    Terminates (.pair (.pair .unit f) x)
      (.app (up.subst θ) (.app (.ix 1) (.app (down.subst θ) (.ix 0))))
      (adaptedValue (up.subst θ) r) :=
  hup.pipeline_forward hΓ hc (arrow_env_typed hf hx)
    (arrow_pipeline_base_typed hdown hΓ hc hf hx) (arrow_pipeline_prefix hdown hΓ hc hf hx) ht

end LeanSce.Target

/-! ## Adapter Universal Pipeline -/

namespace LeanSce.Target

/-- Activation first reads the saved polymorphic value, in exactly two steps. -/
theorem universal_projection_prefix (henv : Value (.pair .unit f)) :
    StepsN (.pair .unit f) 2 (.tapp (.ix 0) u) (.tapp f u) := by
  apply StepsN.next (e' := .tapp (.snd (.pair .unit f)) u) ⟨henv,rfl⟩
  apply StepsN.next (e' := .tapp f u) ⟨henv,?_⟩ .refl
  have hf : Value f := (Bool.and_eq_true_iff.mp henv).2
  simp [step_tapp_eq,step_snd_eq,Term.isValue,(show f.isValue = true from hf)]

theorem universal_pipeline_inv (hd : Adapts Γ a b code) (hΓ : Context.Valid Γ)
    (hc : Closing θ Γ) (henv : ValueType .empty (.pair .unit f) h)
    (htapp : HasType .empty h (.tapp f u) (a.subst θ))
    (ht : TerminatesIn (.pair .unit f) (.app (code.subst θ) (.tapp (.ix 0) u)) k w) :
    ∃ r i, i ≤ k ∧ TerminatesIn (.pair .unit f) (.tapp f u) i r ∧
      w = adaptedValue (code.subst θ) r :=
  hd.pipeline_inv hΓ hc henv htapp (universal_projection_prefix henv.1).toSteps ht

theorem universal_pipeline_forward (hd : Adapts Γ a b code) (hΓ : Context.Valid Γ)
    (hc : Closing θ Γ) (henv : ValueType .empty (.pair .unit f) h)
    (htapp : HasType .empty h (.tapp f u) (a.subst θ))
    (ht : Terminates (.pair .unit f) (.tapp f u) r) :
    Terminates (.pair .unit f) (.app (code.subst θ) (.tapp (.ix 0) u))
      (adaptedValue (code.subst θ) r) :=
  hd.pipeline_forward hΓ hc henv htapp (universal_projection_prefix henv.1).toSteps ht

end LeanSce.Target

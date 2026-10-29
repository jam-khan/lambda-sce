import LeanSce.Target.Adapters.Typing
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Safety
import LeanSce.Target.Metatheory.Substitution

/-!
# Target / Adapters / Termination

Proofs and supporting constructions for termination.
-/

/-! ## Adapter Termination -/

namespace LeanSce.Target

/-- The field-list instance of the existing one-step evaluator. -/
inductive FieldSteps (ν : Expr) : Fields → Fields → Prop where
  | refl : FieldSteps ν fs fs
  | next : Value ν → step ν fs = some fs' → FieldSteps ν fs' gs → FieldSteps ν fs gs

theorem FieldSteps.trans (hs : FieldSteps ν fs gs) (ht : FieldSteps ν gs ks) :
    FieldSteps ν fs ks := by
  induction hs with
  | refl => exact ht
  | next hv hs _ ih => exact .next hv hs (ih ht)

theorem FieldSteps.record (hs : FieldSteps ν fs gs) : Steps ν (.record fs) (.record gs) := by
  induction hs with
  | refl => exact .refl
  | next hv hs _ ih => exact .next ⟨hv, by rw [step_record_eq,hs]; rfl⟩ ih

theorem FieldSteps.cons_left (hs : Steps ν e e') :
    FieldSteps ν (.cons l e fs) (.cons l e' fs) := by
  induction hs with
  | refl => exact .refl
  | next hs _ ih =>
    exact .next hs.1 (by rw [step_cons_left (step_isValue_false hs.2),hs.2]; rfl) ih

theorem FieldSteps.cons_right (hs : FieldSteps ν fs gs) (hv : Value v) :
    FieldSteps ν (.cons l v fs) (.cons l v gs) := by
  induction hs with
  | refl => exact .refl
  | next hν hs _ ih =>
    exact .next hν (by rw [step_cons_right hv (step_isValue_false hs),hs]; rfl) ih

theorem Steps.from_value (hs : Steps ν v w) (hv : Value v) : v = w := by
  cases hs with
  | refl => rfl
  | next hs _ => exact False.elim (value_irreducible hv hs)

theorem Terminates.replace_argument (happ : Terminates ν (.app f v) w)
    (harg : Terminates ν e v) : Terminates ν (.app f e) w := by
  obtain ⟨F,V,hF,hV,hcall⟩ := happ.app_decompose
  cases hV.1.from_value harg.2
  exact ⟨(hF.1.app_left.trans (harg.1.app_right hF.2)).trans hcall.1,hcall.2⟩

theorem close_lam_steps (hν : Value ν) :
    Steps ν (.close (.lam a body)) (.clo .unit a body) :=
  .next ⟨hν,rfl⟩ (.next ⟨hν,rfl⟩ .refl)

theorem Terminates.close_lam_app (hν : Value ν) (hv : Value v)
    (hb : Terminates (.pair .unit v) body w) :
    Terminates ν (.app (.close (.lam a body)) v) w := by
  have he : Value (.pair .unit v) := by simpa [Value,Term.isValue] using hv
  exact ⟨(close_lam_steps hν).app_left.trans
    (.next ⟨hν, by simp [step_app_eq,Value,Term.isValue] at hv ⊢; exact hv⟩
      (hb.box hν he).1),hb.2⟩

theorem ix_zero_terminates (hv : Value v) :
    Terminates (.pair .unit v) (.ix 0) v := by
  have he : Value (.pair .unit v) := by simpa [Value,Term.isValue] using hv
  exact ⟨.next ⟨he,rfl⟩ (.next ⟨he,by simp [step_snd_eq,Term.isValue,(show v.isValue = true from hv)]⟩ .refl),hv⟩

theorem get_ix_terminates (hv : Value (.record fs)) (hl : fs.lookup l = some v) :
    Terminates (.pair .unit (.record fs)) (.get (.ix 0) l) v := by
  have he : Value (.pair .unit (.record fs)) := by simpa [Value,Term.isValue] using hv
  have hsteps : Steps (.pair .unit (.record fs)) (.get (.ix 0) l) (.get (.record fs) l) :=
    (ix_zero_terminates hv).1.lift (fun e => .get e l) (by
      intro a b hs
      exact ⟨hs.1, by simp [step_get_eq,step_isValue_false hs.2,hs.2]⟩)
  exact ⟨hsteps.trans (.single ⟨he,by simp [step_get_eq,(show _ = true from hv),hl]⟩),
    Term.lookup_value fs hv hl⟩

theorem drop_ix_terminates (hv : Value (.record fs)) (hls : ls.all fs.labels.contains = true) :
    Terminates (.pair .unit (.record fs)) (.drop ls (.ix 0))
      (.record (fs.filter (fun l => !ls.contains l))) := by
  have he : Value (.pair .unit (.record fs)) := by simpa [Value,Term.isValue] using hv
  have hsteps : Steps (.pair .unit (.record fs)) (.drop ls (.ix 0)) (.drop ls (.record fs)) :=
    (ix_zero_terminates hv).1.lift (.drop ls) (by
      intro a b hs
      exact ⟨hs.1, by simp [step_drop_eq,step_isValue_false hs.2,hs.2]⟩)
  exact ⟨hsteps.trans (.single ⟨he,by simp [step_drop_eq,(show _ = true from hv),hls]⟩),
    Term.filter_value fs hv⟩

theorem Steps.merge_left (hs : Steps ν e e') : Steps ν (.merge e x) (.merge e' x) := by
  apply hs.lift (fun e => .merge e x)
  intro a b hs
  exact ⟨hs.1,by simp [step_merge_eq,step_isValue_false hs.2,hs.2]⟩

theorem Steps.merge_right (hs : Steps ν e e') (hv : Value v) :
    Steps ν (.merge v e) (.merge v e') := by
  apply hs.lift (.merge v)
  intro a b hs
  exact ⟨hs.1,by simp [step_merge_eq,(show v.isValue = true from hv),step_isValue_false hs.2,hs.2]⟩

/-- Constructing an adapter result never activates a supplied function or type closure. -/
theorem Adapts.terminates (hd : Adapts Δ a b code) :
    Context.Valid Δ → ∀ θ, Closing θ Δ → ∀ ν, Value ν →
      ∀ v, ValueType .empty v (a.subst θ) →
        ∃ w, Terminates ν (.app (code.subst θ) v) w := by
  apply Adapts.rec
    (motive_1 := fun Δ a _ code _ => Context.Valid Δ → ∀ θ, Closing θ Δ →
      ∀ ν, Value ν → ∀ v, ValueType .empty v (a.subst θ) →
        ∃ w, Terminates ν (.app (code.subst θ) v) w)
    (motive_2 := fun Δ r _ es _ => Context.Valid Δ → ∀ θ, Closing θ Δ →
      WellFormed Δ r → ∀ v, ValueType .empty v (.record (r.subst θ)) →
        ∃ ws, FieldSteps (.pair .unit v) (es.subst θ) ws ∧ Value ws)
    (t := hd)
  all_goals intros
  all_goals intros
  case equal =>
    rename_i Δ a b wa wb he hΔ θ hc ν hν v hv
    refine ⟨v,?_⟩
    simpa [identityAdapter,Term.close,Term.subst,Term.ix] using
      (Terminates.close_lam_app (a := a.subst θ) hν hv.1 (ix_zero_terminates hv.1))
  case arrow =>
    rename_i a b c d Δ down up hne hd hu ihd ihu hΔ θ hc ν hν v hv
    have he : Value (.pair .unit v) := by simpa [Value,Term.isValue] using hv.1
    refine ⟨.clo (.pair .unit v) (c.subst θ)
      ((Term.app up (.app (.ix 1) (.app down (.ix 0)))).subst θ),?_⟩
    apply Terminates.close_lam_app hν hv.1
    exact ⟨.single ⟨he,rfl⟩,he⟩
  case all =>
    rename_i Δ k gs a hs b body wa wb hne hg hb ih hΔ θ hc ν hν v hv
    have he : Value (.pair .unit v) := by simpa [Value,Term.isValue] using hv.1
    refine ⟨.tclo (.pair .unit v) k (gs.subst θ.lift)
      ((Term.app body (.tapp (.ix 0) (Arg.variable k 0))).subst θ.lift),?_⟩
    apply Terminates.close_lam_app hν hv.1
    exact ⟨.single ⟨he,rfl⟩,he⟩
  case nil =>
    rename_i Δ r hΔ θ hc wr v hv
    exact ⟨.nil,.refl,rfl⟩
  case cons =>
    rename_i a Δ b code r fs es l hl hd hfs ihd ihfs hΔ θ hc wr v hv
    obtain ⟨vs,rfl⟩ := hv.2.value_shape hv.1
    have hw := (WellFormed.record wr).subst hc.respects
    have hf := hv.2.value_record_inv hv.1 hw.record_row
    obtain ⟨x,hx,hxt⟩ := hf.lookup .empty (wr.lookup_subst hc.respects hl)
    have he : Value (.pair .unit (.record vs)) := by simpa [Value,Term.isValue] using hv.1
    obtain ⟨w,hw⟩ := ihd hΔ θ hc (.pair .unit (.record vs)) he x
      ⟨Term.lookup_value vs hv.1 hx,hxt⟩
    have hhead := hw.replace_argument (get_ix_terminates hv.1 hx)
    obtain ⟨ws,hws,hvs⟩ := ihfs hΔ θ hc wr (.record vs) hv
    exact ⟨.cons l w ws,
      by simpa [Term.subst,Term.ix] using
        ((FieldSteps.cons_left hhead.1).trans (hws.cons_right hhead.2)),
      Bool.and_eq_true_iff.mpr ⟨hhead.2,hvs⟩⟩
  case sameTail =>
    rename_i Δ r s es wr ws hne hp hfs ihfs hΔ θ hc ν hν v hv
    obtain ⟨vs,rfl⟩ := hv.2.value_shape hv.1
    obtain ⟨fields,hfields,hvf⟩ := ihfs hΔ θ hc wr.record_row (.record vs) hv
    have wenv : WellFormed Δ (.prod .unit (.record r)) := .prod .unit wr
    have henv : ValueType .empty (.pair .unit (.record vs))
        (.prod .unit (.record (r.subst θ))) :=
      ⟨by simpa [Value,Term.isValue] using hv.1,.pair (.unit .unit) hv.2⟩
    have hsource := hv.2.value_record_inv hv.1 (wr.subst hc.respects).record_row
    have hall : ∀ l ∈ r.knownLabels, ∃ a, (r.subst θ).lookup l = some a := by
      intro l hl
      obtain ⟨a,ha⟩ := r.mem_lookup hl
      exact ⟨a.subst θ,wr.record_row.lookup_subst hc.respects ha⟩
    have hdrop := drop_ix_terminates hv.1 (hsource.selection_check _ hall)
    have hfcode := (HasType.record (hfs.typing .unit wr.record_row ws.record_row.sortedFields .unit)).subst
      hΔ hc.respects
    have hftyped := hfields.record.preservation henv hfcode .empty
    have hft := hftyped.value_record_inv hvf ((ws.record_row.sortedFields).subst hc.respects)
    have hdcode : HasType Δ (.prod .unit (.record r)) (.drop r.knownLabels (.ix 0))
        (.record (r.drop r.knownLabels)) :=
      .drop (.snd (.query wenv)) wr.record_row.knownLabels_nodup (fun l hl => r.mem_lookup hl)
    have hdtyped := hdrop.1.preservation henv (hdcode.subst hΔ hc.respects) .empty
    have hdt := hdtyped.value_record_inv hdrop.2 ((wr.record_row.drop _).subst hc.respects)
    have hcheck := hft.merge_check hdt ((sameTail_disjoint ws.record_row hp).subst hc.respects)
    have hbody : Terminates (.pair .unit (.record vs))
        (.merge (.record (es.subst θ)) (.drop r.knownLabels (.ix 0)))
        (.record (fields.append (vs.filter (fun l => !r.knownLabels.contains l)))) := by
      refine ⟨(hfields.record.merge_left.trans (hdrop.1.merge_right hvf)).trans
        (.single ⟨henv.1,?_⟩),Term.append_value fields hvf hdrop.2⟩
      have hv₁ : (Term.record fields).isValue = true := hvf
      have hv₂ : (Term.record (vs.filter (fun l => !r.knownLabels.contains l))).isValue = true := hdrop.2
      simp only [step_merge_eq,hv₁,hv₂,Bool.not_true,Bool.false_eq_true,↓reduceIte,hcheck]
    refine ⟨.record (fields.append (vs.filter (fun l => !r.knownLabels.contains l))),?_⟩
    simpa [sameTailAdapter,Term.subst,Term.close,Term.ix] using
      (Terminates.close_lam_app (a := .record (r.subst θ)) hν hv.1 hbody)
  case closed =>
    rename_i Δ r s es wr ws hne hs hp hfs ihfs hΔ θ hc ν hν v hv
    obtain ⟨fields,hfields,hvf⟩ := ihfs hΔ θ hc wr.record_row v hv
    refine ⟨.record fields,?_⟩
    simpa [closedRecordAdapter,Term.subst,Term.close] using
      (Terminates.close_lam_app (a := .record (r.subst θ)) hν hv.1
        (show Terminates (.pair .unit v) (.record (es.subst θ)) (.record fields) from
          ⟨hfields.record,hvf⟩))

/-- T2.2: frozen canonical adapter code terminates on every typed input value. -/
theorem adapter_termination : Goals.AdapterTermination := by
  intro Δ a b h code ν v θ hΔ hd wh hc hν hv
  obtain ⟨w,hw⟩ := hd.terminates hΔ θ hc ν hν.1 v hv
  have whθ := wh.subst hc.respects
  have htyped : HasType .empty (h.subst θ) (.app (code.subst θ) v) (b.subst θ) :=
    .app ((hd.typing.2.2 h wh).subst hΔ hc.respects) (hv.inclusion whθ)
  exact ⟨w,hw,valueType_of_typed_value (hw.1.preservation hν htyped .empty) hw.2⟩

end LeanSce.Target

/-! ## Adapter Correctness -/

namespace LeanSce.Target

/-- T2.3: exact shape follows from full adapter typing, substitution, safety,
    and exact-record value inversion. -/
theorem adapter_exact_shape : Goals.AdapterExactShape := by
  intro Δ a h r code ν v w θ hΔ hd wh hc hν hv hterm
  have whθ := wh.subst hc.respects
  have htyped : HasType .empty (h.subst θ) (.app (code.subst θ) v)
      (.record (r.subst θ)) :=
    .app ((hd.typing.2.2 h wh).subst hΔ hc.respects) (hv.inclusion whθ)
  exact typed_record_result htyped .empty hν hterm

/-- T2.4: strict evaluation plus total construction on values preserves and
    reflects actual infinite reduction traces. -/
theorem adapter_divergence : Goals.AdapterDivergence := by
  intro Δ a b h code ν e θ hΔ hd he hc hν
  have wh := he.ambient_wf
  have heθ := he.subst hΔ hc.respects
  have hcθ := (hd.typing.2.2 h wh).subst hΔ hc.respects
  exact total_application_diverges_iff heθ hcθ .empty hν
    (fun v hv => hd.terminates hΔ θ hc ν hν.1 v hv)

end LeanSce.Target

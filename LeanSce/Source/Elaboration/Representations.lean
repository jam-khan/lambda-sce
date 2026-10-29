import LeanSce.Source.Elaboration.Typing
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.CanonicalForms
import LeanSce.Source.Metatheory.Records
import LeanSce.Target.Metatheory.Values

/-!
# Source / Elaboration / Representations

Proofs and supporting constructions for representations.
-/

/-! ## Correspondence Properties -/

namespace LeanSce.Source

/-- Every source value has its canonical concrete target representation. -/
theorem Related.erase (v : Term s) (hv : Value v) : Related v v.erase := by
  induction v <;> simp only [Value,Term.isValue,Bool.and_eq_true,
    Bool.false_eq_true] at hv
  all_goals try contradiction
  case unit => exact .unit
  case int => exact .int
  case bool => exact .bool
  case string => exact .string
  case pair a b ia ib => exact .pair (ia hv.1) (ib hv.2)
  case inl t a ih => exact .inl (ih hv)
  case inr t a ih => exact .inr (ih hv)
  case tag l a ih => exact .tag (ih hv)
  case record fs ih => exact .record (ih hv) (.refl _)
  case pack u t a ih => exact .pack (ih hv)
  case fold t a ih => exact .fold (ih hv)
  case clo cap t body ih _ => exact .clo (ih hv) .canonical
  case rclo cap a b body ih _ => exact .rclo (ih hv) .canonical
  case tclo cap k gs body ih _ => exact .tclo (ih hv) .canonical
  case nil => exact .nil
  case cons l e fs ie ifs => exact .cons (ie hv.1) (ifs hv.2)
  case moduleVal cap c i o body ih _ =>
    cases cap <;> simp only [Term.isValue,Bool.false_eq_true] at hv
    all_goals try contradiction
    exact .moduleCaptured (ih hv) .canonical
  case resid m saved j k o im is =>
    simpa only [Term.erase,show m.isValue = true from hv.1,
      show saved.isValue = true from hv.2,↓reduceIte] using Related.resid (im hv.1) (is hv.2)

/-- An elaborated source value is related to the actual chosen representation. -/
theorem Elaborates.value_related (he : Elaborates e E) (hv : Value e) : Related e E := by
  revert hv
  apply Elaborates.rec
    (motive_1 := fun e E _ => Value e → Related e E)
    (motive_2 := fun _ _ _ => True)
    (t := he)
  all_goals intros
  all_goals try trivial
  all_goals intros
  all_goals simp only [Value,Term.isValue,Bool.and_eq_true,
    Bool.false_eq_true]
    at *
  all_goals try contradiction
  case canonical => rename_i e hv; exact Related.erase e hv
  case pair => rename_i _ _ _ _ _ _ ia ib hv; exact .pair (ia hv.1) (ib hv.2)
  case inl => rename_i _ _ _ _ ih hv; exact .inl (ih hv)
  case inr => rename_i _ _ _ _ ih hv; exact .inr (ih hv)
  case tag => rename_i _ _ _ _ ih hv; exact .tag (ih hv)
  case record => rename_i _ _ _ ih hv; exact .record (ih hv) (.refl _)
  case cons => rename_i _ _ _ _ _ _ _ ia ib hv; exact .cons (ia hv.1) (ib hv.2)
  case pack => rename_i _ _ _ _ _ ih hv; exact .pack (ih hv)
  case fold => rename_i _ _ _ _ ih hv; exact .fold (ih hv)
  case value => assumption
  case resid => simp_all

/-- Runtime typing excludes malformed module captures; valuehood is then
    reflected by the canonical compiler. -/
theorem HasType.erase_reflects_value (ht : HasType Δ h e a)
    (hv : Target.Value e.erase) : Value e := by
  revert hv
  apply HasType.rec
    (motive_1 := fun _ _ e _ _ => Target.Value e.erase → Value e)
    (motive_2 := fun _ _ fs _ _ => Target.Value fs.erase → Value fs)
    (motive_3 := fun _ _ _ _ _ => True)
    (t := ht)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case moduleVal =>
    rename_i Δ h cap c i o body wh vc hc wi wo hd hb _ _ htarget
    obtain ⟨fs,rfl⟩ := hc.value_shape vc
    exact vc
  case resid =>
    rename_i m Δ j k o h saved vm hm hs wj wk hd _ _ htarget
    by_cases hv : (m.isValue && saved.isValue) = true
    · exact hv
    · simp only [Term.erase,hv,↓reduceIte,Target.Value,Target.Term.isValue,
        Bool.false_eq_true] at htarget
  all_goals simp_all [Term.erase,Value,Term.isValue,Target.Value,Target.Term.isValue,
    Templates.sandbox,Templates.captured,Templates.run,Templates.link,Templates.provide,
    Target.Term.close,Target.Term.letIn]

theorem FieldsType.erase_reflects_value (ht : FieldsType Δ h fs r)
    (hv : Target.Value fs.erase) : Value fs := by
  revert hv
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ fs _ _ => Target.Value fs.erase → Value fs)
    (motive_3 := fun _ _ _ _ _ => True)
    (t := ht)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil => rfl
  case cons =>
    rename_i Δ h e a fs r l he hf hd _ ih hv
    have hh : Target.Value e.erase ∧ Target.Value fs.erase := by
      simpa only [Term.erase,Target.Value,Target.Term.isValue,Bool.and_eq_true] using hv
    exact Bool.and_eq_true_iff.mpr ⟨he.erase_reflects_value hh.1,ih hh.2⟩

end LeanSce.Source

/-! ## Correspondence Substitution -/

namespace LeanSce.Source

private theorem target_fields_subst_list (fs : Target.Fields) (σ : Target.Subst) :
    (fs.subst σ).toList = fs.toList.map (fun p => (p.1,p.2.subst σ)) := by
  cases fs with
  | nil => rfl
  | cons l e fs => simp [Target.Term.subst,Target.Term.toList,target_fields_subst_list fs σ]
termination_by sizeOf fs

local macro "runtime_subst_cases" : tactic => `(tactic| (
  all_goals intros
  all_goals intros
  case canonical =>
    rename_i e σ
    rw [← Term.erase_subst]
    exact .canonical
  all_goals try simp only [Term.subst,Target.Term.subst]
  case record =>
    exact .record (by apply_assumption)
  case record =>
    rename_i fs gs hs hr hp ih σ
    apply Related.record (ih σ)
    simpa only [target_fields_subst_list] using
      hp.map (fun p => (p.1,p.2.subst (Subst.erase σ)))
  all_goals try simp only [Templates.sandbox,Templates.captured,Templates.run,
    Templates.link,Templates.provide,Templates.residual,Templates.residualBody,
    Target.Term.close,Target.Term.letIn,Target.Term.ix,Target.Term.subst,Target.Ty.subst]
  all_goals try simp only [← Ty.erase_subst,← Arg.erase_subst,← Subst.erase_lift]
  case value => apply Elaborates.value; apply_assumption
  case pair => apply Elaborates.pair <;> apply_assumption
  case resid =>
    rename_i m M saved S j k o hm hn hs ihm ihs σ
    apply Elaborates.resid (ihm σ)
    · simpa only [Value,Term.isValue_subst] using hn
    · exact ihs σ
  all_goals first
    | (apply Elaborates.value <;> apply_assumption)
    | (apply Elaborates.pair <;> apply_assumption)
    | (apply Elaborates.fst <;> apply_assumption)
    | (apply Elaborates.snd <;> apply_assumption)
    | (apply Elaborates.box <;> apply_assumption)
    | (apply Elaborates.lam <;> apply_assumption)
    | (apply Elaborates.recfn <;> apply_assumption)
    | (apply Elaborates.app <;> apply_assumption)
    | (apply Elaborates.inl <;> apply_assumption)
    | (apply Elaborates.inr <;> apply_assumption)
    | (apply Elaborates.case <;> apply_assumption)
    | (apply Elaborates.tag <;> apply_assumption)
    | (apply Elaborates.find <;> apply_assumption)
    | (apply Elaborates.record <;> apply_assumption)
    | (apply Elaborates.cons <;> apply_assumption)
    | (apply Elaborates.get <;> apply_assumption)
    | (apply Elaborates.merge <;> apply_assumption)
    | (apply Elaborates.take <;> apply_assumption)
    | (apply Elaborates.drop <;> apply_assumption)
    | (apply Elaborates.relabel <;> apply_assumption)
    | (apply Elaborates.tlam <;> apply_assumption)
    | (apply Elaborates.tapp <;> apply_assumption)
    | (apply Elaborates.pack <;> apply_assumption)
    | (apply Elaborates.unpack <;> apply_assumption)
    | (apply Elaborates.fold <;> apply_assumption)
    | (apply Elaborates.unfold <;> apply_assumption)
    | (apply Elaborates.prim <;> apply_assumption)
    | (apply Elaborates.ite <;> apply_assumption)
    | (apply Elaborates.letVal <;> apply_assumption)
    | (apply Elaborates.view <;> apply_assumption)
    | (apply Elaborates.module <;> apply_assumption)
    | (apply Elaborates.capture <;> apply_assumption)
    | (apply Elaborates.run <;> apply_assumption)
    | (apply Elaborates.link <;> apply_assumption)
    | (apply Elaborates.provide <;> apply_assumption)
    | (apply Elaborates.complete <;> apply_assumption)
    | (apply Elaborates.resid <;> apply_assumption)
    | (apply Elaborates.invoke <;> apply_assumption)
    | (apply Related.unit <;> apply_assumption)
    | (apply Related.int <;> apply_assumption)
    | (apply Related.bool <;> apply_assumption)
    | (apply Related.string <;> apply_assumption)
    | (apply Related.pair <;> apply_assumption)
    | (apply Related.inl <;> apply_assumption)
    | (apply Related.inr <;> apply_assumption)
    | (apply Related.tag <;> apply_assumption)
    | (apply Related.pack <;> apply_assumption)
    | (apply Related.fold <;> apply_assumption)
    | (apply Related.nil <;> apply_assumption)
    | (apply Related.cons <;> apply_assumption)
    | (apply Related.clo <;> apply_assumption)
    | (apply Related.rclo <;> apply_assumption)
    | (apply Related.tclo <;> apply_assumption)
    | (apply Related.moduleCaptured <;> apply_assumption)
    | (apply Related.moduleSandbox <;> apply_assumption)
    | (apply Related.resid <;> apply_assumption)

))

/-- Static instantiation preserves runtime elaboration, including stored bodies
    and the value-priority boundary for residual modules. -/
theorem Elaborates.subst (he : Elaborates e E) (σ : Subst) :
    Elaborates (e.subst σ) (E.subst (Subst.erase σ)) := by
  apply Elaborates.rec
    (motive_1 := fun e E _ => ∀ σ, Elaborates (e.subst σ) (E.subst (Subst.erase σ)))
    (motive_2 := fun v V _ => ∀ σ, Related (v.subst σ) (V.subst (Subst.erase σ)))
    (t := he)
  runtime_subst_cases

/-- Runtime value correspondence is stable under the same static substitution. -/
theorem Related.subst (hr : Related v V) (σ : Subst) :
    Related (v.subst σ) (V.subst (Subst.erase σ)) := by
  apply Related.rec
    (motive_1 := fun e E _ => ∀ σ, Elaborates (e.subst σ) (E.subst (Subst.erase σ)))
    (motive_2 := fun v V _ => ∀ σ, Related (v.subst σ) (V.subst (Subst.erase σ)))
    (t := hr)
  runtime_subst_cases

end LeanSce.Source

/-! ## Correspondence Records -/

namespace LeanSce.Target

theorem Term.toList_labels (fs : Fields) : fs.toList.map Prod.fst = fs.labels := by
  cases fs with
  | nil => rfl
  | cons l e fs => simp only [Term.toList,List.map_cons,Term.labels,Term.toList_labels fs]
termination_by sizeOf fs

theorem Term.toList_append (fs gs : Fields) :
    (fs.append gs).toList = fs.toList ++ gs.toList := by
  cases fs with
  | nil => rfl
  | cons l e fs => simp only [Term.append,Term.toList,List.cons_append,Term.toList_append fs gs]
termination_by sizeOf fs

theorem Term.toList_filter (fs : Fields) (p : String → Bool) :
    (fs.filter p).toList = fs.toList.filter (fun x => p x.1) := by
  cases fs with
  | nil => rfl
  | cons l e fs =>
    cases hp : p l <;> simp [Term.filter,Term.toList,hp,Term.toList_filter fs p]
termination_by sizeOf fs

theorem Term.toList_renameFields (fs : Fields) :
    (fs.renameFields old new).toList =
      fs.toList.map (fun x => (if x.1 == old then new else x.1,x.2)) := by
  cases fs with
  | nil => rfl
  | cons l e fs => simp [Term.renameFields,Term.toList,Term.toList_renameFields fs]
termination_by sizeOf fs

private theorem lookup_perm_list (hp : xs.Perm ys) :
    (xs.map Prod.fst).Nodup → ∀ l,
      (Term.ofList xs).lookup l = (Term.ofList ys).lookup l := by
  induction hp with
  | nil => intros; rfl
  | cons x hp ih =>
    intro hn l
    have ht := (List.nodup_cons.mp hn).2
    simp only [Term.ofList,Term.lookup]
    split <;> first | rfl | exact ih ht l
  | swap x y xs =>
    intro hn l
    have hxy : y.1 ≠ x.1 := by
      have hh := (List.nodup_cons.mp hn).1
      exact fun he => hh (by simp [he])
    by_cases hlx : l = x.1 <;> by_cases hly : l = y.1
    all_goals simp_all [Term.ofList,Term.lookup]
  | trans hp hq ihp ihq =>
    intro hn l
    exact (ihp hn l).trans (ihq ((hp.map Prod.fst).nodup_iff.mp hn) l)

/-- Completed exact records have order-independent lookup. -/
theorem Term.lookup_perm {fs gs : Fields} (hp : fs.toList.Perm gs.toList) (hn : fs.labels.Nodup) :
    fs.lookup l = gs.lookup l := by
  simpa only [Term.ofList_toList] using
    lookup_perm_list hp (by simpa only [Term.toList_labels] using hn) l

end LeanSce.Target

namespace LeanSce.Source

theorem Related.fields_labels {fs : Fields} {Fs : Target.Fields}
    (hr : Related fs Fs) : fs.labels = Fs.labels := by
  cases hr with
  | nil => rfl
  | cons hv hf => simp only [Term.labels,Target.Term.labels,Related.fields_labels hf]
termination_by sizeOf fs

theorem Related.fields_lookup {fs : Fields} {Fs : Target.Fields}
    (hr : Related fs Fs) (hl : fs.lookup l = some v) :
    ∃ V, Fs.lookup l = some V ∧ Related v V := by
  cases hr with
  | nil => cases hl
  | cons hv hf =>
    simp only [Term.lookup] at hl
    split at hl
    · cases hl
      exact ⟨_,by simp_all [Target.Term.lookup],hv⟩
    · obtain ⟨V,hV,hrel⟩ := hf.fields_lookup hl
      exact ⟨V,by simp_all [Target.Term.lookup],hrel⟩
termination_by sizeOf fs

theorem Related.fields_append {fs gs : Fields} {Fs Gs : Target.Fields}
    (hf : Related fs Fs) (hg : Related gs Gs) :
    Related (fs.append gs) (Fs.append Gs) := by
  cases hf with
  | nil => exact hg
  | cons hv ht => exact .cons hv (ht.fields_append hg)
termination_by sizeOf fs

theorem Related.fields_filter {fs : Fields} {Fs : Target.Fields}
    (hf : Related fs Fs) (p : String → Bool) :
    Related (fs.filter p) (Fs.filter p) := by
  cases hf with
  | nil => exact .nil
  | cons hv ht =>
    simp only [Term.filter,Target.Term.filter]
    split
    · exact .cons hv (ht.fields_filter p)
    · exact ht.fields_filter p
termination_by sizeOf fs

theorem Related.fields_relabel {fs : Fields} {Fs : Target.Fields} (hf : Related fs Fs) :
    Related (fs.renameFields old new) (Fs.renameFields old new) := by
  cases hf with
  | nil => exact .nil
  | cons hv ht => exact .cons hv ht.fields_relabel
termination_by sizeOf fs

theorem Related.record_labels (hr : Related (.record fs) (.record Fs)) :
    fs.labels.Perm Fs.labels := by
  cases hr with
  | record hf hp =>
    have hh := hp.map Prod.fst
    simpa only [Target.Term.toList_labels,← hf.fields_labels] using hh

theorem Related.record_shape (hr : Related v V) (ht : HasType Δ h v (.record r))
    (hΔ : Context.Valid Δ) :
    ∃ fs Fs, v = .record fs ∧ V = .record Fs ∧
      fs.labels.Nodup ∧ Related (.record fs) (.record Fs) := by
  obtain ⟨fs,rfl⟩ := ht.value_shape hr.values.1
  have hf := ht.value_record_inv hr.values.1 (ht.result_wf hΔ).record_row
  cases hr with
  | record hfields hp => exact ⟨_,_,rfl,rfl,hf.labels_nodup,.record hfields hp⟩

theorem Related.record_lookup (hr : Related (.record fs) (.record Fs))
    (hn : fs.labels.Nodup) (hl : fs.lookup l = some v) :
    ∃ V, Fs.lookup l = some V ∧ Related v V := by
  cases hr with
  | record hf hp =>
    obtain ⟨V,hV,hrel⟩ := hf.fields_lookup hl
    exact ⟨V,((Target.Term.lookup_perm hp (by rw [← hf.fields_labels]; exact hn)).symm.trans hV),hrel⟩

theorem Related.records_append (hf : Related (.record fs) (.record Fs))
    (hg : Related (.record gs) (.record Gs)) :
    Related (.record (fs.append gs)) (.record (Fs.append Gs)) := by
  cases hf with
  | record hf hp =>
    cases hg with
    | record hg hq =>
      exact .record (hf.fields_append hg) (by
        simpa only [Target.Term.toList_append] using hp.append hq)

theorem Related.record_prepend (hx : Related x X)
    (hf : Related (.record fs) (.record Fs)) :
    Related (.record (.cons l x fs)) (.record (.cons l X Fs)) := by
  cases hf with
  | record hf hp => exact .record (.cons hx hf) (.cons _ hp)

theorem Related.records_filter (hf : Related (.record fs) (.record Fs)) (p : String → Bool) :
    Related (.record (fs.filter p)) (.record (Fs.filter p)) := by
  cases hf with
  | record hf hp =>
    exact .record (hf.fields_filter p) (by
      simpa only [Target.Term.toList_filter] using hp.filter (fun x => p x.1))

theorem Related.records_relabel (hf : Related (.record fs) (.record Fs)) :
    Related (.record (fs.renameFields old new)) (.record (Fs.renameFields old new)) := by
  cases hf with
  | record hf hp =>
    exact .record hf.fields_relabel (by
      simpa only [Target.Term.toList_renameFields] using
        hp.map (fun x => (if x.1 == old then new else x.1,x.2)))

inductive RelatedList : List Expr → List Target.Expr → Prop where
  | nil : RelatedList [] []
  | cons : Related v V → RelatedList vs Vs → RelatedList (v::vs) (V::Vs)

theorem RelatedList.append (ha : RelatedList xs Xs) (hb : RelatedList ys Ys) :
    RelatedList (xs ++ ys) (Xs ++ Ys) := by
  induction ha with
  | nil => exact hb
  | cons hx _ ih => exact .cons hx ih

theorem Related.findTags (hr : Related v V) (l : String) :
    RelatedList (v.findTags l) (V.findTags l) := by
  cases hr
  all_goals simp only [Term.findTags,Target.Term.findTags]
  all_goals try exact .nil
  case pair ha hb => exact (ha.findTags l).append (hb.findTags l)
  case tag hv =>
    split
    · exact .cons hv .nil
    · exact .nil
termination_by sizeOf v

theorem Related.find_singleton (hr : Related v V) (hl : v.findTags l = [x]) :
    ∃ X, V.findTags l = [X] ∧ Related x X := by
  have singleton : ∀ xs, RelatedList [x] xs → ∃ X, xs = [X] ∧ Related x X := by
    intro xs hx
    cases hx with
    | cons hx ht => cases ht; exact ⟨_,rfl,hx⟩
  have hh := hr.findTags l
  rw [hl] at hh
  exact singleton _ hh

theorem Related.evalPrim {fs : Fields} {Fs : Target.Fields}
    (hr : Related fs Fs) (he : evalPrim p fs = some v) :
    ∃ V, Target.evalPrim p Fs = some V ∧ Related v V := by
  cases p <;> cases hr <;> try simp only [evalPrim] at he
  all_goals try contradiction
  all_goals rename_i l x X fs Fs hx hfs
  all_goals cases hx <;> try simp only [evalPrim] at he
  all_goals try contradiction
  all_goals cases hfs <;> try simp only [evalPrim] at he
  all_goals try contradiction
  all_goals first
    | (cases he; exact ⟨_,rfl,.string⟩)
    | skip
  all_goals rename_i y Y tail Tail k hy htail
  all_goals cases hy <;> try simp only [evalPrim] at he
  all_goals try contradiction
  all_goals cases htail <;> try simp only [evalPrim] at he
  all_goals try contradiction
  all_goals cases he
  all_goals first
    | exact ⟨_,rfl,.int⟩
    | exact ⟨_,rfl,.bool⟩
    | exact ⟨_,rfl,.string⟩

end LeanSce.Source

/-! ## Execution Elaboration Inversion -/

namespace LeanSce.Source

theorem Elaborates.pair_inv (he : Elaborates (.pair a b) E) :
    ∃ A B, E = .pair A B ∧ Elaborates a A ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr with | pair ha hb => exact ⟨_,_,rfl,.value ha,.value hb⟩
  | pair ha hb => exact ⟨_,_,rfl,ha,hb⟩

theorem Elaborates.fst_inv (he : Elaborates (.fst a) E) :
    ∃ A, E = .fst A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | fst ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.snd_inv (he : Elaborates (.snd a) E) :
    ∃ A, E = .snd A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | snd ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.box_inv (he : Elaborates (.box a b) E) :
    ∃ A B, E = .box A B ∧ Elaborates a A ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr
  | box ha hb => exact ⟨_,_,rfl,ha,hb⟩

theorem Elaborates.lam_inv (he : Elaborates (.lam a b) E) :
    ∃ B, E = .lam a.erase B ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | lam hb => exact ⟨_,rfl,hb⟩

theorem Elaborates.recfn_inv (he : Elaborates (.recfn a t b) E) :
    ∃ B, E = .recfn a.erase t.erase B ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | recfn hb => exact ⟨_,rfl,hb⟩

theorem Elaborates.app_inv (he : Elaborates (.app a b) E) :
    ∃ A B, E = .app A B ∧ Elaborates a A ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr
  | app ha hb => exact ⟨_,_,rfl,ha,hb⟩

theorem Elaborates.inl_inv (he : Elaborates (.inl t a) E) :
    ∃ A, E = .inl t.erase A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr with | inl ha => exact ⟨_,rfl,.value ha⟩
  | inl ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.inr_inv (he : Elaborates (.inr t a) E) :
    ∃ A, E = .inr t.erase A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr with | inr ha => exact ⟨_,rfl,.value ha⟩
  | inr ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.case_inv (he : Elaborates (.case a b c) E) :
    ∃ A B C, E = .case A B C ∧ Elaborates a A ∧ Elaborates b B ∧ Elaborates c C := by
  cases he with
  | canonical => exact ⟨_,_,_,rfl,.canonical,.canonical,.canonical⟩
  | value hr => cases hr
  | case ha hb hc => exact ⟨_,_,_,rfl,ha,hb,hc⟩

theorem Elaborates.tag_inv (he : Elaborates (.tag l a) E) :
    ∃ A, E = .tag l A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr with | tag ha => exact ⟨_,rfl,.value ha⟩
  | tag ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.find_inv (he : Elaborates (.find l a) E) :
    ∃ A, E = .find l A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | find ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.get_inv (he : Elaborates (.get a l) E) :
    ∃ A, E = .get A l ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | get ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.merge_inv (he : Elaborates (.merge a b) E) :
    ∃ A B, E = .merge A B ∧ Elaborates a A ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr
  | merge ha hb => exact ⟨_,_,rfl,ha,hb⟩

theorem Elaborates.take_inv (he : Elaborates (.take ls a) E) :
    ∃ A, E = .take ls A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | take ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.drop_inv (he : Elaborates (.drop ls a) E) :
    ∃ A, E = .drop ls A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | drop ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.relabel_inv (he : Elaborates (.relabel l k a) E) :
    ∃ A, E = .relabel l k A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | relabel ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.tlam_inv (he : Elaborates (.tlam k gs a) E) :
    ∃ A, E = .tlam k gs.erase A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | tlam ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.tapp_inv (he : Elaborates (.tapp a u) E) :
    ∃ A, E = .tapp A u.erase ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | tapp ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.pack_inv (he : Elaborates (.pack u t a) E) :
    ∃ A, E = .pack u.erase t.erase A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr with | pack ha => exact ⟨_,rfl,.value ha⟩
  | pack ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.unpack_inv (he : Elaborates (.unpack a b) E) :
    ∃ A B, E = .unpack A B ∧ Elaborates a A ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr
  | unpack ha hb => exact ⟨_,_,rfl,ha,hb⟩

theorem Elaborates.fold_inv (he : Elaborates (.fold t a) E) :
    ∃ A, E = .fold t.erase A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr with | fold ha => exact ⟨_,rfl,.value ha⟩
  | fold ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.unfold_inv (he : Elaborates (.unfold a) E) :
    ∃ A, E = .unfold A ∧ Elaborates a A := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | unfold ha => exact ⟨_,rfl,ha⟩

theorem Elaborates.prim_inv (he : Elaborates (.prim p fs) E) :
    ∃ Fs, E = .prim p Fs ∧ Elaborates fs Fs := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | prim hf => exact ⟨_,rfl,hf⟩

theorem Elaborates.ite_inv (he : Elaborates (.ite a b c) E) :
    ∃ A B C, E = .ite A B C ∧ Elaborates a A ∧ Elaborates b B ∧ Elaborates c C := by
  cases he with
  | canonical => exact ⟨_,_,_,rfl,.canonical,.canonical,.canonical⟩
  | value hr => cases hr
  | ite ha hb hc => exact ⟨_,_,_,rfl,ha,hb,hc⟩

theorem Elaborates.letVal_inv (he : Elaborates (.letVal t a b) E) :
    ∃ A B, E = .letIn A B ∧ Elaborates a A ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr
  | letVal ha hb => exact ⟨_,_,rfl,ha,hb⟩

theorem Elaborates.view_inv (he : Elaborates (.view a b cd e) E) :
    ∃ C E₀, E = .app C E₀ ∧ Elaborates cd C ∧ Elaborates e E₀ := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr
  | view hc he => exact ⟨_,_,rfl,hc,he⟩

theorem Elaborates.module_inv (he : Elaborates (.module i o b) E) :
    ∃ B, E = Templates.sandbox i.erase B ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | module hb => exact ⟨_,rfl,hb⟩

theorem Elaborates.capture_inv (he : Elaborates (.capture c i o cap b) E) :
    ∃ C B, E = .app (Templates.captured c.erase i.erase B) C ∧ Elaborates cap C ∧ Elaborates b B := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr
  | capture hc hb => exact ⟨_,_,rfl,hc,hb⟩

theorem Elaborates.run_inv (he : Elaborates (.run p i o cd m e) E) :
    ∃ C M P, E = .app (.app (Templates.run p.erase i.erase o.erase C) M) P ∧ Elaborates cd C ∧ Elaborates m M ∧ Elaborates e P := by
  cases he with
  | canonical => exact ⟨_,_,_,rfl,.canonical,.canonical,.canonical⟩
  | value hr => cases hr
  | run hc hm hp => exact ⟨_,_,_,rfl,hc,hm,hp⟩

theorem Elaborates.link_inv (he : Elaborates (.link p i o cd e m) E) :
    ∃ C P M, E = .app (.app (Templates.link p.erase i.erase o.erase C) P) M ∧ Elaborates cd C ∧ Elaborates e P ∧ Elaborates m M := by
  cases he with
  | canonical => exact ⟨_,_,_,rfl,.canonical,.canonical,.canonical⟩
  | value hr => cases hr
  | link hc hp hm => exact ⟨_,_,_,rfl,hc,hp,hm⟩

theorem Elaborates.provide_inv (he : Elaborates (.provide p j k o cd e m) E) :
    ∃ C P M, E = .app (.app (Templates.provide p.erase j.erase k.erase o.erase C) P) M ∧ Elaborates cd C ∧ Elaborates e P ∧ Elaborates m M := by
  cases he with
  | canonical => exact ⟨_,_,_,rfl,.canonical,.canonical,.canonical⟩
  | value hr => cases hr
  | provide hc hp hm => exact ⟨_,_,_,rfl,hc,hp,hm⟩

theorem Elaborates.complete_inv (he : Elaborates (.complete o m) E) :
    ∃ M, E = .app (.app (Templates.run .empty .empty o.erase (.close (.lam (.record .empty) (.ix 0)))) M) (.record .nil) ∧ Elaborates m M := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => cases hr
  | complete hm => exact ⟨_,rfl,hm⟩

theorem Elaborates.invoke_inv (he : Elaborates (.invoke i o m p) E) :
    ∃ M P, E = .app M P ∧ Elaborates m M ∧ Elaborates p P := by
  cases he with
  | canonical => exact ⟨_,_,rfl,.canonical,.canonical⟩
  | value hr => cases hr
  | invoke hm hp => exact ⟨_,_,rfl,hm,hp⟩

theorem Elaborates.record_nonvalue_inv (he : Elaborates (.record fs) E) (hn : ¬ Value fs) :
    ∃ Fs, E = .record Fs ∧ Elaborates fs Fs := by
  cases he with
  | canonical => exact ⟨_,rfl,.canonical⟩
  | value hr => exact False.elim (hn hr.values.1)
  | record hf => exact ⟨_,rfl,hf⟩

theorem Elaborates.resid_nonvalue_inv (he : Elaborates (.resid m saved j k o) E)
    (hm : Value m) (hn : ¬ Value saved) :
    ∃ M S, E = .app (.app (Templates.residual j.erase k.erase o.erase) M) S ∧
      Related m M ∧ Elaborates saved S := by
  have hs : saved.isValue = false := by
    cases hh : saved.isValue <;> first | rfl | exact False.elim (hn hh)
  cases he with
  | canonical =>
    refine ⟨_,_,?_,Related.erase m hm,.canonical⟩
    simp only [Term.erase,(show m.isValue = true from hm),hs,Bool.true_and,
      Bool.false_eq_true,↓reduceIte]
  | value hr => exact False.elim (hn (Bool.and_eq_true_iff.mp hr.values.1).2)
  | resid hr _ he => exact ⟨_,_,rfl,hr,he⟩

end LeanSce.Source

/-! ## Certificate Correspondence -/

namespace LeanSce.Source

/-- Runtime elaboration translates the stored certificate body. Its explicit
    unit sandbox survives unchanged and no matching is rerun. -/
theorem CertType.closed_elaboration (hc : CertType Δ a b cd) (he : Elaborates cd C) :
    ∃ code CODE, cd = .close code ∧ C = .close CODE ∧
      HasType Δ .unit code (.arr a b) ∧ Elaborates code CODE := by
  cases hc with
  | closed _ ht =>
    obtain ⟨U,B,rfl,hU,hB⟩ := he.box_inv
    obtain rfl := hU.unit_inv
    exact ⟨_,_,rfl,rfl,ht,hB⟩

end LeanSce.Source

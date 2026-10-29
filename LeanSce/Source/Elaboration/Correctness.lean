import LeanSce.Source.Elaboration.ExecutionRelation
import LeanSce.Source.Elaboration.ModuleExecution
import LeanSce.Source.Elaboration.Representations
import LeanSce.Source.Metatheory.Adapters
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.Evaluation
import LeanSce.Source.Metatheory.Substitution
import LeanSce.Target.Metatheory.Safety

/-!
# Source / Elaboration / Correctness

Proofs and supporting constructions for correctness.
-/

/-! ## Execution Fundamental -/

namespace LeanSce.Source

/-- The common calculus uses structural induction only for constructors which
    spend no evaluation step of their own. Activations use the smaller-budget
    hypothesis, including recursive calls and instantiated stored bodies. -/
theorem HasType.finite_of_heads (small : SmallCorrespondence n)
    (heads : SourceHeadCorrespondence n) (ht : HasType Δ h e a) :
    Context.Valid Δ → ElaborationComputes n Δ h e := by
  have aux : HasType Δ h e a → Context.Valid Δ → ElaborationComputes n Δ h e := by
    apply HasType.rec
      (motive_1 := fun Δ h e a _ => HasType Δ h e a →
        Context.Valid Δ → ElaborationComputes n Δ h e)
      (motive_2 := fun Δ h fs r _ => FieldsType Δ h fs r → Context.Valid Δ →
        ∀ Fs ν N, Elaborates fs Fs → ValueType Δ ν h → Related ν N →
          FiniteCorrespondence n ν (.record fs) N (.record Fs))
      (motive_3 := fun _ _ _ _ _ => True)
      (t := ht)
    all_goals intros
    all_goals try trivial
    all_goals intros
    all_goals try unfold ElaborationComputes
    all_goals intros
    all_goals rename_i typed hΔ E ν N he hν henv
    case query =>
      cases he with
      | canonical =>
        exact .creation ⟨.single (query_step hν.1),hν.1⟩
          ⟨.single (Target.query_step henv.values.2),henv.values.2⟩ henv
      | value hr => cases hr
    case unit => exact .value he rfl
    case int => exact .value he rfl
    case bool => exact .value he rfl
    case string => exact .value he rfl
    case pair =>
      rename_i ha hb ia ib
      obtain ⟨A,B,rfl,hA,hB⟩ := he.pair_inv
      exact (ia ha hΔ A ν N hA hν henv).pair (ib hb hΔ B ν N hB hν henv)
    case fst =>
      rename_i hx _
      obtain ⟨A,rfl,hA⟩ := he.fst_inv
      exact finite_unary small hΔ typed hx hA hν henv strict_fst Target.strict_fst
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
        (fun _ _ _ hr _ hs => hr.fst_step henv hs)
    case snd =>
      rename_i hx _
      obtain ⟨A,rfl,hA⟩ := he.snd_inv
      exact finite_unary small hΔ typed hx hA hν henv strict_snd Target.strict_snd
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
        (fun _ _ _ hr _ hs => hr.snd_step henv hs)
    case box =>
      rename_i ha hb ia ib
      obtain ⟨A,B,rfl,hA,hB⟩ := he.box_inv
      apply (ia ha hΔ A ν N hA hν henv).native_box henv
      intro cap Cap hcap hr
      exact ib hb hΔ B cap Cap hB
        (valueType_of_typed_value (hcap.1.preservation hν ha hΔ) hcap.2) hr
    case lam =>
      obtain ⟨B,rfl,hB⟩ := he.lam_inv
      exact .creation ⟨.single ⟨hν.1,rfl⟩,hν.1⟩
        ⟨.single ⟨henv.values.2,rfl⟩,henv.values.2⟩ (.clo henv hB)
    case recfn =>
      obtain ⟨B,rfl,hB⟩ := he.recfn_inv
      exact .creation ⟨.single ⟨hν.1,rfl⟩,hν.1⟩
        ⟨.single ⟨henv.values.2,rfl⟩,henv.values.2⟩ (.rclo henv hB)
    case app =>
      rename_i hf hx _ _
      obtain ⟨F,X,rfl,hF,hX⟩ := he.app_inv
      exact finite_app small hΔ hf hx hF hX hν henv
    case inl =>
      rename_i wb hx ih
      obtain ⟨A,rfl,hA⟩ := he.inl_inv
      exact (ih hx hΔ A ν N hA hν henv).constructor strict_inl Target.strict_inl
        (fun _ hv => hv) (fun _ hv => hv) (fun _ _ hr => .inl hr)
    case inr =>
      rename_i wa hx ih
      obtain ⟨A,rfl,hA⟩ := he.inr_inv
      exact (ih hx hΔ A ν N hA hν henv).constructor strict_inr Target.strict_inr
        (fun _ hv => hv) (fun _ hv => hv) (fun _ _ hr => .inr hr)
    case case =>
      rename_i Δ h x a b left c right hx hl hr _ _ _
      obtain ⟨A,L,R,rfl,hA,hL,hR⟩ := he.case_inv
      exact finite_unary (C := fun x => .case x left right) (D := fun X => .case X L R)
        small hΔ typed hx hA hν henv strict_case Target.strict_case
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
        (fun _ _ _ hv _ hs => hv.case_step henv hL hR hs)
    case tag =>
      rename_i hx ih
      obtain ⟨A,rfl,hA⟩ := he.tag_inv
      exact (ih hx hΔ A ν N hA hν henv).constructor strict_tag Target.strict_tag
        (fun _ hv => hv) (fun _ hv => hv) (fun _ _ hr => .tag hr)
    case find =>
      rename_i hx hu _
      obtain ⟨A,rfl,hA⟩ := he.find_inv
      exact finite_unary small hΔ typed hx hA hν henv strict_find Target.strict_find
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
        (fun _ _ _ hr _ hs => hr.find_step henv hs)
    case record =>
      rename_i Δ h fs r hf ih
      by_cases hv : Value fs
      · exact .value he hv
      obtain ⟨Fs,rfl,hFs⟩ := he.record_nonvalue_inv hv
      exact ih hf hΔ Fs ν N hFs hν henv
    case get =>
      rename_i hx hl _
      obtain ⟨A,rfl,hA⟩ := he.get_inv
      apply finite_unary small hΔ typed hx hA hν henv strict_get Target.strict_get
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
      intro v V hv hr e' hs
      obtain ⟨fs,Fs,rfl,rfl,hn,hr'⟩ := hr.record_shape (hv.1.preservation hν hx hΔ) hΔ
      exact hr'.get_step hn henv hs
    case merge =>
      rename_i hx hy hd _ _
      obtain ⟨A,B,rfl,hA,hB⟩ := he.merge_inv
      apply finite_binary small hΔ typed hx hy hA hB hν henv
        strict_merge_left Target.strict_merge_left
        (fun _ hv => strict_merge_right hv) (fun _ hv => Target.strict_merge_right hv)
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
      intro v V w W hv hw hrv hrw e' hs
      obtain ⟨fs,Fs,rfl,rfl,_,hrv⟩ := hrv.record_shape (hv.1.preservation hν hx hΔ) hΔ
      obtain ⟨gs,Gs,rfl,rfl,_,hrw⟩ := hrw.record_shape (hw.1.preservation hν hy hΔ) hΔ
      exact hrv.merge_step hrw henv hs
    case take =>
      rename_i hx hn hl _
      obtain ⟨A,rfl,hA⟩ := he.take_inv
      apply finite_unary small hΔ typed hx hA hν henv strict_take Target.strict_take
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
      intro v V hv hr e' hs
      obtain ⟨fs,Fs,rfl,rfl,_,hr⟩ := hr.record_shape (hv.1.preservation hν hx hΔ) hΔ
      exact hr.take_step henv hs
    case drop =>
      rename_i hx hn hl _
      obtain ⟨A,rfl,hA⟩ := he.drop_inv
      apply finite_unary small hΔ typed hx hA hν henv strict_drop Target.strict_drop
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
      intro v V hv hr e' hs
      obtain ⟨fs,Fs,rfl,rfl,_,hr⟩ := hr.record_shape (hv.1.preservation hν hx hΔ) hΔ
      exact hr.drop_step henv hs
    case relabel =>
      rename_i hx hl hn hd _
      obtain ⟨A,rfl,hA⟩ := he.relabel_inv
      apply finite_unary small hΔ typed hx hA hν henv strict_relabel Target.strict_relabel
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
      intro v V hv hr e' hs
      obtain ⟨fs,Fs,rfl,rfl,_,hr⟩ := hr.record_shape (hv.1.preservation hν hx hΔ) hΔ
      exact hr.relabel_step henv hs
    case tlam =>
      obtain ⟨B,rfl,hB⟩ := he.tlam_inv
      exact .creation ⟨.single ⟨hν.1,rfl⟩,hν.1⟩
        ⟨.single ⟨henv.values.2,rfl⟩,henv.values.2⟩ (.tclo henv hB)
    case tapp =>
      rename_i hx hk hu hg _
      obtain ⟨A,rfl,hA⟩ := he.tapp_inv
      exact finite_unary small hΔ typed hx hA hν henv strict_tapp Target.strict_tapp
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
        (fun _ _ _ hr _ hs => hr.tapp_step henv hs)
    case pack =>
      rename_i wa hk hu hg hx ih
      obtain ⟨A,rfl,hA⟩ := he.pack_inv
      exact (ih hx hΔ A ν N hA hν henv).constructor strict_pack Target.strict_pack
        (fun _ hv => hv) (fun _ hv => hv) (fun _ _ hr => .pack hr)
    case unpack =>
      rename_i Δ h x k gs a b body hx wb hb _ _
      obtain ⟨A,B,rfl,hA,hB⟩ := he.unpack_inv
      exact finite_unary (C := fun x => .unpack x body) (D := fun X => .unpack X B)
        small hΔ typed hx hA hν henv strict_unpack Target.strict_unpack
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
        (fun _ _ _ hr _ hs => hr.unpack_step henv hB hs)
    case fold =>
      rename_i wa hx ih
      obtain ⟨A,rfl,hA⟩ := he.fold_inv
      exact (ih hx hΔ A ν N hA hν henv).constructor strict_fold Target.strict_fold
        (fun _ hv => hv) (fun _ hv => hv) (fun _ _ hr => .fold hr)
    case unfold =>
      rename_i hx _
      obtain ⟨A,rfl,hA⟩ := he.unfold_inv
      exact finite_unary small hΔ typed hx hA hν henv strict_unfold Target.strict_unfold
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
        (fun _ _ _ hr _ hs => hr.unfold_step henv hs)
    case ite =>
      rename_i Δ h cond x a y hc ha hb _ _ _
      obtain ⟨C,A,B,rfl,hC,hA,hB⟩ := he.ite_inv
      exact finite_unary (C := fun c => .ite c x y) (D := fun c => .ite c A B)
        small hΔ typed hc hC hν henv strict_ite Target.strict_ite
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
        (fun _ _ _ hr _ hs => hr.ite_step henv hA hB hs)
    case clo => apply FiniteCorrespondence.value he; assumption
    case rclo => apply FiniteCorrespondence.value he; assumption
    case tclo => apply FiniteCorrespondence.value he; assumption
    case moduleVal =>
      rename_i wh vc hc wi wo hd hb _ _
      obtain ⟨fs,rfl⟩ := hc.value_shape vc
      exact .value he vc
    case resid =>
      rename_i vm hm hs wj wk hd _ ih
      exact FiniteCorrespondence.residual vm he henv
        (fun S helab => ih hs hΔ S ν N helab hν henv)
    case value => apply FiniteCorrespondence.value he; assumption
    case conv => rename_i old heq wa ih; exact ih old hΔ E ν N he hν henv
    case nil =>
      obtain rfl := he.nil_inv
      exact .value .canonical rfl
    case cons =>
      rename_i hx hf hd ix ifs
      obtain ⟨X,Fs,rfl,hX,hFs⟩ := he.cons_inv
      exact (ix hx hΔ X ν N hX hν henv).record_cons (ifs hf hΔ Fs ν N hFs hν henv)
    case conv => rename_i old heq wa ih; exact ih old hΔ E ν N he hν henv
    case letVal | view | module | capture | run | link | provide | complete | invoke =>
      exact heads _ _ _ _ hΔ typed rfl E ν N he hν henv
    case add | eqInt | concat =>
      rename_i hx hy _ _
      obtain ⟨Fs,rfl,hFs⟩ := he.prim_inv
      obtain ⟨X,tail,rfl,hX,hTail⟩ := hFs.cons_inv
      obtain ⟨Y,last,rfl,hY,hLast⟩ := hTail.cons_inv
      obtain rfl := hLast.nil_inv
      apply finite_binary small hΔ typed hx hy hX hY hν henv
        strict_prim_left Target.strict_prim_left
        (fun _ hv => strict_prim_right hv) (fun _ hv => Target.strict_prim_right hv)
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
      intro v V w W _ _ hv hw e' hs
      exact (Related.cons hv (.cons hw .nil)).prim_step henv hs
    case showInt =>
      rename_i hx _
      obtain ⟨Fs,rfl,hFs⟩ := he.prim_inv
      obtain ⟨X,tail,rfl,hX,hTail⟩ := hFs.cons_inv
      obtain rfl := hTail.nil_inv
      exact finite_unary small hΔ typed hx hX hν henv strict_prim_one Target.strict_prim_one
        (fun _ _ hv => by cases hv) (fun _ _ hv => by cases hv)
        (fun _ _ _ hr _ hs => (Related.cons hr .nil).prim_step henv hs)
  exact aux ht

end LeanSce.Source

/-! ## Execution Correspondence -/

namespace LeanSce.Source

theorem HasType.finite_from_head_family
    (heads : ∀ n, SmallCorrespondence n → SourceHeadCorrespondence n)
    (ht : HasType Δ h e a) (hΔ : Context.Valid Δ) (n : Nat) :
    ElaborationComputes n Δ h e := by
  have hall : ∀ n, ∀ (Δ : Context) (h a : Typ) (e : Expr),
      HasType Δ h e a → Context.Valid Δ → ElaborationComputes n Δ h e := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      have small : SmallCorrespondence n := by
        intro m hm Δ h a e E ν N hΔ ht he hν henv
        exact ih m hm Δ h a e ht hΔ E ν N he hν henv
      intro Δ h a e ht hΔ
      exact ht.finite_of_heads small (heads n small) hΔ
  exact hall n Δ h a e ht hΔ

theorem termination_correspondence_of_heads
    (heads : ∀ n, SmallCorrespondence n → SourceHeadCorrespondence n) :
    Goals.TerminationCorrespondence := by
  intro Δ h a e ν E N θ hΔ ht he hθ hν henv
  have hclosed := ht.subst hΔ hθ.respects
  have hElab := he.subst θ
  constructor
  · intro v hv
    obtain ⟨n,hn⟩ := hv.counted
    exact (hclosed.finite_from_head_family heads .empty n
      _ ν N hElab hν henv).1 n (Nat.le_refl _) v hn
  · intro V hV
    obtain ⟨n,hn⟩ := hV.counted
    exact (hclosed.finite_from_head_family heads .empty n
      _ ν N hElab hν henv).2 n (Nat.le_refl _) V hn

/-- Safety and determinism turn the proved finite equivalence into actual
    infinite-trace equivalence. Divergence is not redefined as nontermination. -/
theorem divergence_correspondence_of_termination (hterm : Goals.TerminationCorrespondence) :
    Goals.DivergenceCorrespondence := by
  intro Δ h a e ν E N θ hΔ ht he hθ hν henv
  have hclosed := ht.subst hΔ hθ.respects
  have hElab := he.subst θ
  have htarget := hclosed.elaborates .empty hElab
  have hN : Target.ValueType .empty N ((h.subst θ).erase) :=
    ⟨henv.values.2,hν.2.elaborates .empty (.value henv)⟩
  have hfinite := hterm Δ h a e ν E N θ hΔ ht he hθ hν henv
  rw [diverges_iff_not_terminates hclosed .empty hν,
    Target.diverges_iff_not_terminates htarget .empty hN]
  constructor
  · intro hn hV
    obtain ⟨V,hV⟩ := hV
    obtain ⟨v,hv,_⟩ := hfinite.2 V hV
    exact hn ⟨v,hv⟩
  · intro hn hv
    obtain ⟨v,hv⟩ := hv
    obtain ⟨V,hV,_⟩ := hfinite.1 v hv
    exact hn ⟨V,hV⟩

end LeanSce.Source

/-! ## Execution Correctness -/

namespace LeanSce.Source

/-- S1.5: every permitted runtime elaboration preserves and reflects actual
    terminating executions, with related literal results. -/
theorem termination_correspondence : Goals.TerminationCorrespondence :=
  termination_correspondence_of_heads (fun _ small => source_heads small)

/-- S1.6: the same complete elaboration preserves and reflects infinite traces. -/
theorem divergence_correspondence : Goals.DivergenceCorrespondence :=
  divergence_correspondence_of_termination termination_correspondence

end LeanSce.Source

/-! ## Separate Compilation -/

namespace LeanSce.Source

/-- An assembled artifact has the advertised type and exactly the source's
    terminating results and divergence, at every closing instance and caller. -/
def ArtifactCorrect (Δ : Context) (h a : Typ) (e : Expr) (E : Target.Expr) : Prop :=
  Elaborates e E ∧ Target.HasType Δ.erase h.erase E a.erase ∧
  ∀ θ ν N, Closing θ Δ → ValueType .empty ν (h.subst θ) → Related ν N →
    ((∀ v, Terminates ν (e.subst θ) v →
        ∃ V, Target.Terminates N (E.subst (Subst.erase θ)) V ∧ Related v V) ∧
     (∀ V, Target.Terminates N (E.subst (Subst.erase θ)) V →
        ∃ v, Terminates ν (e.subst θ) v ∧ Related v V)) ∧
    (Diverges ν (e.subst θ) ↔ Target.Diverges N (E.subst (Subst.erase θ)))

theorem elaboration_artifact (ht : HasType Δ h e a) (he : Elaborates e E)
    (hΔ : Context.Valid Δ) : ArtifactCorrect Δ h a e E := by
  refine ⟨he,ht.elaborates hΔ he,?_⟩
  intro θ ν N hθ hν hr
  exact ⟨termination_correspondence Δ h a e ν E N θ hΔ ht he hθ hν hr,
    divergence_correspondence Δ h a e ν E N θ hΔ ht he hθ hν hr⟩

/-- S2, Run: independently produced component artifacts are combined by the
    fixed interface combinator, without examining either component body. -/
theorem run_separate_compilation (hΔ : Context.Valid Δ)
    (hm : HasType Δ h m (.module i o)) (hp : HasType Δ h provider (.record p))
    (hd : Adapts Δ (.record p) (.record i) cd)
    (hM : Elaborates m M) (hP : Elaborates provider P) :
    ArtifactCorrect Δ h (.record o) (.run p i o cd m provider)
      (.app (.app (Templates.run p.erase i.erase o.erase cd.erase) M) P) :=
  elaboration_artifact (.run hm hp hd.certificate) (.run .canonical hM hP) hΔ

/-- S2, Link: composition retains the provider and executes the independent
    module artifact against the adapted declared imports. -/
theorem link_separate_compilation (hΔ : Context.Valid Δ)
    (hp : HasType Δ h provider (.record p)) (hm : HasType Δ h m (.module i o))
    (hd : Adapts Δ (.record p) (.record i) cd) (hdisj : Disjoint Δ p o)
    (hP : Elaborates provider P) (hM : Elaborates m M) :
    ArtifactCorrect Δ h (.record (.union p o)) (.link p i o cd provider m)
      (.app (.app (Templates.link p.erase i.erase o.erase cd.erase) P) M) :=
  elaboration_artifact (.link hp hm hd.certificate hdisj) (.link .canonical hP hM) hΔ

/-- S2, Provide: the interface combinator constructs a suspended residual
    artifact; it preserves the source's execution timing and divergence. -/
theorem provide_separate_compilation (hΔ : Context.Valid Δ)
    (hp : HasType Δ h provider (.record p)) (hm : HasType Δ h m (.module (.union j k) o))
    (hd : Adapts Δ (.record p) (.record j) cd)
    (hj : WellFormed Δ j) (hk : WellFormed Δ k) (hdisj : Disjoint Δ j k)
    (hP : Elaborates provider P) (hM : Elaborates m M) :
    ArtifactCorrect Δ h (.module k o) (.provide p j k o cd provider m)
      (.app (.app (Templates.provide p.erase j.erase k.erase o.erase cd.erase) P) M) :=
  elaboration_artifact (.provide hp hm hd.certificate hj hk hdisj)
    (.provide .canonical hP hM) hΔ

theorem compile_run : (Term.run p i o cd m provider).erase =
    Target.Term.app (.app (Templates.run p.erase i.erase o.erase cd.erase) m.erase) provider.erase := rfl

theorem compile_link : (Term.link p i o cd provider m).erase =
    Target.Term.app (.app (Templates.link p.erase i.erase o.erase cd.erase) provider.erase) m.erase := rfl

theorem compile_provide : (Term.provide p j k o cd provider m).erase =
    Target.Term.app (.app (Templates.provide p.erase j.erase k.erase o.erase cd.erase) provider.erase) m.erase := rfl

/-- A sandbox's compiled body is independent of the caller ambient type. -/
theorem sandbox_body_independent
    (_h₁ : HasType Δ h₁ (.module i o body) (.module i o))
    (_h₂ : HasType Δ h₂ (.module i o body) (.module i o)) :
    (Term.module i o body).erase = Templates.sandbox i.erase body.erase := rfl

end LeanSce.Source

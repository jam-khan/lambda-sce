import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Constraints
import LeanSce.Target.Metatheory.Rows
import LeanSce.Target.Metatheory.Typing

/-!
# Target / Metatheory / Substitution

Proofs and supporting constructions for substitution.
-/

/-! ## Equality Substitution -/

namespace LeanSce.Target

/-- Pointwise equality of the two kind-indexed substitution images. -/
def Subst.PointwiseEq (σ τ : Subst) : Prop := ∀ k i, TyEq (σ k i) (τ k i)

theorem Subst.PointwiseEq.lift (h : Subst.PointwiseEq σ τ) :
    Subst.PointwiseEq σ.lift τ.lift := by
  intro k i
  cases i with
  | zero => exact .refl
  | succ i => exact (h k i).rename Nat.succ

private theorem rowsCollect_congr (hr : TyEq r r') (hs : TyEq s s') :
    RowsCollect P r s ↔ RowsCollect P r' s' := by
  simp only [rowsCollect_iff_entries]
  constructor
  · intro h x hx y hy
    exact h x (hr.entries_perm.mem_iff.mpr hx) y (hs.entries_perm.mem_iff.mpr hy)
  · intro h x hx y hy
    exact h x (hr.entries_perm.mem_iff.mp hx) y (hs.entries_perm.mem_iff.mp hy)

private theorem Atom.interprets_congr (h : Subst.PointwiseEq σ τ) (a : Atom) :
    a.Interprets P σ ↔ a.Interprets P τ := by
  cases a with
  | labelRow l i => exact rowsCollect_congr .refl (h .row i)
  | rowRow i j => exact rowsCollect_congr (h .row i) (h .row j)

private theorem guardCollects_subst_congr (h : Subst.PointwiseEq σ τ) (g : Guards) :
    Collects P (g.subst σ).guardAtoms ↔ Collects P (g.subst τ).guardAtoms := by
  rw [guardCollects_subst, guardCollects_subst]
  constructor
  · intro hc; exact hc.mono (fun a ha => (Atom.interprets_congr h a).mp ha)
  · intro hc; exact hc.mono (fun a ha => (Atom.interprets_congr h a).mpr ha)

private theorem FreshGuards.atoms_exist (h : FreshGuards k g) : ∃ xs, g.guardAtoms = some xs := by
  cases k with
  | type => change g = .gnil at h; subst g; exact ⟨[], by simp [Ty.guardAtoms]⟩
  | row => obtain ⟨xs,hx,_⟩ := h; exact ⟨xs,hx⟩

private theorem guardsEq_of_collects (hx : g.guardAtoms = some xs)
    (he : ∀ P : Atom → Prop, Collects P g.guardAtoms ↔ Collects P h.guardAtoms) : GuardsEq g h := by
  obtain ⟨ys,hy,hyx⟩ := (he (· ∈ xs)).mp ⟨xs,hx,fun _ ha => ha⟩
  obtain ⟨xs',hx',hxy⟩ := (he (· ∈ ys)).mpr ⟨ys,hy,fun _ ha => ha⟩
  have hxx : xs = xs' := Option.some.inj (hx.symm.trans hx')
  subst xs'
  exact ⟨xs,ys,hx,hy,fun a => ⟨hxy a,hyx a⟩⟩

/-- Equality of substitution images preserves normalized binder constraints. -/
theorem FreshGuards.subst_congr (hf : FreshGuards k g) (he : Subst.PointwiseEq σ τ) :
    GuardsEq (g.subst σ.lift) (g.subst τ.lift) := by
  obtain ⟨xs,hx⟩ := (hf.subst σ).atoms_exist
  exact guardsEq_of_collects hx (fun _ => guardCollects_subst_congr he.lift g)

private def SubstEqProperty {s : TySort} (a : Ty s) (σ τ : Subst) : Prop :=
  match s with
  | .guards => True
  | _ => TyEq (a.subst σ) (a.subst τ)

private theorem subst_congr_property (hw : WellFormed Γ a)
    (he : Subst.PointwiseEq σ τ) : SubstEqProperty a σ τ := by
  induction hw generalizing σ τ with
  | tvar => exact he .type _
  | rvar => exact he .row _
  | unit => exact .refl
  | int => exact .refl
  | bool => exact .refl
  | string => exact .refl
  | prod _ _ ih₁ ih₂ => exact .prod (ih₁ he) (ih₂ he)
  | sum _ _ ih₁ ih₂ => exact .sum (ih₁ he) (ih₂ he)
  | arr _ _ ih₁ ih₂ => exact .arr (ih₁ he) (ih₂ he)
  | tag _ ih => exact .tag (ih he)
  | record _ ih => exact .record (ih he)
  | all hf _ _ _ ih => exact .all (hf.subst_congr he) (ih he.lift)
  | ex hf _ _ _ ih => exact .ex (hf.subst_congr he) (ih he.lift)
  | mu _ ih => exact .mu (ih he.lift)
  | empty => exact .refl
  | field _ ih => exact .field (ih he)
  | union _ _ _ ih₁ ih₂ => exact .union (ih₁ he) (ih₂ he)
  | gnil | gcons => trivial

/-- Equal witnesses yield equal instantiated well-formed ordinary types. -/
theorem WellFormed.subst_congr (hw : WellFormed Γ (a : Typ))
    (he : Subst.PointwiseEq σ τ) : TyEq (a.subst σ) (a.subst τ) :=
  subst_congr_property hw he

inductive ArgEq : Arg → Arg → Prop where
  | type : TyEq a b → ArgEq (.type a) (.type b)
  | row : TyEq r s → ArgEq (.row r) (.row s)

theorem ArgEq.openSubst (h : ArgEq u v) : Subst.PointwiseEq u.openSubst v.openSubst := by
  intro k i
  cases h <;> cases k <;> cases i <;> simp only [Arg.openSubst] <;>
    first | assumption | exact .refl

theorem WellFormed.open_congr (hw : WellFormed Γ (a : Typ)) (he : ArgEq u v) :
    TyEq (a.open u) (a.open v) := hw.subst_congr he.openSubst

/-- Both the body and witness may change by structural equality. -/
theorem TyEq.open_congr (he : TyEq (a : Typ) b) (ha : WellFormed Γ a)
    (hu : ArgEq u v) : TyEq (a.open u) (b.open v) :=
  (ha.open_congr hu).trans (he.subst ha v.openSubst)

theorem GuardsEq.entails_subst (he : GuardsEq g h) (σ : Subst) :
    Entails Δ (g.subst σ) ↔ Entails Δ (h.subst σ) := by
  change Collects (· ∈ Δ.assumptions) (g.subst σ).guardAtoms ↔
    Collects (· ∈ Δ.assumptions) (h.subst σ).guardAtoms
  rw [guardCollects_subst,guardCollects_subst]
  exact he.collects_iff

end LeanSce.Target

/-! ## Static Properties -/

namespace LeanSce.Target

@[simp] theorem Ty.subst_lift_weaken (a : Ty s) (σ : Subst) :
    (a.rename Nat.succ).subst σ.lift = (a.subst σ).rename Nat.succ := by
  simp only [Ty.subst_rename, Ty.rename_subst, Subst.lift]

theorem Ty.subst_open (a : Ty s) (σ : Subst) (u : Arg) :
    (a.open u).subst σ = (a.subst σ.lift).open (u.subst σ) := by
  simp only [Ty.open, Ty.subst_comp]
  congr 1
  funext k i
  cases i with
  | zero => cases k <;> cases u <;> rfl
  | succ i =>
    simp only [Arg.openSubst, Subst.lift]
    simpa only [Ty.subst_var, Ty.open] using (Ty.open_weaken (σ k i) (u.subst σ)).symm

@[simp] theorem Arg.kind_subst (u : Arg) (σ : Subst) : (u.subst σ).kind = u.kind := by
  cases u <;> rfl

theorem Arg.WellFormed.subst {u : Arg} (hu : u.WellFormed Γ) (hs : Subst.Respects Γ Δ σ) :
    (u.subst σ).WellFormed Δ := by
  cases u <;> exact LeanSce.Target.WellFormed.subst hu hs

private theorem Context.Valid.all_extend (hΓ : Context.Valid Γ)
    (hw : WellFormed Γ (.all k g a)) : Context.Valid (Γ.extend k g) := by
  cases hw with | all hf hg _ => exact .extend hΓ hf hg

private theorem Context.Valid.ex_extend (hΓ : Context.Valid Γ)
    (hw : WellFormed Γ (.ex k g a)) : Context.Valid (Γ.extend k g) := by
  cases hw with | ex hf hg _ => exact .extend hΓ hf hg

/-- Static substitution preserves every target typing rule. -/
theorem HasType.subst (ht : HasType Γ h e a) (hΓ : Context.Valid Γ)
    (hs : Subst.Respects Γ Δ σ) : HasType Δ (h.subst σ) (e.subst σ) (a.subst σ) := by
  revert hΓ hs
  revert Δ σ
  apply HasType.rec
    (motive_1 := fun Γ h e a _ => ∀ (Δ : Context) (σ : Subst), Context.Valid Γ →
      Subst.Respects Γ Δ σ → HasType Δ (h.subst σ) (e.subst σ) (a.subst σ))
    (motive_2 := fun Γ h fs r _ => ∀ (Δ : Context) (σ : Subst), Context.Valid Γ →
      Subst.Respects Γ Δ σ → FieldsType Δ (h.subst σ) (fs.subst σ) (r.subst σ))
    (t := ht)
  all_goals intros
  all_goals intros
  case query => rename_i hw Δ σ hΓ hs; exact .query (hw.subst hs)
  case unit => rename_i hw Δ σ hΓ hs; exact .unit (hw.subst hs)
  case int => rename_i hw Δ σ hΓ hs; exact .int (hw.subst hs)
  case bool => rename_i hw Δ σ hΓ hs; exact .bool (hw.subst hs)
  case string => rename_i hw Δ σ hΓ hs; exact .string (hw.subst hs)
  case pair => rename_i ihx ihy Δ σ hΓ hs; exact .pair (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case fst => rename_i ih Δ σ hΓ hs; exact .fst (ih Δ σ hΓ hs)
  case snd => rename_i ih Δ σ hΓ hs; exact .snd (ih Δ σ hΓ hs)
  case box => rename_i ihx ihy Δ σ hΓ hs; exact .box (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case lam => rename_i hw hb ih Δ σ hΓ hs; exact .lam (hw.subst hs) (ih Δ σ hΓ hs)
  case recfn => rename_i wa wb hb ih Δ σ hΓ hs; exact .recfn (wa.subst hs) (wb.subst hs) (ih Δ σ hΓ hs)
  case app => rename_i ihf ihx Δ σ hΓ hs; exact .app (ihf Δ σ hΓ hs) (ihx Δ σ hΓ hs)
  case inl => rename_i wb hx ih Δ σ hΓ hs; exact .inl (wb.subst hs) (ih Δ σ hΓ hs)
  case inr => rename_i wa hx ih Δ σ hΓ hs; exact .inr (wa.subst hs) (ih Δ σ hΓ hs)
  case case => rename_i ihx ihl ihr Δ σ hΓ hs; exact .case (ihx Δ σ hΓ hs) (ihl Δ σ hΓ hs) (ihr Δ σ hΓ hs)
  case tag => rename_i ih Δ σ hΓ hs; exact .tag (ih Δ σ hΓ hs)
  case find => rename_i hx hu ih Δ σ hΓ hs; exact .find (ih Δ σ hΓ hs) (hu.subst σ)
  case record => rename_i ih Δ σ hΓ hs; exact .record (ih Δ σ hΓ hs)
  case get =>
    rename_i hx hl ih Δ σ hΓ hs
    exact .get (ih Δ σ hΓ hs) ((hx.result_wf hΓ).record_row.lookup_subst hs hl)
  case merge => rename_i hx hy hd ihx ihy Δ σ hΓ hs; exact .merge (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs) (hd.subst hs)
  case take =>
    rename_i r ls hx hn hl ih Δ σ hΓ hs
    have hw := (hx.result_wf hΓ).record_row
    have ht := HasType.take (ih Δ σ hΓ hs) hn (fun l hmem => by
      obtain ⟨a,ha⟩ := hl l hmem
      exact ⟨a.subst σ,hw.lookup_subst hs ha⟩)
    exact .conv ht (.record (hw.select_subst hs hl).symm) ((HasType.take hx hn hl).result_wf hΓ |>.subst hs)
  case drop =>
    rename_i r ls hx hn hl ih Δ σ hΓ hs
    have hw := (hx.result_wf hΓ).record_row
    have ht := HasType.drop (ih Δ σ hΓ hs) hn (fun l hmem => by
      obtain ⟨a,ha⟩ := hl l hmem
      exact ⟨a.subst σ,hw.lookup_subst hs ha⟩)
    simpa only [Term.subst, Ty.subst, hw.drop_subst hs hl] using ht
  case relabel =>
    rename_i r l a k hx hl hne hd ih Δ σ hΓ hs
    have hw := (hx.result_wf hΓ).record_row
    have hd' := hd.subst hs
    rw [hw.drop_subst hs (by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact ⟨a,hl⟩)] at hd'
    have ht := HasType.relabel (ih Δ σ hΓ hs) (hw.lookup_subst hs hl) hne hd'
    simpa only [Term.subst, Ty.subst, hw.relabel_subst hs hl] using ht
  case tlam =>
    rename_i hw hh hb ih Δ σ hΓ hs
    have hΓ' := hΓ.all_extend hw
    cases hw with
    | all hf hg ha =>
      apply HasType.tlam ((WellFormed.all hf hg ha).subst hs) (hh.subst hs)
      simpa only [Ty.subst_lift_weaken] using ih _ σ.lift hΓ' (hs.lift hf)
  case tapp =>
    rename_i u hf hk hu hg ih Δ σ hΓ hs
    have ht := HasType.tapp (u := u.subst σ) (ih Δ σ hΓ hs) (by simpa using hk) (hu.subst hs)
      (by simpa only [Ty.subst_open] using hg.subst hs)
    simpa only [Term.subst, Ty.subst_open] using ht
  case pack =>
    rename_i u h e hw hk hu hg hx ih Δ σ hΓ hs
    exact HasType.pack (u := u.subst σ) (hw.subst hs) (by simpa using hk) (hu.subst hs)
      (by simpa only [Ty.subst_open] using hg.subst hs)
      (by simpa only [Ty.subst_open] using ih Δ σ hΓ hs)
  case unpack =>
    rename_i hp wb hb ihp ihb Δ σ hΓ hs
    have hw := hp.result_wf hΓ
    have hΓ' := hΓ.ex_extend hw
    cases hw with
    | ex hf hg ha =>
      apply HasType.unpack (ihp Δ σ hΓ hs) (wb.subst hs)
      simpa only [Ty.subst, Ty.subst_lift_weaken] using ihb _ σ.lift hΓ' (hs.lift hf)
  case fold =>
    rename_i hw hx ih Δ σ hΓ hs
    apply HasType.fold (hw.subst hs)
    simpa only [Ty.subst_open, Arg.subst, Ty.subst] using ih Δ σ hΓ hs
  case unfold =>
    rename_i ih Δ σ hΓ hs
    have ht := HasType.unfold (ih Δ σ hΓ hs)
    simpa only [Term.subst, Ty.subst_open, Arg.subst, Ty.subst] using ht
  case add => rename_i ihx ihy Δ σ hΓ hs; exact .add (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case eqInt => rename_i ihx ihy Δ σ hΓ hs; exact .eqInt (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case showInt => rename_i ih Δ σ hΓ hs; exact .showInt (ih Δ σ hΓ hs)
  case concat => rename_i ihx ihy Δ σ hΓ hs; exact .concat (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case ite => rename_i ihc ihx ihy Δ σ hΓ hs; exact .ite (ihc Δ σ hΓ hs) (ihx Δ σ hΓ hs) (ihy Δ σ hΓ hs)
  case clo =>
    rename_i hh wa hv hc hb ihc ihb Δ σ hΓ hs
    exact .clo (hh.subst hs) (wa.subst hs)
      (by simpa [Value] using hv) (ihc Δ σ hΓ hs) (ihb Δ σ hΓ hs)
  case rclo =>
    rename_i hh wa wb hv hc hb ihc ihb Δ σ hΓ hs
    exact .rclo (hh.subst hs) (wa.subst hs) (wb.subst hs)
      (by simpa [Value] using hv) (ihc Δ σ hΓ hs) (ihb Δ σ hΓ hs)
  case tclo =>
    rename_i hh hw hv hc hb ihc ihb Δ σ hΓ hs
    have hΓ' := hΓ.all_extend hw
    cases hw with
    | all hf hg ha =>
      apply HasType.tclo (hh.subst hs) ((WellFormed.all hf hg ha).subst hs)
        (by simpa [Value] using hv) (ihc Δ σ hΓ hs)
      simpa only [Ty.subst_lift_weaken] using ihb _ σ.lift hΓ' (hs.lift hf)
  case value => rename_i hv ht hh ih Δ σ hΓ hs; exact .value (by simpa [Value] using hv) (ih Δ σ hΓ hs) (hh.subst hs)
  case nil => rename_i hh Δ σ hΓ hs; exact .nil (hh.subst hs)
  case cons => rename_i hx hf hd ihx ihf Δ σ hΓ hs; exact .cons (ihx Δ σ hΓ hs) (ihf Δ σ hΓ hs) (hd.subst hs)
  all_goals
    rename_i ht he hw ih Δ σ hΓ hs
    exact .conv (ih Δ σ hΓ hs) (he.subst (ht.result_wf hΓ) σ) (hw.subst hs)

/-- Field initializers retain order and disjointness under static substitution. -/
theorem FieldsType.subst (ht : FieldsType Γ h fs r) (hΓ : Context.Valid Γ)
    (hs : Subst.Respects Γ Δ σ) : FieldsType Δ (h.subst σ) (fs.subst σ) (r.subst σ) := by
  revert hΓ hs
  revert Δ σ
  apply FieldsType.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Γ h fs r _ => ∀ (Δ : Context) (σ : Subst), Context.Valid Γ →
      Subst.Respects Γ Δ σ → FieldsType Δ (h.subst σ) (fs.subst σ) (r.subst σ))
    (t := ht)
  all_goals intros
  all_goals intros
  all_goals try trivial
  case nil => rename_i hh Δ σ hΓ hs; exact .nil (hh.subst hs)
  case cons =>
    rename_i hx hf hd ihx ihf Δ σ hΓ hs
    exact .cons (hx.subst hΓ hs) (ihf Δ σ hΓ hs) (hd.subst hs)
  case conv =>
    rename_i ht he hw ih Δ σ hΓ hs
    exact .conv (ih Δ σ hΓ hs) (he.subst (ht.result_wf hΓ) σ) (hw.subst hs)

/-- A kind-preserving renaming satisfying all source atoms is an admissible
    parallel substitution. -/
theorem RenRespects.asSubst (hρ : RenRespects Γ Δ ρ) :
    Subst.Respects Γ Δ (Subst.ofRen ρ) := by
  constructor
  · intro k i hi
    cases k with
    | type => exact .tvar (hρ.1 _ _ hi)
    | row => exact .rvar (hρ.1 _ _ hi)
  · intro a ha
    have hr := hρ.2 a ha
    cases a with
    | labelRow l i =>
      refine ⟨[.labelRow l (ρ i)], ?_, ?_⟩
      · simp [Subst.ofRen, Ty.var, Ty.rowAtoms, Ty.entries, crossAtoms, entryAtoms]
      · simpa [Atom.rename] using hr
    | rowRow i j =>
      refine ⟨[.rowRow (min (ρ i) (ρ j)) (max (ρ i) (ρ j))], ?_, ?_⟩
      · simp [Subst.ofRen, Ty.var, Ty.rowAtoms, Ty.entries, crossAtoms, entryAtoms]
      · simpa [Atom.rename] using hr

theorem HasType.rename (ht : HasType Γ h e a) (hΓ : Context.Valid Γ)
    (hρ : RenRespects Γ Δ ρ) : HasType Δ (h.rename ρ) (e.rename ρ) (a.rename ρ) := by
  simpa only [Ty.subst_ofRen, Term.rename] using ht.subst hΓ hρ.asSubst

theorem HasType.weaken (ht : HasType Γ h e a) (hΓ : Context.Valid Γ)
    (k : Kind) (g : Guards) :
    HasType (Γ.extend k g) (h.rename Nat.succ) (e.rename Nat.succ) (a.rename Nat.succ) :=
  ht.rename hΓ (RenRespects.weaken Γ k g)

/-- Opening removes a static binder from expression typing. -/
theorem HasType.open (ht : HasType (Δ.extend k g) h e a)
    (hΓ : Context.Valid (Δ.extend k g)) (hn : Δ.Normal)
    (hk : u.kind = k) (hu : u.WellFormed Δ) (hg : Entails Δ (g.open u)) :
    HasType Δ (h.open u) (e.subst u.openSubst) (a.open u) :=
  ht.subst hΓ (Subst.Respects.open hn hk hu hg)

end LeanSce.Target

/-! ## Closing Properties -/

namespace LeanSce.Target

theorem Closing.empty (θ : Subst) : Closing θ Context.empty := by
  simp [Closing,Context.empty]

/-- The paper's closing-substitution judgment supplies the general static
    substitution theorem's declaration and constraint premises. -/
theorem Closing.respects (hc : Closing θ Δ) : Subst.Respects Δ .empty θ := by
  refine ⟨hc.1, ?_⟩
  intro a ha
  have he := hc.2 a ha
  cases a with
  | labelRow l i =>
    change Collects (· ∈ Context.empty.assumptions)
      (Ty.gcons (.field l .unit) (θ .row i) .gnil).guardAtoms at he
    rw [guardCollects_cons] at he
    exact he.1
  | rowRow i j =>
    change Collects (· ∈ Context.empty.assumptions)
      (Ty.gcons (θ .row i) (θ .row j) .gnil).guardAtoms at he
    rw [guardCollects_cons] at he
    exact he.1

end LeanSce.Target

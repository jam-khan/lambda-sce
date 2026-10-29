import LeanSce.Source.Definitions.Elaboration
import LeanSce.Source.Definitions.Typing
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.CanonicalForms
import LeanSce.Source.Metatheory.Records
import LeanSce.Source.Metatheory.Substitution
import LeanSce.Source.Metatheory.WellFormedness

/-!
# Source / Metatheory / Adapters

Proofs and supporting constructions for adapters.
-/

/-! ## Adapter Rows -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim Atom Entry)

def Ty.joinRows : List Row → Row
  | [] => .empty
  | r::rs => .union r (joinRows rs)

def Ty.fieldsRow (fs : List (String × Typ)) : Row :=
  joinRows (fs.map fun (l,a) => .field l a)

def Ty.tailsRow (is : List Nat) : Row := joinRows (is.map Ty.rvar)

def Ty.parts : Row → List Row
  | .rvar i => [.rvar i]
  | .empty => []
  | .field l a => [.field l a]
  | .union r s => r.parts ++ s.parts

theorem TyEq.empty_union (r : Row) : TyEq (.union .empty r) r :=
  .trans .union_comm .union_empty

theorem TyEq.joinRows_append (xs ys : List Row) :
    TyEq (Ty.joinRows (xs ++ ys)) (.union (Ty.joinRows xs) (Ty.joinRows ys)) := by
  induction xs with
  | nil => exact (TyEq.empty_union _).symm
  | cons x xs ih => exact .trans (.union .refl ih) TyEq.union_assoc.symm

theorem TyEq.joinRows_perm (hp : xs.Perm ys) : TyEq (Ty.joinRows xs) (Ty.joinRows ys) := by
  induction hp with
  | nil => exact .refl
  | cons _ _ ih => exact .union .refl ih
  | swap => exact .trans TyEq.union_assoc.symm (.trans (.union .union_comm .refl) .union_assoc)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Ty.parts_eq (r : Row) : TyEq r (Ty.joinRows r.parts) := by
  cases r with
  | rvar i => simpa [Ty.parts, Ty.joinRows] using (TyEq.union_empty (r := .rvar i)).symm
  | empty => simp [Ty.parts, Ty.joinRows]; exact .refl
  | field l a => simpa [Ty.parts, Ty.joinRows] using (TyEq.union_empty (r := .field l a)).symm
  | union r s => simpa [Ty.parts] using TyEq.trans (.union r.parts_eq s.parts_eq) (TyEq.joinRows_append _ _).symm

theorem Ty.parts_perm (r : Row) :
    r.parts.Perm ((r.knownFields.map fun (l,a) => Ty.field l a) ++ r.tails.map Ty.rvar) := by
  cases r with
  | rvar => simp [Ty.parts, Ty.knownFields, Ty.tails]
  | empty => simp [Ty.parts, Ty.knownFields, Ty.tails]
  | field => simp [Ty.parts, Ty.knownFields, Ty.tails]
  | union r s =>
    have hs := r.parts_perm.append s.parts_perm
    have hp := ((show (r.tails.map Ty.rvar ++ s.knownFields.map (fun (l,a) => Ty.field l a)).Perm
      (s.knownFields.map (fun (l,a) => Ty.field l a) ++ r.tails.map Ty.rvar) from List.perm_append_comm).append_left
      (r.knownFields.map fun (l,a) => Ty.field l a)).append_right (s.tails.map Ty.rvar)
    have he := hs.trans (by simpa [List.append_assoc] using hp)
    simpa [Ty.parts, Ty.knownFields, Ty.tails, List.map_append, List.append_assoc] using he

theorem Ty.decompose (r : Row) :
    TyEq r (.union (Ty.fieldsRow r.knownFields) (Ty.tailsRow r.tails)) :=
  r.parts_eq.trans ((TyEq.joinRows_perm r.parts_perm).trans (TyEq.joinRows_append _ _))

@[simp] theorem disjoint_joinRows_right : Disjoint Δ r (Ty.joinRows xs) ↔
    ∀ s ∈ xs, Disjoint Δ r s := by
  induction xs with
  | nil => simp [Ty.joinRows]
  | cons s xs ih => simp [Ty.joinRows, ih]

theorem WellFormed.joinRows_iff : WellFormed Δ (Ty.joinRows xs) ↔
    (∀ r ∈ xs, WellFormed Δ r) ∧ xs.Pairwise (Disjoint Δ) := by
  induction xs with
  | nil => simp [Ty.joinRows, show WellFormed Δ Ty.empty from .empty]
  | cons r xs ih =>
    constructor
    · intro hw
      cases hw with
      | union hr hxs hd =>
        obtain ⟨ha,hp⟩ := ih.mp hxs
        exact ⟨by simp_all, List.pairwise_cons.mpr ⟨disjoint_joinRows_right.mp hd,hp⟩⟩
    · rintro ⟨ha,hp⟩
      obtain ⟨hd,hp⟩ := List.pairwise_cons.mp hp
      exact .union (ha _ (by simp)) (ih.mpr ⟨fun q hq => ha q (by simp [hq]),hp⟩)
        (disjoint_joinRows_right.mpr hd)

theorem WellFormed.joinRows_perm (hw : WellFormed Δ (Ty.joinRows xs))
    (hp : xs.Perm ys) : WellFormed Δ (Ty.joinRows ys) := by
  obtain ⟨ha,hd⟩ := WellFormed.joinRows_iff.mp hw
  exact WellFormed.joinRows_iff.mpr ⟨fun r hr => ha r (hp.mem_iff.mpr hr),
    hd.perm hp (fun {_ _} h => h.symm)⟩

theorem WellFormed.joinRows_append (hx : WellFormed Δ (Ty.joinRows xs))
    (hy : WellFormed Δ (Ty.joinRows ys))
    (hd : Disjoint Δ (Ty.joinRows xs) (Ty.joinRows ys)) :
    WellFormed Δ (Ty.joinRows (xs ++ ys)) := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
    cases hx with
    | union hx hxs hxxs =>
      obtain ⟨hxy,hxsy⟩ := disjoint_union_left.mp hd
      exact .union hx (ih hxs hxsy)
        (disjoint_joinRows_right.mpr (by
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact disjoint_joinRows_right.mp hxxs r hr
          · exact disjoint_joinRows_right.mp hxy r hr))

theorem WellFormed.parts (hw : WellFormed Δ r) : WellFormed Δ (Ty.joinRows r.parts) := by
  cases hw with
  | rvar h => simpa [Ty.parts, Ty.joinRows] using WellFormed.union (.rvar h) .empty disjoint_empty_right
  | empty => simpa [Ty.parts, Ty.joinRows] using (WellFormed.empty : WellFormed Δ .empty)
  | field h => simpa [Ty.parts, Ty.joinRows] using WellFormed.union (.field h) .empty disjoint_empty_right
  | union hr hs hd =>
    rename_i r s
    simpa [Ty.parts] using WellFormed.joinRows_append hr.parts hs.parts
      (s.parts_eq.disjoint_right (r.parts_eq.disjoint_left hd))

@[simp] theorem disjoint_joinRows_left : Disjoint Δ (Ty.joinRows xs) r ↔
    ∀ s ∈ xs, Disjoint Δ s r := by
  induction xs with
  | nil => simp [Ty.joinRows, disjoint_empty_left]
  | cons s xs ih => simp [Ty.joinRows, ih]

theorem WellFormed.joinRows_split (hw : WellFormed Δ (Ty.joinRows (xs ++ ys))) :
    WellFormed Δ (Ty.joinRows xs) ∧ WellFormed Δ (Ty.joinRows ys) ∧
      Disjoint Δ (Ty.joinRows xs) (Ty.joinRows ys) := by
  obtain ⟨ha,hp⟩ := WellFormed.joinRows_iff.mp hw
  obtain ⟨hpx,hpy,hcross⟩ := List.pairwise_append.mp hp
  exact ⟨WellFormed.joinRows_iff.mpr ⟨fun r hr => ha r (List.mem_append_left _ hr),hpx⟩,
    WellFormed.joinRows_iff.mpr ⟨fun r hr => ha r (List.mem_append_right _ hr),hpy⟩,
    disjoint_joinRows_left.mpr (fun r hr => disjoint_joinRows_right.mpr (hcross r hr))⟩

theorem WellFormed.decomposed (hw : WellFormed Δ r) :
    WellFormed Δ (Ty.fieldsRow r.knownFields) ∧ WellFormed Δ (Ty.tailsRow r.tails) ∧
      Disjoint Δ (Ty.fieldsRow r.knownFields) (Ty.tailsRow r.tails) :=
  (hw.parts.joinRows_perm r.parts_perm).joinRows_split

theorem Ty.sortedFields_perm (r : Row) : r.sortedFields.Perm r.knownFields :=
  List.mergeSort_perm _ _

theorem Ty.fieldsRow_perm (hp : fs.Perm gs) : TyEq (Ty.fieldsRow fs) (Ty.fieldsRow gs) :=
  TyEq.joinRows_perm (hp.map _)

theorem WellFormed.fieldsRow_perm (hw : WellFormed Δ (Ty.fieldsRow fs))
    (hp : fs.Perm gs) : WellFormed Δ (Ty.fieldsRow gs) :=
  hw.joinRows_perm (hp.map _)

theorem WellFormed.sortedFields (hw : WellFormed Δ r) :
    WellFormed Δ (Ty.fieldsRow r.sortedFields) :=
  hw.decomposed.1.fieldsRow_perm r.sortedFields_perm.symm

theorem Ty.sorted_decompose (r : Row) :
    TyEq r (.union (Ty.fieldsRow r.sortedFields) (Ty.tailsRow r.tails)) :=
  r.decompose.trans (.union (Ty.fieldsRow_perm r.sortedFields_perm.symm) .refl)

theorem Ty.drop_to_tails (r : Row) (ls : List String)
    (hls : ∀ l ∈ r.knownLabels, l ∈ ls) :
    TyEq (r.drop ls) (Ty.tailsRow r.tails) := by
  cases r with
  | rvar i => simpa [Ty.drop, Ty.tails, Ty.tailsRow, Ty.joinRows] using
      (TyEq.union_empty (r := .rvar i)).symm
  | empty => simp [Ty.drop, Ty.tails, Ty.tailsRow, Ty.joinRows]; exact .refl
  | field l a =>
    have hl := hls l (by simp [Ty.knownLabels])
    simp [Ty.drop, Ty.tails, Ty.tailsRow, Ty.joinRows,hl]
    exact .refl
  | union r s =>
    have hr := r.drop_to_tails ls (fun l hl => hls l (by simp [Ty.knownLabels,hl]))
    have hs := s.drop_to_tails ls (fun l hl => hls l (by simp [Ty.knownLabels,hl]))
    have he := TyEq.trans (.union hr hs) (TyEq.joinRows_append
      (r.tails.map Ty.rvar) (s.tails.map Ty.rvar)).symm
    simpa [Ty.drop, Ty.tailsRow, Ty.tails, List.map_append] using he

theorem Ty.sameTail_result {r s : Row} (hp : r.tails.Perm s.tails) :
    TyEq (.union (Ty.fieldsRow s.sortedFields) (r.drop r.knownLabels)) s :=
  (TyEq.union .refl ((r.drop_to_tails _ (fun _ h => h)).trans
    (TyEq.joinRows_perm (hp.map Ty.rvar)))).trans s.sorted_decompose.symm

theorem Ty.closed_result (hs : s.tails = []) : TyEq (Ty.fieldsRow s.sortedFields) s := by
  have he := s.sorted_decompose
  simp only [hs, Ty.tailsRow, List.map_nil, Ty.joinRows] at he
  exact (he.trans TyEq.union_empty).symm

theorem WellFormed.knownLabels_nodup (hw : WellFormed Δ r) : r.knownLabels.Nodup := by
  cases hw with
  | rvar => simp [Ty.knownLabels]
  | empty => simp [Ty.knownLabels]
  | field => simp [Ty.knownLabels]
  | union hr hs hd =>
    simpa [Ty.knownLabels] using List.nodup_append.mpr
      ⟨hr.knownLabels_nodup,hs.knownLabels_nodup,by
        intro a ha b hb hab
        subst b
        exact hd.knownLabels a ha hb⟩

theorem sameTail_disjoint {r s : Row} (hs : WellFormed Δ s) (hp : r.tails.Perm s.tails) :
    Disjoint Δ (Ty.fieldsRow s.sortedFields) (r.drop r.knownLabels) := by
  have hd := (Ty.fieldsRow_perm s.sortedFields_perm.symm).disjoint_left hs.decomposed.2.2
  have hd' := (TyEq.joinRows_perm (hp.map Ty.rvar)).symm.disjoint_right hd
  exact (r.drop_to_tails _ (fun _ h => h)).symm.disjoint_right hd'

end LeanSce.Source

/-! ## Certificate Substitution -/

namespace LeanSce.Source

theorem CertType.subst (hc : CertType Γ a b cd) (hΓ : Context.Valid Γ)
    (hs : Subst.Respects Γ Δ σ) :
    CertType Δ (a.subst σ) (b.subst σ) (cd.subst σ) := by
  cases hc with
  | closed hcore ht =>
    exact .closed (by simpa using hcore) (ht.subst hΓ hs)

end LeanSce.Source

/-! ## Adapter Typing -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim Atom Entry liftRen)

theorem Entails.extend_self {Δ : Context} (hf : FreshGuards k g) :
    Entails (Δ.extend k g) g := by
  apply Entails.of_erase
  simpa using Target.Entails.extend_self (Δ := Δ.erase) hf.erase

def Subst.Agree (Γ : Context) (σ τ : Subst) : Prop :=
  ∀ k i, Γ.kinds[i]? = some k → σ k i = τ k i

theorem Subst.Agree.lift (he : Subst.Agree Γ σ τ) :
    Subst.Agree (Γ.extend k gs) σ.lift τ.lift := by
  intro q i hi
  cases i with
  | zero => rfl
  | succ i => simp only [Subst.lift]; rw [he q i (by simpa [Context.extend] using hi)]

theorem WellFormed.subst_ext (hw : WellFormed Γ a) (he : Subst.Agree Γ σ τ) :
    a.subst σ = a.subst τ := by
  induction hw generalizing σ τ with
  | tvar h => exact he .type _ h
  | rvar h => exact he .row _ h
  | unit | int | bool | string | empty | gnil => rfl
  | prod _ _ ih₁ ih₂ => simp only [Ty.subst, ih₁ he, ih₂ he]
  | sum _ _ ih₁ ih₂ => simp only [Ty.subst, ih₁ he, ih₂ he]
  | arr _ _ ih₁ ih₂ => simp only [Ty.subst, ih₁ he, ih₂ he]
  | tag _ ih => simp only [Ty.subst, ih he]
  | record _ ih => simp only [Ty.subst, ih he]
  | all _ _ _ ihg iha => simp only [Ty.subst, ihg he.lift, iha he.lift]
  | ex _ _ _ ihg iha => simp only [Ty.subst, ihg he.lift, iha he.lift]
  | mu _ ih => simp only [Ty.subst, ih he.lift]
  | module _ _ ihi iho => simp only [Ty.subst, ihi he, iho he]
  | field _ ih => simp only [Ty.subst, ih he]
  | union _ _ _ ih₁ ih₂ => simp only [Ty.subst, ih₁ he, ih₂ he]
  | gcons _ _ _ ih₁ ih₂ ih₃ => simp only [Ty.subst, ih₁ he, ih₂ he, ih₃ he]

theorem WellFormed.open_fresh {Δ : Context} (hw : WellFormed (Δ.extend k gs) a) :
    (a.rename (liftRen Nat.succ)).open (Arg.variable k 0) = a := by
  simp only [Ty.open, Ty.subst_rename]
  apply Eq.trans (hw.subst_ext (τ := Subst.id) ?_) (Ty.subst_id a)
  intro q i hi
  cases i with
  | zero =>
    have hq : q = k := by simpa [Context.extend] using hi.symm
    subst q
    cases k <;> rfl
  | succ i => cases q <;> rfl

theorem Arg.variable_wf (Δ : Context) (k : Kind) (gs : Guards) :
    (Arg.variable k 0).WellFormed (Δ.extend k gs) := by
  cases k <;> first | exact WellFormed.tvar rfl | exact WellFormed.rvar rfl

@[simp] theorem Arg.variable_kind (k : Kind) (i : Nat) : (Arg.variable k i).kind = k := by
  cases k <;> rfl

theorem universal_adapter_typed (wa : WellFormed Δ (.all k gs a))
    (wb : WellFormed Δ (.all k hs b)) (he : GuardsEq gs hs)
    (wbody : WellFormed (Δ.extend k gs) b)
    (hb : ∀ h, WellFormed (Δ.extend k gs) h →
      HasType (Δ.extend k gs) h code (.arr a b))
    (hh : WellFormed Δ h) :
    HasType Δ h (universalAdapter (.all k gs a) k gs code)
      (.arr (.all k gs a) (.all k hs b)) := by
  cases wa with
  | all hf wg wa =>
    have win : WellFormed Δ (.all k gs a) := .all hf wg wa
    have wout : WellFormed Δ (.all k gs b) := .all hf wg wbody
    apply HasType.box (.unit hh)
    apply HasType.lam win
    apply HasType.conv (b := .all k hs b) _ (.all he .refl) wb
    apply HasType.tlam wout (.prod .unit win)
    have wenv : WellFormed (Δ.extend k gs) ((Ty.prod .unit (.all k gs a)).rename Nat.succ) :=
      (WellFormed.prod WellFormed.unit win).weaken k gs
    apply HasType.app (hb _ wenv)
    have ht := HasType.tapp (HasType.snd (HasType.query wenv))
      (Arg.variable_kind k 0) (Arg.variable_wf Δ k gs)
      (by simpa only [wg.open_fresh] using (Entails.extend_self (Δ := Δ) hf))
    simpa only [Ty.rename, wa.open_fresh, Term.ix] using ht

/-- Canonical adapters and field adapters are well formed and typed. -/
theorem Adapts.typing (hd : Adapts Δ a b code) :
    WellFormed Δ a ∧ WellFormed Δ b ∧
      ∀ h, WellFormed Δ h → HasType Δ h code (.arr a b) := by
  apply Adapts.rec
    (motive_1 := fun Δ a b code _ => WellFormed Δ a ∧ WellFormed Δ b ∧
      ∀ h, WellFormed Δ h → HasType Δ h code (.arr a b))
    (motive_2 := fun Δ r fs es _ => ∀ h, WellFormed Δ r →
      WellFormed Δ (Ty.fieldsRow fs) → WellFormed Δ h →
      FieldsType Δ (.prod h (.record r)) es (Ty.fieldsRow fs))
    (t := hd)
  all_goals intros
  all_goals intros
  case equal =>
    rename_i wa wb he
    exact ⟨wa,wb,fun h hh => identity_adapter_typed wa wb he hh⟩
  case arrow =>
    rename_i ihd ihu
    exact ⟨.arr ihd.2.1 ihu.1,.arr ihd.1 ihu.2.1,fun h hh =>
      arrow_adapter_typed ihd.2.1 ihu.1 ihd.1 ihu.2.1 ihd.2.2 ihu.2.2 hh⟩
  case sameTail =>
    rename_i Δ r s es wr ws hne hp hfs ihfs
    refine ⟨wr,ws,?_⟩
    intro h hh
    apply HasType.box (.unit hh)
    apply HasType.lam wr
    have hf := ihfs .unit wr.record_row ws.record_row.sortedFields .unit
    have ht : HasType Δ (.prod .unit (.record r)) (.drop r.knownLabels (.ix 0))
        (.record (r.drop r.knownLabels)) :=
      .drop (.snd (.query (.prod .unit wr))) wr.record_row.knownLabels_nodup
        (fun l hl => r.mem_lookup hl)
    apply HasType.conv (.merge (.record hf) ht (sameTail_disjoint ws.record_row hp))
      (.record (Ty.sameTail_result hp)) ws
  case closed =>
    rename_i Δ r s es wr ws hne hs hp hfs ihfs
    refine ⟨wr,ws,?_⟩
    intro h hh
    apply HasType.box (.unit hh)
    apply HasType.lam wr
    exact .conv (.record (ihfs .unit wr.record_row ws.record_row.sortedFields .unit))
      (.record (Ty.closed_result hs)) ws
  case all =>
    rename_i wa wb hne he hcode ih
    exact ⟨wa,wb,fun h hh => universal_adapter_typed wa wb he ih.2.1 ih.2.2 hh⟩
  case nil =>
    rename_i Δ r h wr wf wh
    exact .nil (.prod wh (.record wr))
  case cons =>
    rename_i a Δ b code r fs es l hl hc hfs ihc ihfs h wr wf wh
    have ww : WellFormed Δ (.union (.field l b) (Ty.fieldsRow fs)) := by
      simpa [Ty.fieldsRow, Ty.joinRows] using wf
    cases ww with
    | union wb wtail hdis =>
      have hh : WellFormed Δ (.prod h (.record r)) := .prod wh (.record wr)
      simpa [Ty.fieldsRow, Ty.joinRows, Term.ix] using FieldsType.cons
        (HasType.app (ihc.2.2 _ hh) (.get (.snd (.query hh)) hl))
        (ihfs h wr wtail wh) hdis

/-- Field generation is typed under the saved record argument. -/
theorem AdaptsFields.typing (hd : AdaptsFields Δ r fs es) :
    ∀ h, WellFormed Δ r → WellFormed Δ (Ty.fieldsRow fs) → WellFormed Δ h →
      FieldsType Δ (.prod h (.record r)) es (Ty.fieldsRow fs) := by
  apply AdaptsFields.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Δ r fs es _ => ∀ h, WellFormed Δ r →
      WellFormed Δ (Ty.fieldsRow fs) → WellFormed Δ h →
      FieldsType Δ (.prod h (.record r)) es (Ty.fieldsRow fs))
    (t := hd)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil => rename_i h wr wf wh; exact .nil (.prod wh (.record wr))
  case cons =>
    rename_i a Δ b code r fs es l hl hc hfs ihc ihfs h wr wf wh
    have ww : WellFormed Δ (.union (.field l b) (Ty.fieldsRow fs)) := by
      simpa [Ty.fieldsRow, Ty.joinRows] using wf
    cases ww with
    | union wb wtail hdis =>
      have hh : WellFormed Δ (.prod h (.record r)) := .prod wh (.record wr)
      simpa [Ty.fieldsRow, Ty.joinRows, Term.ix] using FieldsType.cons
        (HasType.app (hc.typing.2.2 _ hh) (.get (.snd (.query hh)) hl))
        (ihfs h wr wtail wh) hdis

end LeanSce.Source

/-! ## Adapter Certificates -/

namespace LeanSce.Source

/-- Canonical source matching emits only kernel operations, even when its type
    annotations mention source modules. -/
theorem Adapts.isCore (hd : Adapts Δ a b code) : code.isCore = true := by
  apply Adapts.rec
    (motive_1 := fun _ _ _ code _ => code.isCore = true)
    (motive_2 := fun _ _ _ es _ => es.isCore = true)
    (t := hd)
  all_goals intros
  all_goals simp_all [identityAdapter, arrowAdapter, sameTailAdapter,
    closedRecordAdapter, universalAdapter, Term.close, Term.ix, Term.isCore]

theorem Adapts.closed_code (hd : Adapts Δ a b code) : ∃ body, code = .close body := by
  cases hd <;> exact ⟨_,rfl⟩

/-- Peeling the explicit unit sandbox retains its body's original typing. -/
theorem HasType.close_inv (ht : HasType Δ h (.close code) a) : HasType Δ .unit code a := by
  have aux : ∀ e a, HasType Δ h e a → ∀ code, e = .close code → HasType Δ .unit code a := by
    intro e a ht
    apply HasType.rec
      (motive_1 := fun Δ _ e a _ => ∀ code, e = .close code → HasType Δ .unit code a)
      (motive_2 := fun _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ => True)
      (t := ht)
    all_goals intros
    all_goals intros
    all_goals try exact True.intro
    case box =>
      rename_i ha hb iha ihb code he
      cases he
      cases ha.value_origin rfl with
      | unit heq => cases heq.shape; exact hb
    case value =>
      rename_i hv ht hh ih code he
      cases he
      cases hv
    case conv =>
      rename_i heq hw ih code he
      exact .conv (ih code he) heq hw
    all_goals rename_i code he; cases he
  exact aux _ _ ht code rfl

/-- U.2: every generated source adapter satisfies the checked source's
    certificate judgment, so surface matching supplies its required evidence. -/
theorem Adapts.certificate (hd : Adapts Δ a b code) : CertType Δ a b code := by
  obtain ⟨body,rfl⟩ := hd.closed_code
  apply CertType.closed
  · simpa only [Term.close,Term.isCore,Bool.true_and] using hd.isCore
  · exact (hd.typing.2.2 .unit .unit).close_inv

end LeanSce.Source

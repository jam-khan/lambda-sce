import LeanSce.Target.Definitions.Typing
import LeanSce.Target.Metatheory.Basic
import LeanSce.Target.Metatheory.Safety
import LeanSce.Target.Metatheory.Substitution
import LeanSce.Target.Metatheory.Typing
import LeanSce.Target.Metatheory.Values

/-!
# Target / Adapters / Typing

Proofs and supporting constructions for typing.
-/

/-! ## Adapter Determinism -/

namespace LeanSce.Target

/-- Priority fixes generated code; proof choices do not affect the adapter. -/
theorem Adapts.deterministic (hd : Adapts Δ a b code) :
    ∀ other, Adapts Δ a b other → code = other := by
  apply Adapts.rec
    (motive_1 := fun Δ a b code _ => ∀ other, Adapts Δ a b other → code = other)
    (motive_2 := fun Δ r fs es _ => ∀ other, AdaptsFields Δ r fs other → es = other)
    (t := hd)
  all_goals intros
  all_goals intros
  case equal =>
    rename_i he other ho
    cases ho <;> first | rfl | contradiction
  case arrow =>
    rename_i hn hdown hup ihd ihu other ho
    cases ho with
    | equal _ _ he => exact False.elim (hn he)
    | arrow _ hd hu => rw [ihd _ hd,ihu _ hu]
  case sameTail =>
    rename_i wr ws hn hp hf ih other ho
    cases ho with
    | equal _ _ he => exact False.elim (hn he)
    | sameTail _ _ _ _ hg => rw [ih _ hg]
    | closed _ _ _ _ hnp _ => exact False.elim (hnp hp)
  case closed =>
    rename_i wr ws hn hs hp hf ih other ho
    cases ho with
    | equal _ _ he => exact False.elim (hn he)
    | sameTail _ _ _ hperm _ => exact False.elim (hp hperm)
    | closed _ _ _ _ _ hg => rw [ih _ hg]
  case all =>
    rename_i wa wb hn he hf ih other ho
    cases ho with
    | equal _ _ he => exact False.elim (hn he)
    | all _ _ _ _ hg => rw [ih _ hg]
  case nil =>
    rename_i other ho
    cases ho
    rfl
  case cons =>
    rename_i hl hd hf ihd ihf other ho
    cases ho with
    | cons hl' hd' hf' =>
      have he := Option.some.inj (hl.symm.trans hl')
      cases he
      rw [ihd _ hd',ihf _ hf']

end LeanSce.Target

/-! ## Adapter Shapes -/

namespace LeanSce.Target

theorem Adapts.head_eq (hd : Adapts Δ a b code) : a.head = b.head := by
  cases hd with
  | equal _ _ he => exact he.head_eq
  | arrow | sameTail | closed | all => rfl

theorem Adapts.record_target (hd : Adapts Δ (.record r) c code) :
    ∃ s, c = .record s := by
  have he := hd.head_eq
  cases c <;> simp_all [Ty.head]

end LeanSce.Target

/-! ## Adapter Rows -/

namespace LeanSce.Target

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

end LeanSce.Target

/-! ## Adapter Typing -/

namespace LeanSce.Target

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

theorem adapter_typing : Goals.AdapterTyping := by
  intro Δ a b h code _ hd hh
  exact hd.typing.2.2 h hh

end LeanSce.Target

/-! ## Closed Syntax -/

namespace LeanSce.Target

theorem Arg.WellFormed.subst_ext {u : Arg} (hu : u.WellFormed Γ)
    (he : Subst.Agree Γ σ τ) : u.subst σ = u.subst τ := by
  cases u <;> simp only [Arg.subst]
  all_goals congr 1; exact LeanSce.Target.WellFormed.subst_ext hu he

/-- A term's static annotations and saved code only use declared variables. -/
theorem HasType.subst_ext (ht : HasType Γ h e a) :
    ∀ σ τ, Subst.Agree Γ σ τ → e.subst σ = e.subst τ := by
  apply HasType.rec
    (motive_1 := fun Γ _ e _ _ => ∀ σ τ, Subst.Agree Γ σ τ → e.subst σ = e.subst τ)
    (motive_2 := fun Γ _ fs _ _ => ∀ σ τ, Subst.Agree Γ σ τ → fs.subst σ = fs.subst τ)
    (t := ht)
  all_goals intros
  all_goals intros
  case query => rfl
  case unit => rfl
  case int => rfl
  case bool => rfl
  case string => rfl
  case pair => rename_i ihx ihy σ τ he; simp only [Term.subst,ihx σ τ he,ihy σ τ he]
  case fst => rename_i ih σ τ he; simp only [Term.subst,ih σ τ he]
  case snd => rename_i ih σ τ he; simp only [Term.subst,ih σ τ he]
  case box => rename_i ihx ihy σ τ he; simp only [Term.subst,ihx σ τ he,ihy σ τ he]
  case lam => rename_i wa _ ih σ τ he; simp only [Term.subst,wa.subst_ext he,ih σ τ he]
  case recfn => rename_i wa wb _ ih σ τ he; simp only [Term.subst,wa.subst_ext he,wb.subst_ext he,ih σ τ he]
  case app => rename_i ihf ihx σ τ he; simp only [Term.subst,ihf σ τ he,ihx σ τ he]
  case inl => rename_i wb _ ih σ τ he; simp only [Term.subst,wb.subst_ext he,ih σ τ he]
  case inr => rename_i wa _ ih σ τ he; simp only [Term.subst,wa.subst_ext he,ih σ τ he]
  case case => rename_i ihx ihl ihr σ τ he; simp only [Term.subst,ihx σ τ he,ihl σ τ he,ihr σ τ he]
  case tag => rename_i ih σ τ he; simp only [Term.subst,ih σ τ he]
  case find => rename_i _ ih σ τ he; simp only [Term.subst,ih σ τ he]
  case record => rename_i ih σ τ he; simp only [Term.subst,ih σ τ he]
  case get => rename_i _ ih σ τ he; simp only [Term.subst,ih σ τ he]
  case merge => rename_i _ ihx ihy σ τ he; simp only [Term.subst,ihx σ τ he,ihy σ τ he]
  case take => rename_i _ _ ih σ τ he; simp only [Term.subst,ih σ τ he]
  case drop => rename_i _ _ ih σ τ he; simp only [Term.subst,ih σ τ he]
  case relabel => rename_i _ _ _ ih σ τ he; simp only [Term.subst,ih σ τ he]
  case tlam =>
    rename_i hw _ _ ih σ τ he
    cases hw with | all _ wg _ => simp only [Term.subst,wg.subst_ext he.lift,ih σ.lift τ.lift he.lift]
  case tapp => rename_i _ hu _ ih σ τ he; simp only [Term.subst,hu.subst_ext he,ih σ τ he]
  case pack => rename_i hw _ hu _ _ ih σ τ he; simp only [Term.subst,hw.subst_ext he,hu.subst_ext he,ih σ τ he]
  case unpack => rename_i ihx ihb σ τ he; simp only [Term.subst,ihx σ τ he,ihb σ.lift τ.lift he.lift]
  case fold => rename_i hw _ ih σ τ he; simp only [Term.subst,hw.subst_ext he,ih σ τ he]
  case unfold => rename_i ih σ τ he; simp only [Term.subst,ih σ τ he]
  case add => rename_i ihx ihy σ τ he; simp only [Term.subst,ihx σ τ he,ihy σ τ he]
  case eqInt => rename_i ihx ihy σ τ he; simp only [Term.subst,ihx σ τ he,ihy σ τ he]
  case showInt => rename_i ih σ τ he; simp only [Term.subst,ih σ τ he]
  case concat => rename_i ihx ihy σ τ he; simp only [Term.subst,ihx σ τ he,ihy σ τ he]
  case ite => rename_i ihc ihx ihy σ τ he; simp only [Term.subst,ihc σ τ he,ihx σ τ he,ihy σ τ he]
  case clo => rename_i _ wa _ _ _ ihc ihb σ τ he; simp only [Term.subst,wa.subst_ext he,ihc σ τ he,ihb σ τ he]
  case rclo => rename_i _ wa wb _ _ _ ihc ihb σ τ he; simp only [Term.subst,wa.subst_ext he,wb.subst_ext he,ihc σ τ he,ihb σ τ he]
  case tclo =>
    rename_i _ hw _ _ _ ihc ihb σ τ he
    cases hw with | all _ wg _ =>
      simp only [Term.subst,wg.subst_ext he.lift,ihc σ τ he,ihb σ.lift τ.lift he.lift]
  case value => rename_i _ ih σ τ he; exact ih σ τ he
  case nil => rfl
  case cons => rename_i _ ihx ihf σ τ he; simp only [Term.subst,ihx σ τ he,ihf σ τ he]
  all_goals rename_i _ _ ih σ τ he; exact ih σ τ he

theorem FieldsType.subst_ext (hf : FieldsType Γ h fs r) (he : Subst.Agree Γ σ τ) :
    fs.subst σ = fs.subst τ :=
  Term.record.inj ((HasType.record hf).subst_ext σ τ he)

/-- Closing a statically closed type cannot change it. -/
theorem WellFormed.closed_subst (hw : WellFormed .empty a) (σ : Subst) : a.subst σ = a := by
  apply Eq.trans (hw.subst_ext (τ := Subst.id) ?_) (Ty.subst_id a)
  intro k i hi
  simp [Context.empty] at hi

/-- A term typed with no static variables is invariant under static substitution. -/
theorem HasType.closed_subst (ht : HasType .empty h e a) (σ : Subst) : e.subst σ = e := by
  apply Eq.trans (ht.subst_ext σ Subst.id ?_) (Term.subst_id e)
  intro k i hi
  simp [Context.empty] at hi

theorem HasType.closed_rename (ht : HasType .empty h e a) (ρ : Nat → Nat) : e.rename ρ = e :=
  ht.closed_subst (Subst.ofRen ρ)

end LeanSce.Target

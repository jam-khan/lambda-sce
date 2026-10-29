import LeanSce.Target.Adapters.Evaluation
import LeanSce.Target.Adapters.Typing
import LeanSce.Target.LogicalRelation.Equality
import LeanSce.Target.LogicalRelation.Functions
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Adapters / Naturality

Proofs and supporting constructions for naturality.
-/

/-! ## Adapter Coherence Naturality -/

namespace LeanSce.Target
open LogicalRelation

@[simp] theorem Arg.variable_open (hk : u.kind = k) :
    (Arg.variable k 0).subst u.openSubst = u := by
  cases u <;> cases k <;> simp_all [Arg.kind,Arg.variable,Arg.subst,Ty.subst,Arg.openSubst]

def AdapterNatural (Δ : Context) (a b : Typ) (code : Expr) : Prop :=
  ∀ n, Context.Valid Δ → ∀ θ, Closing θ Δ → ∀ v V,
    ValRel n (a.subst θ) v V →
    ValRel n (b.subst θ) (adaptedValue (code.subst θ) v) (adaptedValue (code.subst θ) V)

theorem Adapts.natural_lift (hd : Adapts Δ a b code) (hn : AdapterNatural Δ a b code)
    (hΔ : Context.Valid Δ) (hc : Closing θ Δ)
    (he : ExprRel n (a.subst θ) (ν,e) (N,E)) (hν : Value ν) (hN : Value N) :
    ExprRel n (b.subst θ) (ν,.app (code.subst θ) e) (N,.app (code.subst θ) E) := by
  apply he.total_adapters
    (fun v hv => hd.terminates hΔ θ hc ν hν v hv)
    (fun V hV => hd.terminates hΔ θ hc N hN V hV)
  intro m hm v V hv w W hw hW
  rw [hd.result_eq hΔ hc hv.left hν hw,hd.result_eq hΔ hc hv.right hN hW]
  exact hn m hΔ θ hc v V hv

/-- Canonical value construction preserves the relation at the same index. -/
theorem Adapts.natural (hd : Adapts Δ a b code) : AdapterNatural Δ a b code := by
  apply Adapts.rec
    (motive_1 := fun Δ a b code _ => AdapterNatural Δ a b code)
    (motive_2 := fun Δ r fs es _ => ∀ n, Context.Valid Δ → ∀ θ, Closing θ Δ →
      WellFormed Δ r → ∀ v V, ValRel n (.record (r.subst θ)) v V →
      FieldValRel n (fs.map fun (l,a) => (l,a.subst θ))
        (adaptedFields θ v es) (adaptedFields θ V es))
    (t := hd)
  all_goals intros
  all_goals intros
  all_goals try unfold AdapterNatural
  all_goals intros
  case equal =>
    rename_i wa wb he n hΔ θ hc v V hv
    simp only [identityAdapter_subst,adapted_identity hv.left.1,adapted_identity hv.right.1]
    exact ((equal_type n (wa.subst hc.respects) (wb.subst hc.respects)
      (he.subst wa θ)).1 v V).mp hv
  case arrow =>
    rename_i a b c d Δ down up hne hd hu ihd ihu n hΔ θ hc v V hv
    have hmatch := Adapts.arrow hne hd hu
    have hleft := hmatch.adapted_typed hΔ hc hv.left
    have hright := hmatch.adapted_typed hΔ hc hv.right
    rw [ValRel]
    refine ⟨hleft,hright,?_⟩
    simp only [arrowAdapter_subst,adapted_arrow hv.left.1,adapted_arrow hv.right.1,Ty.subst,ShapeRel]
    intro j hj x X hx
    have he := (ValRel.unit.pair (hv.mono (Nat.le_of_lt hj))).pair hx
    have hν := he.left.1
    have hN := he.right.1
    have hquery := ExprRel.query he
    have harg := hquery.snd hν hN
    have hfun := (hquery.fst hν hN).snd hν hN
    have hdown := hd.natural_lift ihd hΔ hc harg hν hN
    have hcall := hfun.app hdown hν hN
    have hup := hu.natural_lift ihu hΔ hc hcall hν hN
    exact ⟨_,_,.clo,.clo,by simpa [Term.subst,Term.ix] using hup⟩
  case closed =>
    rename_i Δ r s es wr ws hne hs hp hfs ihfs n hΔ θ hc v V hv
    have hval := ihfs n hΔ θ hc wr.record_row v V hv
    have wf := ws.record_row.sortedFields
    have hfrel : ValRel n (.record ((Ty.fieldsRow s.sortedFields).subst θ))
        (.record (adaptedFields θ v es)) (.record (adaptedFields θ V es)) := by
      rw [ValRel,ShapeRel]
      exact ⟨hfs.adapted_typed hΔ hc wr.record_row wf hv.left,
        hfs.adapted_typed hΔ hc wr.record_row wf hv.right,
        by simpa only [Ty.fieldsRow_subst] using hval.shape (by simpa only [Ty.fieldsRow_subst] using wf.subst hc.respects)⟩
    rw [adapted_closed_record wr.record_row hΔ hc hfs hv.left,
      adapted_closed_record wr.record_row hΔ hc hfs hv.right]
    exact ((equal_type n (.record (wf.subst hc.respects)) (ws.subst hc.respects)
      (.record ((Ty.closed_result hs).subst wf θ))).1 _ _).mp hfrel
  case sameTail =>
    rename_i Δ r s es wr ws hne hp hfs ihfs n hΔ θ hc v V hv
    obtain ⟨vs,rfl⟩ := hv.left.2.value_shape hv.left.1
    obtain ⟨Vs,rfl⟩ := hv.right.2.value_shape hv.right.1
    have hval := ihfs n hΔ θ hc wr.record_row (.record vs) (.record Vs) hv
    have wf := ws.record_row.sortedFields
    have hfrel : ValRel n (.record ((Ty.fieldsRow s.sortedFields).subst θ))
        (.record (adaptedFields θ (.record vs) es)) (.record (adaptedFields θ (.record Vs) es)) := by
      rw [ValRel,ShapeRel]
      exact ⟨hfs.adapted_typed hΔ hc wr.record_row wf hv.left,
        hfs.adapted_typed hΔ hc wr.record_row wf hv.right,
        by simpa only [Ty.fieldsRow_subst] using hval.shape (by simpa only [Ty.fieldsRow_subst] using wf.subst hc.respects)⟩
    have hdrop := hv.drop r.knownLabels
    rw [← wr.record_row.drop_subst hc.respects (fun l hl => r.mem_lookup hl)] at hdrop
    have hmerge := hfrel.merge hdrop ((sameTail_disjoint ws.record_row hp).subst hc.respects)
    rw [adapted_sameTail_record wr.record_row ws.record_row hp hΔ hc hfs hv.left,
      adapted_sameTail_record wr.record_row ws.record_row hp hΔ hc hfs hv.right]
    have wt : WellFormed Δ (.union (Ty.fieldsRow s.sortedFields) (r.drop r.knownLabels)) :=
      .union wf (wr.record_row.drop _) (sameTail_disjoint ws.record_row hp)
    exact ((equal_type n (.record (wt.subst hc.respects)) (ws.subst hc.respects)
      (.record ((Ty.sameTail_result hp).subst wt θ))).1 _ _).mp hmerge
  case nil =>
    rename_i n hΔ θ hc wr v V hv
    simpa [adaptedFields] using (FieldValRel.nil (n := n))
  case cons =>
    rename_i a Δ b code r fs es l hl hd hf ihd ihf n hΔ θ hc wr v V hv
    have harg := hv.fieldValue (wr.lookup_subst hc.respects hl)
    have hhead := ihd n hΔ θ hc _ _ harg
    have htail := ihf n hΔ θ hc wr v V hv
    simpa [adaptedFields] using FieldValRel.cons (l := l) hhead htail
  case all =>
    rename_i Δ k gs a hs b body wa wb hne hg hb ih n hΔ θ hc v V hv
    have hmatch := Adapts.all wa wb hne hg hb
    have hleft := hmatch.adapted_typed hΔ hc hv.left
    have hright := hmatch.adapted_typed hΔ hc hv.right
    have hfresh : FreshGuards k gs := by cases wa; assumption
    have hguards : WellFormed (Δ.extend k gs) gs := by cases wa; assumption
    have hΓ : Context.Valid (Δ.extend k gs) := .extend hΔ hfresh hguards
    rw [ValRel]
    refine ⟨hleft,hright,?_⟩
    simp only [universalAdapter_subst,adapted_universal hv.left.1,
      adapted_universal hv.right.1,Ty.subst,ShapeRel]
    intro j hj u hk hu hgu
    have hgu' : Entails .empty ((gs.subst θ.lift).open u) := by
      have hh := (hg.entails_subst (Δ := .empty) (θ.instantiate u)).mpr
      simpa only [Ty.subst_instantiate] using hh (by simpa only [Ty.subst_instantiate] using hgu)
    have hσ := hc.instantiate hfresh hk hu hgu'
    have he := ValRel.unit.pair (hv.mono (Nat.le_of_lt hj))
    have hν := he.left.1
    have hN := he.right.1
    have hfun := (ExprRel.query he).snd hν hN
    have hinst := hfun.tapp hk hu hgu' hν hN
    have hinst' : ExprRel j (a.subst (θ.instantiate u))
        (.pair .unit v,.tapp (.snd .query) u) (.pair .unit V,.tapp (.snd .query) u) := by
      simpa only [Ty.subst_instantiate,Ty.subst] using hinst
    have hrel := hb.natural_lift ih hΓ hσ hinst' hν hN
    exact ⟨_,_,.tclo,.tclo,by
      simpa only [Ty.subst_instantiate,Term.subst_instantiate,Term.subst,
        Term.ix,Arg.variable_open hk] using hrel⟩

end LeanSce.Target

/-! ## Adapter Coherence Alignment -/

section

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace LeanSce.Target
open LogicalRelation

theorem Ty.tails_entries (r : Row) :
    r.tails = r.entries.filterMap (fun e => match e with | .tail i => some i | _ => none) := by
  cases r with
  | rvar | empty | field => simp [Ty.tails,Ty.entries]
  | union r s => simp [Ty.tails,Ty.entries,Ty.tails_entries r,Ty.tails_entries s]

theorem TyEq.fieldsRow_eq (he : TyEq r s) (wr : WellFormed Δ r) (ws : WellFormed Γ s) :
    TyEq (Ty.fieldsRow r.knownFields) (Ty.fieldsRow s.knownFields) := by
  apply TyEq.fieldsRow_ext r.knownFields s.knownFields
    (by simpa using wr.knownLabels_nodup) (by simpa using ws.knownLabels_nodup)
  · intro l a ha
    obtain ⟨b,hb,hab⟩ := he.lookup ws (wr.knownField_lookup ha)
    exact ⟨b,Ty.lookup_knownField s hb,hab⟩
  · intro l b hb
    obtain ⟨a,ha,_⟩ := he.symm.lookup wr (ws.knownField_lookup hb)
    exact ⟨a,Ty.lookup_knownField r ha⟩

theorem TyEq.sortedFieldsRow_eq (he : TyEq r s) (wr : WellFormed Δ r) (ws : WellFormed Γ s) :
    TyEq (Ty.fieldsRow r.sortedFields) (Ty.fieldsRow s.sortedFields) :=
  (Ty.fieldsRow_perm r.sortedFields_perm).trans
    ((he.fieldsRow_eq wr ws).trans (Ty.fieldsRow_perm s.sortedFields_perm.symm))

theorem AdaptsFields.adapted_lookup {wanted : Typ} (hd : AdaptsFields Δ r fs es)
    (hl : (Ty.fieldsRow fs).lookup l = some wanted) :
    ∃ a c, r.lookup l = some a ∧ Adapts Δ a wanted c ∧
      (adaptedFields θ v es).lookup l = some (adaptedValue (c.subst θ) (fieldValue v l)) := by
  cases hd with
  | nil => simp [Ty.fieldsRow,Ty.joinRows,Ty.lookup] at hl
  | @cons a Δ b c r fs es k hlookup hc hf =>
    by_cases heq : l = k
    · have hb : b = wanted := by simpa [Ty.fieldsRow,Ty.joinRows,Ty.lookup,heq] using hl
      subst heq
      subst wanted
      exact ⟨a,c,hlookup,hc,by simp [adaptedFields,Term.lookup]⟩
    · have hl' : (Ty.fieldsRow fs).lookup l = some wanted := by
        simpa [Ty.fieldsRow,Ty.joinRows,Ty.lookup,heq] using hl
      obtain ⟨a,c,ha,hc,hval⟩ := hf.adapted_lookup hl'
      exact ⟨a,c,ha,hc,by simpa [adaptedFields,Term.lookup,heq] using hval⟩
termination_by fs.length

/-- Equivalent checked endpoints may use different canonical presentations,
    while the two sides share the same closing assignment. -/
def AdapterAligned (Δ : Context) (a b : Typ) (c : Expr) : Prop :=
  ∀ Γ a' b' d, Adapts Γ a' b' d → TyEq a a' → TyEq b b' →
    ∀ n, Context.Valid Δ → Context.Valid Γ → ∀ θ, Closing θ Δ → Closing θ Γ →
    ∀ v V, ValRel n (a.subst θ) v V →
      ValRel n (b.subst θ) (adaptedValue (c.subst θ) v) (adaptedValue (d.subst θ) V)

private theorem aligned_right_input (hd : Adapts Γ a' b' d) (wa : WellFormed Δ a)
    (he : TyEq a a') (_hc : Closing θ Δ) (hC : Closing θ Γ)
    (hv : ValRel n (a.subst θ) v V) : ValueType .empty V (a'.subst θ) :=
  ⟨hv.right.1,.conv hv.right.2 (he.subst wa θ) (hd.typing.1.subst hC.respects)⟩

private theorem aligned_right_output (hd : Adapts Γ a' b' d)
    (wb : WellFormed Δ b) (he : TyEq b b') (hΓ : Context.Valid Γ)
    (hc : Closing θ Δ) (hC : Closing θ Γ)
    (hv : ValueType .empty V (a'.subst θ)) :
    ValueType .empty (adaptedValue (d.subst θ) V) (b.subst θ) := by
  have ht := hd.adapted_typed hΓ hC hv
  exact ⟨ht.1,.conv ht.2 (he.subst wb θ).symm (wb.subst hc.respects)⟩

theorem Adapts.identity_of_equal (hd : Adapts Δ a b c) (he : TyEq a b) :
    c = identityAdapter a := by
  cases hd with
  | equal => rfl
  | arrow hn _ _ | sameTail _ _ hn _ _ | closed _ _ hn _ _ _ | all _ _ hn _ _ =>
    exact False.elim (hn he)

private theorem aligned_fields
    (wr : WellFormed Δ r) (ws : WellFormed Δ s)
    (wR : WellFormed Γ R) (wS : WellFormed Γ S)
    (heR : TyEq r R) (heS : TyEq s S)
    (hf : AdaptsFields Δ r s.sortedFields es) (hF : AdaptsFields Γ R S.sortedFields Es)
    (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ) (hc : Closing θ Δ) (hC : Closing θ Γ)
    (hv : ValRel n (.record (r.subst θ)) v V)
    (hchild : ∀ l a b c a' b' d, r.lookup l = some a → s.lookup l = some b →
      Adapts Δ a b c → Adapts Γ a' b' d → TyEq a a' → TyEq b b' →
      ValRel n (a.subst θ) (fieldValue v l) (fieldValue V l) →
      ValRel n (b.subst θ) (adaptedValue (c.subst θ) (fieldValue v l))
        (adaptedValue (d.subst θ) (fieldValue V l))) :
    ValRel n (.record ((Ty.fieldsRow s.sortedFields).subst θ))
      (.record (adaptedFields θ v es)) (.record (adaptedFields θ V Es)) := by
  have hinput : ValueType .empty V (.record (R.subst θ)) :=
    ⟨hv.right.1,.conv hv.right.2 (.record (heR.subst wr θ)) (.record (wR.subst hC.respects))⟩
  have hleft := hf.adapted_typed hΔ hc wr ws.sortedFields hv.left
  have hright := hF.adapted_typed hΓ hC wR wS.sortedFields hinput
  have hfieldsEq := heS.sortedFieldsRow_eq ws wS
  have hright' : ValueType .empty (.record (adaptedFields θ V Es))
      (.record ((Ty.fieldsRow s.sortedFields).subst θ)) :=
    ⟨hright.1,.conv hright.2 (.record (hfieldsEq.subst ws.sortedFields θ).symm)
      (.record (ws.sortedFields.subst hc.respects))⟩
  rw [ValRel,ShapeRel]
  refine ⟨hleft,hright',?_⟩
  rw [row_fields (ws.sortedFields.subst hc.respects)]
  intro l b hb
  simp only [Ty.fieldsRow_subst,Ty.knownFields_fieldsRow] at hb
  obtain ⟨⟨l₀,b₀⟩,hmem,heq⟩ := List.mem_map.mp hb
  cases heq
  have hlb : s.lookup l₀ = some b₀ := ws.knownField_lookup (s.sortedFields_perm.mem_iff.mp hmem)
  obtain ⟨b',hLb,heb⟩ := heS.lookup wS hlb
  have hLbmem := S.sortedFields_perm.mem_iff.mpr (Ty.lookup_knownField S hLb)
  have hstatic : (Ty.fieldsRow s.sortedFields).lookup l₀ = some b₀ :=
    ws.sortedFields.knownField_lookup (by simpa using hmem)
  have hStatic : (Ty.fieldsRow S.sortedFields).lookup l₀ = some b' :=
    wS.sortedFields.knownField_lookup (by simpa using hLbmem)
  obtain ⟨a,c,ha,had,hav⟩ := hf.adapted_lookup (θ := θ) (v := v) hstatic
  obtain ⟨a',d,hA,hAd,hAV⟩ := hF.adapted_lookup (θ := θ) (v := V) hStatic
  obtain ⟨A,hAA,hea⟩ := heR.lookup wR ha
  have heAA : A = a' := Option.some.inj (hAA.symm.trans hA)
  subst A
  have harg := hv.fieldValue (wr.lookup_subst hc.respects ha)
  have hvalue := hchild l₀ a b₀ c a' b' d ha hlb had hAd hea heb harg
  exact ⟨_,_,_,_,rfl,rfl,hav,hAV,hvalue⟩

private theorem aligned_expression (hd : Adapts Δ a b c) (hD : Adapts Γ A B d)
    (heA : TyEq a A) (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ)
    (hc : Closing θ Δ) (hC : Closing θ Γ)
    (hm : ∀ m v V, ValRel m (a.subst θ) v V →
      ValRel m (b.subst θ) (adaptedValue (c.subst θ) v) (adaptedValue (d.subst θ) V))
    (he : ExprRel n (a.subst θ) (ν,e) (N,E)) (hν : Value ν) (hN : Value N) :
    ExprRel n (b.subst θ) (ν,.app (c.subst θ) e) (N,.app (d.subst θ) E) := by
  apply he.total_adapters
    (fun v hv => hd.terminates hΔ θ hc ν hν v hv)
    (fun V hV => hD.terminates hΓ θ hC N hN V
      ⟨hV.1,.conv hV.2 (heA.subst hd.typing.1 θ) (hD.typing.1.subst hC.respects)⟩)
  intro m hmn v V hv w W hw hW
  rw [hd.result_eq hΔ hc hv.left hν hw,
    hD.result_eq hΓ hC (aligned_right_input hD hd.typing.1 heA hc hC hv) hN hW]
  exact hm m v V hv

/-- Canonical adapters at equivalent endpoints preserve the relation. -/
private theorem Adapts.aligned_core (hd : Adapts Δ a b c) : AdapterAligned Δ a b c := by
  intro Γ A B d hD heA heB n hΔ hΓ θ hc hC v V hv
  cases hd with
  | equal wa wb hab =>
    have hAB : TyEq A B := heA.symm.trans (hab.trans heB)
    rw [hD.identity_of_equal hAB]
    simp only [identityAdapter_subst,adapted_identity hv.left.1,adapted_identity hv.right.1]
    exact ((equal_type n (wa.subst hc.respects) (wb.subst hc.respects) (hab.subst wa θ)).1 _ _).mp hv
  | arrow hn down up =>
    cases heA.shape with
    | arr hea heb =>
      cases heB.shape with
      | arr hec hed =>
        cases hD with
        | equal _ _ hab => exact False.elim (hn (heA.trans (hab.trans heB.symm)))
        | arrow hN Down Up =>
          have hmatch := Adapts.arrow hn down up
          have hMatch := Adapts.arrow hN Down Up
          have hrinput := aligned_right_input hMatch hmatch.typing.1 heA hc hC hv
          have hleft := hmatch.adapted_typed hΔ hc hv.left
          have hright := aligned_right_output hMatch hmatch.typing.2.1 heB hΓ hc hC hrinput
          rw [ValRel]
          refine ⟨hleft,hright,?_⟩
          simp only [arrowAdapter_subst,adapted_arrow hv.left.1,adapted_arrow hv.right.1,Ty.subst,ShapeRel]
          intro j hj x X hx
          have henv := (ValRel.unit.pair (hv.mono (Nat.le_of_lt hj))).pair hx
          have hν := henv.left.1
          have hN := henv.right.1
          have hquery := ExprRel.query henv
          have harg := hquery.snd hν hN
          have hfun := (hquery.fst hν hN).snd hν hN
          have hdown := aligned_expression down Down hec hΔ hΓ hc hC
            (fun m x X hx => down.aligned_core _ _ _ _ Down hec hea m hΔ hΓ θ hc hC x X hx) harg hν hN
          have hcall := hfun.app hdown hν hN
          have hup := aligned_expression up Up heb hΔ hΓ hc hC
            (fun m x X hx => up.aligned_core _ _ _ _ Up heb hed m hΔ hΓ θ hc hC x X hx) hcall hν hN
          exact ⟨_,_,.clo,.clo,by simpa [Term.subst,Term.ix] using hup⟩
  | sameTail wr ws hn hp hfs =>
    rename_i r s es
    cases heA.shape with
    | record heR =>
      rename_i R
      cases heB.shape with
      | record heS =>
        rename_i S
        cases hD with
        | equal _ _ hab => exact False.elim (hn (heA.trans (hab.trans heB.symm)))
        | closed _ _ _ _ hnp _ =>
          exact False.elim (hnp (heR.tails_perm.symm.trans (hp.trans heS.tails_perm)))
        | sameTail wR wS hN hP hFs =>
          have hmatch := Adapts.sameTail wr ws hn hp hfs
          have hMatch := Adapts.sameTail wR wS hN hP hFs
          have hrinput := aligned_right_input hMatch wr heA hc hC hv
          obtain ⟨vs,rfl⟩ := hv.left.2.value_shape hv.left.1
          obtain ⟨Vs,rfl⟩ := hv.right.2.value_shape hv.right.1
          have hfrel := aligned_fields wr.record_row ws.record_row wR.record_row wS.record_row
            heR heS hfs hFs hΔ hΓ hc hC hv (by
              intro l a b c a' b' d ha hb hd hD hea heb harg
              have hsa := Ty.knownField_size _ (Ty.lookup_knownField _ ha)
              have hsb := Ty.knownField_size _ (Ty.lookup_knownField _ hb)
              exact hd.aligned_core _ _ _ _ hD hea heb n hΔ hΓ θ hc hC _ _ harg)
          have hdrop := hv.drop r.knownLabels
          rw [← wr.record_row.drop_subst hc.respects (fun l hl => Ty.mem_lookup _ hl)] at hdrop
          have hmerge := hfrel.merge hdrop ((sameTail_disjoint ws.record_row hp).subst hc.respects)
          have hfilter : Vs.filter (fun l => !R.knownLabels.contains l) =
              Vs.filter (fun l => !r.knownLabels.contains l) := by
            congr 1
            funext l
            have he : R.knownLabels.contains l = r.knownLabels.contains l := by
              apply Bool.coe_iff_coe.mp
              simpa using (heR.labels_perm.mem_iff (a := l)).symm
            rw [he]
          rw [adapted_sameTail_record wr.record_row ws.record_row hp hΔ hc hfs hv.left,
            adapted_sameTail_record wR.record_row wS.record_row hP hΓ hC hFs hrinput,hfilter]
          have wt := WellFormed.union ws.record_row.sortedFields (wr.record_row.drop _)
            (sameTail_disjoint ws.record_row hp)
          exact ((equal_type n (.record (wt.subst hc.respects)) (ws.subst hc.respects)
            (.record ((Ty.sameTail_result hp).subst wt θ))).1 _ _).mp hmerge
  | closed wr ws hn hs hnp hfs =>
    cases heA.shape with
    | record heR =>
      cases heB.shape with
      | record heS =>
        cases hD with
        | equal _ _ hab => exact False.elim (hn (heA.trans (hab.trans heB.symm)))
        | sameTail _ _ _ hP _ =>
          exact False.elim (hnp (heR.tails_perm.trans (hP.trans heS.tails_perm.symm)))
        | closed wR wS hN hS hNP hFs =>
          have hMatch := Adapts.closed wR wS hN hS hNP hFs
          have hrinput := aligned_right_input hMatch wr heA hc hC hv
          have hfrel := aligned_fields wr.record_row ws.record_row wR.record_row wS.record_row
            heR heS hfs hFs hΔ hΓ hc hC hv (by
              intro l a b c a' b' d ha hb hd hD hea heb harg
              have hsa := Ty.knownField_size _ (Ty.lookup_knownField _ ha)
              have hsb := Ty.knownField_size _ (Ty.lookup_knownField _ hb)
              exact hd.aligned_core _ _ _ _ hD hea heb n hΔ hΓ θ hc hC _ _ harg)
          rw [adapted_closed_record wr.record_row hΔ hc hfs hv.left,
            adapted_closed_record wR.record_row hΓ hC hFs hrinput]
          exact ((equal_type n (.record (ws.record_row.sortedFields.subst hc.respects)) (ws.subst hc.respects)
            (.record ((Ty.closed_result hs).subst ws.record_row.sortedFields θ))).1 _ _).mp hfrel
  | all wa wb hn hg hbody =>
    rename_i k gs a hs b body
    cases heA.shape with
    | all hga hea =>
      rename_i gs' a'
      cases heB.shape with
      | all hgb heb =>
        rename_i hs' b'
        cases hD with
        | equal _ _ hab => exact False.elim (hn (heA.trans (hab.trans heB.symm)))
        | all wA wB hN hG hBody =>
          have hmatch := Adapts.all wa wb hn hg hbody
          have hMatch := Adapts.all wA wB hN hG hBody
          have hrinput := aligned_right_input hMatch wa heA hc hC hv
          have hleft := hmatch.adapted_typed hΔ hc hv.left
          have hright := aligned_right_output hMatch wb heB hΓ hc hC hrinput
          have hfresh := show FreshGuards k gs from (by cases wa; assumption)
          have hfresh' := show FreshGuards k gs' from (by cases wA; assumption)
          have hvalid := show Context.Valid (Δ.extend k gs) from (by cases wa; exact .extend hΔ (by assumption) (by assumption))
          have hValid := show Context.Valid (Γ.extend k gs') from (by cases wA; exact .extend hΓ (by assumption) (by assumption))
          rw [ValRel]
          refine ⟨hleft,hright,?_⟩
          simp only [universalAdapter_subst,adapted_universal hv.left.1,adapted_universal hv.right.1,Ty.subst,ShapeRel]
          intro j hj u hk hu hgu
          have hgu₁ := (hg.entails_subst (Δ := .empty) (θ.instantiate u)).mpr
            (by simpa only [Ty.subst_instantiate] using hgu)
          have hgu₁' : Entails .empty ((gs.subst θ.lift).open u) := by
            simpa only [Ty.subst_instantiate] using hgu₁
          have hgu₂ : Entails .empty ((gs'.subst θ.lift).open u) := by
            rcases hga with rfl | hga
            · exact hgu₁'
            · have hh := (hga.entails_subst (Δ := .empty) (θ.instantiate u)).mp hgu₁
              simpa only [Ty.subst_instantiate] using hh
          have hσ := hc.instantiate hfresh hk hu hgu₁'
          have hCloseRight := hC.instantiate hfresh' hk hu hgu₂
          have henv := ValRel.unit.pair (hv.mono (Nat.le_of_lt hj))
          have hν := henv.left.1
          have hN := henv.right.1
          have hfun := (ExprRel.query henv).snd hν hN
          have hinst := hfun.tapp hk hu hgu₁' hν hN
          have hrel := aligned_expression hbody hBody hea hvalid hValid hσ hCloseRight
            (fun m x X hx => hbody.aligned_core _ _ _ _ hBody hea heb m hvalid hValid _ hσ hCloseRight x X hx)
            (by simpa only [Ty.subst_instantiate] using hinst) hν hN
          exact ⟨_,_,.tclo,.tclo,by
            simpa only [Ty.subst_instantiate,Term.subst_instantiate,Term.subst,
              Term.ix,Arg.variable_open hk] using hrel⟩
termination_by sizeOf a + sizeOf b

decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

theorem Adapts.aligned (hd : Adapts Δ a b c) (hD : Adapts Γ A B d)
    (heA : TyEq a A) (heB : TyEq b B)
    (n : Nat) (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ)
    (θ : Subst) (hc : Closing θ Δ) (hC : Closing θ Γ)
    (v V : Expr) (hv : ValRel n (a.subst θ) v V) :
    ValRel n (b.subst θ) (adaptedValue (c.subst θ) v) (adaptedValue (d.subst θ) V) :=
  hd.aligned_core Γ A B d hD heA heB n hΔ hΓ θ hc hC v V hv

/-- The corresponding computational relation evaluates each adapted input once. -/
theorem Adapts.aligned_lift (hd : Adapts Δ a b c) (hD : Adapts Γ A B d)
    (heA : TyEq a A) (heB : TyEq b B)
    (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ)
    (hc : Closing θ Δ) (hC : Closing θ Γ)
    (he : ExprRel n (a.subst θ) (ν,e) (N,E)) (hν : Value ν) (hN : Value N) :
    ExprRel n (b.subst θ) (ν,.app (c.subst θ) e) (N,.app (d.subst θ) E) :=
  aligned_expression hd hD heA hΔ hΓ hc hC
    (fun m v V hv => hd.aligned hD heA heB m hΔ hΓ θ hc hC v V hv) he hν hN

end LeanSce.Target

end

/-! ## Adapter Coherence Record -/

namespace LeanSce.Target
open LogicalRelation

theorem fieldValue_typed (wr : WellFormed Δ r) (hc : Closing θ Δ)
    (hl : r.lookup l = some a) (hv : ValueType .empty v (.record (r.subst θ))) :
    ValueType .empty (fieldValue v l) (a.subst θ) := by
  obtain ⟨vs,rfl⟩ := hv.2.value_shape hv.1
  have hsource := hv.2.value_record_inv hv.1 ((WellFormed.record wr).subst hc.respects).record_row
  obtain ⟨x,hx,hxt⟩ := hsource.lookup .empty (wr.lookup_subst hc.respects hl)
  simpa [fieldValue,hx] using
    (show ValueType .empty x (a.subst θ) from ⟨Term.lookup_value vs hv.1 hx,hxt⟩)

theorem AdaptsFields.adapted_lookup_fixed (hf : AdaptsFields Δ r fs es)
    (hl : (Ty.fieldsRow fs).lookup l = some b) (ha : r.lookup l = some a)
    (hd : Adapts Δ a b code) :
    (adaptedFields θ v es).lookup l = some (adaptedValue (code.subst θ) (fieldValue v l)) := by
  obtain ⟨a',c',ha',hd',hval⟩ := hf.adapted_lookup (θ := θ) (v := v) hl
  have hea := Option.some.inj (ha'.symm.trans ha)
  subst a'
  have hec := hd'.deterministic code hd
  simpa only [hec] using hval

theorem Ty.sortedFields_lookup (ws : WellFormed Δ s) (hl : s.lookup l = some a) :
    (Ty.fieldsRow s.sortedFields).lookup l = some a := by
  apply ws.sortedFields.knownField_lookup
  rw [Ty.knownFields_fieldsRow]
  exact s.sortedFields_perm.mem_iff.mpr (Ty.lookup_knownField s hl)

/-- Every statically named target field is produced by its named field adapter. -/
theorem Adapts.record_known_field (hd : Adapts Δ (.record r) (.record s) code) (hΔ : Context.Valid Δ)
    (hl : s.lookup l = some b) :
    ∃ a child, r.lookup l = some a ∧ Adapts Δ a b child ∧
      ∀ θ, Closing θ Δ → ∀ v, ValueType .empty v (.record (r.subst θ)) →
        fieldValue (adaptedValue (code.subst θ) v) l =
          adaptedValue (child.subst θ) (fieldValue v l) := by
  cases hd with
  | equal wr ws he =>
    obtain ⟨a,ha,hab⟩ := he.record_inv.symm.lookup wr.record_row hl
    refine ⟨a,identityAdapter a,ha,.equal (wr.record_row.lookup ha) (ws.record_row.lookup hl) hab.symm,?_⟩
    intro θ hc v hv
    have hfv := fieldValue_typed wr.record_row hc ha hv
    simp [identityAdapter_subst,adapted_identity hv.1,adapted_identity hfv.1]
  | sameTail wr ws hn hp hf =>
    have hls := Ty.sortedFields_lookup ws.record_row hl
    obtain ⟨a,child,ha,hchild,_⟩ := hf.adapted_lookup (θ := Subst.id) (v := .unit) hls
    refine ⟨a,child,ha,hchild,?_⟩
    intro θ hc v hv
    obtain ⟨vs,rfl⟩ := hv.2.value_shape hv.1
    rw [adapted_sameTail_record wr.record_row ws.record_row hp hΔ hc hf hv]
    simp [fieldValue,Term.lookup_append,hf.adapted_lookup_fixed hls ha hchild]
  | closed wr ws hn hs hp hf =>
    have hls := Ty.sortedFields_lookup ws.record_row hl
    obtain ⟨a,child,ha,hchild,_⟩ := hf.adapted_lookup (θ := Subst.id) (v := .unit) hls
    refine ⟨a,child,ha,hchild,?_⟩
    intro θ hc v hv
    rw [adapted_closed_record wr.record_row hΔ hc hf hv]
    simp [fieldValue,hf.adapted_lookup_fixed hls ha hchild]

theorem AdaptsFields.adapted_labels (hf : AdaptsFields Δ r fs es) :
    ∀ θ v, (adaptedFields θ v es).labels = fs.map Prod.fst := by
  apply AdaptsFields.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ fs es _ => ∀ θ v, (adaptedFields θ v es).labels = fs.map Prod.fst)
    (t := hf)
  all_goals intros
  all_goals try trivial
  all_goals intros
  case nil => simp [adaptedFields,Term.labels]
  case cons =>
    rename_i _ _ hf _ ih θ v
    simp [adaptedFields,Term.labels,ih θ v]

theorem Adapts.known_subset (hd : Adapts Δ (.record r) (.record s) code) :
    ∀ l ∈ s.knownLabels, l ∈ r.knownLabels := by
  cases hd with
  | equal _ _ he => exact fun l hl => he.record_inv.labels_perm.mem_iff.mpr hl
  | sameTail _ _ _ _ hf | closed _ _ _ _ _ hf =>
    intro l hl
    obtain ⟨b,hb⟩ := s.mem_lookup hl
    have hm := s.sortedFields_perm.mem_iff.mpr (Ty.lookup_knownField s hb)
    obtain ⟨a,c,ha,_⟩ := hf.member hm
    exact Ty.lookup_mem r ha

@[simp] theorem Ty.fieldsRow_labels_subst (fs : List (String × Typ)) (θ : Subst) :
    ((Ty.fieldsRow fs).subst θ).knownLabels = fs.map Prod.fst := by
  simp only [Ty.fieldsRow_subst,← Ty.knownFields_keys,Ty.knownFields_fieldsRow,List.map_map]
  rfl

theorem Ty.sortedFields_labels_subst (r : Row) (θ : Subst) :
    (((Ty.fieldsRow r.sortedFields).subst θ).knownLabels).Perm r.knownLabels := by
  rw [Ty.fieldsRow_labels_subst]
  simpa only [Ty.knownFields_keys] using (r.sortedFields_perm.map Prod.fst)

/-- A dynamic target field outside its named prefix is an opaque source field. -/
theorem Adapts.unknown_source (hd : Adapts Δ (.record r) (.record s) code)
    (hc : Closing θ Δ) (hl : l ∈ (s.subst θ).knownLabels) (hn : l ∉ s.knownLabels) :
    l ∉ r.knownLabels := by
  cases hd with
  | equal _ _ he => exact fun hr => hn (he.record_inv.labels_perm.mem_iff.mp hr)
  | closed wr ws _ hs _ _ =>
    have he := (Ty.closed_result hs).subst ws.record_row.sortedFields θ
    have hm := he.labels_perm.mem_iff.mpr hl
    exact False.elim (hn ((s.sortedFields_labels_subst θ).mem_iff.mp hm))
  | sameTail wr ws _ hp _ =>
    intro hr
    have he := s.sorted_decompose.subst ws.record_row θ
    have hm := he.labels_perm.mem_iff.mp hl
    have htail : l ∈ ((Ty.tailsRow s.tails).subst θ).knownLabels := by
      simp only [Ty.subst,Ty.knownLabels,List.mem_append] at hm
      rcases hm with hm | hm
      · exact False.elim (hn ((s.sortedFields_labels_subst θ).mem_iff.mp hm))
      · exact hm
    have htailEq : TyEq (Ty.tailsRow r.tails) (Ty.tailsRow s.tails) :=
      TyEq.joinRows_perm (hp.map Ty.rvar)
    have htailR := (htailEq.subst wr.record_row.decomposed.2.1 θ).labels_perm.mem_iff.mpr htail
    have hfieldsR : l ∈ ((Ty.fieldsRow r.knownFields).subst θ).knownLabels := by
      simpa only [Ty.fieldsRow_labels_subst,Ty.knownFields_keys] using hr
    exact (wr.record_row.decomposed.2.2.subst hc.respects).knownLabels l hfieldsR htailR

/-- Opaque fields are copied without changing their value. -/
theorem Adapts.record_unknown_field (hd : Adapts Δ (.record r) (.record s) code)
    (hΔ : Context.Valid Δ) (hc : Closing θ Δ)
    (hv : ValueType .empty v (.record (r.subst θ)))
    (hn : l ∉ r.knownLabels) (hl : l ∈ (s.subst θ).knownLabels) :
    fieldValue (adaptedValue (code.subst θ) v) l = fieldValue v l := by
  cases hd with
  | equal _ _ _ => simp [identityAdapter_subst,adapted_identity hv.1]
  | closed wr ws _ hs _ hf =>
    have he := (Ty.closed_result hs).subst ws.record_row.sortedFields θ
    have hm := (s.sortedFields_labels_subst θ).mem_iff.mp (he.labels_perm.mem_iff.mpr hl)
    have hm' := (Adapts.closed wr ws (by assumption) hs (by assumption) hf).known_subset l hm
    exact False.elim (hn hm')
  | sameTail wr ws hne hp hf =>
    rename_i fields
    obtain ⟨vs,rfl⟩ := hv.2.value_shape hv.1
    have hnone : (adaptedFields θ (.record vs) fields).lookup l = none := by
      apply Term.lookup_none_of_not_mem
      rw [hf.adapted_labels]
      intro hm
      have hs : l ∈ s.knownLabels := by
        simpa only [Ty.knownFields_keys] using (s.sortedFields_perm.map Prod.fst).mem_iff.mp hm
      exact hn ((Adapts.sameTail wr ws hne hp hf).known_subset l hs)
    rw [adapted_sameTail_record wr.record_row ws.record_row hp hΔ hc hf hv]
    simp [fieldValue,Term.lookup_append,hnone,Term.lookup_filter,hn]

theorem Adapts.instantiated_known_subset (hd : Adapts Δ (.record r) (.record s) code)
    (hc : Closing θ Δ) : ∀ l ∈ (s.subst θ).knownLabels, l ∈ (r.subst θ).knownLabels := by
  have known : ∀ l ∈ r.knownLabels, l ∈ (r.subst θ).knownLabels := by
    intro l hl
    obtain ⟨a,ha⟩ := r.mem_lookup hl
    exact Ty.lookup_mem (r.subst θ) (hd.typing.1.record_row.lookup_subst hc.respects ha)
  cases hd with
  | equal wr ws he =>
    exact fun l hl => (he.subst wr θ).record_inv.labels_perm.mem_iff.mpr hl
  | closed wr ws hn hs hp hf =>
    intro l hl
    have he := (Ty.closed_result hs).subst ws.record_row.sortedFields θ
    have hm := (s.sortedFields_labels_subst θ).mem_iff.mp (he.labels_perm.mem_iff.mpr hl)
    exact known l ((Adapts.closed wr ws hn hs hp hf).known_subset l hm)
  | sameTail wr ws hn hp hf =>
    intro l hl
    have heS := s.sorted_decompose.subst ws.record_row θ
    have hm := heS.labels_perm.mem_iff.mp hl
    simp only [Ty.subst,Ty.knownLabels,List.mem_append] at hm
    rcases hm with hm | hm
    · have hs := (s.sortedFields_labels_subst θ).mem_iff.mp hm
      exact known l ((Adapts.sameTail wr ws hn hp hf).known_subset l hs)
    · have htailEq : TyEq (Ty.tailsRow r.tails) (Ty.tailsRow s.tails) :=
        TyEq.joinRows_perm (hp.map Ty.rvar)
      have htailR := (htailEq.subst wr.record_row.decomposed.2.1 θ).labels_perm.mem_iff.mpr hm
      have heR := r.sorted_decompose.subst wr.record_row θ
      exact heR.labels_perm.mem_iff.mpr (by
        simp only [Ty.subst,Ty.knownLabels,List.mem_append]
        exact .inr htailR)

/-- Record path coherence reduces only statically named payloads recursively;
    every opaque payload is copied literally along both paths. -/
theorem adapter_record_composition
    (h₁ : Adapts Δ (.record r) (.record s) c₁)
    (h₂ : Adapts Γ (.record s) (.record t) c₂)
    (h₃ : Adapts Ξ (.record r) (.record t) c₃)
    (hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ) (hΞ : Context.Valid Ξ)
    (hc : Closing θ Δ) (hC : Closing θ Γ) (hX : Closing θ Ξ)
    (hv : ValRel n (.record (r.subst θ)) v V)
    (hchild : ∀ l a b c f₁ f₂ f₃,
      r.lookup l = some a → s.lookup l = some b → t.lookup l = some c →
      Adapts Δ a b f₁ → Adapts Γ b c f₂ → Adapts Ξ a c f₃ →
      ValRel n (a.subst θ) (fieldValue v l) (fieldValue V l) →
      ValRel n (c.subst θ)
        (adaptedValue (f₂.subst θ) (adaptedValue (f₁.subst θ) (fieldValue v l)))
        (adaptedValue (f₃.subst θ) (fieldValue V l))) :
    ValRel n (.record (t.subst θ))
      (adaptedValue (c₂.subst θ) (adaptedValue (c₁.subst θ) v))
      (adaptedValue (c₃.subst θ) V) := by
  have hv₁ := h₁.adapted_typed hΔ hc hv.left
  have hv₂ := h₂.adapted_typed hΓ hC hv₁
  have hV₃ := h₃.adapted_typed hΞ hX hv.right
  have href := h₃.natural n hΞ θ hX v V hv
  obtain ⟨fs,hfs⟩ := hv₂.2.value_shape hv₂.1
  obtain ⟨gs,hgs⟩ := hV₃.2.value_shape hV₃.1
  have wt := h₃.typing.2.1.record_row
  have wtθ := wt.subst hX.respects
  have hv₂' : ValueType .empty (.record fs) (.record (t.subst θ)) := by
    simpa only [hfs] using hv₂
  have hV₃' : ValueType .empty (.record gs) (.record (t.subst θ)) := by
    simpa only [hgs] using hV₃
  have hfl := hv₂'.2.value_record_inv hv₂'.1 wtθ
  have hgr := hV₃'.2.value_record_inv hV₃'.1 wtθ
  apply ValRel.of_record_lookups hv₂ hV₃
  intro l c hm
  have hl := wtθ.knownField_lookup hm
  obtain ⟨x,hxl,hxt⟩ := hfl.lookup .empty hl
  obtain ⟨X,hXl,hXt⟩ := hgr.lookup .empty hl
  have hget : ValRel n c
      (fieldValue (adaptedValue (c₂.subst θ) (adaptedValue (c₁.subst θ) v)) l)
      (fieldValue (adaptedValue (c₃.subst θ) V) l) := by
    by_cases hstatic : l ∈ t.knownLabels
    · obtain ⟨C,hClook⟩ := t.mem_lookup hstatic
      have htype : C.subst θ = c := Option.some.inj
        ((wt.lookup_subst hX.respects hClook).symm.trans hl)
      obtain ⟨B,f₂,hB,hD₂,hE₂⟩ := h₂.record_known_field hΓ hClook
      obtain ⟨A,f₁,hA,hD₁,hE₁⟩ := h₁.record_known_field hΔ hB
      obtain ⟨A',f₃,hA',hD₃,hE₃⟩ := h₃.record_known_field hΞ hClook
      have heA := Option.some.inj (hA'.symm.trans hA)
      subst A'
      have hinput := hv.fieldValue (h₁.typing.1.record_row.lookup_subst hc.respects hA)
      rw [hE₂ θ hC _ hv₁,hE₁ θ hc v hv.left,hE₃ θ hX V hv.right]
      simpa only [htype] using hchild l A B C f₁ f₂ f₃ hA hB hClook hD₁ hD₂ hD₃ hinput
    · have htarget := Ty.lookup_mem (t.subst θ) hl
      have hnotR := h₃.unknown_source hX htarget hstatic
      have hnotS : l ∉ s.knownLabels := fun h => hnotR (h₁.known_subset l h)
      have htargetS := h₂.instantiated_known_subset hC l htarget
      have he₁ := h₁.record_unknown_field hΔ hc hv.left hnotR htargetS
      have he₂ := h₂.record_unknown_field hΓ hC hv₁ hnotS htarget
      have he₃ := h₃.record_unknown_field hΞ hX hv.left hnotR htarget
      have hrel := href.fieldValue hl
      rw [he₂,he₁,← he₃]
      exact hrel
  exact ⟨fs,gs,x,X,hfs,hgs,hxl,hXl,by simpa [hfs,hgs,fieldValue,hxl,hXl] using hget⟩

end LeanSce.Target

/-! ## Adapter Composition Identity -/

namespace LeanSce.Target
open LogicalRelation

/-- An identity first leg changes only the checked type presentation. -/
theorem adapter_composition_first_equal
    (wa : WellFormed Δ a) (wb : WellFormed Δ b) (he : TyEq a b)
    (h₂ : Adapts Γ b c c₂) (h₃ : Adapts Ξ a c c₃)
    (_hΔ : Context.Valid Δ) (hΓ : Context.Valid Γ) (hΞ : Context.Valid Ξ)
    (hθ : Closing θ Δ) (hΘ : Closing θ Γ) (hϑ : Closing θ Ξ)
    (hv : ValRel n (a.subst θ) v V) :
    ValRel n (c.subst θ)
      (adaptedValue (c₂.subst θ) (adaptedValue ((identityAdapter a).subst θ) v))
      (adaptedValue (c₃.subst θ) V) := by
  rw [identityAdapter_subst,adapted_identity hv.left.1]
  have hvb := ((equal_type n (wa.subst hθ.respects) (wb.subst hθ.respects)
    (he.subst wa θ)).1 v V).mp hv
  exact h₂.aligned h₃ he.symm .refl n hΓ hΞ θ hΘ hϑ v V hvb

/-- An identity second leg changes only the result type presentation. -/
theorem adapter_composition_second_equal
    (h₁ : Adapts Δ a b c₁)
    (wb : WellFormed Γ b) (wc : WellFormed Γ c) (he : TyEq b c)
    (h₃ : Adapts Ξ a c c₃)
    (hΔ : Context.Valid Δ) (_hΓ : Context.Valid Γ) (hΞ : Context.Valid Ξ)
    (hθ : Closing θ Δ) (hΘ : Closing θ Γ) (hϑ : Closing θ Ξ)
    (hv : ValRel n (a.subst θ) v V) :
    ValRel n (c.subst θ)
      (adaptedValue ((identityAdapter b).subst θ) (adaptedValue (c₁.subst θ) v))
      (adaptedValue (c₃.subst θ) V) := by
  rw [identityAdapter_subst,adapted_identity (h₁.adapted_typed hΔ hθ hv.left).1]
  have hr := h₁.aligned h₃ .refl he n hΔ hΞ θ hθ hϑ v V hv
  exact ((equal_type n (wb.subst hΘ.respects) (wc.subst hΘ.respects)
    (he.subst wb θ)).1 _ _).mp hr

end LeanSce.Target

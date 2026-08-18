
import LeanSce.Core.Syntax
import LeanSce.Core.Typing

open Core

inductive Step : Exp → Exp → Exp → Prop where
  | squery {v}
    : Value v
    -> Step v .query v
  | sappl {v e1 e1' e2}
    : Value v
    → Step v e1 e1'
    → Step v (.app e1 e2) (.app e1' e2)
  | sboxl {v e1 e1' e2}
    : Value v
    → Step v e1 e1'
    → Step v (.box e1 e2) (.box e1' e2)
  | smrgl {v e1 e1' e2}
    : Value v
    → Step v e1 e1'
    → Step v (.mrg e1 e2) (.mrg e1' e2)
  | sappr {v v1 e2 e2'}
    : Value v
    → Value v1
    → Step v e2 e2'
    → Step v (.app v1 e2) (.app v1 e2')
  | sboxr
    : Value v
    → Value v1
    → Step v1 e2 e2'
    → Step v (.box v1 e2) (.box v1 e2')
  | smrgr {v v1 e2 e2'}
    : Value v
    → Value v1
    → Step (.mrg v v1) e2 e2'
    → Step v (.mrg v1 e2) (.mrg v1 e2')
  | sclos {v A e}
    : Value v
    → Step v (.lam A e) (.clos v A e)
  | sbeta {v v1 v2 A e}
    : Value v
    → Value v1
    → Value v2
    → Step v (.app (.clos v2 A e) v1) (.box (.mrg v2 v1) e)
  | sboxv {v v1 v2}
    : Value v
    → Value v1
    → Value v2
    → Step v (.box v1 v2) v2
  | sproj {v e1 e2 n}
    : Value v
    → Step v e1 e2
    → Step v (.proj e1 n) (.proj e2 n)
  | sprojv {v v1 n v2}
    : Value v
    → Value v1
    → LookupV v1 n v2
    → Step v (.proj v1 n) v2
  | slrec {v e1 e2 l}
    : Value v
    → Step v e1 e2
    → Step v (.lrec l e1) (.lrec l e2)
  | srproj
    : Value v
    → Step v e1 e2
    → Step v (.rproj e1 l) (.rproj e2 l)
  | srprojv {v v1 l v2}
    : Value v
    → Value v1
    → RLookupV v1 l v2
    → Step v (.rproj v1 l) v2
  | sinl {v e1 e2 B}
    : Value v
    → Step v e1 e2
    → Step v (.inl B e1) (.inl B e2)
  | sinr {v e1 e2 A}
    : Value v
    → Step v e1 e2
    → Step v (.inr A e1) (.inr A e2)
  | scase {v e e' e1 e2}
    : Value v
    → Step v e e'
    → Step v (.case e e1 e2) (.case e' e1 e2)
  | scasel {v v1 B e1 e2}
    : Value v
    → Value v1
    → Step v (.case (.inl B v1) e1 e2) (.box (.mrg v v1) e1)
  | scaser {v v1 A e1 e2}
    : Value v
    → Value v1
    → Step v (.case (.inr A v1) e1 e2) (.box (.mrg v v1) e2)
  | sfclos {v A B e}
    : Value v
    → Step v (.flam A B e) (.fclos v A B e)
  | sfbeta {v v1 v2 A B e}
    : Value v
    → Value v1
    → Value v2
    → Step v (.app (.fclos v2 A B e) v1)
             (.box (.mrg (.mrg v2 (.fclos v2 A B e)) v1) e)
  | sfold {v e1 e2 T}
    : Value v
    → Step v e1 e2
    → Step v (.fold T e1) (.fold T e2)
  | sunfold {v e1 e2}
    : Value v
    → Step v e1 e2
    → Step v (.unfold e1) (.unfold e2)
  | sunfoldv {v v1 T}
    : Value v
    → Value v1
    → Step v (.unfold (.fold T v1)) v1

inductive MStep : Exp → Exp → Exp → Prop where
  | refl :
    ∀ {v e},
      Value v
    → MStep v e e
  | step :
    ∀ {v e e' e''},
      Step v e e'
    → MStep v e' e''
    → MStep v e e''

@[simp]
theorem value_weaken
  {E A : Typ} { v : Exp} :
  HasType E v A →
  ∀ {E' : Typ},
    Value v
    → HasType E' v A := by
  intro htype
  induction htype with
  | tint          => intro _ _; exact .tint
  | tunit         => intro _ _; exact .tunit
  | trcd ht ih    => intro _ hv; cases hv; exact .trcd (ih ‹_›)
  | tlam _        => intro _ hv; cases hv
  | tquery        => intro _ hv; cases hv
  | tapp _ _      => intro _ hv; cases hv
  | tbox _ _      => intro _ hv; cases hv
  | tproj _ _     => intro _ hv; cases hv
  | trproj _ _    => intro _ hv; cases hv
  | tinl ht ih    => intro _ hv; cases hv; exact .tinl (ih ‹_›)
  | tinr ht ih    => intro _ hv; cases hv; exact .tinr (ih ‹_›)
  | tcase _ _ _   => intro _ hv; cases hv
  | tflam _       => intro _ hv; cases hv
  | tfclos hv' ht' hb ih1 ih2 =>
    intro E' hv
    apply HasType.tfclos <;> assumption
  | tfold ht ih   => intro _ hv; cases hv; exact .tfold (ih ‹_›)
  | tunfold _     => intro _ hv; cases hv
  | tmrg h1 h2 ih1 ih2 =>
    intro _ hv
    cases hv with
    | vmrg hv1 hv2 => exact .tmrg (ih1 hv1) (ih2 hv2)
  | tclos hv' ht' hb ih1 ih2 =>
    rename_i Γ₁ Γ₂ A' B' v₀ e₀
    intro E' hv
    apply HasType.tclos <;> assumption

@[simp]
theorem lookupv_value:
  ∀ {v v' : Exp} {n : Nat},
    LookupV v n v'
    → Value v
    → Value v' := by
  intro v v' n hlook hval
  induction hlook with
  | lvzero =>
    cases hval <;> try assumption
  | lvsucc =>
    cases hval with
    | vmrg hv1 _ =>
      rename_i v1 v2 v3 n ih11 ih12 hv2
      apply ih12
      assumption

@[simp]
theorem lookup_pres_ctx {E n A}:
  Lookup E n A
  → ∀ v v',
    LookupV v n v'
    → Value v
    → HasType .top v E
    → HasType E v' A := by
  intro hl
  induction hl with
  | zero =>
    intro v v' hlv hv ht
    cases hlv
    cases ht with
    | tmrg h1 h2 =>
      cases hv with
      | vmrg hv1 hv2 =>
        exact value_weaken h2 hv2
  | succ hl' ih =>
    intro v v' hlv hv ht
    cases hlv with
    | lvsucc hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          rename_i v1 v2
          have h := ih v1 _ hlv' hv1 (value_weaken h1 hv1)
          exact value_weaken h (lookupv_value hlv' hv1)

@[simp]
theorem lookup_pres {E n A} :
  Lookup E n A
  → ∀ v v',
    LookupV v n v'
    → Value v
    → HasType .top v E
    → HasType .top v' A := by
  intro hl v v' hlv hv ht
  have h := lookup_pres_ctx hl v v' hlv hv ht
  exact value_weaken h (lookupv_value hlv hv)

@[simp]
theorem rlookupv_value {v l v'} :
  RLookupV v l v'
  → Value v
  → Value v' := by
  intro hl hv
  induction hl with
  | rvlzero => cases hv; assumption
  | vlandl _ ih => cases hv with
    | vmrg hv1 hv2 => exact ih hv1
  | vlandr _ ih => cases hv with
    | vmrg hv1 hv2 => exact ih hv2

@[simp]
theorem rcd_shape {E v l B} :
  HasType E v (.rcd l B)
  → Value v
  → ∃ v', v = .lrec l v' := by
  intro ht hv
  cases ht with
  | trcd => exact ⟨_, rfl⟩
  | tquery => cases hv
  | tapp _ _ => cases hv
  | tbox _ _ => cases hv
  | tproj _ _ => cases hv
  | trproj _ _ => cases hv
  | tcase _ _ _ => cases hv
  | tunfold _ => cases hv


@[simp]
theorem notin_false {E v A} :
  HasType E v A
  → ∀ l v',
      RLookupV v l v'
      → ¬ Lin l A
      → False := by
  intro ht
  induction ht with
  | tint => intro l v' hr; cases hr
  | tunit => intro l v' hr; cases hr
  | tquery => intro l v' hr; cases hr
  | tlam _ => intro l v' hr; cases hr
  | tapp _ _ => intro l v' hr; cases hr
  | tbox _ _ => intro l v' hr; cases hr
  | tproj _ _ => intro l v' hr; cases hr
  | trproj _ _ => intro l v' hr; cases hr
  | tinl _ _ => intro l v' hr; cases hr
  | tinr _ _ => intro l v' hr; cases hr
  | tcase _ _ _ => intro l v' hr; cases hr
  | tflam _ => intro l v' hr; cases hr
  | tfclos _ _ _ => intro l v' hr; cases hr
  | tfold _ _ => intro l v' hr; cases hr
  | tunfold _ _ => intro l v' hr; cases hr
  | trcd ht ih =>
    intro l v' hr hnl
    cases hr with
    | rvlzero => exact hnl .rcd
  | tmrg h1 h2 ih1 ih2 =>
    intro l v' hr hnl
    cases hr with
    | vlandl hr' =>
      exact ih1 l _ hr' (fun hlin => hnl (.andl hlin))
    | vlandr hr' =>
      exact ih2 l _ hr' (fun hlin => hnl (.andr hlin))
  | tclos _ _ _ => intro l v' hr; cases hr

@[simp]
theorem rlookup_pres_aux {E l A} :
    RLookup E l A
    → ∀ {v v'},
      RLookupV v l v'
      → Value v
      → HasType .top v E
      → HasType E v' A := by
  intro hl
  induction hl with
  | zero =>
    intro v v' hlv hv ht
    cases ht with
    | tapp _ _ => cases hv
    | tbox _ _ => cases hv
    | tproj _ _ => cases hv
    | trproj _ _ => cases hv
    | tcase _ _ _ => cases hv
    | tunfold _ => cases hv
    | trcd ht' =>
      cases hlv with
      | rvlzero =>
        cases hv with
        | vrcd hv' =>
          exact value_weaken ht' hv'
  | landl hrl hnl ih =>
    intro v v' hlv hv ht
    cases hlv with
    | vlandl hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have h := ih hlv' hv1 (value_weaken h1 hv1)
          exact value_weaken h (rlookupv_value hlv' hv1)
    | vlandr hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have : False := notin_false h2 _ _ hlv' hnl
          contradiction
    | rvlzero =>
      cases ht
  | landr hrl hnla ih =>
    intro v v' hlv hv ht
    cases hlv with
    | vlandl hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have : False := notin_false h1 _ _ hlv' hnla
          contradiction
    | vlandr hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have h := ih hlv' hv2 (value_weaken h2 hv2)
          exact value_weaken h (rlookupv_value hlv' hv2)
    | rvlzero =>
      cases ht

@[simp]
theorem rlookup_pres {E l A} :
  RLookup E l A
  → ∀ {v v'},
      RLookupV v l v'
      → Value v
      → HasType .top v E
      → HasType .top v' A := by
  intro hl v v' hlv hv ht
  have h := rlookup_pres_aux hl hlv hv ht
  exact value_weaken h (rlookupv_value hlv hv)

@[simp]
theorem lookup_prog {n A B} :
  Lookup A n B
  → ∀ {v}, HasType .top v A → Value v
  → ∃ e', LookupV v n e' := by
  intro hl
  induction hl with
  | zero =>
    intro v ht hv
    cases ht <;> cases hv
    · rename_i v1 v2 h1 h2 hv1 hv2
      exact ⟨_, LookupV.lvzero⟩
  | succ _ ih =>
    intro v ht hv
    cases ht <;> cases hv
    · rename_i v1 v2 h1 h2 hv1 hv2
      have ⟨e', he⟩ := ih (value_weaken h1 hv1) hv1
      exact ⟨_, LookupV.lvsucc he⟩

@[simp]
theorem rlookup_prog {l A B} :
  RLookup A l B
  → ∀ {v}, HasType .top v A → Value v
  → ∃ e', RLookupV v l e' := by
  intro hl
  induction hl with
  | zero =>
    intro v ht hv
    cases ht <;> cases hv
    · exact ⟨_, RLookupV.rvlzero⟩
  | landl _ _ ih =>
    intro v ht hv
    cases ht <;> cases hv
    · rename_i v1 v2 h1 h2 hv1 hv2
      have ⟨e', he⟩ := ih (value_weaken h1 hv1) hv1
      exact ⟨_, RLookupV.vlandl he⟩
  | landr _ _ ih =>
    intro v ht hv
    cases ht <;> cases hv
    · rename_i v1 v2 h1 h2 hv1 hv2
      have ⟨e', he⟩ := ih (value_weaken h2 hv2) hv2
      exact ⟨_, RLookupV.vlandr he⟩

@[simp]
theorem gpreservation
  {e e' v : Exp}
  (hstep : Step v e e') :
  ∀ {E A : Typ},
  HasType E e A
  → HasType .top v E
  → HasType E e' A
  := by
  induction hstep with
  | squery heval =>
    rename_i v
    intro E A htype henv
    cases htype
    apply value_weaken; try assumption
    assumption
  | sappl hv hstep ih1 =>
    rename_i v v' e1 e2
    intro E A htype henv
    cases htype with
    | tapp ht1 ht2 =>
      apply HasType.tapp
      · exact ih1 ht1 henv
      · assumption
  | sboxl hv hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tbox ih2 ih3 =>
      rename_i Γ₁
      apply HasType.tbox <;> try assumption
      apply ih1
      repeat assumption
  | smrgl hv hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tmrg ih2 ih3 =>
        rename_i A B
        apply HasType.tmrg <;> try apply ih1
        repeat assumption
  | sappr hv hv1 hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tapp ht1 ht2 =>
      apply HasType.tapp
      · assumption
      · apply ih1<;> assumption
  | sboxr hv hstep ih1 ih2 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tbox ih3 ih4 =>
      rename_i Γ₁
      apply HasType.tbox <;> try assumption
      apply ih2
      repeat assumption
      apply value_weaken <;> try assumption
  | smrgr hv1 hv2 hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tmrg ih2 ih3 =>
        rename_i A B
        apply HasType.tmrg
        · assumption
        · apply ih1
          · assumption
          · apply HasType.tmrg
            · assumption
            · exact value_weaken ih2 hv2
  | sclos hv =>
    rename_i v1 v2 A
    intro E A htype henv
    rename_i e2
    cases htype with
    | tlam ih =>
      rename_i B
      apply HasType.tclos <;> try assumption
  | sbeta hv hv1 hv2 =>
    intro E A htype henv
    rename_i v1 v2 v3 B e1
    cases htype with
    | tapp ih1 ih2 =>
      cases ih1 with
      | tclos hv' ht' hb =>
        rename_i Γ₁
        apply HasType.tbox <;> try assumption
        apply HasType.tmrg
        · exact value_weaken ht' hv2
        · exact value_weaken ih2 hv1
  | sboxv hv1 hv2 hv3 =>
    intro E A htype henv
    rename_i v1 v2 v3
    cases htype with
    | tbox ih1 ih2 =>
      rename_i Γ₁
      apply value_weaken ih2 hv3
  | sproj hv hstep ih =>
    rename_i v1 e1 e2 n
    intro E A htype henv
    cases htype with
    | tproj ht hl =>
      exact HasType.tproj (ih ht henv) hl
  | sprojv hv1 hv2 hlook =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tproj ht hl =>
      rename_i A'
      obtain h1 := lookupv_value hlook
      obtain h2 := h1 hv2
      exact value_weaken (lookup_pres hl v2 v4 hlook hv2 (value_weaken ht hv2)) h2
  | slrec hv hstep ih1 =>
    rename_i v e1 e2 l
    intro E A htype henv
    cases htype
    rename_i A ih2
    apply HasType.trcd
    apply ih1
    repeat assumption
  | srproj hv hstep ih =>
    rename_i v1 e1 e2 l
    intro E A htype henv
    cases htype
    rename_i B ih2 hlook
    apply HasType.trproj <;> try assumption
    apply ih
    repeat assumption
  | srprojv hv hv1 hlook =>
    rename_i v' v1 l v2
    intro E A htype henv
    cases htype
    rename_i B ih2 hlook'
    exact value_weaken (rlookup_pres hlook' hlook hv1 (value_weaken ih2 hv1)) (rlookupv_value hlook hv1)
  | sinl hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tinl ht => exact HasType.tinl (ih ht henv)
  | sinr hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tinr ht => exact HasType.tinr (ih ht henv)
  | scase hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tcase ht h1 h2 => exact HasType.tcase (ih ht henv) h1 h2
  | scasel hv hv1 =>
    intro E A htype henv
    cases htype with
    | tcase hinl h1 h2 =>
      cases hinl with
      | tinl ht1 =>
        exact HasType.tbox (HasType.tmrg (value_weaken henv hv) (value_weaken ht1 hv1)) h1
  | scaser hv hv1 =>
    intro E A htype henv
    cases htype with
    | tcase hinr h1 h2 =>
      cases hinr with
      | tinr ht1 =>
        exact HasType.tbox (HasType.tmrg (value_weaken henv hv) (value_weaken ht1 hv1)) h2
  | sfclos hv =>
    intro E A htype henv
    cases htype with
    | tflam h => exact HasType.tfclos hv henv h
  | sfbeta hv hv1 hv2 =>
    intro E A htype henv
    cases htype with
    | tapp ih1 ih2 =>
      cases ih1 with
      | tfclos hv' ht' hb =>
        exact HasType.tbox
          (HasType.tmrg
            (HasType.tmrg (value_weaken ht' hv2) (HasType.tfclos hv' ht' hb))
            (value_weaken ih2 hv1))
          hb
  | sfold hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tfold ht => exact HasType.tfold (ih ht henv)
  | sunfold hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tunfold ht heq => exact HasType.tunfold (ih ht henv) heq
  | sunfoldv hv hv1 =>
    intro E A htype henv
    cases htype with
    | tunfold ht heq =>
      subst heq
      cases ht with
      | tfold ht1 => exact ht1

theorem gprogress
  {E A : Typ} {e : Exp}
  {htype : HasType E e A} :
  ∀ {v : Exp},
  Value v
  → HasType .top v E
  → (Value e) ∨ (∃ e' : Exp, Step v e e') := by
  induction htype with
  | tquery =>
    rename_i Γ
    intro v hv henv
    right
    exists v
    exact Step.squery hv
  | tint =>
    rename_i Γ n
    intro v hv henv
    left
    exact Value.vint
  | tunit =>
    rename_i Γ
    intro v hv henv
    left
    exact Value.vunit
  | tapp htype1 htype2 ih1 ih2 =>
    rename_i Γ A B e1 e2
    intro v hv henv
    have h1 := ih1 hv henv
    have h2 := ih2 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep1⟩ := h
      right
      exists (.app e' e2)
      exact Step.sappl hv hstep1
    | inl hve1 =>
      right
      cases h2 with
      | inr h =>
        obtain ⟨e', hstep1⟩ := h
        exists (.app e1 e')
        exact Step.sappr hv hve1 hstep1
      | inl h =>
          cases hve1 with
          | vclos hvc =>
            cases htype1 with
            | tclos hv' ht' hb =>
              exact ⟨_, Step.sbeta hv h hvc⟩
          | vfclos hvc =>
            cases htype1 with
            | tfclos hv' ht' hb =>
              exact ⟨_, Step.sfbeta hv h hvc⟩
          | _ =>
            cases htype1
  | tbox htyp1 htyp2 ih1 ih2 =>
    rename_i Γ Γ₁ A e1 e2
    intro v hv henv
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e'', hstep⟩ := h
      right <;> exact ⟨_, Step.sboxl hv hstep⟩
    | inl hv1 =>
      right
      have henv2 : HasType .top e1 Γ₁ := value_weaken htyp1 hv1
      have h2 := ih2 hv1 henv2
      cases h2 with
      | inr h =>
        have ⟨e', hstep⟩ := h
        exists (.box e1 e')
        exact Step.sboxr hv hv1 hstep
      | inl hv' =>
        exists e2
        exact Step.sboxv hv hv1 hv'
  | tmrg htyp1 htyp2 ih1 ih2 =>
    rename_i Γ A B e1 e2
    intro v hv henv
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exact ⟨_, Step.smrgl hv hstep⟩
    | inl hve1 =>
      have henv' : HasType .top (.mrg v e1) (Γ.and A) :=
        HasType.tmrg henv (value_weaken htyp1 hve1)
      have h2 := ih2 (Value.vmrg hv hve1) henv'
      cases h2 with
      | inr h =>
        obtain ⟨e', hstep⟩ := h
        right
        exact ⟨_, Step.smrgr hv hve1 hstep⟩
      | inl hve2 =>
        left
        exact Value.vmrg hve1 hve2
  | tlam htyp ih1 =>
    rename_i Γ A1 B e1
    intro v hv henv
    right
    exists (.clos v A1 e1)
    exact Step.sclos hv
  | tclos hv htyp1 htyp2 ih1 ih2 =>
    rename_i Γ Γ₁ A1 B1 e1 e2
    intro v hv henv
    left
    (expose_names; exact Value.vclos hv_1)
  | tproj htyp1 hlookup ih1 =>
    rename_i Γ A B e1 n
    intro v hv henv
    right
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      exists (.proj e' n)
      exact Step.sproj hv hstep
    | inl h =>
      have htyp_top : HasType .top e1 A := value_weaken htyp1 h
      have ⟨v', hlv⟩ := lookup_prog hlookup htyp_top h
      exact ⟨_, Step.sprojv hv h hlv⟩
  | trcd htype ih1 =>
    intro v hv henv
    rename_i Γ A1 l e1
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exists (.lrec l e')
      exact Step.slrec hv hstep
    | inl h =>
      left
      exact Value.vrcd h
  | trproj htyp1 hlookup ih1 =>
    rename_i Γ A B l e1
    intro v hv henv
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exists (.rproj e' l)
      exact Step.srproj hv hstep
    | inl h =>
      right
      have htyp_top : HasType .top e1 B := value_weaken htyp1 h
      have ⟨v', hlv⟩ := rlookup_prog hlookup htyp_top h
      exact ⟨_, Step.srprojv hv h hlv⟩
  | tinl htyp ih =>
    intro v hv henv
    cases ih hv henv with
    | inl hve => left; exact Value.vinl hve
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exact ⟨_, Step.sinl hv hstep⟩
  | tinr htyp ih =>
    intro v hv henv
    cases ih hv henv with
    | inl hve => left; exact Value.vinr hve
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exact ⟨_, Step.sinr hv hstep⟩
  | tflam htyp ih =>
    intro v hv henv
    right
    exact ⟨_, Step.sfclos hv⟩
  | tfclos hv' htyp1 htyp2 ih1 ih2 =>
    intro v hv henv
    left
    exact Value.vfclos hv'
  | tfold htyp ih =>
    intro v hv henv
    cases ih hv henv with
    | inl hve => left; exact Value.vfold hve
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exact ⟨_, Step.sfold hv hstep⟩
  | tunfold htyp heq ih =>
    intro v hv henv
    right
    cases ih hv henv with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      exact ⟨_, Step.sunfold hv hstep⟩
    | inl hve =>
      match hve with
      | .vfold hv1 => exact ⟨_, Step.sunfoldv hv hv1⟩
      | .vint => cases htyp
      | .vunit => cases htyp
      | .vclos _ => cases htyp
      | .vrcd _ => cases htyp
      | .vmrg _ _ => cases htyp
      | .vinl _ => cases htyp
      | .vinr _ => cases htyp
      | .vfclos _ => cases htyp
  | tcase htyp h1 h2 ih ih1 ih2 =>
    rename_i Γ A B C e e1 e2
    intro v hv henv
    right
    cases ih hv henv with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      exact ⟨_, Step.scase hv hstep⟩
    | inl hve =>
      match hve with
      | .vinl hv1 => exact ⟨_, Step.scasel hv hv1⟩
      | .vinr hv1 => exact ⟨_, Step.scaser hv hv1⟩
      | .vint => cases htyp
      | .vunit => cases htyp
      | .vclos _ => cases htyp
      | .vrcd _ => cases htyp
      | .vmrg _ _ => cases htyp

theorem preservation {e e' A}
  : HasType .top e A
  → Step .unit e e'
  → HasType .top e' A := by
  intros htyp hstep
  apply gpreservation <;> try assumption
  exact HasType.tunit

theorem progress {e A}
  : HasType .top e A
  →   Value e
    ∨ ∃ e', Step .unit e e' := by
  intros htype
  apply gprogress <;> try assumption
  · exact Value.vunit
  · exact HasType.tunit

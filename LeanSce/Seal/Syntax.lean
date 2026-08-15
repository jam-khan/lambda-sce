-- λE^≤ (Seal): λE's de Bruijn binding discipline + Eᵢ's subtyping and restriction.
-- Paper fragment only: Int | ε | A → B | A & B | {l : A}.  See LeanSce/Seal/DESIGN.md.
namespace Seal

inductive Typ where
  | int  : Typ
  | top  : Typ
  | arr  : Typ → Typ → Typ
  | and  : Typ → Typ → Typ
  | rcd  : String → Typ → Typ
  deriving Repr

-- Expressions.  Deviation from λE (forced, see DESIGN.md (f)): lambdas and closures carry
-- the codomain annotation, because Casting-arrow must check and rewrite it and beta must
-- reseal the result.  `anno e A` is the sealing primitive `(e : A)`, ported from Eᵢ.
inductive Exp where
  | query : Exp
  | proj  : Exp → Nat → Exp
  | lit   : Nat → Exp
  | unit  : Exp
  | lam   : Typ → Typ → Exp → Exp
  | box   : Exp → Exp → Exp
  | clos  : Exp → Typ → Typ → Exp → Exp
  | app   : Exp → Exp → Exp
  | mrg   : Exp → Exp → Exp
  | lrec  : String → Exp → Exp
  | rproj : Exp → String → Exp
  | anno  : Exp → Typ → Exp
  deriving Repr

inductive Value : Exp → Prop where
  | vint  {n}       : Value (.lit n)
  | vunit           : Value .unit
  | vclos {v A B e} : Value v → Value (.clos v A B e)
  | vrcd  {v l}     : Value v → Value (.lrec l v)
  | vmrg  {v₁ v₂}   : Value v₁ → Value v₂ → Value (.mrg v₁ v₂)

-- Positional lookup on types (λE, unchanged): index 0 is the rightmost component.
inductive Lookup : Typ → Nat → Typ → Prop where
  | zero {A B}
    : Lookup (.and A B) 0 B
  | succ {A B n C}
    : Lookup A n C
    → Lookup (.and A B) (n+1) C

-- Positional lookup on value environments (λE, unchanged).
inductive LookupV : Exp → Nat → Exp → Prop where
  | lvzero {v₁ v₂ : Exp}
    : LookupV (.mrg v₁ v₂) 0 v₂
  | lvsucc {v₁ v₂ v₃ : Exp} {n : Nat}
    : LookupV v₁ n v₃
    → LookupV (.mrg v₁ v₂) (n + 1) v₃

-- l occurs in A (λE's label membership, used for the containment side conditions).
inductive Lin : String → Typ → Prop where
  | rcd {l A}
    : Lin l (.rcd l A)
  | andl {l A B}
    : Lin l A
    → Lin l (.and A B)
  | andr {l B A}
    : Lin l B
    → Lin l (.and A B)

-- λE's containment judgment l : A ∈ B — the negative premises rule out ambiguous labels.
inductive RLookup : Typ → String → Typ → Prop where
  | zero {l A}
    : RLookup (.rcd l A) l A
  | landl {A l C B}
    : RLookup A l C
    → ¬Lin l B
    → RLookup (.and A B) l C
  | landr {B l C A}
    : RLookup B l C
    → ¬Lin l A
    → RLookup (.and A B) l C

theorem rlookup_lin {A : Typ} {l : String} {C : Typ} : RLookup A l C → Lin l A := by
  intro h
  induction h with
  | zero => exact Lin.rcd
  | landl _ _ ih => exact Lin.andl ih
  | landr _ _ ih => exact Lin.andr ih

-- Value-level selection (λE sel-mrgl/sel-mrgr): nondeterministic as a relation, tamed by
-- typing through containment (see Determinism.lean).
inductive RLookupV : Exp → String → Exp → Prop where
  | rvlzero {l : String} {e : Exp}
    : RLookupV (.lrec l e) l e
  | vlandl {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₁ l e
    → RLookupV (.mrg e₁ e₂) l e
  | vlandr {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₂ l e
    → RLookupV (.mrg e₁ e₂) l e

-- Ordinary types, casting variant (Eᵢ): not ε and not an intersection.
inductive Ordinary : Typ → Prop where
  | oint         : Ordinary .int
  | oarr {A B}   : Ordinary (.arr A B)
  | orcd {l A}   : Ordinary (.rcd l A)

-- Top-like types ⌉A⌈ (Eᵢ, with ε playing Top).
inductive TopLike : Typ → Prop where
  | tltop        : TopLike .top
  | tland {A B}  : TopLike A → TopLike B → TopLike (.and A B)
  | tlarr {A B}  : TopLike B → TopLike (.arr A B)
  | tlrcd {l B}  : TopLike B → TopLike (.rcd l B)

-- Value generator A↑ (Eᵢ Definition 23), total with junk at Int: every lemma about genVal
-- is guarded by TopLike A, so the junk value is never observable.
def genVal : Typ → Exp
  | .int     => .unit
  | .top     => .unit
  | .arr A B => .clos .unit A B (genVal B)
  | .and A B => .mrg (genVal A) (genVal B)
  | .rcd l A => .lrec l (genVal A)

theorem genVal_value : (A : Typ) → Value (genVal A)
  | .int     => Value.vunit
  | .top     => Value.vunit
  | .arr _ _ => Value.vclos Value.vunit
  | .and A B => Value.vmrg (genVal_value A) (genVal_value B)
  | .rcd _ A => Value.vrcd (genVal_value A)

-- Top-likeness is decidable (constructively, by inversion at each shape).
theorem toplike_dec : (A : Typ) → TopLike A ∨ ¬ TopLike A
  | .int => Or.inr (fun h => nomatch h)
  | .top => Or.inl TopLike.tltop
  | .arr _ B =>
    match toplike_dec B with
    | Or.inl h => Or.inl (TopLike.tlarr h)
    | Or.inr h => Or.inr (fun htl => by cases htl with | tlarr hB => exact h hB)
  | .and A B =>
    match toplike_dec A, toplike_dec B with
    | Or.inl hA, Or.inl hB => Or.inl (TopLike.tland hA hB)
    | Or.inr hA, _ => Or.inr (fun htl => by cases htl with | tland h1 _ => exact hA h1)
    | _, Or.inr hB => Or.inr (fun htl => by cases htl with | tland _ h2 => exact hB h2)
  | .rcd l A =>
    match toplike_dec A with
    | Or.inl h => Or.inl (TopLike.tlrcd h)
    | Or.inr h => Or.inr (fun htl => by cases htl with | tlrcd hA => exact h hA)

end Seal

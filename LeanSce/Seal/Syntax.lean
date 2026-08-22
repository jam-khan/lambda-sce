-- λE^≤ (Seal): λE's de Bruijn binding discipline + Eᵢ's subtyping and restriction.
-- Paper fragment Int | ε | A → B | A & B | {l : A}, plus abstract type names (brands) for
-- module sealing with type abstraction.  See LeanSce/Seal/DESIGN.md.
namespace Seal

-- `brand n` is an abstract type name α_n.  Brands are statically allocated (one per
-- sealed compilation unit / seal occurrence); their representations live in a private
-- brand store `BrandStore` that only the sealing unit's typing derivation consults.  To
-- everyone else a brand is an opaque ordinary type: it is a subtype only of itself and ε,
-- disjoint from every type in which it does not occur, and casting at it is the identity
-- on values already wrapped at that brand.
inductive Typ where
  | int   : Typ
  | top   : Typ
  | arr   : Typ → Typ → Typ
  | and   : Typ → Typ → Typ
  | rcd   : String → Typ → Typ
  | brand : Nat → Typ
  -- Unions.  Subtyping is component-wise only (no injection subtyping A <: A∨B): union
  -- values are always explicitly tagged, so casting can follow the tag deterministically
  -- and COST extends without touching the arrow/record story.
  | or    : Typ → Typ → Typ
  deriving Repr

-- The private brand store: `Δ n = some R` means the sealing unit knows α_n ≈ R.  Clients
-- are typed with `Δ n = none`.
def BrandStore := Nat → Option Typ

def noBrands : BrandStore := fun _ => none

-- `substBrand n R S` replaces `brand n` by `R` in `S` (types have no binders, so this is
-- plain structural recursion).  `S[n := R]` is the *representation view* of the signature
-- `S`; `seal`/`unseal` coerce between the two views.
def substBrand (n : Nat) (R : Typ) : Typ → Typ
  | .int       => .int
  | .top       => .top
  | .arr A B   => .arr (substBrand n R A) (substBrand n R B)
  | .and A B   => .and (substBrand n R A) (substBrand n R B)
  | .rcd l A   => .rcd l (substBrand n R A)
  | .brand m   => if m = n then R else .brand m
  | .or A B    => .or (substBrand n R A) (substBrand n R B)

-- Expressions.  Deviation from λE (forced, see DESIGN.md (f)): lambdas and closures carry
-- the codomain annotation, because Casting-arrow must check and rewrite it and beta must
-- reseal the result.  `anno e A` is the value-level sealing primitive `(e : A)`, ported
-- from Eᵢ (hides width and depth).
--
-- Type abstraction adds three forms:
--   `wrap n v`         — a value branded at α_n (runtime form; the only inhabitants of a brand);
--   `seal n R S e`     — coerce `e : S[n:=R]` to `S`, wrapping at every positive α_n position
--                        (proxying arrows); "sealing = casting + branding";
--   `unseal n R S e`   — the converse coercion `S ⇒ S[n:=R]`, used inside the proxies that
--                        `seal` builds at arrow types.
-- Only a unit whose brand store knows α_n ≈ R can type `seal`/`unseal`/`wrap` at n.
inductive Exp where
  | query  : Exp
  | proj   : Exp → Nat → Exp
  | lit    : Nat → Exp
  | unit   : Exp
  | lam    : Typ → Typ → Exp → Exp
  | box    : Exp → Exp → Exp
  | clos   : Exp → Typ → Typ → Exp → Exp
  | app    : Exp → Exp → Exp
  | mrg    : Exp → Exp → Exp
  | lrec   : String → Exp → Exp
  | rproj  : Exp → String → Exp
  | anno   : Exp → Typ → Exp
  | wrap   : Nat → Exp → Exp
  | seal   : Nat → Typ → Typ → Exp → Exp
  | unseal : Nat → Typ → Typ → Exp → Exp
  -- Unions: inl B e injects into _ ∨ B, inr A e into A ∨ _.
  | inl    : Typ → Exp → Exp
  | inr    : Typ → Exp → Exp
  | case   : Exp → Exp → Exp → Exp
  -- Fixpoints (Eᵢ App. B, adapted to environment semantics): `flam A B e` is a recursive
  -- function of type A → B whose body sees ?.0 = argument, ?.1 = the function itself.
  -- `fclos v A B Bx e` is its closure.  It carries TWO codomains: the *internal* B is what
  -- the body and the self-reference in beta see and is never rewritten; the *external* Bx
  -- is the client-facing codomain, rewritten by casts exactly as a clos's codomain is.
  -- One annotation cannot serve both: casting must be able to widen the visible codomain
  -- (cast_progress along S-arr), but the body was typed with (A → B) in its context, and
  -- there is no subsumption to absorb a widened self-entry.
  | flam   : Typ → Typ → Exp → Exp
  | fclos  : Exp → Typ → Typ → Typ → Exp → Exp
  deriving Repr

inductive Value : Exp → Prop where
  | vint  {n}       : Value (.lit n)
  | vunit           : Value .unit
  | vclos {v A B e} : Value v → Value (.clos v A B e)
  | vrcd  {v l}     : Value v → Value (.lrec l v)
  | vmrg  {v₁ v₂}   : Value v₁ → Value v₂ → Value (.mrg v₁ v₂)
  | vwrap {n v}     : Value v → Value (.wrap n v)
  | vinl  {v B}     : Value v → Value (.inl B v)
  | vinr  {v A}     : Value v → Value (.inr A v)
  | vfclos {v A B Bx e} : Value v → Value (.fclos v A B Bx e)

theorem value_clos_env {v : Exp} {A B : Typ} {e : Exp} (h : Value (.clos v A B e))
    : Value v := by cases h with | vclos h' => exact h'

theorem value_fclos_env {v : Exp} {A B Bx : Typ} {e : Exp} (h : Value (.fclos v A B Bx e))
    : Value v := by cases h with | vfclos h' => exact h'

theorem value_inl_payload {v : Exp} {B : Typ} (h : Value (.inl B v)) : Value v := by
  cases h with | vinl h' => exact h'

theorem value_inr_payload {v : Exp} {A : Typ} (h : Value (.inr A v)) : Value v := by
  cases h with | vinr h' => exact h'

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

-- Ordinary types, casting variant (Eᵢ): not ε and not an intersection.  Brands are
-- ordinary: casting selects them out of merges like any other leaf type.
inductive Ordinary : Typ → Prop where
  | oint         : Ordinary .int
  | oarr {A B}   : Ordinary (.arr A B)
  | orcd {l A}   : Ordinary (.rcd l A)
  | obrand {n}   : Ordinary (.brand n)
  | oor {A B}    : Ordinary (.or A B)

-- Top-like types ⌉A⌈ (Eᵢ, with ε playing Top).
inductive TopLike : Typ → Prop where
  | tltop        : TopLike .top
  | tland {A B}  : TopLike A → TopLike B → TopLike (.and A B)
  | tlarr {A B}  : TopLike B → TopLike (.arr A B)
  | tlrcd {l B}  : TopLike B → TopLike (.rcd l B)

-- Value generator A↑ (Eᵢ Definition 23), total with junk at Int and at brands: every lemma
-- about genVal is guarded by TopLike A, so the junk values are never observable.
def genVal : Typ → Exp
  | .int     => .unit
  | .top     => .unit
  | .arr A B => .clos .unit A B (genVal B)
  | .and A B => .mrg (genVal A) (genVal B)
  | .rcd l A => .lrec l (genVal A)
  | .brand _ => .unit
  | .or _ _  => .unit

theorem genVal_value : (A : Typ) → Value (genVal A)
  | .int     => Value.vunit
  | .top     => Value.vunit
  | .arr _ _ => Value.vclos Value.vunit
  | .and A B => Value.vmrg (genVal_value A) (genVal_value B)
  | .rcd _ A => Value.vrcd (genVal_value A)
  | .brand _ => Value.vunit
  | .or _ _  => Value.vunit

-- Top-likeness is decidable (constructively, by inversion at each shape).
theorem toplike_dec : (A : Typ) → TopLike A ∨ ¬ TopLike A
  | .int => Or.inr (fun h => nomatch h)
  | .brand _ => Or.inr (fun h => nomatch h)
  | .or _ _ => Or.inr (fun h => nomatch h)
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

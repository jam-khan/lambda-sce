
namespace SCE

mutual

inductive Typ where
  | int  : Typ
  | top  : Typ
  | arr  : Typ → Typ → Typ
  | and  : Typ → Typ → Typ
  | or   : Typ → Typ → Typ
  | rcd  : String → Typ → Typ
  | sig  : ModTyp → Typ
  -- iso-recursive types: de Bruijn var 0 is bound by the nearest mu
  | var  : Nat → Typ
  | mu   : Typ → Typ
  -- abstract type names (brands), mirrored from Seal (see Seal/DESIGN.md §(g))
  | brand : Nat → Typ

inductive ModTyp where
  | TyIntf : Typ → ModTyp
  | TyArrM : Typ → ModTyp → ModTyp

end

deriving instance Repr for Typ
deriving instance Repr for ModTyp

mutual
-- substTyp d S T replaces var d by S in T (S is closed, so no shifting)
def substTyp (d : Nat) (S : Typ) : Typ → Typ
  | .int => .int
  | .top => .top
  | .arr A B => .arr (substTyp d S A) (substTyp d S B)
  | .and A B => .and (substTyp d S A) (substTyp d S B)
  | .or A B => .or (substTyp d S A) (substTyp d S B)
  | .rcd l A => .rcd l (substTyp d S A)
  | .sig mt => .sig (substModTyp d S mt)
  | .var n => if n = d then S else .var n
  | .mu T => .mu (substTyp (d + 1) S T)
  | .brand n => .brand n

def substModTyp (d : Nat) (S : Typ) : ModTyp → ModTyp
  | .TyIntf T => .TyIntf (substTyp d S T)
  | .TyArrM T mt => .TyArrM (substTyp d S T) (substModTyp d S mt)
end

mutual
-- substBrand n R T replaces brand n by R in T (the representation view of a signature)
def substBrand (n : Nat) (R : Typ) : Typ → Typ
  | .int => .int
  | .top => .top
  | .arr A B => .arr (substBrand n R A) (substBrand n R B)
  | .and A B => .and (substBrand n R A) (substBrand n R B)
  | .or A B => .or (substBrand n R A) (substBrand n R B)
  | .rcd l A => .rcd l (substBrand n R A)
  | .sig mt => .sig (substBrandModTyp n R mt)
  | .var k => .var k
  | .mu T => .mu (substBrand n R T)
  | .brand m => if m = n then R else .brand m

def substBrandModTyp (n : Nat) (R : Typ) : ModTyp → ModTyp
  | .TyIntf T => .TyIntf (substBrand n R T)
  | .TyArrM T mt => .TyArrM (substBrand n R T) (substBrandModTyp n R mt)
end

-- Source-level brand store: the representation type of each brand a compilation unit
-- knows (mirrors Seal.BrandStore; the target store is its image under sealTyp, see
-- Seal/Elaboration.lean).
def BrandStore := Nat → Option Typ

def noBrands : BrandStore := fun _ => none

inductive Sandbox where
  | sandboxed : Sandbox
  | open_ : Sandbox
  deriving Repr

inductive Exp where
  | query  : Exp
  | proj   : Exp → Nat → Exp
  | lit    : Nat → Exp
  | unit   : Exp
  | lam    : Typ → Exp → Exp
  | box    : Exp → Exp → Exp
  | clos   : Exp → Typ → Exp → Exp
  | app    : Exp → Exp → Exp
  | mrg    : Exp → Exp → Exp
  | lrec   : String → Exp → Exp
  | rproj  : Exp → String → Exp
  -- to be elaborated
  | mstruct : Sandbox → Exp → Exp
  | mfunctor : Sandbox → Typ → Exp → Exp
  | mclos : Exp → Typ → Exp → Exp
  | mlink : Exp → Exp → Exp
  | mapp : Exp → Exp → Exp
  -- more terms
  | nmrg  : Exp → Exp → Exp
  | letb  : Exp → Typ → Exp → Exp
  | openm : Exp → Exp → Exp
  -- n-ary linking: satisfy every labeled import of a functor at once
  | mlinkn : Exp → Exp → Exp
  -- unions: inl B e injects into _ ∨ B, inr A e into A ∨ _
  | inl   : Typ → Exp → Exp
  | inr   : Typ → Exp → Exp
  | case  : Exp → Exp → Exp → Exp
  -- fixpoint: flam A B e is a recursive function of type A → B;
  -- its body sees ?.0 = argument, ?.1 = the function itself
  | flam  : Typ → Typ → Exp → Exp
  | fclos : Exp → Typ → Typ → Exp → Exp
  -- iso-recursive types: fold T e stores the mu-body T, folds into mu T
  | fold   : Typ → Exp → Exp
  | unfold : Exp → Exp
  -- type abstraction (mirrored from Seal, see Seal/DESIGN.md §(g)): a value branded at
  -- brand n; the sealing coercion S[n:=R] ⇒ S and its converse
  | wrap    : Nat → Exp → Exp
  | mseal   : Nat → Typ → Typ → Exp → Exp
  | munseal : Nat → Typ → Typ → Exp → Exp
  deriving Repr

inductive Value : Exp → Prop where
  | vint   {n}      : Value (.lit n)
  | vunit           : Value .unit
  | vclos  {v A e}  : Value v → Value (.clos v A e)
  | vmclos {v A e}  : Value v → Value (.mclos v A e)
  | vmrg   {v₁ v₂}  : Value v₁ → Value v₂ → Value (.mrg v₁ v₂)
  | vlrec  {v l}    : Value v → Value (.lrec l v)
  | vinl   {v B}    : Value v → Value (.inl B v)
  | vinr   {v A}    : Value v → Value (.inr A v)
  | vfclos {v A B e} : Value v → Value (.fclos v A B e)
  | vfold  {v T}    : Value v → Value (.fold T v)
  | vwrap  {v n}    : Value v → Value (.wrap n v)

inductive SLookup : Typ → Nat → Typ → Prop
| zero (A B : Typ) : SLookup (Typ.and A B) 0 B
| succ (A B : Typ) (n : Nat) (C : Typ)
    : SLookup A n C → SLookup (Typ.and A B) (Nat.succ n) C

inductive LabelIn : String → Typ → Prop where
  | rcd (label : String) (T : Typ)
    : LabelIn label (Typ.rcd label T)
  | andl (A B : Typ) (label : String)
    : LabelIn label A → LabelIn label (Typ.and A B)
  | andr (A B : Typ) (label : String)
    : LabelIn label B → LabelIn label (Typ.and A B)
  | sig (label : String) (T : Typ)
    : LabelIn label T → LabelIn label (Typ.sig (ModTyp.TyIntf T))

inductive SRLookup : Typ → String → Typ → Prop
| zero (label : String) (T : Typ) :
    SRLookup (Typ.rcd label T) label T
| andl (A B : Typ) (label : String) (T : Typ) :
    SRLookup A label T →
    ¬ LabelIn label B →
    SRLookup (Typ.and A B) label T
| andr (A B : Typ) (label : String) (T : Typ) :
    SRLookup B label T →
    ¬ LabelIn label A →
    SRLookup (Typ.and A B) label T
-- `elabTyp` erases `sig` over an interface, so at the target a label sitting
-- under one is reachable by Core.RLookup.  Selection has to see through it too,
-- or the source would refuse lookups the target performs; this is the case that
-- makes `type_safe_record_lookup` total.  It mirrors `LabelIn.sig`.
| sig (label : String) (T A : Typ) :
    SRLookup T label A →
    SRLookup (Typ.sig (ModTyp.TyIntf T)) label A

-- A successful lookup witnesses containment.  This is why the `and` rules above
-- carry only the negative half of their disjointness condition: the positive
-- half follows from the first premise.  Core.RLookup is stated the same way.
theorem srlookup_labelin {A : Typ} {l : String} {T : Typ} : SRLookup A l T → LabelIn l A := by
  intro h
  induction h with
  | zero => exact LabelIn.rcd _ _
  | andl _ _ _ _ _ _ ih => exact LabelIn.andl _ _ _ ih
  | andr _ _ _ _ _ _ ih => exact LabelIn.andr _ _ _ ih
  | sig _ _ _ _ ih => exact LabelIn.sig _ _ ih

-- LinkOk Γ₁ D: the module type Γ₁ satisfies every labeled import of the
-- interface D ::= rcd l A | D & rcd l A (left-nested intersections of records)
inductive LinkOk : Typ → Typ → Prop where
  | one {Γ₁ : Typ} {l : String} {A : Typ}
    : SRLookup Γ₁ l A
    → LinkOk Γ₁ (.rcd l A)
  | more {Γ₁ D : Typ} {l : String} {A : Typ}
    : LinkOk Γ₁ D
    → SRLookup Γ₁ l A
    → LinkOk Γ₁ (.and D (.rcd l A))

end SCE

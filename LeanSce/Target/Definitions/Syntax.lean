
/-!
# Target / Definitions / Syntax

Calculus definitions.
-/

/-! ## Types -/

/-! Kind-indexed raw syntax for the new target. This development does not import
    the existing `Core` or `SCE` namespaces. Type/row binders share de Bruijn indices;
    the variable constructor records its kind. Guards are a third syntactic sort,
    not a kind that programs may quantify over. -/
namespace LeanSce.Target

inductive Kind where
  | type | row
  deriving DecidableEq, Repr, BEq

inductive TySort where
  | type | row | guards
  deriving DecidableEq, Repr, BEq

def Kind.sort : Kind → TySort
  | .type => .type
  | .row => .row

inductive Ty : TySort → Type where
  | tvar : Nat → Ty .type
  | rvar : Nat → Ty .row
  | unit : Ty .type
  | int : Ty .type
  | bool : Ty .type
  | string : Ty .type
  | prod : Ty .type → Ty .type → Ty .type
  | sum : Ty .type → Ty .type → Ty .type
  | arr : Ty .type → Ty .type → Ty .type
  | tag : String → Ty .type → Ty .type
  | record : Ty .row → Ty .type
  | all : Kind → Ty .guards → Ty .type → Ty .type
  | ex : Kind → Ty .guards → Ty .type → Ty .type
  | mu : Ty .type → Ty .type
  | empty : Ty .row
  | field : String → Ty .type → Ty .row
  | union : Ty .row → Ty .row → Ty .row
  | gnil : Ty .guards
  | gcons : Ty .row → Ty .row → Ty .guards → Ty .guards
  deriving DecidableEq, Repr, BEq

abbrev Typ := Ty .type
abbrev Row := Ty .row
abbrev Guards := Ty .guards

def Ty.var (k : Kind) (i : Nat) : Ty k.sort :=
  match k with | .type => .tvar i | .row => .rvar i

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => ρ n + 1

def Ty.rename (ρ : Nat → Nat) : Ty s → Ty s
  | .tvar i => .tvar (ρ i)
  | .rvar i => .rvar (ρ i)
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .string => .string
  | .prod a b => .prod (a.rename ρ) (b.rename ρ)
  | .sum a b => .sum (a.rename ρ) (b.rename ρ)
  | .arr a b => .arr (a.rename ρ) (b.rename ρ)
  | .tag l a => .tag l (a.rename ρ)
  | .record r => .record (r.rename ρ)
  | .all k g a => .all k (g.rename (liftRen ρ)) (a.rename (liftRen ρ))
  | .ex k g a => .ex k (g.rename (liftRen ρ)) (a.rename (liftRen ρ))
  | .mu a => .mu (a.rename (liftRen ρ))
  | .empty => .empty
  | .field l a => .field l (a.rename ρ)
  | .union r t => .union (r.rename ρ) (t.rename ρ)
  | .gnil => .gnil
  | .gcons r t g => .gcons (r.rename ρ) (t.rename ρ) (g.rename ρ)

abbrev Subst := (k : Kind) → Nat → Ty k.sort

def Subst.id : Subst := fun k i => .var k i

def Subst.lift (σ : Subst) : Subst
  | k, 0 => .var k 0
  | k, n+1 => (σ k n).rename Nat.succ

def Ty.subst (σ : Subst) : Ty s → Ty s
  | .tvar i => σ .type i
  | .rvar i => σ .row i
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .string => .string
  | .prod a b => .prod (a.subst σ) (b.subst σ)
  | .sum a b => .sum (a.subst σ) (b.subst σ)
  | .arr a b => .arr (a.subst σ) (b.subst σ)
  | .tag l a => .tag l (a.subst σ)
  | .record r => .record (r.subst σ)
  | .all k g a => .all k (g.subst σ.lift) (a.subst σ.lift)
  | .ex k g a => .ex k (g.subst σ.lift) (a.subst σ.lift)
  | .mu a => .mu (a.subst σ.lift)
  | .empty => .empty
  | .field l a => .field l (a.subst σ)
  | .union r t => .union (r.subst σ) (t.subst σ)
  | .gnil => .gnil
  | .gcons r t g => .gcons (r.subst σ) (t.subst σ) (g.subst σ)

inductive Arg where
  | type : Typ → Arg
  | row : Row → Arg
  deriving DecidableEq, Repr, BEq

def Arg.kind : Arg → Kind
  | .type _ => .type
  | .row _ => .row

def Arg.rename (ρ : Nat → Nat) : Arg → Arg
  | .type a => .type (a.rename ρ)
  | .row r => .row (r.rename ρ)

def Arg.subst (σ : Subst) : Arg → Arg
  | .type a => .type (a.subst σ)
  | .row r => .row (r.subst σ)

/-- Opening removes the nearest binder. The unused kind at index zero maps to a
    closed dummy; kinding excludes that case from every well-typed occurrence. -/
def Arg.openSubst (u : Arg) : Subst
  | .type, 0 => match u with | .type a => a | .row _ => .unit
  | .row, 0 => match u with | .row r => r | .type _ => .empty
  | k, n+1 => .var k n

def Ty.open (a : Ty s) (u : Arg) : Ty s := a.subst u.openSubst

/-- Close old variables and then instantiate the newly bound variable. -/
def Subst.instantiate (θ : Subst) (u : Arg) : Subst :=
  fun k i => (θ.lift k i).open u

end LeanSce.Target

/-! ## Binding — definitions -/

namespace LeanSce.Target

def Subst.ofRen (ρ : Nat → Nat) : Subst := fun k n => .var k (ρ n)

end LeanSce.Target

/-! ## Syntax — definitions -/

namespace LeanSce.Target

inductive TermSort where
  | expr | fields
  deriving DecidableEq, Repr, BEq

inductive Prim where
  | add | eqInt | showInt | concat
  deriving DecidableEq, Repr, BEq

/-- Field lists retain initializer order. A well-typed completed list has unique
    labels and represents a finite map; programs have no field-order observer. -/
inductive Term : TermSort → Type where
  | unit : Term .expr
  | int : Int → Term .expr
  | bool : Bool → Term .expr
  | string : String → Term .expr
  | query : Term .expr
  | pair : Term .expr → Term .expr → Term .expr
  | fst : Term .expr → Term .expr
  | snd : Term .expr → Term .expr
  | box : Term .expr → Term .expr → Term .expr
  | lam : Typ → Term .expr → Term .expr
  | recfn : Typ → Typ → Term .expr → Term .expr
  | app : Term .expr → Term .expr → Term .expr
  | inl : Typ → Term .expr → Term .expr
  | inr : Typ → Term .expr → Term .expr
  | case : Term .expr → Term .expr → Term .expr → Term .expr
  | tag : String → Term .expr → Term .expr
  | find : String → Term .expr → Term .expr
  | record : Term .fields → Term .expr
  | get : Term .expr → String → Term .expr
  | merge : Term .expr → Term .expr → Term .expr
  | take : List String → Term .expr → Term .expr
  | drop : List String → Term .expr → Term .expr
  | relabel : String → String → Term .expr → Term .expr
  | tlam : Kind → Guards → Term .expr → Term .expr
  | tapp : Term .expr → Arg → Term .expr
  | pack : Arg → Typ → Term .expr → Term .expr
  | unpack : Term .expr → Term .expr → Term .expr
  | fold : Typ → Term .expr → Term .expr
  | unfold : Term .expr → Term .expr
  | prim : Prim → Term .fields → Term .expr
  | ite : Term .expr → Term .expr → Term .expr → Term .expr
  | clo : Term .expr → Typ → Term .expr → Term .expr
  | rclo : Term .expr → Typ → Typ → Term .expr → Term .expr
  | tclo : Term .expr → Kind → Guards → Term .expr → Term .expr
  | nil : Term .fields
  | cons : String → Term .expr → Term .fields → Term .fields
  deriving DecidableEq, Repr, BEq

abbrev Expr := Term .expr
abbrev Fields := Term .fields

/-- Primitive arguments use the same ordered list representation; their labels
    are ignored by the primitive's arity/type table. -/
def Term.ofList : List (String × Expr) → Fields
  | [] => .nil
  | (l,e)::xs => .cons l e (.ofList xs)

/-- Generalizing the sort keeps recursion structural and kernel-reducible.
    Only field lists are supplied at record boundaries. -/
def Term.toList : Term s → List (String × Expr)
  | .cons l e fs => (l,e) :: fs.toList
  | _ => []

def Term.ix : Nat → Expr
  | 0 => .snd .query
  | n+1 => .snd (Nat.rec .query (fun _ e => .fst e) (n+1))

def Term.close (e : Expr) : Expr := .box .unit e

def Term.letIn (a b : Expr) : Expr := .box (.pair .query a) b

def Term.seq (a b : Expr) : Expr := .letIn a (.pair (.snd .query) b)

def Term.isValue : Term s → Bool
  | .unit | .int _ | .bool _ | .string _ | .nil => true
  | .pair a b => a.isValue && b.isValue
  | .inl _ a | .inr _ a | .tag _ a | .record a | .pack _ _ a | .fold _ a => a.isValue
  | .clo cap _ _ | .rclo cap _ _ _ | .tclo cap _ _ _ => cap.isValue
  | .cons _ a rest => a.isValue && rest.isValue
  | _ => false

def Value (e : Term s) : Prop := e.isValue = true

/-- This operation changes only static binders and annotations. It never creates
    a term variable or an implicit dynamic-environment parameter. -/
def Term.subst (σ : Subst) : Term s → Term s
  | .unit => .unit
  | .int n => .int n
  | .bool b => .bool b
  | .string s => .string s
  | .query => .query
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .fst a => .fst (a.subst σ)
  | .snd a => .snd (a.subst σ)
  | .box a b => .box (a.subst σ) (b.subst σ)
  | .lam a b => .lam (a.subst σ) (b.subst σ)
  | .recfn a b e => .recfn (a.subst σ) (b.subst σ) (e.subst σ)
  | .app a b => .app (a.subst σ) (b.subst σ)
  | .inl a e => .inl (a.subst σ) (e.subst σ)
  | .inr a e => .inr (a.subst σ) (e.subst σ)
  | .case a b c => .case (a.subst σ) (b.subst σ) (c.subst σ)
  | .tag l a => .tag l (a.subst σ)
  | .find l a => .find l (a.subst σ)
  | .record fs => .record (fs.subst σ)
  | .get a l => .get (a.subst σ) l
  | .merge a b => .merge (a.subst σ) (b.subst σ)
  | .take ls a => .take ls (a.subst σ)
  | .drop ls a => .drop ls (a.subst σ)
  | .relabel l k a => .relabel l k (a.subst σ)
  | .tlam k g a => .tlam k (g.subst σ.lift) (a.subst σ.lift)
  | .tapp a u => .tapp (a.subst σ) (u.subst σ)
  | .pack u t a => .pack (u.subst σ) (t.subst σ) (a.subst σ)
  | .unpack a b => .unpack (a.subst σ) (b.subst σ.lift)
  | .fold t a => .fold (t.subst σ) (a.subst σ)
  | .unfold a => .unfold (a.subst σ)
  | .prim p args => .prim p (args.subst σ)
  | .ite a b c => .ite (a.subst σ) (b.subst σ) (c.subst σ)
  | .clo cap t b => .clo (cap.subst σ) (t.subst σ) (b.subst σ)
  | .rclo cap a b e => .rclo (cap.subst σ) (a.subst σ) (b.subst σ) (e.subst σ)
  | .tclo cap k g a => .tclo (cap.subst σ) k (g.subst σ.lift) (a.subst σ.lift)
  | .nil => .nil
  | .cons l a rest => .cons l (a.subst σ) (rest.subst σ)

def Term.rename (ρ : Nat → Nat) (e : Term s) : Term s := e.subst (Subst.ofRen ρ)

end LeanSce.Target

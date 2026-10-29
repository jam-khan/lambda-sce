import LeanSce.Target.Definitions.Syntax

/-!
# Source / Definitions / Types

Calculus definitions.
-/

/-! ## Types -/

/-! Source types are a distinct datatype. `Mod` is invariant and is not an arrow;
    only elaboration erases its constructor. Static binder kinds are shared. -/
namespace LeanSce.Source
open LeanSce.Target (Kind TySort liftRen)

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
  | module : Ty .row → Ty .row → Ty .type
  | gnil : Ty .guards
  | gcons : Ty .row → Ty .row → Ty .guards → Ty .guards
  deriving DecidableEq, Repr, BEq

abbrev Typ := Ty .type
abbrev Row := Ty .row
abbrev Guards := Ty .guards

def Ty.var (k : Kind) (i : Nat) : Ty k.sort :=
  match k with | .type => .tvar i | .row => .rvar i

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
  | .module i o => .module (i.rename ρ) (o.rename ρ)
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
  | .module i o => .module (i.subst σ) (o.subst σ)
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

end LeanSce.Source

/-! ## Binding — definitions -/

namespace LeanSce.Source

def Subst.ofRen (ρ : Nat → Nat) : Subst := fun k n => .var k (ρ n)

end LeanSce.Source

import LeanSce.Source.Definitions.Types
import LeanSce.Target.Definitions.Syntax

/-!
# Source / Definitions / Syntax

Calculus definitions.
-/

/-! ## Syntax — definitions -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

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
  | letVal : Typ → Term .expr → Term .expr → Term .expr
  | view : Typ → Typ → Term .expr → Term .expr → Term .expr
  | module : Row → Row → Term .expr → Term .expr
  | capture : Row → Row → Row → Term .expr → Term .expr → Term .expr
  | run : Row → Row → Row → Term .expr → Term .expr → Term .expr → Term .expr
  | link : Row → Row → Row → Term .expr → Term .expr → Term .expr → Term .expr
  | provide : Row → Row → Row → Row → Term .expr → Term .expr → Term .expr → Term .expr
  | complete : Row → Term .expr → Term .expr
  | moduleVal : Term .expr → Row → Row → Row → Term .expr → Term .expr
  | resid : Term .expr → Term .expr → Row → Row → Row → Term .expr
  | invoke : Row → Row → Term .expr → Term .expr → Term .expr
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
  | .moduleVal (.record fs) _ _ _ _ => fs.isValue
  | .resid m j _ _ _ => m.isValue && j.isValue
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
  | .letVal t a b => .letVal (t.subst σ) (a.subst σ) (b.subst σ)
  | .view a b cd e => .view (a.subst σ) (b.subst σ) (cd.subst σ) (e.subst σ)
  | .module i o b => .module (i.subst σ) (o.subst σ) (b.subst σ)
  | .capture c i o cap b => .capture (c.subst σ) (i.subst σ) (o.subst σ) (cap.subst σ) (b.subst σ)
  | .run p i o cd m e => .run (p.subst σ) (i.subst σ) (o.subst σ) (cd.subst σ) (m.subst σ) (e.subst σ)
  | .link p i o cd e m => .link (p.subst σ) (i.subst σ) (o.subst σ) (cd.subst σ) (e.subst σ) (m.subst σ)
  | .provide p j k o cd e m => .provide (p.subst σ) (j.subst σ) (k.subst σ) (o.subst σ) (cd.subst σ) (e.subst σ) (m.subst σ)
  | .complete o m => .complete (o.subst σ) (m.subst σ)
  | .moduleVal cap c i o b => .moduleVal (cap.subst σ) (c.subst σ) (i.subst σ) (o.subst σ) (b.subst σ)
  | .resid m j r k o => .resid (m.subst σ) (j.subst σ) (r.subst σ) (k.subst σ) (o.subst σ)
  | .invoke i o m p => .invoke (i.subst σ) (o.subst σ) (m.subst σ) (p.subst σ)
  | .nil => .nil
  | .cons l a rest => .cons l (a.subst σ) (rest.subst σ)

def Term.rename (ρ : Nat → Nat) (e : Term s) : Term s := e.subst (Subst.ofRen ρ)

/-- Certificates contain ordinary core code even when their annotations contain
    source module types. Source operations cannot occur inside this code. -/
def Term.isCore : Term s → Bool
  | .unit | .int _ | .bool _ | .string _ | .query | .nil => true
  | .pair a b | .box a b | .app a b | .merge a b => a.isCore && b.isCore
  | .fst a | .snd a | .lam _ a | .recfn _ _ a | .inl _ a | .inr _ a
  | .tag _ a | .find _ a | .record a | .get a _ | .take _ a | .drop _ a
  | .relabel _ _ a | .tlam _ _ a | .tapp a _ | .pack _ _ a | .fold _ a
  | .unfold a | .prim _ a => a.isCore
  | .case a b c | .ite a b c => a.isCore && b.isCore && c.isCore
  | .unpack a b | .clo a _ b | .rclo a _ _ b | .tclo a _ _ b => a.isCore && b.isCore
  | .cons _ a fs => a.isCore && fs.isCore
  | .letVal .. | .view .. | .module .. | .capture .. | .run .. | .link ..
  | .provide .. | .complete .. | .moduleVal .. | .resid .. | .invoke .. => false

end LeanSce.Source

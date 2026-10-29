import LeanSce.Target.Definitions.Syntax

/-!
# Target / Definitions / Semantics

Calculus definitions.
-/

/-! ## Semantics — definitions -/

namespace LeanSce.Target

/- These helpers recurse over a variable sort so Lean uses structural recursion.
   The evaluator calls field operations only after matching a record constructor. -/
def Term.lookup (label : String) : Term s → Option Expr
  | .cons l e rest => if label == l then some e else rest.lookup label
  | _ => none

def Term.labels : Term s → List String
  | .cons l _ rest => l :: rest.labels
  | _ => []

def Term.append : Term s → Fields → Fields
  | .cons l e rest, fs => .cons l e (rest.append fs)
  | _, fs => fs

def Term.filter (p : String → Bool) : Term s → Fields
  | .cons l e rest => if p l then .cons l e (rest.filter p) else rest.filter p
  | _ => .nil

def Term.renameFields (old new : String) : Term s → Fields
  | .cons l e rest => .cons (if l == old then new else l) e (rest.renameFields old new)
  | _ => .nil

def Term.findTags (label : String) : Term s → List Expr
  | .tag l e => if label == l then [e] else []
  | .pair a b => a.findTags label ++ b.findTags label
  | _ => []

def evalPrim : Prim → Fields → Option Expr
  | .add, .cons _ (.int a) (.cons _ (.int b) .nil) => some (.int (a+b))
  | .eqInt, .cons _ (.int a) (.cons _ (.int b) .nil) => some (.bool (a == b))
  | .showInt, .cons _ (.int a) .nil => some (.string (toString a))
  | .concat, .cons _ (.string a) (.cons _ (.string b) .nil) => some (.string (a++b))
  | _, _ => none

/-- Deterministic call-by-value reduction. `none` means value or stuck, never
    divergence. The `Step` relation separately requires a value ambient. -/
def step (ν : Expr) (e : Term s) : Option (Term s) :=
  if e.isValue then none else
  match e with
  | .query => some ν
  | .lam a b => some (.clo ν a b)
  | .recfn a b body => some (.rclo ν a b body)
  | .tlam k gs body => some (.tclo ν k gs body)
  | .box a b =>
      if !a.isValue then (step ν a).map (fun a' => .box a' b)
      else if b.isValue then some b
      else (step a b).map (.box a)
  | .pair a b =>
      if !a.isValue then (step ν a).map (fun a' => .pair a' b)
      else (step ν b).map (.pair a)
  | .fst a =>
      if !a.isValue then (step ν a).map .fst
      else match a with | .pair x _ => some x | _ => none
  | .snd a =>
      if !a.isValue then (step ν a).map .snd
      else match a with | .pair _ y => some y | _ => none
  | .app f x =>
      if !f.isValue then (step ν f).map (fun f' => .app f' x)
      else if !x.isValue then (step ν x).map (.app f)
      else match f with
        | .clo cap _ body => some (.box (.pair cap x) body)
        | .rclo cap _ _ body => some (.box (.pair (.pair cap f) x) body)
        | _ => none
  | .inl t a => (step ν a).map (.inl t)
  | .inr t a => (step ν a).map (.inr t)
  | .case a l r =>
      if !a.isValue then (step ν a).map (fun a' => .case a' l r)
      else match a with
        | .inl _ v => some (.box (.pair ν v) l)
        | .inr _ v => some (.box (.pair ν v) r)
        | _ => none
  | .tag l a => (step ν a).map (.tag l)
  | .find l a =>
      if !a.isValue then (step ν a).map (.find l)
      else match a.findTags l with | [v] => some v | _ => none
  | .record fs => (step ν fs).map .record
  | .cons l a rest =>
      if !a.isValue then (step ν a).map (fun a' => .cons l a' rest)
      else (step ν rest).map (.cons l a)
  | .get a l =>
      if !a.isValue then (step ν a).map (fun a' => .get a' l)
      else match a with | .record fs => fs.lookup l | _ => none
  | .merge a b =>
      if !a.isValue then (step ν a).map (fun a' => .merge a' b)
      else if !b.isValue then (step ν b).map (.merge a)
      else match a,b with
        | .record fs,.record gs =>
            if fs.labels.all (fun l => !gs.labels.contains l) then some (.record (fs.append gs)) else none
        | _,_ => none
  | .take ls a =>
      if !a.isValue then (step ν a).map (.take ls)
      else match a with
        | .record fs => if ls.all fs.labels.contains then some (.record (fs.filter ls.contains)) else none
        | _ => none
  | .drop ls a =>
      if !a.isValue then (step ν a).map (.drop ls)
      else match a with
        | .record fs => if ls.all fs.labels.contains then some (.record (fs.filter (fun l => !ls.contains l))) else none
        | _ => none
  | .relabel l k a =>
      if !a.isValue then (step ν a).map (.relabel l k)
      else match a with
        | .record fs =>
            if l != k && fs.labels.contains l && !fs.labels.contains k then some (.record (fs.renameFields l k)) else none
        | _ => none
  | .tapp a u =>
      if !a.isValue then (step ν a).map (fun a' => .tapp a' u)
      else match a with
        | .tclo cap _ _ body => some (.box cap (body.subst u.openSubst))
        | _ => none
  | .pack u t a => (step ν a).map (.pack u t)
  | .unpack a body =>
      if !a.isValue then (step ν a).map (fun a' => .unpack a' body)
      else match a with
        | .pack u _ v => some (.box (.pair ν v) (body.subst u.openSubst))
        | _ => none
  | .fold t a => (step ν a).map (.fold t)
  | .unfold a =>
      if !a.isValue then (step ν a).map .unfold
      else match a with | .fold _ v => some v | _ => none
  | .prim p args => if !args.isValue then (step ν args).map (.prim p) else evalPrim p args
  | .ite c a b =>
      if !c.isValue then (step ν c).map (fun c' => .ite c' a b)
      else match c with | .bool true => some a | .bool false => some b | _ => none
  | .unit | .int _ | .bool _ | .string _ | .nil => none
  | .clo .. | .rclo .. | .tclo .. => none

def Step (ν e e' : Expr) : Prop := Value ν ∧ step ν e = some e'

inductive Steps (ν : Expr) : Expr → Expr → Prop where
  | refl : Steps ν e e
  | next : Step ν e e' → Steps ν e' e'' → Steps ν e e''

def Terminates (ν e v : Expr) : Prop := Steps ν e v ∧ Value v

def Diverges (ν e : Expr) : Prop :=
  ∃ trace : Nat → Expr, trace 0 = e ∧ ∀ n, Step ν (trace n) (trace (n+1))

inductive Outcome where
  | done : Expr → Outcome
  | timeout : Expr → Outcome
  | stuck : Expr → Outcome
  deriving DecidableEq, Repr

def evaluate : Nat → Expr → Expr → Outcome
  | fuel, ν, e =>
    if e.isValue then .done e else
    match fuel with
    | 0 => .timeout e
    | n+1 => match step ν e with | none => .stuck e | some e' => evaluate n ν e'

abbrev Configuration := Expr × Expr

/-- Exactly n reductions in one native ambient. -/
inductive StepsN (ν : Expr) : Nat → Expr → Expr → Prop where
  | refl : StepsN ν 0 e e
  | next : Step ν e e' → StepsN ν n e' v → StepsN ν (n+1) e v

def TerminatesIn (ν e : Expr) (n : Nat) (v : Expr) : Prop :=
  StepsN ν n e v ∧ Value v

end LeanSce.Target

/-! ## Observation -/

namespace LeanSce.Target

/- Ground-data observations for executable regression checks. The finite-map
    view sorts completed record values; it never reorders evaluation. -/
mutual
inductive Ground where
  | unit
  | int : Int → Ground
  | bool : Bool → Ground
  | string : String → Ground
  | pair : Ground → Ground → Ground
  | inl : Ground → Ground
  | inr : Ground → Ground
  | tag : String → Ground → Ground
  | fold : Ground → Ground
  | record : GroundFields → Ground
  deriving DecidableEq, Repr

inductive GroundFields where
  | nil
  | cons : String → Ground → GroundFields → GroundFields
  deriving DecidableEq, Repr
end

def GroundFields.insert (l : String) (v : Ground) : GroundFields → GroundFields
  | .nil => .cons l v .nil
  | .cons k w fs =>
      if l ≤ k then .cons l v (.cons k w fs) else .cons k w (fs.insert l v)

def GroundFields.sorted : List (String × Ground) → GroundFields
  | [] => .nil
  | (l,v)::fs => (sorted fs).insert l v

/-- Unsupported higher-order values or insufficient observation depth yield
    `none`, so they cannot pass a check against a concrete `some` observation. -/
def observeGround : Nat → Expr → Option Ground
  | 0, _ => none
  | n+1, e => match e with
    | .unit => some .unit
    | .int z => some (.int z)
    | .bool b => some (.bool b)
    | .string s => some (.string s)
    | .pair a b => return .pair (← observeGround n a) (← observeGround n b)
    | .inl _ a => return .inl (← observeGround n a)
    | .inr _ a => return .inr (← observeGround n a)
    | .tag l a => return .tag l (← observeGround n a)
    | .fold _ a => return .fold (← observeGround n a)
    | .record fs => do
      let fields ← fs.toList.mapM fun (l,v) => do pure (l, ← observeGround n v)
      pure (.record (.sorted fields))
    | _ => none

def resultGround : Outcome → Option Ground
  | .done v => observeGround 64 v
  | _ => none

end LeanSce.Target

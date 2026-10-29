import LeanSce.Target.Definitions.Syntax

/-!
# Target / Definitions / Statics

Calculus definitions.
-/

/-! ## Rows — definitions -/

namespace LeanSce.Target

inductive Atom where
  | labelRow : String → Nat → Atom
  | rowRow : Nat → Nat → Atom
  deriving DecidableEq, Repr, BEq

def Atom.shift : Atom → Atom
  | .labelRow l i => .labelRow l (i+1)
  | .rowRow i j => .rowRow (min (i+1) (j+1)) (max (i+1) (j+1))

def Atom.mentions (i : Nat) : Atom → Bool
  | .labelRow _ j => i == j
  | .rowRow j k => i == j || i == k

inductive Entry where
  | label : String → Entry
  | tail : Nat → Entry
  deriving DecidableEq, Repr, BEq

def Ty.entries : Row → List Entry
  | .rvar i => [.tail i]
  | .empty => []
  | .field l _ => [.label l]
  | .union r s => r.entries ++ s.entries

def entryAtoms : Entry → Entry → Option (List Atom)
  | .label l, .label k => if l == k then none else some []
  | .label l, .tail i => some [.labelRow l i]
  | .tail i, .label l => some [.labelRow l i]
  | .tail i, .tail j => some [.rowRow (min i j) (max i j)]

def crossAtoms : List Entry → List Entry → Option (List Atom)
  | [], _ => some []
  | x :: xs, ys => do
    let here ← ys.mapM (entryAtoms x)
    let rest ← crossAtoms xs ys
    pure (here.flatten ++ rest)

def Ty.rowAtoms (r s : Row) : Option (List Atom) := crossAtoms r.entries s.entries

def Ty.guardAtoms : Guards → Option (List Atom)
  | .gnil => some []
  | .gcons r s gs => do
    let a ← r.rowAtoms s
    let rest ← gs.guardAtoms
    pure (a ++ rest)

structure Context where
  kinds : List Kind := []
  assumptions : List Atom := []
  deriving DecidableEq, Repr

def Context.empty : Context := ⟨[], []⟩

def Context.extend (Δ : Context) (k : Kind) (g : Guards) : Context :=
  ⟨k :: Δ.kinds, (g.guardAtoms.getD []) ++ Δ.assumptions.map Atom.shift⟩

def Disjoint (Δ : Context) (r s : Row) : Prop :=
  ∃ atoms, r.rowAtoms s = some atoms ∧ ∀ atom ∈ atoms, atom ∈ Δ.assumptions

/-- New atomic assumptions must mention the newly bound row variable. -/
def FreshGuards (k : Kind) (g : Guards) : Prop :=
  match k with
  | .type => g = .gnil
  | .row => ∃ atoms, g.guardAtoms = some atoms ∧ ∀ atom ∈ atoms, atom.mentions 0 = true

def Entails (Δ : Context) (g : Guards) : Prop :=
  ∃ atoms, g.guardAtoms = some atoms ∧ ∀ atom ∈ atoms, atom ∈ Δ.assumptions

inductive WellFormed : Context → Ty s → Prop where
  | tvar : Δ.kinds[i]? = some .type → WellFormed Δ (.tvar i)
  | rvar : Δ.kinds[i]? = some .row → WellFormed Δ (.rvar i)
  | unit : WellFormed Δ .unit
  | int : WellFormed Δ .int
  | bool : WellFormed Δ .bool
  | string : WellFormed Δ .string
  | prod : WellFormed Δ a → WellFormed Δ b → WellFormed Δ (.prod a b)
  | sum : WellFormed Δ a → WellFormed Δ b → WellFormed Δ (.sum a b)
  | arr : WellFormed Δ a → WellFormed Δ b → WellFormed Δ (.arr a b)
  | tag : WellFormed Δ a → WellFormed Δ (.tag l a)
  | record : WellFormed Δ r → WellFormed Δ (.record r)
  | all : FreshGuards k g → WellFormed (Δ.extend k g) g →
      WellFormed (Δ.extend k g) a → WellFormed Δ (.all k g a)
  | ex : FreshGuards k g → WellFormed (Δ.extend k g) g →
      WellFormed (Δ.extend k g) a → WellFormed Δ (.ex k g a)
  | mu : WellFormed (Δ.extend .type .gnil) a → WellFormed Δ (.mu a)
  | empty : WellFormed Δ .empty
  | field : WellFormed Δ a → WellFormed Δ (.field l a)
  | union : WellFormed Δ r → WellFormed Δ s → Disjoint Δ r s →
      WellFormed Δ (.union r s)
  | gnil : WellFormed Δ .gnil
  | gcons : WellFormed Δ r → WellFormed Δ s → WellFormed Δ gs →
      WellFormed Δ (.gcons r s gs)

inductive Context.Valid : Context → Prop where
  | empty : Context.Valid .empty
  | extend : Context.Valid Δ → FreshGuards k g →
      WellFormed (Δ.extend k g) g → Context.Valid (Δ.extend k g)

def Arg.WellFormed (Δ : Context) : Arg → Prop
  | .type a => Target.WellFormed Δ a
  | .row r => Target.WellFormed Δ r

/-- Known fields may be selected; an opaque row variable never reveals a label. -/
def Ty.lookup (l : String) : Row → Option Typ
  | .rvar _ => none
  | .empty => none
  | .field k a => if l == k then some a else none
  | .union r s => r.lookup l <|> s.lookup l

def Ty.knownLabels : Row → List String
  | .rvar _ => []
  | .empty => []
  | .field l _ => [l]
  | .union r s => r.knownLabels ++ s.knownLabels

def Ty.select (labels : List String) : Row → Row
  | .rvar _ => .empty
  | .empty => .empty
  | .field l a => if l ∈ labels then .field l a else .empty
  | .union r s => .union (r.select labels) (s.select labels)

def Ty.drop (labels : List String) : Row → Row
  | .rvar i => .rvar i
  | .empty => .empty
  | .field l a => if l ∈ labels then .empty else .field l a
  | .union r s => .union (r.drop labels) (s.drop labels)

def Ty.relabel (old new : String) : Row → Row
  | .rvar i => .rvar i
  | .empty => .empty
  | .field l a => .field (if l == old then new else l) a
  | .union r s => .union (r.relabel old new) (s.relabel old new)

end LeanSce.Target

/-! ## Equality — definitions -/

namespace LeanSce.Target

def GuardsEq (g h : Guards) : Prop :=
  ∃ xs ys, g.guardAtoms = some xs ∧ h.guardAtoms = some ys ∧ ∀ atom, atom ∈ xs ↔ atom ∈ ys

/-- Structural equality, with row ACU and normalized guard sets. There is no
    recursive-type unfolding or implicit subtyping in this relation. -/
inductive TyEq : Ty s → Ty s → Prop where
  | refl : TyEq a a
  | symm : TyEq a b → TyEq b a
  | trans : TyEq a b → TyEq b c → TyEq a c
  | prod : TyEq a a' → TyEq b b' → TyEq (.prod a b) (.prod a' b')
  | sum : TyEq a a' → TyEq b b' → TyEq (.sum a b) (.sum a' b')
  | arr : TyEq a a' → TyEq b b' → TyEq (.arr a b) (.arr a' b')
  | tag : TyEq a b → TyEq (.tag l a) (.tag l b)
  | record : TyEq r s → TyEq (.record r) (.record s)
  | all : GuardsEq g h → TyEq a b → TyEq (.all k g a) (.all k h b)
  | ex : GuardsEq g h → TyEq a b → TyEq (.ex k g a) (.ex k h b)
  | mu : TyEq a b → TyEq (.mu a) (.mu b)
  | field : TyEq a b → TyEq (.field l a) (.field l b)
  | union : TyEq r r' → TyEq s s' → TyEq (.union r s) (.union r' s')
  | union_empty : TyEq (.union r .empty) r
  | union_comm : TyEq (.union r s) (.union s r)
  | union_assoc : TyEq (.union (.union r s) t) (.union r (.union s t))

inductive Head where
  | variable | unit | int | bool | string | prod | sum | arr | tag | record | all | ex | mu
  deriving DecidableEq, Repr

def Ty.head : Typ → Head
  | .tvar _ => .variable
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .string => .string
  | .prod .. => .prod
  | .sum .. => .sum
  | .arr .. => .arr
  | .tag .. => .tag
  | .record .. => .record
  | .all .. => .all
  | .ex .. => .ex
  | .mu .. => .mu

/-- All known nonproduct constructors are opaque to legacy tag search. In
    particular there is deliberately no `tvar` constructor. -/
inductive Absent (l : String) : Typ → Prop where
  | unit : Absent l .unit
  | int : Absent l .int
  | bool : Absent l .bool
  | string : Absent l .string
  | arr : Absent l (.arr a b)
  | sum : Absent l (.sum a b)
  | record : Absent l (.record r)
  | all : Absent l (.all k g a)
  | ex : Absent l (.ex k g a)
  | mu : Absent l (.mu a)
  | tag : k ≠ l → Absent l (.tag k a)
  | prod : Absent l a → Absent l b → Absent l (.prod a b)

inductive Unique (l : String) : Typ → Typ → Prop where
  | here : Unique l (.tag l a) a
  | left : Unique l a c → Absent l b → Unique l (.prod a b) c
  | right : Absent l a → Unique l b c → Unique l (.prod a b) c

end LeanSce.Target

/-! ## Substitutions -/

namespace LeanSce.Target

/-- Apply a parallel substitution to one normalized constraint atom. Expansion
    happens through the existing row-disjointness checker, including collisions. -/
def Atom.substGuard (σ : Subst) : Atom → Guards
  | .labelRow l i => .gcons (.field l .unit) (σ .row i) .gnil
  | .rowRow i j => .gcons (σ .row i) (σ .row j) .gnil

/-- `θ ⊨ Δ`: every declared variable receives a closed, well-kinded argument,
    and every old row-disjointness assumption is discharged after substitution. -/
def Closing (σ : Subst) (Δ : Context) : Prop :=
  (∀ k i, Δ.kinds[i]? = some k → WellFormed .empty (σ k i)) ∧
  (∀ atom ∈ Δ.assumptions, Entails .empty (atom.substGuard σ))

end LeanSce.Target

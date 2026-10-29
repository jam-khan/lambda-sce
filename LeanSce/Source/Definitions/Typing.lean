import LeanSce.Source.Definitions.Statics
import LeanSce.Source.Definitions.Syntax

/-!
# Source / Definitions / Typing

Calculus definitions.
-/

/-! ## Typing — definitions -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

/- `Δ ; H ⊢ e : A`. Fields have a row as their result sort. Every free value
    reference is a query/projection; `Δ` contains only static type/row binders. -/
mutual
inductive HasType : Context → Typ → Expr → Typ → Prop where
  | query : WellFormed Δ h → HasType Δ h .query h
  | unit : WellFormed Δ h → HasType Δ h .unit .unit
  | int : WellFormed Δ h → HasType Δ h (.int n) .int
  | bool : WellFormed Δ h → HasType Δ h (.bool b) .bool
  | string : WellFormed Δ h → HasType Δ h (.string s) .string
  | pair : HasType Δ h a ta → HasType Δ h b tb → HasType Δ h (.pair a b) (.prod ta tb)
  | fst : HasType Δ h e (.prod a b) → HasType Δ h (.fst e) a
  | snd : HasType Δ h e (.prod a b) → HasType Δ h (.snd e) b
  | box : HasType Δ h a env → HasType Δ env b t → HasType Δ h (.box a b) t
  | lam : WellFormed Δ a → HasType Δ (.prod h a) e b → HasType Δ h (.lam a e) (.arr a b)
  | recfn : WellFormed Δ a → WellFormed Δ b →
      HasType Δ (.prod (.prod h (.arr a b)) a) e b → HasType Δ h (.recfn a b e) (.arr a b)
  | app : HasType Δ h f (.arr a b) → HasType Δ h x a → HasType Δ h (.app f x) b
  | inl : WellFormed Δ b → HasType Δ h e a → HasType Δ h (.inl b e) (.sum a b)
  | inr : WellFormed Δ a → HasType Δ h e b → HasType Δ h (.inr a e) (.sum a b)
  | case : HasType Δ h e (.sum a b) → HasType Δ (.prod h a) l c →
      HasType Δ (.prod h b) r c → HasType Δ h (.case e l r) c
  | tag : HasType Δ h e a → HasType Δ h (.tag l e) (.tag l a)
  | find : HasType Δ h e a → Unique l a b → HasType Δ h (.find l e) b
  | record : FieldsType Δ h fs r → HasType Δ h (.record fs) (.record r)
  | get : HasType Δ h e (.record r) → r.lookup l = some a → HasType Δ h (.get e l) a
  | merge : HasType Δ h e (.record r) → HasType Δ h f (.record s) → Disjoint Δ r s →
      HasType Δ h (.merge e f) (.record (.union r s))
  | take : HasType Δ h e (.record r) → ls.Nodup →
      (∀ l ∈ ls, ∃ a, r.lookup l = some a) → HasType Δ h (.take ls e) (.record (r.select ls))
  | drop : HasType Δ h e (.record r) → ls.Nodup →
      (∀ l ∈ ls, ∃ a, r.lookup l = some a) → HasType Δ h (.drop ls e) (.record (r.drop ls))
  | relabel : HasType Δ h e (.record r) → r.lookup l = some a → l ≠ k →
      Disjoint Δ (.field k a) (r.drop [l]) → HasType Δ h (.relabel l k e) (.record (r.relabel l k))
  | tlam : WellFormed Δ (.all k gs a) → WellFormed Δ h →
      HasType (Δ.extend k gs) (h.rename Nat.succ) e a → HasType Δ h (.tlam k gs e) (.all k gs a)
  | tapp : HasType Δ h e (.all k gs a) → u.kind = k → u.WellFormed Δ →
      Entails Δ (gs.open u) → HasType Δ h (.tapp e u) (a.open u)
  | pack : WellFormed Δ (.ex k gs a) → u.kind = k → u.WellFormed Δ →
      Entails Δ (gs.open u) → HasType Δ h e (a.open u) →
      HasType Δ h (.pack u (.ex k gs a) e) (.ex k gs a)
  | unpack : HasType Δ h p (.ex k gs a) → WellFormed Δ b →
      HasType (Δ.extend k gs) (.prod (h.rename Nat.succ) a) e (b.rename Nat.succ) →
      HasType Δ h (.unpack p e) b
  | fold : WellFormed Δ (.mu a) → HasType Δ h e (a.open (.type (.mu a))) →
      HasType Δ h (.fold (.mu a) e) (.mu a)
  | unfold : HasType Δ h e (.mu a) → HasType Δ h (.unfold e) (a.open (.type (.mu a)))
  | add : HasType Δ h e .int → HasType Δ h f .int →
      HasType Δ h (.prim .add (.cons l e (.cons k f .nil))) .int
  | eqInt : HasType Δ h e .int → HasType Δ h f .int →
      HasType Δ h (.prim .eqInt (.cons l e (.cons k f .nil))) .bool
  | showInt : HasType Δ h e .int → HasType Δ h (.prim .showInt (.cons l e .nil)) .string
  | concat : HasType Δ h e .string → HasType Δ h f .string →
      HasType Δ h (.prim .concat (.cons l e (.cons k f .nil))) .string
  | ite : HasType Δ h c .bool → HasType Δ h e a → HasType Δ h f a → HasType Δ h (.ite c e f) a
  | clo : WellFormed Δ h → WellFormed Δ a → Value cap → HasType Δ .unit cap env →
      HasType Δ (.prod env a) b t → HasType Δ h (.clo cap a b) (.arr a t)
  | rclo : WellFormed Δ h → WellFormed Δ a → WellFormed Δ b → Value cap →
      HasType Δ .unit cap env → HasType Δ (.prod (.prod env (.arr a b)) a) e b →
      HasType Δ h (.rclo cap a b e) (.arr a b)
  | tclo : WellFormed Δ h → WellFormed Δ (.all k gs a) → Value cap → HasType Δ .unit cap env →
      HasType (Δ.extend k gs) (env.rename Nat.succ) e a →
      HasType Δ h (.tclo cap k gs e) (.all k gs a)
  | letVal : WellFormed Δ a → HasType Δ h e a → HasType Δ (.prod h a) body b →
      HasType Δ h (.letVal a e body) b
  | view : HasType Δ h e a → CertType Δ a b cd → HasType Δ h (.view a b cd e) b
  | module : WellFormed Δ h → WellFormed Δ i → WellFormed Δ o →
      HasType Δ (.record i) body (.record o) → HasType Δ h (.module i o body) (.module i o)
  | capture : HasType Δ h cap (.record c) → WellFormed Δ i → WellFormed Δ o →
      Disjoint Δ c i → HasType Δ (.record (.union c i)) body (.record o) →
      HasType Δ h (.capture c i o cap body) (.module i o)
  | run : HasType Δ h m (.module i o) → HasType Δ h p (.record r) →
      CertType Δ (.record r) (.record i) cd → HasType Δ h (.run r i o cd m p) (.record o)
  | link : HasType Δ h p (.record r) → HasType Δ h m (.module i o) →
      CertType Δ (.record r) (.record i) cd → Disjoint Δ r o →
      HasType Δ h (.link r i o cd p m) (.record (.union r o))
  | provide : HasType Δ h p (.record r) → HasType Δ h m (.module (.union j k) o) →
      CertType Δ (.record r) (.record j) cd → WellFormed Δ j → WellFormed Δ k → Disjoint Δ j k →
      HasType Δ h (.provide r j k o cd p m) (.module k o)
  | complete : HasType Δ h m (.module .empty o) → HasType Δ h (.complete o m) (.record o)
  | moduleVal : WellFormed Δ h → Value cap → HasType Δ .unit cap (.record c) →
      WellFormed Δ i → WellFormed Δ o → Disjoint Δ c i →
      HasType Δ (.record (.union c i)) body (.record o) →
      HasType Δ h (.moduleVal cap c i o body) (.module i o)
  | resid : Value m → HasType Δ .unit m (.module (.union j k) o) →
      HasType Δ h saved (.record j) → WellFormed Δ j → WellFormed Δ k → Disjoint Δ j k →
      HasType Δ h (.resid m saved j k o) (.module k o)
  | invoke : HasType Δ h m (.module i o) → HasType Δ h p (.record i) →
      HasType Δ h (.invoke i o m p) (.record o)
  | value : Value v → HasType Δ .unit v a → WellFormed Δ h → HasType Δ h v a
  | conv : HasType Δ h e a → TyEq a b → WellFormed Δ b → HasType Δ h e b

inductive FieldsType : Context → Typ → Fields → Row → Prop where
  | nil : WellFormed Δ h → FieldsType Δ h .nil .empty
  | cons : HasType Δ h e a → FieldsType Δ h fs r → Disjoint Δ (.field l a) r →
      FieldsType Δ h (.cons l e fs) (.union (.field l a) r)
  | conv : FieldsType Δ h fs r → TyEq r s → WellFormed Δ s → FieldsType Δ h fs s
inductive CertType : Context → Typ → Typ → Expr → Prop where
  | closed : code.isCore = true → HasType Δ .unit code (.arr a b) →
      CertType Δ a b (.box .unit code)
end

/-- Ambient-independent value typing, using the fixed well-formed unit ambient. -/
def ValueType (Δ : Context) (v : Expr) (a : Typ) : Prop := Value v ∧ HasType Δ .unit v a

end LeanSce.Source

/-! ## Adapters — definitions -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

def Ty.knownFields : Row → List (String × Typ)
  | .rvar _ | .empty => []
  | .field l a => [(l,a)]
  | .union r s => r.knownFields ++ s.knownFields

def Ty.tails : Row → List Nat
  | .rvar i => [i]
  | .empty | .field .. => []
  | .union r s => r.tails ++ s.tails

def Ty.sortedFields (r : Row) : List (String × Typ) :=
  r.knownFields.mergeSort (fun a b => a.1 ≤ b.1)

def Arg.variable (k : Kind) (i : Nat) : Arg :=
  match k with | .type => .type (.tvar i) | .row => .row (.rvar i)

def identityAdapter (a : Typ) : Expr := .close (.lam a (.ix 0))

def arrowAdapter (a b c : Typ) (down up : Expr) : Expr :=
  .close (.lam (.arr a b) (.lam c (.app up (.app (.ix 1) (.app down (.ix 0))))))

def sameTailAdapter (r : Row) (fields : Fields) : Expr :=
  .close (.lam (.record r) (.merge (.record fields) (.drop r.knownLabels (.ix 0))))

def closedRecordAdapter (r : Row) (fields : Fields) : Expr :=
  .close (.lam (.record r) (.record fields))

def universalAdapter (a : Typ) (k : Kind) (g : Guards) (body : Expr) : Expr :=
  .close (.lam a (.tlam k g (.app body (.tapp (.ix 0) (Arg.variable k 0)))))

mutual
/-- Canonical matching. Negative premises encode the specified priority, and
    matching has no transitivity/subsumption constructor. -/
inductive Adapts : Context → Typ → Typ → Expr → Prop where
  | equal : WellFormed Δ a → WellFormed Δ b → TyEq a b →
      Adapts Δ a b (identityAdapter a)
  | arrow : ¬ TyEq (.arr a b) (.arr c d) →
      Adapts Δ c a down → Adapts Δ b d up →
      Adapts Δ (.arr a b) (.arr c d) (arrowAdapter a b c down up)
  | sameTail : WellFormed Δ (.record r) → WellFormed Δ (.record s) →
      ¬ TyEq (.record r) (.record s) → r.tails.Perm s.tails →
      AdaptsFields Δ r s.sortedFields fields →
      Adapts Δ (.record r) (.record s) (sameTailAdapter r fields)
  | closed : WellFormed Δ (.record r) → WellFormed Δ (.record s) →
      ¬ TyEq (.record r) (.record s) → s.tails = [] → ¬ r.tails.Perm s.tails →
      AdaptsFields Δ r s.sortedFields fields →
      Adapts Δ (.record r) (.record s) (closedRecordAdapter r fields)
  | all : WellFormed Δ (.all k g a) → WellFormed Δ (.all k h b) →
      ¬ TyEq (.all k g a) (.all k h b) → GuardsEq g h →
      Adapts (Δ.extend k g) a b body →
      Adapts Δ (.all k g a) (.all k h b) (universalAdapter (.all k g a) k g body)

inductive AdaptsFields : Context → Row → List (String × Typ) → Fields → Prop where
  | nil : AdaptsFields Δ r [] .nil
  | cons : r.lookup l = some a → Adapts Δ a b c → AdaptsFields Δ r fs es →
      AdaptsFields Δ r ((l,b)::fs) (.cons l (.app c (.get (.ix 0) l)) es)
end

end LeanSce.Source

import LeanSce.Source.Definitions.Semantics
import LeanSce.Source.Definitions.Typing

/-!
# Source / Definitions / Contexts

Calculus definitions.
-/

/-! ## Contextual Equivalence -/

namespace LeanSce.Source

/- Paired typing derivations for every source expression context, including
    stored code, certificates, and value-restricted captures. -/
mutual
inductive Compatible (R : Context → Typ → Expr → Expr → Typ → Prop) :
    Context → Typ → Expr → Expr → Typ → Prop where
  | hole : HasType Δ h e a → HasType Δ h E a → R Δ h e E a → Compatible R Δ h e E a
  | query : WellFormed Δ h → Compatible R Δ h .query .query h
  | unit : WellFormed Δ h → Compatible R Δ h .unit .unit .unit
  | int : WellFormed Δ h → Compatible R Δ h (.int n) (.int n) .int
  | bool : WellFormed Δ h → Compatible R Δ h (.bool b) (.bool b) .bool
  | string : WellFormed Δ h → Compatible R Δ h (.string s) (.string s) .string
  | pair : Compatible R Δ h x X a → Compatible R Δ h y Y b →
      Compatible R Δ h (.pair x y) (.pair X Y) (.prod a b)
  | fst : Compatible R Δ h x X (.prod a b) → Compatible R Δ h (.fst x) (.fst X) a
  | snd : Compatible R Δ h x X (.prod a b) → Compatible R Δ h (.snd x) (.snd X) b
  | box : Compatible R Δ h x X env → Compatible R Δ env y Y a →
      Compatible R Δ h (.box x y) (.box X Y) a
  | lam : WellFormed Δ a → Compatible R Δ (.prod h a) x X b →
      Compatible R Δ h (.lam a x) (.lam a X) (.arr a b)
  | recfn : WellFormed Δ a → WellFormed Δ b →
      Compatible R Δ (.prod (.prod h (.arr a b)) a) x X b →
      Compatible R Δ h (.recfn a b x) (.recfn a b X) (.arr a b)
  | app : Compatible R Δ h f F (.arr a b) → Compatible R Δ h x X a →
      Compatible R Δ h (.app f x) (.app F X) b
  | inl : WellFormed Δ b → Compatible R Δ h x X a →
      Compatible R Δ h (.inl b x) (.inl b X) (.sum a b)
  | inr : WellFormed Δ a → Compatible R Δ h x X b →
      Compatible R Δ h (.inr a x) (.inr a X) (.sum a b)
  | case : Compatible R Δ h x X (.sum a b) → Compatible R Δ (.prod h a) l L c →
      Compatible R Δ (.prod h b) r S c → Compatible R Δ h (.case x l r) (.case X L S) c
  | tag : Compatible R Δ h x X a → Compatible R Δ h (.tag l x) (.tag l X) (.tag l a)
  | find : Compatible R Δ h x X a → Unique l a b →
      Compatible R Δ h (.find l x) (.find l X) b
  | record : CompatibleFields R Δ h fs Fs r →
      Compatible R Δ h (.record fs) (.record Fs) (.record r)
  | get : Compatible R Δ h x X (.record r) → r.lookup l = some a →
      Compatible R Δ h (.get x l) (.get X l) a
  | merge : Compatible R Δ h x X (.record r) → Compatible R Δ h y Y (.record s) →
      Disjoint Δ r s → Compatible R Δ h (.merge x y) (.merge X Y) (.record (.union r s))
  | take : Compatible R Δ h x X (.record r) → ls.Nodup →
      (∀ l ∈ ls, ∃ a, r.lookup l = some a) →
      Compatible R Δ h (.take ls x) (.take ls X) (.record (r.select ls))
  | drop : Compatible R Δ h x X (.record r) → ls.Nodup →
      (∀ l ∈ ls, ∃ a, r.lookup l = some a) →
      Compatible R Δ h (.drop ls x) (.drop ls X) (.record (r.drop ls))
  | relabel : Compatible R Δ h x X (.record r) → r.lookup l = some a → l ≠ k →
      Disjoint Δ (.field k a) (r.drop [l]) →
      Compatible R Δ h (.relabel l k x) (.relabel l k X) (.record (r.relabel l k))
  | tlam : WellFormed Δ (.all k gs a) → WellFormed Δ h →
      Compatible R (Δ.extend k gs) (h.rename Nat.succ) x X a →
      Compatible R Δ h (.tlam k gs x) (.tlam k gs X) (.all k gs a)
  | tapp : Compatible R Δ h x X (.all k gs a) → u.kind = k → u.WellFormed Δ →
      Entails Δ (gs.open u) → Compatible R Δ h (.tapp x u) (.tapp X u) (a.open u)
  | pack : WellFormed Δ (.ex k gs a) → u.kind = k → u.WellFormed Δ →
      Entails Δ (gs.open u) → Compatible R Δ h x X (a.open u) →
      Compatible R Δ h (.pack u (.ex k gs a) x) (.pack u (.ex k gs a) X) (.ex k gs a)
  | unpack : Compatible R Δ h x X (.ex k gs a) → WellFormed Δ b →
      Compatible R (Δ.extend k gs) (.prod (h.rename Nat.succ) a) y Y (b.rename Nat.succ) →
      Compatible R Δ h (.unpack x y) (.unpack X Y) b
  | fold : WellFormed Δ (.mu a) → Compatible R Δ h x X (a.open (.type (.mu a))) →
      Compatible R Δ h (.fold (.mu a) x) (.fold (.mu a) X) (.mu a)
  | unfold : Compatible R Δ h x X (.mu a) →
      Compatible R Δ h (.unfold x) (.unfold X) (a.open (.type (.mu a)))
  | add : Compatible R Δ h x X .int → Compatible R Δ h y Y .int →
      Compatible R Δ h (.prim .add (.cons l x (.cons k y .nil)))
        (.prim .add (.cons l X (.cons k Y .nil))) .int
  | eqInt : Compatible R Δ h x X .int → Compatible R Δ h y Y .int →
      Compatible R Δ h (.prim .eqInt (.cons l x (.cons k y .nil)))
        (.prim .eqInt (.cons l X (.cons k Y .nil))) .bool
  | showInt : Compatible R Δ h x X .int →
      Compatible R Δ h (.prim .showInt (.cons l x .nil)) (.prim .showInt (.cons l X .nil)) .string
  | concat : Compatible R Δ h x X .string → Compatible R Δ h y Y .string →
      Compatible R Δ h (.prim .concat (.cons l x (.cons k y .nil)))
        (.prim .concat (.cons l X (.cons k Y .nil))) .string
  | ite : Compatible R Δ h c C .bool → Compatible R Δ h x X a → Compatible R Δ h y Y a →
      Compatible R Δ h (.ite c x y) (.ite C X Y) a
  | clo : WellFormed Δ h → WellFormed Δ a → Value cap → Value CAP →
      Compatible R Δ .unit cap CAP env → Compatible R Δ (.prod env a) b B t →
      Compatible R Δ h (.clo cap a b) (.clo CAP a B) (.arr a t)
  | rclo : WellFormed Δ h → WellFormed Δ a → WellFormed Δ b → Value cap → Value CAP →
      Compatible R Δ .unit cap CAP env →
      Compatible R Δ (.prod (.prod env (.arr a b)) a) x X b →
      Compatible R Δ h (.rclo cap a b x) (.rclo CAP a b X) (.arr a b)
  | tclo : WellFormed Δ h → WellFormed Δ (.all k gs a) → Value cap → Value CAP →
      Compatible R Δ .unit cap CAP env →
      Compatible R (Δ.extend k gs) (env.rename Nat.succ) x X a →
      Compatible R Δ h (.tclo cap k gs x) (.tclo CAP k gs X) (.all k gs a)
  | letVal : WellFormed Δ a → Compatible R Δ h x X a → Compatible R Δ (.prod h a) b B t →
      Compatible R Δ h (.letVal a x b) (.letVal a X B) t
  | view : Compatible R Δ h x X a → CompatibleCert R Δ a b cd CD →
      Compatible R Δ h (.view a b cd x) (.view a b CD X) b
  | module : WellFormed Δ h → WellFormed Δ i → WellFormed Δ o →
      Compatible R Δ (.record i) b B (.record o) →
      Compatible R Δ h (.module i o b) (.module i o B) (.module i o)
  | capture : Compatible R Δ h cap CAP (.record c) → WellFormed Δ i → WellFormed Δ o →
      Disjoint Δ c i → Compatible R Δ (.record (.union c i)) b B (.record o) →
      Compatible R Δ h (.capture c i o cap b) (.capture c i o CAP B) (.module i o)
  | run : Compatible R Δ h m M (.module i o) → Compatible R Δ h p P (.record r) →
      CompatibleCert R Δ (.record r) (.record i) cd CD →
      Compatible R Δ h (.run r i o cd m p) (.run r i o CD M P) (.record o)
  | link : Compatible R Δ h p P (.record r) → Compatible R Δ h m M (.module i o) →
      CompatibleCert R Δ (.record r) (.record i) cd CD → Disjoint Δ r o →
      Compatible R Δ h (.link r i o cd p m) (.link r i o CD P M) (.record (.union r o))
  | provide : Compatible R Δ h p P (.record r) → Compatible R Δ h m M (.module (.union j k) o) →
      CompatibleCert R Δ (.record r) (.record j) cd CD → WellFormed Δ j → WellFormed Δ k →
      Disjoint Δ j k → Compatible R Δ h (.provide r j k o cd p m) (.provide r j k o CD P M) (.module k o)
  | complete : Compatible R Δ h m M (.module .empty o) →
      Compatible R Δ h (.complete o m) (.complete o M) (.record o)
  | moduleVal : WellFormed Δ h → Value cap → Value CAP →
      Compatible R Δ .unit cap CAP (.record c) → WellFormed Δ i → WellFormed Δ o →
      Disjoint Δ c i → Compatible R Δ (.record (.union c i)) b B (.record o) →
      Compatible R Δ h (.moduleVal cap c i o b) (.moduleVal CAP c i o B) (.module i o)
  | resid : Value m → Value M → Compatible R Δ .unit m M (.module (.union j k) o) →
      Compatible R Δ h saved SAVED (.record j) → WellFormed Δ j → WellFormed Δ k → Disjoint Δ j k →
      Compatible R Δ h (.resid m saved j k o) (.resid M SAVED j k o) (.module k o)
  | invoke : Compatible R Δ h m M (.module i o) → Compatible R Δ h p P (.record i) →
      Compatible R Δ h (.invoke i o m p) (.invoke i o M P) (.record o)
  | value : Value v → Value V → Compatible R Δ .unit v V a → WellFormed Δ h →
      Compatible R Δ h v V a
  | conv : Compatible R Δ h x X a → TyEq a b → WellFormed Δ b → Compatible R Δ h x X b

inductive CompatibleFields (R : Context → Typ → Expr → Expr → Typ → Prop) :
    Context → Typ → Fields → Fields → Row → Prop where
  | nil : WellFormed Δ h → CompatibleFields R Δ h .nil .nil .empty
  | cons : Compatible R Δ h x X a → CompatibleFields R Δ h fs Fs r →
      Disjoint Δ (.field l a) r → CompatibleFields R Δ h (.cons l x fs) (.cons l X Fs) (.union (.field l a) r)
  | conv : CompatibleFields R Δ h fs Fs r → TyEq r s → WellFormed Δ s →
      CompatibleFields R Δ h fs Fs s

inductive CompatibleCert (R : Context → Typ → Expr → Expr → Typ → Prop) :
    Context → Typ → Typ → Expr → Expr → Prop where
  | closed : code.isCore = true → CODE.isCore = true →
      Compatible R Δ .unit code CODE (.arr a b) →
      CompatibleCert R Δ a b (.box .unit code) (.box .unit CODE)
end

inductive GroundType : Typ → Prop where
  | unit : GroundType .unit
  | int : GroundType .int
  | bool : GroundType .bool
  | string : GroundType .string

def ObservationEq (ν e E : Expr) : Prop :=
  (∀ v, Terminates ν e v ↔ Terminates ν E v) ∧ (Diverges ν e ↔ Diverges ν E)

def HoleAt (h a : Typ) (e E : Expr) : Context → Typ → Expr → Expr → Typ → Prop :=
  fun _ H x X b => H = h ∧ b = a ∧ x = e ∧ X = E

/-- All closing, typed ground source observations, with holes permitted in any
    expression slot and in value slots when both fillings are values. -/
def ContextualEq (Δ : Context) (h a : Typ) (e E : Expr) : Prop :=
  ∀ θ, Closing θ Δ → ∀ H g ν c C, GroundType g → ValueType .empty ν H →
    Compatible (HoleAt (h.subst θ) (a.subst θ) (e.subst θ) (E.subst θ)) .empty H c C g →
    ObservationEq ν c C

end LeanSce.Source

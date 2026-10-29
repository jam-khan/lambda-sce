import LeanSce.Target.Definitions.Semantics
import LeanSce.Target.Definitions.Statics
import LeanSce.Target.Definitions.Typing

/-!
# Target / LogicalRelation / Definitions

Homogeneous logical relation and typed observation contexts.
-/

/-! ## Logical Relation -/

namespace LeanSce.Target.LogicalRelation

/-- The activated computation of a function closure; application itself and
    removal of its administrative box are outside this configuration. -/
inductive ApplyBody : Expr → Expr → Configuration → Prop where
  | clo : ApplyBody (.clo cap a body) x (.pair cap x,body)
  | rclo : ApplyBody (.rclo cap a b body) x (.pair (.pair cap (.rclo cap a b body)) x,body)

inductive TypeBody : Expr → Arg → Configuration → Prop where
  | tclo : TypeBody (.tclo cap k gs body) u (cap,body.subst u.openSubst)

mutual
/-- Symmetric termination testing with the residual index charged to the
    computation whose bounded termination is being tested. -/
def ExprRel (n : Nat) (a : Typ) (q r : Configuration) : Prop :=
  (∀ k, k < n → ∀ v, TerminatesIn q.1 q.2 k v →
    ∃ w, Terminates r.1 r.2 w ∧ ValRel (n-k) a v w) ∧
  (∀ k, k < n → ∀ w, TerminatesIn r.1 r.2 k w →
    ∃ v, Terminates q.1 q.2 v ∧ ValRel (n-k) a v w)
termination_by (n,3 * sizeOf a + 2)
decreasing_by
  all_goals
    by_cases hz : k = 0
    · subst k; apply Prod.Lex.right; omega
    · apply Prod.Lex.left; omega

/-- Homogeneous closed values. Both sides use one closed type; existential
    witnesses are shared. This relation is sufficient for adapter coherence. -/
def ValRel (n : Nat) (a : Typ) (v w : Expr) : Prop :=
  ValueType .empty v a ∧ ValueType .empty w a ∧ ShapeRel n a v w
termination_by (n,3 * sizeOf a + 1)
decreasing_by all_goals (first | apply Prod.Lex.left; omega | apply Prod.Lex.right; omega)

/-- Rows are traversed structurally, while their concrete record values retain
    their initializer order. Exact field domains follow from the typing clause. -/
def ShapeRel (n : Nat) {s : TySort} (a : Ty s) (v w : Expr) : Prop :=
  match a with
  | .unit => v = .unit ∧ w = .unit
  | .int => ∃ z, v = .int z ∧ w = .int z
  | .bool => ∃ b, v = .bool b ∧ w = .bool b
  | .string => ∃ t, v = .string t ∧ w = .string t
  | .tvar _ => False
  | .prod a b => ∃ x y X Y, v = .pair x y ∧ w = .pair X Y ∧ ValRel n a x X ∧ ValRel n b y Y
  | .sum a b =>
      (∃ t t' x X, v = .inl t x ∧ w = .inl t' X ∧ ValRel n a x X) ∨
      (∃ t t' y Y, v = .inr t y ∧ w = .inr t' Y ∧ ValRel n b y Y)
  | .tag l a => ∃ x X, v = .tag l x ∧ w = .tag l X ∧ ValRel n a x X
  | .record r => ShapeRel n r v w
  | .arr a b => ∀ j, j < n → ∀ x X, ValRel j a x X →
      ∃ q r, ApplyBody v x q ∧ ApplyBody w X r ∧ ExprRel j b q r
  | .all k gs a => ∀ j, j < n → ∀ u, u.kind = k → u.WellFormed .empty →
      Entails .empty (gs.open u) →
      ∃ q r, TypeBody v u q ∧ TypeBody w u r ∧ ExprRel j (a.open u) q r
  | .ex k gs a => ∃ u t t' x X, v = .pack u t x ∧ w = .pack u t' X ∧
      u.kind = k ∧ u.WellFormed .empty ∧ Entails .empty (gs.open u) ∧
      ∀ j, j < n → ValRel j (a.open u) x X
  | .mu a => ∃ t t' x X, v = .fold t x ∧ w = .fold t' X ∧
      ∀ j, j < n → ValRel j (a.open (.type (.mu a))) x X
  | .rvar _ => False
  | .empty => True
  | .field l a => ∃ fs gs x X, v = .record fs ∧ w = .record gs ∧
      fs.lookup l = some x ∧ gs.lookup l = some X ∧ ValRel n a x X
  | .union r s => ShapeRel n r v w ∧ ShapeRel n s v w
  | .gnil | .gcons .. => True
termination_by (n,3 * sizeOf a)
decreasing_by all_goals simp_wf <;> first | apply Prod.Lex.left; omega | apply Prod.Lex.right; omega
end

end LeanSce.Target.LogicalRelation

/-! ## Contextual Equivalence — definitions -/

namespace LeanSce.Target

/- The compatible closure records actual syntax construction. Its derived `same` theorem
   supplies fixed context fragments, and `hole` supplies the compared terms.
   It includes stored closure code and respects value-only capture positions. -/
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
end

inductive GroundType : Typ → Prop where
  | unit : GroundType .unit
  | int : GroundType .int
  | bool : GroundType .bool
  | string : GroundType .string

def ObservationEq (ν e E : Expr) : Prop :=
  (∀ v, Terminates ν e v ↔ Terminates ν E v) ∧ (Diverges ν e ↔ Diverges ν E)

/-- A closed hole may occur under later static binders; its code and public
    types remain fixed. Both plugging judgments are checked by `Compatible.hole`. -/
def HoleAt (h a : Typ) (e E : Expr) : Context → Typ → Expr → Expr → Typ → Prop :=
  fun _ H x X b => H = h ∧ b = a ∧ x = e ∧ X = E

/-- All typed ground observation contexts, including runtime stored code and
    value-restricted slots. Compatible permits multiple occurrences of the hole. -/
def ContextualEq (Δ : Context) (h a : Typ) (e E : Expr) : Prop :=
  ∀ θ, Closing θ Δ → ∀ H g ν c C, GroundType g → ValueType .empty ν H →
    Compatible (HoleAt (h.subst θ) (a.subst θ) (e.subst θ) (E.subst θ)) .empty H c C g →
    ObservationEq ν c C

namespace LogicalRelation

def OpenRel (Δ : Context) (h : Typ) (e E : Expr) (a : Typ) : Prop :=
  ∀ θ, Closing θ Δ → ∀ n ν N, ValRel n (h.subst θ) ν N →
    ExprRel n (a.subst θ) (ν,e.subst θ) (N,E.subst θ)

end LogicalRelation
end LeanSce.Target

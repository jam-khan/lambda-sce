import LeanSce.Target.LogicalRelation.Definitions

/-!
# Target / Abstraction / Definitions

Heterogeneous representation relations, semantic environments, and admissibility.
-/

/-! ## Heterogeneous Relation -/

namespace LeanSce.Target.Heterogeneous

/-- A representation relation has no algebraic assumptions besides downward
    closure. Its value-typing obligations are stated separately. -/
structure IndexedRelation where
  holds : Nat → Expr → Expr → Prop
  mono : ∀ {m n v w}, m ≤ n → holds n v w → holds m v w

instance : CoeFun IndexedRelation (fun _ => Nat → Expr → Expr → Prop) := ⟨IndexedRelation.holds⟩

def IndexedRelation.empty : IndexedRelation := ⟨fun _ _ _ => False,by intros; contradiction⟩

def TypedRelation (r : IndexedRelation) (a b : Typ) : Prop :=
  ∀ n v w, r n v w → ValueType .empty v a ∧ ValueType .empty w b

/-- Paired type or row witnesses and arbitrary downward-closed representation
    relations. Unused components impose no condition. -/
structure Candidate where
  left : Arg
  right : Arg
  typeRelation : IndexedRelation
  fieldRelation : String → IndexedRelation

/-- Exactly the paper's admissibility requirements: closed witnesses, typed
    values, downward closure, and equal finite domains for row witnesses. -/
def Candidate.Admissible (p : Candidate) (k : Kind) : Prop :=
  p.left.kind = k ∧ p.right.kind = k ∧
  p.left.WellFormed .empty ∧ p.right.WellFormed .empty ∧
  match p.left,p.right with
  | .type a,.type b => TypedRelation p.typeRelation a b
  | .row r,.row s => r.knownLabels.Perm s.knownLabels ∧
      ∀ l a b, r.lookup l = some a → s.lookup l = some b →
        TypedRelation (p.fieldRelation l) a b
  | _,_ => False

structure Valuation where
  left : Subst
  right : Subst
  types : Nat → IndexedRelation
  fields : Nat → String → IndexedRelation

/-- Extend the semantic environment with the two independent witnesses. -/
def Valuation.extend (η : Valuation) (p : Candidate) : Valuation where
  left := η.left.instantiate p.left
  right := η.right.instantiate p.right
  types := fun i => match i with | 0 => p.typeRelation | i+1 => η.types i
  fields := fun i => match i with | 0 => p.fieldRelation | i+1 => η.fields i

/-- A valuation closes every declaration and guard on each side; its variable
    relations contain only values at the declared pair of closed types. -/
def Valuation.Valid (η : Valuation) (Δ : Context) : Prop :=
  Closing η.left Δ ∧ Closing η.right Δ ∧
  (∀ i, Δ.kinds[i]? = some .type → TypedRelation (η.types i) (η.left .type i) (η.right .type i)) ∧
  (∀ i, Δ.kinds[i]? = some .row →
    (η.left .row i).knownLabels.Perm (η.right .row i).knownLabels ∧
    ∀ l a b, (η.left .row i).lookup l = some a → (η.right .row i).lookup l = some b →
      TypedRelation (η.fields i l) a b)

mutual
/-- Symmetric termination testing with each tested execution charged its exact
    small-step cost. The two sides may have different hidden representations. -/
def ExprRel (n : Nat) (a : Typ) (η : Valuation) (q r : Configuration) : Prop :=
  (∀ k, k < n → ∀ v, TerminatesIn q.1 q.2 k v →
    ∃ w, Terminates r.1 r.2 w ∧ ValRel (n-k) a η v w) ∧
  (∀ k, k < n → ∀ w, TerminatesIn r.1 r.2 k w →
    ∃ v, Terminates q.1 q.2 v ∧ ValRel (n-k) a η v w)
termination_by (n,5 * sizeOf a + 4)
decreasing_by
  all_goals
    by_cases hz : k = 0
    · subst k; apply Prod.Lex.right; omega
    · apply Prod.Lex.left; omega

def ValRel (n : Nat) (a : Typ) (η : Valuation) (v w : Expr) : Prop :=
  ValueType .empty v (a.subst η.left) ∧ ValueType .empty w (a.subst η.right) ∧
    ShapeRel n a η v w
termination_by (n,5 * sizeOf a + 3)
decreasing_by all_goals (first | apply Prod.Lex.left; omega | apply Prod.Lex.right; omega)

def ShapeRel (n : Nat) (a : Typ) (η : Valuation) (v w : Expr) : Prop :=
  match a with
  | .unit => v = .unit ∧ w = .unit
  | .int => ∃ z, v = .int z ∧ w = .int z
  | .bool => ∃ b, v = .bool b ∧ w = .bool b
  | .string => ∃ t, v = .string t ∧ w = .string t
  | .tvar i => η.types i n v w
  | .prod a b => ∃ x y X Y, v = .pair x y ∧ w = .pair X Y ∧
      ValRel n a η x X ∧ ValRel n b η y Y
  | .sum a b =>
      (∃ t t' x X, v = .inl t x ∧ w = .inl t' X ∧ ValRel n a η x X) ∨
      (∃ t t' y Y, v = .inr t y ∧ w = .inr t' Y ∧ ValRel n b η y Y)
  | .tag l a => ∃ x X, v = .tag l x ∧ w = .tag l X ∧ ValRel n a η x X
  | .record r => RowShape n r η v w
  | .arr a b => ∀ j, j < n → ∀ x X, ValRel j a η x X →
      ∃ q r, LogicalRelation.ApplyBody v x q ∧ LogicalRelation.ApplyBody w X r ∧ ExprRel j b η q r
  | .all k gs a => ∀ j, j < n → ∀ p : Candidate, p.Admissible k →
      Entails .empty ((gs.subst η.left.lift).open p.left) →
      Entails .empty ((gs.subst η.right.lift).open p.right) →
      ∃ q r, LogicalRelation.TypeBody v p.left q ∧ LogicalRelation.TypeBody w p.right r ∧
        ExprRel j a (η.extend p) q r
  | .ex k gs a => ∃ p : Candidate, ∃ t t' x X,
      v = .pack p.left t x ∧ w = .pack p.right t' X ∧ p.Admissible k ∧
      Entails .empty ((gs.subst η.left.lift).open p.left) ∧
      Entails .empty ((gs.subst η.right.lift).open p.right) ∧
      ValRel n a (η.extend p) x X
  | .mu a => ∃ t t' x X, v = .fold t x ∧ w = .fold t' X ∧
      ∀ j, j < n → ValRel j (a.open (.type (.mu a))) η x X
termination_by (n,5 * sizeOf a + 2)
decreasing_by all_goals simp_wf <;> first | apply Prod.Lex.left; omega | apply Prod.Lex.right; omega

/-- The complete finite field domain is preserved, independently of initializer
    order. Each retained field uses the candidate assigned to its static origin. -/
def RowShape (n : Nat) (r : Row) (η : Valuation) (v w : Expr) : Prop :=
  ∃ fs gs, v = .record fs ∧ w = .record gs ∧ fs.labels.Perm gs.labels ∧
    ∀ l x X, fs.lookup l = some x → gs.lookup l = some X → FieldRel n r η l x X
termination_by (n,5 * sizeOf r + 1)
decreasing_by all_goals apply Prod.Lex.right; omega

/-- A row union interprets the disjoint union of its field candidates; opaque
    variables contribute their assigned per-label representation relations. -/
def FieldRel (n : Nat) (r : Row) (η : Valuation) (l : String) (v w : Expr) : Prop :=
  match r with
  | .rvar i => l ∈ (η.left .row i).knownLabels ∧ l ∈ (η.right .row i).knownLabels ∧
      η.fields i l n v w
  | .empty => False
  | .field k a => l = k ∧ ValRel n a η v w
  | .union r s => FieldRel n r η l v w ∨ FieldRel n s η l v w
termination_by (n,5 * sizeOf r)
decreasing_by all_goals simp_wf; all_goals apply Prod.Lex.right; all_goals omega
end

end LeanSce.Target.Heterogeneous

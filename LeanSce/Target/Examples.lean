import LeanSce.Target.Definitions.Typing
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Examples

Proofs and supporting constructions for examples.
-/

/-! ## Examples -/

namespace LeanSce.Target.Examples

/-- Opening an outer binder does not capture the inner type variable. -/
example : (Ty.all .type .gnil (.prod (.tvar 1) (.tvar 0))).open (.type .int) =
    .all .type .gnil (.prod .int (.tvar 0)) := by decide

/-- Type and row binders share index positions, while retaining their kinds. -/
example : (Ty.all .type .gnil (.record (.rvar 1))).open (.row (.field "x" .int)) =
    .all .type .gnil (.record (.field "x" .int)) := by decide

example : ¬ FreshGuards .type (.gcons .empty .empty .gnil) := by
  simp [FreshGuards]

/-- A fresh row binder cannot introduce an assumption about only an older row. -/
example : ¬ FreshGuards .row (.gcons (.rvar 1) (.field "x" .unit) .gnil) := by
  simp [FreshGuards, Ty.guardAtoms, Ty.rowAtoms, Ty.entries, crossAtoms,
    entryAtoms, Atom.mentions]

/-- Native query works at a scalar ambient, without an environment argument. -/
example : HasType .empty .int .query .int := query_typed .int

example : Terminates (.int 42) .query (.int 42) :=
  evaluate_sound (fuel := 1) rfl (by decide)

end LeanSce.Target.Examples

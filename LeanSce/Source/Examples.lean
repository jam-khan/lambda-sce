import LeanSce.Source.Definitions.Elaboration
import LeanSce.Source.Definitions.Semantics
import LeanSce.Source.Definitions.Typing
import LeanSce.Source.Metatheory.Basic
import LeanSce.Target.Definitions.Semantics
import LeanSce.Target.Metatheory.Basic

/-!
# Source / Examples

Proofs and supporting constructions for examples.
-/

/-! ## Examples -/

namespace LeanSce.Source.Examples
open LeanSce.Target (crossAtoms entryAtoms Atom)

def answerRow : Row := .union (.field "answer" .int) .empty
def answerBody : Expr := .record (.cons "answer" (.int 42) .nil)
def answerModule : Expr := .module .empty answerRow answerBody

private theorem answer_disjoint : Disjoint Δ (.field "answer" .int) .empty := by
  refine ⟨[], ?_, by simp⟩
  simp [Ty.rowAtoms, Ty.entries, crossAtoms]

/-- A closed module's body is checked under its imports, independently of H. -/
theorem answer_module_typed (hh : WellFormed Δ h) :
    HasType Δ h answerModule (.module .empty answerRow) := by
  apply HasType.module hh .empty (.union (.field .int) .empty answer_disjoint)
  exact .record (.cons (.int (.record .empty)) (.nil (.record .empty)) answer_disjoint)

theorem completed_module_typed (hh : WellFormed Δ h) :
    HasType Δ h (.complete answerRow answerModule) (.record answerRow) :=
  .complete (answer_module_typed hh)

/-- Both independent operational definitions produce the advertised export. -/
example : Terminates .unit (.get (.complete answerRow answerModule) "answer") (.int 42) :=
  evaluate_sound (fuel := 40) rfl (by decide)

example : Target.Terminates .unit
    (Term.get (.complete answerRow answerModule) "answer").erase (.int 42) :=
  Target.evaluate_sound (fuel := 80) rfl (by decide)

example : ¬ FreshGuards .type (.gcons .empty .empty .gnil) := by
  simp [FreshGuards]

example : ¬ FreshGuards .row (.gcons (.rvar 1) (.field "x" .unit) .gnil) := by
  simp [FreshGuards, Ty.guardAtoms, Ty.rowAtoms, Ty.entries, crossAtoms,
    entryAtoms, Atom.mentions]

end LeanSce.Source.Examples

/-! ## Prototype Examples -/

/-! Generated from the checked prototype corpus by sce-prototype/app/ExportLean.hs.
    The reduction checks use kernel-checked decide, not native_decide.
    The two timeout programs assert only exhaustion of 80 steps. -/
namespace LeanSce.Source.PrototypeExamples

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def isTimeout : Outcome → Bool
  | .timeout _ => true
  | _ => false
def targetTimeout : Target.Outcome → Bool
  | .timeout _ => true
  | _ => false

-- 01-native-query.sce
def ex01 : Expr :=
  (.box (.int (7)) (.get (.link (.union (.field "seed" .int) .empty) (.union (.field "seed" .int) .empty) (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "seed" .int) .empty)) (.snd .query))) (.record (.cons "seed" .query .nil)) (.capture (.union (.field "offset" .int) .empty) (.union (.field "seed" .int) .empty) (.union (.field "answer" .int) .empty) (.record (.cons "offset" .query .nil)) (.record (.cons "answer" (.prim .add (.cons "0" (.get .query "seed") (.cons "1" (.get .query "offset") .nil))) .nil)))) "answer"))
example : resultGround (evaluate 400 .unit ex01) = some (.int (14)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex01.erase) = some (.int (14)) := by decide

-- 02-capture-and-sandbox.sce
def ex02 : Expr :=
  (.letVal .int (.int (999)) (.letVal (.module (.union (.field "x" .int) .empty) (.union (.field "answer" .int) .empty)) (.capture (.union (.field "base" .int) .empty) (.union (.field "x" .int) .empty) (.union (.field "answer" .int) .empty) (.record (.cons "base" (.int (40)) .nil)) (.record (.cons "answer" (.prim .add (.cons "0" (.get .query "base") (.cons "1" (.get .query "x") .nil))) .nil))) (.get (.run (.union (.field "x" .int) (.union (.field "ignored" .int) .empty)) (.union (.field "x" .int) .empty) (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "x" .int) (.union (.field "ignored" .int) .empty))) (.merge (.record (.cons "x" (.app (.box .unit (.lam .int (.snd .query))) (.get (.snd .query) "x")) .nil)) (.drop ["ignored", "x"] (.snd .query))))) (.snd .query) (.record (.cons "x" (.int (2)) (.cons "ignored" (.snd (.fst .query)) .nil)))) "answer")))
example : resultGround (evaluate 400 .unit ex02) = some (.int (42)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex02.erase) = some (.int (42)) := by decide

-- 03-impredicative.sce
def ex03 : Expr :=
  (.letVal (.all .type .gnil (.arr (.tvar 0) (.tvar 0))) (.tlam .type .gnil (.lam (.tvar 0) (.box (.snd .query) .query))) (.letVal (.all .type .gnil (.arr (.tvar 0) (.tvar 0))) (.app (.tapp (.snd .query) (.type (.all .type .gnil (.arr (.tvar 0) (.tvar 0))))) (.snd .query)) (.app (.tapp (.snd .query) (.type .int)) (.int (42)))))
example : resultGround (evaluate 400 .unit ex03) = some (.int (42)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex03.erase) = some (.int (42)) := by decide

-- 04-open-row-extension.sce
def ex04 : Expr :=
  (.letVal (.all .row (.gcons (.union (.field "health" .unit) .empty) (.rvar 0) .gnil) (.arr (.record (.rvar 0)) (.record (.union (.rvar 0) (.union (.field "health" (.arr .unit .bool)) .empty))))) (.tlam .row (.gcons (.union (.field "health" .unit) .empty) (.rvar 0) .gnil) (.lam (.record (.rvar 0)) (.merge (.snd .query) (.record (.cons "health" (.lam .unit (.bool true)) .nil))))) (.app (.get (.app (.tapp (.snd .query) (.row (.union (.field "name" .string) (.union (.field "version" .int) .empty)))) (.record (.cons "name" (.string "SCE") (.cons "version" (.int (2)) .nil)))) "health") .unit))
example : resultGround (evaluate 400 .unit ex04) = some (.bool true) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex04.erase) = some (.bool true) := by decide

-- 05-polymorphic-staging.sce
def ex05 : Expr :=
  (.letVal (.all .row (.gcons (.union (.field "greeting" .unit) .empty) (.rvar 0) .gnil) (.arr (.module (.union (.union (.field "greeting" .string) .empty) (.rvar 0)) (.union (.field "message" .string) .empty)) (.module (.rvar 0) (.union (.field "message" .string) .empty)))) (.tlam .row (.gcons (.union (.field "greeting" .unit) .empty) (.rvar 0) .gnil) (.lam (.module (.union (.union (.field "greeting" .string) .empty) (.rvar 0)) (.union (.field "message" .string) .empty)) (.provide (.union (.field "greeting" .string) .empty) (.union (.field "greeting" .string) .empty) (.rvar 0) (.union (.field "message" .string) .empty) (.box .unit (.lam (.record (.union (.field "greeting" .string) .empty)) (.snd .query))) (.record (.cons "greeting" (.string "hello ") .nil)) (.snd .query)))) (.get (.run (.union (.field "name" .string) .empty) (.union (.field "name" .string) .empty) (.union (.field "message" .string) .empty) (.box .unit (.lam (.record (.union (.field "name" .string) .empty)) (.snd .query))) (.app (.tapp (.snd .query) (.row (.union (.field "name" .string) .empty))) (.module (.union (.field "name" .string) (.union (.field "greeting" .string) .empty)) (.union (.field "message" .string) .empty) (.record (.cons "message" (.prim .concat (.cons "0" (.get .query "greeting") (.cons "1" (.get .query "name") .nil))) .nil)))) (.record (.cons "name" (.string "Ada") .nil))) "message"))
example : resultGround (evaluate 400 .unit ex05) = some (.string "hello Ada") := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex05.erase) = some (.string "hello Ada") := by decide

-- 06-shared-abstract-witness.sce
def ex06 : Expr :=
  (.letVal (.ex .type .gnil (.record (.union (.field "load" (.arr .unit (.tvar 0))) (.union (.field "render" (.arr (.tvar 0) .string)) .empty)))) (.pack (.type .int) (.ex .type .gnil (.record (.union (.field "load" (.arr .unit (.tvar 0))) (.union (.field "render" (.arr (.tvar 0) .string)) .empty)))) (.record (.cons "load" (.lam .unit (.int (42))) (.cons "render" (.lam .int (.prim .concat (.cons "0" (.string "user ") (.cons "1" (.prim .showInt (.cons "0" (.snd .query) .nil)) .nil)))) .nil)))) (.unpack (.snd .query) (.get (.run (.union (.field "load" (.arr .unit (.tvar 0))) (.union (.field "render" (.arr (.tvar 0) .string)) .empty)) (.union (.field "load" (.arr .unit (.tvar 0))) (.union (.field "render" (.arr (.tvar 0) .string)) .empty)) (.union (.field "page" .string) .empty) (.box .unit (.lam (.record (.union (.field "load" (.arr .unit (.tvar 0))) (.union (.field "render" (.arr (.tvar 0) .string)) .empty))) (.snd .query))) (.module (.union (.field "load" (.arr .unit (.tvar 0))) (.union (.field "render" (.arr (.tvar 0) .string)) .empty)) (.union (.field "page" .string) .empty) (.record (.cons "page" (.app (.get .query "render") (.app (.get .query "load") .unit)) .nil))) (.snd .query)) "page")))
example : resultGround (evaluate 400 .unit ex06) = some (.string "user 42") := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex06.erase) = some (.string "user 42") := by decide

-- 07-function-variance.sce
def ex07 : Expr :=
  (.letVal (.record (.union (.field "process" (.arr (.record (.union (.field "name" .string) .empty)) (.record (.union (.field "ok" .bool) (.union (.field "trace" .string) .empty))))) .empty)) (.record (.cons "process" (.lam (.record (.union (.field "name" .string) .empty)) (.record (.cons "ok" (.bool true) (.cons "trace" (.get (.snd .query) "name") .nil)))) .nil)) (.letVal (.record (.union (.field "process" (.arr (.record (.union (.field "age" .int) (.union (.field "name" .string) .empty))) (.record (.union (.field "ok" .bool) .empty)))) .empty)) (.view (.record (.union (.field "process" (.arr (.record (.union (.field "name" .string) .empty)) (.record (.union (.field "ok" .bool) (.union (.field "trace" .string) .empty))))) .empty)) (.record (.union (.field "process" (.arr (.record (.union (.field "age" .int) (.union (.field "name" .string) .empty))) (.record (.union (.field "ok" .bool) .empty)))) .empty)) (.box .unit (.lam (.record (.union (.field "process" (.arr (.record (.union (.field "name" .string) .empty)) (.record (.union (.field "ok" .bool) (.union (.field "trace" .string) .empty))))) .empty)) (.merge (.record (.cons "process" (.app (.box .unit (.lam (.arr (.record (.union (.field "name" .string) .empty)) (.record (.union (.field "ok" .bool) (.union (.field "trace" .string) .empty)))) (.lam (.record (.union (.field "age" .int) (.union (.field "name" .string) .empty))) (.app (.box .unit (.lam (.record (.union (.field "ok" .bool) (.union (.field "trace" .string) .empty))) (.merge (.record (.cons "ok" (.app (.box .unit (.lam .bool (.snd .query))) (.get (.snd .query) "ok")) .nil)) (.drop ["ok", "trace"] (.snd .query))))) (.app (.snd (.fst .query)) (.app (.box .unit (.lam (.record (.union (.field "age" .int) (.union (.field "name" .string) .empty))) (.merge (.record (.cons "name" (.app (.box .unit (.lam .string (.snd .query))) (.get (.snd .query) "name")) .nil)) (.drop ["age", "name"] (.snd .query))))) (.snd .query))))))) (.get (.snd .query) "process")) .nil)) (.drop ["process"] (.snd .query))))) (.snd .query)) (.get (.app (.get (.snd .query) "process") (.record (.cons "age" (.int (21)) (.cons "name" (.string "Ada") .nil)))) "ok")))
example : resultGround (evaluate 400 .unit ex07) = some (.bool true) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex07.erase) = some (.bool true) := by decide

-- 08-universal-adapter.sce
def ex08 : Expr :=
  (.letVal (.all .type .gnil (.arr (.tvar 0) (.record (.union (.field "value" (.tvar 0)) (.union (.field "debug" .bool) .empty))))) (.tlam .type .gnil (.lam (.tvar 0) (.record (.cons "value" (.snd .query) (.cons "debug" (.bool true) .nil))))) (.letVal (.all .type .gnil (.arr (.tvar 0) (.record (.union (.field "value" (.tvar 0)) .empty)))) (.view (.all .type .gnil (.arr (.tvar 0) (.record (.union (.field "value" (.tvar 0)) (.union (.field "debug" .bool) .empty))))) (.all .type .gnil (.arr (.tvar 0) (.record (.union (.field "value" (.tvar 0)) .empty)))) (.box .unit (.lam (.all .type .gnil (.arr (.tvar 0) (.record (.union (.field "value" (.tvar 0)) (.union (.field "debug" .bool) .empty))))) (.tlam .type .gnil (.app (.box .unit (.lam (.arr (.tvar 0) (.record (.union (.field "value" (.tvar 0)) (.union (.field "debug" .bool) .empty)))) (.lam (.tvar 0) (.app (.box .unit (.lam (.record (.union (.field "value" (.tvar 0)) (.union (.field "debug" .bool) .empty))) (.merge (.record (.cons "value" (.app (.box .unit (.lam (.tvar 0) (.snd .query))) (.get (.snd .query) "value")) .nil)) (.drop ["debug", "value"] (.snd .query))))) (.app (.snd (.fst .query)) (.app (.box .unit (.lam (.tvar 0) (.snd .query))) (.snd .query))))))) (.tapp (.snd .query) (.type (.tvar 0))))))) (.snd .query)) (.get (.app (.tapp (.snd .query) (.type .int)) (.int (42))) "value")))
example : resultGround (evaluate 400 .unit ex08) = some (.int (42)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex08.erase) = some (.int (42)) := by decide

-- 09-opaque-tail-views.sce
def ex09 : Expr :=
  (.letVal (.all .row (.gcons (.union (.field "x" .unit) (.union (.field "debug" .unit) (.union (.field "fresh" .unit) .empty))) (.rvar 0) .gnil) (.arr (.record (.union (.rvar 0) (.union (.field "x" .int) (.union (.field "debug" .bool) .empty)))) (.record (.union (.rvar 0) (.union (.field "x" .int) (.union (.field "fresh" .int) .empty)))))) (.tlam .row (.gcons (.union (.field "x" .unit) (.union (.field "debug" .unit) (.union (.field "fresh" .unit) .empty))) (.rvar 0) .gnil) (.lam (.record (.union (.rvar 0) (.union (.field "x" .int) (.union (.field "debug" .bool) .empty)))) (.merge (.view (.record (.union (.rvar 0) (.union (.field "x" .int) (.union (.field "debug" .bool) .empty)))) (.record (.union (.rvar 0) (.union (.field "x" .int) .empty))) (.box .unit (.lam (.record (.union (.rvar 0) (.union (.field "x" .int) (.union (.field "debug" .bool) .empty)))) (.merge (.record (.cons "x" (.app (.box .unit (.lam .int (.snd .query))) (.get (.snd .query) "x")) .nil)) (.drop ["debug", "x"] (.snd .query))))) (.snd .query)) (.record (.cons "fresh" (.int (8)) .nil))))) (.app (.tapp (.snd .query) (.row (.union (.field "payload" .string) .empty))) (.record (.cons "debug" (.bool true) (.cons "payload" (.string "kept") (.cons "x" (.int (7)) .nil))))))
example : resultGround (evaluate 400 .unit ex09) = some (.record (.cons "fresh" (.int (8)) (.cons "payload" (.string "kept") (.cons "x" (.int (7)) .nil)))) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex09.erase) = some (.record (.cons "fresh" (.int (8)) (.cons "payload" (.string "kept") (.cons "x" (.int (7)) .nil)))) := by decide

-- 10-recursion-and-folds.sce
def ex10 : Expr :=
  (.letVal (.arr (.mu (.sum .unit (.tvar 0))) .int) (.recfn (.mu (.sum .unit (.tvar 0))) .int (.case (.unfold (.snd .query)) (.int (0)) (.prim .add (.cons "0" (.int (1)) (.cons "1" (.app (.snd (.fst (.fst .query))) (.snd .query)) .nil))))) (.letVal (.mu (.sum .unit (.tvar 0))) (.fold (.mu (.sum .unit (.tvar 0))) (.inr .unit (.fold (.mu (.sum .unit (.tvar 0))) (.inr .unit (.fold (.mu (.sum .unit (.tvar 0))) (.inr .unit (.fold (.mu (.sum .unit (.tvar 0))) (.inl (.mu (.sum .unit (.tvar 0))) .unit)))))))) (.letVal (.arr .int .int) (.recfn .int .int (.ite (.prim .eqInt (.cons "0" (.snd .query) (.cons "1" (.int (0)) .nil))) (.int (0)) (.prim .add (.cons "0" (.snd .query) (.cons "1" (.app (.snd (.fst .query)) (.prim .add (.cons "0" (.snd .query) (.cons "1" (.int (-1)) .nil)))) .nil))))) (.app (.snd .query) (.app (.snd (.fst (.fst .query))) (.snd (.fst .query)))))))
example : resultGround (evaluate 400 .unit ex10) = some (.int (6)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex10.erase) = some (.int (6)) := by decide

-- 11-commuting-provision.sce
def ex11 : Expr :=
  (.letVal (.module (.union (.field "a" .int) (.union (.field "b" .int) (.union (.field "c" .int) .empty))) (.union (.field "answer" .int) .empty)) (.module (.union (.field "c" .int) (.union (.field "a" .int) (.union (.field "b" .int) .empty))) (.union (.field "answer" .int) .empty) (.record (.cons "answer" (.prim .add (.cons "0" (.get .query "a") (.cons "1" (.prim .add (.cons "0" (.get .query "b") (.cons "1" (.get .query "c") .nil))) .nil))) .nil))) (.letVal (.module (.union (.field "c" .int) .empty) (.union (.field "answer" .int) .empty)) (.provide (.union (.field "b" .int) .empty) (.union (.field "b" .int) .empty) (.union (.field "c" .int) .empty) (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "b" .int) .empty)) (.snd .query))) (.record (.cons "b" (.int (20)) .nil)) (.provide (.union (.field "a" .int) .empty) (.union (.field "a" .int) .empty) (.union (.field "b" .int) (.union (.field "c" .int) .empty)) (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "a" .int) .empty)) (.snd .query))) (.record (.cons "a" (.int (10)) .nil)) (.snd .query))) (.letVal (.module (.union (.field "c" .int) .empty) (.union (.field "answer" .int) .empty)) (.provide (.union (.field "a" .int) .empty) (.union (.field "a" .int) .empty) (.union (.field "c" .int) .empty) (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "a" .int) .empty)) (.snd .query))) (.record (.cons "a" (.int (10)) .nil)) (.provide (.union (.field "b" .int) .empty) (.union (.field "b" .int) .empty) (.union (.field "a" .int) (.union (.field "c" .int) .empty)) (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "b" .int) .empty)) (.snd .query))) (.record (.cons "b" (.int (20)) .nil)) (.snd (.fst .query)))) (.prim .eqInt (.cons "0" (.get (.run (.union (.field "c" .int) .empty) (.union (.field "c" .int) .empty) (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "c" .int) .empty)) (.snd .query))) (.snd (.fst .query)) (.record (.cons "c" (.int (12)) .nil))) "answer") (.cons "1" (.get (.run (.union (.field "c" .int) .empty) (.union (.field "c" .int) .empty) (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "c" .int) .empty)) (.snd .query))) (.snd .query) (.record (.cons "c" (.int (12)) .nil))) "answer") .nil))))))
example : resultGround (evaluate 400 .unit ex11) = some (.bool true) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex11.erase) = some (.bool true) := by decide

-- 12-final-provision-delays.sce
def ex12 : Expr :=
  (.letVal (.module (.union (.field "seed" .int) .empty) (.union (.field "answer" .int) .empty)) (.module (.union (.field "seed" .int) .empty) (.union (.field "answer" .int) .empty) (.record (.cons "answer" (.app (.recfn .int .int (.app (.snd (.fst .query)) (.snd .query))) (.get .query "seed")) .nil))) (.letVal (.module .empty (.union (.field "answer" .int) .empty)) (.provide (.union (.field "seed" .int) .empty) (.union (.field "seed" .int) .empty) .empty (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "seed" .int) .empty)) (.snd .query))) (.record (.cons "seed" (.int (0)) .nil)) (.snd .query)) (.int (42))))
example : resultGround (evaluate 400 .unit ex12) = some (.int (42)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex12.erase) = some (.int (42)) := by decide

-- 13-completion-activates.sce
def ex13 : Expr :=
  (.complete (.union (.field "answer" .int) .empty) (.provide (.union (.field "seed" .int) .empty) (.union (.field "seed" .int) .empty) .empty (.union (.field "answer" .int) .empty) (.box .unit (.lam (.record (.union (.field "seed" .int) .empty)) (.snd .query))) (.record (.cons "seed" (.int (0)) .nil)) (.module (.union (.field "seed" .int) .empty) (.union (.field "answer" .int) .empty) (.record (.cons "answer" (.app (.recfn .int .int (.app (.snd (.fst .query)) (.snd .query))) (.get .query "seed")) .nil)))))
example : isTimeout (evaluate 80 .unit ex13) = true := by decide
example : targetTimeout (Target.evaluate 80 .unit ex13.erase) = true := by decide

-- 14-discarded-initializer.sce
def ex14 : Expr :=
  (.view (.record (.union (.field "answer" .int) (.union (.field "discarded" .int) .empty))) (.record (.union (.field "answer" .int) .empty)) (.box .unit (.lam (.record (.union (.field "answer" .int) (.union (.field "discarded" .int) .empty))) (.merge (.record (.cons "answer" (.app (.box .unit (.lam .int (.snd .query))) (.get (.snd .query) "answer")) .nil)) (.drop ["answer", "discarded"] (.snd .query))))) (.record (.cons "answer" (.int (42)) (.cons "discarded" (.app (.recfn .int .int (.app (.snd (.fst .query)) (.snd .query))) (.int (0))) .nil))))
example : isTimeout (evaluate 80 .unit ex14) = true := by decide
example : targetTimeout (Target.evaluate 80 .unit ex14.erase) = true := by decide

-- 15-alpha-and-aliases.sce
def ex15 : Expr :=
  (.letVal (.all .type .gnil (.arr (.tvar 0) (.arr (.all .type .gnil (.arr (.tvar 0) (.tvar 0))) (.tvar 0)))) (.tlam .type .gnil (.lam (.tvar 0) (.lam (.all .type .gnil (.arr (.tvar 0) (.tvar 0))) (.snd (.fst .query))))) (.app (.app (.tapp (.snd .query) (.type .int)) (.int (42))) (.tlam .type .gnil (.lam (.tvar 0) (.snd .query)))))
example : resultGround (evaluate 400 .unit ex15) = some (.int (42)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex15.erase) = some (.int (42)) := by decide

-- 16-legacy-environments.sce
def ex16 : Expr :=
  (.box (.tag "base" (.int (40))) (.snd (.box (.pair .query (.tag "extra" (.int (2)))) (.pair (.snd .query) (.prim .add (.cons "0" (.find "base" (.fst .query)) (.cons "1" (.find "extra" (.snd .query)) .nil)))))))
example : resultGround (evaluate 400 .unit ex16) = some (.int (42)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex16.erase) = some (.int (42)) := by decide

-- 17-exact-record-operations.sce
def ex17 : Expr :=
  (.letVal (.record (.union (.field "x" .int) (.union (.field "debug" .string) (.union (.field "kept" .bool) .empty)))) (.record (.cons "x" (.int (42)) (.cons "debug" (.string "private") (.cons "kept" (.bool true) .nil)))) (.merge (.relabel "x" "answer" (.take ["x"] (.snd .query))) (.merge (.drop ["x"] (.view (.record (.union (.field "x" .int) (.union (.field "debug" .string) (.union (.field "kept" .bool) .empty)))) (.record (.union (.field "x" .int) (.union (.field "kept" .bool) .empty))) (.box .unit (.lam (.record (.union (.field "x" .int) (.union (.field "debug" .string) (.union (.field "kept" .bool) .empty)))) (.merge (.record (.cons "kept" (.app (.box .unit (.lam .bool (.snd .query))) (.get (.snd .query) "kept")) (.cons "x" (.app (.box .unit (.lam .int (.snd .query))) (.get (.snd .query) "x")) .nil))) (.drop ["debug", "kept", "x"] (.snd .query))))) (.snd .query))) (.record (.cons "debug" (.int (0)) .nil)))))
example : resultGround (evaluate 400 .unit ex17) = some (.record (.cons "answer" (.int (42)) (.cons "debug" (.int (0)) (.cons "kept" (.bool true) .nil)))) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex17.erase) = some (.record (.cons "answer" (.int (42)) (.cons "debug" (.int (0)) (.cons "kept" (.bool true) .nil)))) := by decide

-- 18-existential-row.sce
def ex18 : Expr :=
  (.letVal (.ex .row (.gcons (.union (.field "answer" .unit) .empty) (.rvar 0) .gnil) (.record (.union (.rvar 0) (.union (.field "answer" .int) .empty)))) (.pack (.row (.union (.field "secret" .string) .empty)) (.ex .row (.gcons (.union (.field "answer" .unit) .empty) (.rvar 0) .gnil) (.record (.union (.rvar 0) (.union (.field "answer" .int) .empty)))) (.record (.cons "secret" (.string "hidden") (.cons "answer" (.int (42)) .nil)))) (.unpack (.snd .query) (.get (.view (.record (.union (.rvar 0) (.union (.field "answer" .int) .empty))) (.record (.union (.field "answer" .int) .empty)) (.box .unit (.lam (.record (.union (.rvar 0) (.union (.field "answer" .int) .empty))) (.record (.cons "answer" (.app (.box .unit (.lam .int (.snd .query))) (.get (.snd .query) "answer")) .nil)))) (.snd .query)) "answer")))
example : resultGround (evaluate 400 .unit ex18) = some (.int (42)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex18.erase) = some (.int (42)) := by decide

-- 19-certificate-substitution.sce
def ex19 : Expr :=
  (.letVal (.all .row .gnil (.arr (.record (.rvar 0)) (.record .empty))) (.tlam .row .gnil (.lam (.record (.rvar 0)) (.view (.record (.rvar 0)) (.record .empty) (.box .unit (.lam (.record (.rvar 0)) (.record .nil))) (.snd .query)))) (.app (.tapp (.snd .query) (.row .empty)) (.record .nil)))
example : resultGround (evaluate 400 .unit ex19) = some (.record .nil) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex19.erase) = some (.record .nil) := by decide

-- 20-first-class-modules.sce
def ex20 : Expr :=
  (.letVal (.all .type .gnil (.arr (.tvar 0) (.tvar 0))) (.tlam .type .gnil (.lam (.tvar 0) (.snd .query))) (.letVal (.record (.union (.field "m" (.module .empty (.union (.field "answer" .int) .empty))) (.union (.field "unused" .bool) .empty))) (.record (.cons "m" (.app (.tapp (.snd .query) (.type (.module .empty (.union (.field "answer" .int) .empty)))) (.module .empty (.union (.field "answer" .int) .empty) (.record (.cons "answer" (.int (42)) .nil)))) (.cons "unused" (.bool true) .nil))) (.box (.get (.view (.record (.union (.field "m" (.module .empty (.union (.field "answer" .int) .empty))) (.union (.field "unused" .bool) .empty))) (.record (.union (.field "m" (.module .empty (.union (.field "answer" .int) .empty))) .empty)) (.box .unit (.lam (.record (.union (.field "m" (.module .empty (.union (.field "answer" .int) .empty))) (.union (.field "unused" .bool) .empty))) (.merge (.record (.cons "m" (.app (.box .unit (.lam (.module .empty (.union (.field "answer" .int) .empty)) (.snd .query))) (.get (.snd .query) "m")) .nil)) (.drop ["m", "unused"] (.snd .query))))) (.snd .query)) "m") (.get (.complete (.union (.field "answer" .int) .empty) .query) "answer"))))
example : resultGround (evaluate 400 .unit ex20) = some (.int (42)) := by decide
example : Target.resultGround (Target.evaluate 400 .unit ex20.erase) = some (.int (42)) := by decide

end LeanSce.Source.PrototypeExamples

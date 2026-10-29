import LeanSce.Target.All
import LeanSce.Source.All
import Lean

/-! Check the new development, including private example proofs. Definitions in
    Goals are propositions, not assumed axioms and not counted as proofs. -/

-- Check the exact paper statements, in addition to the stronger internal results.
example : LeanSce.Target.Goals.Preservation := LeanSce.Target.preservation
example : LeanSce.Target.Goals.Progress := by
  intro ν e h a hν ht
  exact LeanSce.Target.progress hν ht
example : LeanSce.Target.Goals.AdapterTyping := LeanSce.Target.adapter_typing
example : LeanSce.Target.Goals.AdapterTermination := LeanSce.Target.adapter_termination
example : LeanSce.Target.Goals.AdapterExactShape := LeanSce.Target.adapter_exact_shape
example : LeanSce.Target.Goals.AdapterDivergence := LeanSce.Target.adapter_divergence
example : LeanSce.Target.Goals.AdapterCoherence := LeanSce.Target.adapter_coherence
example : LeanSce.Target.Goals.RepresentationIndependence := LeanSce.Target.representation_independence
example : LeanSce.Source.Goals.Preservation := LeanSce.Source.preservation
example : LeanSce.Source.Goals.Progress := by
  intro ν e h a hν ht
  exact LeanSce.Source.progress hν ht
example : LeanSce.Source.Goals.ElaborationTyping := LeanSce.Source.elaboration_typing
example : LeanSce.Source.Goals.TerminationCorrespondence := LeanSce.Source.termination_correspondence
example : LeanSce.Source.Goals.DivergenceCorrespondence := LeanSce.Source.divergence_correspondence
example : LeanSce.Source.Goals.AbstractModuleReplacement := LeanSce.Source.abstract_module_replacement
example (hd : LeanSce.Source.Adapts Δ a b code) : LeanSce.Source.CertType Δ a b code :=
  hd.certificate

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  -- Share dependency traversal across proofs; each referenced declaration is
  -- audited once even when thousands of proofs use the same supporting lemma.
  let mut dependencies : CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    let str := name.toString
    if (`LeanSce.Target).isPrefixOf name || (`LeanSce.Source).isPrefixOf name ||
        str.startsWith "_private.LeanSce.Target." ||
        str.startsWith "_private.LeanSce.Source." then
      match info with
      | .axiomInfo _ => throwError "New calculus declares an axiom: {name}"
      | .thmInfo _ =>
        count := count + 1
        let (_, nextDependencies) := ((CollectAxioms.collect name).run env).run dependencies
        for ax in nextDependencies.axioms.extract dependencies.axioms.size do
          unless ax == `propext || ax == `Quot.sound || ax == `Classical.choice do
            throwError "{name} depends on an unapproved axiom: {ax}"
        dependencies := nextDependencies
      | _ => pure ()
  logInfo m!"New-calculus proof audit passed ({count} theorem declarations, including generated support)."

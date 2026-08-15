import LeanSce.Seal.Sealing
import LeanSce.Seal.Elaboration

-- Smoke tests: sealing is not inert — the cast actually discards components, beta
-- actually casts the argument and reseals the result, and providers that differ outside
-- the seal agree exactly after sealing.
namespace Seal

-- Sealing discards: {x = 1} # {y = 2} sealed at {x : Int} is exactly {x = 1}.
example : Cast (.mrg (.lrec "x" (.lit 1)) (.lrec "y" (.lit 2))) (.rcd "x" .int)
    (.lrec "x" (.lit 1)) :=
  Cast.cmrgl Ordinary.orcd (Cast.crcd Cast.cint)

-- ... and the seal fires in the operational semantics (contrast λE, where annotations
-- do not even exist as expressions).
example : Step .unit
    (.anno (.mrg (.lrec "x" (.lit 1)) (.lrec "y" (.lit 2))) (.rcd "x" .int))
    (.lrec "x" (.lit 1)) :=
  Step.sannov Value.vunit (Value.vmrg (Value.vrcd Value.vint) (Value.vrcd Value.vint))
    (Cast.cmrgl Ordinary.orcd (Cast.crcd Cast.cint))

-- The typing side of the same seal: the merge has the full inferred type
-- {x : Int} & {y : Int}; the annotation compiles the client against {x : Int} only.
example : HasType .top
    (.anno (.mrg (.lrec "x" (.lit 1)) (.lrec "y" (.lit 2))) (.rcd "x" .int))
    (.rcd "x" .int) :=
  HasType.tanno
    (HasType.tmrg (HasType.trcd HasType.tint) (HasType.trcd HasType.tint)
      disj_top_r (disj_rcd_ne (by decide)))
    (Sub.sandl (sub_refl _))

-- Beta casts the argument at the annotation input and reseals the result at the
-- annotation codomain (the two casting premises new in λE^≤'s Step-beta).
example : Step .unit
    (.app (.clos .unit .int .int (.proj .query 0)) (.lit 7))
    (.box (.mrg .unit (.lit 7)) (.anno (.proj .query 0) .int)) :=
  Step.sbeta Value.vunit Value.vunit Value.vint Cast.cint

-- Two providers that differ outside the seal — {x = 1} # {y = 2} vs {x = 1} # {z = 3} —
-- both seal to {x = 1}, hence are related at the seal, hence (by `sealing`)
-- indistinguishable to any client typed against {x : Int}.
example : LR (.rcd "x" .int) (.lrec "x" (.lit 1)) (.lrec "x" (.lit 1)) :=
  ⟨_, _, rfl, rfl, 1, rfl, rfl⟩

-- A client of the seal: select x from the sealed environment.
example : HasType (.rcd "x" .int) (.rproj .query "x") .int :=
  HasType.trproj HasType.tquery RLookup.zero

-- SCE's non-capturing merge elaborates into λE^≤ via sealing — the (? : Γ) restriction
-- replaces Core's λ-self-application combinator (which λE^≤'s Disj Γ Γ premise forbids).
example : elabSeal .top (.nmrg (.lrec "x" (.lit 1)) (.lrec "y" (.lit 2)))
    (.and (.rcd "x" .int) (.rcd "y" .int))
    (.mrg (.lrec "x" (.lit 1))
      (.box (.anno .query .top) (.lrec "y" (.lit 2)))) :=
  elabSeal.enmrg (elabSeal.elrec (elabSeal.elit .top 1))
    (elabSeal.elrec (elabSeal.elit .top 2))
    disj_top_r (disj_rcd_ne (by decide))

-- ... and the elaborated code is well-typed λE^≤ by the preservation theorem.
example : Seal.HasType .top
    (.mrg (.lrec "x" (.lit 1)) (.box (.anno .query .top) (.lrec "y" (.lit 2))))
    (.and (.rcd "x" .int) (.rcd "y" .int)) :=
  seal_type_preservation
    (elabSeal.enmrg (elabSeal.elrec (elabSeal.elit .top 1))
      (elabSeal.elrec (elabSeal.elit .top 2))
      disj_top_r (disj_rcd_ne (by decide)))

end Seal

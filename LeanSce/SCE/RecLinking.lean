import LeanSce.SCE.Preservation
import LeanSce.SCE.Progress
import LeanSce.SCE.Determinism

open SCE S_Sem

/-
  Recursive module linking as a DERIVED form.

  A functor `e : sig (rcd l (A₁ → A₂) ⇒ B)` imports a single function
  `l : A₁ → A₂`; when its own output `B` exports `l` at the same type
  (the knot condition `SRLookup B l (A₁ → A₂)`), the import can be
  satisfied by the functor's own export: `mrecExp` ties the knot with the
  source-level fixpoint `flam` — no new primitive, no new metatheory.

  Semantics: each recursive call re-applies the functor to a package
  containing the wrapper itself (generative re-evaluation, the standard
  call-by-value reading). The recursive import must be function-typed:
  CBV value recursion would diverge.
-/

/-- The functor type for a recursive module: imports `l : A₁ → A₂`,
    exports `B`. -/
def FunctorTy (l : String) (A₁ A₂ B : Typ) : Typ :=
  .sig (.TyArrM (.rcd l (.arr A₁ A₂)) (.TyIntf B))

/-- The recursive-import wrapper: a fixpoint function whose body re-applies
    the functor (`?.2`) to a package containing the wrapper itself (`?.1`),
    projects the export `l`, and applies it to the argument (`?.0`). -/
def recWrap (l : String) (A₁ A₂ : Typ) : Exp :=
  .flam A₁ A₂
    (.app (.rproj (.mapp (.proj .query 2) (.lrec l (.proj .query 1))) l)
      (.proj .query 0))

/-- Recursive linking: bind the functor, then apply it to a package whose
    `l` import is the recursive wrapper. -/
def mrecExp (l : String) (A₁ A₂ : Typ) (e : Exp) : Exp :=
  .letb e
    (.mapp (.proj .query 0) (.lrec l (recWrap l A₁ A₂)))

-- The knot's context extensions demand disjointness on the sealTyp images: eletb's
-- context extension by the functor type, and eflam's double extension inside the
-- wrapper.  They are hypotheses of the mrec_* results (for closed programs the first
-- is free).

namespace Seal

variable {Δ : SCE.BrandStore}

/-- `mrecExp` elaborates to λE^≤ using only the existing rules, given the knot's
    disjointness obligations. -/
theorem source_mrec_elab
    {Γ B : SCE.Typ} {l : String} {A₁ A₂ : SCE.Typ} {e : SCE.Exp} {ce : Seal.Exp}
    (helab : elabSeal Δ Γ e (FunctorTy l A₁ A₂ B) ce)
    (hknot : SCE.SRLookup B l (.arr A₁ A₂))
    (hd₁ : Disj (sealTyp Γ) (sealTyp (FunctorTy l A₁ A₂ B)))
    (hd₂ : Disj (sealTyp (.and Γ (FunctorTy l A₁ A₂ B)))
      (.arr (sealTyp A₁) (sealTyp A₂)))
    (hd₃ : Disj (.and (sealTyp (.and Γ (FunctorTy l A₁ A₂ B)))
        (.arr (sealTyp A₁) (sealTyp A₂)))
      (sealTyp A₁))
    : ∃ ce', elabSeal Δ Γ (mrecExp l A₁ A₂ e) B ce' :=
  ⟨_, .eletb helab
    (.emapp
      (.eproj .equery (.zero _ _))
      (.elrec
        (.eflam
          (.eapp
            (.erproj
              (.emapp
                (.eproj .equery (.succ _ _ _ _ (.succ _ _ _ _ (.zero _ _))))
                (.elrec (.eproj .equery (.succ _ _ _ _ (.zero _ _)))))
              hknot)
            (.eproj .equery (.zero _ _)))
          hd₂ hd₃)))
    hd₁⟩

/-- A closed recursive module is a value or can step (progress). -/
theorem source_mrec_progress
    {B : SCE.Typ} {l : String} {A₁ A₂ : SCE.Typ} {e : SCE.Exp} {ce : Seal.Exp}
    (helab : elabSeal Δ .top e (FunctorTy l A₁ A₂ B) ce)
    (hknot : SCE.SRLookup B l (.arr A₁ A₂))
    (hd₂ : Disj (sealTyp (.and .top (FunctorTy l A₁ A₂ B)))
      (.arr (sealTyp A₁) (sealTyp A₂)))
    (hd₃ : Disj (.and (sealTyp (.and .top (FunctorTy l A₁ A₂ B)))
        (.arr (sealTyp A₁) (sealTyp A₂)))
      (sealTyp A₁))
    : SCE.Value (mrecExp l A₁ A₂ e)
      ∨ ∃ e', SStep .unit (mrecExp l A₁ A₂ e) e' :=
  source_sprogress (source_mrec_elab helab hknot disj_top hd₂ hd₃)

/-- Stepping a closed recursive module preserves its type (preservation). -/
theorem source_mrec_preservation
    {B : SCE.Typ} {l : String} {A₁ A₂ : SCE.Typ} {e e' : SCE.Exp} {ce : Seal.Exp}
    (helab : elabSeal Δ .top e (FunctorTy l A₁ A₂ B) ce)
    (hknot : SCE.SRLookup B l (.arr A₁ A₂))
    (hd₂ : Disj (sealTyp (.and .top (FunctorTy l A₁ A₂ B)))
      (.arr (sealTyp A₁) (sealTyp A₂)))
    (hd₃ : Disj (.and (sealTyp (.and .top (FunctorTy l A₁ A₂ B)))
        (.arr (sealTyp A₁) (sealTyp A₂)))
      (sealTyp A₁))
    (hstep : SStep .unit (mrecExp l A₁ A₂ e) e')
    : ∃ ce', elabSeal Δ .top e' B ce' :=
  source_spreservation (source_mrec_elab helab hknot disj_top hd₂ hd₃) hstep

/-- Evaluation of a recursive module is deterministic. -/
theorem source_mrec_deterministic
    {B : SCE.Typ} {l : String} {A₁ A₂ : SCE.Typ} {e v₁ v₂ : SCE.Exp} {ce : Seal.Exp}
    (helab : elabSeal Δ .top e (FunctorTy l A₁ A₂ B) ce)
    (hknot : SCE.SRLookup B l (.arr A₁ A₂))
    (hd₂ : Disj (sealTyp (.and .top (FunctorTy l A₁ A₂ B)))
      (.arr (sealTyp A₁) (sealTyp A₂)))
    (hd₃ : Disj (.and (sealTyp (.and .top (FunctorTy l A₁ A₂ B)))
        (.arr (sealTyp A₁) (sealTyp A₂)))
      (sealTyp A₁))
    (h₁ : BStep .unit (mrecExp l A₁ A₂ e) v₁)
    (h₂ : BStep .unit (mrecExp l A₁ A₂ e) v₂)
    : v₁ = v₂ :=
  source_bigstep_deterministic (source_mrec_elab helab hknot disj_top hd₂ hd₃) h₁ h₂

/-- The elaboration of a recursive module is well-typed λE^≤ code. -/
theorem source_mrec_seal_typed
    {Γ B : SCE.Typ} {l : String} {A₁ A₂ : SCE.Typ} {e : SCE.Exp} {ce : Seal.Exp}
    (helab : elabSeal Δ Γ e (FunctorTy l A₁ A₂ B) ce)
    (hknot : SCE.SRLookup B l (.arr A₁ A₂))
    (hd₁ : Disj (sealTyp Γ) (sealTyp (FunctorTy l A₁ A₂ B)))
    (hd₂ : Disj (sealTyp (.and Γ (FunctorTy l A₁ A₂ B)))
      (.arr (sealTyp A₁) (sealTyp A₂)))
    (hd₃ : Disj (.and (sealTyp (.and Γ (FunctorTy l A₁ A₂ B)))
        (.arr (sealTyp A₁) (sealTyp A₂)))
      (sealTyp A₁))
    : ∃ ce', elabSeal Δ Γ (mrecExp l A₁ A₂ e) B ce'
             ∧ HasType (sealStore Δ) (sealTyp Γ) ce' (sealTyp B) := by
  obtain ⟨ce', h⟩ := source_mrec_elab helab hknot hd₁ hd₂ hd₃
  exact ⟨ce', h, seal_type_preservation h⟩

/-- Whole-program correctness: if a closed recursive module evaluates to a source
    value, its λE^≤ elaboration evaluates to an EVal-related value. -/
theorem source_mrec_correctness
    {B : SCE.Typ} {l : String} {A₁ A₂ : SCE.Typ} {e vs : SCE.Exp} {ce : Seal.Exp}
    (helab : elabSeal Δ .top e (FunctorTy l A₁ A₂ B) ce)
    (hknot : SCE.SRLookup B l (.arr A₁ A₂))
    (hd₂ : Disj (sealTyp (.and .top (FunctorTy l A₁ A₂ B)))
      (.arr (sealTyp A₁) (sealTyp A₂)))
    (hd₃ : Disj (.and (sealTyp (.and .top (FunctorTy l A₁ A₂ B)))
        (.arr (sealTyp A₁) (sealTyp A₂)))
      (sealTyp A₁))
    (heval : BStep .unit (mrecExp l A₁ A₂ e) vs)
    : ∃ ce' vc, elabSeal Δ .top (mrecExp l A₁ A₂ e) B ce'
                ∧ MStep .unit ce' vc
                ∧ EVal Δ B vs vc := by
  obtain ⟨ce', h⟩ := source_mrec_elab helab hknot disj_top hd₂ hd₃
  obtain ⟨vc, hbig, hv⟩ := seal_whole_program_correctness h heval
  exact ⟨ce', vc, h, hbig, hv⟩

end Seal

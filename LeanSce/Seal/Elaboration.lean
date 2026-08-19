import LeanSce.SCE.Syntax
import LeanSce.Seal.CastingLemmas

-- Type-preserving elaboration of λSCE's module/linking fragment into λE^≤.
--
-- Scope: everything except unions (inl/inr/case), fix (flam/fclos), and iso-recursive
-- types (fold/unfold) — those require casting rules that exist in neither source paper
-- (see DESIGN.md).  `sealTyp` maps the unsupported type formers to ε as inert junk; no
-- elaboration rule produces an expression whose behavior depends on them.
--
-- Two things change relative to the SCE→Core elaboration (SCE/Elaboration.lean):
--
-- 1. Every rule that extends a context — merges, lambdas, closures, links — now carries
--    the disjointness premises λE^≤'s type system demands (Disj on the sealTyp images).
--    This is the obligation predicted by DESIGN.md (c): the source type system must
--    check disjointness or elaborated merges will not type.
--
-- 2. The bind-once combinators are gone.  Core's `nmrgCore`/`linkedCore` use the
--    self-application idiom (λ⟦Γ⟧. …) ? to evaluate both operands under the ambient
--    environment; that pattern is UNTYPEABLE in λE^≤, because tlam demands Disj Γ Γ,
--    which fails for any non-top-like Γ.  Sealing itself replaces the trick: (? : Γ)
--    restricts the extended environment back to the ambient one, so the non-capturing
--    merge is simply  mrg e₁ (box (? : Γ) e₂).  The construct that motivated λE's
--    combinator machinery is a one-liner once restriction is a first-class operation.
namespace Seal

variable {Δ : BrandStore}

mutual
@[simp]
def sealTyp : SCE.Typ → Seal.Typ
  | .int       => .int
  | .top       => .top
  | .arr A B   => .arr (sealTyp A) (sealTyp B)
  | .and A B   => .and (sealTyp A) (sealTyp B)
  | .or _ _    => .top
  | .rcd l A   => .rcd l (sealTyp A)
  | .sig mt    => sealModTyp mt
  | .var _     => .top
  | .mu _      => .top

@[simp]
def sealModTyp : SCE.ModTyp → Seal.Typ
  | .TyIntf T     => sealTyp T
  | .TyArrM T mt  => .arr (sealTyp T) (sealModTyp mt)
end

-- ── Transport of the lookup judgments along sealTyp ──────────────────────────────────

theorem slookup_seal {A : SCE.Typ} {n : Nat} {B : SCE.Typ} (h : SCE.SLookup A n B)
    : Seal.Lookup (sealTyp A) n (sealTyp B) := by
  induction h with
  | zero A B => exact Lookup.zero
  | succ A B n C _ ih => exact Lookup.succ ih

-- A label present in the image was present in the source (the direction the negative
-- containment premises need).
mutual
theorem lin_seal : {B : SCE.Typ} → {l : String} → Seal.Lin l (sealTyp B) → SCE.LabelIn l B
  | .rcd _ _, _, .rcd => SCE.LabelIn.rcd _ _
  | .and _ _, _, .andl h => SCE.LabelIn.andl _ _ _ (lin_seal h)
  | .and _ _, _, .andr h => SCE.LabelIn.andr _ _ _ (lin_seal h)
  | .sig _, _, h => lin_modtyp_seal h

theorem lin_modtyp_seal : {mt : SCE.ModTyp} → {l : String} → Seal.Lin l (sealModTyp mt)
    → SCE.LabelIn l (.sig mt)
  | .TyIntf _, _, h => SCE.LabelIn.sig _ _ (lin_seal h)
end

theorem srlookup_seal {B : SCE.Typ} {l : String} {A : SCE.Typ} (h : SCE.SRLookup B l A)
    : Seal.RLookup (sealTyp B) l (sealTyp A) := by
  induction h with
  | zero l T => exact RLookup.zero
  | andl A B l T _ hnl ih =>
    exact RLookup.landl ih (fun hlin => hnl (lin_seal hlin))
  | andr A B l T _ hnl ih =>
    exact RLookup.landr ih (fun hlin => hnl (lin_seal hlin))
  | sig l T A _ ih => exact ih

-- ── Seal-side link plumbing ──────────────────────────────────────────────────────────

-- Import package for an n-ary link: one record per labeled import, later components
-- evaluated under the ambient environment restored by sealing.
def wireArgSeal (ctx : Seal.Typ) (ce₁ : Seal.Exp) : SCE.Typ → Seal.Exp
  | .rcd l _ => .lrec l (.rproj ce₁ l)
  | .and D (.rcd l _) =>
    .mrg (wireArgSeal ctx ce₁ D) (.box (.anno .query ctx) (.lrec l (.rproj ce₁ l)))
  | _ => .unit

-- Well-formedness of an import interface for linking against a module of type Γ₁ in
-- ambient context Γ: every import is present in the module, and the accumulated package
-- is disjoint enough to merge.  This is the disjointness-enriched LinkOk that λE^≤
-- requires (SCE's LinkOk carries only the lookups).
inductive WireOk (Γ : Seal.Typ) (Γ₁ : SCE.Typ) : SCE.Typ → Prop where
  | one {l : String} {A : SCE.Typ}
    : SCE.SRLookup Γ₁ l A
    → WireOk Γ Γ₁ (.rcd l A)
  | more {D : SCE.Typ} {l : String} {A : SCE.Typ}
    : WireOk Γ Γ₁ D
    → SCE.SRLookup Γ₁ l A
    → Seal.Disj (sealTyp D) Γ
    → Seal.Disj (sealTyp D) (.rcd l (sealTyp A))
    → WireOk Γ Γ₁ (.and D (.rcd l A))

-- The package inhabits the import interface.
theorem wireArgSeal_typed {Γ : Seal.Typ} {Γ₁ : SCE.Typ} {ce₁ : Seal.Exp} {D : SCE.Typ}
    (hw : WireOk Γ Γ₁ D) (ht₁ : Seal.HasType Δ Γ ce₁ (sealTyp Γ₁))
    : Seal.HasType Δ Γ (wireArgSeal Γ ce₁ D) (sealTyp D) := by
  induction hw with
  | one hl => exact HasType.trcd (HasType.trproj ht₁ (srlookup_seal hl))
  | more _ hl hd₁ hd₂ ih =>
    exact HasType.tmrg ih
      (HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _)))
        (HasType.trcd (HasType.trproj ht₁ (srlookup_seal hl))))
      hd₁ hd₂

-- ── The elaboration relation ─────────────────────────────────────────────────────────

inductive elabSeal : SCE.Typ → SCE.Exp → SCE.Typ → Seal.Exp → Prop where
  | equery {ctx}
    : elabSeal ctx .query ctx .query
  | elit (ctx : SCE.Typ) (n : Nat)
    : elabSeal ctx (.lit n) .int (.lit n)
  | eunit (ctx : SCE.Typ)
    : elabSeal ctx .unit .top .unit
  | eapp {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal ctx se₁ (.arr A B) ce₁
    → elabSeal ctx se₂ A ce₂
    → elabSeal ctx (.app se₁ se₂) B (.app ce₁ ce₂)
  | eproj {ctx A B : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp} {i : Nat}
    : elabSeal ctx se A ce
    → SCE.SLookup A i B
    → elabSeal ctx (.proj se i) B (.proj ce i)
  | ebox {ctx ctx' A : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal ctx se₁ ctx' ce₁
    → elabSeal ctx' se₂ A ce₂
    → elabSeal ctx (.box se₁ se₂) A (.box ce₁ ce₂)
  -- dependent merge: now carries λE^≤'s two disjointness side conditions
  | edmrg {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal ctx se₁ A ce₁
    → elabSeal (.and ctx A) se₂ B ce₂
    → Seal.Disj (sealTyp A) (sealTyp ctx)
    → Seal.Disj (sealTyp A) (sealTyp B)
    → elabSeal ctx (.mrg se₁ se₂) (.and A B) (.mrg ce₁ ce₂)
  -- value merges elaborate context-freely (the elaboration-level mirror of tmergev;
  -- needed so value elaborations stay context-irrelevant, since edmrg's Disj A Γ premise
  -- is context-sensitive)
  | evmrg {ctx A B : SCE.Typ} {v₁ v₂ : SCE.Exp} {w₁ w₂ : Seal.Exp}
    : SCE.Value v₁
    → SCE.Value v₂
    → elabSeal .top v₁ A w₁
    → elabSeal .top v₂ B w₂
    → Seal.Disj (sealTyp A) (sealTyp B)
    → elabSeal ctx (.mrg v₁ v₂) (.and A B) (.mrg w₁ w₂)
  -- non-capturing merge: the bind-once combinator is replaced by sealing the extended
  -- environment back to the ambient context
  | enmrg {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal ctx se₁ A ce₁
    → elabSeal ctx se₂ B ce₂
    → Seal.Disj (sealTyp A) (sealTyp ctx)
    → Seal.Disj (sealTyp A) (sealTyp B)
    → elabSeal ctx (.nmrg se₁ se₂) (.and A B)
        (.mrg ce₁ (.box (.anno .query (sealTyp ctx)) ce₂))
  -- λE^≤ lambdas carry the codomain, which elaboration already infers
  | elam {ctx A B : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp}
    : elabSeal (.and ctx A) se B ce
    → Seal.Disj (sealTyp ctx) (sealTyp A)
    → elabSeal ctx (.lam A se) (.arr A B) (.lam (sealTyp A) (sealTyp B) ce)
  | erproj {ctx A B : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp} {l : String}
    : elabSeal ctx se B ce
    → SCE.SRLookup B l A
    → elabSeal ctx (.rproj se l) A (.rproj ce l)
  | eclos {ctx ctx' A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : SCE.Value se₁
    → elabSeal .top se₁ ctx' ce₁
    → elabSeal (.and ctx' A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx') (sealTyp A)
    → elabSeal ctx (.clos se₁ A se₂) (.arr A B)
        (.clos ce₁ (sealTyp A) (sealTyp B) ce₂)
  | elrec {ctx A : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp} {l : String}
    : elabSeal ctx se A ce
    → elabSeal ctx (.lrec l se) (.rcd l A) (.lrec l ce)
  | eletb {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal ctx se₁ A ce₁
    → elabSeal (.and ctx A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx) (sealTyp A)
    → elabSeal ctx (.letb se₁ A se₂) B
        (.app (.lam (sealTyp A) (sealTyp B) ce₂) ce₁)
  | eopenm {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp} {l : String}
    : elabSeal ctx se₁ (.rcd l A) ce₁
    → elabSeal (.and ctx A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx) (sealTyp A)
    → elabSeal ctx (.openm se₁ se₂) B
        (.app (.lam (sealTyp A) (sealTyp B) ce₂) (.rproj ce₁ l))
  | emstruct {ctx ctxInner B : SCE.Typ} {sb : SCE.Sandbox} {se : SCE.Exp} {ce : Seal.Exp}
    : (sb = .sandboxed → ctxInner = .top)
    → (sb = .open_ → ctxInner = ctx)
    → elabSeal ctxInner se B ce
    → elabSeal ctx (.mstruct sb se) B
        (.box (match sb with | .sandboxed => .unit | .open_ => .query) ce)
  | emfunctor {ctx ctxInner A B : SCE.Typ} {sb : SCE.Sandbox} {se : SCE.Exp} {ce : Seal.Exp}
    : (sb = .sandboxed → ctxInner = .and .top A)
    → (sb = .open_ → ctxInner = .and ctx A)
    → (sb = .open_ → Seal.Disj (sealTyp ctx) (sealTyp A))
    → elabSeal ctxInner se B ce
    → elabSeal ctx (.mfunctor sb A se) (.sig (.TyArrM A (.TyIntf B)))
        (match sb with
          | .sandboxed => .box .unit (.lam (sealTyp A) (sealTyp B) ce)
          | .open_ => .lam (sealTyp A) (sealTyp B) ce)
  | emclos {ctx ctx' A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : SCE.Value se₁
    → elabSeal .top se₁ ctx' ce₁
    → elabSeal (.and ctx' A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx') (sealTyp A)
    → elabSeal ctx (.mclos se₁ A se₂) (.sig (.TyArrM A (.TyIntf B)))
        (.clos ce₁ (sealTyp A) (sealTyp B) ce₂)
  | emapp {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal ctx se₁ (.sig (.TyArrM A (.TyIntf B))) ce₁
    → elabSeal ctx se₂ A ce₂
    → elabSeal ctx (.mapp se₁ se₂) B (.app ce₁ ce₂)
  -- linking: the module's exports feed the functor's labeled import; both operands are
  -- evaluated under the ambient environment, restored by sealing
  | emlink {ctx Γ₁ A B : SCE.Typ} {l : String} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal ctx se₁ Γ₁ ce₁
    → elabSeal ctx se₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ce₂
    → SCE.SRLookup Γ₁ l A
    → Seal.Disj (sealTyp Γ₁) (sealTyp ctx)
    → Seal.Disj (sealTyp Γ₁) (sealTyp B)
    → elabSeal ctx (.mlink se₁ se₂) (.and Γ₁ B)
        (.mrg ce₁ (.box (.anno .query (sealTyp ctx))
          (.app ce₂ (.lrec l (.rproj ce₁ l)))))
  -- n-ary linking, with the disjointness-enriched interface well-formedness
  | emlinkn {ctx Γ₁ D B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal ctx se₁ Γ₁ ce₁
    → elabSeal ctx se₂ (.sig (.TyArrM D (.TyIntf B))) ce₂
    → WireOk (sealTyp ctx) Γ₁ D
    → Seal.Disj (sealTyp Γ₁) (sealTyp ctx)
    → Seal.Disj (sealTyp Γ₁) (sealTyp B)
    → elabSeal ctx (.mlinkn se₁ se₂) (.and Γ₁ B)
        (.mrg ce₁ (.box (.anno .query (sealTyp ctx))
          (.app ce₂ (wireArgSeal (sealTyp ctx) ce₁ D))))

-- ── Elaboration maps source values to target values ──────────────────────────────────

theorem elabSeal_value {Γ : SCE.Typ} {es : SCE.Exp} {A : SCE.Typ} {ce : Seal.Exp}
    (h : elabSeal Γ es A ce) (hv : SCE.Value es) : Seal.Value ce := by
  induction h with
  | elit _ _ => exact Value.vint
  | eunit _ => exact Value.vunit
  | eclos _ _ _ _ ih₁ _ =>
    cases hv with
    | vclos hv₁ => exact Value.vclos (ih₁ hv₁)
  | emclos _ _ _ _ ih₁ _ =>
    cases hv with
    | vmclos hv₁ => exact Value.vclos (ih₁ hv₁)
  | edmrg _ _ _ _ ih₁ ih₂ =>
    cases hv with
    | vmrg hv₁ hv₂ => exact Value.vmrg (ih₁ hv₁) (ih₂ hv₂)
  | evmrg hv₁ hv₂ _ _ _ ih₁ ih₂ => exact Value.vmrg (ih₁ hv₁) (ih₂ hv₂)
  | elrec _ ih =>
    cases hv with
    | vlrec hv' => exact Value.vrcd (ih hv')
  | equery => nomatch hv
  | eapp _ _ _ _ => nomatch hv
  | eproj _ _ _ => nomatch hv
  | ebox _ _ _ _ => nomatch hv
  | enmrg _ _ _ _ _ _ => nomatch hv
  | elam _ _ _ => nomatch hv
  | erproj _ _ _ => nomatch hv
  | eletb _ _ _ _ _ => nomatch hv
  | eopenm _ _ _ _ _ => nomatch hv
  | emstruct _ _ _ _ => nomatch hv
  | emfunctor _ _ _ _ _ => nomatch hv
  | emapp _ _ _ _ => nomatch hv
  | emlink _ _ _ _ _ _ _ => nomatch hv
  | emlinkn _ _ _ _ _ _ _ => nomatch hv

-- ── Type preservation: elaborated code is well-typed λE^≤ ────────────────────────────

theorem seal_type_preservation {Γ : SCE.Typ} {es : SCE.Exp} {A : SCE.Typ} {ce : Seal.Exp}
    (h : elabSeal Γ es A ce)
    : Seal.HasType Δ (sealTyp Γ) ce (sealTyp A) := by
  induction h with
  | equery => exact HasType.tquery
  | elit _ _ => exact HasType.tint
  | eunit _ => exact HasType.tunit
  | eapp _ _ ih₁ ih₂ => exact HasType.tapp ih₁ ih₂
  | eproj _ hl ih => exact HasType.tproj ih (slookup_seal hl)
  | ebox _ _ ih₁ ih₂ => exact HasType.tbox ih₁ ih₂
  | edmrg _ _ hd₁ hd₂ ih₁ ih₂ => exact HasType.tmrg ih₁ ih₂ hd₁ hd₂
  | evmrg hv₁ hv₂ h₁ h₂ hd ih₁ ih₂ =>
    exact HasType.tmergev (elabSeal_value h₁ hv₁) (elabSeal_value h₂ hv₂) ih₁ ih₂
      (disjoint_consistent (elabSeal_value h₁ hv₁) (elabSeal_value h₂ hv₂) ih₁ ih₂ hd)
  | enmrg _ _ hd₁ hd₂ ih₁ ih₂ =>
    exact HasType.tmrg ih₁
      (HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _))) ih₂)
      hd₁ hd₂
  | elam _ hd ih => exact HasType.tlam hd ih
  | erproj _ hl ih => exact HasType.trproj ih (srlookup_seal hl)
  | eclos hv _ _ hd ih₁ ih₂ =>
    exact HasType.tclos (elabSeal_value (by assumption) hv) ih₁ hd ih₂
      (sub_refl _) (sub_refl _)
  | elrec _ ih => exact HasType.trcd ih
  | eletb _ _ hd ih₁ ih₂ => exact HasType.tapp (HasType.tlam hd ih₂) ih₁
  | eopenm _ _ hd ih₁ ih₂ =>
    exact HasType.tapp (HasType.tlam hd ih₂)
      (HasType.trproj ih₁ RLookup.zero)
  | @emstruct ctx ctxInner B sb se ce hsb hop _ ih =>
    cases sb with
    | sandboxed =>
      rw [hsb rfl] at ih
      exact HasType.tbox HasType.tunit ih
    | open_ =>
      rw [hop rfl] at ih
      exact HasType.tbox HasType.tquery ih
  | @emfunctor ctx ctxInner A B sb se ce hsb hop hdop _ ih =>
    cases sb with
    | sandboxed =>
      rw [hsb rfl] at ih
      exact HasType.tbox HasType.tunit (HasType.tlam disj_top ih)
    | open_ =>
      rw [hop rfl] at ih
      exact HasType.tlam (hdop rfl) ih
  | emclos hv _ _ hd ih₁ ih₂ =>
    exact HasType.tclos (elabSeal_value (by assumption) hv) ih₁ hd ih₂
      (sub_refl _) (sub_refl _)
  | emapp _ _ ih₁ ih₂ => exact HasType.tapp ih₁ ih₂
  | emlink _ _ hl hd₁ hd₂ ih₁ ih₂ =>
    exact HasType.tmrg ih₁
      (HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _)))
        (HasType.tapp ih₂ (HasType.trcd (HasType.trproj ih₁ (srlookup_seal hl)))))
      hd₁ hd₂
  | emlinkn _ _ hw hd₁ hd₂ ih₁ ih₂ =>
    exact HasType.tmrg ih₁
      (HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _)))
        (HasType.tapp ih₂ (wireArgSeal_typed hw ih₁)))
      hd₁ hd₂

end Seal

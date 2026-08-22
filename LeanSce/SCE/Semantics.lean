import LeanSce.SCE.Syntax

open SCE

namespace S_Sem

inductive LookupV : Exp → Nat → Exp → Prop where
  | dmrg_zero {v₁ v₂ : Exp}
    : LookupV (.mrg v₁ v₂) 0 v₂
  | dmrg_succ {v₁ v₂ v' : Exp} {n : Nat}
    : LookupV v₁ n v'
    → LookupV (.mrg v₁ v₂) (n + 1) v'
  | nmrg_zero {v₁ v₂ : Exp}
    : LookupV (.nmrg v₁ v₂) 0 v₂
  | nmrg_succ {v₁ v₂ v' : Exp} {n : Nat}
    : LookupV v₁ n v'
    → LookupV (.nmrg v₁ v₂) (n + 1) v'

inductive Sel : Exp → String → Exp → Prop where
  | rcd {l : String} {v : Exp}
    : Sel (.lrec l v) l v
  | dmrg_left {v₁ v₂ v' : Exp} {l : String}
    : Sel v₁ l v'
    → Sel (.mrg v₁ v₂) l v'
  | dmrg_right {v₁ v₂ v' : Exp} {l : String}
    : Sel v₂ l v'
    → Sel (.mrg v₁ v₂) l v'
  | nmrg_left {v₁ v₂ v' : Exp} {l : String}
    : Sel v₁ l v'
    → Sel (.nmrg v₁ v₂) l v'
  | nmrg_right {v₁ v₂ v' : Exp} {l : String}
    : Sel v₂ l v'
    → Sel (.nmrg v₁ v₂) l v'

-- SelPkg v D pkg: extract from the module value v the record package pkg
-- shaped after the import interface D (one Sel per labeled import)
inductive SelPkg : Exp → Typ → Exp → Prop where
  | one {v : Exp} {l : String} {A : Typ} {vl : Exp}
    : Sel v l vl
    → SelPkg v (.rcd l A) (.lrec l vl)
  | more {v : Exp} {D : Typ} {pkg : Exp} {l : String} {A : Typ} {vl : Exp}
    : SelPkg v D pkg
    → Sel v l vl
    → SelPkg v (.and D (.rcd l A)) (.mrg pkg (.lrec l vl))

theorem sel_value {v v' : Exp} {l : String}
    (hsel : Sel v l v') (hv : Value v) : Value v' := by
  induction hsel with
  | rcd => cases hv; assumption
  | dmrg_left _ ih => cases hv with | vmrg h1 h2 => exact ih h1
  | dmrg_right _ ih => cases hv with | vmrg h1 h2 => exact ih h2
  | nmrg_left _ ih => cases hv
  | nmrg_right _ ih => cases hv

theorem selpkg_value {v : Exp} {D : Typ} {pkg : Exp}
    (hsp : SelPkg v D pkg) (hv : Value v) : Value pkg := by
  induction hsp with
  | one hsel => exact Value.vlrec (sel_value hsel hv)
  | more _ hsel ih => exact Value.vmrg ih (Value.vlrec (sel_value hsel hv))

-- Source-level sealing coercions, mirroring Seal.SealV/UnsealV (Seal/DESIGN.md §(g)):
-- structural on the signature; wrap/unwrap at brand n, identity at other leaves,
-- componentwise on merges/records, a proxy closure at arrows.  The source has no casts,
-- so the proxy is a plain SCE closure; its shape is chosen to elaborate exactly to the
-- target proxy.
def proxyEnv (c : Exp) : Exp := .mrg .unit (.lrec "#f" c)
def proxyFun : Exp := .rproj (.proj .query 1) "#f"

inductive SSealV (n : Nat) (R : Typ) : Typ → Exp → Exp → Prop where
  | brand_eq {v} : SSealV n R (.brand n) v (.wrap n v)
  | brand_ne {m v} : m ≠ n → SSealV n R (.brand m) v v
  | int {i} : SSealV n R .int (.lit i) (.lit i)
  | top {v} : SSealV n R .top v .unit
  | and {A B v₁ v₂ w₁ w₂}
    : SSealV n R A v₁ w₁ → SSealV n R B v₂ w₂
    → SSealV n R (.and A B) (.mrg v₁ v₂) (.mrg w₁ w₂)
  | rcd {l A v w} : SSealV n R A v w → SSealV n R (.rcd l A) (.lrec l v) (.lrec l w)
  | arr {A B c}
    : SSealV n R (.arr A B) c
        (.clos (proxyEnv c) A (.mseal n R B (.app proxyFun (.munseal n R A (.proj .query 0)))))
  -- functor signatures: the same proxy pattern with the module forms (an mclos proxy,
  -- applied with mapp) — sealTyp maps both to the target arrow proxy
  | sig {A B : Typ} {c}
    : SSealV n R (.sig (.TyArrM A (.TyIntf B))) c
        (.mclos (proxyEnv c) A
          (.mseal n R B (.mapp proxyFun (.munseal n R A (.proj .query 0)))))
  -- unions coerce under the tag; μ (and stray variables) are opaque to sealing
  | inl {A B v w}
    : SSealV n R A v w → SSealV n R (.or A B) (.inl (substBrand n R B) v) (.inl B w)
  | inr {A B v w}
    : SSealV n R B v w → SSealV n R (.or A B) (.inr (substBrand n R A) v) (.inr A w)
  | var {m v} : SSealV n R (.var m) v v
  | mu {T v} : SSealV n R (.mu T) v v

inductive SUnsealV (n : Nat) (R : Typ) : Typ → Exp → Exp → Prop where
  | brand_eq {v} : SUnsealV n R (.brand n) (.wrap n v) v
  | brand_ne {m v} : m ≠ n → SUnsealV n R (.brand m) v v
  | int {i} : SUnsealV n R .int (.lit i) (.lit i)
  | top {v} : SUnsealV n R .top v .unit
  | and {A B v₁ v₂ w₁ w₂}
    : SUnsealV n R A v₁ w₁ → SUnsealV n R B v₂ w₂
    → SUnsealV n R (.and A B) (.mrg v₁ v₂) (.mrg w₁ w₂)
  | rcd {l A v w} : SUnsealV n R A v w → SUnsealV n R (.rcd l A) (.lrec l v) (.lrec l w)
  | arr {A B c}
    : SUnsealV n R (.arr A B) c
        (.clos (proxyEnv c) (substBrand n R A)
          (.munseal n R B (.app proxyFun (.mseal n R A (.proj .query 0)))))
  | sig {A B : Typ} {c}
    : SUnsealV n R (.sig (.TyArrM A (.TyIntf B))) c
        (.mclos (proxyEnv c) (substBrand n R A)
          (.munseal n R B (.mapp proxyFun (.mseal n R A (.proj .query 0)))))
  | inl {A B v w}
    : SUnsealV n R A v w → SUnsealV n R (.or A B) (.inl B v) (.inl (substBrand n R B) w)
  | inr {A B v w}
    : SUnsealV n R B v w → SUnsealV n R (.or A B) (.inr A v) (.inr (substBrand n R A) w)
  | var {m v} : SUnsealV n R (.var m) v v
  | mu {T v} : SUnsealV n R (.mu T) v v

theorem ssealv_value {n : Nat} {R S : Typ} {v w : Exp} (hv : Value v) (h : SSealV n R S v w)
    : Value w := by
  induction h with
  | brand_eq => exact Value.vwrap hv
  | brand_ne _ => exact hv
  | int => exact Value.vint
  | top => exact Value.vunit
  | and _ _ ih₁ ih₂ => cases hv with | vmrg h₁ h₂ => exact Value.vmrg (ih₁ h₁) (ih₂ h₂)
  | rcd _ ih => cases hv with | vlrec h' => exact Value.vlrec (ih h')
  | arr => exact Value.vclos (Value.vmrg Value.vunit (Value.vlrec hv))
  | sig => exact Value.vmclos (Value.vmrg Value.vunit (Value.vlrec hv))
  | inl _ ih => cases hv with | vinl h' => exact Value.vinl (ih h')
  | inr _ ih => cases hv with | vinr h' => exact Value.vinr (ih h')
  | var => exact hv
  | mu => exact hv

theorem sunsealv_value {n : Nat} {R S : Typ} {v w : Exp} (hv : Value v) (h : SUnsealV n R S v w)
    : Value w := by
  induction h with
  | brand_eq => cases hv with | vwrap h' => exact h'
  | brand_ne _ => exact hv
  | int => exact Value.vint
  | top => exact Value.vunit
  | and _ _ ih₁ ih₂ => cases hv with | vmrg h₁ h₂ => exact Value.vmrg (ih₁ h₁) (ih₂ h₂)
  | rcd _ ih => cases hv with | vlrec h' => exact Value.vlrec (ih h')
  | arr => exact Value.vclos (Value.vmrg Value.vunit (Value.vlrec hv))
  | sig => exact Value.vmclos (Value.vmrg Value.vunit (Value.vlrec hv))
  | inl _ ih => cases hv with | vinl h' => exact Value.vinl (ih h')
  | inr _ ih => cases hv with | vinr h' => exact Value.vinr (ih h')
  | var => exact hv
  | mu => exact hv

theorem ssealv_det {n : Nat} {R S : Typ} {v w₁ : Exp} (h₁ : SSealV n R S v w₁)
    : ∀ {w₂ : Exp}, SSealV n R S v w₂ → w₁ = w₂ := by
  induction h₁ with
  | brand_eq => intro _ h₂; cases h₂ with | brand_eq => rfl | brand_ne hne => exact absurd rfl hne
  | brand_ne hne => intro _ h₂; cases h₂ with | brand_eq => exact absurd rfl hne | brand_ne _ => rfl
  | int => intro _ h₂; cases h₂; rfl
  | top => intro _ h₂; cases h₂; rfl
  | and _ _ ih₁ ih₂ => intro _ h₂; cases h₂ with | and a b => rw [ih₁ a, ih₂ b]
  | rcd _ ih => intro _ h₂; cases h₂ with | rcd a => rw [ih a]
  | arr => intro _ h₂; cases h₂; rfl
  | sig => intro _ h₂; cases h₂; rfl
  | inl _ ih => intro _ h₂; cases h₂ with | inl a => rw [ih a]
  | inr _ ih => intro _ h₂; cases h₂ with | inr a => rw [ih a]
  | var => intro _ h₂; cases h₂; rfl
  | mu => intro _ h₂; cases h₂; rfl

theorem sunsealv_det {n : Nat} {R S : Typ} {v w₁ : Exp} (h₁ : SUnsealV n R S v w₁)
    : ∀ {w₂ : Exp}, SUnsealV n R S v w₂ → w₁ = w₂ := by
  induction h₁ with
  | brand_eq => intro _ h₂; cases h₂ with | brand_eq => rfl | brand_ne hne => exact absurd rfl hne
  | brand_ne hne => intro _ h₂; cases h₂ with | brand_eq => exact absurd rfl hne | brand_ne _ => rfl
  | int => intro _ h₂; cases h₂; rfl
  | top => intro _ h₂; cases h₂; rfl
  | and _ _ ih₁ ih₂ => intro _ h₂; cases h₂ with | and a b => rw [ih₁ a, ih₂ b]
  | rcd _ ih => intro _ h₂; cases h₂ with | rcd a => rw [ih a]
  | arr => intro _ h₂; cases h₂; rfl
  | sig => intro _ h₂; cases h₂; rfl
  | inl _ ih => intro _ h₂; cases h₂ with | inl a => rw [ih a]
  | inr _ ih => intro _ h₂; cases h₂ with | inr a => rw [ih a]
  | var => intro _ h₂; cases h₂; rfl
  | mu => intro _ h₂; cases h₂; rfl

inductive BStep : Exp → Exp → Exp → Prop where
  | query {ρ : Exp}
    : Value ρ
    → BStep ρ .query ρ
  | lit {ρ : Exp} {n : Nat}
    : Value ρ
    → BStep ρ (.lit n) (.lit n)
  | unit {ρ : Exp}
    : Value ρ
    → BStep ρ .unit .unit
  | clos_val {ρ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BStep ρ (.clos v A body) (.clos v A body)
  | mclos_val {ρ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BStep ρ (.mclos v A body) (.mclos v A body)
  | proj {ρ e v v' : Exp} {n : Nat}
    : Value ρ
    → BStep ρ e v
    → LookupV v n v'
    → BStep ρ (.proj e n) v'
  | lam {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.lam A body) (.clos ρ A body)
  | box {ρ e₁ e₂ v₁ v : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep v₁ e₂ v
    → BStep ρ (.box e₁ e₂) v
  | app_clos {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ (.clos v₁ A body)
    → BStep ρ e₂ v₂
    → BStep (.mrg v₁ v₂) body v
    → BStep ρ (.app e₁ e₂) v
  | app_mclos {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ (.mclos v₁ A body)
    → BStep ρ e₂ v₂
    → BStep (.mrg v₁ v₂) body v
    → BStep ρ (.mapp e₁ e₂) v
  | dmrg {ρ e₁ e₂ v₁ v₂ : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep (.mrg ρ v₁) e₂ v₂
    → BStep ρ (.mrg e₁ e₂) (.mrg v₁ v₂)
  | nmrg {ρ e₁ e₂ v₁ v₂ : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep ρ e₂ v₂
    → BStep ρ (.nmrg e₁ e₂) (.mrg v₁ v₂)
  | lrec {ρ e v : Exp} {l : String}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.lrec l e) (.lrec l v)
  | rproj {ρ e v v' : Exp} {l : String}
    : Value ρ
    → BStep ρ e v
    → Sel v l v'
    → BStep ρ (.rproj e l) v'
  | letb {ρ e₁ e₂ v₁ v : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep (.mrg ρ v₁) e₂ v
    → BStep ρ (.letb e₁ e₂) v
  | openm {ρ e₁ e₂ v' v : Exp} {l : String}
    : Value ρ
    → BStep ρ e₁ (.lrec l v')
    → BStep (.mrg ρ v') e₂ v
    → BStep ρ (.openm e₁ e₂) v
  | mstruct_sandboxed {ρ body v : Exp}
    : Value ρ
    → BStep .unit body v
    → BStep ρ (.mstruct .sandboxed body) v
  | mstruct_open {ρ body v : Exp}
    : Value ρ
    → BStep ρ body v
    → BStep ρ (.mstruct .open_ body) v
  | mfunctor_sandboxed {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.mfunctor .sandboxed A body) (.mclos .unit A body)
  | mfunctor_open {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.mfunctor .open_ A body) (.mclos ρ A body)
| mlink {ρ e₁ e₂ v₁ v₂ vₗ v₃ : Exp} {A : Typ} {body : Exp} {l : String}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep ρ e₂ (.mclos v₂ (.rcd l A) body)
    → Sel v₁ l vₗ
    → BStep (.mrg v₂ (.lrec l vₗ)) body v₃
    → BStep ρ (.mlink e₁ e₂) (.mrg v₁ v₃)
  | inl {ρ e v : Exp} {B : Typ}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.inl B e) (.inl B v)
  | inr {ρ e v : Exp} {A : Typ}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.inr A e) (.inr A v)
  | case_inl {ρ e e₁ e₂ v₁ v : Exp} {B : Typ}
    : Value ρ
    → BStep ρ e (.inl B v₁)
    → BStep (.mrg ρ v₁) e₁ v
    → BStep ρ (.case e e₁ e₂) v
  | case_inr {ρ e e₁ e₂ v₁ v : Exp} {A : Typ}
    : Value ρ
    → BStep ρ e (.inr A v₁)
    → BStep (.mrg ρ v₁) e₂ v
    → BStep ρ (.case e e₁ e₂) v
  | fclos_val {ρ v : Exp} {A B : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BStep ρ (.fclos v A B body) (.fclos v A B body)
  | flam {ρ : Exp} {A B : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.flam A B body) (.fclos ρ A B body)
  | app_fclos {ρ e₁ e₂ v₁ v₂ v : Exp} {A B : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ (.fclos v₁ A B body)
    → BStep ρ e₂ v₂
    → BStep (.mrg (.mrg v₁ (.fclos v₁ A B body)) v₂) body v
    → BStep ρ (.app e₁ e₂) v
  | fold {ρ e v : Exp} {T : Typ}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.fold T e) (.fold T v)
  | unfold {ρ e v : Exp} {T : Typ}
    : Value ρ
    → BStep ρ e (.fold T v)
    → BStep ρ (.unfold e) v
  | wrap {ρ e v : Exp} {n : Nat}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.wrap n e) (.wrap n v)
  | mseal {ρ e v w : Exp} {n : Nat} {R S : Typ}
    : Value ρ
    → BStep ρ e v
    → SSealV n R S v w
    → BStep ρ (.mseal n R S e) w
  | munseal {ρ e v w : Exp} {n : Nat} {R S : Typ}
    : Value ρ
    → BStep ρ e v
    → SUnsealV n R S v w
    → BStep ρ (.munseal n R S e) w
  | mlinkn {ρ e₁ e₂ v₁ v₂ pkg v₃ : Exp} {D : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep ρ e₂ (.mclos v₂ D body)
    → SelPkg v₁ D pkg
    → BStep (.mrg v₂ pkg) body v₃
    → BStep ρ (.mlinkn e₁ e₂) (.mrg v₁ v₃)
end S_Sem

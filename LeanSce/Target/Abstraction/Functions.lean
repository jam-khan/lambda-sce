import LeanSce.Target.Abstraction.Infrastructure
import LeanSce.Target.Abstraction.Substitution
import LeanSce.Target.LogicalRelation.Contexts
import LeanSce.Target.LogicalRelation.Evaluation
import LeanSce.Target.Metatheory.Basic

/-!
# Target / Abstraction / Functions

Proofs and supporting constructions for functions.
-/

/-! ## Heterogeneous Functions -/

namespace LeanSce.Target.Heterogeneous

theorem ValRel.unit : ValRel n .unit η .unit .unit := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨rfl,.unit .unit⟩,⟨rfl,.unit .unit⟩,rfl,rfl⟩

theorem ValRel.int : ValRel n .int η (.int z) (.int z) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨rfl,.int .unit⟩,⟨rfl,.int .unit⟩,z,rfl,rfl⟩

theorem ValRel.bool : ValRel n .bool η (.bool b) (.bool b) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨rfl,.bool .unit⟩,⟨rfl,.bool .unit⟩,b,rfl,rfl⟩

theorem ValRel.string : ValRel n .string η (.string s) (.string s) := by
  rw [ValRel,ShapeRel]
  exact ⟨⟨rfl,.string .unit⟩,⟨rfl,.string .unit⟩,s,rfl,rfl⟩

def BodyRel (η : Valuation) (h a : Typ) (e E : Expr) : Prop :=
  ∀ n ν N, ValRel n h η ν N → ExprRel n a η (ν,e) (N,E)

theorem ValRel.pair (hx : ValRel n a η x X) (hy : ValRel n b η y Y) :
    ValRel n (.prod a b) η (.pair x y) (.pair X Y) := by
  rw [ValRel] at hx hy ⊢
  refine ⟨⟨Bool.and_eq_true_iff.mpr ⟨hx.1.1,hy.1.1⟩,.pair hx.1.2 hy.1.2⟩,
    ⟨Bool.and_eq_true_iff.mpr ⟨hx.2.1.1,hy.2.1.1⟩,.pair hx.2.1.2 hy.2.1.2⟩,?_⟩
  rw [ShapeRel]
  exact ⟨x,y,X,Y,rfl,rfl,by rw [ValRel];exact hx,by rw [ValRel];exact hy⟩

theorem ExprRel.query (hr : ValRel n h η ν N) : ExprRel n h η (ν,.query) (N,.query) := by
  cases n with
  | zero => exact ExprRel.zero
  | succ n =>
    exact ExprRel.step (query_step hr.left.1) (query_step hr.right.1)
      ((hr.mono (by omega)).toExpr)

theorem ExprRel.box_value (hb : ExprRel n a η (env,body) (Env,Body))
    (hν : Value ν) (hN : Value N) (he : Value env) (hE : Value Env) :
    ExprRel (n+1) a η (ν,.box env body) (N,.box Env Body) := by
  rw [ExprRel] at hb ⊢
  constructor
  · intro k hk v hv
    obtain ⟨j,hj,ht⟩ := hv.box_inv hν he
    obtain ⟨w,hw,hr⟩ := hb.1 j (by omega) v ht
    exact ⟨w,hw.box hN hE,by simpa [hj] using hr⟩
  · intro k hk w hw
    obtain ⟨j,hj,ht⟩ := hw.box_inv hN hE
    obtain ⟨v,hv,hr⟩ := hb.2 j (by omega) w ht
    exact ⟨v,hv.box hν he,by simpa [hj] using hr⟩

theorem ValRel.app (hf : ValRel n (.arr a b) η f F) (hx : ValRel n a η x X)
    (hν : Value ν) (hN : Value N) : ExprRel n b η (ν,.app f x) (N,.app F X) := by
  have hvf : Value f := by rw [ValRel] at hf; exact hf.1.1
  have hvF : Value F := by rw [ValRel] at hf; exact hf.2.1.1
  have hvx : Value x := by rw [ValRel] at hx; exact hx.1.1
  have hvX : Value X := by rw [ValRel] at hx; exact hx.2.1.1
  have hs : ShapeRel n (.arr a b) η f F := by rw [ValRel] at hf;exact hf.2.2
  rw [ShapeRel] at hs
  cases n with
  | zero => exact ExprRel.zero
  | succ m =>
    cases m with
    | zero =>
      obtain ⟨q,r,hq,hr,hbody⟩ := hs 0 (by omega) x X (hx.mono (by omega))
      exact ExprRel.step (hq.step hν hvf hvx) (hr.step hN hvF hvX) ExprRel.zero
    | succ j =>
      obtain ⟨q,r,hq,hr,hbody⟩ := hs j (by omega) x X (hx.mono (by omega))
      exact ExprRel.step (hq.step hν hvf hvx) (hr.step hN hvF hvX)
        (hbody.box_value hν hN (hq.env_value hvf hvx) (hr.env_value hvF hvX))

theorem ExprRel.app (hf : ExprRel n (.arr a b) η (ν,f) (N,F))
    (hx : ExprRel n a η (ν,x) (N,X)) (hν : Value ν) (hN : Value N) :
    ExprRel n b η (ν,.app f x) (N,.app F X) := by
  apply hf.bind strict_app_left strict_app_left
  intro i hi v V hv
  have htv : Value v := by rw [ValRel] at hv; exact hv.1.1
  have htV : Value V := by rw [ValRel] at hv; exact hv.2.1.1
  apply (hx.mono (Nat.sub_le _ _)).bind (strict_app_right htv) (strict_app_right htV)
  intro j hj w W hw
  exact (hv.mono (Nat.sub_le _ _)).app hw hν hN

theorem ValRel.clo (wa : WellFormed .empty (a.subst η.left)) (wA : WellFormed .empty (a.subst η.right))
    (hb : HasType .empty ((Ty.prod h a).subst η.left) body (b.subst η.left)) (hB : HasType .empty ((Ty.prod h a).subst η.right) Body (b.subst η.right))
    (hr : BodyRel η (.prod h a) b body Body) (hc : ValRel n h η cap Cap) :
    ValRel n (.arr a b) η (.clo cap (a.subst η.left) body) (.clo Cap (a.subst η.right) Body) := by
  have hcap : ValueType .empty cap (h.subst η.left) := by rw [ValRel] at hc; exact hc.1
  have hCap : ValueType .empty Cap (h.subst η.right) := by rw [ValRel] at hc; exact hc.2.1
  rw [ValRel]
  refine ⟨⟨hcap.1,.clo .unit wa hcap.1 hcap.2 hb⟩,
    ⟨hCap.1,.clo .unit wA hCap.1 hCap.2 hB⟩,?_⟩
  rw [ShapeRel]
  intro j hj x X hx
  exact ⟨_,_,.clo,.clo,hr j _ _ (ValRel.pair (hc.mono (Nat.le_of_lt hj)) hx)⟩

theorem ValRel.rclo (wa : WellFormed .empty (a.subst η.left)) (wA : WellFormed .empty (a.subst η.right)) (wb : WellFormed .empty (b.subst η.left)) (wB : WellFormed .empty (b.subst η.right))
    (hb : HasType .empty ((Ty.prod (.prod h (.arr a b)) a).subst η.left) body (b.subst η.left))
    (hB : HasType .empty ((Ty.prod (.prod h (.arr a b)) a).subst η.right) Body (b.subst η.right))
    (hr : BodyRel η (.prod (.prod h (.arr a b)) a) b body Body)
    (hc : ValRel n h η cap Cap) :
    ValRel n (.arr a b) η (.rclo cap (a.subst η.left) (b.subst η.left) body) (.rclo Cap (a.subst η.right) (b.subst η.right) Body) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hcap : ValueType .empty cap (h.subst η.left) := by rw [ValRel] at hc; exact hc.1
    have hCap : ValueType .empty Cap (h.subst η.right) := by rw [ValRel] at hc; exact hc.2.1
    rw [ValRel]
    refine ⟨⟨hcap.1,.rclo .unit wa wb hcap.1 hcap.2 hb⟩,
      ⟨hCap.1,.rclo .unit wA wB hCap.1 hCap.2 hB⟩,?_⟩
    rw [ShapeRel]
    intro j hj x X hx
    have hcs := hc.mono (Nat.le_of_lt hj)
    have hself := ih j hj hcs
    exact ⟨_,_,.rclo,.rclo,hr j _ _ (ValRel.pair (ValRel.pair hcs hself) hx)⟩

theorem ExprRel.lam (wa : WellFormed .empty (a.subst η.left)) (wA : WellFormed .empty (a.subst η.right))
    (hb : HasType .empty ((Ty.prod h a).subst η.left) body (b.subst η.left)) (hB : HasType .empty ((Ty.prod h a).subst η.right) Body (b.subst η.right))
    (hr : BodyRel η (.prod h a) b body Body) (hc : ValRel n h η ν N) :
    ExprRel n (.arr a b) η (ν,.lam (a.subst η.left) body) (N,.lam (a.subst η.right) Body) := by
  cases n with
  | zero => exact ExprRel.zero
  | succ n =>
    have hν : Value ν := by rw [ValRel] at hc; exact hc.1.1
    have hN : Value N := by rw [ValRel] at hc; exact hc.2.1.1
    exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩
      ((ValRel.clo wa wA hb hB hr (hc.mono (by omega))).toExpr)

theorem ExprRel.recfn (wa : WellFormed .empty (a.subst η.left)) (wA : WellFormed .empty (a.subst η.right)) (wb : WellFormed .empty (b.subst η.left)) (wB : WellFormed .empty (b.subst η.right))
    (hb : HasType .empty ((Ty.prod (.prod h (.arr a b)) a).subst η.left) body (b.subst η.left))
    (hB : HasType .empty ((Ty.prod (.prod h (.arr a b)) a).subst η.right) Body (b.subst η.right))
    (hr : BodyRel η (.prod (.prod h (.arr a b)) a) b body Body) (hc : ValRel n h η ν N) :
    ExprRel n (.arr a b) η (ν,.recfn (a.subst η.left) (b.subst η.left) body) (N,.recfn (a.subst η.right) (b.subst η.right) Body) := by
  cases n with
  | zero => exact ExprRel.zero
  | succ n =>
    have hν : Value ν := by rw [ValRel] at hc; exact hc.1.1
    have hN : Value N := by rw [ValRel] at hc; exact hc.2.1.1
    exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩
      ((ValRel.rclo wa wA wb wB hb hB hr (hc.mono (by omega))).toExpr)

private theorem strict_box_left : StrictFrame ν (fun e => .box e body) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_box_eq,he]

theorem ExprRel.box (he : ExprRel n h η (ν,e) (N,E))
    (hb : BodyRel η h a body Body) (hν : Value ν) (hN : Value N) :
    ExprRel n a η (ν,.box e body) (N,.box E Body) := by
  apply he.bind strict_box_left strict_box_left
  intro i hi v V hv
  have hvv : Value v := by rw [ValRel] at hv; exact hv.1.1
  have hvV : Value V := by rw [ValRel] at hv; exact hv.2.1.1
  cases hr : n-i with
  | zero => simpa only [hr] using (ExprRel.zero (a := a) (q := (ν,.box v body)) (r := (N,.box V Body)))
  | succ j =>
    have hrel : ValRel j h η v V := hv.mono (by omega)
    simpa only [hr] using (hb j v V hrel).box_value hν hN hvv hvV

end LeanSce.Target.Heterogeneous

/-! ## Heterogeneous Polymorphism -/

namespace LeanSce.Target.Heterogeneous

def PolyBodyRel (η : Valuation) (k : Kind) (gs : Guards) (a h : Typ) (body Body : Expr) : Prop :=
  ∀ p : Candidate, p.Admissible k →
    Entails .empty ((gs.subst η.left.lift).open p.left) →
    Entails .empty ((gs.subst η.right.lift).open p.right) →
    BodyRel (η.extend p) (h.rename Nat.succ) a
      (body.subst p.left.openSubst) (Body.subst p.right.openSubst)

def UnpackBodyRel (η : Valuation) (k : Kind) (gs : Guards) (a h b : Typ) (body Body : Expr) : Prop :=
  ∀ p : Candidate, p.Admissible k →
    Entails .empty ((gs.subst η.left.lift).open p.left) →
    Entails .empty ((gs.subst η.right.lift).open p.right) →
    BodyRel (η.extend p) (.prod (h.rename Nat.succ) a) (b.rename Nat.succ)
      (body.subst p.left.openSubst) (Body.subst p.right.openSubst)

theorem ValRel.tclo
    (wa : WellFormed .empty ((Ty.all k gs a).subst η.left))
    (wA : WellFormed .empty ((Ty.all k gs a).subst η.right))
    (hb : HasType (Context.empty.extend k (gs.subst η.left.lift))
      ((h.subst η.left).rename Nat.succ) body (a.subst η.left.lift))
    (hB : HasType (Context.empty.extend k (gs.subst η.right.lift))
      ((h.subst η.right).rename Nat.succ) Body (a.subst η.right.lift))
    (hr : PolyBodyRel η k gs a h body Body) (hc : ValRel n h η cap Cap) :
    ValRel n (.all k gs a) η
      (.tclo cap k (gs.subst η.left.lift) body) (.tclo Cap k (gs.subst η.right.lift) Body) := by
  rw [ValRel]
  refine ⟨⟨hc.left.1,.tclo .unit wa hc.left.1 hc.left.2 hb⟩,
    ⟨hc.right.1,.tclo .unit wA hc.right.1 hc.right.2 hB⟩,?_⟩
  rw [ShapeRel]
  intro j hj p hp hl hr'
  exact ⟨_,_,.tclo,.tclo,hr p hp hl hr' j _ _
    ((ValRel.weaken h η p).mpr (hc.mono (Nat.le_of_lt hj)))⟩

theorem ExprRel.tlam
    (wa : WellFormed .empty ((Ty.all k gs a).subst η.left))
    (wA : WellFormed .empty ((Ty.all k gs a).subst η.right))
    (hb : HasType (Context.empty.extend k (gs.subst η.left.lift))
      ((h.subst η.left).rename Nat.succ) body (a.subst η.left.lift))
    (hB : HasType (Context.empty.extend k (gs.subst η.right.lift))
      ((h.subst η.right).rename Nat.succ) Body (a.subst η.right.lift))
    (hr : PolyBodyRel η k gs a h body Body) (hc : ValRel n h η ν N) :
    ExprRel n (.all k gs a) η
      (ν,.tlam k (gs.subst η.left.lift) body) (N,.tlam k (gs.subst η.right.lift) Body) := by
  cases n with
  | zero => exact ExprRel.zero
  | succ n =>
    exact ExprRel.step ⟨hc.left.1,rfl⟩ ⟨hc.right.1,rfl⟩
      ((ValRel.tclo wa wA hb hB hr (hc.mono (by omega))).toExpr)

theorem ValRel.tapp (hf : ValRel n (.all k gs a) η f F)
    (hp : p.Admissible k)
    (hl : Entails .empty ((gs.subst η.left.lift).open p.left))
    (hr : Entails .empty ((gs.subst η.right.lift).open p.right))
    (hν : Value ν) (hN : Value N) :
    ExprRel n a (η.extend p) (ν,.tapp f p.left) (N,.tapp F p.right) := by
  have hs := hf.shape
  rw [ShapeRel] at hs
  cases n with
  | zero => exact ExprRel.zero
  | succ m =>
    cases m with
    | zero =>
      obtain ⟨q,r,hq,hr,hbody⟩ := hs 0 (by omega) p hp hl hr
      exact ExprRel.step (hq.step hν hf.left.1) (hr.step hN hf.right.1) ExprRel.zero
    | succ j =>
      obtain ⟨q,r,hq,hr,hbody⟩ := hs j (by omega) p hp hl hr
      exact ExprRel.step (hq.step hν hf.left.1) (hr.step hN hf.right.1)
        (hbody.box_value hν hN (hq.env_value hf.left.1) (hr.env_value hf.right.1))

private theorem strict_tapp : StrictFrame ν (fun f => .tapp f u) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_tapp_eq,he]

theorem ExprRel.tapp (hf : ExprRel n (.all k gs a) η (ν,f) (N,F))
    (hp : p.Admissible k)
    (hl : Entails .empty ((gs.subst η.left.lift).open p.left))
    (hr : Entails .empty ((gs.subst η.right.lift).open p.right))
    (hν : Value ν) (hN : Value N) :
    ExprRel n a (η.extend p) (ν,.tapp f p.left) (N,.tapp F p.right) := by
  apply hf.bind strict_tapp strict_tapp
  intro i hi v V hv
  exact hv.tapp hp hl hr hν hN

theorem ValRel.pack_candidate
    (wa : WellFormed .empty ((Ty.ex k gs a).subst η.left))
    (wA : WellFormed .empty ((Ty.ex k gs a).subst η.right))
    (hp : p.Admissible k)
    (hl : Entails .empty ((gs.subst η.left.lift).open p.left))
    (hr : Entails .empty ((gs.subst η.right.lift).open p.right))
    (hx : ValRel n a (η.extend p) x X) :
    ValRel n (.ex k gs a) η
      (.pack p.left ((Ty.ex k gs a).subst η.left) x)
      (.pack p.right ((Ty.ex k gs a).subst η.right) X) := by
  have hxl : HasType .empty .unit x ((a.subst η.left.lift).open p.left) := by
    simpa only [Valuation.extend,Ty.subst_instantiate] using hx.left.2
  have hxr : HasType .empty .unit X ((a.subst η.right.lift).open p.right) := by
    simpa only [Valuation.extend,Ty.subst_instantiate] using hx.right.2
  rw [ValRel,ShapeRel]
  exact ⟨⟨hx.left.1,.pack wa hp.1 hp.2.2.1 hl hxl⟩,
    ⟨hx.right.1,.pack wA hp.2.1 hp.2.2.2.1 hr hxr⟩,p,_,_,x,X,rfl,rfl,hp,hl,hr,hx⟩

private theorem strict_pack : StrictFrame ν (.pack u t) :=
  ⟨fun _ hv => hv,fun _ _ => step_pack_eq⟩

theorem ExprRel.pack_candidate
    (wa : WellFormed .empty ((Ty.ex k gs a).subst η.left))
    (wA : WellFormed .empty ((Ty.ex k gs a).subst η.right))
    (hp : p.Admissible k)
    (hl : Entails .empty ((gs.subst η.left.lift).open p.left))
    (hr : Entails .empty ((gs.subst η.right.lift).open p.right))
    (hx : ExprRel n a (η.extend p) (ν,x) (N,X)) :
    ExprRel n (.ex k gs a) η
      (ν,.pack p.left ((Ty.ex k gs a).subst η.left) x)
      (N,.pack p.right ((Ty.ex k gs a).subst η.right) X) := by
  apply hx.bind strict_pack strict_pack
  intro i hi v V hv
  exact (ValRel.pack_candidate wa wA hp hl hr hv).toExpr

theorem ValRel.fold (wa : WellFormed .empty ((Ty.mu a).subst η.left))
    (wA : WellFormed .empty ((Ty.mu a).subst η.right))
    (hx : ValRel n (a.open (.type (.mu a))) η x X) :
    ValRel n (.mu a) η
      (.fold ((Ty.mu a).subst η.left) x) (.fold ((Ty.mu a).subst η.right) X) := by
  have hxl : HasType .empty .unit x
      ((a.subst η.left.lift).open (.type ((Ty.mu a).subst η.left))) := by
    simpa only [Ty.subst_open,Arg.subst] using hx.left.2
  have hxr : HasType .empty .unit X
      ((a.subst η.right.lift).open (.type ((Ty.mu a).subst η.right))) := by
    simpa only [Ty.subst_open,Arg.subst] using hx.right.2
  rw [ValRel,ShapeRel]
  exact ⟨⟨hx.left.1,.fold wa hxl⟩,⟨hx.right.1,.fold wA hxr⟩,_,_,x,X,rfl,rfl,
    fun j hj => hx.mono (Nat.le_of_lt hj)⟩

private theorem strict_fold : StrictFrame ν (.fold t) :=
  ⟨fun _ hv => hv,fun _ _ => step_fold_eq⟩

theorem ExprRel.fold (wa : WellFormed .empty ((Ty.mu a).subst η.left))
    (wA : WellFormed .empty ((Ty.mu a).subst η.right))
    (hx : ExprRel n (a.open (.type (.mu a))) η (ν,x) (N,X)) :
    ExprRel n (.mu a) η
      (ν,.fold ((Ty.mu a).subst η.left) x) (N,.fold ((Ty.mu a).subst η.right) X) := by
  apply hx.bind strict_fold strict_fold
  intro i hi v V hv
  exact (ValRel.fold wa wA hv).toExpr

theorem ValRel.unfold (hx : ValRel n (.mu a) η x X) (hν : Value ν) (hN : Value N) :
    ExprRel n (a.open (.type (.mu a))) η (ν,.unfold x) (N,.unfold X) := by
  cases n with
  | zero => exact ExprRel.zero
  | succ n =>
    have hs := hx.shape
    rw [ShapeRel] at hs
    obtain ⟨t,t',v,V,hxv,hXV,hvalues⟩ := hs
    subst x;subst X
    exact ExprRel.step
      ⟨hν,by simp [step_unfold_eq,(show _ = true from hx.left.1)]⟩
      ⟨hN,by simp [step_unfold_eq,(show _ = true from hx.right.1)]⟩
      ((hvalues n (by omega)).toExpr)

private theorem strict_unfold : StrictFrame ν Term.unfold := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_unfold_eq,he]

theorem ExprRel.unfold (hx : ExprRel n (.mu a) η (ν,x) (N,X)) (hν : Value ν) (hN : Value N) :
    ExprRel n (a.open (.type (.mu a))) η (ν,.unfold x) (N,.unfold X) := by
  apply hx.bind strict_unfold strict_unfold
  intro i hi v V hv
  exact hv.unfold hν hN

theorem ValRel.unpack (hp : ValRel n (.ex k gs a) η p P) (hc : ValRel n h η ν N)
    (hb : UnpackBodyRel η k gs a h b body Body) :
    ExprRel n b η (ν,.unpack p body) (N,.unpack P Body) := by
  have hs := hp.shape
  rw [ShapeRel] at hs
  obtain ⟨S,t,t',v,V,hpval,hPval,hS,hgl,hgr,hvalues⟩ := hs
  subst p;subst P
  have hl : Step ν (.unpack (.pack S.left t v) body) (.box (.pair ν v) (body.subst S.left.openSubst)) :=
    ⟨hc.left.1,by simp [step_unpack_eq,(show _ = true from hp.left.1)]⟩
  have hr : Step N (.unpack (.pack S.right t' V) Body) (.box (.pair N V) (Body.subst S.right.openSubst)) :=
    ⟨hc.right.1,by simp [step_unpack_eq,(show _ = true from hp.right.1)]⟩
  cases n with
  | zero => exact ExprRel.zero
  | succ m =>
    cases m with
    | zero => exact ExprRel.step hl hr ExprRel.zero
    | succ j =>
      have hval := hvalues.mono (m:=j) (by omega)
      have hcap := (ValRel.weaken h η S).mpr (hc.mono (m:=j) (by omega))
      have henv := hcap.pair hval
      have hbody := (ExprRel.weaken b η S).mp (hb S hS hgl hgr j _ _ henv)
      exact ExprRel.step hl hr (hbody.box_value hc.left.1 hc.right.1 henv.left.1 henv.right.1)

private theorem strict_unpack : StrictFrame ν (fun p => .unpack p body) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_unpack_eq,he]

theorem ExprRel.unpack (hp : ExprRel n (.ex k gs a) η (ν,p) (N,P)) (hc : ValRel n h η ν N)
    (hb : UnpackBodyRel η k gs a h b body Body) :
    ExprRel n b η (ν,.unpack p body) (N,.unpack P Body) := by
  apply hp.bind strict_unpack strict_unpack
  intro i hi v V hv
  exact hv.unpack (hc.mono (Nat.sub_le _ _)) hb

end LeanSce.Target.Heterogeneous

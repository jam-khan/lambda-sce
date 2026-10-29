import LeanSce.Target.LogicalRelation.Contexts
import LeanSce.Target.LogicalRelation.Data
import LeanSce.Target.LogicalRelation.Evaluation
import LeanSce.Target.Metatheory.Basic

/-!
# Target / LogicalRelation / Functions

Proofs and supporting constructions for functions.
-/

/-! ## Logical Relation Functions -/

namespace LeanSce.Target.LogicalRelation

def BodyRel (h a : Typ) (e E : Expr) : Prop :=
  ∀ n ν N, ValRel n h ν N → ExprRel n a (ν,e) (N,E)

private theorem pair_related (hx : ValRel n a x X) (hy : ValRel n b y Y) :
    ValRel n (.prod a b) (.pair x y) (.pair X Y) := by
  rw [ValRel] at hx hy ⊢
  refine ⟨⟨Bool.and_eq_true_iff.mpr ⟨hx.1.1,hy.1.1⟩,.pair hx.1.2 hy.1.2⟩,
    ⟨Bool.and_eq_true_iff.mpr ⟨hx.2.1.1,hy.2.1.1⟩,.pair hx.2.1.2 hy.2.1.2⟩,?_⟩
  rw [ShapeRel]
  exact ⟨x,y,X,Y,rfl,rfl,by rw [ValRel];exact hx,by rw [ValRel];exact hy⟩

theorem ExprRel.box_value (hb : ExprRel n a (env,body) (Env,Body))
    (hν : Value ν) (hN : Value N) (he : Value env) (hE : Value Env) :
    ExprRel (n+1) a (ν,.box env body) (N,.box Env Body) := by
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

theorem ValRel.app (hf : ValRel n (.arr a b) f F) (hx : ValRel n a x X)
    (hν : Value ν) (hN : Value N) : ExprRel n b (ν,.app f x) (N,.app F X) := by
  have hvf : Value f := by rw [ValRel] at hf; exact hf.1.1
  have hvF : Value F := by rw [ValRel] at hf; exact hf.2.1.1
  have hvx : Value x := by rw [ValRel] at hx; exact hx.1.1
  have hvX : Value X := by rw [ValRel] at hx; exact hx.2.1.1
  have hs : ShapeRel n (.arr a b) f F := by rw [ValRel] at hf;exact hf.2.2
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

theorem ExprRel.app (hf : ExprRel n (.arr a b) (ν,f) (N,F))
    (hx : ExprRel n a (ν,x) (N,X)) (hν : Value ν) (hN : Value N) :
    ExprRel n b (ν,.app f x) (N,.app F X) := by
  apply hf.bind strict_app_left strict_app_left
  intro i hi v V hv
  have htv : Value v := by rw [ValRel] at hv; exact hv.1.1
  have htV : Value V := by rw [ValRel] at hv; exact hv.2.1.1
  apply (hx.mono (Nat.sub_le _ _)).bind (strict_app_right htv) (strict_app_right htV)
  intro j hj w W hw
  exact (hv.mono (Nat.sub_le _ _)).app hw hν hN

theorem ValRel.clo (wa : WellFormed .empty a)
    (hb : HasType .empty (.prod h a) body b) (hB : HasType .empty (.prod h a) Body b)
    (hr : BodyRel (.prod h a) b body Body) (hc : ValRel n h cap Cap) :
    ValRel n (.arr a b) (.clo cap a body) (.clo Cap a Body) := by
  have hcap : ValueType .empty cap h := by rw [ValRel] at hc; exact hc.1
  have hCap : ValueType .empty Cap h := by rw [ValRel] at hc; exact hc.2.1
  rw [ValRel]
  refine ⟨⟨hcap.1,.clo .unit wa hcap.1 hcap.2 hb⟩,
    ⟨hCap.1,.clo .unit wa hCap.1 hCap.2 hB⟩,?_⟩
  rw [ShapeRel]
  intro j hj x X hx
  exact ⟨_,_,.clo,.clo,hr j _ _ (pair_related (hc.mono (Nat.le_of_lt hj)) hx)⟩

theorem ValRel.rclo (wa : WellFormed .empty a) (wb : WellFormed .empty b)
    (hb : HasType .empty (.prod (.prod h (.arr a b)) a) body b)
    (hB : HasType .empty (.prod (.prod h (.arr a b)) a) Body b)
    (hr : BodyRel (.prod (.prod h (.arr a b)) a) b body Body)
    (hc : ValRel n h cap Cap) :
    ValRel n (.arr a b) (.rclo cap a b body) (.rclo Cap a b Body) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hcap : ValueType .empty cap h := by rw [ValRel] at hc; exact hc.1
    have hCap : ValueType .empty Cap h := by rw [ValRel] at hc; exact hc.2.1
    rw [ValRel]
    refine ⟨⟨hcap.1,.rclo .unit wa wb hcap.1 hcap.2 hb⟩,
      ⟨hCap.1,.rclo .unit wa wb hCap.1 hCap.2 hB⟩,?_⟩
    rw [ShapeRel]
    intro j hj x X hx
    have hcs := hc.mono (Nat.le_of_lt hj)
    have hself := ih j hj hcs
    exact ⟨_,_,.rclo,.rclo,hr j _ _ (pair_related (pair_related hcs hself) hx)⟩

theorem ExprRel.lam (wa : WellFormed .empty a)
    (hb : HasType .empty (.prod h a) body b) (hB : HasType .empty (.prod h a) Body b)
    (hr : BodyRel (.prod h a) b body Body) (hc : ValRel n h ν N) :
    ExprRel n (.arr a b) (ν,.lam a body) (N,.lam a Body) := by
  cases n with
  | zero => exact ExprRel.zero
  | succ n =>
    have hν : Value ν := by rw [ValRel] at hc; exact hc.1.1
    have hN : Value N := by rw [ValRel] at hc; exact hc.2.1.1
    exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩
      ((ValRel.clo wa hb hB hr (hc.mono (by omega))).toExpr)

theorem ExprRel.recfn (wa : WellFormed .empty a) (wb : WellFormed .empty b)
    (hb : HasType .empty (.prod (.prod h (.arr a b)) a) body b)
    (hB : HasType .empty (.prod (.prod h (.arr a b)) a) Body b)
    (hr : BodyRel (.prod (.prod h (.arr a b)) a) b body Body) (hc : ValRel n h ν N) :
    ExprRel n (.arr a b) (ν,.recfn a b body) (N,.recfn a b Body) := by
  cases n with
  | zero => exact ExprRel.zero
  | succ n =>
    have hν : Value ν := by rw [ValRel] at hc; exact hc.1.1
    have hN : Value N := by rw [ValRel] at hc; exact hc.2.1.1
    exact ExprRel.step ⟨hν,rfl⟩ ⟨hN,rfl⟩
      ((ValRel.rclo wa wb hb hB hr (hc.mono (by omega))).toExpr)

private theorem strict_box_left : StrictFrame ν (fun e => .box e body) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_box_eq,he]

theorem ExprRel.box (he : ExprRel n h (ν,e) (N,E))
    (hb : BodyRel h a body Body) (hν : Value ν) (hN : Value N) :
    ExprRel n a (ν,.box e body) (N,.box E Body) := by
  apply he.bind strict_box_left strict_box_left
  intro i hi v V hv
  have hvv : Value v := by rw [ValRel] at hv; exact hv.1.1
  have hvV : Value V := by rw [ValRel] at hv; exact hv.2.1.1
  cases hr : n-i with
  | zero => simpa only [hr] using (ExprRel.zero (a := a) (q := (ν,.box v body)) (r := (N,.box V Body)))
  | succ j =>
    have hrel : ValRel j h v V := hv.mono (by omega)
    simpa only [hr] using (hb j v V hrel).box_value hν hN hvv hvV

end LeanSce.Target.LogicalRelation

/-! ## Logical Relation Branches -/

namespace LeanSce.Target.LogicalRelation

theorem ValRel.case {left Left right Right : Expr} (hx : ValRel n (.sum a b) x X) (hc : ValRel n h ν N)
    (hl : BodyRel (.prod h a) c left Left) (hr : BodyRel (.prod h b) c right Right) :
    ExprRel n c (ν,.case x left right) (N,.case X Left Right) := by
  have hs := hx.shape
  rw [ShapeRel] at hs
  rcases hs with ⟨t,t',v,V,hxv,hXV,hvals⟩ | ⟨t,t',v,V,hxv,hXV,hvals⟩
  · subst x;subst X
    have hstep : Step ν (.case (.inl t v) left right) (.box (.pair ν v) left) :=
      ⟨hc.left.1,by simp [step_case_eq,(show _ = true from hx.left.1)]⟩
    have Hstep : Step N (.case (.inl t' V) Left Right) (.box (.pair N V) Left) :=
      ⟨hc.right.1,by simp [step_case_eq,(show _ = true from hx.right.1)]⟩
    cases n with
    | zero => exact ExprRel.zero
    | succ m =>
      cases m with
      | zero => exact ExprRel.step hstep Hstep ExprRel.zero
      | succ j =>
        have he := (hc.mono (m := j) (by omega)).pair (hvals.mono (m := j) (by omega))
        exact ExprRel.step hstep Hstep
          ((hl j _ _ he).box_value hc.left.1 hc.right.1 he.left.1 he.right.1)
  · subst x;subst X
    have hstep : Step ν (.case (.inr t v) left right) (.box (.pair ν v) right) :=
      ⟨hc.left.1,by simp [step_case_eq,(show _ = true from hx.left.1)]⟩
    have Hstep : Step N (.case (.inr t' V) Left Right) (.box (.pair N V) Right) :=
      ⟨hc.right.1,by simp [step_case_eq,(show _ = true from hx.right.1)]⟩
    cases n with
    | zero => exact ExprRel.zero
    | succ m =>
      cases m with
      | zero => exact ExprRel.step hstep Hstep ExprRel.zero
      | succ j =>
        have he := (hc.mono (m := j) (by omega)).pair (hvals.mono (m := j) (by omega))
        exact ExprRel.step hstep Hstep
          ((hr j _ _ he).box_value hc.left.1 hc.right.1 he.left.1 he.right.1)

theorem ExprRel.case {left Left right Right : Expr} (hx : ExprRel n (.sum a b) (ν,x) (N,X)) (hc : ValRel n h ν N)
    (hl : BodyRel (.prod h a) c left Left) (hr : BodyRel (.prod h b) c right Right) :
    ExprRel n c (ν,.case x left right) (N,.case X Left Right) := by
  apply hx.bind strict_case strict_case
  intro i hi v V hv
  exact hv.case (hc.mono (Nat.sub_le _ _)) hl hr

end LeanSce.Target.LogicalRelation

/-! ## Logical Relation Polymorphism -/

namespace LeanSce.Target.LogicalRelation

def PolyBodyRel (k : Kind) (gs : Guards) (a h : Typ) (body Body : Expr) : Prop :=
  ∀ u, u.kind = k → u.WellFormed .empty → Entails .empty (gs.open u) →
    BodyRel h (a.open u) (body.subst u.openSubst) (Body.subst u.openSubst)

def UnpackBodyRel (k : Kind) (gs : Guards) (a h b : Typ) (body Body : Expr) : Prop :=
  ∀ u, u.kind = k → u.WellFormed .empty → Entails .empty (gs.open u) →
    BodyRel (.prod h (a.open u)) b (body.subst u.openSubst) (Body.subst u.openSubst)

theorem ValRel.tclo (wa : WellFormed .empty (.all k gs a))
    (hb : HasType (Context.empty.extend k gs) (h.rename Nat.succ) body a)
    (hB : HasType (Context.empty.extend k gs) (h.rename Nat.succ) Body a)
    (hr : PolyBodyRel k gs a h body Body) (hc : ValRel n h cap Cap) :
    ValRel n (.all k gs a) (.tclo cap k gs body) (.tclo Cap k gs Body) := by
  have hcap := hc.left
  have hCap := hc.right
  rw [ValRel]
  refine ⟨⟨hcap.1,.tclo .unit wa hcap.1 hcap.2 hb⟩,
    ⟨hCap.1,.tclo .unit wa hCap.1 hCap.2 hB⟩,?_⟩
  rw [ShapeRel]
  intro j hj u hk hu hg
  exact ⟨_,_,.tclo,.tclo,hr u hk hu hg j _ _ (hc.mono (Nat.le_of_lt hj))⟩

theorem ExprRel.tlam (wa : WellFormed .empty (.all k gs a))
    (hb : HasType (Context.empty.extend k gs) (h.rename Nat.succ) body a)
    (hB : HasType (Context.empty.extend k gs) (h.rename Nat.succ) Body a)
    (hr : PolyBodyRel k gs a h body Body) (hc : ValRel n h ν N) :
    ExprRel n (.all k gs a) (ν,.tlam k gs body) (N,.tlam k gs Body) := by
  cases n with
  | zero => exact ExprRel.zero
  | succ n =>
    exact ExprRel.step ⟨hc.left.1,rfl⟩ ⟨hc.right.1,rfl⟩
      ((ValRel.tclo wa hb hB hr (hc.mono (by omega))).toExpr)

theorem ValRel.tapp (hf : ValRel n (.all k gs a) f F)
    (hk : u.kind = k) (hu : u.WellFormed .empty) (hg : Entails .empty (gs.open u))
    (hν : Value ν) (hN : Value N) :
    ExprRel n (a.open u) (ν,.tapp f u) (N,.tapp F u) := by
  have hs := hf.shape
  rw [ShapeRel] at hs
  cases n with
  | zero => exact ExprRel.zero
  | succ m =>
    cases m with
    | zero =>
      obtain ⟨q,r,hq,hr,hbody⟩ := hs 0 (by omega) u hk hu hg
      exact ExprRel.step (hq.step hν hf.left.1) (hr.step hN hf.right.1) ExprRel.zero
    | succ j =>
      obtain ⟨q,r,hq,hr,hbody⟩ := hs j (by omega) u hk hu hg
      exact ExprRel.step (hq.step hν hf.left.1) (hr.step hN hf.right.1)
        (hbody.box_value hν hN (hq.env_value hf.left.1) (hr.env_value hf.right.1))

private theorem strict_tapp : StrictFrame ν (fun f => .tapp f u) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_tapp_eq,he]

theorem ExprRel.tapp (hf : ExprRel n (.all k gs a) (ν,f) (N,F))
    (hk : u.kind = k) (hu : u.WellFormed .empty) (hg : Entails .empty (gs.open u))
    (hν : Value ν) (hN : Value N) :
    ExprRel n (a.open u) (ν,.tapp f u) (N,.tapp F u) := by
  apply hf.bind strict_tapp strict_tapp
  intro i hi v V hv
  exact hv.tapp hk hu hg hν hN

theorem ValRel.pack (wa : WellFormed .empty (.ex k gs a))
    (hk : u.kind = k) (hu : u.WellFormed .empty) (hg : Entails .empty (gs.open u))
    (hx : ValRel n (a.open u) x X) :
    ValRel n (.ex k gs a) (.pack u (.ex k gs a) x) (.pack u (.ex k gs a) X) := by
  rw [ValRel]
  refine ⟨⟨hx.left.1,.pack wa hk hu hg hx.left.2⟩,
    ⟨hx.right.1,.pack wa hk hu hg hx.right.2⟩,?_⟩
  rw [ShapeRel]
  exact ⟨u,_,_,x,X,rfl,rfl,hk,hu,hg,fun j hj => hx.mono (Nat.le_of_lt hj)⟩

private theorem strict_pack : StrictFrame ν (.pack u t) :=
  ⟨fun _ hv => hv,fun _ _ => step_pack_eq⟩

theorem ExprRel.pack (wa : WellFormed .empty (.ex k gs a))
    (hk : u.kind = k) (hu : u.WellFormed .empty) (hg : Entails .empty (gs.open u))
    (hx : ExprRel n (a.open u) (ν,x) (N,X)) :
    ExprRel n (.ex k gs a) (ν,.pack u (.ex k gs a) x) (N,.pack u (.ex k gs a) X) := by
  apply hx.bind strict_pack strict_pack
  intro i hi v V hv
  exact (ValRel.pack wa hk hu hg hv).toExpr

theorem ValRel.fold (wa : WellFormed .empty (.mu a))
    (hx : ValRel n (a.open (.type (.mu a))) x X) :
    ValRel n (.mu a) (.fold (.mu a) x) (.fold (.mu a) X) := by
  rw [ValRel]
  refine ⟨⟨hx.left.1,.fold wa hx.left.2⟩,⟨hx.right.1,.fold wa hx.right.2⟩,?_⟩
  rw [ShapeRel]
  exact ⟨_,_,x,X,rfl,rfl,fun j hj => hx.mono (Nat.le_of_lt hj)⟩

private theorem strict_fold : StrictFrame ν (.fold t) :=
  ⟨fun _ hv => hv,fun _ _ => step_fold_eq⟩

theorem ExprRel.fold (wa : WellFormed .empty (.mu a))
    (hx : ExprRel n (a.open (.type (.mu a))) (ν,x) (N,X)) :
    ExprRel n (.mu a) (ν,.fold (.mu a) x) (N,.fold (.mu a) X) := by
  apply hx.bind strict_fold strict_fold
  intro i hi v V hv
  exact (ValRel.fold wa hv).toExpr

theorem ValRel.unfold (hx : ValRel n (.mu a) x X) (hν : Value ν) (hN : Value N) :
    ExprRel n (a.open (.type (.mu a))) (ν,.unfold x) (N,.unfold X) := by
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

theorem ExprRel.unfold (hx : ExprRel n (.mu a) (ν,x) (N,X)) (hν : Value ν) (hN : Value N) :
    ExprRel n (a.open (.type (.mu a))) (ν,.unfold x) (N,.unfold X) := by
  apply hx.bind strict_unfold strict_unfold
  intro i hi v V hv
  exact hv.unfold hν hN

theorem ValRel.unpack (hp : ValRel n (.ex k gs a) p P) (hc : ValRel n h ν N)
    (hb : UnpackBodyRel k gs a h b body Body) :
    ExprRel n b (ν,.unpack p body) (N,.unpack P Body) := by
  have hs := hp.shape
  rw [ShapeRel] at hs
  obtain ⟨u,t,t',v,V,hpval,hPval,hk,hu,hg,hvalues⟩ := hs
  subst p;subst P
  have hl : Step ν (.unpack (.pack u t v) body) (.box (.pair ν v) (body.subst u.openSubst)) :=
    ⟨hc.left.1,by simp [step_unpack_eq,(show _ = true from hp.left.1)]⟩
  have hr : Step N (.unpack (.pack u t' V) Body) (.box (.pair N V) (Body.subst u.openSubst)) :=
    ⟨hc.right.1,by simp [step_unpack_eq,(show _ = true from hp.right.1)]⟩
  cases n with
  | zero => exact ExprRel.zero
  | succ m =>
    cases m with
    | zero => exact ExprRel.step hl hr ExprRel.zero
    | succ j =>
      have hval := hvalues j (by omega)
      have henv := (hc.mono (by omega)).pair hval
      exact ExprRel.step hl hr
        ((hb u hk hu hg j _ _ henv).box_value hc.left.1 hc.right.1 henv.left.1 henv.right.1)

private theorem strict_unpack : StrictFrame ν (fun p => .unpack p body) := by
  constructor
  · intro e hv; cases hv
  · intro e hn
    have he : e.isValue = false := by cases hv : e.isValue <;> first | rfl | exact False.elim (hn hv)
    simp [step_unpack_eq,he]

theorem ExprRel.unpack (hp : ExprRel n (.ex k gs a) (ν,p) (N,P)) (hc : ValRel n h ν N)
    (hb : UnpackBodyRel k gs a h b body Body) :
    ExprRel n b (ν,.unpack p body) (N,.unpack P Body) := by
  apply hp.bind strict_unpack strict_unpack
  intro i hi v V hv
  exact hv.unpack (hc.mono (Nat.sub_le _ _)) hb

end LeanSce.Target.LogicalRelation

/-! ## Logical Relation Open -/

namespace LeanSce.Target.LogicalRelation

/-- Closing a static context turns open compatibility into compatibility of
    bodies under arbitrary related native ambient values. -/
theorem OpenRel.body (he : OpenRel Δ h e E a) (hθ : Closing θ Δ) :
    BodyRel (h.subst θ) (a.subst θ) (e.subst θ) (E.subst θ) := he θ hθ

/-- A fresh binder receives the same closed witness in both computations. -/
theorem OpenRel.polybody {h : Typ} (he : OpenRel (Δ.extend k gs) (h.rename Nat.succ) e E a)
    (hθ : Closing θ Δ) (hf : FreshGuards k gs) :
    PolyBodyRel k (gs.subst θ.lift) (a.subst θ.lift) (h.subst θ)
      (e.subst θ.lift) (E.subst θ.lift) := by
  intro u hk hu hg n ν N hcap
  have hθ' := hθ.instantiate hf hk hu hg
  have hrel := he (θ.instantiate u) hθ' n ν N
    (by simpa only [Ty.subst_instantiate_weaken] using hcap)
  simpa only [Ty.subst_instantiate,Term.subst_instantiate] using hrel

/-- Existential clients use one shared witness throughout their extended scope. -/
theorem OpenRel.unpack_body {h b : Typ}
    (he : OpenRel (Δ.extend k gs) (.prod (h.rename Nat.succ) a) e E (b.rename Nat.succ))
    (hθ : Closing θ Δ) (hf : FreshGuards k gs) :
    UnpackBodyRel k (gs.subst θ.lift) (a.subst θ.lift) (h.subst θ) (b.subst θ)
      (e.subst θ.lift) (E.subst θ.lift) := by
  intro u hk hu hg n ν N hcap
  have hθ' := hθ.instantiate hf hk hu hg
  have hrel := he (θ.instantiate u) hθ' n ν N
    (by simpa only [Ty.subst,Ty.subst_instantiate_weaken,Ty.subst_instantiate,Ty.subst_lift_weaken,Ty.open_weaken] using hcap)
  simpa only [Ty.subst_instantiate_weaken,Term.subst_instantiate] using hrel

/-- A related value-position context supplies related values, without evaluating
    a capture expression or changing its caller's environment. -/
theorem OpenRel.values (he : OpenRel Δ .unit e E a) (hv : Value e) (hV : Value E)
    (hθ : Closing θ Δ) : ValRel n (a.subst θ) (e.subst θ) (E.subst θ) := by
  have hrel := he θ hθ (n+1) .unit .unit ValRel.unit
  rw [ExprRel] at hrel
  have hvθ : Value (e.subst θ) := by simpa [Value] using hv
  have hVθ : Value (E.subst θ) := by simpa [Value] using hV
  obtain ⟨w,hw,hr⟩ := hrel.1 0 (by omega) (e.subst θ) ⟨.refl,hvθ⟩
  have heq := hw.1.value_result hVθ
  subst w
  exact hr.mono (by omega)

end LeanSce.Target.LogicalRelation

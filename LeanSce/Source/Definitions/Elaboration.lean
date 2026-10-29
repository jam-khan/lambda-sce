import LeanSce.Source.Definitions.Semantics
import LeanSce.Source.Definitions.Typing
import LeanSce.Target.Definitions.Typing

/-!
# Source / Definitions / Elaboration

Calculus definitions.
-/

/-! ## Type Erasure — definitions -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort)

/-- All static structure survives except the source module constructor. -/
def Ty.erase : Ty s → Target.Ty s
  | .tvar i => .tvar i
  | .rvar i => .rvar i
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .string => .string
  | .prod a b => .prod a.erase b.erase
  | .sum a b => .sum a.erase b.erase
  | .arr a b => .arr a.erase b.erase
  | .tag l a => .tag l a.erase
  | .record r => .record r.erase
  | .all k g a => .all k g.erase a.erase
  | .ex k g a => .ex k g.erase a.erase
  | .mu a => .mu a.erase
  | .empty => .empty
  | .field l a => .field l a.erase
  | .union r s => .union r.erase s.erase
  | .gnil => .gnil
  | .gcons r s g => .gcons r.erase s.erase g.erase
  | .module i o => .arr (.record i.erase) (.record o.erase)

def Arg.erase : Arg → Target.Arg
  | .type a => .type a.erase
  | .row r => .row r.erase

def Subst.erase (σ : Subst) : Target.Subst := fun k i => (σ k i).erase

end LeanSce.Source

/-! ## Static Erasure — definitions -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort Atom Entry crossAtoms)

def Context.erase (Δ : Context) : Target.Context := ⟨Δ.kinds, Δ.assumptions⟩

end LeanSce.Source

/-! ## Elaboration — definitions -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

namespace Templates
open LeanSce.Target

def sandbox (i : Target.Row) (body : Target.Expr) : Target.Expr :=
  .close (.lam (.record i) (.box (.ix 0) body))

def captured (c i : Target.Row) (body : Target.Expr) : Target.Expr :=
  .close (.lam (.record c) (.lam (.record i) (.box (.merge (.ix 1) (.ix 0)) body)))

def run (p i o : Target.Row) (cd : Target.Expr) : Target.Expr :=
  .close (.lam (.arr (.record i) (.record o))
    (.lam (.record p) (.app (.ix 1) (.app cd (.ix 0)))))

def link (p i o : Target.Row) (cd : Target.Expr) : Target.Expr :=
  .close (.lam (.record p) (.lam (.arr (.record i) (.record o))
    (.letIn (.app cd (.ix 1))
      (.letIn (.app (.ix 1) (.ix 0)) (.merge (.ix 3) (.ix 0))))))

def residualBody : Target.Expr :=
  .app (.fst (.fst .query)) (.merge (.snd (.fst .query)) (.snd .query))

def provide (p j k o : Target.Row) (cd : Target.Expr) : Target.Expr :=
  .close (.lam (.record p) (.lam (.arr (.record (.union j k)) (.record o))
    (.letIn (.app cd (.ix 1))
      (.box (.pair (.ix 1) (.ix 0)) (.lam (.record k) residualBody)))))

def residual (j k o : Target.Row) : Target.Expr :=
  .close (.lam (.arr (.record (.union j k)) (.record o)) (.lam (.record j)
    (.box (.pair (.ix 1) (.ix 0)) (.lam (.record k) residualBody))))
end Templates

/-- Total translation of checked/runtime syntax. All helper types are retained
    annotations, so the translation never reruns source matching on erased types.
    It translates saved certificates recursively, including their stored code. -/
def Term.erase : Term s → Target.Term s
  | .unit => .unit
  | .int n => .int n
  | .bool b => .bool b
  | .string s => .string s
  | .query => .query
  | .pair a b => .pair a.erase b.erase
  | .fst a => .fst a.erase
  | .snd a => .snd a.erase
  | .box a b => .box a.erase b.erase
  | .lam a b => .lam a.erase b.erase
  | .recfn a b e => .recfn a.erase b.erase e.erase
  | .app a b => .app a.erase b.erase
  | .inl a e => .inl a.erase e.erase
  | .inr a e => .inr a.erase e.erase
  | .case a b c => .case a.erase b.erase c.erase
  | .tag l a => .tag l a.erase
  | .find l a => .find l a.erase
  | .record fs => .record fs.erase
  | .get a l => .get a.erase l
  | .merge a b => .merge a.erase b.erase
  | .take ls a => .take ls a.erase
  | .drop ls a => .drop ls a.erase
  | .relabel l k a => .relabel l k a.erase
  | .tlam k g a => .tlam k g.erase a.erase
  | .tapp a u => .tapp a.erase u.erase
  | .pack u t a => .pack u.erase t.erase a.erase
  | .unpack a b => .unpack a.erase b.erase
  | .fold t a => .fold t.erase a.erase
  | .unfold a => .unfold a.erase
  | .prim p args => .prim p args.erase
  | .ite a b c => .ite a.erase b.erase c.erase
  | .clo cap t b => .clo cap.erase t.erase b.erase
  | .rclo cap a b e => .rclo cap.erase a.erase b.erase e.erase
  | .tclo cap k g a => .tclo cap.erase k g.erase a.erase
  | .nil => .nil
  | .cons l a rest => .cons l a.erase rest.erase
  | .letVal _ e body => .letIn e.erase body.erase
  | .view _ _ cd e => .app cd.erase e.erase
  | .module i _ body => Templates.sandbox i.erase body.erase
  | .capture c i _ cap body => .app (Templates.captured c.erase i.erase body.erase) cap.erase
  | .run p i o cd m provider => .app (.app (Templates.run p.erase i.erase o.erase cd.erase) m.erase) provider.erase
  | .link p i o cd provider m => .app (.app (Templates.link p.erase i.erase o.erase cd.erase) provider.erase) m.erase
  | .provide p j k o cd provider m =>
      .app (.app (Templates.provide p.erase j.erase k.erase o.erase cd.erase) provider.erase) m.erase
  | .complete o m => .app (.app (Templates.run .empty .empty o.erase
      (.close (.lam (.record .empty) (.ix 0)))) m.erase) (.record .nil)
  | .moduleVal cap _ i _ body =>
      .clo (.pair .unit cap.erase) (.record i.erase) (.box (.merge (.ix 1) (.ix 0)) body.erase)
  | .resid m saved j k o =>
      if m.isValue && saved.isValue then
        .clo (.pair m.erase saved.erase) (.record k.erase) Templates.residualBody
      else .app (.app (Templates.residual j.erase k.erase o.erase) m.erase) saved.erase
  | .invoke _ _ m imports => .app m.erase imports.erase

/-- The executable compiler graph. Runtime elaboration is the more general
    relation in Correspondence.lean, permitting both empty-module representations. -/
def Compiles (e : Expr) (E : Target.Expr) : Prop := e.erase = E

end LeanSce.Source

/-! ## Correspondence -/

namespace LeanSce.Source
open LeanSce.Target (Kind TySort TermSort Prim)

mutual
/-- Runtime elaboration. The canonical compiler is one choice; compatible
    subterms may use other related value representations. Field initializers
    retain their order. Only completed record values may be permuted. -/
inductive Elaborates : Term s → Target.Term s → Prop where
  | canonical : Elaborates e e.erase
  | value : Related v V → Elaborates v V
  | pair : Elaborates a A → Elaborates b B → Elaborates (.pair a b) (.pair A B)
  | fst : Elaborates a A → Elaborates (.fst a) (.fst A)
  | snd : Elaborates a A → Elaborates (.snd a) (.snd A)
  | box : Elaborates a A → Elaborates b B → Elaborates (.box a b) (.box A B)
  | lam : Elaborates b B → Elaborates (.lam a b) (.lam a.erase B)
  | recfn : Elaborates b B → Elaborates (.recfn a t b) (.recfn a.erase t.erase B)
  | app : Elaborates a A → Elaborates b B → Elaborates (.app a b) (.app A B)
  | inl : Elaborates a A → Elaborates (.inl t a) (.inl t.erase A)
  | inr : Elaborates a A → Elaborates (.inr t a) (.inr t.erase A)
  | case : Elaborates a A → Elaborates b B → Elaborates c C → Elaborates (.case a b c) (.case A B C)
  | tag : Elaborates a A → Elaborates (.tag l a) (.tag l A)
  | find : Elaborates a A → Elaborates (.find l a) (.find l A)
  | record : Elaborates fs Fs → Elaborates (.record fs) (.record Fs)
  | cons : Elaborates e E → Elaborates fs Fs → Elaborates (.cons l e fs) (.cons l E Fs)
  | get : Elaborates a A → Elaborates (.get a l) (.get A l)
  | merge : Elaborates a A → Elaborates b B → Elaborates (.merge a b) (.merge A B)
  | take : Elaborates a A → Elaborates (.take ls a) (.take ls A)
  | drop : Elaborates a A → Elaborates (.drop ls a) (.drop ls A)
  | relabel : Elaborates a A → Elaborates (.relabel l k a) (.relabel l k A)
  | tlam : Elaborates a A → Elaborates (.tlam k g a) (.tlam k g.erase A)
  | tapp : Elaborates a A → Elaborates (.tapp a u) (.tapp A u.erase)
  | pack : Elaborates a A → Elaborates (.pack u t a) (.pack u.erase t.erase A)
  | unpack : Elaborates a A → Elaborates b B → Elaborates (.unpack a b) (.unpack A B)
  | fold : Elaborates a A → Elaborates (.fold t a) (.fold t.erase A)
  | unfold : Elaborates a A → Elaborates (.unfold a) (.unfold A)
  | prim : Elaborates fs Fs → Elaborates (.prim p fs) (.prim p Fs)
  | ite : Elaborates a A → Elaborates b B → Elaborates c C → Elaborates (.ite a b c) (.ite A B C)
  | letVal : Elaborates a A → Elaborates b B → Elaborates (.letVal t a b) (.letIn A B)
  | view : Elaborates cd C → Elaborates e E → Elaborates (.view a b cd e) (.app C E)
  | module : Elaborates b B → Elaborates (.module i o b) (Templates.sandbox i.erase B)
  | capture : Elaborates cap C → Elaborates b B →
      Elaborates (.capture c i o cap b) (.app (Templates.captured c.erase i.erase B) C)
  | run : Elaborates cd C → Elaborates m M → Elaborates p P →
      Elaborates (.run r i o cd m p) (.app (.app (Templates.run r.erase i.erase o.erase C) M) P)
  | link : Elaborates cd C → Elaborates p P → Elaborates m M →
      Elaborates (.link r i o cd p m) (.app (.app (Templates.link r.erase i.erase o.erase C) P) M)
  | provide : Elaborates cd C → Elaborates p P → Elaborates m M →
      Elaborates (.provide r j k o cd p m)
        (.app (.app (Templates.provide r.erase j.erase k.erase o.erase C) P) M)
  | complete : Elaborates m M → Elaborates (.complete o m)
      (.app (.app (Templates.run .empty .empty o.erase (.close (.lam (.record .empty) (.ix 0)))) M) (.record .nil))
  | resid : Related m M → ¬ Value saved → Elaborates saved S →
      Elaborates (.resid m saved j k o) (.app (.app (Templates.residual j.erase k.erase o.erase) M) S)
  | invoke : Elaborates m M → Elaborates p P → Elaborates (.invoke i o m p) (.app M P)

/-- Concrete value correspondence, mutually defined with stored-code elaboration.
    It does not assert contextual equivalence of arbitrary implementations. -/
inductive Related : Term s → Target.Term s → Prop where
  | unit : Related .unit .unit
  | int : Related (.int n) (.int n)
  | bool : Related (.bool b) (.bool b)
  | string : Related (.string s) (.string s)
  | pair : Related a x → Related b y → Related (.pair a b) (.pair x y)
  | inl : Related v w → Related (.inl a v) (.inl a.erase w)
  | inr : Related v w → Related (.inr a v) (.inr a.erase w)
  | tag : Related v w → Related (.tag l v) (.tag l w)
  | pack : Related v w → Related (.pack u a v) (.pack u.erase a.erase w)
  | fold : Related v w → Related (.fold a v) (.fold a.erase w)
  | nil : Related .nil .nil
  | cons : Related v w → Related vs ws → Related (.cons l v vs) (.cons l w ws)
  | record : Related fs gs → gs.toList.Perm hs.toList → Related (.record fs) (.record hs)
  | clo : Related c C → Elaborates b B → Related (.clo c a b) (.clo C a.erase B)
  | rclo : Related c C → Elaborates e E → Related (.rclo c a b e) (.rclo C a.erase b.erase E)
  | tclo : Related c C → Elaborates e E → Related (.tclo c k g e) (.tclo C k g.erase E)
  | moduleCaptured : Related (.record fs) C → Elaborates body B →
      Related (.moduleVal (.record fs) c i o body)
        (.clo (.pair .unit C) (.record i.erase) (.box (.merge (.ix 1) (.ix 0)) B))
  | moduleSandbox : Elaborates body B → Related (.moduleVal (.record .nil) .empty i o body)
      (.clo .unit (.record i.erase) (.box (.ix 0) B))
  | resid : Related m M → Related saved S →
      Related (.resid m saved j k o)
        (.clo (.pair M S) (.record k.erase) Templates.residualBody)
end

end LeanSce.Source

/-! ## Goals -/

/-! Main statements as propositions, never proof assumptions. Safety and
    elaboration typing and execution correspondence are proved in their
    corresponding modules. -/
namespace LeanSce.Source.Goals

/-- Full open-context type preservation of elaboration. -/
def ElaborationTyping : Prop :=
  ∀ (Δ : Context) (h a : Typ) (e : Expr) (E : Target.Expr),
    Context.Valid Δ → HasType Δ h e a → Elaborates e E →
    Target.HasType Δ.erase h.erase E a.erase

def Preservation : Prop :=
  ∀ (ν e e' : Expr) (h a : Typ), ValueType .empty ν h → HasType .empty h e a →
    Step ν e e' → HasType .empty h e' a

def Progress : Prop :=
  ∀ (ν e : Expr) (h a : Typ), ValueType .empty ν h → HasType .empty h e a →
    Value e ∨ ∃ e', Step ν e e'

/-- S1.5 exactly as two implications, retaining open contexts and closing
    substitutions. No typing premise is added for the quantified result value. -/
def TerminationCorrespondence : Prop :=
  ∀ (Δ : Context) (h a : Typ) (e ν : Expr) (E N : Target.Expr) (θ : Subst),
    Context.Valid Δ → HasType Δ h e a → Elaborates e E → Closing θ Δ →
    ValueType .empty ν (h.subst θ) → Related ν N →
    (∀ v, Terminates ν (e.subst θ) v →
      ∃ V, Target.Terminates N (E.subst (Subst.erase θ)) V ∧ Related v V) ∧
    (∀ V, Target.Terminates N (E.subst (Subst.erase θ)) V →
      ∃ v, Terminates ν (e.subst θ) v ∧ Related v V)

/-- S1.6 under the same hypotheses. -/
def DivergenceCorrespondence : Prop :=
  ∀ (Δ : Context) (h a : Typ) (e ν : Expr) (E N : Target.Expr) (θ : Subst),
    Context.Valid Δ → HasType Δ h e a → Elaborates e E → Closing θ Δ →
    ValueType .empty ν (h.subst θ) → Related ν N →
    (Diverges ν (e.subst θ) ↔ Target.Diverges N (E.subst (Subst.erase θ)))

end LeanSce.Source.Goals

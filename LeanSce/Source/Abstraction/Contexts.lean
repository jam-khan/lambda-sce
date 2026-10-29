import LeanSce.Source.Elaboration.Contexts
import LeanSce.Source.Elaboration.Representations
import LeanSce.Source.Elaboration.Typing
import LeanSce.Source.Metatheory.Basic
import LeanSce.Source.Metatheory.CanonicalForms
import LeanSce.Target.LogicalRelation.Contexts

/-!
# Source / Abstraction / Contexts

Proofs and supporting constructions for contexts.
-/

/-! ## Representation Context Values -/

namespace LeanSce.Source

/-- Value positions are preserved when both fillings of every hole have the
    same value status. This includes the runtime residual value-priority rule. -/
theorem Compatible.isValue_eq (hc : Compatible R Δ h e E a)
    (hR : ∀ Δ h e E a, R Δ h e E a → e.isValue = E.isValue) :
    e.isValue = E.isValue := by
  apply Compatible.rec
    (motive_1 := fun _ _ e E _ _ => e.isValue = E.isValue)
    (motive_2 := fun _ _ fs Fs _ _ => fs.isValue = Fs.isValue)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (t := hc)
  all_goals intros
  case hole => rename_i Δ h e a E he hE hr; exact hR Δ h e E a hr
  case moduleVal =>
    rename_i hh hv hV hcap hi ho hd hb ihcap ihb
    obtain ⟨fs,rfl⟩ := hcap.left_typed.value_shape hv
    obtain ⟨gs,rfl⟩ := hcap.right_typed.value_shape hV
    simpa only [Term.isValue] using ihcap
  all_goals simp_all [Value,Term.isValue]

end LeanSce.Source

/-! ## Representation Contexts -/

namespace LeanSce.Source

abbrev TargetRelation := Target.Context → Target.Typ → Target.Expr → Target.Expr → Target.Typ → Prop

def ContextArtifacts (S : TargetRelation) (Δ : Context) (h : Typ) (e E : Expr) (a : Typ) : Prop :=
  ∃ F G, Elaborates e F ∧ Elaborates E G ∧ Target.Compatible S Δ.erase h.erase F G a.erase

def FieldArtifacts (S : TargetRelation) (Δ : Context) (h : Typ) (fs Fs : Fields) (r : Row) : Prop :=
  ∃ F G, Elaborates fs F ∧ Elaborates Fs G ∧ Target.CompatibleFields S Δ.erase h.erase F G r.erase

def CertificateArtifacts (S : TargetRelation) (Δ : Context) (a b : Typ) (cd CD : Expr) : Prop :=
  ∃ F G, Elaborates cd F ∧ Elaborates CD G ∧
    ∀ h, Target.WellFormed Δ.erase h → Target.Compatible S Δ.erase h F G (.arr a.erase b.erase)

private theorem validAll (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.all k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | all hf hg _ => exact .extend hΔ hf hg

private theorem validEx (hΔ : Context.Valid Δ) (hw : WellFormed Δ (.ex k gs a)) :
    Context.Valid (Δ.extend k gs) := by
  cases hw with | ex hf hg _ => exact .extend hΔ hf hg

/-- Compile the observation context with its chosen runtime representatives in
    the holes. The compilation is permitted to choose either legal empty-module
    representation, and preserves all source value-restricted positions. -/
theorem Compatible.representation_context (hc : Compatible R Δ h e E a)
    (hR : ∀ Δ h e E a, Context.Valid Δ → HasType Δ h e a → HasType Δ h E a →
      R Δ h e E a → ContextArtifacts S Δ h e E a)
    (hvalues : ∀ Δ h e E a, R Δ h e E a → e.isValue = E.isValue)
    (hS : ∀ Δ h e E a, S Δ h e E a → ∀ H, Target.WellFormed Δ H → S Δ H e E a) :
    Context.Valid Δ → ContextArtifacts S Δ h e E a := by
  apply Compatible.rec
    (motive_1 := fun Δ h e E a _ => Context.Valid Δ → ContextArtifacts S Δ h e E a)
    (motive_2 := fun Δ h fs Fs r _ => Context.Valid Δ → FieldArtifacts S Δ h fs Fs r)
    (motive_3 := fun Δ a b cd CD _ => Context.Valid Δ → CertificateArtifacts S Δ a b cd CD)
    (t := hc)
  all_goals intros
  all_goals intros
  case hole => rename_i Δ h e a E he hE hh hΔ; exact hR Δ h e E a hΔ he hE hh
  case query => rename_i hh hΔ; exact ⟨_,_,.canonical,.canonical,.query hh.erase⟩
  case unit => rename_i hh hΔ; exact ⟨_,_,.canonical,.canonical,.unit hh.erase⟩
  case int => rename_i hh hΔ; exact ⟨_,_,.canonical,.canonical,.int hh.erase⟩
  case bool => rename_i hh hΔ; exact ⟨_,_,.canonical,.canonical,.bool hh.erase⟩
  case string => rename_i hh hΔ; exact ⟨_,_,.canonical,.canonical,.string hh.erase⟩
  case pair =>
    rename_i hx hy ihx ihy hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihy hΔ
    exact ⟨_,_,.pair hF hX,.pair hG hY,.pair hfg hxy⟩
  case fst =>
    rename_i hx ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.fst hF,.fst hG,.fst hfg⟩
  case snd =>
    rename_i hx ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.snd hF,.snd hG,.snd hfg⟩
  case box =>
    rename_i hx hb ihx ihb hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihb hΔ
    exact ⟨_,_,.box hF hX,.box hG hY,.box hfg hxy⟩
  case lam =>
    rename_i wa hb ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.lam hF,.lam hG,.lam wa.erase hfg⟩
  case recfn =>
    rename_i wa wb hb ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.recfn hF,.recfn hG,.recfn wa.erase wb.erase hfg⟩
  case app =>
    rename_i hf hx ihf ihx hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihf hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihx hΔ
    exact ⟨_,_,.app hF hX,.app hG hY,.app hfg hxy⟩
  case inl =>
    rename_i wb hx ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.inl hF,.inl hG,.inl wb.erase hfg⟩
  case inr =>
    rename_i wa hx ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.inr hF,.inr hG,.inr wa.erase hfg⟩
  case case =>
    rename_i hx hl hr ihx ihl ihr hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihl hΔ
    obtain ⟨U,V,hU,hV,huv⟩ := ihr hΔ
    exact ⟨_,_,.case hF hX hU,.case hG hY hV,.case hfg hxy huv⟩
  case tag =>
    rename_i hx ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.tag hF,.tag hG,.tag hfg⟩
  case find =>
    rename_i hx hu ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.find hF,.find hG,.find hfg hu.erase⟩
  case record =>
    rename_i hf ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.record hF,.record hG,.record hfg⟩
  case get =>
    rename_i hx hl ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.get hF,.get hG,.get hfg (by simp [hl])⟩
  case merge =>
    rename_i hx hy hd ihx ihy hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihy hΔ
    exact ⟨_,_,.merge hF hX,.merge hG hY,.merge hfg hxy hd.erase⟩
  case take =>
    rename_i hx hn hl ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    refine ⟨_,_,.take hF,.take hG,?_⟩
    simpa only [Ty.erase,Ty.erase_select] using Target.Compatible.take hfg hn (fun l hm => by
      obtain ⟨a,ha⟩ := hl l hm
      exact ⟨a.erase,by simp [ha]⟩)
  case drop =>
    rename_i hx hn hl ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    refine ⟨_,_,.drop hF,.drop hG,?_⟩
    simpa only [Ty.erase,Ty.erase_drop] using Target.Compatible.drop hfg hn (fun l hm => by
      obtain ⟨a,ha⟩ := hl l hm
      exact ⟨a.erase,by simp [ha]⟩)
  case relabel =>
    rename_i Δ h x X r l a k hx hl hn hd ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    refine ⟨_,_,.relabel hF,.relabel hG,?_⟩
    simpa only [Ty.erase,Ty.erase_relabel] using Target.Compatible.relabel (a:=a.erase) hfg
      (by simp [hl]) hn (by simpa only [Ty.erase,Ty.erase_drop] using hd.erase)
  case tlam =>
    rename_i hw hh hb ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih (validAll hΔ hw)
    refine ⟨_,_,.tlam hF,.tlam hG,.tlam hw.erase hh.erase ?_⟩
    simpa only [Context.erase_extend,Ty.erase_rename] using hfg
  case tapp =>
    rename_i hx hk hu hg ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    refine ⟨_,_,.tapp hF,.tapp hG,?_⟩
    simpa only [Ty.erase_open] using Target.Compatible.tapp hfg (by simpa using hk)
      hu.erase (by simpa using hg.erase)
  case pack =>
    rename_i hw hk hu hg hx ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.pack hF,.pack hG,.pack hw.erase (by simpa using hk) hu.erase
      (by simpa using hg.erase) (by simpa only [Ty.erase_open] using hfg)⟩
  case unpack =>
    rename_i hx wb hb ihx ihb hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihb (validEx hΔ (hx.left_typed.result_wf hΔ))
    exact ⟨_,_,.unpack hF hX,.unpack hG hY,.unpack hfg wb.erase
      (by simpa only [Context.erase_extend,Ty.erase,Ty.erase_rename] using hxy)⟩
  case fold =>
    rename_i hw hx ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.fold hF,.fold hG,.fold hw.erase (by simpa only [Ty.erase_open,Ty.erase,Arg.erase] using hfg)⟩
  case unfold =>
    rename_i hx ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    refine ⟨_,_,.unfold hF,.unfold hG,?_⟩
    simpa only [Ty.erase_open,Ty.erase,Arg.erase] using Target.Compatible.unfold hfg
  case add =>
    rename_i hx hy ihx ihy hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihy hΔ
    exact ⟨_,_,.prim (.cons hF (.cons hX .canonical)),.prim (.cons hG (.cons hY .canonical)),.add hfg hxy⟩
  case eqInt =>
    rename_i hx hy ihx ihy hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihy hΔ
    exact ⟨_,_,.prim (.cons hF (.cons hX .canonical)),.prim (.cons hG (.cons hY .canonical)),.eqInt hfg hxy⟩
  case concat =>
    rename_i hx hy ihx ihy hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihy hΔ
    exact ⟨_,_,.prim (.cons hF (.cons hX .canonical)),.prim (.cons hG (.cons hY .canonical)),.concat hfg hxy⟩
  case showInt =>
    rename_i hx ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.prim (.cons hF .canonical),.prim (.cons hG .canonical),.showInt hfg⟩
  case ite =>
    rename_i hc hx hy ihc ihx ihy hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihc hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihx hΔ
    obtain ⟨U,V,hU,hV,huv⟩ := ihy hΔ
    exact ⟨_,_,.ite hF hX hU,.ite hG hY hV,.ite hfg hxy huv⟩
  case clo =>
    rename_i hh wa hv hV hcap hb ihcap ihb hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihcap hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihb hΔ
    exact ⟨_,_,.value (.clo (hF.value_related hv) hX),.value (.clo (hG.value_related hV) hY),
      .clo hh.erase wa.erase (hF.value_preservation hv) (hG.value_preservation hV) hfg hxy⟩
  case rclo =>
    rename_i hh wa wb hv hV hcap hb ihcap ihb hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihcap hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihb hΔ
    exact ⟨_,_,.value (.rclo (hF.value_related hv) hX),.value (.rclo (hG.value_related hV) hY),
      .rclo hh.erase wa.erase wb.erase (hF.value_preservation hv) (hG.value_preservation hV) hfg hxy⟩
  case tclo =>
    rename_i hh hw hv hV hcap hb ihcap ihb hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihcap hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihb (validAll hΔ hw)
    exact ⟨_,_,.value (.tclo (hF.value_related hv) hX),.value (.tclo (hG.value_related hV) hY),
      .tclo hh.erase hw.erase (hF.value_preservation hv) (hG.value_preservation hV) hfg
        (by simpa only [Context.erase_extend,Ty.erase_rename] using hxy)⟩
  case letVal =>
    rename_i wa hx hb ihx ihb hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihb hΔ
    exact ⟨_,_,.letVal hF hX,.letVal hG hY,Templates.letIn_compatible hfg hxy⟩
  case view =>
    rename_i hx hc ihx ihc hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihc hΔ
    exact ⟨_,_,.view hX hF,.view hY hG,.app (hxy _ hx.left_typed.ambient_wf.erase) hfg⟩
  case module =>
    rename_i hh hi ho hb ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.module hF,.module hG,Templates.sandbox_compatible hh.erase hi.erase hfg⟩
  case capture =>
    rename_i hc hi ho hd hb ihc ihb hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihc hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihb hΔ
    exact ⟨_,_,.capture hF hX,.capture hG hY,.app
      (Templates.captured_compatible hc.left_typed.ambient_wf.erase
        (hc.left_typed.result_wf hΔ).record_row.erase hi.erase hd.erase hxy) hfg⟩
  case run =>
    rename_i hm hp hc ihm ihp ihc hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihm hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihp hΔ
    obtain ⟨U,V,hU,hV,huv⟩ := ihc hΔ
    have hw := hm.left_typed.result_wf hΔ
    exact ⟨_,_,.run hU hF hX,.run hV hG hY,.app (.app
      (Templates.run_compatible hm.left_typed.ambient_wf.erase
        (hp.left_typed.result_wf hΔ).record_row.erase hw.module_imports.erase hw.module_exports.erase huv)
      hfg) hxy⟩
  case link =>
    rename_i hp hm hc hd ihp ihm ihc hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihp hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihm hΔ
    obtain ⟨U,V,hU,hV,huv⟩ := ihc hΔ
    have hw := hm.left_typed.result_wf hΔ
    exact ⟨_,_,.link hU hF hX,.link hV hG hY,.app (.app
      (Templates.link_compatible hp.left_typed.ambient_wf.erase
        (hp.left_typed.result_wf hΔ).record_row.erase hw.module_imports.erase hw.module_exports.erase hd.erase huv)
      hfg) hxy⟩
  case provide =>
    rename_i hp hm hc hj hk hd ihp ihm ihc hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihp hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihm hΔ
    obtain ⟨U,V,hU,hV,huv⟩ := ihc hΔ
    exact ⟨_,_,.provide hU hF hX,.provide hV hG hY,.app (.app
      (Templates.provide_compatible hp.left_typed.ambient_wf.erase
        (hp.left_typed.result_wf hΔ).record_row.erase hj.erase hk.erase
        (hm.left_typed.result_wf hΔ).module_exports.erase hd.erase huv) hfg) hxy⟩
  case complete =>
    rename_i hm ihm hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihm hΔ
    refine ⟨_,_,.complete hF,.complete hG,.app (.app ?_ hfg) (.record (.nil hm.left_typed.ambient_wf.erase))⟩
    apply Templates.run_compatible hm.left_typed.ambient_wf.erase .empty .empty
      (hm.left_typed.result_wf hΔ).module_exports.erase
    intro H hH
    exact .box (.unit hH) (.lam (.record .empty) (.snd (.query (.prod .unit (.record .empty)))))
  case moduleVal =>
    rename_i hh vc vC hc hi ho hd hb ihc ihb hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihc hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihb hΔ
    obtain ⟨fs,rfl⟩ := hc.left_typed.value_shape vc
    obtain ⟨gs,rfl⟩ := hc.right_typed.value_shape vC
    exact ⟨_,_,.value (.moduleCaptured (hF.value_related vc) hX),
      .value (.moduleCaptured (hG.value_related vC) hY),
      Templates.module_value_compatible hh.erase hi.erase hfg
        (hF.value_preservation vc) (hG.value_preservation vC) hd.erase hxy hΔ.erase⟩
  case resid =>
    rename_i m M Δ j k o h saved SAVED vm vM hm hs hj hk hd ihm ihs hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihm hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihs hΔ
    have hM := hF.value_related vm
    have hN := hG.value_related vM
    have hval := hs.isValue_eq hvalues
    have hh := hs.left_typed.ambient_wf
    have ho := (hm.left_typed.result_wf hΔ).module_exports
    by_cases hv : Value saved
    · have hV : Value SAVED := by simpa only [Value,hval] using hv
      have hxy' := hxy.value_reambient (hX.value_preservation hv) (hY.value_preservation hV) hS .unit .unit
      exact ⟨_,_,.value (.resid hM (hX.value_related hv)),.value (.resid hN (hY.value_related hV)),
        Templates.residual_value_compatible hh.erase hj.erase hk.erase ho.erase hd.erase hfg hxy'
          hM.values.2 hN.values.2 (hX.value_preservation hv) (hY.value_preservation hV)⟩
    · have hV : ¬ Value SAVED := by simpa only [Value,hval] using hv
      have hfg' := hfg.value_reambient hM.values.2 hN.values.2 hS h.erase hh.erase
      exact ⟨_,_,.resid hM hv hX,.resid hN hV hY,.app (.app
        (Templates.residual_compatible hh.erase hj.erase hk.erase ho.erase hd.erase) hfg') hxy⟩
  case invoke =>
    rename_i hm hp ihm ihp hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihm hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihp hΔ
    exact ⟨_,_,.invoke hF hX,.invoke hG hY,.app hfg hxy⟩
  case value =>
    rename_i hv hV hc hh ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    exact ⟨_,_,.value (hF.value_related hv),.value (hG.value_related hV),
      .value (hF.value_preservation hv) (hG.value_preservation hV) hfg hh.erase⟩
  case nil => rename_i hh hΔ; exact ⟨_,_,.canonical,.canonical,.nil hh.erase⟩
  case cons =>
    rename_i hx hf hd ihx ihf hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ihx hΔ
    obtain ⟨X,Y,hX,hY,hxy⟩ := ihf hΔ
    exact ⟨_,_,.cons hF hX,.cons hG hY,.cons hfg hxy hd.erase⟩
  case closed =>
    rename_i hc hC hb ih hΔ
    obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
    refine ⟨_,_,.box .canonical hF,.box .canonical hG,?_⟩
    intro H hH
    exact .box (.unit hH) hfg
  all_goals first
    | (rename_i hx he wb ih hΔ
       obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
       exact ⟨F,G,hF,hG,Target.Compatible.conv hfg he.erase wb.erase⟩)
    | (rename_i hf he wb ih hΔ
       obtain ⟨F,G,hF,hG,hfg⟩ := ih hΔ
       exact ⟨F,G,hF,hG,Target.CompatibleFields.conv hfg he.erase wb.erase⟩)

end LeanSce.Source

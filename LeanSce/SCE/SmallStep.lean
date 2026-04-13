import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics

open SCE S_Sem

inductive SStep : Exp → Exp → Exp → Prop where
  | ssquery {v}
    : Value v
    -> SStep v .query v
  | ssappl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.app e1 e2) (.app e1' e2)
  | ssboxl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.box e1 e2) (.box e1' e2)
  | ssmrgl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.mrg e1 e2) (.mrg e1' e2)
  | ssappr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep v e2 e2'
    → SStep v (.app v1 e2) (.app v1 e2')
  | ssboxr
    : Value v
    → Value v1
    → SStep v1 e2 e2'
    → SStep v (.box v1 e2) (.box v1 e2')
  | ssmrgr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep (.mrg v v1) e2 e2'
    → SStep v (.mrg v1 e2) (.mrg v1 e2')
  | ssclos {v A e}
    : Value v
    → SStep v (.lam A e) (.clos v A e)
  | ssbeta {v v1 v2 A e}
    : Value v
    → Value v1
    → Value v2
    → SStep v (.app (.clos v2 A e) v1) (.box (.mrg v2 v1) e)
  | ssboxv {v v1 v2}
    : Value v
    → Value v1
    → Value v2
    → SStep v (.box v1 v2) v2
  | ssproj {v e1 e2 n}
    : Value v
    → SStep v e1 e2
    → SStep v (.proj e1 n) (.proj e2 n)
  | ssprojv {v v1 n v2}
    : Value v
    → Value v1
    → LookupV v1 n v2
    → SStep v (.proj v1 n) v2
  | sslrec {v e1 e2 l}
    : Value v
    → SStep v e1 e2
    → SStep v (.lrec l e1) (.lrec l e2)
  | ssrproj
    : Value v
    → SStep v e1 e2
    → SStep v (.rproj e1 l) (.rproj e2 l)
  | ssrprojv {v v1 l v2}
    : Value v
    → Value v1
    → Sel v1 l v2
    → SStep v (.rproj v1 l) v2
  | ssmstruct_sandboxed {v e e'}
    : Value v
    → SStep .unit e e'
    → SStep v (.mstruct .sandboxed e) (.mstruct .sandboxed e')
  | ssmstruct_open {v e e'}
    : Value v
    → SStep v e e'
    → SStep v (.mstruct .open_ e) (.mstruct .open_ e')
  | ssmstructv_sandboxed {v v'}
    : Value v
    → Value v'
    → SStep v (.mstruct .sandboxed v') v'
  | ssmstructv_open {v v'}
    : Value v
    → Value v'
    → SStep v (.mstruct .open_ v') v'
  | ssmfunctor_sandboxed {v : Exp} {A : Typ} {e : Exp}
    : Value v
    → SStep v (.mfunctor .sandboxed A e) (.mclos .unit A e)
  | ssmfunctor_open {v : Exp} {A : Typ} {e : Exp}
    : Value v
    → SStep v (.mfunctor .open_ A e) (.mclos v A e)
  | ssmappl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.mapp e1 e2) (.mapp e1' e2)
  | ssmappr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep v e2 e2'
    → SStep v (.mapp v1 e2) (.mapp v1 e2')
  | ssmbeta {v v1 v2 A e}
    : Value v
    → Value v1
    → Value v2
    → SStep v (.mapp (.mclos v2 A e) v1) (.box (.mrg v2 v1) e)
  | ssnmrgl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.nmrg e1 e2) (.nmrg e1' e2)
  | ssnmrgr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep v e2 e2'
    → SStep v (.nmrg v1 e2) (.nmrg v1 e2')
  | ssnmrgv {v v1 v2}
    : Value v
    → Value v1
    → Value v2
    → SStep v (.nmrg v1 v2) (.mrg v1 v2)
  | ssletbl {v e1 e1' e2 A}
    : Value v
    → SStep v e1 e1'
    → SStep v (.letb e1 A e2) (.letb e1' A e2)
  | ssletbv {v v1 A e2}
    : Value v
    → Value v1
    → SStep v (.letb v1 A e2) (.box (.mrg v v1) e2)
  | ssmlinkl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.mlink e1 e2) (.mlink e1' e2)
  | ssmlinkr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep v e2 e2'
    → SStep v (.mlink v1 e2) (.mlink v1 e2')
  | ssmlinkbeta {v v1 v2 vl A body l}
    : Value v
    → Value v1
    → Value v2
    → Sel v1 l vl
    → SStep v (.mlink v1 (.mclos v2 (.rcd l A) body))
              (.mrg v1 (.box (.mrg v2 (.lrec l vl)) body))
  | ssopenml {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.openm e1 e2) (.openm e1' e2)
  | ssopenm {v v' e2 l}
    : Value v
    → Value v'
    → SStep v (.openm (.lrec l v') e2) (.box (.mrg v v') e2)

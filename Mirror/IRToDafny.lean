import Lean
import Mirror.IR
import Mirror.Dafny
import Mirror.Extension

namespace Lean.ToDafny

-- The return needs to be transformed
-- pure exp
-- into
-- o := exp ; return

def subst (fro to : String) (e : Expression): MetaM Expression := do
  match e with
  | .name n => if n = fro then return .name to else return e
  | .letb n rhs body => if n = fro then return .letb to rhs body else return e
  | _=> return e

def inline (e : Expression) : MetaM Expression := do
  match e with
  | .bind (.prob_while cond (.monadic callee args) init) (.lam binder body) =>
    let st : State := extension.getState (← getEnv)
    if callee ∈ st.inlines
    then
      if let some defn := st.glob.find? callee
      then
        let body' ← defn.body.map (subst "o" binder)
        return .bind (.prob_while cond body' init) (.lam binder body)
      else throwError "Definition is in list of inlines but not exported"
    else return e
  | _ => return e

partial def Expression.toStatements (e : Expression) : MetaM (List Statement) := do
  match e with
  | tr => throwError "toStatements: unexpected expression tr {e}"
  | fa => throwError "toStatements: unexpected expression fa {e}"
  | num val => throwError "toStatements: unexpected expression num {e}"
  | str s => throwError "toStatements: unexpected expression str {e}"
  | app f args => throwError "toStatements: unexpected expression app {e}"
  | letb v rhs body => return ((.assignment v rhs) :: (← body.toStatements))
  | ite cond (.throw msg) right =>
    let s1 : Statement := .expect cond msg
    return s1 :: (← right.toStatements)
  | ite cond left right => return [.conditional cond (← left.toStatements) (← right.toStatements)]
  | bind (.prob_while (.lam binder1 cond) body init) (.lam binderk bodyk) =>
    let s_tmp : Expression := (.prob_while (.lam binder1 cond) body init)
    let s1 : List Statement ← s_tmp.toStatements
    let s2 : Statement := .assignment binderk (.name binder1)
    let s3 : List Statement ← bodyk.toStatements
    return s1 ++ [s2] ++ s3
  | bind (.prob_until body1 (.lam binder1 bodyin)) (.lam binder2 body2) =>
    let s_tmp : Expression := (.prob_until body1 (.lam binder1 bodyin))
    let s1 : List Statement ← s_tmp.toStatements
    let s2 : Statement := .assignment binder2 (.name binder1)
    let s3 : List Statement ← body2.toStatements
    return s1 ++ [s2] ++ s3
  | bind v (.lam binder body) =>
    let s1 : Statement := .assignment binder v -- v could be prob_while or prob_until expression
    return s1 :: (← body.toStatements)
  | bind v body => throwError "toStatements: to do {e}"
  | lam v body => throwError "toStatements: unexpected expression lam {e}"
  | pure e => return [.ret e]
  | throw e => throwError "toStatements: unexpected expression throw {e}"
  | prob_until body (.lam binder cond) =>
    let s1 : Statement := .assignment binder body
    let s2 : List Statement ← body.toStatements
    -- condition needs to be substituted
    let s3 : Statement := .loop cond s2
    return [s1] ++ [s3]
  | prob_until body cond => throwError "toStatements: to do {e}"
  | prob_while (.lam state cond) body init =>
    let s1 : Statement := .assignment state init
    let s2 : List Statement ← body.toStatements
    -- condition needs to be substituted
    let s3 : Statement := .loop cond s2
    return [s1] ++ [s3]
  | prob_while cond body init => throwError "toStatements: to do {e}"
  | name n => throwError "toStatements: unexpected expression name {e}"
  | unop op rhs => throwError "toStatements: unexpected expression unop {e}"
  | binop op lhs rhs => throwError "toStatements: unexpected expression binop {e}"
  | proj id idx => throwError "toStatements: unexpected expression proj {e}"
  | pair left right => throwError "toStatements: unexpected expression pair {e}"
  | monadic n e => throwError "toStatements: unexpected expression monadic {e}"

def Expression.pipeline (body : Expression) : MetaM (List Statement) := do
  let body1 ← body.map inline
  body1.toStatements

def CodeGen (pi : RandomMDef) : MetaM Method := do
  return {
    name := pi.name,
    inParamType := pi.inParamType,
    outParamType := pi.outParamType,
    inParam := pi.inParam,
    body := ← pi.body.pipeline
  }

end Lean.ToDafny

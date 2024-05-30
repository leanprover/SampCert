/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Lean
import SampCert.Extractor.IR
import SampCert.Extractor.Extension
import SampCert.Extractor.Abstract

import Mathlib.Data.Nat.Log
import Mathlib.Data.PNat.Defs

namespace Lean.ToDafny

/--
Check if the program is a tuple, whose first element is of type Capsid.
-/
def readCapsid (e : Expr) : MetaM (Option (Name × Expr)) :=
  IO.println s!" - Reading Capsid {e}" >>= fun _ =>
  match e with
  | .app (.app (.const ``Prod [1, 0]) (.app (.const ``Capsid _) (.const t _))) f => do
    return (some (t, f))
  | _ => return none

def readCapsidProg (e : Expr) : MetaM (Option (Name × Name)) :=
  IO.println s!" - Reading Capsid Program {e}" >>= fun _ =>
  match e with
  | .app (.app _ (.const e1 _)) (.const e2 _) => return some (e1, e2)
  | _ => do
    IO.println s!"Capsid program read failure"
    return none

def IsWFMonadic (capsidM : Name) (e: Expr) : MetaM Bool :=
  IO.println s!" - Checking if {e} is WF monadic" >>= fun _ =>
  match e with
  | .app (.const n ..) _ => return (n = capsidM)
  | .app .. => return true -- Need to work out details of this one, related to translation of dependent types
  | .forallE _ _ range _ => IsWFMonadic capsidM range
  | _ => return false -- throwError "IsWFMonadic {e}"

def chopLambda (e : Expr) : Expr :=
  match e with
  | .lam _ _ body _ => body
  | _ => e

mutual

partial def toDafnyTyp (capsidM : Name) (env : List String) (e : Expr) : MetaM Typ := do
  match e with
  | .bvar .. => throwError "toDafnyTyp: not supported -- bound variable {e}"
  | .fvar .. => throwError "toDafnyTyp: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyTyp: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyTyp: not supported -- sort {e}"
  | .const ``Nat .. => return .nat
  | .const ``PNat .. => return .pos
  | .const ``Bool .. => return .bool
  | .const ``Int .. => return .int
  | .const .. => throwError "toDafnyTyp: not supported -- constant {e}"
  | .app .. => (e.withApp fun fn args => do
      if let .const name .. := fn then
      match name with
      | ``Prod => return .prod (← toDafnyTyp capsidM env args[0]!) (← toDafnyTyp capsidM env args[1]!)
      | ``Capsid => return (← toDafnyTyp capsidM env args[0]!)
      | _ => return .dependent (← toDafnyExpr capsidM "dummycalledfromtoDafnyTyp" env e)
      else throwError "toDafnyExpr: OOL {fn} {args}"
    )
  | .lam .. => throwError "toDafnyTyp: not supported -- lambda abstraction {e}"
  | .forallE .. => throwError "toDafnyTyp: not supported -- pi {e}"
  | .letE .. => throwError "toDafnyTyp: not supported -- let expressions {e}"
  | .lit .. => throwError "toDafnyTyp: not supported -- literals {e}"
  | .mdata .. => throwError "toDafnyTyp: not supported -- metadata {e}"
  | .proj .. => throwError "toDafnyTyp: not supported -- projection {e}"

partial def toDafnyExpr (capsidM : Name) (dname : String) (env : List String) (e : Expr) : MetaM Expression := do
  IO.println s!"      + translate {e}"
  match e with
  | .bvar i => return .name (env[i]!)
  | .fvar .. => throwError "toDafnyExpr: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyExpr: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyExpr: not supported -- sort {e}"
  | .const ``true .. => return .tr
  | .const ``false .. => return .fa
  | .const ``PUnit.unit .. => throwError "WF: all conditions are if then else, including the ones to throw errors"
  | .const .. => throwError "toDafnyExpr: not supported -- constant {e}"
  | .app .. => (e.withApp fun fn args => do
      if let .const name .. := fn then
      let info ← getConstInfo name
      match name with
      | ``pure => return .pure (← toDafnyExpr capsidM dname env args[3]!)
      | ``bind => return .bind (← toDafnyExpr capsidM dname env args[4]!) (← toDafnyExpr capsidM dname env args[5]!)
      | ``ite => return .ite (← toDafnyExpr capsidM dname env args[1]!) (← toDafnyExpr capsidM dname env args[3]!) (← toDafnyExpr capsidM dname env args[4]!)
      | ``dite => return .ite (← toDafnyExpr capsidM dname env args[1]!) (← toDafnyExpr capsidM dname ("dummy" :: env) (chopLambda args[3]!)) (← toDafnyExpr capsidM dname ("dummy" :: env) (chopLambda args[4]!))
      | ``throwThe => return .throw (← toDafnyExpr capsidM dname env args[4]!)
      | ``Capsid.capsWhile => return .prob_while (← toDafnyExpr capsidM dname env args[1]!) (← toDafnyExpr capsidM dname env args[2]!) (← toDafnyExpr capsidM dname env args[3]!)
      | ``OfNat.ofNat => toDafnyExpr capsidM dname env args[1]!
      | ``HAdd.hAdd => return .binop .addition (← toDafnyExpr capsidM dname env args[4]!) (← toDafnyExpr capsidM dname env args[5]!)
      | ``HSub.hSub => return .binop .substraction (← toDafnyExpr capsidM dname env args[4]!) (← toDafnyExpr capsidM dname env args[5]!)
      | ``HMul.hMul => return .binop .multiplication (← toDafnyExpr capsidM dname env args[4]!) (← toDafnyExpr capsidM dname env args[5]!)
      | ``HDiv.hDiv => return .binop .division (← toDafnyExpr capsidM dname env args[4]!) (← toDafnyExpr capsidM dname env args[5]!)
      | ``HPow.hPow => return .binop .pow (← toDafnyExpr capsidM dname env args[4]!) (← toDafnyExpr capsidM dname env args[5]!)
      | ``HMod.hMod => return .binop .mod (← toDafnyExpr capsidM dname env args[4]!) (← toDafnyExpr capsidM dname env args[5]!)
      | ``Eq => return .binop .equality (← toDafnyExpr capsidM dname env args[1]!) (← toDafnyExpr capsidM dname env args[2]!)
      | ``Ne => return .binop .inequality (← toDafnyExpr capsidM dname env args[1]!) (← toDafnyExpr capsidM dname env args[2]!)
      | ``And => return .binop .conjunction (← toDafnyExpr capsidM dname env args[0]!) (← toDafnyExpr capsidM dname env args[1]!)
      | ``Or => return .binop .disjunction (← toDafnyExpr capsidM dname env args[0]!) (← toDafnyExpr capsidM dname env args[1]!)
      | ``Not => return .unop .negation (← toDafnyExpr capsidM dname env args[0]!)
      | ``LT.lt => return .binop .least (← toDafnyExpr capsidM dname env args[2]!) (← toDafnyExpr capsidM dname env args[3]!)
      | ``LE.le => return .binop .leastequal (← toDafnyExpr capsidM dname env args[2]!) (← toDafnyExpr capsidM dname env args[3]!)
      | ``GT.gt => return .binop .greater (← toDafnyExpr capsidM dname env args[2]!) (← toDafnyExpr capsidM dname env args[3]!)
      | ``GE.ge => return .binop .greaterequal (← toDafnyExpr capsidM dname env args[2]!) (← toDafnyExpr capsidM dname env args[3]!)
      | ``Nat.log => return .binop .log (← toDafnyExpr capsidM dname env args[0]!) (← toDafnyExpr capsidM dname env args[1]!)
      | ``decide => toDafnyExpr capsidM dname env args[0]!
      | ``_root_.Rat.den => return .unop .denominator (← toDafnyExpr capsidM dname env args[0]!)
      | ``_root_.Rat.num => return .unop .numerator (← toDafnyExpr capsidM dname env args[0]!)
      | ``Nat.cast => toDafnyExpr capsidM dname env args[2]!
      | ``Int.cast => toDafnyExpr capsidM dname env args[2]!
      | ``Prod.fst => return .proj (← toDafnyExpr capsidM dname env args[2]!) 1
      | ``Prod.snd => return .proj (← toDafnyExpr capsidM dname env args[2]!) 2
      | ``Prod.mk => return .pair (← toDafnyExpr capsidM dname env args[2]!) (← toDafnyExpr capsidM dname env args[3]!)
      | ``Neg.neg => return .unop .minus (← toDafnyExpr capsidM dname env args[2]!)
      -- | ``abs => return .unop .abs (← toDafnyExpr capsidM dname env args[2]!)
      | ``Int.natAbs => return .unop .abs (← toDafnyExpr capsidM dname env args[0]!)
      | ``OfScientific.ofScientific => toDafnyExpr capsidM dname env args[4]!
      | ``PNat.val => toDafnyExpr capsidM dname env args[0]!
      | ``Subtype.mk => toDafnyExpr capsidM dname env args[2]!
      | ``Int.sub => return .binop .substraction (← toDafnyExpr capsidM dname env args[0]!) (← toDafnyExpr capsidM dname env args[1]!)
      | _ =>
        if ← IsWFMonadic capsidM info.type
        then
          let st : State := extension.getState (← getEnv)
          if let some defn := st.glob.find? name.toString
          then
            -- Translate only arguments that correspond to non-dependent types
            let args1 := defn.inParamType.zip args.toList
            let args2 := args1.filter (λ (x,_) => match x with | .dependent _ => false | _ => true)
            let args3 := args2.map (λ (_,y) => y)
            let args' ← args3.mapM (toDafnyExpr capsidM dname env)
            return .monadic name.toString args'
          else
            let args' ← args.mapM (toDafnyExpr capsidM dname env)
            return .monadic name.toString args'.toList
        else throwError "toDafnyExpr: not supported -- application of {fn} to {args}, info.type {info.type}"
      else if let .bvar _ := fn
          -- Coin...
           then return .monadic dname [(← toDafnyExpr capsidM dname env args[0]!)]
           else throwError "toDafnyExpr: OOL {fn} {args}"
    )
  | .lam binderName _ body _  => return (.lam binderName.toString (← toDafnyExpr capsidM dname (binderName.toString :: env) body))
  | .forallE .. => throwError "toDafnyExpr: not supported -- pi {e}"
  | .letE lhs _ rhs body _ => return (.letb lhs.toString (← toDafnyExpr capsidM dname env rhs) (← toDafnyExpr capsidM dname (lhs.toString :: env) body))
  | .lit (.natVal n) => return .num n
  | .lit (.strVal s) => return .str s
  | .mdata .. => throwError "toDafnyExpr: not supported -- meta {e}"
  | .proj .. => throwError "toDafnyExpr: not supported -- projection {e}"

end

def toDafnyTypTop (capsidM : Name) (env : List String) (e: Expr) : MetaM ((List Typ) × Typ) := do
  match e with
  | .forallE _ (.sort _) _ _ => throwError "toDafnyTypTop: Polymorphism not supported yet"
  | (.app (.const t ..) arg) =>
          if t = capsidM
            then return ([],← toDafnyTyp capsidM [] arg)
            else throwError "toDafnyTypTop: error on {e} (1)"
  | .forallE binder domain range _ =>
    let nenv := binder.toString :: env
    let r ← toDafnyTypTop capsidM nenv range
    return ((← toDafnyTyp capsidM env domain) :: r.1 , r.2)
  | _ => throwError "toDafnyTypTop: error on {e} (2)"

partial def toDafnyExprTop (capsidM : Name) (dname : String) (num_args : Nat) (names : List String) (e : Expr) : MetaM (List String × Expression) := do
  match e with
  | .bvar .. => throwError "toDafnyExprTop: not supported -- bound variable {e}"
  | .fvar .. => throwError "toDafnyExprTop: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyExprTop: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyExprTop: not supported -- sort {e}"
  | .const .. => throwError "toDafnyExprTop: not supported -- constant {e}"
  | .app .. =>
    e.withApp fun fn args =>
      match fn with
      | (.const ``WellFounded.fix ..) => toDafnyExprTop capsidM dname num_args names (args[4]!)
      -- Very wrong
      -- | (.const ``pure ..) => do
      --   let to_translate := args[3]!
      --   let de <- toDafnyExpr capsidM dname names to_translate
      --   IO.println s!" - PURE: translated value {to_translate}"
      --   return (names, de)
      | _ =>  throwError "toDafnyExprTop: not supported -- application {e}"
  | .lam binderName _ body _ =>
    let sig_names := names ++ [binderName.toString]
    if num_args = List.length names + 1
    then
      match body with
      | (.lam _ _ body _) => return (sig_names, ← toDafnyExpr capsidM dname ("dummy" :: sig_names.reverse) (chopLambda body))
      | _ => return (sig_names, ← toDafnyExpr capsidM dname sig_names.reverse body)
    else toDafnyExprTop capsidM dname num_args sig_names body
  | .forallE .. => throwError "toDafnyExprTop: not supported -- pi {e}"
  | .letE .. => throwError "toDafnyExprTop: not supported -- let expression {e}"
  | .lit .. => throwError "toDafnyExprTop: not supported -- literals {e}"
  | .mdata .. => throwError "toDafnyExprTop: not supported -- meta {e}"
  | .proj .. => throwError "toDafnyExprTop: not supported -- projection {e}"

def printParamTypes (params : List Typ) : String :=
  match params with
  | [] => ""
  | param :: params => s!"{param.print}, {printParamTypes params}"


/--
Entry point for converting a declaration (by name) into the IR

Expects a pair of a Capsid instance, and a program.
-/
def toDafnySLangDefIn (declName: Name) : MetaM MDef := do
  let info ← getConstInfo declName
  IO.println s!" - Working on {declName}"
  match info with
    | ConstantInfo.defnInfo _ =>
      IO.println s!" - Type: {info.type}"

      -- Try to read Capsid information
      let capsidV <- readCapsid (info.type)
      match capsidV with
      | some (capsidM, progT) => do
        IO.println s!" - Capsid monad: {capsidM}"
        let isMonadic <- (IsWFMonadic capsidM progT)
        if !isMonadic then throwError "Program type {progT} is not monadic"
        let (inParamTyp, outParamTyp) ← toDafnyTypTop capsidM [] progT
        let p <- readCapsidProg info.value!
        match p with
        | none => throwError "program is malformed (should be impossible if normalized)"
        | some (capsid_instance_name, program_name) => do
          IO.println s!" - Read Capsid instance name {capsid_instance_name}"
          IO.println s!" - Read program value name {program_name}"

          -- Now I need to get the program body from the program mane
          let progInfo <- getConstInfoDefn program_name
          IO.println s!" - Got program value {progInfo.value}"
          let capsidInfo <- getConstInfoDefn capsid_instance_name
          IO.println s!" - Got capsid value {capsidInfo.value}"

          let (inParam, body) ← toDafnyExprTop capsidM declName.toString (List.length inParamTyp) [] (progInfo.value)
          let defn := MDef.mk (declName.toString) inParamTyp outParamTyp inParam body
          return defn
      | _ => throwError "Failed to read Capsid information (1)"
    | _ => throwError "Failed to read Capsid information (2)"

end Lean.ToDafny

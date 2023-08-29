/- Copyright 2023 Daniel J. Velleman -/

import Lean.Elab.Tactic
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Rel
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs

def Iff.ltr {p q : Prop} (h : p ↔ q) := h.mp
def Iff.rtl {p q : Prop} (h : p ↔ q) := h.mpr

--New set theory notation.
--Lower priority than all other set theory notation
macro (priority := low-1) "{ " pat:term " : " t:term " | " p:term " }" : term =>
  `({ x : $t | match x with | $pat => $p })

macro (priority := low-1) "{ " pat:term " | " p:term " }" : term =>
  `({ x | match x with | $pat => $p })

@[app_unexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => match $y:ident with | $pat => $p) =>
      if x == y then
        `({ $pat:term | $p:term })
      else
        throw ()  --Or could use `({ $x:ident | match $y:ident with | $pat => $p})
  | `($_ fun ($x:ident : $ty:term) => match $y:ident with | $pat => $p) =>
      if x == y then
        `({ $pat:term : $ty:term | $p:term })
      else
        throw ()
  | _ => throw ()

--Make sure Lean understands {x} and ∅ as Sets, not Finsets
attribute [default_instance] Set.instSingletonSet
attribute [default_instance] Set.instEmptyCollectionSet

-- Set theory notation that should be in library.
-- Copying similar in:  Mathlib/Init/Set.lean, lean4/Init/Notation.lean, std4/Std/Classes/SetNotation.lean
notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

--Note:  Mathlib.Order.SymmDiff.lean defines this with ∆ (\increment) instead of △ (\bigtriangleup).
--But display of symmDiff seems to use △.
infixl:100 " △ " => symmDiff

namespace HTPI
--Some theorems not in library
theorem not_not_and_distrib {p q : Prop} : ¬(¬ p ∧ q) ↔ (p ∨ ¬ q) := by
  rw [not_and_or, Classical.not_not]

theorem not_and_not_distrib {p q : Prop} : ¬(p ∧ ¬ q) ↔ (¬ p ∨ q) := by
  rw [not_and_or, Classical.not_not]

theorem not_not_or_distrib {p q : Prop} : ¬(¬ p ∨ q) ↔ (p ∧ ¬ q) := by
  rw [not_or, Classical.not_not]

theorem not_or_not_distrib {p q : Prop} : ¬(p ∨ ¬ q) ↔ (¬ p ∧ q) := by
  rw [not_or, Classical.not_not]

theorem not_imp_not_iff_and {p q : Prop} : ¬ (p → ¬ q) ↔ p ∧ q := by
  rw [not_imp, Classical.not_not]

theorem not_imp_iff_not_and {p q : Prop} : ¬ (q → p) ↔ ¬ p ∧ q := by
  rw [not_imp]
  exact And.comm

theorem not_not_iff {p q : Prop} : ¬(¬p ↔ q) ↔ (p ↔ q) := by
  rw [not_iff, Classical.not_not]

def Pred (t : Type u) : Type u := t → Prop
def BinRel (t : Type u) : Type u := Rel t t

--Definitions of tactics
section tactic_defs
open Lean Elab Tactic Expr MVarId

--Syntax for arguments to tactics
syntax oneLoc := " at " ident
syntax colonTerm := " : " term
syntax withId := " with " ident
syntax with2Ids := " with " ident (", " ident)?
syntax idOrTerm := ident <|> ("(" term ")")
syntax idOrTerm?Type := ident <|> ("(" term (" : " term)? ")")

abbrev OneLoc := TSyntax ``oneLoc
abbrev ColonTerm := TSyntax ``colonTerm
abbrev WithId := TSyntax ``withId
abbrev With2Ids := TSyntax ``with2Ids
abbrev IdOrTerm := TSyntax ``idOrTerm
abbrev IdOrTerm?Type := TSyntax ``idOrTerm?Type

--Get formula from identifier
def formFromIdent (h : Syntax) : TacticM Expr := do
  instantiateMVars (← Meta.getLocalDeclFromUserName h.getId).type

--Get formula from optional location.  Note both formFromIdent and getMainTarget call instantiateMVars
def formFromLoc (l : Option OneLoc) : TacticM Expr := do
  match l with
    | some h => formFromIdent h.raw[1]
    | none => getMainTarget

--For debugging:
def myTrace (msg : String) : TacticM Unit := do
  let m := Syntax.mkStrLit msg
  evalTactic (← `(tactic| trace $m))

partial def SyntaxToString (s : Syntax) : String :=
match s with
  | .missing => "(missing)"
  | .node _ k as => "(node " ++ toString k ++ (SyntaxListToString as.data) ++ ")"
  | .atom _ v => "(atom " ++ toString v ++ ")"
  | .ident _ rv v _ => "(ident " ++ (toString rv) ++ " " ++ (toString v) ++ ")"
where SyntaxListToString (ss : List Syntax) : String :=
  match ss with
    | (s :: rest) => " " ++ (SyntaxToString s) ++ (SyntaxListToString rest)
    | [] => ""

def traceThisSyntax (s : Syntax) : TacticM Unit := myTrace (SyntaxToString s)

def binderString (bi : BinderInfo) : String :=
  match bi with
    | .default => "default"
    | _ => "not default"
    
def ExprToString (e : Expr) : String := 
match e with
  | .bvar n => "(bvar " ++ (toString n) ++ ")" -- bound variables
  | .fvar f => "(fvar " ++ (toString f.name) ++ ")"  -- free variables
  | .mvar m => "(mvar " ++ (toString m.name) ++ ")"   -- meta variables
  | .sort l => "(sort " ++ (toString l) ++ ")"   -- Sort
  | .const n ls => "(const " ++ (toString n) ++ " " ++ (toString ls) ++ ")"   -- constants
  | .app a b => "(app " ++ (ExprToString a) ++ " " ++ (ExprToString b) ++ ")" -- application
  | .lam n t b bi => "(lam " ++ (toString n) ++ " " ++ (ExprToString t) ++ " " ++ (ExprToString b) ++ " " ++ (binderString bi) ++ ")"    -- lambda abstraction
  | .forallE n t b bi => "(forallE " ++ (toString n) ++ " " ++ (ExprToString t) ++ " " ++ (ExprToString b) ++ " " ++ (binderString bi) ++ ")"  -- (dependent) arrow
  | .letE n t v b _ => "(let " ++ (toString n) ++ " " ++ (ExprToString t) ++ " "
        ++ (ExprToString v) ++ " " ++ (ExprToString b) ++ ")" -- let expressions
  | .lit _ => "(lit)"  -- literals
  | .mdata m e => "(mdata " ++ (toString m) ++ " " ++ (ExprToString e) ++ ")"   -- metadata
  | .proj t i c => "(proj " ++ (toString t) ++ " " ++ (toString i) ++ " " ++ (ExprToString c) ++ ")" -- projection

def traceThisExpr (e : Expr) : TacticM Unit := myTrace (ExprToString e)

elab "traceExpr" t:(colonTerm)? l:(oneLoc)? : tactic =>
  withMainContext do
    match t with
      | some tstx => do
        traceThisSyntax tstx.raw[1]
        let e ← elabTerm tstx.raw[1] none
        traceThisExpr e
      | none =>
        let e ← formFromLoc l
        traceThisExpr e

-- Get head and arg list
def getHeadData (e : Expr) : Expr × List Expr :=
  match e with
    | app f a =>
      let (h, as) := getHeadData f
      (h, a :: as)
    | mdata _ e' => getHeadData e'
    | _ => (e, [])

-- Recover expression from head and arg list
def mkAppList (h : Expr) (args : List Expr) : Expr :=
  match args with
    | a :: rest => mkApp (mkAppList h rest) a
    | [] => h

--Determine if e is a proposition, in current local context
def exprIsProp (e : Expr) : TacticM Bool :=
  return (← Meta.inferType e).isProp

--Logical form of a proposition.
inductive PropForm where
  | not     : Expr → PropForm
  | and     : Expr → Expr → PropForm
  | or      : Expr → Expr → PropForm
  | implies : Expr → Expr → PropForm
  | iff     : Expr → Expr → PropForm
  | all     : Name → Expr → Expr → BinderInfo → PropForm
  | ex      : Level → Name → Expr → Expr → BinderInfo → PropForm
  | exun    : Level → Name → Expr → Expr → BinderInfo → PropForm
  | f       : PropForm
  | t       : PropForm
  | none    : PropForm

/- Try to unfold definition, and if result is negative, return PropForm.not
Note:  Uses constants but not fvars with let declarations.  Also, only unfolds once.
This might be best--only detect expressions immediately recognized as negative by def.
-/
def findNegPropAll (e : Expr) : TacticM PropForm := do
  match (← Meta.unfoldDefinition? (consumeMData e)) with
    | some e' =>
      match getHeadData e' with
        | (const ``Not _, [l]) => return PropForm.not l
        | _ => return PropForm.none
    | none => return PropForm.none

--Apply a function to data for an existential.  Existentials usually apply to a
--lambda expression, but allow for others
def applyToExData {α : Type} (f : Level → Name → Expr → Expr → BinderInfo → α)
  (lev : Level) (l r : Expr) : α :=
  let r' := consumeMData r
  match r' with
    | lam v t b bi => f lev v t b bi
    | _ => f lev `x l (mkApp r' (bvar 0)) BinderInfo.default

-- Get logical form of a proposition.
-- Recognizes negative predicates by findNegPropAll.
def getPropForm (e : Expr) : TacticM PropForm := do
  if !(← exprIsProp e) then return PropForm.none
  let (h, args) := getHeadData e
  match h with
    | const c levs =>
      match (c, levs, args) with
        | (``False, _, _) => return PropForm.f
        | (``True, _, _) => return PropForm.t
        | (``Not, _, [l]) => return PropForm.not l
        | (``And, _, [r, l]) => return PropForm.and l r
        | (``Or, _, [r, l]) => return PropForm.or l r
        | (``Iff, _, [r, l]) => return PropForm.iff l r
        | (``Exists, [lev], [r, l]) => return applyToExData PropForm.ex lev l r
        | (``ExistsUnique, [lev], [r, l]) => return applyToExData PropForm.exun lev l r
        | _ => findNegPropAll e
    | forallE v t b bi =>
      if (b.hasLooseBVars || !(← exprIsProp t)) then
        return PropForm.all v t b bi
      else
        return PropForm.implies t b
    | _ => return PropForm.none

--mkNot, mkAnd, mkOr, and mkForall are already defined.  Also mkArrow and Meta.mkEq
def mkIff (l r : Expr) : Expr :=
  mkApp2 (mkConst ``Iff) l r

--Need to supply level--I always have it, so easiest to use it.
def mkExists (l : Level) (x : Name) (bi : BinderInfo) (t b : Expr) : Expr :=
  mkApp2 (mkConst ``Exists [l]) t (mkLambda x bi t b)

def myFail {α} (tac : Name) (msg : String) : TacticM α := do
  Meta.throwTacticEx tac (← getMainGoal) msg

/- Functions for unfolding head -/

--Unfold ExistsUnique; default version doesn't do a good job of naming variables
def unfoldExUn (lev : Level) (v : Name) (t b : Expr) (_ : BinderInfo) : Expr :=
  let v1 := Name.appendIndexAfter v 1
  let eqn := mkApp3 (mkConst ``Eq [lev]) t (bvar 1) (bvar 2)
  let body := mkAnd b (mkForall v1 BinderInfo.default t (mkForall `x BinderInfo.default b eqn))
  mkExists lev v BinderInfo.default t body

-- Constants not to unfold except if explicitly asked to
def dontUnfold : List Name := [``ite, ``dite]
def dontUnfoldNum : List Name := [``LT.lt, ``LE.le, ``GT.gt, ``GE.ge]
def numNames : List Name := [``Nat, ``Int, ``_root_.Rat, ``Real]

/- Unfold head in current context--must set local context before call.
If first = true, then unfold ExistsUnique using my def; else don't unfold it.
Also, if first = true, then unfold constants in list dontUnfold; otherwise don't.
If rep = true, unfold repeatedly.
Let whnfCore handle everything except unfolding of constants.
Do all normalization up to first unfolding of a definition; on next call do that unfolding
-/

def fixElt (e : Expr) (doFix : Bool) : TacticM Expr := do
  if doFix then
    match e with  --if e is "set elt", change to "elt ∈ set"
      | app st elt =>
        let tp ← Meta.inferType st
        match tp with
          | app (const ``Set [lev]) t =>
            return (mkApp5 (mkConst ``Membership.mem [lev, lev])
              t
              (mkApp (mkConst ``Set [lev]) t)
              (mkApp (mkConst ``Set.instMembershipSet [lev]) t)
              elt
              st)
          | _ => return e
      | _ => return e
  else
    return e
  
--Unfold if possible, else return input.  Input should have no MData.
partial def unfoldHeadCore (e : Expr) (first rep : Bool) : TacticM Expr := do
  match e with  --Don't unfold { x | p } if not applied to anything
    | (app (app (const ``setOf _) _) _) => return e
    | _ => pure ()
  let (h, args) := getHeadData e
  -- First let e1 = result of one unfolding, or handle negation, or return e
  let e1 ← match h with
    | const c levs =>
      match (c, levs, args) with
        | (``Not, _, [l]) => return mkNot (← unfoldHeadCore (consumeMData l) first rep)
        | (``ExistsUnique, [lev], [r, l]) =>
          if first then
            pure (applyToExData unfoldExUn lev l r)
          else
            return e
        | _ => 
          if !first then
            if c ∈ dontUnfold then
              return e
            if c ∈ dontUnfoldNum then
              match args[3]! with
                | const nc _ => if nc ∈ numNames then return e
                | _ => pure ()
          let edo ← Meta.unfoldDefinition? e
          match edo with
            | some ed => pure ed
            | none => return (← fixElt e rep)
    | _ =>
      let ew ← Meta.whnfCore e
      if ew == e then
        return (← fixElt e rep)
      else
        pure ew
  if rep then
    return (← unfoldHeadCore (consumeMData e1) false true)
  else
    return e1
  
def unfoldHead (e : Expr) (tac : Name) (first rep : Bool) : TacticM Expr := do
  let e1 := consumeMData e
  let e2 ← unfoldHeadCore e1 first rep
  if e2 == e1 then
    myFail tac "failed to unfold definition"
  else
    return e2

-- whnf, but don't unfold ``ExistsUnique
def whnfNotExUn (e : Expr) : TacticM Expr :=
  Meta.whnfHeadPred e (fun x => return !(x.isAppOf ``ExistsUnique))

-- w = 0 : no whnf, w = 1 : whnfNotExun, w = 2 : full whnf
def exprFromPf (t : Term) (w : Nat) : TacticM Expr := do
  let p ← elabTerm t none
  let e ← instantiateMVars (← Meta.inferType p)
  match w with
    | 0 => return e
    | 1 => whnfNotExUn e
    | _ => Meta.whnf e

--Add new hypothesis with name n, asserting form, proven by pfstx.
def doHave (n : Name) (form : Expr) (pfstx : Syntax) : TacticM Unit := do
  let goal ← getMainGoal
  let oldtar ← getType goal
  let pf ← elabTermEnsuringType pfstx form
  let mvarIdNew ← assert goal n form pf
  let (_, newGoal) ← intro1P mvarIdNew    --blank is FVarId of new hyp.
  let newtar ← getType newGoal
  if (oldtar != newtar) && (← Meta.isExprDefEq oldtar newtar) then
    --intro1P sometimes changes target to something def. equal.  Put it back to original
    replaceMainGoal [← newGoal.replaceTargetDefEq oldtar]
  else
    replaceMainGoal [newGoal]

--Set goal to be form; pfstx is proof that it suffices.
def doSuffices (form : Expr) (pfstx : Syntax) : TacticM Unit := do
  let goal ← getMainGoal
  let tag ← getTag goal
  let target ← getType goal
  let imp ← mkArrow form target
  let pf ← elabTermEnsuringType pfstx imp
  let newTarget ← Meta.mkFreshExprSyntheticOpaqueMVar form tag
  assign goal (mkApp pf newTarget)
  replaceMainGoal [newTarget.mvarId!]

--Do rewrite; symm says whether to reverse direction, rule is Term for rule, l is optional location
def doRewrite (symm : Bool) (rule : Term) (l : Option OneLoc) : TacticM Unit := do
  match l with
    | some id =>
        let idstx : Ident := ⟨id.raw[1]⟩
        if symm then
          evalTactic (← `(tactic| rewrite [← $rule:term] at $idstx:ident))
        else
          evalTactic (← `(tactic| rewrite [$rule:term] at $idstx:ident))
    | none =>
        if symm then
          evalTactic (← `(tactic| rewrite [← $rule:term]))
        else
          evalTactic (← `(tactic| rewrite [$rule:term]))

--Swap first two goals, if there are at least two
def doSwap : TacticM Unit := do
  let g ← getGoals
  let ng := match g with
    | g1 :: (g2 :: rest) => g2 :: (g1 :: rest)
    | _ => g
  setGoals ng

/- Functions for all equivalence tactics: contrapos, demorgan, quant_neg, conditional, double_neg -/
def ruleType := Name × Expr

def equivMakeRule (f : Expr)
  (ruleFunc : Expr → TacticM ruleType) : TacticM ruleType := do
  let (rule, res) ← ruleFunc f
  return (rule, mkIff f res)

def equivRuleFromForm (p : Expr)
  (ruleFunc : Expr → TacticM ruleType) : TacticM ruleType := do
    try
      equivMakeRule p ruleFunc
    catch ex =>
      match (← getPropForm p) with
        | PropForm.iff l r =>
          try
            equivMakeRule l ruleFunc
          catch _ =>
            equivMakeRule r ruleFunc
        | _ => throw ex

def equivRule (f : Option ColonTerm) (l : Option OneLoc)
  (ruleFunc : Expr → TacticM ruleType) : TacticM ruleType := do
  match f with
    | some fs => equivMakeRule (← elabTerm fs.raw[1] none) ruleFunc
    | none => equivRuleFromForm (← formFromLoc l) ruleFunc

def doReplace (tac : Name) (l : Option OneLoc) (res : Expr) (pf : Syntax) : TacticM Unit := do
    let hn ← mkFreshUserName `h
    doHave hn res pf
    let h := mkIdent hn
    let ht : Term := ⟨h.raw⟩
    try
      doRewrite false ht l
      evalTactic (← `(tactic| clear $h:ident)) -- Could also do: (try apply Iff.refl); try assumption
    catch _ =>
      evalTactic (← `(tactic| clear $h:ident))
      myFail tac  "target expression not found"

def doEquivTac (f : Option ColonTerm) (l : Option OneLoc)
  (tac : Name) (ruleFunc : Expr → TacticM ruleType) : TacticM Unit :=
  withMainContext do
    let (rule, res) ← equivRule f l ruleFunc
    doReplace tac l res (mkIdent rule)

/- contrapos tactic -/
def cpRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.implies l r => match (← getPropForm l) with
      | PropForm.not nl => match (← getPropForm r) with
        | PropForm.not nr =>
          return (`not_imp_not, (← mkArrow nr nl))
        | _ =>
          return (`not_imp_comm, (← mkArrow (mkNot r) nl))
      | _ => match (← getPropForm r) with
        | PropForm.not nr =>
          return (`imp_not_comm, (← mkArrow nr (mkNot l)))
        | _ =>
          return (`not_imp_not.symm, (← mkArrow (mkNot r) (mkNot l)))
    | _ => myFail `contrapos "contrapositive law doesn't apply"

elab "contrapos" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `contrapos cpRule

/- demorgan tactic -/
def dmRuleFromInfoNoNeg (l r : Expr) (conn : Expr → Expr → Expr) (rs : Array Name) : TacticM ruleType := do
  match (← getPropForm l) with
  | PropForm.not nl =>
      match (← getPropForm r) with
        | PropForm.not nr => return (rs[0]!, conn nl nr)
        | _ => return (rs[1]!, conn nl (mkNot r))
  | _ => 
      match (← getPropForm r) with
        | PropForm.not nr => return (rs[2]!, conn (mkNot l) nr)
        | _ => return (rs[3]!, conn (mkNot l) (mkNot r))

def dmRuleFromInfo (l r : Expr) (conn : Expr → Expr → Expr) (n : Bool) (rs : Array Name) : TacticM ruleType := do
  let p ← dmRuleFromInfoNoNeg l r conn rs
  if n then
    return (p.1, mkNot p.2)
  else
    return p

def dmRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not a => match (← getPropForm a) with
      | PropForm.and l r =>
        dmRuleFromInfo l r mkOr false
          #[`or_iff_not_and_not.symm, `not_not_and_distrib, `not_and_not_distrib, `not_and_or]
      | PropForm.or l r =>
        dmRuleFromInfo l r mkAnd false
          #[`and_iff_not_or_not.symm, `not_not_or_distrib, `not_or_not_distrib, `not_or]
      | _ => myFail `demorgan "De Morgan's laws don't apply"
    | PropForm.and l r =>
        dmRuleFromInfo l r mkOr true
          #[`not_or.symm, `not_or_not_distrib.symm, `not_not_or_distrib.symm, `and_iff_not_or_not]
    | PropForm.or l r =>
      dmRuleFromInfo l r mkAnd true
        #[`not_and_or.symm, `not_and_not_distrib.symm, `not_not_and_distrib.symm, `or_iff_not_and_not]
    | _ => myFail `demorgan "De Morgan's laws don't apply"

elab "demorgan" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `demorgan dmRule

/- quant_neg tactic -/
def qnRuleFromInfoNoNeg (v : Name) (t b : Expr) (qf : Name → BinderInfo → Expr → Expr → Expr)
  (rs : Name × Name) : TacticM ruleType := do
  let f := mkLambda `x BinderInfo.default t b
  let negres ← Meta.lambdaTelescope f fun fvs e => do
    match (← getPropForm e) with
      | PropForm.not ne => return some (← Meta.mkLambdaFVars fvs ne)
      | _ => return none
  match negres with
    | some ne => match ne with
      | lam _ _ nb _ => return (rs.1, qf v BinderInfo.default t nb)
      | _ => return (rs.2, qf v BinderInfo.default t (mkNot b))
    | none => return (rs.2, qf v BinderInfo.default t (mkNot b))

def qnRuleFromInfo (v : Name) (t b : Expr) (qf : Name → BinderInfo → Expr → Expr → Expr)
  (n : Bool) (rs : Name × Name) : TacticM ruleType := do
  let p ← qnRuleFromInfoNoNeg v t b qf rs
  if n then
    return (p.1, mkNot p.2)
  else
    return p

def qnRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not p => match (← getPropForm p) with
      | PropForm.all v t b _ =>           
        qnRuleFromInfo v t b (mkExists (← Meta.getLevel t)) false
          (`not_forall_not, `not_forall)
      | PropForm.ex _ v t b _ =>
        qnRuleFromInfo v t b mkForall false
          (`not_exists_not, `not_exists)
      | _ => myFail `quant_neg "quantifier negation laws don't apply"
    | PropForm.all v t b _ =>
      qnRuleFromInfo v t b (mkExists (← Meta.getLevel t)) true
        (`not_exists.symm, `not_exists_not.symm)
    | PropForm.ex _ v t b _ => 
      qnRuleFromInfo v t b mkForall true
        (`not_forall.symm, `not_forall_not.symm)
    | _ => myFail `quant_neg "quantifier negation laws don't apply"

elab "quant_neg" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `quant_neg qnRule

/- conditional tactic -/
def cdlRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not p => match (← getPropForm p) with
      | PropForm.implies l r => match (← getPropForm r) with
        | PropForm.not nr => return (`not_imp_not_iff_and, mkAnd l nr)
        | _ => return (`not_imp, mkAnd l (mkNot r))
      | _ => myFail `conditional "conditional laws don't apply"
    | PropForm.implies l r => match (← getPropForm l) with
      | PropForm.not nl => return (`or_iff_not_imp_left.symm, mkOr nl r)
      | _ => return (`imp_iff_not_or, mkOr (mkNot l) r)
    | PropForm.and l r => match (← getPropForm r) with
      | PropForm.not nr => return (`not_imp.symm, mkNot (← mkArrow l nr))
      | _ => match (← getPropForm l) with
        | PropForm.not nl => return (`not_imp_iff_not_and.symm, mkNot (← mkArrow r nl))
        | _ => return (`not_imp_not_iff_and.symm, mkNot (← mkArrow l (mkNot r)))
    | PropForm.or l r => match (← getPropForm l) with
      | PropForm.not nl => return (`imp_iff_not_or.symm, (← mkArrow nl r))
      | _ => match (← getPropForm r) with
        | PropForm.not nr => return (`imp_iff_or_not.symm, (← mkArrow nr l))
        | _ => return (`or_iff_not_imp_left, (← mkArrow (mkNot l) r))
    | _ => myFail `conditional "conditional laws don't apply"

elab "conditional" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `conditional cdlRule

/- double_neg tactic -/
def dnRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not p1 => match (← getPropForm p1) with
      | PropForm.not p2 => return (`Classical.not_not, p2)
      | _ => myFail `double_neg "double negation law doesn't apply"
    | _ => myFail `double_neg "double negation law doesn't apply"

elab "double_neg" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `double_neg dnRule

/- bicond_neg tactic
Note converts P ↔ Q to ¬(¬P ↔ Q).
So to convert only one side of ↔, must use : [term to convert] -/
def binegRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not p => match (← getPropForm p) with
      | PropForm.iff l r => match (← getPropForm l) with
        | PropForm.not nl => return (`not_not_iff, mkIff nl r)
        | _ => return (`not_iff, mkIff (mkNot l) r)
      | _ => myFail `bicond_neg "biconditional negation law doesn't apply"
    | PropForm.iff l r => match (← getPropForm l) with
      | PropForm.not nl => return (`not_iff.symm, mkNot (mkIff nl r))
      | _ => return (`not_not_iff.symm, mkNot (mkIff (mkNot l) r))
    | _ => myFail `bicond_neg "biconditional negation law doesn't apply"

elab "bicond_neg" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `bicond_neg binegRule

-- Give error if any ident in i is already in use.  Is this right thing to do in all cases?
partial def checkIdUsed (tac : Name) (i : Syntax) : TacticM Unit := do
  match i with
    | .missing => return ()
    | .node _ _ as => for a in as do checkIdUsed tac a
    | .atom _ _ => return ()
    | .ident _ _ v _ => 
        if (← getLCtx).usesUserName v then
          myFail tac ("identifier " ++ (toString v) ++ " already in use")
        else
          return ()

-- Get label from "with" clause, or default label.  Used by several tactics
def getLabel (tac : Name) (w : Option WithId) (dflt : Ident := mkIdent `this) : TacticM Ident := do
  match w with
    | some h => 
      let i := h.raw[1]
      checkIdUsed tac i
      return ⟨i⟩
    | none => return dflt

def isLocalVar (s : Syntax) : TacticM Bool := do
  match s with
    | .ident _ _ v _ => return (← getLCtx).usesUserName v
    | _ => return False

/- or_left and or_right tactics -/
def negData (e : Expr) : TacticM (Expr × Bool) := do
  match (← getPropForm e) with
    | PropForm.not ne => return (ne, true)
    | _ => return (e, false)

def orstrat (tac : Name) (w : Option WithId) (left : Bool) : TacticM Unit :=
  withMainContext do
    let label ← getLabel tac w
    let d ← getMainDecl
    let t ← Meta.whnf (← instantiateMVars d.type)
    match (← getPropForm t) with
      | PropForm.or l r => do
          let (form, neg) ← negData (if left then r else l)
          let goalName := d.userName
          let emn ← mkFreshUserName `h
          let emi := mkIdent emn
          doHave emn (mkOr form (mkNot form)) (← `(em _))
          evalTactic (← `(tactic|refine Or.elim $emi:ident ?_ ?_))
          if neg then doSwap
          let (rule1, rule2) :=
            if left then
              (mkIdent ``Or.inr, mkIdent ``Or.inl)
            else
              (mkIdent ``Or.inl, mkIdent ``Or.inr)
          evalTactic (← `(tactic| exact fun x => $rule1:ident x))
          evalTactic (← `(tactic| intro $label:ident; refine $rule2:ident ?_; clear $emi:ident))
          let newGoal ← getMainGoal
          setUserName newGoal goalName
      | _ => myFail tac "goal is not a disjunction"

elab "or_left" w:(withId)? : tactic => orstrat `or_left w true
elab "or_right" w:(withId)? : tactic => orstrat `or_right w false

/- disj_syll tactic -/
def matchFirstNeg (e1 e2 : Expr) : TacticM Bool := do
  match (← getPropForm e1) with
    | PropForm.not ne1 => Meta.isExprDefEq ne1 e2
    | _ => return false

--1st coord:  does one match neg of other?  2nd coord:  does first match neg of second?
def matchNeg (e1 e2 : Expr) : TacticM (Bool × Bool) := do
  if (← matchFirstNeg e1 e2) then
    return (true, true)
  else
    return ((← matchFirstNeg e2 e1), false)

--1st coord:  Does neg contradict right side of disj?  (else left side)
--2nd coord:  Is disjunct negation of neg?  (else neg is negation of disj)
def DisjSyllData (disj neg : Expr) : TacticM (Bool × Bool) := do
  match (← getPropForm disj) with
    | PropForm.or l r =>
      let (isneg, disjneg) ← matchNeg l neg
      if isneg then
        return (false, disjneg)
      else
        let (isneg, disjneg) ← matchNeg r neg
        if isneg then
          return (true, disjneg)
        else
          myFail `disj_syll "disjunctive syllogism rule doesn't apply"
    | _ => myFail `disj_syll "disjunctive syllogism rule doesn't apply"

def parseIdOrTerm (it : IdOrTerm) : Term :=
  let s := it.raw[0]
  match s with
    | .ident .. => ⟨s⟩
    | _ => ⟨s[1]⟩

elab "disj_syll" dIOrT:idOrTerm nIOrT:idOrTerm w:(withId)? : tactic =>
  withMainContext do
    let d := parseIdOrTerm dIOrT
    let n := parseIdOrTerm nIOrT
    let disj ← exprFromPf d 2
    let neg ← exprFromPf n 0
    let (dId, deflabel) :=
      if (← isLocalVar d.raw) then
        (true, ⟨d.raw⟩)
      else
        (false, mkIdent `this)
    let label ← getLabel `disj_syll w deflabel
    let (conright, disjneg) ← DisjSyllData disj neg
    let goalName := (← getMainDecl).userName
    evalTactic (← `(tactic| refine Or.elim $d ?_ ?_))
    if conright then doSwap
    if disjneg then
      evalTactic (← `(tactic| exact fun x => absurd $n x))
    else
      evalTactic (← `(tactic| exact fun x => absurd x $n))
    if (dId && (w == none)) then evalTactic (← `(tactic| clear $label:ident))
    evalTactic (← `(tactic| intro $label:ident))
    let newGoal ← getMainGoal
    setUserName newGoal goalName

/- contradict tactic -/
def ensureContra (w : Option WithId) : TacticM Unit :=
  withMainContext do
    let label ← getLabel `contradict w
    let t ← getMainTarget
    match (← getPropForm t) with
      | PropForm.f => return ()
      | _ => evalTactic (← `(tactic| by_contra $label:ident))
 
elab "contradict" h:term w:(withId)? : tactic => do
  ensureContra w
  withMainContext do
    --let tocon ← formFromIdent h.raw
    let tocon ← exprFromPf h 0
    match (← getPropForm tocon) with
      | PropForm.not p =>
        doSuffices p (← `(fun x => $h x))
      | _ =>
        doSuffices (mkNot tocon) (← `(fun x => x $h))

/- define, def_step, and whnf tactics -/
def unfoldOrWhnf (tac: Name) (e : Expr) (w rep : Bool) : TacticM Expr := do
  if w then
    match (← getPropForm e) with
      | PropForm.exun lev v t b bi => return unfoldExUn lev v t b bi
      | _ => whnfNotExUn e
  else
    unfoldHead e tac true rep

def doDefine (tac : Name) (f : Option ColonTerm) (l : Option OneLoc) (w rep : Bool) : TacticM Unit :=
  withMainContext do
    let e ← match f with
      | some fs => elabTerm fs.raw[1] none
      | none => formFromLoc l
    let e' ← unfoldOrWhnf tac e w rep
    doReplace tac l (← Meta.mkEq e e') (← `(Eq.refl _))

elab "define" f:(colonTerm)? l:(oneLoc)? : tactic => doDefine `define f l false true
elab "whnf" f:(colonTerm)? l:(oneLoc)? : tactic => doDefine `whnf f l true true
elab "def_step" f:(colonTerm)? l:(oneLoc)? : tactic => doDefine `def_step f l false false

/- definition and definition! tactics -/
--Context set in doDefinition, which calls these functions
def getDefineFormLabel (f : Option ColonTerm) (l : Option OneLoc) : TacticM (Expr × Name) := do
  match f with
    | some t => return (← elabTerm t.raw[1] none, `this)
    | none => match l with
      | some h => do
        let hs := h.raw[1]
        return (← formFromIdent hs, Name.mkStr hs.getId "def")
      | none => return (← getMainTarget, `goal.def)

-- use Iff for propositions, = for other types
def mkRel (e1 e2 : Expr) (prop : Bool) : TacticM Expr :=
  if prop then
    return mkIff e1 e2
  else
    Meta.mkEq e1 e2

-- repeatedly assert definition equivalences or equations, numbering steps
partial def doDefinitionRep (label : Name) (e e1 : Expr) (prop : Bool) (rule : Ident) (firstNum : Nat) : TacticM Unit := do
  let e' ← unfoldHead e1 `definition (firstNum == 1) false
  let res ← mkRel e e' prop
  doHave (Name.appendIndexAfter label firstNum) res (← `($rule _))
  try
    withMainContext (doDefinitionRep label e e' prop rule (firstNum + 1))  -- Context changes each time through
  catch _ =>
    return ()

def doDefinition (all : Bool) (f : Option ColonTerm) (l : Option OneLoc) (wid : Option WithId) : TacticM Unit :=
  withMainContext do
    let (e, deflabel) ← getDefineFormLabel f l
    let label ← getLabel `definition wid (mkIdent deflabel)
    let labeln := label.getId
    let (prop, rule) := if (← exprIsProp e) then
        (true, mkIdent ``Iff.refl)
      else
        (false, mkIdent ``Eq.refl)
    if all then
      doDefinitionRep labeln e e prop rule 1
    else
      let e' ← unfoldHead e `definition true true
      let res ← mkRel e e' prop
      doHave labeln res (← `($rule _))

elab "definition" f:(colonTerm) wid:(withId)? : tactic => doDefinition false (some f) none wid
elab "definition" l:(oneLoc)? wid:(withId)? : tactic => doDefinition false none l wid
elab "definition!" f:(colonTerm) wid:(withId)? : tactic => doDefinition true (some f) none wid
elab "definition!" l:(oneLoc)? wid:(withId)? : tactic => doDefinition true none l wid

def addToName (n : Name) (s : String) : Name :=
  Name.modifyBase n (fun x => Name.mkStr x s)

--Bool is whether or not to clear "or" given; Idents for two cases
def setUpCases (t : Term) (wids : Option With2Ids) : TacticM (Bool × Ident × Ident) := do
  match wids with
    | some ids =>
      let id1s := ids.raw[1]
      checkIdUsed `by_cases id1s
      let id1 : Ident := ⟨id1s⟩
      match ids.raw[2].getArgs[1]? with
        | some id2 =>
          checkIdUsed `by_cases id2
          return (false, id1, ⟨id2⟩)
        | none => return (false, id1, id1)
    | none =>
      if (← isLocalVar t.raw) then
        let tid : Ident := ⟨t.raw⟩
        return (true, tid, tid)
      else
        let thisId := mkIdent `this
        return (false, thisId, thisId)

def fixCase (clear : Bool) (label : Ident) (g : Name) (c : String) : TacticM Unit := do
  if clear then
    evalTactic (← `(tactic| clear $label))
  evalTactic (← `(tactic| intro $label:ident))
  setUserName (← getMainGoal) (addToName g c)
  doSwap

elab "by_cases" "on" t:term wids:(with2Ids)? : tactic =>
  withMainContext do
    let e ← exprFromPf t 2
    match (← getPropForm e) with
      | PropForm.or _ _ =>
        let (clear, label1, label2) ← setUpCases t wids
        let goalname :=  (← getMainDecl).userName
        evalTactic (← `(tactic| refine Or.elim $t ?_ ?_))
        fixCase clear label1 goalname "Case_1"
        fixCase clear label2 goalname "Case_2"
      | _ => myFail `by_cases "hypothesis is not a disjunction"

/- exists_unique tactic -/
def mkUn (lev: Level) (v : Name) (t b : Expr) : TacticM Expr := do
  let v1 := Name.appendIndexAfter v 1
  let v2 := Name.appendIndexAfter v 2
  let f1 := mkLambda v1 BinderInfo.default t b
  let f2 := mkLambda v2 BinderInfo.default t b
  Meta.lambdaTelescope f1 fun fv1 e1 => 
    Meta.lambdaTelescope f2 fun fv2 e2 => do
      let body ← mkArrow e1 (← mkArrow e2
        (mkApp3 (const ``Eq [lev]) t fv1[0]! fv2[0]!))
      Meta.mkForallFVars (fv1.push fv2[0]!) body

elab "exists_unique" : tactic => do
  let goal ← getMainGoal
  withContext goal do
    let d ← getDecl goal
    let goalname := d.userName
    let tar ← instantiateMVars d.type
    match (← getPropForm tar) with
      | PropForm.exun lev v t b _ =>
        let un ← mkUn lev v t b
        let ex := mkExists lev v BinderInfo.default t b
        let h ← mkFreshUserName `h
        let hid := mkIdent h
        let hex := (mkForall `a BinderInfo.default ex
          (mkForall `b BinderInfo.default un tar))
        doHave h hex (← `(exists_unique_of_exists_of_unique))
        evalTactic (← `(tactic| refine $hid ?_ ?_; clear $hid))
        setUserName (← getMainGoal) (addToName goalname "Existence")
        doSwap
        evalTactic (← `(tactic| clear $hid))
        setUserName (← getMainGoal) (addToName goalname "Uniqueness")
        doSwap
      | _ => myFail `exists_unique "goal is not a unique existence statement"

/- obtain tactic -/
def parseIdOrTerm?Type (tac : Name) (it : IdOrTerm?Type) : TacticM (Term × (Option Term)) := do
  let s := it.raw[0]
  let res := match s with
    | .ident .. => (⟨s⟩, none)
    | _ => match s[2].getArgs[1]? with
      | some t => (⟨s[1]⟩, some ⟨t⟩)
      | none => (⟨s[1]⟩, none)
  checkIdUsed tac res.1.raw
  return res

/- Old version
def doIntroOption (i : Term) (t : Option Term) : TacticM Unit := do
  match t with
    | some tt => --evalTactic (← `(tactic| intro ($i : $tt)))
      --Above fails in Chap8Part1 line 572.  Problem seems to be that
      --{a} is not understood as a Set despite default instance declarations above.
      evalTactic (← `(tactic| intro h; match @h with | ($i : $tt) => ?_; try clear h))
    | none => evalTactic (← `(tactic| intro $i:term))
-/

--Imitating mkHasTypeButIsExpectedMsg
def mkDeclaredTypeButIsExpectedMsg (decType expectedType : Expr) : MetaM MessageData := do
  try
    let decTypeType ← Meta.inferType decType
    let expectedTypeType ← Meta.inferType expectedType
    let (decType, expectedType) ← Meta.addPPExplicitToExposeDiff decType expectedType
    let (decTypeType, expectedTypeType) ← Meta.addPPExplicitToExposeDiff decTypeType expectedTypeType
    return m!"is declared to have type{indentD m!"{decType} : {decTypeType}"}\nbut is expected to have type{indentD m!"{expectedType} : {expectedTypeType}"}"
  catch _ =>
    let (decType, expectedType) ← Meta.addPPExplicitToExposeDiff decType expectedType
    return m!"is declared to have type{indentExpr decType}\nbut is expected to have type{indentExpr expectedType}"

def doIntroOption (tac : Name) (i : Term) (t : Option Term) : TacticM Unit := withMainContext do
  match t with
    | some tt =>
      let et ← elabTerm tt none
      let goal ← getMainGoal
      let h ← mkFreshUserName `h
      let hid := mkIdent h
      let (fvid, goal2) ← goal.intro h
      replaceMainGoal [goal2]
      withMainContext do
        let fv := mkFVar fvid
        let fvt ← Meta.inferType fv
        if (← Meta.isDefEq et fvt) then
          replaceMainGoal [← goal2.replaceLocalDeclDefEq fvid et]
          evalTactic (← `(tactic| match @$hid with | ($i : _) => ?_; try clear $hid))
        else
          Meta.throwTacticEx tac goal m!"type mismatch: {i} {← mkDeclaredTypeButIsExpectedMsg et fvt}"
    | none => evalTactic (← `(tactic| intro $i:term))

def doObtain (itw ith : IdOrTerm?Type) (tm : Term) : TacticM Unit :=
  withMainContext do
    let e ← exprFromPf tm 1
    match (← getPropForm e) with
      | PropForm.ex _ _ _ _ _ =>
        let (wi, wt) ← parseIdOrTerm?Type `obtain itw
        let (hi, ht) ← parseIdOrTerm?Type `obtain ith
        evalTactic (← `(tactic| refine Exists.elim $tm ?_))
        doIntroOption `obtain wi wt
        doIntroOption `obtain hi ht
      | _ => myFail `obtain "hypothesis is not an existence statement"

theorem exun_elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h2 : ∃! x, p x) (h1 : ∀ x, p x → (∀ y z, p y → p z → y = z) → b) : b := by
      apply ExistsUnique.elim h2
      intro x h3 h4
      apply h1 x h3
      intro y z h5 h6
      have h7 := h4 y h5
      have h8 := h4 z h6
      rw [h7,h8]

def doObtainExUn (itw ith1 ith2 : IdOrTerm?Type) (tm : Term) : TacticM Unit :=
  withMainContext do
    let e ← exprFromPf tm 1
    match (← getPropForm e) with
      | PropForm.exun lev v t b _ =>
        let (wi, wt) ← parseIdOrTerm?Type `obtain itw
        let (h1i, h1t) ← parseIdOrTerm?Type `obtain ith1
        let (h2i, h2t) ← parseIdOrTerm?Type `obtain ith2
        let tar ← getMainTarget
        let un ← mkUn lev v t b
        let exun := mkForall v BinderInfo.default t (← mkArrow b (← mkArrow un tar))
        let h ← mkFreshUserName `h
        let hid := mkIdent h
        doHave h (← mkArrow exun tar) (← `(exun_elim $tm))
        evalTactic (← `(tactic| refine $hid ?_; clear $hid))
        doIntroOption `obtain wi wt
        doIntroOption `obtain h1i h1t
        doIntroOption `obtain h2i h2t
      | _ => myFail `obtain "hypothesis is not a unique existence statement"

--Make 1 assertion for existential, 2 for unique existential
elab "obtain" itw:idOrTerm?Type ith:idOrTerm?Type " from " t:term : tactic =>
  doObtain itw ith t
elab "obtain" itw:idOrTerm?Type ith1:idOrTerm?Type ith2:idOrTerm?Type " from " t:term : tactic =>
  doObtainExUn itw ith1 ith2 t

/- assume and fix tactics -/
def doAssume (w : Term) (t : Option Term) : TacticM Unit :=
  withMainContext do
    checkIdUsed `assume w
    match (← getPropForm (← Meta.whnf (← getMainTarget))) with
      | PropForm.implies _ _ => doIntroOption `assume w t
      --| PropForm.not _ => doIntroOption w t  --Not necessary--whnf will have changed to implies
      | _ => myFail `assume "goal is not a conditional statement"

def doFix (w : Term) (t : Option Term) : TacticM Unit :=
  withMainContext do
    checkIdUsed `fix w
    match (← getPropForm (← Meta.whnf (← getMainTarget))) with
      | PropForm.all _ _ _ _ => doIntroOption `fix w t
      | _ => myFail `fix "goal is not a universally quantified statement"

elab "assume" w:term : tactic => doAssume w none
elab "assume" w:term " : " t:term : tactic => doAssume w (some t)
elab "fix" w:term : tactic => doFix w none
elab "fix" w:term " : " t:term : tactic => doFix w (some t)

/- show tactic: allow either "from" or ":="  Probably best to stick to "from" -/
macro "show " c:term " from " p:term : tactic => `(tactic| {show $c; exact $p})
macro "show " c:term " := " p:term : tactic => `(tactic| {show $c; exact $p})
macro "show " c:term " by " p:tactic : tactic => `(tactic| {show $c; $p})

theorem induc_from (P : Nat → Prop) (k : Nat) (h1 : P k) (h2 : (∀ n ≥ k, P n → P (n+1))) :
    ∀ n ≥ k, P n := by
  apply @Nat.rec
  assume h3
  have h4 : k = 0 := Nat.eq_zero_of_le_zero h3
  rewrite [h4] at h1
  exact h1
  fix n
  assume h3
  assume h4
  have h5 : k < n + 1 ∨ k = n + 1 := LE.le.lt_or_eq_dec h4
  by_cases on h5
  have h6 : k ≤ n := Nat.le_of_lt_succ h5
  have h7 := h3 h6
  exact h2 n h6 h7
  rewrite [h5] at h1
  exact h1

-- For ordinary induction, uses a different base if appropriate
def doInduc (strong : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  withContext goal do
    let d ← getDecl goal
    let tag := d.userName
    let target ← instantiateMVars d.type
    match (← getPropForm target) with
      | PropForm.all v t b _ =>
        match t with
          | (.const ``Nat _) =>
            let m := Expr.lam v t b BinderInfo.default  --motive
            let vid := mkIdent v
            if strong then
              let v1 := Name.appendIndexAfter v 1
              let v1id := mkIdent v1
              let m1 := Expr.lam v1 t m BinderInfo.default
              let newtar ← Meta.lambdaTelescope m1 fun fvs Pv => do
                let fv1 := fvs[0]!
                let fv := fvs[1]!
                let Pv1 := replaceFVar Pv fv fv1
                let v1lv ← elabTerm (← `($v1id < $vid)) none
                let ih ← Meta.mkForallFVars #[fv1] (← mkArrow v1lv Pv1)
                Meta.mkForallFVars #[fv] (← mkArrow ih Pv)
              let newgoal ← Meta.mkFreshExprSyntheticOpaqueMVar newtar tag
              assign goal (mkApp2 (Expr.const ``Nat.strongRec' [Level.zero]) m newgoal)
              replaceMainGoal [newgoal.mvarId!]
            else
              let (base, ind, rule) ← Meta.lambdaTelescope m fun fvs Pv => do
                -- fvs.size should be 1.
                let fv := fvs[0]!
                let PFPv ← getPropForm Pv
                let (fr, Qv) := match PFPv with
                  | PropForm.implies l r => match (consumeMData l) with
                    | (app (app (app (app (const ``GE.ge _) (const ``Nat _)) _) a) min) =>
                      if (a == fv) && !(containsFVar min (fvarId! fv)) then
                        (some (min, l), r)
                      else
                        (none, Pv)
                    | (app (app (app (app (const ``LE.le _) (const ``Nat _)) _) min) a) =>
                      if (a == fv) && !(containsFVar min (fvarId! fv)) then
                        (some (min, l), r)
                      else
                        (none, Pv)
                    | _ => (none, Pv)
                  | _ => (none, Pv)
                let fvp1 ← elabTerm (← `($vid:ident + 1)) none
                let Qimp ← mkArrow Qv (replaceFVar Qv fv fvp1)
                match fr with
                  | some (min, cond) =>
                    let base := replaceFVar Qv fv min
                    let ind ← Meta.mkForallFVars fvs (← mkArrow cond Qimp)
                    let m' ← Meta.mkLambdaFVars fvs Qv
                    pure (base, ind, mkApp2 (const ``induc_from []) m' min)
                  | none =>
                    let base := replaceFVar Qv fv (Expr.lit (.natVal 0))
                    let ind ← Meta.mkForallFVars fvs Qimp
                    pure (base, ind, app (const ``Nat.rec [Level.zero]) m)
              let baseGoal ← Meta.mkFreshExprSyntheticOpaqueMVar base (addToName tag "Base_Case")
              let indGoal ← Meta.mkFreshExprSyntheticOpaqueMVar ind (addToName tag "Induction_Step")
              assign goal (mkApp2 rule baseGoal indGoal)
              replaceMainGoal [baseGoal.mvarId!, indGoal.mvarId!]
          | _ => myFail `by_induc "mathematical induction doesn't apply"
      | _ => myFail `by_induc "mathematical induction doesn't apply"

elab "by_induc" : tactic => doInduc false
elab "by_strong_induc" : tactic => doInduc true
end tactic_defs

--Sum of m terms of the form f i, starting with i = k
def sum_seq {A : Type} [AddZeroClass A] (m k : Nat) (f : Nat → A) : A :=
  match m with
    | 0 => 0
    | n + 1 => sum_seq n k f + f (k + n)

def sum_from_to {A : Type} [AddZeroClass A] (k n : Nat) (f : Nat → A) : A :=
  sum_seq (n + 1 - k) k f

syntax (name := sumFromTo) "Sum " ident " from " term " to " term ", " term:51 : term
macro_rules (kind := sumFromTo)
  | `(Sum $i from $k to $n, $p) => `(sum_from_to $k $n (fun $i => $p))

@[app_unexpander sum_from_to] def unexpandSumFromTo : Lean.PrettyPrinter.Unexpander
  | `($_ $k:term $n:term fun $i:ident => $b) => `(Sum $i from $k to $n, $b)
  | `($_ $k:term $n:term fun ($i:ident : $_) => $b) => `(Sum $i from $k to $n, $b)
  | _ => throw ()

theorem sum_base {A : Type} [AddZeroClass A] {k : Nat} {f : Nat → A} :
    Sum i from k to k, f i = f k := by
  define : Sum i from k to k, f i
  rewrite [Nat.add_sub_cancel_left]
  rewrite [sum_seq, sum_seq]
  rewrite [zero_add, add_zero]
  rfl
  done
 
theorem sum_step {A : Type} [AddZeroClass A] {k n : Nat} {f : Nat → A}
    (h : k ≤ n) : Sum i from k to (n + 1), f i = (Sum i from k to n, f i) + f (n + 1) := by
  define : Sum i from k to (n + 1), f i
  obtain j h1 from Nat.le.dest h
  have h2 : n + 1 + 1 - k = n + 1 - k + 1 := by
    rewrite [←h1, add_assoc, add_assoc, Nat.add_sub_cancel_left,
      add_assoc, Nat.add_sub_cancel_left, add_assoc]
    rfl
  have h3 : f (n + 1) = f (k + (n + 1 - k)) := by
    rewrite [←h1, add_assoc, Nat.add_sub_cancel_left]
    rfl
  rewrite [h2, h3]
  rfl
  done

theorem sum_from_zero_step {A : Type} [AddZeroClass A] {n : Nat} {f : Nat → A} :
    Sum i from 0 to (n + 1), f i = (Sum i from 0 to n, f i) + f (n + 1) :=
  sum_step (Nat.zero_le n)

theorem sum_empty {A : Type} [AddZeroClass A] {k n : Nat} {f : Nat → A}
    (h : n < k) : Sum i from k to n, f i = 0 := by
  define : Sum i from k to n, f i
  have h2 : n + 1 - k = 0 := Nat.sub_eq_zero_of_le h
  rewrite [h2]
  rfl
  done
import Lean.Elab.Tactic
import Mathlib

/- macros for assume, fix, and obtain in term mode (doesn't include ∃!)-/
syntax withPosition("assume " ident " : " term ("; " <|> linebreak)) term : term
syntax withPosition("assume " ident ("; " <|> linebreak)) term : term
syntax withPosition("fix " ident " : " term ("; " <|> linebreak)) term : term
syntax withPosition("fix " ident ("; " <|> linebreak)) term : term

macro_rules
  | `(assume $v:ident : $t:term; $b:term) => `(fun ($v : $t) => $b)
  | `(assume $v:ident; $b:term) => `(fun $v => $b)
  | `(fix $v:ident : $t:term; $b:term) => `(fun ($v : $t) => $b)
  | `(fix $v:ident; $b:term) => `(fun $v => $b)

syntax withPosition("obtain " (ident <|> ("(" ident " : " term ") "))
  (ident <|> ("(" ident " : " term ")")) " from " term
  ("; " <|> linebreak)) term : term

macro_rules
  | `(obtain $v:ident $hv:ident from $h:term; $b:term) =>
      `(Exists.elim $h (fun $v $hv => $b))
  | `(obtain ($v:ident : $vt:term) $hv:ident from $h:term; $b:term) =>
      `(Exists.elim $h (fun ($v : $vt) $hv => $b))
  | `(obtain $v:ident ($hv:ident : $hvt:term) from $h:term; $b:term) =>
      `(Exists.elim $h (fun $v ($hv : $hvt) => $b))
  | `(obtain ($v:ident : $vt:term) ($hv:ident : $hvt:term) from $h:term; $b:term) =>
      `(Exists.elim $h (fun ($v : $vt) ($hv : $hvt) => $b))

def Iff.ltr {p q : Prop} (h : p ↔ q) := h.mp
def Iff.rtl {p q : Prop} (h : p ↔ q) := h.mpr
def Pred (t : Type u) : Type u := t → Prop
def Relation (t : Type u) : Type u := t → t → Prop

--open Classical   --Don't seem to need this.
-- If put it back in, look out for possible ambiguity of not_not

--Some theorems that should be in library
/-
theorem not_not {a : Prop} : ¬ ¬ a ↔ a := by
  apply Iff.intro
  intro h1
  have h2 := em a
  cases h2 with
    | inl h3 => exact h3
    | inr h3 => exact absurd h3 h1
  intro h1 h2
  exact h2 h1

theorem not_imp_not {a b : Prop} : ¬ a → ¬ b ↔ b → a := by
  apply Iff.intro
  intro h1 h2
  have h3 := em a
  cases h3 with
    | inl h4 => exact h4
    | inr h4 => exact absurd h2 (h1 h4)
  intro h1 h2 h3
  exact h2 (h1 h3)

theorem not_imp_comm {a b : Prop} : ¬ a → b ↔ ¬ b → a := by
  rw [← @not_imp_not a (¬ b), not_not]
  apply Iff.refl

theorem imp_not_comm {a b : Prop} : a → ¬ b ↔ b → ¬ a := by
  rw [← @not_imp_not (¬ a) b, not_not]
  apply Iff.refl

theorem not_and_distrib {a b : Prop} : ¬(a ∧ b) ↔ (¬ a ∨ ¬ b) := by
  apply Iff.intro
  intro h1
  have h2 := em a
  cases h2 with
    | inl h3 =>
        apply Or.inr
        intro h4
        exact h1 (And.intro h3 h4)
    | inr h3 => exact Or.inl h3
  intro h1 h2
  cases h1 with
    | inl h3 => exact h3 h2.left
    | inr h3 => exact h3 h2.right

theorem not_or_distrib {a b : Prop} : ¬(a ∨ b) ↔ (¬ a ∧ ¬ b) := by
  apply Iff.intro
  intro h1
  have h2 : ¬ a := by
    intro h3
    exact h1 (Or.inl h3)
  have h3 : ¬ b := by
    intro h3
    exact h1 (Or.inr h3)
  exact And.intro h2 h3
  intro h1 h2
  cases h2 with
    | inl h3 => exact h1.left h3
    | inr h3 => exact h1.right h3
  
theorem or_iff_not_and_not {a b : Prop} : a ∨ b ↔ ¬(¬ a ∧ ¬ b) := by
  rw [not_and_distrib, not_not, not_not]
  apply Iff.refl
  
theorem and_iff_not_or_not {a b : Prop} : a ∧ b ↔ ¬(¬ a ∨ ¬ b) := by
  rw [not_or_distrib, not_not, not_not]
  apply Iff.refl

theorem not_forall {α : Sort u_1} {p : α → Prop} : (¬ ∀ (x : α), p x) ↔ ∃ (x : α), ¬ p x := by
  apply Iff.intro
  intro h1
  apply byContradiction
  intro h2
  apply h1
  intro x
  apply byContradiction
  intro h3
  apply h2
  exact Exists.intro x h3
  intro h1 h2
  cases h1 with
    | intro x h3 => exact h3 (h2 x)

theorem not_exists {α : Sort u_1} {p : α → Prop} : (¬ ∃ (x : α), p x) ↔ ∀ (x : α), ¬ p x := by
  apply Iff.intro
  intro h1 x h2
  apply h1
  exact Exists.intro x h2
  intro h1 h2
  cases h2 with
    | intro x h3 => exact (h1 x) h3
-/

theorem not_forall_not {α : Sort u_1} {p : α → Prop} : (¬ ∀ (x : α), ¬ p x) ↔ ∃ (x : α), p x := by
  rw [← not_exists, Classical.not_not]

theorem not_exists_not {α : Sort u_1} {p : α → Prop} : (¬ ∃ (x : α), ¬ p x) ↔ ∀ (x : α), p x := by
  rw [← not_forall, Classical.not_not]

/-
theorem not_imp {a b : Prop} : ¬ (a → b) ↔ a ∧ ¬ b := by
  apply Iff.intro
  intro h1
  apply And.intro
  have h2 := em a
  cases h2 with
    | inl h3 => exact h3
    | inr h3 =>
      have h4 : a → b := by
        intro h5
        exact absurd h5 h3
      exact absurd h4 h1
  intro h3
  apply h1
  intro _
  exact h3
  intro h1 h2
  exact h1.right (h2 h1.left)

theorem imp_iff_not_or {a b : Prop} : a → b ↔ ¬ a ∨ b := by
  apply Iff.intro
  intro h1
  have h2 := em a
  cases h2 with
    | inl h3 => exact Or.inr (h1 h3)
    | inr h3 => exact Or.inl h3
  intro h1
  intro h2
  cases h1 with
    | inl h3 => exact absurd h2 h3
    | inr h3 => exact h3
-/

/- Not needed anymore
theorem and.swap {a b : Prop} : a ∧ b → b ∧ a := by
  intro h
  exact And.intro h.right h.left

theorem or.swap {a b : Prop} : a ∨ b → b ∨ a := by
  intro h
  cases h with
    | inl h2 => exact Or.inr h2
    | inr h2 => exact Or.inl h2
-/

--Some theorems not in library
theorem not_not_and_distrib {p q : Prop} : ¬(¬ p ∧ q) ↔ (p ∨ ¬ q) := by
  rw [not_and_distrib, Classical.not_not]

theorem not_and_not_distrib {p q : Prop} : ¬(p ∧ ¬ q) ↔ (¬ p ∨ q) := by
  rw [not_and_distrib, Classical.not_not]

theorem not_not_or_distrib {p q : Prop} : ¬(¬ p ∨ q) ↔ (p ∧ ¬ q) := by
  rw [not_or_distrib, Classical.not_not]

theorem not_or_not_distrib {p q : Prop} : ¬(p ∨ ¬ q) ↔ (¬ p ∧ q) := by
  rw [not_or_distrib, Classical.not_not]

theorem not_imp_not_iff_and {p q : Prop} : ¬ (p → ¬ q) ↔ p ∧ q := by
  rw [not_imp, Classical.not_not]

theorem not_imp_iff_or {p q : Prop} : ¬ p → q ↔ p ∨ q := by
  rw [imp_iff_not_or, Classical.not_not]

/- Not needed anymore
theorem imp_iff_or_not {p q : Prop} : q → p ↔ p ∨ ¬ q := by
  rw [imp_iff_not_or]
  exact Or.comm
-/

theorem not_imp_iff_not_and {p q : Prop} : ¬ (q → p) ↔ ¬ p ∧ q := by
  rw [not_imp]
  exact And.comm

--Definitions of tactics
section tactic_defs
open Lean Elab Tactic Expr MVarId

--Syntax for arguments to tactics
syntax oneLoc := " at " ident
syntax colonTerm := " : " term
syntax withId := " with " ident
syntax with2Ids := " with " ident (ident)?
syntax id?Type := ident <|> ("(" ident " : " term ")")

abbrev OneLoc := TSyntax `oneLoc
abbrev ColonTerm := TSyntax `colonTerm
abbrev WithId := TSyntax `withId
abbrev With2Ids := TSyntax `with2Ids
abbrev Id?Type := TSyntax `id?Type

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
  | .letE _ _ _ _ _ => "(let)" -- let expressions
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

-- Get head and arg list, and recover expression from head and arg list
def getHeadData (e : Expr) : Expr × List Expr :=
  match e with
    | app f a =>
      let (h, as) := getHeadData f
      (h, a :: as)
    | mdata _ e' => getHeadData e'
    | _ => (e, [])

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

/- Two ways to see if expression whose head is a constant expands to a negative.
Use one or the other in getPropForm to decide whether to return PropForm.not
First uses a list of constants that denote negative of another constant.  That method
only returns PropForm.not for constants on the list.
Second uses Meta.unfoldDefinition? and then checks is result is a negative; returns
PropForm.not for any constant that expands to a negative.
-/

/- Method 1: -/
--List of constants for negative predicates, and the corresponding positive predicate.
--First must be definitionally equal to negation of second.
def NegPosPairs : List (Name × Name) := [(``Ne, ``Eq)]

-- Given data for an expression with a negative constant as head, change to positive constant
def makeNegPredPos (c : Name) (ls : List Level) (args : List Expr) (key : List (Name × Name)) : Option Expr :=
  match key with
    | (neg, pos) :: rest => 
      if neg == c then
        some (mkAppList (mkConst pos ls) args)
      else
        makeNegPredPos c ls args rest
    | _ => none

-- If constant is on list, change to positive and return PropForm.not.
def findNegPropList (c : Name) (ls : List Level) (args : List Expr) : PropForm :=
  match makeNegPredPos c ls args NegPosPairs with
    | some pos => PropForm.not pos
    | none => PropForm.none

/- Method 2:  Try to unfold definition, and if result is negative, return PropForm.not
Note:  Uses constants but not fvars with let declarations.  Could add check for them?
Could multiple unfoldings be necessary to get negative result?  Maybe, but might only
want to recognize cases of only one unfolding--only want expressions that are immediately
recognized as negative.
-/
def findNegPropAll (e : Expr) : TacticM PropForm := do
  match (← Meta.unfoldDefinition? (consumeMData e)) with
    | some e' =>
      match getHeadData e' with
        | (const ``Not _, [l]) => return PropForm.not l
        | _ => return PropForm.none
    | none => return PropForm.none

def applyToExData {α : Type} (f : Level → Name → Expr → Expr → BinderInfo → α)
  (lev : Level) (l r : Expr) : α :=
  let r' := consumeMData r
  match r' with
    | lam v t b bi => f lev v t b bi
    | _ => f lev `x l (mkApp r' (bvar 0)) BinderInfo.default

-- Get logical form of a proposition.
-- Recognizes negative predicates by one of two methods from above.
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
        | _ => -- Do one of two methods to check for a constant that represents a negative:
          --return findNegPropList c levs args   -- see if negative from list
          findNegPropAll e               -- or see if negative from definition
    | forallE v t b bi =>
      if (b.hasLooseBVars || !(← exprIsProp t)) then
        return PropForm.all v t b bi
      else
        return PropForm.implies t b
    | _ => return PropForm.none

--mkNot, mkAnd, mkOr, and mkForall are already defined.  Also mkArrow and Meta.mkEq
def mkIff (l r : Expr) : Expr :=
  mkApp2 (mkConst ``Iff) l r

--Need to supply level.  Could write version that infers level, but would require MetaM
def mkExists (l : Level) (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : Expr :=
  mkApp2 (mkConst ``Exists [l]) t (mkLambda x bi t b)

def myFail {α} (tac : Name) (msg : String) : TacticM α := do
  Meta.throwTacticEx tac (← getMainGoal) msg

/- Functions for unfolding head -/
def addSuffixAux (suff : String) (v : Name) : Name :=
  match v with
    | .str p s => Name.mkStr p (s ++ suff)
    | .num p i => Name.mkNum (addSuffixAux suff p) i
    | .anonymous => Name.mkSimple ("a" ++ suff)
  
def addSuffixToVar (suff : String) (v : Name) : Name :=
  Name.modifyBase v (addSuffixAux suff)

def unfoldExUn (lev : Level) (v : Name) (t b : Expr) (_ : BinderInfo) : Expr :=
  let v1 := addSuffixToVar "1" v
  let eqn := mkApp3 (mkConst ``Eq [lev]) t (bvar 1) (bvar 2)
  let body := mkAnd b (mkForall v1 BinderInfo.default t (mkForall `x BinderInfo.default b eqn))
  mkExists lev v BinderInfo.default t body

-- Unfold head in current context--must set local context before call.
-- If exun = true, then unfold ExistsUnique using my def; else don't unfold it
/- Old version
partial def unfoldHead (e : Expr) (tac : Name) (exun : Bool) : TacticM Expr := do
  let e' := consumeMData e
  let (h, args) := getHeadData e'
  try
    match h with
      | const c levs => 
        match (c, levs, args) with
          | (``Not, _, [l]) => return mkNot (← unfoldHead l tac exun)
          | (``ExistsUnique, [lev], [r, l]) => 
              if exun then
                return applyToExData unfoldExUn lev l r
              else
                throwError "don't unfold ExistsUnique"
          | _ => Meta.unfoldDefinition e'
      | fvar fvarId => do
        let decl ← fvarId.getDecl
        match decl with
          | .cdecl .. => Meta.unfoldDefinition e'    -- Will this ever succeed?  Probably not
          | .ldecl (value := val) .. => do
            return mkAppList val args
      | lam _ _ _ _ => 
        let er ← Core.betaReduce e'
        if er == e' then
          throwError "beta reduction failed"
        else
          return er
      | proj _ i c =>
        match (← Meta.project? c i) with
          | some ep => return mkAppList ep args
          | none => Meta.unfoldDefinition e'   -- Probably won't succeed
      | _ => Meta.unfoldDefinition e'
  catch _ =>
    myFail tac "failed to unfold definition"
-/

-- Let whnfCore handle everything except unfolding of constants.
-- Do all normalization up to first unfolding of a definition; on next call do that unfolding
partial def unfoldHead (e : Expr) (tac : Name) (exun : Bool) : TacticM Expr := do
  let e' := consumeMData e
  let (h, args) := getHeadData e'
  try
    match h with
      | const c levs => 
        match (c, levs, args) with
          | (``Not, _, [l]) => return mkNot (← unfoldHead l tac exun)
          | (``ExistsUnique, [lev], [r, l]) => 
              if exun then
                return applyToExData unfoldExUn lev l r
              else
                throwError "don't unfold ExistsUnique"
          | _ => Meta.unfoldDefinition e'
      | _ => 
        let ew ← Meta.whnfCore e'
        if ew == e' then
          throwError "whnfCore failed"
        else
          return ew
  catch _ =>
    myFail tac "failed to unfold definition"

-- Repeatedly unfold head.  If exun is true, allow unfolding of ExistsUnique only in first step
partial def unfoldHeadRep (e : Expr) (tac : Name) (exun : Bool) : TacticM Expr := do
  let e' ← unfoldHead e tac exun
  try
    unfoldHeadRep e' tac false
  catch _ =>
    return e'

-- whnf, but don't unfold ``ExistsUnique
def whnfNotExUn (e : Expr) : TacticM Expr :=
  Meta.whnfHeadPred e (fun x => return !(x.isAppOf ``ExistsUnique))

--Add new hypothesis with name n, asserting form, proven by pfstx.
def doHave (n : Name) (form : Expr) (pfstx : Syntax) : TacticM Unit := do
  let goal ← getMainGoal
  let pf ← elabTermEnsuringType pfstx form
  let mvarIdNew ← assert goal n form pf
  let (_, newGoal) ← intro1P mvarIdNew    --blank is FVarId of new hyp.
  replaceMainGoal [newGoal]

--Add n : (Type) := val to context.
/- **Not used
def doLet (n : Name) (val : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  withContext goal do
    let valType ← Meta.inferType val
    let mvarIdNew ← define goal n valType val
    let (_, newGoal) ← intro1P mvarIdNew
    replaceMainGoal [newGoal]
-/

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

/- Functions for all equivalence tactics: contrapos, demorgan, quantneg, condl, doubleneg -/
def ruleType := Name × Expr

def equivMakeRule (f : Expr)
  (ruleFunc : Expr → TacticM ruleType) : TacticM ruleType := do
  let (rule, res) ← ruleFunc f
  return (rule, mkIff f res)

def equivRuleFromForm (p : Expr)
  (ruleFunc : Expr → TacticM ruleType) : TacticM ruleType := do
    match (← getPropForm p) with
      | PropForm.iff l r =>
          try
            commitIfNoEx (equivMakeRule l ruleFunc)
          catch _ =>
            equivMakeRule r ruleFunc
      | _ => equivMakeRule p ruleFunc

def equivRule (f : Option ColonTerm) (l : Option OneLoc)
  (ruleFunc : Expr → TacticM ruleType) : TacticM ruleType := do
  match f with
    | some fs => equivMakeRule (← elabTerm fs.raw[1] none) ruleFunc
    | none => equivRuleFromForm (← formFromLoc l) ruleFunc

def doEquivTac (f : Option ColonTerm) (l : Option OneLoc)
  (tac : Name) (ruleFunc : Expr → TacticM ruleType) : TacticM Unit :=
  withMainContext do
    let (rule, res) ← equivRule f l ruleFunc
    let hn ← mkFreshUserName `h
    doHave hn res (mkIdent rule)
    let h := mkIdent hn
    let ht : Term := ⟨h.raw⟩
    try
      doRewrite false ht l
      evalTactic (← `(tactic| clear $h:ident)) -- Could also do: (try apply Iff.refl); try assumption
    catch _ =>
      evalTactic (← `(tactic| clear $h:ident))
      myFail tac  "target expression not found"

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
          #[`or_iff_not_and_not.symm, `not_not_and_distrib, `not_and_not_distrib, `not_and_distrib]
      | PropForm.or l r =>
        dmRuleFromInfo l r mkAnd false
          #[`and_iff_not_or_not.symm, `not_not_or_distrib, `not_or_not_distrib, `not_or_distrib]
      | _ => myFail `demorgan "De Morgan's laws don't apply"
    | PropForm.and l r =>
        dmRuleFromInfo l r mkOr true
          #[`not_or_distrib.symm, `not_or_not_distrib.symm, `not_not_or_distrib.symm, `and_iff_not_or_not]
    | PropForm.or l r =>
      dmRuleFromInfo l r mkAnd true
        #[`not_and_distrib.symm, `not_and_not_distrib.symm, `not_not_and_distrib.symm, `or_iff_not_and_not]
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
      | PropForm.not nl => return (`not_imp_iff_or, mkOr nl r)
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
        | _ => return (`not_imp_iff_or.symm, (← mkArrow (mkNot l) r))
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

-- Get label from "with" clause, or default label.  Used by several tactics
def checkIdUsed (tac : Name) (i : Syntax) : TacticM Unit := do
  let d :=(← getLCtx).findFromUserName? i.getId
  match d with
    | some _ => myFail tac ("identifier " ++ (toString i.getId) ++ " already in use")
    | none => return ()

def getLabel (tac : Name) (w : Option WithId) (dflt : Ident := mkIdent `this) : TacticM Ident := do
  match w with
    | some h => 
      let i := h.raw[1]
      checkIdUsed tac i
      return ⟨i⟩
    | none => return dflt

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
          evalTactic (← `(tactic|apply Or.elim $emi:ident))
          if neg then doSwap
          let (rule1, rule2) :=
            if left then
              (mkIdent ``Or.inr, mkIdent ``Or.inl)
            else
              (mkIdent ``Or.inl, mkIdent ``Or.inr)
          evalTactic (← `(tactic| exact fun x => $rule1:ident x))
          evalTactic (← `(tactic| intro $label:ident; apply $rule2:ident; clear $emi:ident))
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

elab "disj_syll" d:ident n:ident w:(withId)? : tactic =>
  withMainContext do
    let label ← getLabel `disj_syll w d
    let disj ← Meta.whnf (← formFromIdent d.raw)
    let neg ← formFromIdent n.raw
    let (conright, disjneg) ← DisjSyllData disj neg
    let goalName := (← getMainDecl).userName
    evalTactic (← `(tactic| apply Or.elim $d:ident))
    if conright then doSwap
    if disjneg then
      evalTactic (← `(tactic| exact fun x => absurd $n:ident x))
    else
      evalTactic (← `(tactic| exact fun x => absurd x $n:ident))
    if (w == none) then evalTactic (← `(tactic| clear $d:ident))
    evalTactic (← `(tactic| intro $label:ident))
    let newGoal ← getMainGoal
    setUserName newGoal goalName

/- contradict tactic -/
def ensureContra (tac : Name) (w : Option WithId) : TacticM Unit :=
  withMainContext do
    let label ← getLabel tac w
    let t ← getMainTarget
    match (← getPropForm t) with
      | PropForm.f => return ()
      | _ => evalTactic (← `(tactic| by_contra $label))
      /- This was more complicated -- not nec
      | PropForm.not _ =>
        evalTactic (← `(tactic| intro $label:ident))
      | _ =>
        doSuffices (mkNot (mkNot t)) (← `(Classical.not_not.mp))
        evalTactic (← `(tactic| intro $label:ident))
      -/

/- Standard by_contra just as good (although doesn't check identifier in use).
elab "bycontra" w:(withId)? : tactic => ensureContra `bycontra w
-/
 
elab "contradict" h:ident w:(withId)? : tactic => do
  ensureContra `contradict w
  withMainContext do
    let tocon ← formFromIdent h.raw
    match (← getPropForm tocon) with
      | PropForm.not p =>
        doSuffices p (← `(fun x => $h:ident x))
      | _ =>
        doSuffices (mkNot tocon) (← `(fun x => x $h:ident))

/- define and whnf tactics -/
def unfoldOrWhnf (e : Expr) (w : Bool) : TacticM Expr := do
  if w then
    match (← getPropForm e) with
      | PropForm.exun lev v t b bi => return unfoldExUn lev v t b bi
      | _ => whnfNotExUn e
  else
    unfoldHeadRep e `define true

--Unfold head repeatedly or whnf at a location
def unfoldOrWhnfAt (l : Option OneLoc) (w : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  withContext goal do
    match l with
      | some h => do
        let hdec ← Meta.getLocalDeclFromUserName h.raw[1].getId
        let e ← instantiateMVars hdec.type
        let e' ← unfoldOrWhnf e w
        if !(← Meta.isExprDefEq e e') then   --Just to be sure we didn't make a mistake
          Meta.throwTacticEx `define goal "got definition wrong"
        let newgoal ← replaceLocalDeclDefEq goal hdec.fvarId e'
        replaceMainGoal [newgoal]
      | none => do
        let e ← getMainTarget
        let e' ← unfoldOrWhnf e w
        if !(← Meta.isExprDefEq e e') then
          Meta.throwTacticEx `define goal "got definition wrong"
        let newgoal ← replaceTargetDefEq goal e'
        replaceMainGoal [newgoal]

elab "define" l:(oneLoc)? : tactic => unfoldOrWhnfAt l false
--Probably prefer defn, but should test whnf
elab "whnf" l:(oneLoc)? : tactic => unfoldOrWhnfAt l true

/- define and define! tactics -/
--Context set in doDefine, which calls these functions
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
partial def doDefineRep (label : Name) (e e1 : Expr) (prop : Bool) (rule : Ident) (firstNum : Nat) : TacticM Unit := do
  let e' ← unfoldHead e1 `definition (firstNum == 1)
  let res ← mkRel e e' prop
  doHave (addSuffixToVar ("_" ++ (toString firstNum)) label) res (← `($rule _))
  --doHave (Name.mkStr label ("_" ++ (toString firstNum))) res (← `($rule _))
  try
    withMainContext (doDefineRep label e e' prop rule (firstNum + 1))  -- Context changes each time through
  catch _ =>
    return ()

def doDefinition (all : Bool) (f : Option ColonTerm) (l : Option OneLoc) (wid : Option WithId) : TacticM Unit :=
  withMainContext do
    let (e, deflabel) ← getDefineFormLabel f l
    let label ← getLabel `definition wid (mkIdent deflabel)
    let labeln := label.getId
    --let label := match wid with
    --  | some i => i.raw[1].getId
    --  | none => deflabel
    let (prop, rule) := if (← exprIsProp e) then
        (true, mkIdent ``Iff.refl)
      else
        (false, mkIdent ``Eq.refl)
    if all then
      doDefineRep labeln e e prop rule 1
    else
      let e' ← unfoldHeadRep e `definition true
      let res ← mkRel e e' prop
      doHave labeln res (← `($rule _))

elab "definition" f:(colonTerm) wid:(withId)? : tactic => doDefinition false (some f) none wid
elab "definition" l:(oneLoc)? wid:(withId)? : tactic => doDefinition false none l wid
elab "definition!" f:(colonTerm) wid:(withId)? : tactic => doDefinition true (some f) none wid
elab "definition!" l:(oneLoc)? wid:(withId)? : tactic => doDefinition true none l wid

/- by_cases on tactic -/
def getCaseLabels (deflabel : Ident) (wids : Option With2Ids) : TacticM (Ident × Ident) := do
  match wids with
    | some ids =>
      let id1s := ids.raw[1]
      checkIdUsed `by_cases id1s
      let id1 : Ident := ⟨id1s⟩
      match ids.raw[2].getArgs[0]? with
        | some id2 =>
          checkIdUsed `by_cases id2
          return (id1, ⟨id2⟩)
        | none => return ⟨id1, id1⟩
    | none => return ⟨deflabel, deflabel⟩

def fixCase (orid label : Ident) : TacticM Unit := do
  evalTactic (← `(tactic| clear $orid:ident; intro $label:ident))
  doSwap

def finishCases (orid label1 label2 : Ident) : TacticM Unit := do
  evalTactic (← `(tactic| apply Or.elim $orid:ident))
  fixCase orid label1
  fixCase orid label2

/- Standard by_cases just as good?
elab "bycases" t:colonTerm wids:(with2Ids)? : tactic =>
  withMainContext do
    let e ← elabTerm t.raw[1] none
    if !(← exprIsProp e) then myFail `bycases "cases specifier is not a proposition"
    let (label1, label2) ← getCaseLabels (mkIdent `this) wids
    let emn ← mkFreshUserName `p
    doHave emn (mkOr e (mkNot e)) (← `(em _))
    finishCases (mkIdent emn) label1 label2
-/

elab "by_cases" "on" l:ident wids:(with2Ids)? : tactic =>
  withMainContext do
    let e ← Meta.whnf (← formFromIdent l.raw)
    match (← getPropForm e) with
      | PropForm.or _ _ =>
        let (label1, label2) ← getCaseLabels l wids
        finishCases l label1 label2
      | _ => myFail `by_cases "hypothesis is not a disjunction"

/- exists_unique tactic -/
elab "exists_unique" : tactic =>
  withMainContext do
    let tar ← getMainTarget
    match (← getPropForm tar) with
      | PropForm.exun lev v t b _ =>
        let v1 := addSuffixToVar "1" v
        let v2 := addSuffixToVar "2" v
        let f1 := mkLambda v1 BinderInfo.default t b
        let f2 := mkLambda v2 BinderInfo.default t b
        let un ← Meta.lambdaTelescope f1 fun fv1 e1 => 
          Meta.lambdaTelescope f2 fun fv2 e2 => do
            let body ← mkArrow e1 (← mkArrow e2
              (mkApp3 (const ``Eq [lev]) t fv1[0]! fv2[0]!))
            Meta.mkForallFVars (fv1.push fv2[0]!) body
        let ex := mkExists lev v BinderInfo.default t b
        let h ← mkFreshUserName `h
        let hid := mkIdent h
        let hex := (mkForall `Existence BinderInfo.default ex
          (mkForall `Uniqueness BinderInfo.default un tar))
        doHave h hex (← `(exists_unique_of_exists_of_unique))
        evalTactic (← `(tactic| apply $hid; clear $hid))
        doSwap
        evalTactic (← `(tactic| clear $hid))
        doSwap
      | _ => myFail `exists_unique "goal is not a unique existence statement"

/- obtain tactic -/
def parseId?Type (tac : Name) (it : Id?Type) : TacticM (Ident × (Option Term)) := do
  let s := it.raw[0]
  let res := match s with
    | .ident .. => (⟨s⟩, none)
    | _ => (⟨s[1]⟩, some ⟨s[3]⟩)
  checkIdUsed tac res.1.raw
  return res

def doIntroOption (i : Ident) (t : Option Term) : TacticM Unit := do
  match t with
    | some tt => evalTactic (← `(tactic| intro ($i : $tt)))
    | none => evalTactic (← `(tactic| intro $i:ident))

/- Not used anymore
def doIntro (it : Id?Type) : TacticM Unit := do
  let (h, t) := parseId?Type it
  doIntroOption h t
-/

def doObtain (itw ith : Id?Type) (l : Ident) : TacticM Unit :=
  withMainContext do
    let e ← Meta.whnf (← formFromIdent l.raw)
    match (← getPropForm e) with
      | PropForm.ex _ _ _ _ _ =>
        let (wi, wt) ← parseId?Type `obtain itw
        let (hi, ht) ← parseId?Type `obtain ith
        evalTactic (← `(tactic| apply Exists.elim $l))
        doIntroOption wi wt
        doIntroOption hi ht
      | _ => myFail `obtain "hypothesis is not an existence statement"

def doObtainExUn (itw ith1 ith2 : Id?Type) (l : Ident) : TacticM Unit :=
  withMainContext do
    let e ← whnfNotExUn (← formFromIdent l.raw)
    match (← getPropForm e) with
      | PropForm.exun lev v t b _ =>
        let (wi, wt) ← parseId?Type `obtain itw
        let (h1i, h1t) ← parseId?Type `obtain ith1
        let (h2i, h2t) ← parseId?Type `obtain ith2
        let v1 := addSuffixToVar "1" v
        let tar ← getMainTarget
        let eqn := mkApp3 (mkConst ``Eq [lev]) t (bvar 1) (bvar 3)
        let un := mkForall v1 BinderInfo.default t (← mkArrow b eqn)
        let exun := mkForall v BinderInfo.default t (← mkArrow b (← mkArrow un tar))
        let h ← mkFreshUserName `h
        let hid := mkIdent h
        doHave h (← mkArrow exun tar) (← `(ExistsUnique.elim $l))
        evalTactic (← `(tactic| apply $hid; clear $hid))
        doIntroOption wi wt
        doIntroOption h1i h1t
        doIntroOption h2i h2t
      | _ => myFail `obtain "hypothesis is not a unique existence statement"

--Make 1 assertion for existential, 2 for unique existential
elab "obtain" itw:id?Type ith:id?Type " from " l:ident : tactic =>
  doObtain itw ith l
elab "obtain" itw:id?Type ith1:id?Type ith2:id?Type " from " l:ident : tactic =>
  doObtainExUn itw ith1 ith2 l

/- assume and fix tactics -/
def doAssume (w : Ident) (t : Option Term) : TacticM Unit :=
  withMainContext do
    checkIdUsed `assume w
    match (← getPropForm (← Meta.whnf (← getMainTarget))) with
      | PropForm.implies _ _ => doIntroOption w t
      --| PropForm.not _ => doIntroOption w t  --Not necessary--whnf will have changed to implies
      | _ => myFail `assume "goal is not a conditional statement"

def doFix (w : Ident) (t : Option Term) : TacticM Unit :=
  withMainContext do
    checkIdUsed `fix w
    match (← getPropForm (← Meta.whnf (← getMainTarget))) with
      | PropForm.all _ _ _ _ => doIntroOption w t
      | _ => myFail `fix "goal is not a universally quantified statement"

elab "assume" w:ident : tactic => doAssume w none
elab "assume" w:ident " : " t:term : tactic => doAssume w (some t)
elab "fix" w:ident : tactic => doFix w none
elab "fix" w:ident " : " t:term : tactic => doFix w (some t)

/- show tactic: allow either "from" or ":="  Probably best to stick to "from" -/
macro "show " c:term " from " p:term : tactic => `(tactic| show $c; exact $p)
macro "show " c:term " := " p:term : tactic => `(tactic| show $c; exact $p)
--No point in below; just use `show c` and then continue in tactic mode
--macro "show " c:term " by " t:tacticSeq : tactic => `(tactic| show $c; exact by $t)

end tactic_defs
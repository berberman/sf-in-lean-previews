import LF.CustomTactics
import LF.Typeclasses
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer

import SFLCompat

--  # Imp: Simple Imperative Programs

--  We concentrate here on defining the *syntax* and
--  *semantics* of Imp; later in this volume we develop a
--  theory of *program equivalence* and introduce *Hoare
--  Logic*, a popular logic for reasoning about imperative
--  programs.

--  ## Expressions With Variables

--  ### States

--  Since we'll want to look variables up to find out their
--  current values, we'll use total maps from the `Maps`
--  chapter. A *machine state* (or just *state*) represents
--  the current values of all variables at some point in the
--  execution of a program.
--
--  We give the type of variable identifiers a name,
--  `Ident`. For now it is just `String`; naming it makes
--  the intent clearer.

open scoped MyGetElem

abbrev Ident := String
abbrev State := TotalMap Ident Nat

--  ### Syntax

--  We can add variables to the arithmetic expressions we
--  had before simply by including one more constructor.
--  (This is a fresh `Aexp`, replacing the variable-free one
--  from the *Slang* chapter.)

inductive Aexp where
  | num (n : Nat)
  | id (x : Ident)                -- NEW
  | plus (a₁ a₂ : Aexp)
  | minus (a₁ a₂ : Aexp)
  | mult (a₁ a₂ : Aexp)

--  The `Bexp` definition is unchanged, except that it now
--  refers to the new `Aexp`.

inductive Bexp where
  | bool (b : Bool)
  | eq (a₁ a₂ : Aexp)
  | neq (a₁ a₂ : Aexp)
  | le (a₁ a₂ : Aexp)
  | gt (a₁ a₂ : Aexp)
  | not (b : Bexp)
  | and (b₁ b₂ : Bexp)

--  Defining a few variable names as shorthands will make
--  examples easier to read.

def W : Ident := "W"
def X : Ident := "X"
def Y : Ident := "Y"
def Z : Ident := "Z"

--  ### Notations

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: arithmetic expressions)
/-- Arithmetic expressions of Imp -/
declare_syntax_cat imp_aexp
/-- Numeric literal -/
syntax:max num : imp_aexp
/-- Variable reference -/
syntax:max ident : imp_aexp
/-- Addition -/
syntax:65 imp_aexp:65 " + " imp_aexp:66 : imp_aexp
/-- Subtraction -/
syntax:65 imp_aexp:65 " - " imp_aexp:66 : imp_aexp
/-- Multiplication -/
syntax:70 imp_aexp:70 " * " imp_aexp:71 : imp_aexp
/-- Parentheses for grouping -/
syntax "(" imp_aexp ")" : imp_aexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_aexp

/-- Embed an Imp arithmetic expression into a Lean term -/
syntax:min "aexp " "{" imp_aexp "}" : term
--  END DETAILS

open Lean in
macro_rules
  | `(aexp { $n:num }) => `(Aexp.num $(quote n.getNat))
  | `(aexp { $x:ident }) => `(Aexp.id $x)
  | `(aexp { ~$e }) => pure e
  | `(aexp { $a + $b }) => `(Aexp.plus (aexp {$a}) (aexp {$b}))
  | `(aexp { $a - $b }) => `(Aexp.minus (aexp {$a}) (aexp {$b}))
  | `(aexp { $a * $b }) => `(Aexp.mult (aexp {$a}) (aexp {$b}))
  | `(aexp { ($a) }) => `(aexp {$a})

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: boolean expressions)
/-- Boolean expressions of Imp -/
declare_syntax_cat imp_bexp
/-- Boolean literal (`true` or `false`) -/
syntax:max ident : imp_bexp
/-- Equality of arithmetic expressions -/
syntax:50 imp_aexp:51 " = " imp_aexp:51 : imp_bexp
/-- Disequality of arithmetic expressions -/
syntax:50 imp_aexp:51 " ≠ " imp_aexp:51 : imp_bexp
/-- Less than or equal -/
syntax:50 imp_aexp:51 " ≤ " imp_aexp:51 : imp_bexp
/-- Greater than -/
syntax:50 imp_aexp:51 " > " imp_aexp:51 : imp_bexp
/-- Boolean negation -/
syntax:70 "¬ " imp_bexp:70 : imp_bexp
/-- Boolean conjunction -/
syntax:35 imp_bexp:36 " ∧ " imp_bexp:35 : imp_bexp
/-- Parentheses for grouping -/
syntax "(" imp_bexp ")" : imp_bexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_bexp

/-- Embed an Imp boolean expression into a Lean term -/
syntax:min "bexp " "{" imp_bexp "}" : term
--  END DETAILS

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: boolean expressions, macro rules)
open Lean in
macro_rules
  | `(bexp { $x:ident }) =>
    match x.getId with
    | `true  => `(Bexp.bool true)
    | `false => `(Bexp.bool false)
    | _      => Macro.throwErrorAt x s!"expected 'true' or 'false', got '{x.getId}'"
  | `(bexp { ~$e }) => pure e
  | `(bexp { $a:imp_aexp = $b:imp_aexp }) => `(Bexp.eq (aexp {$a}) (aexp {$b}))
  | `(bexp { $a:imp_aexp ≠ $b:imp_aexp }) => `(Bexp.neq (aexp {$a}) (aexp {$b}))
  | `(bexp { $a:imp_aexp ≤ $b:imp_aexp }) => `(Bexp.le (aexp {$a}) (aexp {$b}))
  | `(bexp { $a:imp_aexp > $b:imp_aexp }) => `(Bexp.gt (aexp {$a}) (aexp {$b}))
  | `(bexp { ¬ $b:imp_bexp }) => `(Bexp.not (bexp {$b}))
  | `(bexp { $b₁:imp_bexp ∧ $b₂:imp_bexp }) => `(Bexp.and (bexp {$b₁}) (bexp {$b₂}))
  | `(bexp { ($b:imp_bexp) }) => `(bexp {$b})
--  END DETAILS

#check aexp { 3 + (X * 2) }
#check bexp { true ∧ ¬(X ≤ 4) }

--  ### Delaborators

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing expressions back)
namespace Imp.Delab
open Lean PrettyPrinter Delaborator SubExpr Parenthesizer

/-- Re-inserts parentheses in `imp_aexp` output according to the grammar's precedences. -/
@[category_parenthesizer imp_aexp]
def imp_aexp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `imp_aexp true wrapParens prec <|
    parenthesizeCategoryCore `imp_aexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

/-- Re-inserts parentheses in `imp_bexp` output according to the grammar's precedences. -/
@[category_parenthesizer imp_bexp]
def imp_bexp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `imp_bexp true wrapParens prec <|
    parenthesizeCategoryCore `imp_bexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

/-- Tag freshly built syntax with the term info that Lean's pretty printer expects. -/
def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

/-- Rebuild `imp_aexp` concrete syntax from an `Aexp` term. -/
partial def delabAexpInner : DelabM (TSyntax `imp_aexp) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Aexp.num _ =>
      match (← withAppArg getExpr).nat? with
      | some v => pure ⟨Syntax.mkNumLit (toString v) |>.raw⟩
      | none   => `(imp_aexp| ~$(← withAppArg delab))
    | Aexp.id _ =>
      -- A variable reference like aexp { X } elaborates to Aexp.id X where X is the
      -- declared Ident constant, so the delaborators print the constant's name as a
      -- bare identifier (and also handle the .id "X" string-literal form).
      match ← withAppArg getExpr with
      | .const nm _      => `(imp_aexp| $(mkIdent nm):ident)
      | .lit (.strVal s) => `(imp_aexp| $(mkIdent (.mkSimple s)):ident)
      | _                => `(imp_aexp| ~$(← withAppArg delab))
    | Aexp.plus _ _ =>
      let s₁ ← withAppFn <| withAppArg delabAexpInner
      let s₂ ← withAppArg delabAexpInner
      `(imp_aexp| $s₁ + $s₂)
    | Aexp.minus _ _ =>
      let s₁ ← withAppFn <| withAppArg delabAexpInner
      let s₂ ← withAppArg delabAexpInner
      `(imp_aexp| $s₁ - $s₂)
    | Aexp.mult _ _ =>
      let s₁ ← withAppFn <| withAppArg delabAexpInner
      let s₂ ← withAppArg delabAexpInner
      `(imp_aexp| $s₁ * $s₂)
    | _ => `(imp_aexp| ~$(← delab))
  annAsTerm stx

/-- Rebuild `imp_bexp` concrete syntax from a `Bexp` term. -/
partial def delabBexpInner : DelabM (TSyntax `imp_bexp) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Bexp.bool _ =>
      match ← withAppArg getExpr with
      | .const ``Bool.true _  => `(imp_bexp| $(mkIdent `true):ident)
      | .const ``Bool.false _ => `(imp_bexp| $(mkIdent `false):ident)
      | _                     => `(imp_bexp| ~$(← withAppArg delab))
    | Bexp.eq _ _ =>
      let s₁ ← withAppFn <| withAppArg delabAexpInner
      let s₂ ← withAppArg delabAexpInner
      `(imp_bexp| $s₁:imp_aexp = $s₂:imp_aexp)
    | Bexp.neq _ _ =>
      let s₁ ← withAppFn <| withAppArg delabAexpInner
      let s₂ ← withAppArg delabAexpInner
      `(imp_bexp| $s₁:imp_aexp ≠ $s₂:imp_aexp)
    | Bexp.le _ _ =>
      let s₁ ← withAppFn <| withAppArg delabAexpInner
      let s₂ ← withAppArg delabAexpInner
      `(imp_bexp| $s₁:imp_aexp ≤ $s₂:imp_aexp)
    | Bexp.gt _ _ =>
      let s₁ ← withAppFn <| withAppArg delabAexpInner
      let s₂ ← withAppArg delabAexpInner
      `(imp_bexp| $s₁:imp_aexp > $s₂:imp_aexp)
    | Bexp.not _ =>
      let s ← withAppArg delabBexpInner
      `(imp_bexp| ¬ $s)
    | Bexp.and _ _ =>
      let s₁ ← withAppFn <| withAppArg delabBexpInner
      let s₂ ← withAppArg delabBexpInner
      `(imp_bexp| $s₁ ∧ $s₂)
    | _ => `(imp_bexp| ~$(← delab))
  annAsTerm stx
--  END DETAILS

--  The `whenPPOption getPPNotation` wrapper lets
--  `set_option pp.notation false` switch this delaborator
--  off, revealing the raw constructors (see the "Desugaring
--  Notations" discussion, after the commands are
--  introduced).

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: registering the delaborators)
@[delab app.Aexp.num, delab app.Aexp.id, delab app.Aexp.plus,
  delab app.Aexp.minus, delab app.Aexp.mult]
partial def delabAexp : Delab := whenPPOption getPPNotation do
  -- This delaborator only understands `Aexp`'s constructors -- bail otherwise.
  guard <| match_expr ← getExpr with
    | Aexp.num _ => true
    | Aexp.id _ => true
    | Aexp.plus _ _ => true
    | Aexp.minus _ _ => true
    | Aexp.mult _ _ => true
    | _ => false
  match ← delabAexpInner with
  | `(imp_aexp| ~$e) => pure e
  | e => `(term| aexp { $e })

@[delab app.Bexp.bool, delab app.Bexp.eq, delab app.Bexp.neq, delab app.Bexp.le,
  delab app.Bexp.gt, delab app.Bexp.not, delab app.Bexp.and]
partial def delabBexp : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Bexp.bool _ => true
    | Bexp.eq _ _ => true
    | Bexp.neq _ _ => true
    | Bexp.le _ _ => true
    | Bexp.gt _ _ => true
    | Bexp.not _ => true
    | Bexp.and _ _ => true
    | _ => false
  match ← delabBexpInner with
  | `(imp_bexp| ~$e) => pure e
  | e => `(term| bexp { $e })

end Imp.Delab
--  END DETAILS

/-- info: aexp {3 + X * 2} : Aexp -/
#guard_msgs in
#check aexp { 3 + (X * 2) }

/-- info: bexp {true ∧ ¬ (X ≤ 4)} : Bexp -/
#guard_msgs in
#check bexp { true ∧ ¬(X ≤ 4) }

--  ### Evaluation

--  Now we need to add an `st` parameter to both evaluation
--  functions:

def Aexp.eval (st : State) (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | id    x     =>  st[x]                    -- NEW
  | plus  a₁ a₂ =>  a₁.eval st + a₂.eval st
  | minus a₁ a₂ =>  a₁.eval st - a₂.eval st
  | mult  a₁ a₂ =>  a₁.eval st * a₂.eval st

def Bexp.eval (st : State) (b : Bexp) : Bool :=
  match b with
  | bool b      =>  b
  | eq   a₁ a₂  =>  a₁.eval st == a₂.eval st
  | neq  a₁ a₂  =>  a₁.eval st != a₂.eval st
  | le   a₁ a₂  =>  a₁.eval st ≤  a₂.eval st
  | gt   a₁ a₂  =>  a₁.eval st >  a₂.eval st
  | not  b₁     =>  !b₁.eval st
  | and  b₁ b₂  =>  b₁.eval st && b₂.eval st

@[simp] theorem Aexp.eval_num (st : State) (n : Nat) : (num n).eval st = n := rfl
@[simp] theorem Aexp.eval_id (st : State) (x : Ident) : (Aexp.id x).eval st = st[x] := rfl
@[simp] theorem Aexp.eval_plus (st : State) (a₁ a₂ : Aexp) :
    (plus a₁ a₂).eval st = a₁.eval st + a₂.eval st := rfl
@[simp] theorem Aexp.eval_minus (st : State) (a₁ a₂ : Aexp) :
    (minus a₁ a₂).eval st = a₁.eval st - a₂.eval st := rfl
@[simp] theorem Aexp.eval_mult (st : State) (a₁ a₂ : Aexp) :
    (mult a₁ a₂).eval st = a₁.eval st * a₂.eval st := rfl

@[simp] theorem Bexp.eval_bool (st : State) (b : Bool) : (bool b).eval st = b := rfl
@[simp] theorem Bexp.eval_eq (st : State) (a₁ a₂ : Aexp) :
    (eq a₁ a₂).eval st = (a₁.eval st == a₂.eval st) := rfl
@[simp] theorem Bexp.eval_neq (st : State) (a₁ a₂ : Aexp) :
    (neq a₁ a₂).eval st = (a₁.eval st != a₂.eval st) := rfl
@[simp] theorem Bexp.eval_le (st : State) (a₁ a₂ : Aexp) :
    (le a₁ a₂).eval st = (a₁.eval st ≤ a₂.eval st : Bool) := rfl
@[simp] theorem Bexp.eval_gt (st : State) (a₁ a₂ : Aexp) :
    (gt a₁ a₂).eval st = (a₁.eval st > a₂.eval st : Bool) := rfl
@[simp] theorem Bexp.eval_not (st : State) (b : Bexp) : (not b).eval st = !b.eval st := rfl
@[simp] theorem Bexp.eval_and (st : State) (b₁ b₂ : Bexp) :
    (and b₁ b₂).eval st = (b₁.eval st && b₂.eval st) := rfl

--  We reuse the total-map notation (`x →ₜ v ; ∅` etc.) for
--  states.

example : aexp { 3 + (X * 2) }.eval (X →ₜ 5 ; ∅) = 13 := by rfl

example : aexp { Z + (X * Y) }.eval (X →ₜ 5 ; Y →ₜ 4 ; ∅) = 20 := by rfl

example : bexp { true ∧ ¬(X ≤ 4) }.eval (X →ₜ 5 ; ∅) = true := by rfl

--  ## Commands

inductive Com where
  | skip
  | asgn (x : Ident) (a : Aexp)
  | seq (c₁ c₂ : Com)
  | cond (b : Bexp) (c₁ c₂ : Com)
  | whileDo (b : Bexp) (c : Com)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: commands, macro rules)
/-- Imp commands -/
declare_syntax_cat imp_com
/-- The command that does nothing (`skip`) -/
syntax ident : imp_com
/-- Sequencing: one command after another -/
syntax imp_com ";" ppDedent(ppLine imp_com) : imp_com
/-- Assignment -/
syntax ident " := " imp_aexp : imp_com
/-- Conditional -/
syntax "if " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}" ppHardSpace "else" ppHardSpace "{") ppLine imp_com ppDedent(ppLine "}") : imp_com
/-- Loop -/
syntax "while " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : imp_com
/-- Escape to Lean -/
syntax:max "~" term:max : imp_com

/-- Include an Imp command in Lean code -/
syntax:min "imp" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : term

namespace Com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $c₁ ; $c₂ }) =>
    `(Com.seq (imp {$c₁}) (imp {$c₂}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c₁} else {$c₂} }) =>
    `(Com.cond (bexp {$b}) (imp {$c₁}) (imp {$c₂}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { ~$c }) =>
    pure c

end Com

open scoped Com
--  END DETAILS

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing commands back)
namespace Imp.Delab
open Lean PrettyPrinter Delaborator SubExpr

partial def delabComInnerFor (ns : Name) (extra : DelabM (TSyntax `imp_com)) :
    DelabM (TSyntax `imp_com) := do
  let e ← getExpr
  let stx ←
    -- Using `(imp_com| skip)` would delaborate as `skip✝`. `mkIdent` fixes this.
    if e.isConstOf (ns ++ `skip) then
      `(imp_com| $(mkIdent `skip):ident)
    else if e.isAppOfArity (ns ++ `asgn) 2 then
      match ← withAppFn <| withAppArg getExpr with
      | .lit (.strVal s) =>
        let a ← withAppArg delabAexpInner
        `(imp_com| $(mkIdent (.mkSimple s)):ident := $a)
      | _ =>
        let `($x:ident) ← withAppFn <| withAppArg delab | failure
        let a ← withAppArg delabAexpInner
        `(imp_com| $x:ident := $a)
    else if e.isAppOfArity (ns ++ `seq) 2 then
      let s₁ ← withAppFn <| withAppArg (delabComInnerFor ns extra)
      let s₂ ← withAppArg (delabComInnerFor ns extra)
      `(imp_com| $s₁; $s₂)
    else if e.isAppOfArity (ns ++ `cond) 3 then
      let b  ← withAppFn <| withAppFn <| withAppArg delabBexpInner
      let c₁ ← withAppFn <| withAppArg (delabComInnerFor ns extra)
      let c₂ ← withAppArg (delabComInnerFor ns extra)
      `(imp_com| if ($b) {$c₁} else {$c₂})
    else if e.isAppOfArity (ns ++ `whileDo) 2 then
      let b ← withAppFn <| withAppArg delabBexpInner
      let c ← withAppArg (delabComInnerFor ns extra)
      `(imp_com| while ($b) {$c})
    else
      extra <|> `(imp_com| ~$(← delab))
  annAsTerm stx

/-- Rebuild `imp_com` concrete syntax from a `Com` term. -/
partial def delabComInner : DelabM (TSyntax `imp_com) :=
  delabComInnerFor ``Com failure

@[delab app.Com.skip, delab app.Com.asgn, delab app.Com.seq,
  delab app.Com.cond, delab app.Com.whileDo]
partial def delabCom : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Com.skip => true
    | Com.asgn _ _ => true
    | Com.seq _ _ => true
    | Com.cond _ _ _ => true
    | Com.whileDo _ _ => true
    | _ => false
  match ← delabComInner with
  | `(imp_com| ~$e) => pure e
  | e => `(term| imp { $e })

end Imp.Delab
--  END DETAILS

def fact_in_lean : Com := imp {
  Z := X;
  Y := 1;
  while (Z ≠ 0) {
    Y := Y * Z;
    Z := Z - 1
  }
}

/--
info: def fact_in_lean : Com :=
imp {
  Z := X;
  Y := 1;
  while (Z ≠ 0) {
    Y := Y * Z;
    Z := Z - 1
  }
}
-/
#guard_msgs in
#print fact_in_lean

--  ### Desugaring Notations

/-- info: imp {
  X := X + 1
} : Com -/
#guard_msgs in
#check imp { X := X + 1 }

/-- info: Com.asgn X ((Aexp.id X).plus (Aexp.num 1)) : Com -/
#guard_msgs in
set_option pp.notation false in
#check imp { X := X + 1 }

--  ### More Examples

--  A few more examples.

--  Assignment:

def plus2 : Com := imp { X := X + 2 }
def XtimesYinZ : Com := imp { Z := X * Y }

--  Loops:

def subtract_slowly_body : Com := imp {
  Z := Z - 1;
  X := X - 1
}

def subtract_slowly : Com := imp {
  while (X ≠ 0) {
    ~subtract_slowly_body
  }
}

def subtract_3_from_5_slowly : Com := imp {
  X := 3;
  Z := 5;
  ~subtract_slowly
}

--  An infinite loop:

def loop : Com := imp { while (true) { skip } }

--  ## Evaluating Commands

--  ### Evaluation as a Function (Failed Attempt)

--  Here's an attempt at defining an evaluation function for
--  commands (with a bogus `while` case).

def Com.ceval_fun_no_while (st : State) (c : Com) : State :=
  match c with
  | imp {skip} => st
  | imp {x := ~a} => (x →ₜ a.eval st ; st)
  | imp {~c₁; ~c₂} =>
      let st' := ceval_fun_no_while st c₁
      ceval_fun_no_while st' c₂
  | imp {if (~b) {~c₁} else {~c₂}} =>
      if b.eval st then ceval_fun_no_while st c₁
      else ceval_fun_no_while st c₂
  | imp {while (~_) {~_}} => st     -- bogus

--  A nonterminating
--  `def loop_false (n) : False := loop_false n` would make
--  `False` provable, so Lean rejects it.

--  ### Evaluation as a Relation

--  Here's a better way: define `ceval` as a *relation*
--  rather than a *function* -- i.e., make its result a
--  `Prop` rather than a `State`, similar to what we did for
--  `Aexp.EvalR` in the Slang chapter.

--  We'll use the notation `st =[ c ]=> st'` for the
--  `Com.EvalR` relation: `st =[ c ]=> st'` means that
--  executing program `c` in a starting state `st` results
--  in an ending state `st'`. This can be pronounced "`c`
--  takes state `st` to `st'`".

--  Operational Semantics

--  Here is an informal definition of evaluation, presented
--  as inference rules for readability:
--
--                            -----------------                  (skip)
--                            st =[ skip ]=> st
--
--                            a.eval st = n
--                    --------------------------------           (asgn)
--                    st =[ x := a ]=> (x →ₜ n ; st)
--
--                            st  =[ c₁ ]=> st'
--                            st' =[ c₂ ]=> st''
--                          ---------------------                (seq)
--                          st =[ c₁;c₂ ]=> st''
--
--                           b.eval st = true
--                            st =[ c₁ ]=> st'
--                 --------------------------------------        (ifTrue)
--                 st =[ if b then c₁ else c₂ end ]=> st'
--
--                          b.eval st = false
--                            st =[ c₂ ]=> st'
--                 --------------------------------------        (ifFalse)
--                 st =[ if b then c₁ else c₂ end ]=> st'
--
--                          b.eval st = false
--                     -----------------------------             (whileFalse)
--                     st =[ while b do c end ]=> st
--
--                           b.eval st = true
--                            st =[ c ]=> st'
--                   st' =[ while b do c end ]=> st''
--                   --------------------------------            (whileTrue)
--                   st  =[ while b do c end ]=> st''
--
--  Here is the formal definition. Make sure you understand
--  how it corresponds to the inference rules.

inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} : EvalR (imp {skip}) st st
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (x →ₜ n ; st)
  | seq {c₁ c₂ : Com} {st st' st'' : State} (h₁ : EvalR c₁ st st') (h₂ : EvalR c₂ st' st'') :
      EvalR (imp {~c₁; ~c₂}) st st''
  | ifTrue {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = true)
      (hc : EvalR c₁ st st') :
      EvalR (imp {if (~b) {~c₁} else {~c₂}}) st st'
  | ifFalse {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = false)
      (hc : EvalR c₂ st st') :
      EvalR (imp {if (~b) {~c₁} else {~c₂}}) st st'
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c}}) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st') (hloop : Com.EvalR (imp {while (~b) {~c}}) st' st'') :
      EvalR (imp {while (~b) {~c}}) st st''

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: commands)
class HasEval (Com : Type) (In : outParam <| Type) (Out : outParam <| Type) where
  Eval : Com → In → Out → Prop

namespace HasEval
/-- Evaluation: `st =[ c ]=> st'` with `imp_com` command syntax -/
scoped syntax:lead term " =[ " imp_com:lead " ]=> " term : term
scoped macro_rules
  | `($st =[ $c:imp_com ]=> $st') => ``(HasEval.Eval (imp { $c }) $st $st')

namespace Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab
@[delab app.HasEval.Eval]
def delabTriple : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``HasEval.Eval 7
  let c ← withNaryArg 4 delab
  let st ← withNaryArg 5 delab
  let st' ← withNaryArg 6 delab
  match c with
  | `(imp { $c:imp_com }) => ``($st =[ $c ]=> $st')
  | c => ``($st =[ ~$c ]=> $st')
end Delab
end HasEval

open scoped HasEval

instance : HasEval Com State State where
  Eval := Com.EvalR

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()
--  END DETAILS

--  The cost of defining evaluation as a relation instead of
--  a function is that we now need to construct a *proof*
--  that some program evaluates to some result state, rather
--  than letting Lean's computation mechanism do it for us.

example :
    ∅ =[
      X := 2;
      if (X ≤ 1) {
        Y := 3
      } else {
        Z := 4
      }
    ]=> (Z →ₜ 4 ; X →ₜ 2 ; ∅) := by
  -- We must supply the intermediate state.
  apply Com.EvalR.seq (st' := (X →ₜ 2 ; ∅))
  · apply Com.EvalR.asgn; rfl
  · apply Com.EvalR.ifFalse
    · rfl
    · apply Com.EvalR.asgn; rfl

--  ### Exercise (2 stars): ceval_example₂ ⭐⭐

example :
    ∅ =[
      X := 0;
      Y := 1;
      Z := 2
    ]=> (Z →ₜ 2 ; Y →ₜ 1 ; X →ₜ 0 ; ∅) := by
  sorry

--  What sorts of things might we want to prove using these
--  definitions? Here are some simple examples...

--   ----------------------------------------

--  _Quiz:_

--  Is the following proposition provable?
--
--      ∀ (c : Com) (st st' : State),
--        st =[ skip; ~c ]=> st' →
--        st =[ c ]=> st'
--
--  (A) Yes (B) No (C) Not sure

--   ----------------------------------------

--  _Quiz:_

--  Is the following proposition provable?
--
--      ∀ (c₁ c₂ : Com) (st st' : State),
--        st =[ ~c₁ ~c₂ ]=> st' →
--        st =[ c₁ ]=> st →
--        st =[ c₂ ]=> st'
--
--  (A) Yes (B) No (C) Not sure

--   ----------------------------------------

--  _Quiz:_

--  Is the following proposition provable?
--
--      ∀ (b : Bexp) (c : Com) (st st' : State),
--        st =[ if (~b) { ~c } else { ~c } ]=> st' →
--        st =[ c ]=> st'
--
--  (A) Yes (B) No (C) Not sure

--   ----------------------------------------

--  _Quiz:_

--  Is the following proposition provable?
--
--      ∀ (b : Bexp),
--        (∀ st, b.eval st = true) →
--        ∀ (c : Com) (st : State),
--        ¬ ∃ st', st =[ while (~b) { ~c } ]=> st'
--
--  (A) Yes (B) No (C) Not sure

--   ----------------------------------------

--  _Quiz:_

--  Is the following proposition provable?
--
--      ∀ (b : Bexp) (c : Com) (st : State),
--        (¬ ∃ st', st =[ while (~b) { ~c } ]=> st') →
--        ∀ st'', b.eval st'' = true
--
--  (A) Yes (B) No (C) Not sure

--   ----------------------------------------

--  ### Determinism of Evaluation

--  Finally, we should pause to check that our evaluation
--  relation really is a (partial) function...

theorem ceval_deterministic (c : Com) (st st1 st2 : State)
    (e₁ : st =[ ~c ]=> st1) (e₂ : st =[ ~c ]=> st2) : st1 = st2 := by
  induction e₁ generalizing st2 with
  | @skip st =>
      inversion e₂
      rfl
  | @asgn st a n x h =>
      inversion e₂ with
      | asgn h' => subst h; subst h'; rfl
  | @seq c₁ c₂ st st' st'' h₁ h₂ ih₁ ih₂ =>
      inversion e₂ with
      | seq st2' h₁' h₂' =>
          have hst : st' = st2' := ih₁ _ h₁'
          subst hst
          exact ih₂ _ h₂'
  | @ifTrue st st' b c₁ c₂ hb hc ih =>
      inversion e₂ with
      | ifTrue hb' hc' => exact ih _ hc'
      | ifFalse hb' hc' => simp_all
  | @ifFalse st st' b c₁ c₂ hb hc ih =>
      inversion e₂ with
      | ifTrue hb' hc' => simp_all
      | ifFalse hb' hc' => exact ih _ hc'
  | @whileFalse b st c hb =>
      inversion e₂ with
      | whileFalse hb' => rfl
      | whileTrue hb' hc' hl' => simp_all
  | @whileTrue st st' st'' b c hb hc hloop ih₁ ih₂ =>
      inversion e₂ with
      | whileFalse hb' => simp_all
      | whileTrue st2' _ hc' hl' =>
          have hst : st' = st2' := ih₁ _ hc'
          subst hst
          exact ih₂ _ hl'

--  ### Exercise (3 stars): pup_to_n (Optional) ⭐⭐⭐

--  Write an Imp program that sums the numbers from `1` to
--  `X` (inclusive) in the variable `Y`. Your program should
--  update the state as shown in `pup_to_2_ceval`, which you
--  can reverse-engineer to discover the program you should
--  write. The proof of that theorem will be somewhat
--  lengthy.

def pup_to_n : Com := sorry

theorem pup_to_2_ceval :
    (X →ₜ 2 ; ∅) =[ ~pup_to_n ]=>
      (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅) := by
  sorry

--  ## Reasoning About Imp Programs

theorem plus2_spec (st : State) (n : Nat) (st' : State)
    (hx : st[X] = n) (heval : st =[ ~plus2 ]=> st') :
    st'[X] = n + 2 := by
  -- Inverting `heval` forces one step of the `ceval` computation: since
  -- `plus2` is an assignment, `st'` must be `st` extended at `X`.
  unfold plus2 at heval
  inversion heval with
  | asgn m h =>
      simp [Aexp.eval_plus, Aexp.eval_id, Aexp.eval_num, TotalMap.update_eq] at h ⊢
      lia

--  ### Exercise (3 stars): XtimesYinZ_spec (Optional) ⭐⭐⭐

--  State and prove a specification of `XtimesYinZ`.

--  FILL IN HERE

--  ### Exercise (3 stars): loop_never_stops ⭐⭐⭐

--  Hint: proceed by induction on the assumed derivation
--  showing that `loop` terminates. Most of the cases are
--  immediately contradictory and so can be solved in one
--  step (by `simp`/`contradiction` on the impossible
--  command equation).

theorem loop_never_stops (st st' : State) : ¬ (st =[ ~loop ]=> st') := by
  sorry

--  ### Exercise (3 stars): no_whiles_eqv ⭐⭐⭐

--  The following function yields `true` just on programs
--  with no while loops. Using `inductive`, write a property
--  `Com.NoWhilesR` that holds exactly when `c` is
--  while-free, then prove it equivalent to `Com.no_whiles`.

def Com.no_whiles (c : Com) : Bool :=
  match c with
  | imp {skip} => true
  | imp {_x := ~_a} => true
  | imp {~c₁; ~c₂} => no_whiles c₁ && no_whiles c₂
  | imp {if (~_) {~ct} else {~cf}} => no_whiles ct && no_whiles cf
  | imp {while (~_) {~_}} => false

inductive Com.NoWhilesR : Com → Prop where
  --  FILL IN HERE

theorem no_whiles_eqv (c : Com) : c.no_whiles = true ↔ Com.NoWhilesR c := by
  sorry

--  ### Exercise (4 stars): no_whiles_terminating ⭐⭐⭐⭐

--  Imp programs that don't involve while loops always
--  terminate. State and prove a theorem
--  `no_whiles_terminating` that says this. Use either
--  `Com.no_whiles` or `Com.NoWhilesR`, as you prefer.

theorem no_whiles_terminating (c : Com) (st : State) (h : Com.NoWhilesR c) :
    ∃ st', st =[ ~c ]=> st' := by
  sorry

--  And here is an alternative solution by induction on `c`
--  (using `Com.no_whiles` instead of `Com.NoWhilesR`):

--  FILL IN HERE

--  ### Additional Exercises

--  ### Exercise (3 stars): stack_compiler ⭐⭐⭐

--  Old HP Calculators, programming languages like Forth and
--  Postscript, and abstract machines like the Java Virtual
--  Machine all evaluate arithmetic expressions using a
--  *stack*. For instance, the expression
--
--      (2*3)+(3*(4-2))
--
--  would be written as
--
--            2 3 * 3 4 2 - * +
--
--  and evaluated like this (where we show the program being
--  evaluated on the right and the contents of the stack on
--  the left):

--  [ ]           |    2 3 * 3 4 2 - * +
--        [2]           |    3 * 3 4 2 - * +
--        [3, 2]        |    * 3 4 2 - * +
--        [6]           |    3 4 2 - * +
--        [3, 6]        |    4 2 - * +
--        [4, 3, 6]     |    2 - * +
--        [2, 4, 3, 6]  |    - * +
--        [2, 3, 6]     |    * +
--        [6, 6]        |    +
--        [12]          |

--  The goal of this exercise is to write a small compiler
--  that translates `aexp`s into stack machine instructions.
--
--  The instruction set for our stack language will consist
--  of the following instructions:
--
--  - `sPush n`: Push the number `n` on the stack.
--
--  - `sLoad x`: Load the identifier `x` from the store and
--    push it on the stack
--
--  - `sPlus`: Pop the two top numbers from the stack, add
--    them, and push the result onto the stack.
--
--  - `sMinus`: Similar, but subtract the first number from
--    the second.
--
--  - `sMult`: Similar, but multiply.

namespace StackCompiler

inductive Sinstr : Type where
| sPush (n : Nat)
| sLoad (x : String)
| sPlus
| sMinus
| sMult

open Sinstr

--  Write a function to evaluate programs in the stack
--  language. It should take as input a state, a stack
--  represented as a list of numbers (top stack item is the
--  head of the list), and a program represented as a list
--  of instructions, and it should return the stack after
--  executing the program. Test your function on the
--  examples below.
--
--  Note that it is unspecified what to do when encountering
--  an `sPlus`, `sMinus`, or `sMult` instruction if the
--  stack contains fewer than two elements. In a sense, it
--  is immaterial what we do, since a correct compiler will
--  never emit such a malformed program. But for sake of
--  later exercises, it would be best to skip the offending
--  instruction and continue with the next one.

def sExecute (st : State) (stack : List Nat) (prog : List Sinstr) : List Nat :=
  sorry
                                        -- Bad state: skip

--  FILL IN HERE

example : sExecute ∅ [] [sPush 5, sPush 3, sPush 1, sMinus] = [2, 5] := by
  sorry

example : sExecute (X →ₜ 3) [3, 4] [sPush 4, sLoad X, sMult, sPlus] = [15, 4] := by
  sorry

--  Next, write a function that compiles an `Aexp` into a
--  stack machine program. The effect of running the program
--  should be the same as pushing the value of the
--  expression on the stack.

def sCompile (a : Aexp) : List Sinstr :=
  sorry

--  FILL IN HERE

--  After you've defined `sCompile`, prove the following to
--  test that it works.

example : sCompile (aexp { X - (2 * Y) }) = [sLoad X, sPush 2, sLoad Y, sMult, sMinus] := by
  sorry

--  ### Exercise (3 stars): execute_app ⭐⭐⭐

--  Execution can be decomposed in the following sense:
--  executing stack program `p₁ ++ p₂` is the same as
--  executing `p₁`, taking the resulting stack, and
--  executing `p₂` from that stack. Prove that fact.

theorem execute_app (st : State) (p₁ p₂ : List Sinstr) (stack : List Nat) :
    sExecute st stack (p₁ ++ p₂) = sExecute st (sExecute st stack p₁) p₂ := by
  sorry

--  ### Exercise (3 stars): compiler_correct ⭐⭐⭐

--  Now we'll prove the correctness of the compiler
--  implemented in the previous exercise. Begin by proving
--  the following lemma. If it becomes difficult, consider
--  whether your implementation of `sExecute` or `sCompile`
--  could be simplified.

theorem sCompile_correct_aux (st : State) (a : Aexp) (stack : List Nat) :
  sExecute st stack (sCompile a) = Aexp.eval st a :: stack := by
  sorry

--  The main theorem should be a very easy corollary of that
--  lemma.

theorem sCompile_correct (st : State) (a : Aexp) :
  sExecute st [] (sCompile a) = [ Aexp.eval st a ] := by
  sorry

end StackCompiler

--  ### Exercise (3 stars): short_circuit (Optional) ⭐⭐⭐

--  Most modern programming languages use a "short-circuit"
--  evaluation rule for boolean `and`: to evaluate
--  `BExp.and b₁ b₂`, first evaluate `b₁`. If it evaluates
--  to `false`, then the entire `and` expression evaluates
--  to `false` immediately, without evaluating `b₂`.
--  Otherwise, `b₂` is evaluated to determine the result of
--  the `and` expression.
--
--  Write an alternate version of `BExp.eval` that performs
--  short-circuit evaluation of `BAnd` in this manner, and
--  prove that it is equivalent to `BExp.eval`. (N.b. This
--  is only true because expression evaluation in Imp is
--  rather simple. In a bigger language where evaluating an
--  expression might diverge, the short-circuiting `and`
--  would *not* be equivalent to the original, since it
--  would make more programs terminate.)

def Bexp.evalSC (st : State) (b : Bexp) : Bool := sorry

--  FILL IN HERE

-- This exercise turned out to be easier than we intended!
theorem Bexp.eval_eq_evalSc (st : State) (b : Bexp) :
  b.eval st = b.evalSC st := by
  sorry

--  ### Exercise (3 stars): break_imp (Optional) ⭐⭐⭐

--  Imperative languages like C and Java often include a
--  `break` or similar statement for interrupting the
--  execution of loops. In this exercise we consider how to
--  add `break` to Imp. First, we need to enrich the
--  language of commands with an additional case. Because
--  `break` is a reserved keyword in Lean, we will
--  abbreviate it as `brk`.

namespace BreakImp

inductive Com where
  | skip
  | brk                          -- <--- NEW
  | asgn (x : Ident) (a : Aexp)
  | seq (c₁ c₂ : Com)
  | cond (b : Bexp) (c₁ c₂ : Com)
  | whileDo (b : Bexp) (c : Com)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: commands, macro rules)
namespace Com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else if x.getId == `brk then `(Com.brk)
    else Macro.throwErrorAt x s!"expected 'skip' or 'break', got '{x.getId}'"
  | `(imp { $c₁; $c₂ }) =>
    `(Com.seq (imp {$c₁}) (imp {$c₂}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c₁} else {$c₂} }) =>
    `(Com.cond (bexp {$b}) (imp {$c₁}) (imp {$c₂}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { ~$c }) =>
    pure c

end Com

open scoped Com

namespace Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab

/-- Rebuild `imp_com` syntax from a `BreakImp.Com` term. -/
partial def delabComInner : DelabM (TSyntax `imp_com) :=
  delabComInnerFor ``Com do
    let e ← getExpr
    guard <| e.isConstOf ``Com.brk
    annAsTerm (← `(imp_com| $(mkIdent `brk):ident))

@[delab app.BreakImp.Com.skip, delab app.BreakImp.Com.brk, delab app.BreakImp.Com.asgn,
  delab app.BreakImp.Com.seq, delab app.BreakImp.Com.cond, delab app.BreakImp.Com.whileDo]
partial def delabCom : Delab := whenPPOption getPPNotation do
  match ← delabComInner with
  | `(imp_com| ~$e) => pure e
  | e => `(term| imp { $e })

end Delab

/--
info: imp {
  brk
} : Com
-/
#guard_msgs in
#check imp {brk}
--  END DETAILS

--  Next, we need to define the behavior of `brk`.
--  Informally, whenever `brk` is executed in a sequence of
--  commands, it stops the execution of that sequence and
--  signals that the innermost enclosing loop should
--  terminate. (If there aren't any enclosing loops, then
--  the whole program simply terminates.) The final state
--  should be the same as the one in which the `brk`
--  statement was executed.
--
--  One important point is what to do when there are
--  multiple loops enclosing a given `brk`. In those cases,
--  `brk` should only terminate the *innermost* loop. Thus,
--  after executing the following...
--
--          X := 0;
--          Y := 1;
--          while (0 <> Y) {
--            while (true) {
--              break
--            };
--            X := 1;
--            Y := Y - 1
--          }
--
--  ... the value of `X` should be `1`, and not `0`.
--
--  One way of expressing this behavior is to add another
--  parameter to the evaluation relation that specifies
--  whether evaluation of a command executes a `brk`
--  statement:

inductive Result : Type where
  | sContinue
  | sBreak

open Result

--  We will use the syntax `st =[ c ]=> st' // s` to mean
--  that, if `c` is started in state `st`, then it
--  terminates in state `st'` and either signals that the
--  innermost surrounding loop (or the whole program) should
--  exit immediately (`s = sBreak`) or that execution should
--  continue normally (`s = sContinue`).
--
--  The definition of the `st =[ c ]=> st' // s` relation is
--  very similar to the one we gave above for the regular
--  evaluation relation (`st =[ c ]=> st'`) -- we just need
--  to handle the termination signals appropriately:
--
--  - If the command is `skip`, then the state doesn't
--    change and execution of any enclosing loop can
--    continue normally.
--
--  - If the command is `brk`, the state stays unchanged but
--    we signal a `sBreak`.
--
--  - If the command is an assignment, then we update the
--    binding for that variable in the state accordingly and
--    signal that execution can continue normally.
--
--  - If the command is of the form `if (b) {c₁} {c₂}`, then
--    the state is updated as in the original semantics of
--    Imp, except that we also propagate the signal from the
--    execution of whichever branch was taken.
--
--  - If the command is a sequence `c₁ ; c₂`, we first
--    execute `c₁`. If this yields a `sBreak`, we skip the
--    execution of `c₂` and propagate the `sBreak` signal to
--    the surrounding context; the resulting state is the
--    same as the one obtained by executing `c₁` alone.
--    Otherwise, we execute `c₂` on the state obtained after
--    executing `c₁`, and propagate the signal generated
--    there.
--
--  - Finally, for a loop of the form `while (b) {c}`, the
--    semantics is almost the same as before. The only
--    difference is that, when `b` evaluates to `true`, we
--    execute `c` and check the signal that it raises. If
--    that signal is `sContinue`, then the execution
--    proceeds as in the original semantics. Otherwise, we
--    stop the execution of the loop, and the resulting
--    state is the same as the one resulting from the
--    execution of the current iteration. In either case,
--    since `break` only terminates the innermost loop,
--    `while` signals `sContinue`.
--
--  Based on the above description, complete the definition
--  of the `Com.EvalR` relation:

inductive Com.EvalR : Com → State → State → Result → Prop where
  | skip {st : State} : EvalR (imp {skip}) st st sContinue
  --  FILL IN HERE

scoped notation:40 st0:41 " =[ " c " ]=> " st1:41 " // " s:41 => Com.EvalR c st0 st1 s

--  Now prove the following properties of your definition:

theorem break_ignore (c : Com) (st st' : State) (s : Result) (h : st =[ imp { brk ; ~c } ]=> st' // s) :
  st = st' := by
  sorry

theorem while_continue (b : Bexp) (c : Com) (st st' : State) (s : Result)
  (h : st =[ imp { while (~b) {~c} } ]=> st' // s) :
  s = sContinue := by
  sorry

theorem while_stops_on_break (b : Bexp) (c : Com) (st st' : State)
  (h₁ : b.eval st = true)
  (h₂ : st =[ imp { ~c } ]=> st' // sBreak) :
  st =[ imp { while (~b) {~c} } ]=> st' // sContinue := by
  sorry

theorem seq_continue (c₁ c₂ : Com) (st st' st'' : State)
  (h₁ : st =[ imp { ~c₁ } ]=> st' // sContinue)
  (h₂ : st' =[ imp { ~c₂ } ]=> st'' // sContinue) :
  st =[ imp { ~c₁ ; ~c₂ } ]=> st'' // sContinue := by
  sorry

theorem seq_stops_on_break (c₁ c₂ : Com) (st st' : State)
  (h : st =[ imp { ~c₁ } ]=> st' // sBreak) :
  st =[ imp { ~c₁ ; ~c₂ } ]=> st' // sBreak := by
  sorry

--  ### Exercise (3 stars): while_break_true (Optional) ⭐⭐⭐

theorem while_break_true (b : Bexp) (c : Com) (st st' : State)
  (h₁ : st =[ imp { while (~b) {~c} } ]=> st' // sContinue)
  (h₂ : b.eval st' = true) :
  ∃ st'', st'' =[ imp { ~c } ]=> st' // sBreak := by
  sorry

--  ### Exercise (4 stars): ceval_deterministic (Optional) ⭐⭐⭐⭐

theorem ceval_deterministic (c : Com) (st st₁ st₂ : State) (s₁ s₂ : Result)
  (h₁ : st =[ imp { ~c } ]=> st₁ // s₁)
  (h₂ : st =[ imp { ~c } ]=> st₂ // s₂) :
  st₁ = st₂ ∧ s₁ = s₂ := by
  sorry

end BreakImp

--  ### Exercise (4 stars): add_for_loop (Optional) ⭐⭐⭐⭐

--  Add C-style `for` loops to the language of commands,
--  update the `ceval` definition to define the semantics of
--  `for` loops, and add cases for `for` loops as needed so
--  that all the proofs in this file are accepted by Rocq.
--
--  A `for` loop should be parameterized by (a) a statement
--  executed initially, (b) a test that is run on each
--  iteration of the loop to determine whether the loop
--  should continue, (c) a statement executed at the end of
--  each loop iteration, and (d) a statement that makes up
--  the body of the loop. (You don't need to worry about
--  making up a concrete Notation for `for` loops, but feel
--  free to play with this too if you like.)

-- Built on 2026-08-31 21:28 UTC

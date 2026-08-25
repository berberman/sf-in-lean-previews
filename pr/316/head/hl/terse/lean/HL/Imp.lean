import LF.CustomTactics
import LF.Typeclasses
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer

import SFLCompat

--  # Imp: Simple Imperative Programs

--  Note to developers (before next release):
--      Needs some WORKINCLASSes and some quizzes
--
--      LATER: Another nice challenge exercise at some point
--      would be to add C-style arrays (i.e., indirect
--      read/write). This sets up some really nice challenge
--      problems in Hoare (reasoning about arrays / aliasing
--      / etc.).
--
--      SOONER: BCP 25: Maybe we should write / instead of
--      && in assertions, to save a mismatch in the
--      `dec_minimum` exercise in Hoare2?
--
--      At some point we could consider moving material from
--      the old HoareLists to this chapter (and into later
--      files, as appropriate). We haven't done it yet
--      because it's a shame to complicate the nice simple
--      presentation here when it's used as the basis for
--      applications like Xavier's static analysis lectures.
--      Also, we now have a whole volume on real separation
--      logic...
--
--      MWH (port note): The Rocq chapter's "Rocq
--      Automation" tour has been retooled here for Lean.
--      The tactic combinators `try` and `repeat` (and the
--      custom-tactic `macro`) are introduced in this
--      chapter; `<;>` and `simp` were already introduced in
--      Logical Foundations (`<;>` in `Induction`) so we use
--      them freely and the `<;>` section below is a recap.
--      For linear arithmetic we use `lia`; NOTE that LF
--      currently introduces `omega`, not `lia`, so this
--      needs to be reconciled volume-wide (either introduce
--      `lia` in LF, or keep `omega`).

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

--  Note to developers (Benjamin Pierce @bcpierce00):
--      That should be a live chapter link.

inductive Aexp where
  | num (n : Nat)
  | id (x : Ident)                -- NEW
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)

--  Note to developers (Chris Henson @chenson2018):
--      Rather than define identifiers as Ident, a more
--      general approach is to use a **type variable** with
--      `DecidableEq` (as the `Maps` chapter does), threaded
--      through `Aexp`/`Bexp`/`Com`/`State`. Stashed for a
--      future decision; the parameterized version would
--      look like:
--
--      `inductive Aexp (V : Type) where
--        | num (n : Nat)
--        | id (x : V)
--        | plus (a1 a2 : Aexp V)
--        | minus (a1 a2 : Aexp V)
--        | mult (a1 a2 : Aexp V)
--      -- … then `Bexp V`, `Com V`, `abbrev State (V) [DecidableEq V] :=
--      -- TotalMap V Nat`, and `[DecidableEq V]` wherever a lookup/update is
--      -- performed.`

--  The `Bexp` definition is unchanged, except that it now
--  refers to the new `Aexp`.

inductive Bexp where
  | bool (b : Bool)
  | eq (a1 a2 : Aexp)
  | neq (a1 a2 : Aexp)
  | le (a1 a2 : Aexp)
  | gt (a1 a2 : Aexp)
  | not (b : Bexp)
  | and (b1 b2 : Bexp)

--  Defining a few variable names as shorthands will make
--  examples easier to read.

def W : Ident := "W"
def X : Ident := "X"
def Y : Ident := "Y"
def Z : Ident := "Z"

--  ### Notations

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

open Lean in
macro_rules
  | `(aexp { $n:num }) => `(Aexp.num $(quote n.getNat))
  | `(aexp { $x:ident }) => `(Aexp.id $x)
  | `(aexp { ~$e }) => pure e
  | `(aexp { $a + $b }) => `(Aexp.plus (aexp {$a}) (aexp {$b}))
  | `(aexp { $a - $b }) => `(Aexp.minus (aexp {$a}) (aexp {$b}))
  | `(aexp { $a * $b }) => `(Aexp.mult (aexp {$a}) (aexp {$b}))
  | `(aexp { ($a) }) => `(aexp {$a})

--  THESE DETAILS CAN BE SKIPPED: Notation encoding: boolean expressions

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

--  THESE DETAILS CAN BE SKIPPED: Notation encoding: boolean expressions, macro rules

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
  | `(bexp { $b1:imp_bexp ∧ $b2:imp_bexp }) => `(Bexp.and (bexp {$b1}) (bexp {$b2}))
  | `(bexp { ($b:imp_bexp) }) => `(bexp {$b})

--  END DETAILS

#check aexp { 3 + (X * 2) }
#check bexp { true ∧ ¬(X ≤ 4) }

--  ### Delaborators

--  THESE DETAILS CAN BE SKIPPED: Notation encoding: printing expressions back

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
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_aexp| $s1 + $s2)
    | Aexp.minus _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_aexp| $s1 - $s2)
    | Aexp.mult _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_aexp| $s1 * $s2)
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
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp = $s2:imp_aexp)
    | Bexp.neq _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp ≠ $s2:imp_aexp)
    | Bexp.le _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp ≤ $s2:imp_aexp)
    | Bexp.gt _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp > $s2:imp_aexp)
    | Bexp.not _ =>
      let s ← withAppArg delabBexpInner
      `(imp_bexp| ¬ $s)
    | Bexp.and _ _ =>
      let s1 ← withAppFn <| withAppArg delabBexpInner
      let s2 ← withAppArg delabBexpInner
      `(imp_bexp| $s1 ∧ $s2)
    | _ => `(imp_bexp| ~$(← delab))
  annAsTerm stx

--  END DETAILS

--  The `whenPPOption getPPNotation` wrapper lets
--  `set_option pp.notation false` switch this delaborator
--  off, revealing the raw constructors (see the "Desugaring
--  Notations" discussion, after the commands are
--  introduced).

--  THESE DETAILS CAN BE SKIPPED: Notation encoding: registering the delaborators

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
  | plus  a1 a2 =>  a1.eval st + a2.eval st
  | minus a1 a2 =>  a1.eval st - a2.eval st
  | mult  a1 a2 =>  a1.eval st * a2.eval st

def Bexp.eval (st : State) (b : Bexp) : Bool :=
  match b with
  | bool b      =>  b
  | eq   a1 a2  =>  a1.eval st == a2.eval st
  | neq  a1 a2  =>  a1.eval st != a2.eval st
  | le   a1 a2  =>  a1.eval st ≤  a2.eval st
  | gt   a1 a2  =>  a1.eval st >  a2.eval st
  | not  b1     =>  !b1.eval st
  | and  b1 b2  =>  b1.eval st && b2.eval st

@[simp] theorem Aexp.eval_num (st : State) (n : Nat) : (num n).eval st = n := rfl
@[simp] theorem Aexp.eval_id (st : State) (x : Ident) : (Aexp.id x).eval st = st[x] := rfl
@[simp] theorem Aexp.eval_plus (st : State) (a1 a2 : Aexp) :
    (plus a1 a2).eval st = a1.eval st + a2.eval st := rfl
@[simp] theorem Aexp.eval_minus (st : State) (a1 a2 : Aexp) :
    (minus a1 a2).eval st = a1.eval st - a2.eval st := rfl
@[simp] theorem Aexp.eval_mult (st : State) (a1 a2 : Aexp) :
    (mult a1 a2).eval st = a1.eval st * a2.eval st := rfl

@[simp] theorem Bexp.eval_bool (st : State) (b : Bool) : (bool b).eval st = b := rfl
@[simp] theorem Bexp.eval_eq (st : State) (a1 a2 : Aexp) :
    (eq a1 a2).eval st = (a1.eval st == a2.eval st) := rfl
@[simp] theorem Bexp.eval_neq (st : State) (a1 a2 : Aexp) :
    (neq a1 a2).eval st = (a1.eval st != a2.eval st) := rfl
@[simp] theorem Bexp.eval_le (st : State) (a1 a2 : Aexp) :
    (le a1 a2).eval st = (a1.eval st ≤ a2.eval st : Bool) := rfl
@[simp] theorem Bexp.eval_gt (st : State) (a1 a2 : Aexp) :
    (gt a1 a2).eval st = (a1.eval st > a2.eval st : Bool) := rfl
@[simp] theorem Bexp.eval_not (st : State) (b : Bexp) : (not b).eval st = !b.eval st := rfl
@[simp] theorem Bexp.eval_and (st : State) (b1 b2 : Bexp) :
    (and b1 b2).eval st = (b1.eval st && b2.eval st) := rfl

--  We reuse the total-map notation (`x →ₜ v ; ∅` etc.) for
--  states.

example : aexp { 3 + (X * 2) }.eval (X →ₜ 5 ; ∅) = 13 := by rfl

example : aexp { Z + (X * Y) }.eval (X →ₜ 5 ; Y →ₜ 4 ; ∅) = 20 := by rfl

example : bexp { true ∧ ¬(X ≤ 4) }.eval (X →ₜ 5 ; ∅) = true := by rfl

--  Note to developers:
--      dsainati: Bikeshedding: I'm not sure how I feel
--      about this arrow subscript for maps. Easy to change
--      later but just flagging to discuss. mwhicks1: This
--      comes from the Maps chapter, which chenson2018 is
--      working on. There is a keyboard shortcut for ↦ we
--      could use (mapsto).

--  ## Commands

inductive Com where
  | skip
  | asgn (x : Ident) (a : Aexp)
  | seq (c1 c2 : Com)
  | cond (b : Bexp) (c1 c2 : Com)
  | whileDo (b : Bexp) (c : Com)

--  THESE DETAILS CAN BE SKIPPED: Notation encoding: commands, macro rules

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
  | `(imp { $c1 ; $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { ~$c }) =>
    pure c

end Com

open scoped Com

--  END DETAILS

--  THESE DETAILS CAN BE SKIPPED: Notation encoding: printing commands back

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
      let s1 ← withAppFn <| withAppArg (delabComInnerFor ns extra)
      let s2 ← withAppArg (delabComInnerFor ns extra)
      `(imp_com| $s1; $s2)
    else if e.isAppOfArity (ns ++ `cond) 3 then
      let b  ← withAppFn <| withAppFn <| withAppArg delabBexpInner
      let c1 ← withAppFn <| withAppArg (delabComInnerFor ns extra)
      let c2 ← withAppArg (delabComInnerFor ns extra)
      `(imp_com| if ($b) {$c1} else {$c2})
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
  | imp {~c1; ~c2} =>
      let st' := ceval_fun_no_while st c1
      ceval_fun_no_while st' c2
  | imp {if (~b) {~c1} else {~c2}} =>
      if b.eval st then ceval_fun_no_while st c1
      else ceval_fun_no_while st c2
  | imp {while (~_) {~_}} => st     -- bogus

--  Note to developers:
--      Perhaps that discussion should be moved to -- or
--      previewed in -- Logic.v? MRC'20: It's already in
--      ProofObjects (which not everyone sees).

--  A nonterminating
--  `def loop_false (n) : False := loop_false n` would make
--  `False` provable, so Lean rejects it.

--  ### Evaluation as a Relation

--  Here's a better way: define `ceval` as a *relation*
--  rather than a *function* -- i.e., make its result a
--  `Prop` rather than a `State`, similar to what we did for
--  `Aexp.EvalR` above.

--  Note to developers (Michael Hicks @mwhicks1):
--      I kind of hate this notation. Is there something
--      more standard in Lean? CSLib precedent maybe?

--  We'll use the notation `st =[ c ]=> st'` for the
--  `Com.EvalR` relation: `st =[ c ]=> st'` means that
--  executing program `c` in a starting state `st` results
--  in an ending state `st'`. This can be pronounced "`c`
--  takes state `st` to `st'`".

--  Operational Semantics

--  Note to developers (before next release):
--      BCP 21: I wonder if `seq` would be easier to work
--      with if st' and st'' were swapped...

--  Here is an informal definition of evaluation, presented
--  as inference rules for readability:

--                          -----------------                  (skip)
--                          st =[ skip ]=> st

--                          a.eval st = n
--                  --------------------------------           (asgn)
--                  st =[ x := a ]=> (x →ₜ n ; st)

--                          st  =[ c1 ]=> st'
--                          st' =[ c2 ]=> st''
--                        ---------------------                (seq)
--                        st =[ c1;c2 ]=> st''

--                         b.eval st = true
--                          st =[ c1 ]=> st'
--               --------------------------------------        (ifTrue)
--               st =[ if b then c1 else c2 end ]=> st'

--                        b.eval st = false
--                          st =[ c2 ]=> st'
--               --------------------------------------        (ifFalse)
--               st =[ if b then c1 else c2 end ]=> st'

--                        b.eval st = false
--                   -----------------------------             (whileFalse)
--                   st =[ while b do c end ]=> st

--                         b.eval st = true
--                          st =[ c ]=> st'
--                 st' =[ while b do c end ]=> st''
--                 --------------------------------            (whileTrue)
--                 st  =[ while b do c end ]=> st''

--  Here is the formal definition. Make sure you understand
--  how it corresponds to the inference rules.

--  Note to developers (Chris Henson @chenson2018):
--      TODO Propose you use inline notation such as
--      `Com.EvalR (imp {skip;}) st st`

inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} : EvalR (imp {skip}) st st
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (x →ₜ n ; st)
  | seq {c1 c2 : Com} {st st' st'' : State} (h1 : EvalR c1 st st') (h2 : EvalR c2 st' st'') :
      EvalR (imp {~c1; ~c2}) st st''
  | ifTrue {st st' : State} {b : Bexp} {c1 c2 : Com} (hb : b.eval st = true)
      (hc : EvalR c1 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2}}) st st'
  | ifFalse {st st' : State} {b : Bexp} {c1 c2 : Com} (hb : b.eval st = false)
      (hc : EvalR c2 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2}}) st st'
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c}}) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st') (hloop : Com.EvalR (imp {while (~b) {~c}}) st' st'') :
      EvalR (imp {while (~b) {~c}}) st st''

--  Note to developers (Niklas Halonen @xhalo32):
--      Setting `In` and `Out` as `outParam`s is a hack to
--      resolve various typeclass synthesis problems or at
--      least I can't explain why it works.

class HasEval (Com : Type) (In : outParam <| Type) (Out : outParam <| Type) where
  Eval : Com → In → Out → Prop

namespace HasEval
scoped notation:40 st0:41 " =[ " c " ]=> " st1:41 => Eval c st0 st1

-- Also accept a bare Imp command between the brackets, so concrete programs can
-- be written without the `imp { … }` wrapper. Bare `Com` terms still work via the
-- notation above; splice a Lean term into the command with `~`.
scoped syntax:40 term:41 " =[ " imp_com " ]=> " term:41 : term
scoped macro_rules
  | `($st0 =[ $c:imp_com ]=> $st1) => ``($st0 =[ imp { $c } ]=> $st1)
end HasEval

instance : HasEval Com State State where
  Eval := Com.EvalR

open scoped HasEval

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()

--  Note to developers (Niklas Halonen @xhalo32):
--      Currently in Hoare.lean the info view in
--
--      `theorem hoare_skip (P : Assertion) :
--          {{ P }} skip {{ P }} := by
--        intro st st' h hp`
--
--      displays
--
--      `P : Assertion
--      st st' : State
--      h : st =[
--        imp {
--          skip
--        } ]=>
--        st'
--      hst : P st
--      ⊢ P st'`
--
--      but we would like it to display
--      `h : st =[ skip ]=> st'`.
--
--      This issue is also relevant for other `EvalR`
--      present in Hoare.lean.

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

--  ### Exercise (2 stars): ceval_example2 ⭐⭐

example :
    ∅ =[
      X := 0;
      Y := 1;
      Z := 2
    ]=> (Z →ₜ 2 ; Y →ₜ 1 ; X →ₜ 0 ; ∅) := by
  sorry

--  What sorts of things might we want to prove using these
--  definitions? Here are some simple examples...

--  Note to developers:
--      PR: I phrased these quizzes with the following
--      alternatives: (A) Not true (B) True and easily
--      provable (C) True and takes more work to prove (D)
--      True and cannot be proved without additional axioms

--  _Quiz:_

--  Is the following proposition provable?

--    ∀ (c : Com) (st st' : State),
--      st =[ skip; ~c ]=> st' →
--      st =[ c ]=> st'

--  (A) Yes (B) No (C) Not sure

--  _Quiz:_

--  Is the following proposition provable?

--    ∀ (c1 c2 : Com) (st st' : State),
--      st =[ ~c1 ~c2 ]=> st' →
--      st =[ c1 ]=> st →
--      st =[ c2 ]=> st'

--  (A) Yes (B) No (C) Not sure

--  _Quiz:_

--  Is the following proposition provable?

--    ∀ (b : Bexp) (c : Com) (st st' : State),
--      st =[ if (~b) { ~c } else { ~c } ]=> st' →
--      st =[ c ]=> st'

--  (A) Yes (B) No (C) Not sure

--  _Quiz:_

--  Is the following proposition provable?

--    ∀ (b : Bexp),
--      (∀ st, b.eval st = true) →
--      ∀ (c : Com) (st : State),
--      ¬ ∃ st', st =[ while (~b) { ~c } ]=> st'

--  (A) Yes (B) No (C) Not sure

--  _Quiz:_

--  Is the following proposition provable?

--    ∀ (b : Bexp) (c : Com) (st : State),
--      (¬ ∃ st', st =[ while (~b) { ~c } ]=> st') →
--      ∀ st'', b.eval st'' = true

--  (A) Yes (B) No (C) Not sure

--  ### Determinism of Evaluation

--  Finally, we should pause to check that our evaluation
--  relation really is a (partial) function...

theorem ceval_deterministic (c : Com) (st st1 st2 : State)
    (e1 : st =[ c ]=> st1) (e2 : st =[ c ]=> st2) : st1 = st2 := by
  induction e1 generalizing st2 with
  | @skip st =>
      inversion e2
      rfl
  | @asgn st a n x h =>
      inversion e2 with
      | asgn h' => subst h; subst h'; rfl
  | @seq c1 c2 st st' st'' h1 h2 ih1 ih2 =>
      inversion e2 with
      | seq st2' h1' h2' =>
          have hst : st' = st2' := ih1 _ h1'
          subst hst
          exact ih2 _ h2'
  | @ifTrue st st' b c1 c2 hb hc ih =>
      inversion e2 with
      | ifTrue hb' hc' => exact ih _ hc'
      | ifFalse hb' hc' => simp_all
  | @ifFalse st st' b c1 c2 hb hc ih =>
      inversion e2 with
      | ifTrue hb' hc' => simp_all
      | ifFalse hb' hc' => exact ih _ hc'
  | @whileFalse b st c hb =>
      inversion e2 with
      | whileFalse hb' => rfl
      | whileTrue hb' hc' hl' => simp_all
  | @whileTrue st st' st'' b c hb hc hloop ih1 ih2 =>
      inversion e2 with
      | whileFalse hb' => simp_all
      | whileTrue st2' _ hc' hl' =>
          have hst : st' = st2' := ih1 _ hc'
          subst hst
          exact ih2 _ hl'

--  ### Exercise (3 stars): pup_to_n (Optional) ⭐⭐⭐

--  Write an Imp program that sums the numbers from `1` to
--  `X` (inclusive) in the variable `Y`. Your program should
--  update the state as shown in `pup_to_2_ceval`, which you
--  can reverse-engineer to discover the program you should
--  write. The proof of that theorem will be somewhat
--  lengthy.

def pup_to_n : Com := sorry

theorem pup_to_2_ceval :
    (X →ₜ 2 ; ∅) =[ pup_to_n ]=>
      (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅) := by
  sorry

--  ## Reasoning About Imp Programs

theorem plus2_spec (st : State) (n : Nat) (st' : State)
    (hx : st[X] = n) (heval : st =[ plus2 ]=> st') :
    st'[X] = n + 2 := by
  -- Inverting `heval` forces one step of the `ceval` computation: since
  -- `plus2` is an assignment, `st'` must be `st` extended at `X`.
  unfold plus2 at heval
  inversion heval with
  | asgn m h =>
      simp only [Aexp.eval_plus, Aexp.eval_id, Aexp.eval_num] at h
      rw [TotalMap.update_eq]
      lia

--  ### Exercise (3 stars): XtimesYinZ_spec (Optional) ⭐⭐⭐

--  State and prove a specification of `XtimesYinZ`.

-- FILL IN HERE

--  Note to developers (Niklas Halonen @xhalo32):
--      We should use the `generalize` tactic here instead
--      of `have key`. I've changed some Hoare proofs from
--      `have key` to `generalize` but the tactic hasn't
--      been explained yet.

--  ### Exercise (3 stars): loop_never_stops ⭐⭐⭐

--  Hint: proceed by induction on the assumed derivation
--  showing that `loop` terminates. Most of the cases are
--  immediately contradictory and so can be solved in one
--  step (by `simp`/`discriminate` on the impossible command
--  equation).

theorem loop_never_stops (st st' : State) : ¬ (st =[ loop ]=> st') := by
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
  | imp {~c1; ~c2} => no_whiles c1 && no_whiles c2
  | imp {if (~_) {~ct} else {~cf}} => no_whiles ct && no_whiles cf
  | imp {while (~_) {~_}} => false

inductive Com.NoWhilesR : Com → Prop where
  -- FILL IN HERE

theorem no_whiles_eqv (c : Com) : c.no_whiles = true ↔ Com.NoWhilesR c := by
  sorry

--  ### Exercise (4 stars): no_whiles_terminating ⭐⭐⭐⭐

--  Imp programs that don't involve while loops always
--  terminate. State and prove a theorem
--  `no_whiles_terminating` that says this. Use either
--  `Com.no_whiles` or `Com.NoWhilesR`, as you prefer.

theorem no_whiles_terminating (c : Com) (st : State) (h : Com.NoWhilesR c) :
    ∃ st', st =[ c ]=> st' := by
  sorry

--  And here is an alternative solution by induction on `c`
--  (using `Com.no_whiles` instead of `Com.NoWhilesR`):

-- FILL IN HERE

--  Note to developers (Michael Hicks @mwhicks1):
--      `NOT PORTED YET — remaining sections of sfdev/lf/Imp.v to port:
--        - Case Study (Optional), Imp.v:2774
--            * subtract_slowly_spec (EX4?, Imp.v:2919): loop-invariant style proof
--              about `subtract_slowly`.
--        - Additional Exercises, Imp.v:2986
--            * stack_compiler (EX3, Imp.v:2988): define `s_execute` (stack machine)
--              and `s_compile : aexp -> list sinstr`; needs a `SInstr` inductive
--              (SPush/SLoad/SPlus/SMinus/SMult) and a list-based stack.
--            * execute_app (EX3, Imp.v:3114)
--            * stack_compiler_correct (EX3, Imp.v:3134): the correctness theorem;
--              the standard proof needs a strengthened lemma over an arbitrary
--              initial stack (generalize the stack before inducting).
--            * short_circuit (EX3?, Imp.v:3184): short-circuiting `Bexp.eval`.
--            * break_imp (EX4?, Imp.v:3227): extends Com with `CBreak`; new
--              relational semantics `ceval` carrying a `result` (SContinue/SBreak).
--              Large. See verso-book branch (lf/Imp.lean ~line 1141, CEvalBreak) for
--              a prior take on the signal type.
--            * while_break_true (EX3A?, Imp.v:3454)
--            * ceval_deterministic for break (EX4A?, Imp.v:3477)
--            * exn_imp (EX4A?, Imp.v:3524): exceptions variant. Large.
--            * add_for_loop (EX4?, Imp.v:3728): add a C-style `for` loop to Com,
--              its notation, and extend ceval.`

--  Note to developers:
--      `HTML polish — deferred Verso-markup opportunities for a later pass (see
--      CONTRIBUTING.md, "Verso markup for nicer HTML"):
--      * {name} was applied to resolvable declaration references in visible prose.
--        More could be added, but bare type names were linked only selectively (avoid
--        over-linking; mind forward references and namespace scope — a name must
--        already be defined and in scope at that point in the document, or {name} fails
--        to build).
--      * {ref "tag"} cross-references link "see the X section" phrasings; add a
--        `%%% tag := "…" %%%` block under a heading to make it a target. Done for the
--        Notations and Delaborators sections; more internal "above/below" phrasings
--        could get the same treatment.
--      * {tactic}`simp` — link tactic names in the automation/tactics prose (`try`,
--        `repeat`, `<;>`, `simp`, `lia`, `cases`, `induction`).
--      * {deftech}/{tech} — a small glossary: define Imp's core terms once with
--        {deftech} (abstract syntax, state, big-step, relation, partial function, …)
--        and link later uses with {tech}.
--      * {lean}`expr` — inline elaborated expressions/types where a whole expression,
--        not just a single name, reads better with hover types (e.g. the
--        `Coe Ident Aexp` / `OfNat Aexp n` bullets in the Notations section).`


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
--  current values, we'll use total maps from the
--  `Typeclasses` chapter. A *machine state* (or just
--  *state*) represents the current values of all variables
--  at some point in the execution of a program.
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
--  from the Slang chapter.)

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
/-- `Ident` or Lean identifier -/
syntax:max ident : imp_aexp
/-- Addition -/
syntax:65 imp_aexp:65 " + " imp_aexp:66 : imp_aexp
/-- Subtraction -/
syntax:65 imp_aexp:65 " - " imp_aexp:66 : imp_aexp
/-- Multiplication -/
syntax:70 imp_aexp:70 " * " imp_aexp:71 : imp_aexp
/-- Parentheses for grouping -/
syntax:max "(" imp_aexp ")" : imp_aexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_aexp

/-- Embed an Imp arithmetic expression into a Lean term -/
syntax:80 "aexp " "{" imp_aexp "}" : term
--  END DETAILS

namespace Imp.Elab

open Lean Elab Term Meta

def withSourceInfoOf {kind : Name} (ref : Syntax) (stx : TSyntax kind)
    (canonical := true) : TSyntax kind :=
  let info := SourceInfo.fromRef ref (canonical := canonical)
  ⟨stx.raw.setInfo info⟩

macro_rules
  | `(aexp { $exp:imp_aexp }) => do
    let stx ← match exp with
      | `(imp_aexp| $n:num) => ``(Aexp.num $n)
      | `(imp_aexp| ~$e:term) => ``(($e : Aexp))
      | `(imp_aexp| $a + $b) => ``(Aexp.plus (aexp {$a}) (aexp {$b}))
      | `(imp_aexp| $a - $b) => ``(Aexp.minus (aexp {$a}) (aexp {$b}))
      | `(imp_aexp| $a * $b) => ``(Aexp.mult (aexp {$a}) (aexp {$b}))
      | `(imp_aexp| ($a)) => ``(aexp {$a})
      | _ => Lean.Macro.throwUnsupported
    return withSourceInfoOf exp stx

elab_rules : term
  | `(aexp { $x:ident }) => do
    let some e ← resolveId? x (withInfo := true)
      | throwErrorAt x "unknown identifier `{x.getId.eraseMacroScopes}`"
    let type ← whnf (← inferType e)
    tryPostponeIfMVar type
    match_expr type with
    | Aexp => pure e
    | String => mkAppM ``Aexp.id #[e]
    | _ => throwErrorAt x "expected an Imp identifier or arithmetic expression"

end Imp.Elab

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: boolean expressions)
/-- Boolean expressions of Imp -/
declare_syntax_cat imp_bexp
/-- Boolean literal (`true` or `false`) and Lean identifier -/
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
/-- Boolean conjunction (right associative) -/
syntax:35 imp_bexp:36 " ∧ " imp_bexp:35 : imp_bexp
/-- Parentheses for grouping -/
syntax:max "(" imp_bexp ")" : imp_bexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_bexp

/-- Embed an Imp boolean expression into a Lean term -/
syntax:80 "bexp " "{" imp_bexp "}" : term
--  END DETAILS

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: boolean expressions, macro rules)
namespace Imp.Elab

open Lean

macro_rules
  | `(bexp { $exp:imp_bexp }) => do
    let stx ← match exp with
      | `(imp_bexp| true) => ``(Bexp.bool true)
      | `(imp_bexp| false) => ``(Bexp.bool false)
      | `(imp_bexp| $x:ident) => ``(($x : Bexp))
      | `(imp_bexp| ~$e:term) => ``(($e : Bexp))
      | `(imp_bexp| $a:imp_aexp = $b:imp_aexp) => ``(Bexp.eq (aexp {$a}) (aexp {$b}))
      | `(imp_bexp| $a:imp_aexp ≠ $b:imp_aexp) => ``(Bexp.neq (aexp {$a}) (aexp {$b}))
      | `(imp_bexp| $a:imp_aexp ≤ $b:imp_aexp) => ``(Bexp.le (aexp {$a}) (aexp {$b}))
      | `(imp_bexp| $a:imp_aexp > $b:imp_aexp) => ``(Bexp.gt (aexp {$a}) (aexp {$b}))
      | `(imp_bexp| ¬ $b:imp_bexp) => ``(Bexp.not (bexp {$b}))
      | `(imp_bexp| $b₁:imp_bexp ∧ $b₂:imp_bexp) => ``(Bexp.and (bexp {$b₁}) (bexp {$b₂}))
      | `(imp_bexp| ($b:imp_bexp)) => ``(bexp {$b})
      | _ => Macro.throwUnsupported
    return withSourceInfoOf exp stx

end Imp.Elab
--  END DETAILS

#check aexp { 3 + (X * 2) }
#check bexp { true ∧ ¬(X ≤ 4) }

--  ### Delaborators

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing expressions back)
namespace Imp.Delab

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer Imp.Elab

@[category_parenthesizer imp_aexp]
def imp_aexp.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `imp_aexp true wrapParens prec <|
    parenthesizeCategoryCore `imp_aexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let stxInfo := SourceInfo.fromRef stx
    let stx := stx.setInfo .none
    let pstx ← `(imp_aexp| ($(⟨stx⟩)))
    return pstx.raw.setInfo stxInfo

@[category_parenthesizer imp_bexp]
def imp_bexp.parenthesizer : CategoryParenthesizer := fun prec => do
  Parenthesizer.maybeParenthesize `imp_bexp true wrapParens prec <|
    Parenthesizer.parenthesizeCategoryCore `imp_bexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let stxInfo := SourceInfo.fromRef stx
    let stx := stx.setInfo .none
    let pstx ← `(imp_bexp| ($(⟨stx⟩)))
    return pstx.raw.setInfo stxInfo
--  END DETAILS

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: registering the delaborators)
/--
Recognizes a term as being an `aexp { ... }` expression.
-/
def getAexp (stx : Term) : TSyntax `imp_aexp :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(aexp { $e:imp_aexp }) => return e
    | _ => `(imp_aexp| ~$stx)

@[app_unexpander Aexp.num]
private def Aexp.unexpandNum : Unexpander
  | `($_ $n:num) => `(aexp { $n:num })
  | _ => throw ()

@[app_unexpander Aexp.id]
private def Aexp.unexpandId : Unexpander
  | `($_ $x:ident) => `(aexp { $x:ident })
  | _ => throw ()

@[app_unexpander Aexp.plus]
private def Aexp.unexpandPlus : Unexpander
  | `($_ $a $b) => `(aexp { $(getAexp a) + $(getAexp b) })
  | _ => throw ()

@[app_unexpander Aexp.minus]
private def Aexp.unexpandMinus : Unexpander
  | `($_ $a $b) => `(aexp { $(getAexp a) - $(getAexp b) })
  | _ => throw ()

@[app_unexpander Aexp.mult]
private def Aexp.unexpandMult : Unexpander
  | `($_ $a $b) => `(aexp { $(getAexp a) * $(getAexp b) })
  | _ => throw ()

/--
Recognizes a term as being an `bexp { ... }` expression.
-/
def getBexp (stx : Term) : TSyntax `imp_bexp :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(bexp { $e:imp_bexp }) => return e
    | _ => `(imp_bexp| ~$stx)

/--
Delaborator for `Bexp.bool`. This is needed since we want to be sure we are
matching on the actual `true`/`false` expressions, rather than matching on the
delaborated identifiers `true`/`false` (which might not be accurate).
-/
@[app_delab Bexp.bool]
private def BExp.delabBool : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isAppOfArity ``Bexp.bool 1
  match_expr e.appArg! with
  | true => `(bexp { $(mkIdent `true):ident })
  | false => `(bexp { $(mkIdent `false):ident })
  | _ => failure


@[app_unexpander Bexp.eq]
private def Bexp.unexpandEq : Unexpander
  | `($_ $a $b) => `(bexp { $(getAexp a):imp_aexp = $(getAexp b):imp_aexp })
  | _ => throw ()

@[app_unexpander Bexp.neq]
private def Bexp.unexpandNeq : Unexpander
  | `($_ $a $b) => `(bexp { $(getAexp a):imp_aexp ≠ $(getAexp b):imp_aexp })
  | _ => throw ()

@[app_unexpander Bexp.le]
private def Bexp.unexpandLe : Unexpander
  | `($_ $a $b) => `(bexp { $(getAexp a):imp_aexp ≤ $(getAexp b):imp_aexp })
  | _ => throw ()

@[app_unexpander Bexp.gt]
private def Bexp.unexpandGt : Unexpander
  | `($_ $a $b) => `(bexp { $(getAexp a):imp_aexp > $(getAexp b):imp_aexp })
  | _ => throw ()

@[app_unexpander Bexp.not]
private def Bexp.unexpandNot : Unexpander
  | `($_ $a) => `(bexp { ¬ $(getBexp a):imp_bexp })
  | _ => throw ()

@[app_unexpander Bexp.and]
private def Bexp.unexpandAnd : Unexpander
  | `($_ $a $b) => `(bexp { $(getBexp a):imp_bexp ∧ $(getBexp b):imp_bexp })
  | _ => throw ()

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

--  We reuse the total-map notation (`x →ₜ v` etc.) for
--  states.

example : aexp { 3 + (X * 2) }.eval (X →ₜ 5) = 13 := by rfl

example : aexp { Z + (X * Y) }.eval (X →ₜ 5 ; Y →ₜ 4) = 20 := by rfl

example : bexp { true ∧ ¬(X ≤ 4) }.eval (X →ₜ 5) = true := by rfl

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
syntax:max ident : imp_com
/-- Sequencing: one command after another (right associative. min + 1 = 11) -/
syntax:80 imp_com:11 Lean.Parser.semicolonOrLinebreak ppHardSpace imp_com:min : imp_com
/-- Assignment -/
syntax:max ident ppHardSpace ":=" ppHardSpace imp_aexp : imp_com
/-- Conditional -/
syntax:max "if " "(" imp_bexp ")" ppHardSpace "{" imp_com "}" ppHardSpace "else" ppHardSpace "{" imp_com "}" : imp_com
/-- Loop -/
syntax:max "while " "(" imp_bexp ")" ppHardSpace "{" imp_com "}" : imp_com
/-- Escape to Lean -/
syntax:max "~" term:max : imp_com

/-- Include an Imp command in Lean code -/
syntax:80 "imp" ppHardSpace "{" imp_com "}" : term

namespace Com

open Lean Imp.Elab

scoped macro_rules
  | `(imp { $s }) => do
    let stx ← match s with
      | `(imp_com| skip) => ``(Com.skip)
      | `(imp_com| $x:ident) => ``(($x : Com))
      | `(imp_com| $c₁ ; $c₂) =>
        ``(Com.seq (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| $x:ident := $a) =>
        ``(Com.asgn $x (aexp {$a}))
      | `(imp_com| if ($b) {$c₁} else {$c₂}) =>
        ``(Com.cond (bexp {$b}) (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| while ($b) {$c}) =>
        ``(Com.whileDo (bexp {$b}) (imp {$c}))
      | `(imp_com| ~$c) => `(($c : Com))
      | _ => Macro.throwUnsupported
    return withSourceInfoOf s stx

end Com

open scoped Com
--  END DETAILS

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing commands back)
namespace Imp.Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Elab

/--
Recognizes a term as being an `imp { ... }` expression.
-/
def getImp (stx : Term) : TSyntax `imp_com :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(imp { $e:imp_com }) => return e
    | _ => `(imp_com| ~$stx)

@[app_unexpander Com.skip]
def unexpandComSkip : Unexpander
  | _ => `(imp { $(mkIdent `skip):ident })

@[app_unexpander Com.asgn]
def unexpandComAsgn : Unexpander
  | `($_ $x:ident $a) => `(imp { $x:ident := $(getAexp a) })
  | _ => throw ()

@[app_unexpander Com.seq]
def unexpandComSeq : Unexpander
  | `($_ $a $b) =>
    match a with
    | `(imp { $_ ; $_ }) =>
      -- seq syntax is right associative, so need to quote `a`
      `(imp { ~$a ; $(getImp b):imp_com })
    | _ =>
      `(imp { $(getImp a):imp_com ; $(getImp b):imp_com })
  | _ => throw ()

@[app_unexpander Com.cond]
def unexpandComCond : Unexpander
  | `($_ $b $c₁ $c₂) => `(imp { if ($(getBexp b)) { $(getImp c₁) } else { $(getImp c₂) } })
  | _ => throw ()

@[app_unexpander Com.whileDo]
def unexpandComWhileDo : Unexpander
  | `($_ $b $c) => `(imp { while ($(getBexp b)) { $(getImp c) } })
  | _ => throw ()

end Imp.Delab
--  END DETAILS

def fact_in_lean : Com := imp {
  Z := X
  Y := 1
  while (Z ≠ 0) {
    Y := Y * Z
    Z := Z - 1
  }
}

#print fact_in_lean

--  Output:
--    def fact_in_lean : Com :=
--    imp {Z := X; Y := 1; while (Z ≠ 0) {Y := Y * Z; Z := Z - 1}}

--  ### Desugaring Notations

--  Even though the notations are useful for getting the
--  high-level picture, it's sometimes helpful to turn off
--  the notation to see the parsed structure as a plain
--  term. This can be done with
--  `set_option pp.notation false` (which we briefly
--  mentioned in the `Typeclasses` chapter) as follows:

#check imp { X := X + 1 }

--  Output:
--    imp {X := X + 1} : Com

set_option pp.notation false in
#check imp { X := X + 1 }

--  Output:
--    Com.asgn X ((Aexp.id X).plus (Aexp.num 1)) : Com

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

--  In a more conventional functional language like OCaml or
--  Haskell we could define the evaluation function as
--  follows:

sf_expect_failure_in
  def Com.eval (st : State) (c : Com) : State :=
    match c with
    | imp {skip} => st
    | imp {x := ~a} => (x →ₜ a.eval st ; st)
    | imp {c₁; c₂} =>
        let st' := eval st c₁
        eval st' c₂
    | imp {if (b) {c₁} else {c₂}} =>
        if b.eval st then eval st c₁
        else eval st c₂
    | imp {while (b) {c}} =>
        if b.eval st then eval st (imp { c; while (b) {c}})
        --                ^-- recursive call without a decreasing argument
        else st

--  Output:
--    fail to show termination for
--      Com.eval
--    with errors
--    failed to infer structural recursion:
--    Cannot use parameter st:
--      the type TotalMap Ident Nat does not have a `.brecOn` recursor
--    Cannot use parameter c:
--      failed to eliminate recursive application
--        eval st (imp {~c; while (~b) {~c}})
--
--
--    failed to prove termination, possible solutions:
--      - Use `have`-expressions to prove the remaining goals
--      - Use `termination_by` to specify a different well-founded relation
--      - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
--    st : State
--    b : Bexp
--    c : Com
--    h✝ : Bexp.eval st b = true
--    ⊢ 1 + sizeOf c + (1 + sizeOf b + sizeOf c) < 1 + sizeOf b + sizeOf c

--  A nonterminating
--  `theorem loop_false (n : Nat) : False := loop_false n`
--  would make `False` provable, so Lean rejects it.

--  ### Evaluation as a Relation

--  Here's a better way: define `Com.eval` as a *relation*
--  rather than a *function* -- i.e., make its result a
--  `Prop` rather than a `State`, similar to what we did for
--  `Aexp.EvalR` in the Slang chapter.

--  We'll use the notation `st =[ c ]=> st'` for the
--  `Com.EvalR` relation: `st =[ c ]=> st'` means that
--  executing program `c` in a starting state `st` results
--  in an ending state `st'`. This can be pronounced "`c`
--  takes state `st` to `st'`".

--  ### Operational Semantics

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
      EvalR (imp {x := a}) st (x →ₜ n ; st)
  | seq {c₁ c₂ : Com} {st st' st'' : State} (h₁ : EvalR c₁ st st') (h₂ : EvalR c₂ st' st'') :
      EvalR (imp {c₁; c₂}) st st''
  | ifTrue {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = true)
      (hc : EvalR c₁ st st') :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st'
  | ifFalse {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = false)
      (hc : EvalR c₂ st st') :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st'
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (b) {c}}) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st') (hloop : Com.EvalR (imp {while (b) {c}}) st' st'') :
      EvalR (imp {while (b) {c}}) st st''

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: commands)
class HasEval (Com : Type) (In : outParam <| Type) (Out : outParam <| Type) where
  Eval : Com → In → Out → Prop

namespace HasEval
/-- Evaluation: `st =[ c ]=> st'` with `imp_com` command syntax -/
scoped syntax:lead term " =[ " imp_com:min " ]=> " term : term
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

@[simp]
theorem Com.evalR_eq {c : Com} {st st' : State} :
    EvalR c st st' ↔ st =[ c ]=> st' := by rfl
--  END DETAILS

--  The cost of defining evaluation as a relation instead of
--  a function is that we now need to construct a *proof*
--  that some program evaluates to some result state, rather
--  than letting Lean's computation mechanism do it for us.

open scoped KVPair
open Com

example :
    ∅ =[
      X := 2;
      if (X ≤ 1) {
        Y := 3
      } else {
        Z := 4
      }
    ]=> {Z ↦ 4, X ↦ 2} := by
  -- To supply the intermediate state to the `seq` rule, which is sometimes necessary,
  -- we can write `Com.EvalR.seq (st' := ...)`.
  apply EvalR.seq (st' := {X ↦ 2})
  · exact EvalR.asgn rfl
  · apply EvalR.ifFalse
    · rfl
    · exact EvalR.asgn rfl

--  Since the total map update notation (`→ₜ`) is difficult
--  to type, we prefer to use the `{}`-notation with
--  `KVPair`s.
--
--  In the above proof, using `EvalR.asgn rfl` is convenient
--  because it computes the value of the right hand side and
--  can use it to determine `st'`.

example {x : Nat} : ∅ =[ X := ~(.num x) ]=> {X ↦ x} := by
  apply EvalR.asgn
  -- `⊢ Aexp.eval ∅ x = (X ↦ x).value`, which we can prove with `simp` or `rfl`
  simp

example {x : Nat} : ∅ =[ X := ~(.num x) ]=> {X ↦ x} := by
  exact EvalR.asgn rfl

example : ∅ =[ X := 2; Y := 3 ]=> {Y ↦ 3, X ↦ 2} := by
  apply EvalR.seq
  · -- `⊢ imp {X := 2}.EvalR ∅ ?st'`
    exact EvalR.asgn rfl -- assigns the metavariable `?st'` to `{X ↦ 2}` (or equivalent)
  · simp only [Aexp.eval_num, evalR_eq]
    exact EvalR.asgn rfl

--  This is a case where `rfl` is more powerful than `simp`,
--  because it can assign the `?st'` metavariable. To
--  demonstrate, here's a version with `simp`

sf_expect_failure_in
  example : ∅ =[ X := 2; Y := 3 ]=> {Y ↦ 3, X ↦ 2} := by
    apply EvalR.seq
    · apply EvalR.asgn
      simp -- doesn't work because `simp` doesn't assign the metavariable
    · sorry

--  However, it's possible to use `simp` as long as we have
--  assigned `st'` ourselves:

example : ∅ =[ X := 2; Y := 3 ]=> {Y ↦ 3, X ↦ 2} := by
  apply EvalR.seq (st' := {X ↦ 2})
  · apply EvalR.asgn
    simp
  · apply EvalR.asgn
    simp

--  What sorts of things might we want to prove using these
--  definitions? Here are some simple examples...

--   ----------------------------------------

--  _Quiz:_

--  Is the following proposition provable?
--
--      ∀ (c : Com) (st st' : State),
--        st =[ skip; c ]=> st' →
--        st =[ c ]=> st'
--
--  (A) Yes (B) No (C) Not sure

--   ----------------------------------------

--  _Quiz:_

--  Is the following proposition provable?
--
--      ∀ (c₁ c₂ : Com) (st st' : State),
--        st =[ c₁; c₂ ]=> st' →
--        st =[ c₁ ]=> st →
--        st =[ c₂ ]=> st'
--
--  (A) Yes (B) No (C) Not sure

--   ----------------------------------------

--  _Quiz:_

--  Is the following proposition provable?
--
--      ∀ (b : Bexp) (c : Com) (st st' : State),
--        st =[ if (b) { c } else { c } ]=> st' →
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
--        ¬ ∃ st', st =[ while (b) { c } ]=> st'
--
--  (A) Yes (B) No (C) Not sure

--   ----------------------------------------

--  _Quiz:_

--  Is the following proposition provable?
--
--      ∀ (b : Bexp) (c : Com) (st : State),
--        (¬ ∃ st', st =[ while (b) { c } ]=> st') →
--        ∀ st'', b.eval st'' = true
--
--  (A) Yes (B) No (C) Not sure

--   ----------------------------------------

--  ### Determinism of Evaluation

--  Finally, we should pause to check that our evaluation
--  relation really is a (partial) function...

theorem ceval_deterministic {c : Com} {st st1 st2 : State}
    (e₁ : st =[ c ]=> st1) (e₂ : st =[ c ]=> st2) : st1 = st2 := by
  induction e₁ generalizing st2 with
  | skip =>
      inversion e₂
      rfl
  | asgn =>
      inversion e₂ with
      | asgn h' => subst_vars; rfl
  | seq h₁ h₂ ih₁ ih₂ =>
      inversion e₂ with
      | seq st2' h₁' h₂' =>
          apply ih₁ at h₁'; subst h₁'
          exact ih₂ h₂'
  | ifTrue hb hc ih =>
      inversion e₂ with
      | ifTrue hb' hc' => exact ih hc'
      | ifFalse hb' hc' => simp_all
  | ifFalse hb hc ih =>
      inversion e₂ with
      | ifTrue hb' hc' => simp_all
      | ifFalse hb' hc' => exact ih hc'
  | whileFalse hb =>
      inversion e₂ with
      | whileFalse hb' => rfl
      | whileTrue hb' hc' hl' => simp_all
  | whileTrue hb hc hloop ih₁ ih₂ =>
      inversion e₂ with
      | whileFalse hb' => simp_all
      | whileTrue st2' _ hc' hl' =>
          apply ih₁ at hc'; subst hc'
          exact ih₂ hl'

--  ## Reasoning About Imp Programs

theorem plus2_spec {st : State} {n : Nat} {st' : State}
    (hx : st[X] = n) (heval : st =[ plus2 ]=> st') :
    st'[X] = n + 2 := by
  -- Inverting `heval` forces one step of the evaluation relation: since
  -- `plus2` is an assignment, `st'` must be `st` extended at `X`.
  rw [plus2] at heval
  inversion heval with
  | asgn m h =>
    simp [hx] at h ⊢
    lia

--  ## Case Study (Optional)

--  Recall the factorial program (broken up into smaller
--  pieces this time, for convenience of proving things
--  about it).

def factBody : Com := imp {
  Y := Y * Z;
  Z := Z - 1
}

def factLoop : Com := imp {
  while (Z ≠ 0) {
    ~factBody
  }
}

def factCom : Com := imp {
  Z := X;
  Y := 1;
  ~factLoop
}

--  Here is an alternative "mathematical" definition of the
--  factorial function:

def realFact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n' + 1 => (n' + 1) * realFact n'

--  We would like to show that they agree -- if we start
--  `factCom` in a state where variable `X` contains some
--  number `n`, then it will terminate in a state where
--  variable `Y` contains the factorial of `n`.
--
--  To show this, we rely on the critical idea of a *loop
--  invariant*.

def FactInvariant (n : Nat) (st : State) : Prop :=
  st[Y] * realFact st[Z] = realFact n

--  We show that the body of the factorial loop preserves
--  the invariant:

theorem factBody_preserves_invariant {st st' : State} {n : Nat}
    (hinv : FactInvariant n st) (hz : st[Z] ≠ 0)
    (heval : st =[ ~factBody ]=> st') :
    FactInvariant n st' := by
  rw [FactInvariant] at hinv ⊢
  rw [factBody] at heval
  inversion heval with
  | seq _ h₁ h₂ =>
    inversion h₁ with
    | asgn hy =>
      inversion h₂ with
      | asgn hz' =>
        subst hy hz'
        have hyz : Y ≠ Z := by decide
        have hzy : Z ≠ Y := by decide
        simp [hyz, hzy]
        -- Show that `st[Z] = z + 1` for some `z`
        cases hzz : st[Z] with
        | zero => contradiction
        | succ z =>
          rw [hzz, realFact] at hinv
          rw [Nat.add_sub_cancel, Nat.mul_assoc]
          exact hinv

--  From this, we can show that the whole loop also
--  preserves the invariant:

theorem factLoop_preserves_invariant {st st' : State} {n : Nat}
    (hinv : FactInvariant n st) (heval : st =[ ~factLoop ]=> st') :
    FactInvariant n st' := by
  generalize heq : factLoop = c at heval
  induction heval with
  | whileFalse hb =>
    -- trivial when the loop doesn't run...
    exact hinv
  | @whileTrue st st' st'' b c hb hc hloop ih₁ ih₂ =>
    -- if the loop does run, we know that `factBody` preserves
    -- `FactInvariant` -- we just need to assemble the pieces
    rw [factLoop] at heq
    injection heq with hb' hc'
    subst hb' hc'
    have hz : st[Z] ≠ 0 := by
      intro hz
      simp [hz] at hb
    exact ih₂ (factBody_preserves_invariant hinv hz hc) rfl
  | skip | asgn | seq | ifTrue | ifFalse => simp [factLoop] at heq

--  Next, we show that, for any loop, if the loop
--  terminates, then the condition guarding the loop must be
--  false at the end:

theorem guard_false_after_loop {b : Bexp} {c : Com} {st st' : State}
    (heval : st =[ while (~b) {~c} ]=> st') :
    b.eval st' = false := by
  generalize heq : (imp { while (~b) {~c} }) = cmd at heval
  induction heval with
  | whileFalse hb =>
    injection heq with hb' _
    subst hb'
    exact hb
  | whileTrue _ _ _ _ ih₂ => exact ih₂ heq
  | skip | asgn | seq | ifTrue | ifFalse => simp at heq

--  Finally, we can patch it all together...

theorem factCom_correct {st st' : State} {n : Nat}
    (hx : st[X] = n) (heval : st =[ ~factCom ]=> st') :
    st'[Y] = realFact n := by
  rw [factCom] at heval
  inversion heval with
  | seq _ h₁ h₂ =>
    inversion h₁ with
    | asgn hz =>
      inversion h₂ with
      | seq _ h₃ h₄ =>
        inversion h₃ with
        | asgn hy =>
          subst hz hy
          -- The invariant is true before the loop runs...
          have hinv : FactInvariant n (Y →ₜ 1 ; Z →ₜ st[X] ; st) := by
            have hyz : Y ≠ Z := by decide
            simp [FactInvariant, hyz, hx]
          -- ...so when the loop is done running, the invariant
          -- is maintained
          have hinv' := factLoop_preserves_invariant hinv h₄
          -- Finally, if the loop terminated, then `Z` is `0`; so `Y` must be
          -- factorial of `X`
          rw [factLoop] at h₄
          have hz := guard_false_after_loop h₄
          simp at hz
          rw [FactInvariant, hz, realFact, Nat.mul_one] at hinv'
          exact hinv'

--  One might wonder whether all this work with poking at
--  states and unfolding definitions could be ameliorated
--  with some more powerful lemmas and/or more uniform
--  reasoning principles... Indeed, this is exactly the
--  point of the Hoare chapters!

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
--  - `sPush n`: Push the number `n` on the stack.
--  - `sLoad x`: Load the identifier `x` from the store and
--    push it on the stack
--  - `sPlus`: Pop the two top numbers from the stack, add
--    them, and push the result onto the stack.
--  - `sMinus`: Similar, but subtract the first number from
--    the second.
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

--  FILL IN HERE

theorem sExecute1 : sExecute ∅ [] [sPush 5, sPush 3, sPush 1, sMinus] = [2, 5] := by
  sorry

theorem sExecute2 : sExecute {X ↦ 3} [3, 4] [sPush 4, sLoad X, sMult, sPlus] = [15, 4] := by
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

theorem sCompile1 : sCompile (aexp { X - (2 * Y) }) = [sLoad X, sPush 2, sLoad Y, sMult, sMinus] := by
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
    sExecute st [] (sCompile a) = [Aexp.eval st a] := by
  sorry

end StackCompiler

-- Source revision: 8bf373d, committed 2026-09-22 21:03 UTC

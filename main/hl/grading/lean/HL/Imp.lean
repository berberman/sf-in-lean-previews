import LF.CustomTactics
import LF.Typeclasses
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer

import ComparatorAutograderLib
import SFLCompat

--  # Imp: Simple Imperative Programs

--  Note to developers (before next release):
--      Needs some WORKINCLASSes and some quizzes
--
--      LATER: Another nice challenge exercise at some point would be to
--      add C-style arrays (i.e., indirect read/write). This sets up some
--      really nice challenge problems in Hoare (reasoning about arrays /
--      aliasing / etc.).
--
--      SOONER: BCP 25: Maybe we should write / instead of && in
--      assertions, to save a mismatch in the `dec_minimum` exercise in
--      Hoare₂?
--
--      At some point we could consider moving material from the old
--      HoareLists to this chapter (and into later files, as appropriate).
--      We haven't done it yet because it's a shame to complicate the nice
--      simple presentation here when it's used as the basis for
--      applications like Xavier's static analysis lectures. Also, we now
--      have a whole volume on real separation logic...
--
--      MWH (port note): The Rocq chapter's "Rocq Automation" tour has been
--      retooled here for Lean. The tactic combinators `try` and `repeat`
--      (and the custom-tactic `macro`) are introduced in this chapter;
--      `<;>` and `simp` were already introduced in Logical Foundations
--      (`<;>` in `Induction`) so we use them freely and the `<;>` section
--      below is a recap. For linear arithmetic we use `lia`; NOTE that LF
--      currently introduces `omega`, not `lia`, so this needs to be
--      reconciled volume-wide (either introduce `lia` in LF, or keep
--      `omega`).

--  In this chapter, we take a more serious look at how to use Lean as a
--  tool to study other things. Our case study is a *simple imperative
--  programming language* called Imp, embodying a tiny core fragment of
--  conventional mainstream languages such as C and Java.
--
--  Here is a familiar mathematical function written in Imp.
--
--      Z := X;
--      Y := 1;
--      while (Z ≠ 0) {
--        Y := Y * Z;
--        Z := Z - 1;
--      }

--  We concentrate here on defining the *syntax* and *semantics* of Imp;
--  later in this volume we develop a theory of *program equivalence* and
--  introduce *Hoare Logic*, a popular logic for reasoning about imperative
--  programs.

--  We build Imp in three layers. The first — a core language of
--  *arithmetic and boolean expressions* — is developed in its own chapter,
--  *Slang*; read that one first. There you meet the abstract syntax of
--  arithmetic expressions (`Aexp`) and boolean expressions (`Bexp`), their
--  evaluation both as a recursive *function* and as an inductive
--  *relation* (proved equivalent), and a small `optimize0plus` program
--  transformation together with its correctness proof. Those expressions
--  are *variable-free*.
--
--  This chapter picks up from there. First we extend the expressions with
--  *variables*; then we add a language of *commands* — assignment,
--  conditionals, sequencing, and loops.

--  ## Expressions With Variables

--  Let's return to defining Imp. The next thing we need to do is to enrich
--  our arithmetic and boolean expressions with variables. To keep things
--  simple, we'll assume that all variables are global and that they only
--  hold numbers.

--  ### States

--  Since we'll want to look variables up to find out their current values,
--  we'll use total maps from the `Maps` chapter. A *machine state* (or
--  just *state*) represents the current values of all variables at some
--  point in the execution of a program.

--  For simplicity, we assume that the state is defined for *all*
--  variables, even though any given program is only able to mention a
--  finite number of them. Because each variable stores a natural number,
--  we represent the state as a total map from strings (variable names) to
--  `Nat`, and will use `0` as the default value in the store.

--  We give the type of variable identifiers a name, `Ident`. For now it is
--  just `String`; naming it makes the intent clearer.

open scoped MyGetElem

abbrev Ident := String
abbrev State := TotalMap Ident Nat

--  ### Syntax

--  We can add variables to the arithmetic expressions we had before simply
--  by including one more constructor. (This is a fresh `Aexp`, replacing
--  the variable-free one from the *Slang* chapter.)

--  Note to developers (Benjamin Pierce @bcpierce00):
--      That should be a live chapter link.

inductive Aexp where
  | num (n : Nat)
  | id (x : Ident)                -- NEW
  | plus (a₁ a₂ : Aexp)
  | minus (a₁ a₂ : Aexp)
  | mult (a₁ a₂ : Aexp)

--  Note to developers (Chris Henson @chenson2018):
--      Rather than define identifiers as Ident, a more general approach is
--      to use a **type variable** with `DecidableEq` (as the `Maps`
--      chapter does), threaded through `Aexp`/`Bexp`/`Com`/`State`.
--      Stashed for a future decision; the parameterized version would look
--      like:
--
--      `inductive Aexp (V : Type) where
--        | num (n : Nat)
--        | id (x : V)
--        | plus (a₁ a₂ : Aexp V)
--        | minus (a₁ a₂ : Aexp V)
--        | mult (a₁ a₂ : Aexp V)
--      -- … then `Bexp V`, `Com V`, `abbrev State (V) [DecidableEq V] :=
--      -- TotalMap V Nat`, and `[DecidableEq V]` wherever a lookup/update is
--      -- performed.`

--  The `Bexp` definition is unchanged, except that it now refers to the
--  new `Aexp`.

inductive Bexp where
  | bool (b : Bool)
  | eq (a₁ a₂ : Aexp)
  | neq (a₁ a₂ : Aexp)
  | le (a₁ a₂ : Aexp)
  | gt (a₁ a₂ : Aexp)
  | not (b : Bexp)
  | and (b₁ b₂ : Bexp)

--  Defining a few variable names as shorthands will make examples easier
--  to read.

def W : Ident := "W"
def X : Ident := "X"
def Y : Ident := "Y"
def Z : Ident := "Z"

--  ### Notations

--  To make Imp programs easier to read and write, we introduce some
--  notations.
--
--  You do not need to understand exactly what these declarations do.
--  Briefly, though, here is how the two blocks below fit together:
--
--  - The `declare_syntax_cat` directive adds a new non-terminal to Lean's
--    grammar, called `imp_aexp`. We'll add additional non-terminals
--    further below.
--
--  - Each `syntax` directive defines a grammar production, of which there
--    are eight in total. The first two define literals, `num` and `ident`,
--    as `imp_aexp`s. The next several directives define productions for
--    building larger expressions, with some annotations to define
--    precedence, etc.
--
--  - Finally, `macro_rules` is used to translate each production of the
--    `imp_aexp` nonterminal into a Lean expression.
--
--  Boolean expressions and, later, commands follow this same pattern
--  exactly, so their declarations are collapsed where they appear: open
--  one if you want to see the pattern repeated, and skip them otherwise.

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
syntax:min "aexp " "{" imp_aexp "}" : term
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
syntax:min "bexp " "{" imp_bexp "}" : term
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

--  The notations above are *input* only: they teach Lean how to **read**
--  `aexp
--  { … }` and `bexp { … }`, but Lean still **prints** an expression
--  using its raw constructors -- `example_aexp` shows up as
--  `Aexp.plus (Aexp.num 3) …` rather than `aexp { 3 + X * 2 }`. A
--  *delaborator* closes the loop. Where a `macro` turns surface syntax
--  into a term (*elaboration*), a delaborator does the reverse: it turns
--  an elaborated term back into surface syntax so that Lean's own output
--  uses our concrete Imp notation.
--
--  Each delaborator walks a term of the given type and rebuilds the
--  matching piece of `imp_aexp`/`imp_bexp` syntax; a subterm Lean doesn't
--  recognize is printed with the `~` escape. The `@[delab …]` attribute
--  registers the top-level function to fire whenever Lean is about to
--  display a term headed by one of those constructors -- unless notation
--  printing has been switched off with `set_option pp.notation false`,
--  which lets us fall back to the raw constructors when debugging (see
--  *Desugaring Notations* below). The companion *category parenthesizer*
--  re-inserts the parentheses the grammar's precedences demand, so that,
--  e.g., `(1 + 2) * 3` prints with its parentheses intact.
--
--  You do not need to understand the details, and the code is collapsed
--  below for that reason. The result is that a `#check`, an `#eval`, or a
--  proof goal mentioning an Imp expression is displayed in readable Imp
--  syntax rather than as a pile of constructors.

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

--  The `whenPPOption getPPNotation` wrapper lets
--  `set_option pp.notation false` switch this delaborator off, revealing
--  the raw constructors (see the "Desugaring Notations" discussion, after
--  the commands are introduced).

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

--  With these delaborators in place, Lean pretty-prints Imp expressions
--  with the higher-level notations rather than their raw constructors.
--
--  The pretty-printed version of an expression might not exactly match its
--  original form. For example, the parentheses around `X * 2` in
--  `aexp { 3 + (X * 2) }` are not printed because they are redundant --
--  which the parenthesizer knows.

/-- info: aexp {3 + X * 2} : Aexp -/
#guard_msgs in
#check aexp { 3 + (X * 2) }

/-- info: bexp {true ∧ ¬ (X ≤ 4)} : Bexp -/
#guard_msgs in
#check bexp { true ∧ ¬(X ≤ 4) }

--  ### Evaluation

--  The arithmetic and boolean evaluators must now be extended to handle
--  variables, taking a state `st` as an extra argument. A variable is
--  looked up in the state with the map-indexing notation `st[x]` from the
--  Typeclasses chapter in the Logical Foundations book. For the notation
--  to work, we used `open scoped MyGetElem` earlier, which opens only the
--  scoped items like notation from the module.

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

--  We reuse the total-map notation (`x →ₜ v ; ∅` etc.) for states.

example : aexp { 3 + (X * 2) }.eval (X →ₜ 5 ; ∅) = 13 := by rfl

example : aexp { Z + (X * Y) }.eval (X →ₜ 5 ; Y →ₜ 4 ; ∅) = 20 := by rfl

example : bexp { true ∧ ¬(X ≤ 4) }.eval (X →ₜ 5 ; ∅) = true := by rfl

--  Note to developers:
--      dsainati: Bikeshedding: I'm not sure how I feel about this arrow
--      subscript for maps. Easy to change later but just flagging to
--      discuss. mwhicks1: This comes from the Maps chapter, which
--      chenson2018 is working on. There is a keyboard shortcut for ↦ we
--      could use (mapsto).

--  ## Commands

--  Now we are ready to define the syntax and behavior of Imp *commands*
--  (or *statements*). Informally, commands `c` are described by the
--  following BNF grammar:

--  c ::= skip
--      | x := a
--      | c ; c
--      | if b then c else c end
--      | while b do c end

--  Here is the formal definition of the abstract syntax of commands.

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
syntax:min imp_com:11 ";" ppDedent(ppLine imp_com:min) : imp_com
/-- Assignment -/
syntax:max ident ppHardSpace ":=" ppHardSpace imp_aexp : imp_com
/-- Conditional -/
syntax:max "if " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}" ppHardSpace "else" ppHardSpace "{") ppLine imp_com ppDedent(ppLine "}") : imp_com
/-- Loop -/
syntax:max "while " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : imp_com
/-- Escape to Lean -/
syntax:max "~" term:max : imp_com

/-- Include an Imp command in Lean code -/
syntax:min "imp" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : term

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

--  Just as we did for expressions, we add a delaborator so that Lean
--  prints commands back in the `imp { … }` concrete syntax (see the
--  Delaborators section above). It reuses the expression delaborators for
--  the condition of an `if`/`while` and for the right-hand side of an
--  assignment, and prints an unrecognized subcommand with the `~` escape.

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

--  As an example, here is the factorial function again, written as a
--  formal definition. When this command terminates, the variable `Y` will
--  contain the factorial of the initial value of `X`. (Compare this to the
--  concrete Imp program at the very start of the chapter.)

def fact_in_lean : Com := imp {
  Z := X;
  Y := 1;
  while (Z ≠ 0) {
    Y := Y * Z;
    Z := Z - 1
  }
}

--  Because we registered a delaborator, we can inspect a defined program
--  with `#print`, which pretty prints the stored definition using the same
--  syntax:

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

--  The `imp { … }` notation, together with the delaborators, is purely a
--  convenience for reading and writing programs. Occasionally, such as
--  when debugging a definition or a stuck proof, the concrete syntax
--  `hide`s the underlying structure we want to see. For those moments we
--  can switch the Imp notation off in Lean's output with
--  `set_option pp.notation false`, which our delaborators honor.
--
--  Note that unlike a `def`, `imp { … }` is a `macro` which is expanded
--  during elaboration, **before** the resulting term is type-checked. So
--  `fact_in_lean` is not a program hidden behind a layer of notation that
--  a proof must first peel back; it simply **is** the underlying tree of
--  `Com`, `Aexp`, and `Bexp` constructors. Consequently, when a proof goal
--  mentions an Imp program, tactics such as `cases`, `injection`, and
--  `simp` already act on those constructors directly -- there is nothing
--  to "unfold". The delaborators affect only how that tree is
--  **displayed**. Nevertheless, seeing the raw constructors is sometimes
--  very helpful!

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
--
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

--  Next we need to define what it means to evaluate an Imp command. The
--  fact that `while` loops don't necessarily terminate makes defining an
--  evaluation function tricky.

--  ### Evaluation as a Function (Failed Attempt)

--  Here's an attempt at defining an evaluation function for commands (with
--  a bogus `while` case).

def Com.ceval_fun_no_while (st : State) (c : Com) : State :=
  match c with
  | imp {skip} => st
  | imp {x := ~a} => (x →ₜ a.eval st ; st)
  | imp {c₁; c₂} =>
      let st' := ceval_fun_no_while st c₁
      ceval_fun_no_while st' c₂
  | imp {if (b) {c₁} else {c₂}} =>
      if b.eval st then ceval_fun_no_while st c₁
      else ceval_fun_no_while st c₂
  | imp {while (~_) {~_}} => st     -- bogus

--  In a more conventional functional language like OCaml or Haskell we
--  could add the `while` case as follows:

--  | .whileDo b c =>
--      if b.eval st then ceval_fun st (.seq c (.whileDo b c))
--      else st

--  Lean doesn't accept such a definition ("fail to show termination")
--  because the function we want to define is not guaranteed to terminate.
--  Indeed, it *doesn't* always terminate: the full `ceval_fun` applied to
--  the `loop` program above would run forever. Since Lean aims to be not
--  just a programming language but also a consistent logic, any
--  potentially non-terminating function must be rejected. Here is what
--  would go wrong if Lean allowed non-terminating recursive functions:

--  def loop_false (n : Nat) : False := loop_false n

--  That is, propositions like `False` would become provable
--  (`loop_false 0` would be a proof of `False`), a disaster for logical
--  consistency.
--
--  Thus, because it doesn't terminate on all inputs, the full `ceval_fun`
--  cannot be written in Lean -- at least not without additional tricks and
--  workarounds.

--  Note to developers:
--      Perhaps that discussion should be moved to -- or previewed in --
--      Logic.v? MRC'20: It's already in ProofObjects (which not everyone
--      sees).

--  ### Evaluation as a Relation

--  Here's a better way: define `ceval` as a *relation* rather than a
--  *function* -- i.e., make its result a `Prop` rather than a `State`,
--  similar to what we did for `Aexp.EvalR` in the Slang chapter.

--  This is an important change. Besides freeing us from awkward
--  workarounds, it gives us more flexibility in the definition. For
--  example, if we add nondeterministic features like `any` to the
--  language, we want the definition of evaluation to be nondeterministic
--  -- i.e., not only will it not be total, it will not even be a function!

--  Note to developers (Michael Hicks @mwhicks1):
--      I kind of hate this notation. Is there something more standard in
--      Lean? CSLib precedent maybe?

--  We'll use the notation `st =[ c ]=> st'` for the `Com.EvalR` relation:
--  `st =[ c ]=> st'` means that executing program `c` in a starting state
--  `st` results in an ending state `st'`. This can be pronounced "`c`
--  takes state `st` to `st'`".
--
--  Operational Semantics

--  Note to developers (before next release):
--      BCP 21: I wonder if `seq` would be easier to work with if st' and
--      st'' were swapped...

--  Here is an informal definition of evaluation, presented as inference
--  rules for readability:
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
--  Here is the formal definition. Make sure you understand how it
--  corresponds to the inference rules.

--  Note to developers (Chris Henson @chenson2018):
--      TODO Propose you use inline notation such as
--      `Com.EvalR (imp {skip;}) st st`

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

--  Note to developers (Niklas Halonen @xhalo32):
--      Setting `In` and `Out` as `outParam`s is a hack to resolve various
--      typeclass synthesis problems or at least I can't explain why it
--      works.

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

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()
--  END DETAILS

--  The cost of defining evaluation as a relation instead of a function is
--  that we now need to construct a *proof* that some program evaluates to
--  some result state, rather than letting Lean's computation mechanism do
--  it for us.

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

--  Note to developers:
--      PR: I phrased these quizzes with the following alternatives: (A)
--      Not true (B) True and easily provable (C) True and takes more work
--      to prove (D) True and cannot be proved without additional axioms

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
--        st =[ c₁ c₂ ]=> st' →
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

--  Changing from a computational to a relational definition of evaluation
--  is a good move because it frees us from the artificial requirement that
--  evaluation be a total function. But it raises a question: is the
--  relational definition really a partial *function*? Could the same
--  command, from the same state, evaluate to two different final states?
--  In fact this cannot happen: `ceval` *is* a partial function.

theorem ceval_deterministic (c : Com) (st st1 st2 : State)
    (e₁ : st =[ c ]=> st1) (e₂ : st =[ c ]=> st2) : st1 = st2 := by
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

--  Write an Imp program that sums the numbers from `1` to `X` (inclusive)
--  in the variable `Y`. Your program should update the state as shown in
--  `pup_to_2_ceval`, which you can reverse-engineer to discover the
--  program you should write. The proof of that theorem will be somewhat
--  lengthy.

def pup_to_n : Com := sorry

theorem pup_to_2_ceval :
    (X →ₜ 2 ; ∅) =[ pup_to_n ]=>
      (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅) := by
  sorry

--  ## Reasoning About Imp Programs

--  We'll get into more systematic and powerful techniques for reasoning
--  about Imp programs in the next chapter, but we can already do a few
--  things (albeit in a somewhat low-level way) just by working with the
--  bare definitions. This section explores some examples.

theorem plus2_spec (st : State) (n : Nat) (st' : State)
    (hx : st[X] = n) (heval : st =[ plus2 ]=> st') :
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

--  Note to developers (Niklas Halonen @xhalo32):
--      We should use the `generalize` tactic here instead of `have key`.
--      I've changed some Hoare proofs from `have key` to `generalize` but
--      the tactic hasn't been explained yet.

--  ### Exercise (3 stars): loop_never_stops ⭐⭐⭐

--  Hint: proceed by induction on the assumed derivation showing that
--  `loop` terminates. Most of the cases are immediately contradictory and
--  so can be solved in one step (by `simp`/`contradiction` on the
--  impossible command equation).

theorem loop_never_stops (st st' : State) : ¬ (st =[ loop ]=> st') := by
  sorry

--  ### Exercise (3 stars): no_whiles_eqv ⭐⭐⭐

--  The following function yields `true` just on programs with no while
--  loops. Using `inductive`, write a property `Com.NoWhilesR` that holds
--  exactly when `c` is while-free, then prove it equivalent to
--  `Com.no_whiles`.

def Com.no_whiles (c : Com) : Bool :=
  match c with
  | imp {skip} => true
  | imp {_x := ~_a} => true
  | imp {c₁; c₂} => no_whiles c₁ && no_whiles c₂
  | imp {if (~_) {ct} else {cf}} => no_whiles ct && no_whiles cf
  | imp {while (~_) {~_}} => false

inductive Com.NoWhilesR : Com → Prop where
  --  FILL IN HERE

theorem no_whiles_eqv (c : Com) : c.no_whiles = true ↔ Com.NoWhilesR c := by
  sorry

--  ### Exercise (4 stars): no_whiles_terminating ⭐⭐⭐⭐

--  Imp programs that don't involve while loops always terminate. State and
--  prove a theorem `no_whiles_terminating` that says this. Use either
--  `Com.no_whiles` or `Com.NoWhilesR`, as you prefer.

theorem no_whiles_terminating (c : Com) (st : State) (h : Com.NoWhilesR c) :
    ∃ st', st =[ c ]=> st' := by
  sorry

--  And here is an alternative solution by induction on `c` (using
--  `Com.no_whiles` instead of `Com.NoWhilesR`):

--  FILL IN HERE

--  ### Additional Exercises

--  ### Exercise (3 stars): stack_compiler ⭐⭐⭐

--  Old HP Calculators, programming languages like Forth and Postscript,
--  and abstract machines like the Java Virtual Machine all evaluate
--  arithmetic expressions using a *stack*. For instance, the expression
--
--      (2*3)+(3*(4-2))
--
--  would be written as
--
--            2 3 * 3 4 2 - * +
--
--  and evaluated like this (where we show the program being evaluated on
--  the right and the contents of the stack on the left):

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

--  The goal of this exercise is to write a small compiler that translates
--  `aexp`s into stack machine instructions.
--
--  The instruction set for our stack language will consist of the
--  following instructions:
--
--  - `sPush n`: Push the number `n` on the stack.
--
--  - `sLoad x`: Load the identifier `x` from the store and push it on the
--    stack
--
--  - `sPlus`: Pop the two top numbers from the stack, add them, and push
--    the result onto the stack.
--
--  - `sMinus`: Similar, but subtract the first number from the second.
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

--  Write a function to evaluate programs in the stack language. It should
--  take as input a state, a stack represented as a list of numbers (top
--  stack item is the head of the list), and a program represented as a
--  list of instructions, and it should return the stack after executing
--  the program. Test your function on the examples below.
--
--  Note that it is unspecified what to do when encountering an `sPlus`,
--  `sMinus`, or `sMult` instruction if the stack contains fewer than two
--  elements. In a sense, it is immaterial what we do, since a correct
--  compiler will never emit such a malformed program. But for sake of
--  later exercises, it would be best to skip the offending instruction and
--  continue with the next one.

def sExecute (st : State) (stack : List Nat) (prog : List Sinstr) : List Nat :=
  sorry
                                        -- Bad state: skip

--  FILL IN HERE

example : sExecute ∅ [] [sPush 5, sPush 3, sPush 1, sMinus] = [2, 5] := by
  sorry

example : sExecute (X →ₜ 3) [3, 4] [sPush 4, sLoad X, sMult, sPlus] = [15, 4] := by
  sorry

--  Next, write a function that compiles an `Aexp` into a stack machine
--  program. The effect of running the program should be the same as
--  pushing the value of the expression on the stack.

def sCompile (a : Aexp) : List Sinstr :=
  sorry

--  FILL IN HERE

--  After you've defined `sCompile`, prove the following to test that it
--  works.

example : sCompile (aexp { X - (2 * Y) }) = [sLoad X, sPush 2, sLoad Y, sMult, sMinus] := by
  sorry

--  ### Exercise (3 stars): execute_app ⭐⭐⭐

--  Execution can be decomposed in the following sense: executing stack
--  program `p₁ ++ p₂` is the same as executing `p₁`, taking the resulting
--  stack, and executing `p₂` from that stack. Prove that fact.

theorem execute_app (st : State) (p₁ p₂ : List Sinstr) (stack : List Nat) :
    sExecute st stack (p₁ ++ p₂) = sExecute st (sExecute st stack p₁) p₂ := by
  sorry

--  ### Exercise (3 stars): compiler_correct ⭐⭐⭐

--  Now we'll prove the correctness of the compiler implemented in the
--  previous exercise. Begin by proving the following lemma. If it becomes
--  difficult, consider whether your implementation of `sExecute` or
--  `sCompile` could be simplified.

theorem sCompile_correct_aux (st : State) (a : Aexp) (stack : List Nat) :
  sExecute st stack (sCompile a) = Aexp.eval st a :: stack := by
  sorry

--  The main theorem should be a very easy corollary of that lemma.

theorem sCompile_correct (st : State) (a : Aexp) :
  sExecute st [] (sCompile a) = [ Aexp.eval st a ] := by
  sorry

end StackCompiler

--  ### Exercise (3 stars): short_circuit (Optional) ⭐⭐⭐

--  Most modern programming languages use a "short-circuit" evaluation rule
--  for boolean `and`: to evaluate `BExp.and b₁ b₂`, first evaluate `b₁`.
--  If it evaluates to `false`, then the entire `and` expression evaluates
--  to `false` immediately, without evaluating `b₂`. Otherwise, `b₂` is
--  evaluated to determine the result of the `and` expression.
--
--  Write an alternate version of `BExp.eval` that performs short-circuit
--  evaluation of `BAnd` in this manner, and prove that it is equivalent to
--  `BExp.eval`. (N.b. This is only true because expression evaluation in
--  Imp is rather simple. In a bigger language where evaluating an
--  expression might diverge, the short-circuiting `and` would *not* be
--  equivalent to the original, since it would make more programs
--  terminate.)

def Bexp.evalSC (st : State) (b : Bexp) : Bool := sorry

--  FILL IN HERE

-- This exercise turned out to be easier than we intended!
theorem Bexp.eval_eq_evalSc (st : State) (b : Bexp) :
  b.eval st = b.evalSC st := by
  sorry

--  ### Exercise (3 stars): break_imp (Optional) ⭐⭐⭐

--  Imperative languages like C and Java often include a `break` or similar
--  statement for interrupting the execution of loops. In this exercise we
--  consider how to add `break` to Imp. First, we need to enrich the
--  language of commands with an additional case. Because `break` is a
--  reserved keyword in Lean, we will abbreviate it as `brk`.

namespace Imp.Break

inductive Com where
  | skip
  | brk                          -- <--- NEW
  | asgn (x : Ident) (a : Aexp)
  | seq (c₁ c₂ : Com)
  | cond (b : Bexp) (c₁ c₂ : Com)
  | whileDo (b : Bexp) (c : Com)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: commands, macro rules)
namespace Com

open Lean

scoped macro_rules
  | `(imp { $s }) => do
    let stx ← match s with
      | `(imp_com| skip) => ``(Com.skip)
      | `(imp_com| brk) => ``(Com.brk)
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
    return Imp.Elab.withSourceInfoOf s stx

end Com

open scoped Com

namespace Delab
open Lean PrettyPrinter Imp.Delab

@[app_unexpander Com.brk]
private def unexpandComBrk : Unexpander
  | _ => `(imp { $(mkIdent `brk):ident })

attribute [app_unexpander Com.skip] unexpandComSkip
attribute [app_unexpander Com.asgn] unexpandComAsgn
attribute [app_unexpander Com.seq] unexpandComSeq
attribute [app_unexpander Com.cond] unexpandComCond
attribute [app_unexpander Com.whileDo] unexpandComWhileDo

end Delab

/--
info: imp {
  brk
} : Com
-/
#guard_msgs in
#check imp {brk}
--  END DETAILS

--  Next, we need to define the behavior of `brk`. Informally, whenever
--  `brk` is executed in a sequence of commands, it stops the execution of
--  that sequence and signals that the innermost enclosing loop should
--  terminate. (If there aren't any enclosing loops, then the whole program
--  simply terminates.) The final state should be the same as the one in
--  which the `brk` statement was executed.
--
--  One important point is what to do when there are multiple loops
--  enclosing a given `brk`. In those cases, `brk` should only terminate
--  the *innermost* loop. Thus, after executing the following...
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
--  One way of expressing this behavior is to add another parameter to the
--  evaluation relation that specifies whether evaluation of a command
--  executes a `brk` statement:

inductive Result : Type where
  | sContinue
  | sBreak

open Result

--  We will use the syntax `st =[ c ]=> st' // s` to mean that, if `c` is
--  started in state `st`, then it terminates in state `st'` and either
--  signals that the innermost surrounding loop (or the whole program)
--  should exit immediately (`s = sBreak`) or that execution should
--  continue normally (`s = sContinue`).
--
--  The definition of the `st =[ c ]=> st' // s` relation is very similar
--  to the one we gave above for the regular evaluation relation
--  (`st =[ c ]=> st'`) -- we just need to handle the termination signals
--  appropriately:
--
--  - If the command is `skip`, then the state doesn't change and execution
--    of any enclosing loop can continue normally.
--
--  - If the command is `brk`, the state stays unchanged but we signal a
--    `sBreak`.
--
--  - If the command is an assignment, then we update the binding for that
--    variable in the state accordingly and signal that execution can
--    continue normally.
--
--  - If the command is of the form `if (b) {c₁} {c₂}`, then the state is
--    updated as in the original semantics of Imp, except that we also
--    propagate the signal from the execution of whichever branch was
--    taken.
--
--  - If the command is a sequence `c₁ ; c₂`, we first execute `c₁`. If
--    this yields a `sBreak`, we skip the execution of `c₂` and propagate
--    the `sBreak` signal to the surrounding context; the resulting state
--    is the same as the one obtained by executing `c₁` alone. Otherwise,
--    we execute `c₂` on the state obtained after executing `c₁`, and
--    propagate the signal generated there.
--
--  - Finally, for a loop of the form `while (b) {c}`, the semantics is
--    almost the same as before. The only difference is that, when `b`
--    evaluates to `true`, we execute `c` and check the signal that it
--    raises. If that signal is `sContinue`, then the execution proceeds as
--    in the original semantics. Otherwise, we stop the execution of the
--    loop, and the resulting state is the same as the one resulting from
--    the execution of the current iteration. In either case, since `break`
--    only terminates the innermost loop, `while` signals `sContinue`.
--
--  Based on the above description, complete the definition of the
--  `Com.EvalR` relation:

inductive Com.EvalR : Com → State → State → Result → Prop where
  | skip {st : State} : EvalR (imp {skip}) st st sContinue
  --  FILL IN HERE

scoped notation:40 st0:41 " =[ " c " ]=> " st1:41 " // " s:41 => Com.EvalR c st0 st1 s

--  Now prove the following properties of your definition:

theorem break_ignore (c : Com) (st st' : State) (s : Result) (h : st =[ imp { brk ; c } ]=> st' // s) :
  st = st' := by
  sorry

theorem while_continue (b : Bexp) (c : Com) (st st' : State) (s : Result)
  (h : st =[ imp { while (b) {c} } ]=> st' // s) :
  s = sContinue := by
  sorry

theorem while_stops_on_break (b : Bexp) (c : Com) (st st' : State)
  (h₁ : b.eval st = true)
  (h₂ : st =[ imp { c } ]=> st' // sBreak) :
  st =[ imp { while (b) {c} } ]=> st' // sContinue := by
  sorry

theorem seq_continue (c₁ c₂ : Com) (st st' st'' : State)
  (h₁ : st =[ imp { c₁ } ]=> st' // sContinue)
  (h₂ : st' =[ imp { c₂ } ]=> st'' // sContinue) :
  st =[ imp { c₁ ; c₂ } ]=> st'' // sContinue := by
  sorry

theorem seq_stops_on_break (c₁ c₂ : Com) (st st' : State)
  (h : st =[ imp { c₁ } ]=> st' // sBreak) :
  st =[ imp { c₁ ; c₂ } ]=> st' // sBreak := by
  sorry

--  ### Exercise (3 stars): while_break_true (Optional) ⭐⭐⭐

theorem while_break_true (b : Bexp) (c : Com) (st st' : State)
  (h₁ : st =[ imp { while (b) {c} } ]=> st' // sContinue)
  (h₂ : b.eval st' = true) :
  ∃ st'', st'' =[ imp { c } ]=> st' // sBreak := by
  sorry

--  ### Exercise (4 stars): ceval_deterministic (Optional) ⭐⭐⭐⭐

theorem ceval_deterministic (c : Com) (st st₁ st₂ : State) (s₁ s₂ : Result)
  (h₁ : st =[ imp { c } ]=> st₁ // s₁)
  (h₂ : st =[ imp { c } ]=> st₂ // s₂) :
  st₁ = st₂ ∧ s₁ = s₂ := by
  sorry

end Imp.Break

--  ### Exercise (4 stars): add_for_loop (Optional) ⭐⭐⭐⭐

--  Add C-style `for` loops to the language of commands, update the `ceval`
--  definition to define the semantics of `for` loops, and add cases for
--  `for` loops as needed so that all the proofs in this file are accepted
--  by Rocq.
--
--  A `for` loop should be parameterized by (a) a statement executed
--  initially, (b) a test that is run on each iteration of the loop to
--  determine whether the loop should continue, (c) a statement executed at
--  the end of each loop iteration, and (d) a statement that makes up the
--  body of the loop. (You don't need to worry about making up a concrete
--  Notation for `for` loops, but feel free to play with this too if you
--  like.)

--  Note to developers (Michael Hicks @mwhicks1):
--      `NOT PORTED YET — remaining sections of sfdev/lf/Imp.v to port:
--        - Case Study (Optional), Imp.v:2774
--            * subtract_slowly_spec (EX4?, Imp.v:2919): loop-invariant style proof
--              about `subtract_slowly`.
--        - Additional Exercises, Imp.v:2986
--            * exn_imp (EX4A?, Imp.v:3524): exceptions variant. Large.`

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
--      * {deftech}/{tech} — a small glossary: define Imp's core terms once with
--        {deftech} (abstract syntax, state, big-step, relation, partial function, …)
--        and link later uses with {tech}.
--      * {lean}`expr` — inline elaborated expressions/types where a whole expression,
--        not just a single name, reads better with hover types (e.g. the
--        `Coe Ident Aexp` / `OfNat Aexp n` bullets in the Notations section).`

-- Built on 2026-09-03 11:56 UTC

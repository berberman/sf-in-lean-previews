import LF.CustomTactics
import LF.Typeclasses
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer

import SFLCompat

-- # Imp: Simple Imperative Programs

-- In this chapter, we take a more serious look at how to use Lean as a tool
-- to study other things. Our case study is a *simple imperative programming
-- language* called Imp, embodying a tiny core fragment of conventional
-- mainstream languages such as C and Java.

-- Here is a familiar mathematical function written in Imp.

--   Z := X;
--   Y := 1;
--   while (Z ≠ 0) {
--     Y := Y * Z;
--     Z := Z - 1;
--   }

-- We concentrate here on defining the *syntax* and *semantics* of Imp; later
-- in this volume we develop a theory of *program equivalence* and introduce
-- *Hoare Logic*, a popular logic for reasoning about imperative programs.

-- We build Imp in three layers. The first — a core language of *arithmetic
-- and boolean expressions* — is developed in its own chapter, *Slang*; read
-- that one first. There you meet the abstract syntax of arithmetic
-- expressions (`Aexp`) and boolean expressions (`Bexp`), their evaluation
-- both as a recursive *function* and as an inductive *relation* (proved
-- equivalent), and a small `optimize0plus` program transformation together
-- with its correctness proof. Those expressions are *variable-free*.

-- This chapter picks up from there. First we extend the expressions with
-- *variables*; then we add a language of *commands* — assignment,
-- conditionals, sequencing, and loops.

-- ## Expressions With Variables

-- Let's return to defining Imp. The next thing we need to do is to enrich our
-- arithmetic and boolean expressions with variables. To keep things simple,
-- we'll assume that all variables are global and that they only hold numbers.

-- ### States

-- Since we'll want to look variables up to find out their current values,
-- we'll use total maps from the `Maps` chapter. A *machine state* (or just
-- *state*) represents the current values of all variables at some point in
-- the execution of a program.

-- For simplicity, we assume that the state is defined for *all* variables,
-- even though any given program is only able to mention a finite number of
-- them. Because each variable stores a natural number, we represent the state
-- as a total map from strings (variable names) to `Nat`, and will use `0` as
-- the default value in the store.

-- We give the type of variable identifiers a name, `Ident`. For now it is
-- just `String`; naming it makes the intent clearer.

open scoped MyGetElem

abbrev Ident := String
abbrev State := TotalMap Ident Nat

-- ### Syntax

-- We can add variables to the arithmetic expressions we had before simply by
-- including one more constructor. (This is a fresh `Aexp`, replacing the
-- variable-free one from the *Slang* chapter.)

inductive Aexp where
  | num (n : Nat)
  | id (x : Ident)                -- NEW
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)

-- The `Bexp` definition is unchanged, except that it now refers to the new
-- `Aexp`.

inductive Bexp where
  | bool (b : Bool)
  | eq (a1 a2 : Aexp)
  | neq (a1 a2 : Aexp)
  | le (a1 a2 : Aexp)
  | gt (a1 a2 : Aexp)
  | not (b : Bexp)
  | and (b1 b2 : Bexp)

-- Defining a few variable names as shorthands will make examples easier to
-- read.

def W : Ident := "W"
def X : Ident := "X"
def Y : Ident := "Y"
def Z : Ident := "Z"

-- ### Notations

-- To make Imp programs easier to read and write, we introduce some notations.

-- You do not need to understand exactly what these declarations do. Briefly,
-- though, here is how the two blocks below fit together:

-- - The `declare_syntax_cat` directive adds a new non-terminal to Lean's
--   grammar, called `imp_aexp`. We'll add additional non-terminals further
--   below.

-- - Each `syntax` directive defines a grammar production, of which there are
--   eight in total. The first two define literals, `num` and `ident`, as
--   `imp_aexp`s. The next several directives define productions for building
--   larger expressions, with some annotations to define precedence, etc.

-- - Finally, `macro_rules` is used to translate each production of the
--   `imp_aexp` nonterminal into a Lean expression.

-- Boolean expressions and, later, commands follow this same pattern exactly,
-- so their declarations are collapsed where they appear: open one if you want
-- to see the pattern repeated, and skip them otherwise.

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

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: boolean expressions

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

-- END DETAILS

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: boolean expressions, macro rules

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

-- END DETAILS

#check aexp { 3 + (X * 2) }
#check bexp { true ∧ ¬(X ≤ 4) }

-- ### Delaborators

-- The notations above are *input* only: they teach Lean how to **read**
-- `aexp
-- { … }` and `bexp { … }`, but Lean still **prints** an expression
-- using its raw constructors -- `example_aexp` shows up as
-- `Aexp.plus (Aexp.num 3) …` rather than `aexp { 3 + X * 2 }`. A
-- *delaborator* closes the loop. Where a `macro` turns surface syntax into a
-- term (*elaboration*), a delaborator does the reverse: it turns an
-- elaborated term back into surface syntax so that Lean's own output uses our
-- concrete Imp notation.

-- Each delaborator walks a term of the given type and rebuilds the matching
-- piece of `imp_aexp`/`imp_bexp` syntax; a subterm Lean doesn't recognize is
-- printed with the `~` escape. The `@[delab …]` attribute registers the
-- top-level function to fire whenever Lean is about to display a term headed
-- by one of those constructors -- unless notation printing has been switched
-- off with `set_option pp.notation false`, which lets us fall back to the raw
-- constructors when debugging (see *Desugaring Notations* below). The
-- companion *category parenthesizer* re-inserts the parentheses the grammar's
-- precedences demand, so that, e.g., `(1 + 2) * 3` prints with its
-- parentheses intact.

-- You do not need to understand the details, and the code is collapsed below
-- for that reason. The result is that a `#check`, an `#eval`, or a proof goal
-- mentioning an Imp expression is displayed in readable Imp syntax rather
-- than as a pile of constructors.

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: printing expressions back

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

-- END DETAILS

-- The `whenPPOption getPPNotation` wrapper lets
-- `set_option pp.notation false` switch this delaborator off, revealing the
-- raw constructors (see the "Desugaring Notations" discussion, after the
-- commands are introduced).

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: registering the delaborators

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

-- END DETAILS

-- With these delaborators in place, Lean pretty-prints Imp expressions with
-- the higher-level notations rather than their raw constructors.

-- The pretty-printed version of an expression might not exactly match its
-- original form. For example, the parentheses around `X * 2` in
-- `aexp { 3 + (X * 2) }` are not printed because they are redundant -- which
-- the parenthesizer knows.

/-- info: aexp {3 + X * 2} : Aexp -/
#guard_msgs in
#check aexp { 3 + (X * 2) }

/-- info: bexp {true ∧ ¬ (X ≤ 4)} : Bexp -/
#guard_msgs in
#check bexp { true ∧ ¬(X ≤ 4) }

-- ### Evaluation

-- The arithmetic and boolean evaluators must now be extended to handle
-- variables, taking a state `st` as an extra argument. A variable is looked
-- up in the state with the map-indexing notation `st[x]` from the
-- `Typeclasses` chapter. For the notation to work, we used
-- `open scoped MyGetElem` earlier, which opens only the scoped items like
-- notation from the module.

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

-- We reuse the total-map notation (`x →ₜ v ; ∅` etc.) for states.

example : aexp { 3 + (X * 2) }.eval (X →ₜ 5 ; ∅) = 13 := by rfl

example : aexp { Z + (X * Y) }.eval (X →ₜ 5 ; Y →ₜ 4 ; ∅) = 20 := by rfl

example : bexp { true ∧ ¬(X ≤ 4) }.eval (X →ₜ 5 ; ∅) = true := by rfl

-- ## Commands

-- Now we are ready to define the syntax and behavior of Imp *commands* (or
-- *statements*). Informally, commands `c` are described by the following BNF
-- grammar:

-- c ::= skip
--     | x := a
--     | c ; c
--     | if b then c else c end
--     | while b do c end

-- Here is the formal definition of the abstract syntax of commands.

inductive Com where
  | skip
  | asgn (x : Ident) (a : Aexp)
  | seq (c1 c2 : Com)
  | cond (b : Bexp) (c1 c2 : Com)
  | whileDo (b : Bexp) (c : Com)

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: commands, macro rules

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

-- END DETAILS

-- Just as we did for expressions, we add a delaborator so that Lean prints
-- commands back in the `imp { … }` concrete syntax (see the Delaborators
-- section above). It reuses the expression delaborators for the condition of
-- an `if`/`while` and for the right-hand side of an assignment, and prints an
-- unrecognized subcommand with the `~` escape.

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: printing commands back

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

-- END DETAILS

-- As an example, here is the factorial function again, written as a formal
-- definition. When this command terminates, the variable `Y` will contain the
-- factorial of the initial value of `X`. (Compare this to the concrete Imp
-- program at the very start of the chapter.)

def fact_in_lean : Com := imp {
  Z := X;
  Y := 1;
  while (Z ≠ 0) {
    Y := Y * Z;
    Z := Z - 1
  }
}

-- Because we registered a delaborator, we can inspect a defined program with
-- `#print`, which pretty prints the stored definition using the same syntax:

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

-- ### Desugaring Notations

-- The `imp { … }` notation, together with the delaborators, is purely a
-- convenience for reading and writing programs. Occasionally, such as when
-- debugging a definition or a stuck proof, the concrete syntax `hide`s the
-- underlying structure we want to see. For those moments we can switch the
-- Imp notation off in Lean's output with `set_option pp.notation false`,
-- which our delaborators honor.

-- Note that unlike a `def`, `imp { … }` is a `macro` which is expanded during
-- elaboration, **before** the resulting term is type-checked. So
-- `fact_in_lean` is not a program hidden behind a layer of notation that a
-- proof must first peel back; it simply **is** the underlying tree of `Com`,
-- `Aexp`, and `Bexp` constructors. Consequently, when a proof goal mentions
-- an Imp program, tactics such as `cases`, `injection`, and `simp` already
-- act on those constructors directly -- there is nothing to "unfold". The
-- delaborators affect only how that tree is **displayed**. Nevertheless,
-- seeing the raw constructors is sometimes very helpful!

/-- info: imp {
  X := X + 1
} : Com -/
#guard_msgs in
#check imp { X := X + 1 }

/-- info: Com.asgn X ((Aexp.id X).plus (Aexp.num 1)) : Com -/
#guard_msgs in
set_option pp.notation false in
#check imp { X := X + 1 }

-- ### More Examples

-- A few more examples.

-- Assignment:

def plus2 : Com := imp { X := X + 2 }
def XtimesYinZ : Com := imp { Z := X * Y }

-- Loops:

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

-- An infinite loop:

def loop : Com := imp { while (true) { skip } }

-- ## Evaluating Commands

-- Next we need to define what it means to evaluate an Imp command. The fact
-- that `while` loops don't necessarily terminate makes defining an evaluation
-- function tricky.

-- ### Evaluation as a Function (Failed Attempt)

-- Here's an attempt at defining an evaluation function for commands (with a
-- bogus `while` case).

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

-- In a more conventional functional language like OCaml or Haskell we could
-- add the `while` case as follows:

-- | .whileDo b c =>
--     if b.eval st then ceval_fun st (.seq c (.whileDo b c))
--     else st

-- Lean doesn't accept such a definition ("fail to show termination") because
-- the function we want to define is not guaranteed to terminate. Indeed, it
-- *doesn't* always terminate: the full `ceval_fun` applied to the `loop`
-- program above would run forever. Since Lean aims to be not just a
-- programming language but also a consistent logic, any potentially
-- non-terminating function must be rejected. Here is what would go wrong if
-- Lean allowed non-terminating recursive functions:

-- def loop_false (n : Nat) : False := loop_false n

-- That is, propositions like `False` would become provable (`loop_false 0`
-- would be a proof of `False`), a disaster for logical consistency.

-- Thus, because it doesn't terminate on all inputs, the full `ceval_fun`
-- cannot be written in Lean -- at least not without additional tricks and
-- workarounds.

-- ### Evaluation as a Relation

-- Here's a better way: define `ceval` as a *relation* rather than a
-- *function* -- i.e., make its result a `Prop` rather than a `State`, similar
-- to what we did for `Aexp.EvalR` above.

-- This is an important change. Besides freeing us from awkward workarounds,
-- it gives us more flexibility in the definition. For example, if we add
-- nondeterministic features like `any` to the language, we want the
-- definition of evaluation to be nondeterministic -- i.e., not only will it
-- not be total, it will not even be a function!

-- We'll use the notation `st =[ c ]=> st'` for the `Com.EvalR` relation:
-- `st =[ c ]=> st'` means that executing program `c` in a starting state `st`
-- results in an ending state `st'`. This can be pronounced "`c` takes state
-- `st` to `st'`".

-- Operational Semantics

-- Here is an informal definition of evaluation, presented as inference rules
-- for readability:

--                         -----------------                  (skip)
--                         st =[ skip ]=> st

--                         a.eval st = n
--                 --------------------------------           (asgn)
--                 st =[ x := a ]=> (x →ₜ n ; st)

--                         st  =[ c1 ]=> st'
--                         st' =[ c2 ]=> st''
--                       ---------------------                (seq)
--                       st =[ c1;c2 ]=> st''

--                        b.eval st = true
--                         st =[ c1 ]=> st'
--              --------------------------------------        (ifTrue)
--              st =[ if b then c1 else c2 end ]=> st'

--                       b.eval st = false
--                         st =[ c2 ]=> st'
--              --------------------------------------        (ifFalse)
--              st =[ if b then c1 else c2 end ]=> st'

--                       b.eval st = false
--                  -----------------------------             (whileFalse)
--                  st =[ while b do c end ]=> st

--                        b.eval st = true
--                         st =[ c ]=> st'
--                st' =[ while b do c end ]=> st''
--                --------------------------------            (whileTrue)
--                st  =[ while b do c end ]=> st''

-- Here is the formal definition. Make sure you understand how it corresponds
-- to the inference rules.

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

-- The cost of defining evaluation as a relation instead of a function is that
-- we now need to construct a *proof* that some program evaluates to some
-- result state, rather than letting Lean's computation mechanism do it for
-- us.

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

-- ### Exercise (2 stars): ceval_example2 ⭐⭐

example :
    ∅ =[
      X := 0;
      Y := 1;
      Z := 2
    ]=> (Z →ₜ 2 ; Y →ₜ 1 ; X →ₜ 0 ; ∅) := by
  sorry

-- _Quiz:_

-- Is the following proposition provable?

--   ∀ (c : Com) (st st' : State),
--     st =[ skip; ~c ]=> st' →
--     st =[ c ]=> st'

-- (A) Yes (B) No (C) Not sure

-- _Quiz:_

-- Is the following proposition provable?

--   ∀ (c1 c2 : Com) (st st' : State),
--     st =[ ~c1 ~c2 ]=> st' →
--     st =[ c1 ]=> st →
--     st =[ c2 ]=> st'

-- (A) Yes (B) No (C) Not sure

-- _Quiz:_

-- Is the following proposition provable?

--   ∀ (b : Bexp) (c : Com) (st st' : State),
--     st =[ if (~b) { ~c } else { ~c } ]=> st' →
--     st =[ c ]=> st'

-- (A) Yes (B) No (C) Not sure

-- _Quiz:_

-- Is the following proposition provable?

--   ∀ (b : Bexp),
--     (∀ st, b.eval st = true) →
--     ∀ (c : Com) (st : State),
--     ¬ ∃ st', st =[ while (~b) { ~c } ]=> st'

-- (A) Yes (B) No (C) Not sure

-- _Quiz:_

-- Is the following proposition provable?

--   ∀ (b : Bexp) (c : Com) (st : State),
--     (¬ ∃ st', st =[ while (~b) { ~c } ]=> st') →
--     ∀ st'', b.eval st'' = true

-- (A) Yes (B) No (C) Not sure

-- ### Determinism of Evaluation

-- Changing from a computational to a relational definition of evaluation is a
-- good move because it frees us from the artificial requirement that
-- evaluation be a total function. But it raises a question: is the relational
-- definition really a partial *function*? Could the same command, from the
-- same state, evaluate to two different final states? In fact this cannot
-- happen: `ceval` *is* a partial function.

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

-- ### Exercise (3 stars): pup_to_n (Optional) ⭐⭐⭐

-- Write an Imp program that sums the numbers from `1` to `X` (inclusive) in
-- the variable `Y`. Your program should update the state as shown in
-- `pup_to_2_ceval`, which you can reverse-engineer to discover the program
-- you should write. The proof of that theorem will be somewhat lengthy.

def pup_to_n : Com := sorry

theorem pup_to_2_ceval :
    (X →ₜ 2 ; ∅) =[ pup_to_n ]=>
      (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅) := by
  sorry

-- ## Reasoning About Imp Programs

-- We'll get into more systematic and powerful techniques for reasoning about
-- Imp programs in the next chapter, but we can already do a few things
-- (albeit in a somewhat low-level way) just by working with the bare
-- definitions. This section explores some examples.

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

-- ### Exercise (3 stars): XtimesYinZ_spec (Optional) ⭐⭐⭐

-- State and prove a specification of `XtimesYinZ`.

-- FILL IN HERE

-- ### Exercise (3 stars): loop_never_stops ⭐⭐⭐

-- Hint: proceed by induction on the assumed derivation showing that `loop`
-- terminates. Most of the cases are immediately contradictory and so can be
-- solved in one step (by `simp`/`discriminate` on the impossible command
-- equation).

theorem loop_never_stops (st st' : State) : ¬ (st =[ loop ]=> st') := by
  sorry

-- ### Exercise (3 stars): no_whiles_eqv ⭐⭐⭐

-- The following function yields `true` just on programs with no while loops.
-- Using `inductive`, write a property `Com.NoWhilesR` that holds exactly when
-- `c` is while-free, then prove it equivalent to `Com.no_whiles`.

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

-- ### Exercise (4 stars): no_whiles_terminating ⭐⭐⭐⭐

-- Imp programs that don't involve while loops always terminate. State and
-- prove a theorem `no_whiles_terminating` that says this. Use either
-- `Com.no_whiles` or `Com.NoWhilesR`, as you prefer.

theorem no_whiles_terminating (c : Com) (st : State) (h : Com.NoWhilesR c) :
    ∃ st', st =[ c ]=> st' := by
  sorry

-- And here is an alternative solution by induction on `c` (using
-- `Com.no_whiles` instead of `Com.NoWhilesR`):

-- FILL IN HERE


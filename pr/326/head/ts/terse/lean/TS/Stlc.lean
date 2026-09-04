import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer
import LF.Typeclasses
import TS.Smallstep

import SFLCompat

--  # Stlc: The Simply Typed Lambda-Calculus

--  Our job for this chapter: Formalize a small *functional*
--  language and its type system.
--
--  Language: The *simply typed lambda-calculus* (STLC).
--
--  - A small subset of Lean's built-in functional
--    language...
--
--  - ...but we'll use different concrete syntax (to avoid
--    confusion, and for consistency with standard
--    treatments)
--
--  Main new technical challenges:
--
--  - variable binding
--  - substitution

--  The STLC lives in the lower-left front corner of the
--  famous *lambda cube* (also called the *Barendregt
--  Cube*), which visualizes three sets of features that can
--  be added to its simple core:

--  Calculus of Constructions
--   type operators +--------+
--                 /|       /|
--                / |      / |
--  polymorphism +--------+  |
--               |  |     |  |
--               |  +-----|--+
--               | /      | /
--               |/       |/
--               +--------+ dependent types
--             STLC

--  Moving from bottom to top in the cube corresponds to
--  adding *polymorphic types* like `∀ α : Type, α → α`.
--  Adding *just* polymorphism gives us the famous
--  Girard-Reynolds calculus, System F.
--
--  Moving from front to back corresponds to adding *type
--  operators* like `List`.
--
--  Moving from left to right corresponds to adding
--  *dependent types* like `∀ n, ArrayOfSize n`.
--
--  The top right corner on the back, which combines all
--  three features, is called the *Calculus of
--  Constructions*. First studied by Coquand and Huet, it
--  forms the foundation of Lean's logic.

--  ## Overview

--  Begin with some set of *base types* (here, just `Bool`)
--
--  Add: variables, function abstractions, and applications
--
--  Informal concrete syntax of terms `t`:

--  t ::= x                     (variable)
--      | λ x : T . t           (abstraction)
--      | t t                   (application)
--      | true                  (constant true)
--      | false                 (constant false)
--      | if t then t else t    (conditional)

--  The *types* of the STLC include the base type `Bool` for
--  boolean values and arrow types for functions.

--  T ::= Bool
--      | T → T

--  Some examples of STLC terms:

--   `λx:Bool. x`

--  The identity function for booleans.

--   `(λx:Bool. x) true`

--  The identity function for booleans, applied to the
--  boolean `true`.

--   `λx:Bool. if x then false else true`

--  The boolean "not" function.

--   `λx:Bool. true`

--  The constant function that takes every (boolean)
--  argument to `true`.

--   `λx:Bool. λy:Bool. x`

--  A two-argument function that takes two booleans and
--  returns the first one.

--   `(λx:Bool. λy:Bool. x) false true`

--  A two-argument function that takes two booleans and
--  returns the first one, applied to the booleans `false`
--  and `true`.

--   `λf:Bool → Bool. f (f true)`

--  A higher-order function that takes a *function* `f`
--  (from booleans to booleans) as an argument, applies `f`
--  to `true`, and applies `f` again to the result.

--   `(λf:Bool → Bool. f (f true)) (λx:Bool. false)`

--  The same higher-order function, applied to the
--  constantly `false` function.

--  Now reconsider our examples, each along with its type:
--
--  - `λx:Bool. x` has type `Bool → Bool`
--
--  - `(λx:Bool. x) true` has type `Bool`
--
--  - `λx:Bool. if x then false else true` has type
--    `Bool → Bool`
--
--  - `λx:Bool. true` has type `Bool → Bool`
--
--  - `λx:Bool. λy:Bool. x` has type `Bool → Bool → Bool`
--    (i.e., `Bool → (Bool → Bool)`)
--
--  - `(λx:Bool. λy:Bool. x) false true` has type `Bool`
--
--  The last two, higher-order examples are left off the
--  list on purpose — working out their types is the subject
--  of the quizzes that follow.

--  Note that *all* functions are anonymous.
--
--  We'll see how to add named function declarations as
--  "syntactic sugar" in the `MoreStlc` chapter.

--   ----------------------------------------

--  _Quiz:_

--  What is the type of the following term?
--
--      λf:Bool → Bool. f (f true)
--
--  (A) `Bool → (Bool → Bool)`
--
--  (B) `(Bool → Bool) → Bool`
--
--  (C) `Bool → Bool`
--
--  (D) `Bool`
--
--  (E) none of the above

--   ----------------------------------------

--  _Quiz:_

--  How about the type of this one?
--
--      (λf:Bool → Bool. f (f true)) (λx:Bool. false)
--
--  (A) `Bool → (Bool → Bool)`
--
--  (B) `(Bool → Bool) → Bool`
--
--  (C) `Bool → Bool`
--
--  (D) `Bool`
--
--  (E) none of the above

--   ----------------------------------------

--  ## Syntax

--  We next formalize the syntax of the STLC.

namespace Stlc

open scoped MyGetElem

--  ### Types

inductive Ty where
  | bool
  | arrow (T₁ T₂ : Ty)

--  ### Terms

inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (T : Ty) (t : Tm)
  | tru
  | fls
  | ite (c t e : Tm)

--  We need some notation magic to set up the concrete
--  syntax, as we did in the Types chapter...

--  Types and terms are both written inside `<{ … }>`; `~e`
--  escapes to Lean.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: types)
--  The `stlcTy` grammar covers `Bool`, arrows (written `→`
--  or `->`, associating to the right), parentheses, and
--  `~e`. A bare identifier other than `Bool` is spliced in
--  as a Lean term, so a local `T` — or any Lean expression
--  of type `Ty` — can appear directly inside the brackets.
--
--  To extend the grammar, a later chapter adds a `syntax`
--  line to the category and a matching `macro_rules` case;
--  that is all it takes to add a new type construct.

declare_syntax_cat stlcTy
syntax:max "~" term:max : stlcTy
syntax:max "(" stlcTy ")" : stlcTy
syntax:max ident : stlcTy
syntax:50 stlcTy:51 " → " stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " -> " stlcTy:50 : stlcTy
syntax:max (name := tyBracket) "<{ " stlcTy " }>" : term

macro_rules (kind := tyBracket)
  | `(<{ ~$T:term }>)    => pure T
  | `(<{ ($T:stlcTy) }>) => `(<{ $T:stlcTy }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Bool" => `(Ty.bool)
      | _ => `(($x : Ty))
  | `(<{ $T₁:stlcTy → $T₂:stlcTy }>)  => `(Ty.arrow <{ $T₁:stlcTy }> <{ $T₂:stlcTy }>)
  | `(<{ $T₁:stlcTy -> $T₂:stlcTy }>) => `(Ty.arrow <{ $T₁:stlcTy }> <{ $T₂:stlcTy }>)
--  END DETAILS

--  We'll write types inside of `<{ ... }>` brackets:

#check <{ Bool }>
#check <{ Bool -> Bool }>
#check <{ (Bool -> Bool) -> Bool }>

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: terms)
--  Terms are built from variables, application (associating
--  to the left), abstraction, the two boolean constants,
--  and conditionals. A binding occurrence — the `x` in
--  `λ x : T . t` — has a small grammar of its own,
--  `stlcVar`, and `varStr` turns it into the string that
--  `Tm.abs` stores.
--
--  Because types and terms share the brackets, each
--  `macro_rules` group says which bracket it belongs to
--  (`kind := tyBracket`, `kind := tmBracket`), and each
--  antiquote in a nested quotation says which grammar it
--  came from. A bare identifier is the one genuinely
--  overlapping case: `Bool` in term position would
--  otherwise quietly become a variable named `Bool`, so
--  that rule rejects it, which also settles which grammar a
--  lone `<{ Bool }>` belongs to.
--
--  The last production, `[x := s] t`, is the notation for
--  substitution; we give it its meaning when we define
--  substitution below. It binds tighter than application,
--  so `[x:=s] t₁ t₂` is the application of `[x:=s] t₁` to
--  `t₂`, and a `λ` or `if` body must be parenthesized:
--  `[x:=s] (λ y : Bool . x)`.

declare_syntax_cat stlcVar
syntax:max ident : stlcVar
syntax:max "~" term:max : stlcVar

open Lean in
/-- The string named by a variable in binding position. -/
def varStr (x : TSyntax `stlcVar) : MacroM Term :=
  match x with
  | `(stlcVar| $i:ident) => pure (quote i.getId.toString : Term)
  | `(stlcVar| ~$e)      => pure e
  | _ => Macro.throwUnsupported

declare_syntax_cat stlcTm
syntax:max "~" term:max : stlcTm
syntax:max "(" stlcTm ")" : stlcTm
syntax:max ident : stlcTm
syntax:75 stlcTm:75 ppSpace stlcTm:76 : stlcTm
syntax:50 "λ " stlcVar " : " stlcTy " . " stlcTm:50 : stlcTm
syntax:50 "if " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm
syntax:max "[" stlcVar " := " stlcTm "] " stlcTm:max : stlcTm
syntax:max (name := tmBracket) "<{ " stlcTm " }>" : term

open Lean in
macro_rules (kind := tmBracket)
  | `(<{ ~$e:term }>)    => pure e
  | `(<{ ($t:stlcTm) }>) => `(<{ $t:stlcTm }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "true"  => `(Tm.tru)
      | "false" => `(Tm.fls)
      | "Bool"  => Macro.throwErrorAt x "`Bool` is a type, not a term"
      | _       => `(Tm.var $(quote x.getId.toString))
  | `(<{ $t₁:stlcTm $t₂:stlcTm }>) => `(Tm.app <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ λ $x : $T . $t }>) => do
      `(Tm.abs $(← varStr x) <{ $T:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ if $c then $t else $e }>) =>
      `(Tm.ite <{ $c:stlcTm }> <{ $t:stlcTm }> <{ $e:stlcTm }>)
--  END DETAILS

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing it back)
--  A *delaborator* runs the grammar backwards: it rebuilds
--  the concrete syntax from a `Ty` or `Tm` value, so that
--  types and terms appearing in goals and in `#check`
--  output print as `<{ λ x : Bool . x }>` rather than as a
--  pile of constructors. (Setting `pp.notation false` turns
--  it off, revealing the underlying representation.)

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
/-- Re-inserts parentheses in `stlcTy` output according to the grammar's precedences. -/
@[category_parenthesizer stlcTy]
def stlcTy.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `stlcTy true wrapParens prec <|
    parenthesizeCategoryCore `stlcTy prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(stlcTy| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
/-- Re-inserts parentheses in `stlcTm` output according to the grammar's precedences. -/
@[category_parenthesizer stlcTm]
def stlcTm.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `stlcTm true wrapParens prec <|
    parenthesizeCategoryCore `stlcTm prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(stlcTm| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTy` concrete syntax from a `Ty` value. -/
partial def delabTyInner : DelabM (TSyntax `stlcTy) := do
  let stx ←
    match_expr ← getExpr with
    | Ty.bool => `(stlcTy| $(mkIdent `Bool):ident)
    | Ty.arrow _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a → $b)
    | _ => do
        match ← delab with
        | `($i:ident) => `(stlcTy| $i:ident)
        | e => `(stlcTy| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean in
/-- Is `s` usable as a bare identifier in the object syntax? -/
def isPlainName (s : String) : Bool :=
  !s.isEmpty && s != "_" && !s.front.isDigit &&
    s.all fun c => c.isAlphanum || c == '_'

open Lean in
/-- Is `s` usable as a bare variable in `stlcTm` rather than as reserved syntax? -/
def isPlainTmVarName (s : String) : Bool :=
  isPlainName s && s != "true" && s != "false" && s != "Bool"

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcVar` concrete syntax from the string in a binding position. -/
def delabVarInner : DelabM (TSyntax `stlcVar) := do
  match ← delab with
  | `($s:str) =>
      if isPlainName s.getString then
        `(stlcVar| $(mkIdent (Name.mkSimple s.getString)):ident)
      else `(stlcVar| ~$s)
  | e => `(stlcVar| ~$e)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTm` concrete syntax from a `Tm` value. -/
partial def delabTmInner : DelabM (TSyntax `stlcTm) := do
  let stx ←
    match_expr ← getExpr with
    | Tm.tru => `(stlcTm| $(mkIdent `true):ident)
    | Tm.fls => `(stlcTm| $(mkIdent `false):ident)
    | Tm.var _ => do
        let x ← withAppArg delab
        match x with
        | `($s:str) =>
            if isPlainTmVarName s.getString then
              `(stlcTm| $(mkIdent (Name.mkSimple s.getString)):ident)
            else
              let var : Term := mkIdent ``Stlc.Tm.var
              `(stlcTm| ~($var $x))
        | _ =>
            let var : Term := mkIdent ``Stlc.Tm.var
            `(stlcTm| ~($var $x))
    | Tm.app _ _ => do
        let f ← withAppFn <| withAppArg delabTmInner
        let a ← withAppArg delabTmInner
        `(stlcTm| $f $a)
    | Tm.abs _ _ _ => do
        let x ← withAppFn <| withAppFn <| withAppArg delabVarInner
        let T ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| λ $x : $T . $t)
    | Tm.ite _ _ _ => do
        let c ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let t ← withAppFn <| withAppArg delabTmInner
        let e ← withAppArg delabTmInner
        `(stlcTm| if $c then $t else $e)
    | _ => do
        -- `subst` is defined below, so it is matched by name rather than with
        -- `match_expr`; a substitution prints in its own bracket notation.
        let e ← getExpr
        if e.getAppFn.constName? == some `Stlc.subst && e.getAppNumArgs == 3 then
          let x ← withAppFn <| withAppFn <| withAppArg delabVarInner
          let s ← withAppFn <| withAppArg delabTmInner
          let t ← withAppArg delabTmInner
          `(stlcTm| [$x := $s] $t)
        else
          match ← delab with
          | `($i:ident) => `(stlcTm| $i:ident)
          | e => `(stlcTm| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Stlc.Ty.bool, delab app.Stlc.Ty.arrow]
def delabTy : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Ty.bool => true | Ty.arrow _ _ => true | _ => false
  match ← delabTyInner with
  | `(stlcTy| ~$e) => pure e
  | e => `(<{ $e:stlcTy }>)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Stlc.Tm.var, delab app.Stlc.Tm.app, delab app.Stlc.Tm.abs,
  delab app.Stlc.Tm.tru, delab app.Stlc.Tm.fls, delab app.Stlc.Tm.ite]
def delabTm : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Tm.var _ => true | Tm.app _ _ => true | Tm.abs _ _ _ => true
    | Tm.tru => true | Tm.fls => true | Tm.ite _ _ _ => true
    | _ => false
  match ← delabTmInner with
  | `(stlcTm| ~($e)) => pure e
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
--  END DETAILS

--  Here are the terms we will use as running examples,
--  written in the new notation:

abbrev idB := <{ λ x : Bool . x }>

abbrev idBB := <{ λ x : Bool → Bool . x }>

abbrev idBBBB := <{ λ x : (Bool → Bool) → (Bool → Bool) . x }>

abbrev k := <{ λ x : Bool . λ y : Bool . x }>

abbrev notB := <{ λ x : Bool . if x then false else true }>

--  Note that an abstraction `λ x : T . t` (formally,
--  `Tm.abs` applied to `x`, `T`, and `t`) is always
--  annotated with the type `T` of its parameter, in
--  contrast to Lean (and other functional languages like
--  ML, Haskell, etc.), which use type inference to fill in
--  missing annotations. We're not considering type
--  inference at all here.

--  ## Operational Semantics

--  To define the small-step semantics of STLC terms...
--
--  - We begin by defining the set of values.
--
--  - Next, we define *free variables* and *substitution*.
--    These are used in the reduction rule for application
--    expressions.
--
--  - Finally, we give the small-step relation itself.

--  ### Values

--  To define the values of the STLC, we have a few cases to
--  consider.
--
--  First, for the boolean part of the language, the
--  situation is clear: `true` and `false` are the only
--  values. An `if` expression is never a value.

--  Second, an application is not a value: it represents a
--  function being invoked on some argument, which clearly
--  still has work left to do.

--  Third, for abstractions, we have a choice:
--
--  - We can say that `λx:T. t` is a value only when `t` is
--    a value — i.e., only if the function's body has been
--    reduced (as much as it can be without knowing what
--    argument it is going to be applied to).
--
--  - Or we can say that `λx:T. t` is always a value, no
--    matter whether `t` is one or not — in other words, we
--    can say that reduction stops at abstractions.
--
--  Our usual way of evaluating expressions in Lean makes
--  the first choice — for example,

#reduce fun _x : Bool => 3 + 4

--  yields:
--
--      fun _x => 7
--
--  But Lean is rather unusual in this respect. Most
--  functional programming languages make the second choice
--  — reduction of a function's body only begins when the
--  function is actually applied to an argument.
--
--  We also make the second choice here.

inductive Tm.IsValue : Tm → Prop where
  | abs (x : String) (T₂ : Ty) (t₁ : Tm) : Tm.IsValue <{ λ ~x : ~T₂ . ~t₁ }>
  | tru : Tm.IsValue <{ true }>
  | fls : Tm.IsValue <{ false }>

attribute [StlcEval] Tm.IsValue.abs Tm.IsValue.tru Tm.IsValue.fls

theorem idB_value : idB.IsValue := .abs ..
theorem idBB_value : idBB.IsValue := .abs ..
theorem notB_value : notB.IsValue := .abs ..

--  ### STLC Programs

--  Finally, we must consider what constitutes a *complete*
--  program.
--
--  Intuitively, a "complete program" must not refer to any
--  undefined variables. We'll see shortly how to define the
--  *free* variables in a STLC term. A complete program,
--  then, is one that is *closed* — that is, that contains
--  no free variables.
--
--  (Conversely, a term that may contain free variables is
--  often called an *open term*.)

--  Having made the choice not to reduce under abstractions,
--  we don't need to worry about whether variables are
--  values, since we'll always be reducing programs "from
--  the outside in," and that means the `step` relation will
--  always be working with closed terms.

--  ### Substitution

--  Now we come to the heart of the STLC: the operation of
--  *substituting* one term for a variable in another term.
--  This operation is used below to define the operational
--  semantics of function application, where we will need to
--  substitute the argument term for the function parameter
--  in the function's body. For example, we reduce
--
--      (λx:Bool. if x then true else x) false
--
--  to
--
--      if false then true else false
--
--  by substituting `false` for the parameter `x` in the
--  body of the function.
--
--  In general, we need to be able to substitute some given
--  term `s` for occurrences of some variable `x` in another
--  term `t`. Informally, this is written `[x:=s]t` and
--  pronounced "substitute `s` for `x` in `t`."

--  Here are some examples:
--
--  - `[x:=true] (if x then true else false)` yields
--    `if true then true else false`
--
--  - `[x:=true] x` yields `true`
--
--  - `[x:=true] (if x then x else y)` yields
--    `if true then true else y`
--
--  - `[x:=true] y` yields `y`
--
--  - `[x:=true] false` yields `false` (vacuous
--    substitution)
--
--  - `[x:=true] (λy:Bool. if y then x else false)` yields
--    `λy:Bool. if y then true else false`
--
--  - `[x:=true] (λy:Bool. x)` yields `λy:Bool. true`
--
--  - `[x:=true] (λy:Bool. y)` yields `λy:Bool. y`
--
--  - `[x:=true] (λx:Bool. x)` yields `λx:Bool. x`
--
--  The last example is illuminating: substituting `x` with
--  `true` in `λx:Bool. x` does *not* yield `λx:Bool. true`!
--  The reason for this is that the `x` in the body of
--  `λx:Bool. x` is *bound* by the abstraction: it is a new,
--  local name that just happens to be spelled the same as
--  some global name `x`.

--  Here is the definition, informally...
--
--      [x:=s]x               = s
--      [x:=s]y               = y                     if x ≠ y
--      [x:=s](λx:T. t)       = λx:T. t
--      [x:=s](λy:T. t)       = λy:T. [x:=s]t         if x ≠ y
--      [x:=s](t₁ t₂)         = ([x:=s]t₁) ([x:=s]t₂)
--      [x:=s]true            = true
--      [x:=s]false           = false
--      [x:=s](if t₁ then t₂ else t₃) =
--                      if [x:=s]t₁ then [x:=s]t₂ else [x:=s]t₃

--  ... and formally:

section
set_option hygiene false in
local macro_rules (kind := tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- `.var y`, not `<{ ~y }>`: `y` is the variable's *name*, a `String`
  -- (see the note below the definition).
  | .var y =>
      if x = y then s else t
  | <{ λ ~y : ~T . ~t₁ }> =>
      if x = y then t else <{ λ ~y : ~T . [~x := ~s] ~t₁ }>
  | <{ ~t₁ ~t₂ }> =>
      <{ ([~x := ~s] ~t₁) ([~x := ~s] ~t₂) }>
  | <{ true }> =>
      <{ true }>
  | <{ false }> =>
      <{ false }>
  | <{ if ~t₁ then ~t₂ else ~t₃ }> =>
      <{ if [~x := ~s] ~t₁ then [~x := ~s] ~t₂ else [~x := ~s] ~t₃ }>
end

macro_rules (kind := tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: substitution)
--  One more line registers substitutions with the printer,
--  so that a goal mentioning one reads as `[x := s] t`
--  rather than as a `subst` application.

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Stlc.subst]
def delabSubst : Delab := whenPPOption getPPNotation do
  match ← delabTmInner with
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
--  END DETAILS

variable (x y : String) (s t t₁ t₂ t₃ : Tm) (T : Ty)

@[simp] theorem subst_var_eq : <{ [~x := ~s] ~(Tm.var x) }> = s := by
  simp [subst]

@[simp] theorem subst_var_ne (h : x ≠ y) : <{ [~x := ~s] ~(Tm.var y) }> = .var y := by
  simp [subst, h]

@[simp] theorem subst_abs_eq : <{ [~x := ~s] (λ ~x : ~T . ~t) }> = <{ λ ~x : ~T . ~t }> := by
  simp [subst]

@[simp] theorem subst_abs_ne (h : x ≠ y) :
    <{ [~x := ~s] (λ ~y : ~T . ~t) }> = <{ λ ~y : ~T . [~x := ~s] ~t }> := by
  simp [subst, h]

@[simp] theorem subst_app :
    <{ [~x := ~s] (~t₁ ~t₂) }> = <{ ([~x := ~s] ~t₁) ([~x := ~s] ~t₂) }> := rfl

@[simp] theorem subst_tru : <{ [~x := ~s] true }> = <{ true }> := rfl

@[simp] theorem subst_fls : <{ [~x := ~s] false }> = <{ false }> := rfl

@[simp] theorem subst_ite :
    <{ [~x := ~s] (if ~t₁ then ~t₂ else ~t₃) }> =
      <{ if [~x := ~s] ~t₁ then [~x := ~s] ~t₂ else [~x := ~s] ~t₃ }> := rfl

--   ----------------------------------------

--  _Quiz:_

--  What is the result of the following substitution?
--
--      [x:=s](λy:T₁. x (λx:T₂. x))
--
--  (1) `(λy:T₁. x (λx:T₂. x))`
--
--  (2) `(λy:T₁. s (λx:T₂. s))`
--
--  (3) `(λy:T₁. s (λx:T₂. x))`
--
--  (4) none of the above

--   ----------------------------------------

--  *Technical note*: Substitution becomes trickier to
--  define if we consider the case where `s`, the term being
--  substituted for a variable in some other term, may
--  itself contain free variables. We say that `s` is an
--  *open* term.

--  Here is an example. Using the above definition to
--  substitute the open term
--
--      s = λx:Bool. r
--
--  (where `r` is a *free* reference to some global
--  resource) for the free variable `z` in the term
--
--      t = λr:Bool. z
--
--  where `r` is a bound variable, we would get
--
--      λr:Bool. λx:Bool. r
--
--  where the free reference to `r` in `s` has been
--  "captured" by the binder at the beginning of `t`.

--  Why would this be bad? Because it violates the principle
--  that the names of bound variables do not matter. For
--  example, if we rename the bound variable in `t`, e.g.,
--  let
--
--      t' = λw:Bool. z
--
--  then `[z:=s]t'` is
--
--      λw:Bool. λx:Bool. r
--
--  which does not behave the same as the substituting in
--  the original `t`:
--
--      [z:=s]t = λr:Bool. λx:Bool. r
--
--  That is, renaming a bound variable in `t` would change
--  how `t` behaves under our simple substitution. So
--  substitution gets more complicated in that setting, but
--  fortunately we don't have that problem in our STLC
--  variant.

--  Fortunately, since we are only interested here in
--  defining the `step` relation on *closed* terms (i.e.,
--  terms like `λx:Bool. x` that include binders for all of
--  the variables they mention), we can sidestep this extra
--  complexity, but it must be dealt with when formalizing
--  richer languages.

--  ### Reduction

--  v.IsValue
--                         -----------------------      (appAbs)
--                          (λx:T. t) v ⟶ [x:=v]t
--
--                                t₁ ⟶ t₁'
--                            ----------------          (app1)
--                             t₁ t₂ ⟶ t₁' t₂
--
--                                v.IsValue
--                                t₂ ⟶ t₂'
--                            ----------------          (app2)
--                             v₁ t₂ ⟶ v₁ t₂'

--  (plus the usual rules for conditionals).

--  The `appAbs` rule is often called *beta-reduction*.

--  This is *call by value* reduction: to reduce an
--  application `(t₁ t₂)`, we
--
--  - first reduce `t₁` to a value: a function `λx:T. t`
--
--  - then reduce the argument `t₂` to a value `v`
--
--  - then reduce the application itself by substituting `v`
--    for the bound variable `x` in the body `t`.

section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
  | appAbs (x : String) (T : Ty) (t v : Tm) (hv : v.IsValue) :
      <{ (λ ~x : ~T . ~t) ~v }> ⟶ <{ [~x := ~v] ~t }>
  | app1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ ~t₁ ~t₂ }> ⟶ <{ ~t₁' ~t₂ }>
  | app2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ ~v₁ ~t₂ }> ⟶ <{ ~v₁ ~t₂' }>
  | ifTrue (t₁ t₂ : Tm) :
      <{ if true then ~t₁ else ~t₂ }> ⟶ t₁
  | ifFalse (t₁ t₂ : Tm) :
      <{ if false then ~t₁ else ~t₂ }> ⟶ t₂
  | ifStep (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if ~t₁ then ~t₂ else ~t₃ }> ⟶ <{ if ~t₁' then ~t₂ else ~t₃ }>
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

-- for later use with `normalize`
attribute [StlcEval] Step.appAbs Step.app1 Step.app2 Step.ifTrue Step.ifFalse Step.ifStep

--   ----------------------------------------

--  _Quiz:_

--  What does the following term step to?
--
--      (λx:Bool → Bool. x) (λx:Bool. x) ⟶ ???
--
--  (A) `λx:Bool. x`
--
--  (B) `λx:Bool → Bool. x`
--
--  (C) `(λx:Bool → Bool. x) (λx:Bool. x)`
--
--  (D) none of the above

--   ----------------------------------------

--  _Quiz:_

--  What does the following term step to?
--
--      (λx:Bool → Bool. x)
--          ((λx:Bool → Bool. x) (λx:Bool. x))
--      ⟶ ???
--
--  (A) `λx:Bool. x`
--
--  (B) `λx:Bool → Bool. x`
--
--  (C) `(λx:Bool → Bool. x) (λx:Bool. x)`
--
--  (D)
--  `(λx:Bool → Bool. x) ((λx:Bool → Bool. x) (λx:Bool. x))`
--
--  (E) none of the above

--   ----------------------------------------

--  _Quiz:_

--  What does the following term *normalize* to?
--
--      (λx:Bool → Bool. x) notB true  ⟶* ???
--
--  where `notB` abbreviates
--  `λx:Bool. if x then false else true`
--
--  (A) `λx:Bool. x`
--
--  (B) `true`
--
--  (C) `false`
--
--  (D) `notB`
--
--  (E) none of the above

--   ----------------------------------------

--  _Quiz:_

--  What does the following term normalize to?
--
--      (λx:Bool. x) (notB true) ⟶* ???
--
--  (A) `λx:Bool. x`
--
--  (B) `true`
--
--  (C) `false`
--
--  (D) `notB true`
--
--  (E) none of the above

--   ----------------------------------------

--  ### Examples

--  Example:
--
--      (λx:Bool → Bool. x) (λx:Bool. x) ⟶* λx:Bool. x
--
--  i.e.,
--
--      idBB idB ⟶* idB

example : <{ ~idBB ~idB }> ⟶* idB := by
  apply Multi.step (y := idB)
  · exact .appAbs "x" <{ Bool → Bool }> <{ x }> idB idB_value
  · rfl

--  Example:
--
--      (λx:Bool → Bool. x) ((λx:Bool → Bool. x) (λx:Bool. x))
--            ⟶* λx:Bool. x
--
--  i.e.,
--
--      (idBB (idBB idB)) ⟶* idB.

example : <{ ~idBB (~idBB ~idB) }> ⟶* idB := by
  -- the same reduction happens twice, so we name it
  have step₁ : <{ ~idBB ~idB }> ⟶ idB := by
    exact .appAbs "x" <{ Bool → Bool }> <{ x }> idB idB_value
  apply Multi.step (y := <{ ~idBB ~idB }>)
  · exact .app2 idBB <{ ~idBB ~idB }> idB idBB_value step₁
  apply Multi.step (y := idB)
  · exact step₁
  · rfl

--  Example:
--
--      (λx:Bool → Bool. x)
--         (λx:Bool. if x then false else true)
--         true
--            ⟶* false
--
--  i.e.,
--
--      (idBB notB) true ⟶* false.

example : <{ ~idBB ~notB true }> ⟶* <{ false }> := by
  apply Multi.step (y := <{ ~notB true }>)
  · exact .app1 <{ ~idBB ~notB }> notB <{ true }>
      (.appAbs "x" <{ Bool → Bool }> <{ x }> notB notB_value)
  apply Multi.step (y := <{ if true then false else true }>)
  · exact .appAbs "x" <{ Bool }> <{ if x then false else true }> <{ true }> .tru
  apply Multi.step (y := <{ false }>)
  · exact .ifTrue <{ false }> <{ true }>
  · rfl

--  Example:
--
--      (λx:Bool → Bool. x)
--         ((λx:Bool. if x then false else true) true)
--            ⟶* false
--
--  i.e.,
--
--      idBB (notB true) ⟶* false.
--
--  (Note that this term doesn't actually typecheck; even
--  so, we can ask how it reduces.)

example : <{ ~idBB (~notB true) }> ⟶* <{ false }> := by
  apply Multi.step (y := <{ ~idBB (if true then false else true) }>)
  · exact .app2 idBB <{ ~notB true }> <{ if true then false else true }> idBB_value
      (.appAbs "x" <{ Bool }> <{ if x then false else true }> <{ true }> .tru)
  apply Multi.step (y := <{ ~idBB false }>)
  · exact .app2 idBB <{ if true then false else true }> <{ false }> idBB_value
      (.ifTrue <{ false }> <{ true }>)
  apply Multi.step (y := <{ false }>)
  · exact .appAbs "x" <{ Bool → Bool }> <{ x }> <{ false }> .fls
  · rfl

--  As in the Smallstep chapter, we can use the `normalize`
--  tactic to simplify these proofs:

example : <{ ~idBB ~idB }> ⟶* idB := by
  normalize using StlcEval

example : <{ ~idBB (~idBB ~idB) }> ⟶* idB := by
  normalize using StlcEval

example : <{ ~idBB ~notB true }> ⟶* <{ false }> := by
  normalize using StlcEval

example : <{ ~idBB (~notB true) }> ⟶* <{ false }> := by
  normalize using StlcEval

--   ----------------------------------------

--  _Quiz:_

--  Do values and normal forms coincide in the language
--  presented so far?
--
--  (A) yes
--
--  (B) no

--   ----------------------------------------

--  ## Typing

--  Next we consider the typing relation of the STLC, which
--  is meant to prevent reduction from getting stuck.

--  ### Contexts

--  *Question*: What is the type of the term "`x y`"?
--
--  *Answer*: It depends on the types of `x` and `y`!
--
--  I.e., in order to assign a type to a term, we need to
--  know what assumptions we should make about the types of
--  its free variables.
--
--  This leads us to a three-place *typing judgment*,
--  informally written `Γ ⊢ t ⦂ T`, where `Γ` is a "typing
--  context" — a mapping from variables to their types.

abbrev Context := PartialMap String Ty

--  Following the usual notation for partial maps, we write
--  `(x ↦ T, Γ)` for "update the partial function `Γ` so
--  that it maps `x` to `T`."

--  ### Typing Relation

--  Γ x = T₁
--                              ------------                       (var)
--                               Γ ⊢ x ⦂ T₁
--
--                          x ↦ T₂ ; Γ ⊢ t₁ ⦂ T₁
--                        -------------------------                (abs)
--                         Γ ⊢ λx:T₂. t₁ ⦂ T₂ → T₁
--
--                            Γ ⊢ t₁ ⦂ T₂ → T₁
--                              Γ ⊢ t₂ ⦂ T₂
--                           ------------------                    (app)
--                             Γ ⊢ t₁ t₂ ⦂ T₁
--
--                            -----------------                    (tru)
--                             Γ ⊢ true ⦂ Bool
--
--                           ------------------                    (fls)
--                            Γ ⊢ false ⦂ Bool
--
--               Γ ⊢ t₁ ⦂ Bool    Γ ⊢ t₂ ⦂ T₁    Γ ⊢ t₃ ⦂ T₁
--              ---------------------------------------------      (ite)
--                     Γ ⊢ if t₁ then t₂ else t₃ ⦂ T₁

--  We can read the three-place relation `Γ ⊢ t ⦂ T` as:
--  "under the assumptions in Γ, the term `t` has the type
--  `T`."

--  In the formal development, we write this judgment inside
--  the same `<{ .. }>` brackets.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: contexts and judgments)
--  Contexts get a grammar of their own, `stlcCtx`. The
--  **meaning** is the map update we already have —
--  `x ↦ T ; Γ` expands to exactly the `Typeclasses`
--  chapter's partial-map update on `Γ` — but its surface
--  syntax has to be our own, because inside these brackets
--  all three positions are in object syntax. Writing the
--  map notation directly would mean writing the binding as
--  `"x" →ₚ <{ Bool → Bool }> ; Γ`: the name quoted, and the
--  type escaped back out of the brackets it belongs in. The
--  grammar hides those two encoding details, and nothing
--  else.

declare_syntax_cat stlcCtx
syntax:max "∅" : stlcCtx
syntax:max "~" term:max : stlcCtx
syntax:max stlcVar " ↦ " stlcTy " ; " stlcCtx : stlcCtx

syntax:max (name := judgeBracket) "<{ " stlcCtx " ⊢ " stlcTm " ⦂ " stlcTy " }>" : term

open Lean in
/-- The `Context` denoted by a context expression. -/
partial def ctxTerm (G : TSyntax `stlcCtx) : MacroM Term :=
  match G with
  | `(stlcCtx| ∅)   => `((∅ : Context))
  | `(stlcCtx| ~$e) => pure e
  | `(stlcCtx| $x:stlcVar ↦ $T:stlcTy ; $G:stlcCtx) => do
      `(PartialMap.update $(← ctxTerm G) $(← varStr x) <{ $T:stlcTy }>)
  | _ => Macro.throwUnsupported

--  As with `subst`, the judgment notation is used inside
--  the definition it names, so it is introduced in two
--  steps: the rule below is declared `local` with hygiene
--  off, so the `HasType` in its expansion resolves to the
--  relation being declared, and after the `section` closes
--  it is declared again for real use.

section
set_option hygiene false in
local macro_rules (kind := judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $T:stlcTy }>)
--  END DETAILS

inductive HasType : Context → Tm → Ty → Prop where
  | var (Γ : Context) (x : String) (T₁ : Ty) (h : Γ[x] = some T₁) :
      <{ ~Γ ⊢ ~(Tm.var x) ⦂ ~T₁ }>
  | abs (Γ : Context) (x : String) (T₁ T₂ : Ty) (t₁ : Tm)
      (h : <{ ~x ↦ ~T₂ ; ~Γ ⊢ ~t₁ ⦂ ~T₁ }>) :
      <{ ~Γ ⊢ λ ~x : ~T₂ . ~t₁ ⦂ ~T₂ → ~T₁ }>
  | app (Γ : Context) (T₁ T₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ ~T₂ → ~T₁ }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~T₂ }>) :
      <{ ~Γ ⊢ ~t₁ ~t₂ ⦂ ~T₁ }>
  | tru (Γ : Context) :
      <{ ~Γ ⊢ true ⦂ Bool }>
  | fls (Γ : Context) :
      <{ ~Γ ⊢ false ⦂ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (T₁ : Ty)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Bool }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~T₁ }>)
      (h₃ : <{ ~Γ ⊢ ~t₃ ⦂ ~T₁ }>) :
      <{ ~Γ ⊢ if ~t₁ then ~t₂ else ~t₃ ⦂ ~T₁ }>

attribute [StlcTyping] HasType.var HasType.abs HasType.app HasType.tru HasType.fls HasType.ite

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: the judgment, for real)
--  Closing the `section` retires the hygiene-free rule; the
--  same rule is then declared again, hygienically, for
--  every later use.

end

macro_rules (kind := judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $T:stlcTy }>)
--  END DETAILS

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing judgments back)
--  As with terms, a judgment prints back in its own
--  notation, so that a goal reads as
--  `<{ x ↦ Bool ; ∅ ⊢ x ⦂ Bool }>` rather than as a
--  `HasType` applied to a chain of map updates.

open Lean PrettyPrinter in
/-- Rebuild `stlcCtx` syntax from the term syntax of a `Context`, so that a
context prints as `x ↦ Bool ; Γ` rather than as a chain of map updates. -/
partial def unexpandCtx : Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₚ $T) => do
      unexpandCtx (← `($x →ₚ $T ; ∅))
  | `($x:str →ₚ $T ; $G) => do
      let G' ← unexpandCtx G
      let x' : TSyntax `stlcVar ←
        if isPlainName x.getString then
          `(stlcVar| $(mkIdent (Name.mkSimple x.getString)):ident)
        else `(stlcVar| ~$x)
      match T with
      | `(<{ $T':stlcTy }>) => `(stlcCtx| $x':stlcVar ↦ $T' ; $G')
      | _                   => `(stlcCtx| $x':stlcVar ↦ ~($T) ; $G')
  | G => `(stlcCtx| ~($G))

open Lean PrettyPrinter in
@[app_unexpander Stlc.HasType]
def HasType.unexpand : Unexpander
  | `($_ $G <{ $t:stlcTm }> <{ $T:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ $T }>)
  | `($_ $G <{ $t:stlcTm }> $T) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ ~($T) }>)
  | `($_ $G $t <{ $T:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ $T }>)
  | `($_ $G $t $T) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ ~($T) }>)
  | _ => throw ()
--  END DETAILS

--  ### Examples

example : <{ ∅ ⊢ λ x : Bool . x ⦂ Bool → Bool }> := by
  apply HasType.abs
  apply HasType.var; rfl

--  The derivation is small enough to write out directly: an
--  abstraction rule whose premise is the variable rule, and
--  the variable rule's premise — that the extended context
--  maps `x` to `Bool` — holds by computation, hence `rfl`.

--  Much like reduction sequences, long derivations of
--  typing rules can grow quite tedious to prove. Luckily,
--  we can have Lean automate proofs of this sort, using
--  another tactic: `apply_rules`. This tactic works much
--  like `normalize`, but is more efficient and will make
--  progress even if it cannot solve the goal outright. Like
--  `normalize`, `apply_rules` also takes a `using` argument
--  which tells Lean which set of constructors to draw from.
--
--      ∅ ⊢ λx:Bool. λy:Bool → Bool. y (y x)
--            ⦂ Bool → (Bool → Bool) → Bool.

example :
    <{ ∅ ⊢ λ x : Bool . λ y : Bool → Bool . y (y x) ⦂
       Bool → (Bool → Bool) → Bool }> := by
  apply_rules using StlcTyping

--  It's worth noting that `apply_rules` relies on an
--  important property of our typing rules - namely, that
--  they are *syntax directed*. A syntax directed judgment
--  is one where the syntax of a term completely determines
--  which rule can be applied at any given time; only one
--  rule can be applied to each term. This is important
--  because `apply_rules` just applies the first rule in its
--  set of constructors or lemmas that it can - it doesn't
--  backtrack if that rule isn't correct. So, making sure
--  that only one rule can apply to any given term is
--  important to ensure that `apply_rules` always discovers
--  a valid derivation, if one exists.

--  We can also show that some terms are *not* typable. For
--  example, we can check that there is no typing derivation
--  assigning a type to the term `λx:Bool. λy:Bool. x y` —
--  i.e.,
--
--      ¬ ∃ T, ∅ ⊢ λx:Bool. λy:Bool. x y ⦂ T

example : ¬ ∃ T, <{ ∅ ⊢ λ x : Bool . λ y : Bool . x y ⦂ ~T }> := by
  intro ⟨T, hc⟩
  -- Each `cases` peels off one rule of the derivation, naming the premise it
  -- leaves behind; the context stays small because the old hypothesis goes away.
  cases hc with
  | abs _ _ _ _ _ h₁ =>
    cases h₁ with
    | abs _ _ _ _ _ h₂ =>
      cases h₂ with
      | app _ _ _ _ _ hf _ =>
        cases hf with
        | var _ _ _ hx =>
          -- `x` is bound to `Bool` in the context, but the application rule
          -- needs it to have an arrow type.
          exact Ty.noConfusion (Option.some.inj hx)

--  Another nonexample:
--
--      ¬ ∃ S T, ∅ ⊢ λx:S. x x ⦂ T

--   ----------------------------------------

--  _Quiz:_

--  Which of the following propositions is *not* provable?
--
--  (A) `y ↦ Bool ; ∅ ⊢ λx:Bool. x ⦂ Bool → Bool`
--
--  (B) `∃ T,  ∅ ⊢ λy:Bool → Bool. λx:Bool. y x ⦂ T`
--
--  (C) `∃ T,  ∅ ⊢ λy:Bool → Bool. λx:Bool. x y ⦂ T`
--
--  (D)
--  `∃ S, x ↦ S ; ∅ ⊢ λy:Bool → Bool. y x ⦂ (Bool → Bool) → S`

--   ----------------------------------------

--  _Quiz:_

--  Which of these is not provable?
--
--  (A) `∃ T,  ∅ ⊢ λy:Bool → Bool → Bool. λx:Bool. y x ⦂ T`
--
--  (B) `∃ S T, x ↦ S ; ∅ ⊢ x x x ⦂ T`
--
--  (C) `∃ S U T, x ↦ S ; y ↦ U ; ∅ ⊢ λz:Bool. x (y z) ⦂ T`
--
--  (D) `∃ S T, x ↦ S ; ∅ ⊢ λy:Bool. x (x y) ⦂ T`

--   ----------------------------------------

end Stlc

-- Built on 2026-09-04 18:45 UTC

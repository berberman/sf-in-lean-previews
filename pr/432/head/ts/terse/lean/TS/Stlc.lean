import TS.StlcCommon
import TS.Smallstep

import SFLCompat

--  # Stlc: The Simply Typed Lambda-Calculus

--  Our job for this chapter: Formalize a small *functional*
--  language and its type system.
--
--  Language: The *simply typed lambda-calculus* (STLC).
--  - A small subset of Lean's built-in functional
--    language...
--  - ...but we'll use different concrete syntax (to avoid
--    confusion, and for consistency with standard
--    treatments)
--
--  Main new technical challenges:
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
--  *dependent types* like `∀ n m : Nat, n = m`.
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
--  Informal grammar for terms (where `x` and `t` stand for
--  arbitrary variables and terms):

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
--  - `λx:Bool. x` has type `Bool → Bool`
--  - `(λx:Bool. x) true` has type `Bool`
--  - `λx:Bool. if x then false else true` has type
--    `Bool → Bool`
--  - `λx:Bool. true` has type `Bool → Bool`
--  - `λx:Bool. λy:Bool. x` has type `Bool → Bool → Bool`
--    (i.e., `Bool → (Bool → Bool)`)
--  - `(λx:Bool. λy:Bool. x) false true` has type `Bool`
--
--  The last two, higher-order examples are left off the
--  list on purpose — working out their types is the subject
--  of the quizzes that follow.
--
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
  | arrow (τ₁ τ₂ : Ty)

--  ### Terms

inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (τ : Ty) (t : Tm)
  | tru
  | fls
  | ite (c t e : Tm)

--  The constructors above give us a precise representation
--  of STLC syntax, but expressions written directly with
--  them quickly become hard to read. We need some notation
--  magic to set up the concrete syntax, as we did in the
--  Types chapter...
--
--  We will write STLC syntax inside `<{ ... }>` brackets.
--  For example, `<{ λ X : Bool . X }>` represents the term
--  `Tm.abs "X" Ty.bool (Tm.var "X")`.
--
--  We write STLC syntax inside `<{ ... }>` brackets.
--  Capital Latin names are literal STLC names. Lowercase
--  and Greek names refer to Lean variables in the
--  surrounding proof. Larger Lean expressions are inserted
--  with `~`.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding)
syntax:50 "if " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

namespace Elab

open StlcCommon
open Lean Meta Elab Term

def language : Language where
  tyType := ``Ty
  tmType := ``Tm
  arrowCtor := ``Ty.arrow
  varCtor := ``Tm.var
  appCtor := ``Tm.app
  absCtor := ``Tm.abs

  -- defined later
  subst := `Stlc.subst
  hasType := `Stlc.HasType

def boolTyHandler : TyElabHandler :=
  fun _recur k T => do
    match T with
    | `(stlcTy| Bool) =>
        return mkConst ``Ty.bool
    | _ => k T

def tyHandlers : TyElabHandler :=
  boolTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy <| unsupportedTy language

def boolTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| true) => do
        return (mkConst ``Tm.tru, free)
    | `(stlcTm| false) => do
        return (mkConst ``Tm.fls, free)
    | `(stlcTm| Bool) => do
        throwError "`Bool` is not a valid term."
    | `(stlcTm| if $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite) c t e, free)
    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  boolTmHandler.orElse (commonTmHandler language elabTy)

partial def elabTm : TmElab :=
  tmHandlers elabTm unsupportedTm

def elabCtx : CtxElab := elabCtxCommon language elabTy

@[scoped term_elab StlcCommon.bracket]
def elabBracket : TermElab :=
  fun stx expectedType? => do
    let `(<{ $q:stlcQuoted }>) := stx
      | throwUnsupportedSyntax
    elabQuoted language elabTy elabTm elabCtx q expectedType?

end Elab

open scoped Elab

namespace Delab

open StlcCommon Delab
open Lean PrettyPrinter Delaborator

@[app_unexpander Ty.bool]
private def Ty.unexpandBool : Unexpander
  | _ => do
    let T ← `(stlcTy| $(mkIdent `Bool):ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Tm.tru]
private def Tm.unexpandTru : Unexpander
  | _ => do
    let t ← `(stlcTm| $(mkIdent `true):ident)
    `(<{ $t:stlcTm }>)

@[app_unexpander Tm.fls]
private def Tm.unexpandFls : Unexpander
  | _ => do
    let t ← `(stlcTm| $(mkIdent `false):ident)
    `(<{ $t:stlcTm }>)

private def reservedNames : String → Bool
  | "true" | "false" | "Bool" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.ite]
private def Tm.unexpandIte : Unexpander
  | `($_ $c $t $e) =>
      `(<{ if $(getTm c) then $(getTm t) else $(getTm e) }>)
  | _ => throw ()

end Delab
--  END DETAILS

--  Here are the terms we will use as running examples,
--  written in the new notation:

abbrev idB := <{ λ X : Bool . X }>

abbrev idBB := <{ λ X : Bool → Bool . X }>

abbrev idBBBB := <{ λ X : (Bool → Bool) → (Bool → Bool) . X }>

abbrev k := <{ λ X : Bool . λ Y : Bool . X }>

abbrev notB := <{ λ X : Bool . if X then false else true }>

--  Note that an abstraction `λ x : T . t` (formally,
--  `Tm.abs` applied to `x`, `T`, and `t`) is always
--  annotated with the type `T` of its parameter, in
--  contrast to Lean (and other functional languages like
--  ML, Haskell, etc.), which use type inference to fill in
--  missing annotations. We're not considering type
--  inference at all here.

--  ## Operational Semantics

--  To define the small-step semantics of STLC terms...
--  - We begin by defining the set of values.
--  - Next, we define *free variables* and *substitution*.
--    These are used in the reduction rule for application
--    expressions.
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
--  - We can say that `λx:T. t` is a value only when `t` is
--    a value — i.e., only if the function's body has been
--    reduced (as much as it can be without knowing what
--    argument it is going to be applied to).
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
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) : IsValue <{ λ x : τ₂ . t₁ }>
  | tru : IsValue <{ true }>
  | fls : IsValue <{ false }>

attribute [StlcEval] Tm.IsValue.abs Tm.IsValue.tru Tm.IsValue.fls

theorem idB_value : Tm.IsValue idB := .abs ..
theorem idBB_value : Tm.IsValue idBB := .abs ..
theorem notB_value : Tm.IsValue notB := .abs ..

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
--      (λX:Bool. if X then true else X) false
--
--  to
--
--      if false then true else false
--
--  by substituting `false` for the parameter `X` in the
--  body of the function.
--
--  In general, we need to be able to substitute some given
--  term `s` for occurrences of some variable `x` in another
--  term `t`. Informally, this is written `[x:=s]t` and
--  pronounced "substitute `s` for `x` in `t`."

--  Here are some examples:
--  - `[X:=true] (if X then true else false)` yields
--    `if true then true else false`
--  - `[X:=true] X` yields `true`
--  - `[X:=true] (if X then X else Y)` yields
--    `if true then true else Y`
--  - `[X:=true] Y` yields `Y`
--  - `[X:=true] false` yields `false` (vacuous
--    substitution)
--  - `[X:=true] (λY:Bool. if Y then X else false)` yields
--    `λY:Bool. if Y then true else false`
--  - `[X:=true] (λY:Bool. X)` yields `λY:Bool. true`
--  - `[X:=true] (λY:Bool. Y)` yields `λY:Bool. Y`
--  - `[X:=true] (λX:Bool. X)` yields `λX:Bool. X`
--
--  The last example is illuminating: substituting `X` with
--  `true` in `λX:Bool. X` does *not* yield `λX:Bool. true`!
--  The reason for this is that the `X` in the body of
--  `λX:Bool. X` is *bound* by the abstraction: it is a new,
--  local name that just happens to be spelled the same as
--  some global name `X`.

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

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ y : τ . [x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([x := s] t₁) ([x := s] t₂) }>
  | .tru => .tru
  | .fls => .fls
  | .ite t₁ t₂ t₃ =>
      <{ if [x := s] t₁ then [x := s] t₂ else [x := s] t₃ }>

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding)
open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst
--  END DETAILS

variable (x y : String) (s t t₁ t₂ t₃ : Tm) (τ : Ty)

@[simp] theorem subst_var_eq : <{ [x := s] ~(Tm.var x) }> = s := by
  simp [subst]

@[simp] theorem subst_var_ne (h : x ≠ y) : <{ [x := s] ~(Tm.var y) }> = .var y := by
  simp [subst, h]

@[simp] theorem subst_abs_eq : <{ [x := s] (λ x : τ . t) }> = <{ λ x : τ . t }> := by
  simp [subst]

@[simp] theorem subst_abs_ne (h : x ≠ y) :
    <{ [x := s] (λ y : τ . t) }> = <{ λ y : τ . [x := s] t }> := by
  simp [subst, h]

@[simp] theorem subst_app :
    <{ [x := s] (t₁ t₂) }> = <{ ([x := s] t₁) ([x := s] t₂) }> := rfl

@[simp] theorem subst_tru : <{ [x := s] true }> = <{ true }> := rfl

@[simp] theorem subst_fls : <{ [x := s] false }> = <{ false }> := rfl

@[simp] theorem subst_ite :
    <{ [x := s] (if t₁ then t₂ else t₃) }> =
      <{ if [x := s] t₁ then [x := s] t₂ else [x := s] t₃ }> := rfl

--   ----------------------------------------

--  _Quiz:_

--  What is the result of the following substitution?
--
--      [X:=s](λY:T₁. X (λX:T₂. X))
--
--  (1) `(λY:T₁. X (λX:T₂. X))`
--
--  (2) `(λY:T₁. s (λX:T₂. s))`
--
--  (3) `(λY:T₁. s (λX:T₂. X))`
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
--      s = λX:Bool. R
--
--  (where `R` is a *free* reference to some global
--  resource) for the free variable `Z` in the term
--
--      t = λR:Bool. Z
--
--  where `R` is a bound variable, we would get
--
--      λR:Bool. λX:Bool. R
--
--  where the free reference to `R` in `s` has been
--  "captured" by the binder at the beginning of `t`.

--  Why would this be bad? Because it violates the principle
--  that the names of bound variables do not matter. For
--  example, if we rename the bound variable in `t`, e.g.,
--  let
--
--      t' = λW:Bool. Z
--
--  then `[Z:=s]t'` is
--
--      λW:Bool. λX:Bool. R
--
--  which does not behave the same as the substituting in
--  the original `t`:
--
--      [Z:=s]t = λR:Bool. λX:Bool. R
--
--  That is, renaming a bound variable in `t` would change
--  how `t` behaves under our simple substitution. So
--  substitution gets more complicated in that setting, but
--  fortunately we don't have that problem in our STLC
--  variant.

--  Fortunately, since we are only interested here in
--  defining the `step` relation on *closed* terms (i.e.,
--  terms like `λX:Bool. X` that include binders for all of
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
--
--  The `appAbs` rule is often called *beta-reduction*.
--
--  This is *call by value* reduction: to reduce an
--  application `(t₁ t₂)`, we
--  - first reduce `t₁` to a value: a function `λx:T. t`
--  - then reduce the argument `t₂` to a value `v`
--  - then reduce the application itself by substituting `v`
--    for the bound variable `x` in the body `t`.

section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
  | appAbs (x : String) (τ : Ty) (t v : Tm) (hv : v.IsValue) :
      <{ (λ x : τ . t) v }> ⟶ <{ [x := v] t }>
  | app1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ t₁ t₂ }> ⟶ <{ t₁' t₂ }>
  | app2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ v₁ t₂ }> ⟶ <{ v₁ t₂' }>
  | ifTrue (t₁ t₂ : Tm) :
      <{ if true then t₁ else t₂ }> ⟶ t₁
  | ifFalse (t₁ t₂ : Tm) :
      <{ if false then t₁ else t₂ }> ⟶ t₂
  | ifStep (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if t₁ then t₂ else t₃ }> ⟶ <{ if t₁' then t₂ else t₃ }>
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

-- for later use with `normalize`
attribute [StlcEval] Step.appAbs Step.app1 Step.app2 Step.ifTrue Step.ifFalse Step.ifStep

--   ----------------------------------------

--  _Quiz:_

--  What does the following term step to?
--
--      (λX:Bool → Bool. X) (λX:Bool. X) ⟶ ???
--
--  (A) `λX:Bool. X`
--
--  (B) `λX:Bool → Bool. X`
--
--  (C) `(λX:Bool → Bool. X) (λX:Bool. X)`
--
--  (D) none of the above

--   ----------------------------------------

--  _Quiz:_

--  What does the following term step to?
--
--      (λX:Bool → Bool. X)
--          ((λX:Bool → Bool. X) (λX:Bool. X))
--      ⟶ ???
--
--  (A) `λX:Bool. X`
--
--  (B) `λX:Bool → Bool. X`
--
--  (C) `(λX:Bool → Bool. X) (λX:Bool. X)`
--
--  (D)
--  `(λX:Bool → Bool. X) ((λX:Bool → Bool. X) (λX:Bool. X))`
--
--  (E) none of the above

--   ----------------------------------------

--  _Quiz:_

--  What does the following term *normalize* to?
--
--      (λX:Bool → Bool. X) notB true  ⟶* ???
--
--  where `notB` abbreviates
--  `λX:Bool. if X then false else true`
--
--  (A) `λX:Bool. X`
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
--      (λX:Bool. X) (notB true) ⟶* ???
--
--  (A) `λX:Bool. X`
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
--      (λX:Bool → Bool. X) (λX:Bool. X) ⟶* λX:Bool. X
--
--  i.e.,
--
--      idBB idB ⟶* idB

example : <{ idBB idB }> ⟶* idB := by
  apply Multi.step (y := idB)
  · exact .appAbs "X" <{ Bool → Bool }> <{ X }> idB idB_value
  · rfl

--  Example:
--
--      (λX:Bool → Bool. X) ((λX:Bool → Bool. X) (λX:Bool. X))
--            ⟶* λX:Bool. X
--
--  i.e.,
--
--      (idBB (idBB idB)) ⟶* idB.

example : <{ idBB (idBB idB) }> ⟶* idB := by
  -- the same reduction happens twice, so we name it
  have step₁ : <{ idBB idB }> ⟶ idB := by
    exact .appAbs "X" <{ Bool → Bool }> <{ X }> idB idB_value
  apply Multi.step (y := <{ idBB idB }>)
  · exact .app2 idBB <{ idBB idB }> idB idBB_value step₁
  apply Multi.step (y := idB)
  · exact step₁
  · rfl

--  Example:
--
--      (λX:Bool → Bool. X)
--         (λX:Bool. if X then false else true)
--         true
--            ⟶* false
--
--  i.e.,
--
--      (idBB notB) true ⟶* false.

example : <{ idBB notB true }> ⟶* <{ false }> := by
  apply Multi.step (y := <{ notB true }>)
  · exact .app1 <{ idBB notB }> notB <{ true }>
      (.appAbs "X" <{ Bool → Bool }> <{ X }> notB notB_value)
  apply Multi.step (y := <{ if true then false else true }>)
  · exact .appAbs "X" <{ Bool }> <{ if X then false else true }> <{ true }> .tru
  apply Multi.step (y := <{ false }>)
  · exact .ifTrue <{ false }> <{ true }>
  · rfl

--  Example:
--
--      (λX:Bool → Bool. X)
--         ((λX:Bool. if X then false else true) true)
--            ⟶* false
--
--  i.e.,
--
--      idBB (notB true) ⟶* false.
--
--  (Note that this term doesn't actually typecheck; even
--  so, we can ask how it reduces.)

example : <{ idBB (notB true) }> ⟶* <{ false }> := by
  apply Multi.step (y := <{ idBB (if true then false else true) }>)
  · exact .app2 idBB <{ notB true }> <{ if true then false else true }> idBB_value
      (.appAbs "X" <{ Bool }> <{ if X then false else true }> <{ true }> .tru)
  apply Multi.step (y := <{ idBB false }>)
  · exact .app2 idBB <{ if true then false else true }> <{ false }> idBB_value
      (.ifTrue <{ false }> <{ true }>)
  apply Multi.step (y := <{ false }>)
  · exact .appAbs "X" <{ Bool → Bool }> <{ X }> <{ false }> .fls
  · rfl

--  As in the Smallstep chapter, we can use the `normalize`
--  tactic to simplify these proofs:

example : <{ idBB idB }> ⟶* idB := by
  normalize using StlcEval

example : <{ idBB (idBB idB) }> ⟶* idB := by
  normalize using StlcEval

example : <{ idBB notB true }> ⟶* <{ false }> := by
  normalize using StlcEval

example : <{ idBB (notB true) }> ⟶* <{ false }> := by
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

--  *Question*: What is the type of the term "`X Y`"?
--
--  *Answer*: It depends on the types of `X` and `Y`!
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

--  Γ x = τ₁
--                              ------------                       (var)
--                               Γ ⊢ x ⦂ τ₁
--
--                          x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁
--                        -------------------------                (abs)
--                         Γ ⊢ λx:τ₂. t₁ ⦂ τ₂ → τ₁
--
--                            Γ ⊢ t₁ ⦂ τ₂ → τ₁
--                              Γ ⊢ t₂ ⦂ τ₂
--                           ------------------                    (app)
--                             Γ ⊢ t₁ t₂ ⦂ τ₁
--
--                            -----------------                    (tru)
--                             Γ ⊢ true ⦂ Bool
--
--                           ------------------                    (fls)
--                            Γ ⊢ false ⦂ Bool
--
--               Γ ⊢ t₁ ⦂ Bool    Γ ⊢ t₂ ⦂ τ₁    Γ ⊢ t₃ ⦂ τ₁
--              ---------------------------------------------      (ite)
--                     Γ ⊢ if t₁ then t₂ else t₃ ⦂ τ₁

--  We can read the three-place relation `Γ ⊢ t ⦂ T` as:
--  "under the assumptions in Γ, the term `t` has the type
--  `T`."
--
--  In the formal development, we write this judgment inside
--  the same `<{ .. }>` brackets.

inductive HasType : Context → Tm → Ty → Prop where
  | var (Γ : Context) (x : String) (τ₁ : Ty)
      (h : Γ[x] = some τ₁) :
      <{ Γ ⊢ ~(Tm.var x) ⦂ τ₁ }>
  | abs (Γ : Context) (x : String)
      (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ ⊢ λ x : τ₂ . t₁ ⦂ τ₂ → τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty)
      (t₁ t₂ : Tm)
      (h₁ : <{ Γ ⊢ t₁ ⦂ τ₂ → τ₁ }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ ⊢ t₁ t₂ ⦂ τ₁ }>
  | tru (Γ : Context) :
       <{ Γ ⊢ true ⦂ Bool }>
  | fls (Γ : Context) :
       <{ Γ ⊢ false ⦂ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (τ₁ : Ty)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Bool }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ τ₁ }>)
      (h₃ : <{ Γ ⊢ t₃ ⦂ τ₁ }>) :
      <{ Γ ⊢ if t₁ then t₂ else t₃ ⦂ τ₁ }>


attribute [StlcTyping] HasType.var HasType.abs HasType.app HasType.tru HasType.fls HasType.ite

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding)
open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander := StlcCommon.Delab.unexpandHasType
--  END DETAILS

--  ### Examples

example : <{ ∅ ⊢ λ X : Bool . X ⦂ Bool → Bool }> := by
  apply HasType.abs
  apply HasType.var; rfl

--  The derivation is small enough to write out directly: an
--  abstraction rule whose premise is the variable rule, and
--  the variable rule's premise — that the extended context
--  maps `X` to `Bool` — holds by computation, hence `rfl`.

--  Much like reduction sequences, long derivations of
--  typing rules can grow quite tedious to prove. Luckily,
--  we can have Lean automate proofs of this sort, using
--  another tactic: `apply_rules`. This tactic works much
--  like `normalize`, but is more efficient and will make
--  progress even if it cannot solve the goal outright. Like
--  `normalize`, `apply_rules` also takes a `using` argument
--  which tells Lean which set of constructors to draw from.
--
--      ∅ ⊢ λX:Bool. λY:Bool → Bool. Y (Y X)
--            ⦂ Bool → (Bool → Bool) → Bool.

example :
    <{ ∅ ⊢ λ X : Bool . λ Y : Bool → Bool . Y (Y X) ⦂
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
--  assigning a type to the term `λX:Bool. λY:Bool. X Y` —
--  i.e.,
--
--      ¬ ∃ τ, ∅ ⊢ λX:Bool. λY:Bool. X Y ⦂ τ

example : ¬ ∃ τ, <{ ∅ ⊢ λ X : Bool . λ Y : Bool . X Y ⦂ τ }> := by
  intro ⟨τ, hc⟩
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
          -- `X` is bound to `Bool` in the context, but the application rule
          -- needs it to have an arrow type.
          exact Ty.noConfusion (Option.some.inj hx)

--  Another nonexample:
--
--      ¬ ∃ σ τ, ∅ ⊢ λX:σ. X X ⦂ τ

--   ----------------------------------------

--  _Quiz:_

--  Which of the following propositions is *not* provable?
--
--  (A) `Y ↦ Bool ; ∅ ⊢ λX:Bool. X ⦂ Bool → Bool`
--
--  (B) `∃ τ,  ∅ ⊢ λY:Bool → Bool. λX:Bool. Y X ⦂ τ`
--
--  (C) `∃ τ,  ∅ ⊢ λY:Bool → Bool. λX:Bool. X Y ⦂ τ`
--
--  (D)
--  `∃ σ, X ↦ σ ; ∅ ⊢ λY:Bool → Bool. Y X ⦂ (Bool → Bool) → σ`

--   ----------------------------------------

--  _Quiz:_

--  Which of these is not provable?
--
--  (A) `∃ τ,  ∅ ⊢ λY:Bool → Bool → Bool. λX:Bool. Y X ⦂ τ`
--
--  (B) `∃ σ τ, X ↦ σ ; ∅ ⊢ X X X ⦂ τ`
--
--  (C) `∃ σ υ τ, X ↦ σ ; Y ↦ υ ; ∅ ⊢ λZ:Bool. X (Y Z) ⦂ τ`
--
--  (D) `∃ σ τ, X ↦ σ ; ∅ ⊢ λY:Bool. X (X Y) ⦂ τ`

--   ----------------------------------------

end Stlc

-- Source revision: d629cf5, committed 2026-10-05 22:04 UTC

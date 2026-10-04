import TS.Stlc
import LF.CustomTactics
import LF.Typeclasses

import SFLCompat

--  # Sub: Subtyping

--  ## Concepts

--  ### A Motivating Example

--  Suppose we are writing a program involving two record
--  types defined as follows:
--
--            Person  = {name:String, age:Nat}
--            Student = {name:String, age:Nat, gpa:Nat}
--
--  *Problem*: In the pure STLC with records, the following
--  term is not typable:
--
--          (λR:Person. (R.age)+1) {name="Pat",age=21,gpa=1}
--
--  This is a shame.
--
--  *Idea*: Introduce *subtyping*, formalizing the
--  observation that "some types are better than others."
--
--  Safe substitution principle:
--  - `σ` is a subtype of `τ`, written `σ <: τ`, if a value
--    of type `σ` can safely be used in any context where a
--    value of type `τ` is expected.

--  ### Subtyping and Object-Oriented Languages

--  Subtyping plays a fundamental role in OO programming
--  languages.
--
--  Roughly, an *object* can be thought of as a record of
--  functions ("methods") and data values ("fields" or
--  "instance variables").
--  - Invoking a method `m` of an object `o` on some
--    arguments `a₁..an` consists of projecting out the `m`
--    field of `o` and applying it to `a₁..an`.
--
--  The type of an object is a *class* (or an *interface*).
--
--  Classes are related by the *subclass* relation.
--  - An object belonging to a subclass must provide all the
--    methods and fields of one belonging to a superclass,
--    plus possibly some more.
--  - Thus a subclass object can be used anywhere a
--    superclass object is expected.
--  - Very handy for organizing large libraries
--
--  "Of course, real OO languages have lots of other
--  features...
--  - mutable fields
--  - "private" and other visibility modifiers
--  - method inheritance
--  - static components
--  - etc., etc.
--
--  We'll ignore all these and focus on core mechanisms.

--  ### The Subsumption Rule

--  τ₂ Our goal for this chapter is to add subtyping to the
--  simply typed lambda-calculus (with some basic
--  extensions). This involves two steps:
--  - Defining a binary *subtype relation* between types.
--  - Enriching the typing relation to take subtyping into
--    account.
--
--  The second step is actually very simple. We add just a
--  single rule to the typing relation: the so-called *rule
--  of subsumption*:
--
--                               Γ ⊢ t₁ ⦂ τ₁     τ₁ <: τ₂
--                               --------------------------           (sub)
--                                     Γ ⊢ t₁ ⦂ τ₂
--
--  This rule says, intuitively, that it is OK to "forget"
--  some of what we know about a term.

--  ### The Subtype Relation

--  The first step -- the definition of the relation
--  `σ <: τ` -- is where all the action is. Let's look at
--  each of the clauses of its definition.

--  #### Structural Rules

--  To start off, we impose two "structural rules" that are
--  independent of any particular type constructor: a rule
--  of *transitivity*, which says intuitively that, if `σ`
--  is better (richer, safer) than `υ` and `υ` is better
--  than `τ`, then `σ` is better than `τ`...
--
--                                    σ <: υ    υ <: τ
--                                    ----------------                        (trans)
--                                         σ <: τ
--
--  ... and a rule of *reflexivity*, since certainly any
--  type `τ` is as good as itself:
--
--                                         ------                              (refl)
--                                         τ <: τ

--  #### Products

--  Now we consider the individual type constructors, one by
--  one, beginning with product types. We consider one pair
--  to be a subtype of another if each of its components is.
--
--                                  σ₁ <: τ₁    σ₂ <: τ₂
--                                  --------------------                        (prod)
--                                   σ₁ × σ₂ <: τ₁ × τ₂
--
--  Suppose we have functions `F` and `G` with these types:
--
--          F : C → Student
--          G : (C→Person) → D
--
--  Is it safe to allow the application `G F`?
--
--  Yes.
--
--  So we want:
--
--            C→Student  <:  C→Person
--
--  I.e., arrow is *covariant* in its right-hand argument.
--
--  Now suppose we have:
--
--             F : Person → C
--             G : (Student→C) → D
--
--  Is it safe to allow the application `G F`?
--
--  Again yes.
--
--  So we want:
--
--            Person → C  <:  Student → C
--
--  I.e., arrow is *contravariant* in its left-hand
--  argument.
--
--  Putting these together...
--
--                                  τ₁ <: σ₁    σ₂ <: τ₂
--                                  --------------------                      (arrow)
--                                  σ₁ → σ₂ <: τ₁ → τ₂

--   ----------------------------------------

--  _Quiz:_

--  Suppose we have `σ <: τ` and `υ <: δ`. Which of the
--  following subtyping assertions is *false*?
--
--  (A) `σ×υ <: τ×δ`
--
--  (B) `τ→υ <: σ→υ`
--
--  (C) `(σ→υ) → (σ×δ)  <:  (σ→υ) → (τ×υ)`
--
--  (D) `(τ×υ) → δ  <:  (σ×υ) → δ`
--
--  (E) `σ→υ <: σ→δ`

--   ----------------------------------------

--  _Quiz:_

--  Suppose again that we have `σ <: τ` and `υ <: δ`. Which
--  of the following is incorrect?
--
--  (A) `(τ→τ)×υ  <: (σ→τ)×δ`
--
--  (B) `τ→υ <: σ→δ`
--
--  (C) `(σ→υ) → (σ→δ)  <:  (τ→υ) → (τ→δ)`
--
--  (D) `(σ→δ) → δ  <:  (τ→υ) → δ`
--
--  (E) `σ → (δ→υ) <: σ → (υ→υ)`

--   ----------------------------------------

--  #### Records

--  What about subtyping for record types?
--
--  The basic intuition is that it is always safe to use a
--  "bigger" record in place of a "smaller" one. That is,
--  given a record type, adding extra fields will always
--  result in a subtype. If some code is expecting a record
--  with fields `x` and `y`, it is perfectly safe for it to
--  receive a record with fields `x`, `y`, and `z`; the `z`
--  field will simply be ignored. For example,
--
--          {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}
--          {name:String, age:Nat} <: {name:String}
--          {name:String} <: {}
--
--  This is known as "width subtyping" for records.
--
--  We can also create a subtype of a record type by
--  replacing the type of one of its fields with a subtype.
--  If some code is expecting a record with a field `x` of
--  type `τ`, it will be happy with a record having a field
--  `x` of type `σ` as long as `σ` is a subtype of `τ`. For
--  example,
--
--          {x:Student} <: {x:Person}
--
--  This is known as "depth subtyping".
--
--  Finally, although the fields of a record type are
--  written in a particular order, the order does not really
--  matter. For example,
--
--          {name:String,age:Nat} <: {age:Nat,name:String}
--
--  This is known as "permutation subtyping".
--
--  We *could* formalize these requirements in a single
--  subtyping rule for records as follows:
--
--                              ∀ jₖ in j₁..jₙ,
--                          ∃ iₚ in i₁..iₘ, such that
--                              jₖ=iₚ and σₚ <: τₖ
--                        ----------------------------------                    (rcd)
--                        {i₁:σ₁...iₘ:σₘ} <: {j₁:τ₁...jₙ:τₙ}
--
--  That is, the record on the left should have all the
--  field labels of the one on the right (and possibly
--  more), while the types of the common fields should be in
--  the subtype relation.
--
--  However, this rule is rather heavy and hard to read, so
--  it is often decomposed into three simpler rules, which
--  can be combined using `trans` to achieve all the same
--  effects.
--
--  First, adding fields to the end of a record type gives a
--  subtype:
--
--                                     n > m
--                       ---------------------------------                 (rcdWidth)
--                       {i₁:τ₁...iₙ:τₙ} <: {i₁:τ₁...iₘ:τₘ}
--
--  We can use `rcdWidth` to drop later fields of a
--  multi-field record while keeping earlier fields, showing
--  for example that `{age:Nat,name:String} <: {age:Nat}`.
--
--  Second, subtyping can be applied inside the components
--  of a compound record type:
--
--                             σ₁ <: τ₁  ...  σₙ <: τₙ
--                        ----------------------------------               (rcdDepth)
--                        {i₁:σ₁...iₙ:σₙ} <: {i₁:τ₁...iₙ:τₙ}
--
--  For example, we can use `rcdDepth` and `rcdWidth`
--  together to show that
--  `{y:Student, x:Nat} <: {y:Person}`.
--
--  Third, subtyping can reorder fields. For example, we
--  want `{name:String, gpa:Nat, age:Nat} <: Person`, but we
--  haven't quite achieved this yet: using just `rcdDepth`
--  and `rcdWidth` we can only drop fields from the *end* of
--  a record type. So we add:
--
--               {i₁:σ₁...iₙ:σₙ} is a permutation of {j₁:τ₁...jₙ:τₙ}
--               ---------------------------------------------------        (rcdPerm)
--                        {i₁:σ₁...iₙ:σₙ} <: {j₁:τ₁...jₙ:τₙ}
--
--  It is worth noting that full-blown language designs may
--  choose not to adopt all of these subtyping rules. For
--  example, in Java:
--  - Each class member (field or method) can be assigned a
--    single index, adding new indices "on the right" as
--    more members are added in subclasses (i.e., no
--    permutation for classes).
--  - A class may implement multiple interfaces -- so-called
--    "multiple inheritance" of interfaces (i.e.,
--    permutation is allowed for interfaces).
--  - In early versions of Java, a subclass could not change
--    the argument or result types of a method of its
--    superclass (i.e., no depth subtyping or no arrow
--    subtyping, depending how you look at it).

--  #### ⊤

--  Finally, it is convenient to give the subtype relation a
--  maximum element -- a type that lies above every other
--  type and is inhabited by all (well-typed) values. We do
--  this by adding to the language one new type constant,
--  called `⊤` (pronounced "⊤" and written ⊤), together with
--  a subtyping rule that places it above every other type
--  in the subtype relation:
--
--                                         --------                             (⊤)
--                                         σ <: ⊤
--
--  The `⊤` type is an analog of the `Object` type in Java
--  and C#.

--  #### Summary

--  In summary, we form the STLC with subtyping by starting
--  with the pure STLC (over some set of base types) and
--  then...
--  - adding a base type `⊤`,
--  - adding the rule of subsumption
--
--                               Γ ⊢ t₁ ⦂ τ₁     τ₁ <: τ₂
--                               --------------------------------            (sub)
--                                     Γ ⊢ t₁ ⦂ τ₂
--
--  to the typing relation, and
--  - defining a subtype relation as follows:
--
--                                    σ <: υ    υ <: τ
--                                    ----------------                        (trans)
--                                         σ <: τ
--
--                                         ------                              (refl)
--                                         τ <: τ
--
--                                         --------                             (⊤)
--                                         σ <: ⊤
--
--                                  σ₁ <: τ₁    σ₂ <: τ₂
--                                  --------------------                       (prod)
--                                   σ₁ × σ₂ <: τ₁ × τ₂
--
--                                  τ₁ <: σ₁    σ₂ <: τ₂
--                                  --------------------                      (arrow)
--                                  σ₁ → σ₂ <: τ₁ → τ₂
--
--                                     n > m
--                       ---------------------------------                 (rcdWidth)
--                       {i₁:τ₁...iₙ:τₙ} <: {i₁:τ₁...iₘ:τₘ}
--
--                             σ₁ <: τ₁  ...  σₙ <: τₙ
--                        ----------------------------------               (rcdDepth)
--                        {i₁:σ₁...iₙ:σₙ} <: {i₁:τ₁...iₙ:τₙ}
--
--               {i₁:σ₁...iₙ:σₙ} is a permutation of {j₁:τ₁...jₙ:τₙ}
--               ---------------------------------------------------        (rcdPerm)
--                        {i₁:σ₁...iₙ:σₙ} <: {j₁:τ₁...jₙ:τₙ}

--   ----------------------------------------

--  _Quiz:_

--  Suppose we have `σ <: τ` and `υ <: δ`. Which of the
--  following subtyping assertions is false?
--
--  (A) `σ×υ <: ⊤`
--
--  (B) `{i₁:σ,i₂:τ}→υ <: {i₁:σ,i₂:τ,i₃:δ}→υ`
--
--  (C) `(σ→τ) → (⊤ → ⊤)  <:  (σ→τ) → ⊤`
--
--  (D) `(⊤ → ⊤) → δ  <:  ⊤ → δ`
--
--  (E) `σ → {i₁:υ,i₂:δ} <: σ → {i₂:δ,i₁:υ}`

--   ----------------------------------------

--  _Quiz:_

--  How about these?
--
--  (A) `{i₁:⊤} <: ⊤`
--
--  (B) `⊤ → (⊤ → ⊤)  <:  ⊤ → ⊤`
--
--  (C) `{i₁:τ} → {i₁:τ}  <:  {i₁:τ,i₂:σ} → ⊤`
--
--  (D) `{i₁:τ,i₂:δ,i₃:δ} <: {i₁:σ,i₂:υ} × {i₃:δ}`
--
--  (E) `⊤ → {i₁:υ,i₂:δ} <: {i₁:σ} → {i₂:δ,i₁:δ}`

--   ----------------------------------------

--  ### Exercises

--   ----------------------------------------

--  _Quiz:_

--  What is the *smallest* type `τ` that makes the following
--  assertion true?
--
--          X:A ⊢ (λP:(A×τ). (P.snd) (P.fst)) (X, λZ:A. Z) ⦂ A
--
--  (A) `⊤`
--
--  (B) `A`
--
--  (C) `⊤→⊤`
--
--  (D) `⊤→A`
--
--  (E) `A→A`
--
--  (F) `A→⊤`

--   ----------------------------------------

--  _Quiz:_

--  What is the *largest* type `τ` that makes the following
--  assertion true?
--
--             X:A ⊢ (λP:(A×τ). (P.snd) (P.fst)) (X, λZ:A. Z) ⦂ A
--
--  (A) `⊤`
--
--  (B) `A`
--
--  (C) `⊤→⊤`
--
--  (D) `⊤→A`
--
--  (E) `A→A`
--
--  (F) `A→⊤`

--   ----------------------------------------

--  _Quiz:_

--  "The type `Bool` has no proper subtypes." (I.e., the
--  only type smaller than `Bool` is `Bool` itself.)
--
--  (A) True
--
--  (B) False

--   ----------------------------------------

--  _Quiz:_

--  "Suppose `σ`, `τ₁`, and `τ₂` are types with
--  `σ <: τ₁ → τ₂`. Then `σ` itself is an arrow type --
--  i.e., `σ = σ₁ → σ₂` for some `σ₁` and `σ₂` -- with `τ₁`
--  <: `σ₁` and `σ₂ <: τ₂`."
--
--  (A) True
--
--  (B) False

--   ----------------------------------------

--  ## Formal Definitions

namespace StlcSub

open scoped MyGetElem

--  Most of the definitions needed to formalize what we've
--  discussed above -- in particular, the syntax and
--  operational semantics of the language -- are identical
--  to what we saw in the last chapter. We just need to
--  extend the typing relation with the subsumption rule and
--  add a new `inductive` definition for the subtyping
--  relation. Let's first do the identical bits.

--  ### Core Definitions

--  #### Syntax

--  Omitting records, to avoid dealing with "..." stuff.

inductive Ty : Type where
  | top   : Ty
  | bool  : Ty
  | base  : String → Ty
  | arrow : Ty → Ty → Ty
  | unit  : Ty
  | prod : Ty → Ty → Ty

inductive Tm : Type where
  | var : String → Tm
  | app : Tm → Tm → Tm
  | abs : String → Ty → Tm → Tm
  | tru : Tm
  | fls : Tm
  | ite : Tm → Tm → Tm → Tm
  | unit : Tm
  | pair : Tm → Tm → Tm
  | fst : Tm → Tm
  | snd : Tm → Tm

--  This language uses the shared `<{ ... }>` notation from
--  Stlc. Capital Latin identifiers in term positions are
--  `Tm` variables. In type positions, `Bool` and `Unit`
--  name the distinguished types above, while other capital
--  Latin identifiers, such as `A`, `Int`, or `String`, name
--  base types in `Ty`. Lowercase and Greek identifiers
--  refer directly to in-scope Lean variables, while
--  arbitrary Lean expressions require `~` antiquotation.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation)
scoped syntax:50 stlcTy:51 " × " stlcTy:50 : stlcTy
scoped syntax:max " ⊤ " : stlcTy
scoped syntax:50 "if " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm
scoped syntax:max " ( " stlcTm:60 " , " stlcTm:60 " ) " : stlcTm

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
  subst := `StlcSub.subst
  hasType := `StlcSub.HasType

def subTyHandler : TyElabHandler :=
  fun recur k T => do
    match T with
    | `(stlcTy| ⊤) => do
        return mkConst ``Ty.top
    | `(stlcTy| Bool) => do
        return mkConst ``Ty.bool
    | `(stlcTy| Unit) => do
        return mkConst ``Ty.unit
    | `(stlcTy| $T₁:stlcTy × $T₂:stlcTy) => do
        let T₁ ← recur T₁
        let T₂ ← recur T₂
        return mkApp2 (mkConst ``Ty.prod) T₁ T₂
    | _ => k T

/--
Make unresolved type identifiers "base types".
This must run after `commonTyHandler`
so a Lean variable `τ : Ty` is implicitly antiquoted first.
-/

def baseTyHandler : TyElabHandler :=
  fun _recur k T => do
    match T with
    | `(stlcTy| $id:ident) => do
        match classifyIdent? id with
        | some (.object, name) =>
          return mkApp (mkConst ``Ty.base) (mkStrLit name)
        | _ => k T
    | _ => k T

def tyHandlers : TyElabHandler :=
  subTyHandler.orElse ((commonTyHandler language).orElse baseTyHandler)

partial def elabTy : TyElab := tyHandlers elabTy  <| unsupportedTy language

def subTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| true) =>
        return (mkConst ``Tm.tru, free)
    | `(stlcTm| false) =>
        return (mkConst ``Tm.fls, free)
    | `(stlcTm| Bool) =>
        throwError "`Bool` is not a valid term."
    | `(stlcTm| Unit) =>
        throwError "`Unit` is not a valid term."
    | `(stlcTm| if $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite) c t e, free)
    | `(stlcTm| unit) =>
        return (mkConst ``Tm.unit, free)
    | `(stlcTm| ($t₁:stlcTm, $t₂:stlcTm)) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.pair) t₁ t₂, free)
    | `(stlcTm| fst $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.fst) t, free)
    | `(stlcTm| snd $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.snd) t, free)
    | _ => k Γ free t

def tmHandlers : TmElabHandler := subTmHandler.orElse (commonTmHandler language elabTy)

partial def elabTm : TmElab := tmHandlers elabTm unsupportedTm

def elabCtx : CtxElab :=
  elabCtxCommon language elabTy

@[scoped term_elab StlcCommon.bracket]
def elabBracket : TermElab :=
  fun stx expectedType? => do
    let `(<{ $q:stlcQuoted }>) := stx
      | throwUnsupportedSyntax
    elabQuoted language elabTy elabTm elabCtx q expectedType?

end Elab

open scoped Elab

namespace Delab

open StlcCommon Elab Delab
open Lean PrettyPrinter Delaborator


@[app_unexpander Ty.top]
private def Ty.unexpandTop : Unexpander
  | _ => `(<{ ⊤ }>)

@[app_unexpander Ty.bool]
private def Ty.unexpandBool : Unexpander
  | stx => do
      let Bool := mkObjectIdentFrom stx "Bool"
      let T ← `(stlcTy| $Bool:ident)
      `(<{ $T:stlcTy }>)

@[app_unexpander Ty.unit]
private def Ty.unexpandUnit : Unexpander
  | stx => do
      let Unit := mkObjectIdentFrom stx "Unit"
      let T ← `(stlcTy| $Unit:ident)
      `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Ty.prod]
private def Ty.unexpandProd : Unexpander
  | `($_ $T₁ $T₂) => do
      let T₁' := getTy T₁
      let T₂' := getTy T₂
      `(<{ $T₁':stlcTy × $T₂':stlcTy }>)
  | _ => throw ()

private def reservedTyNames : String → Bool
  | "Bool" | "Unit" => true
  | _ => false

@[app_unexpander Ty.base]
private def Ty.unexpandBase : Unexpander
  | stx@`($_ $s:str) => do
      let name := s.getString
      let id := mkObjectIdentFrom stx name
      match classifyIdent? id, reservedTyNames name with
      | some (.object, _), false =>
          let T ← `(stlcTy| $id:ident)
          `(<{ $T:stlcTy }>)
      | _, _ => throw ()
  | _ => throw ()

private def reservedTmNames : String → Bool
  | "true" | "false" | "Bool"
  | "Unit" | "unit" | "fst"
  | "snd" => true
  | _ => false


@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander :=
  Delab.unexpandVar reservedTmNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.tru]
private def Tm.unexpandTru : Unexpander
  | stx => do
      let tru := mkObjectIdentFrom stx "true"
      let t ← `(stlcTm| $tru:ident)
      `(<{ $t:stlcTm }>)

@[app_unexpander Tm.fls]
private def Tm.unexpandFls : Unexpander
  | stx => do
      let fls := mkObjectIdentFrom stx "false"
      let t ← `(stlcTm| $fls:ident)
      `(<{ $t:stlcTm }>)

@[app_unexpander Tm.ite]
private def Tm.unexpandIte : Unexpander
  | `($_ $c $t $e) => do
      let c' := getTm c
      let t' := getTm t
      let e' := getTm e
      `(<{if $c':stlcTm then $t':stlcTm else $e':stlcTm }>)
  | _ => throw ()


@[app_unexpander Tm.unit]
private def Tm.unexpandUnit : Unexpander
  | stx => do
      let unit := mkObjectIdentFrom stx "unit"
      let t ← `(stlcTm| $unit:ident)
      `(<{ $t:stlcTm }>)

@[app_unexpander Tm.pair]
private def Tm.unexpandPair : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ ($t₁':stlcTm, $t₂':stlcTm) }>)
  | _ => throw ()


@[app_unexpander Tm.fst]
private def Tm.unexpandFst : Unexpander
  | stx@`($_ $t) => do
      let fst := mkObjectIdentFrom stx "fst"
      let t' := getTm t
      `(<{ $fst:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.snd]
private def Tm.unexpandSnd : Unexpander
  | stx@`($_ $t) => do
      let snd := mkObjectIdentFrom stx "snd"
      let t' := getTm t
      `(<{ $snd:ident $t':stlcTm }>)
  | _ => throw ()

end Delab
--  END DETAILS

--  ### Substitution

--  The definition of substitution remains exactly the same
--  as for the pure STLC.

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- pure STLC
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ y : τ . [x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([x := s] t₁) ([x := s] t₂) }>
  -- unit
  | .unit => <{ unit }>
  -- bools
  | .tru => <{ true }>
  | .fls => <{ false }>
  | .ite t₁ t₂ t₃ =>
      <{ if [x := s] t₁ then [x := s] t₂ else [x := s] t₃ }>

  -- Complete the following cases when you do the `products` exercise later
  | .pair t₁ t₂ =>
      sorry
  | .fst t =>
      sorry
  | .snd t =>
      sorry

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding)
open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst
--  END DETAILS

--  ### Reduction

--  Likewise the definitions of `IsValue` and `Step`.

inductive Tm.IsValue : Tm → Prop where
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) :
      IsValue <{λ x : τ₂ . t₁}>
  | tru :
      IsValue <{true}>
  | fls :
      IsValue <{false}>
  | unit :
      IsValue <{unit}>

-- Fill in more rules when you do the `products` exercise later
--  FILL IN HERE

attribute [StlcSubEval] Tm.IsValue.abs Tm.IsValue.tru Tm.IsValue.fls Tm.IsValue.unit

section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
  -- pure STLC
  | appAbs (x : String) (τ₂ : Ty) (t₁ v₂ : Tm) :
      v₂.IsValue →
       <{(λ x : τ₂ . t₁) v₂}> ⟶ <{ [x := v₂] t₁ }>
  | app₁ (t₁ t₁' t₂ : Tm) :
      t₁ ⟶ t₁' →
      <{t₁ t₂}> ⟶ <{t₁' t₂}>
  | app₂ (v₁ t₂ t₂' : Tm) :
      v₁.IsValue →
      t₂ ⟶ t₂' →
      <{v₁ t₂}> ⟶ <{v₁ t₂'}>
  -- booleans
  | ifStep (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if t₁ then t₂ else t₃ }> ⟶ <{ if t₁' then t₂ else t₃ }>
  | ifTrue (t₂ t₃ : Tm) :
      <{ if true then t₂ else t₃ }> ⟶ t₂
  | ifFalse (t₂ t₃ : Tm) :
      <{ if false then t₂ else t₃ }> ⟶ t₃

  -- Fill in more rules when you do the `products` exercise later
  --  FILL IN HERE
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

-- Be sure to add your constructors for pairs to this list later
attribute [StlcSubEval] Step.appAbs Step.app₁ Step.app₂
    Step.ifStep Step.ifTrue Step.ifFalse
--  FILL IN HERE

--  ### Subtyping

section
set_option hygiene false in
local notation:40 τ:41 " <: " τ':41 => Subtype τ τ'

inductive Subtype : Ty → Ty → Prop where
  | refl {τ : Ty} :
      τ <: τ
  | trans {σ υ τ: Ty}
      (h₁ : σ <: υ)
      (h₂ : υ <: τ) :
      σ <: τ
  | top {σ : Ty} :
      σ <: <{ ⊤ }>
  | arrow { σ₁ σ₂ τ₁ τ₂ : Ty}
      (h₁ : τ₁ <: σ₁)
      (h₂ : σ₂ <: τ₂) :
      <{ σ₁ → σ₂ }> <: <{ τ₁ → τ₂ }>

-- Fill in more rules when you do the `products` exercise later
--  FILL IN HERE
end

scoped notation:40 τ:41 " <: " τ':41 => Subtype τ τ'

attribute [StlcSubTyping] Subtype.refl Subtype.trans Subtype.top Subtype.arrow
--  FILL IN HERE

--  Note that we don't need any special rules for base types
--  (`Bool` and `Base`): they are automatically subtypes of
--  themselves (by `refl`) and `⊤` (by `top`), and that's
--  all we want.

--  ### Typing

--  The only change to the typing relation is the addition
--  of the rule of subsumption, `sub`.

abbrev Context := PartialMap String Ty

inductive HasType : Context → Tm → Ty → Prop where
  -- pure STLC
  | var (Γ : Context) (x : String) (τ₁ : Ty) (h : Γ[x] = some τ₁) :
      <{ Γ ⊢ ~(Tm.var x) ⦂ τ₁ }>
  | abs (Γ : Context) (x : String) (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ ⊢ λ x : τ₂ . t₁ ⦂ τ₂ → τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ Γ ⊢ t₁ ⦂ τ₂ → τ₁ }>) (h₂ : <{ Γ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ ⊢ t₁ t₂ ⦂ τ₁ }>
  -- booleans
  | tru (Γ : Context) :
      <{ Γ ⊢ true ⦂ Bool }>
  | fls (Γ : Context) :
      <{ Γ ⊢ false ⦂ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (τ : Ty)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Bool }>) (h₂ : <{ Γ ⊢ t₂ ⦂ τ }>)
      (h₃ : <{ Γ ⊢ t₃ ⦂ τ }>) :
      <{ Γ ⊢ if t₁ then t₂ else t₃ ⦂ τ }>
  -- unit
  | unit (Γ : Context) :
      <{ Γ ⊢ unit ⦂ Unit }>
  -- subsumption
  | sub (Γ : Context) (t₁ : Tm) (τ₁ τ₂ : Ty)
      (ht : <{ Γ ⊢ t₁ ⦂ τ₁ }>)
      (hs : τ₁ <: τ₂) :
      <{ Γ ⊢ t₁ ⦂ τ₂ }>

  -- Fill in more rules when you do the `products` exercise later
  --  FILL IN HERE

-- Make sure to add your constructors here
attribute [StlcSubTyping] HasType.var HasType.abs HasType.app
    HasType.ite HasType.tru HasType.fls HasType.unit
--  FILL IN HERE

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding)
open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander := StlcCommon.Delab.unexpandHasType
--  END DETAILS

--  We deliberately exclude `HasType.sub` from the list of
--  constructors with the `StlcSubTyping`.
--  `apply_rules using StlcSubTyping` will search for
--  derivations without using the subtyping rule; if you
--  want to make use of it in a derivation you will need to
--  do so yourself.

--  ## Properties

--  We want the same properties as always: progress +
--  preservation.
--  - *Statements* of these theorems don't need to change,
--    compared to pure STLC
--  - But *proofs* are a bit more involved, to account for
--    the additional flexibility in the typing relation

--  ### Inversion Lemmas for Subtyping

--  Before we look at the properties of the typing relation,
--  we need to establish a couple of critical structural
--  properties of the subtype relation:
--  - `Bool` is the only subtype of `Bool`, and
--  - every subtype of an arrow type is itself an arrow
--    type.
--
--  Formally:

--  ### Exercise (2 stars): sub_inversion_bool (Optional) ⭐⭐

theorem sub_inversion_bool (τ : Ty)
    (h : τ <: <{ Bool }>) :
    τ = Ty.bool := by
  sorry

--  ### Exercise (3 stars): sub_inversion_arrow ⭐⭐⭐

theorem sub_inversion_arrow {σ τ₁ τ₂ : Ty}
     (h : σ <: <{ τ₁ → τ₂ }>) :
     ∃ σ₁ σ₂,
     σ = <{ σ₁ → σ₂ }> ∧ τ₁ <: σ₁ ∧ σ₂ <: τ₂ := by
  sorry

--  ### Canonical Forms

--  The proof of progress uses facts of the form "every
--  value belonging to an arrow type is an abstraction."
--
--  In the pure STLC, such facts are "immediate from the
--  definition" (formally, they follow directly by
--  `inversion`).
--
--  With subtyping, they require real proofs by induction...

--  ### Exercise (3 stars): canonical_forms_of_arrow_types (Optional) ⭐⭐⭐

theorem canonical_forms_of_arrow_types {Γ : Context} {t : Tm} {τ₁ τ₂ : Ty}
  (ht : <{ Γ ⊢ t ⦂ τ₁ → τ₂ }>)
  (hv : t.IsValue) :
  ∃ x σ₁ t₂, t = <{λ x : σ₁ . t₂}> := by
  sorry

--  (End of exercise)

--  Similarly, the canonical forms of type `Bool` are the
--  constants `tru` and `fls`

theorem canonical_forms_of_bool {Γ : Context} {t : Tm}
  (ht : <{ Γ ⊢ t ⦂ Bool }>)
  (hv : t.IsValue) :
  t = Tm.tru ∨ t = Tm.fls := by

  generalize heq : Ty.bool = τ at ht
  induction ht with (subst_vars; first | trivial | try lia)
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
    apply sub_inversion_bool at hs; subst_vars
    exact ih hv rfl

--  ### Progress

--  Formally:

theorem progress (t : Tm) (τ : Ty) (h : <{ ∅ ⊢ t ⦂ τ }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  generalize heq : (∅ : Context) = Γ at h
  induction h with (subst_vars; first
    | contradiction
    -- discharge cases where `t` is obviously a value
    | try (left; constructor; done)
  )
  | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      right; cases ih₁ rfl with
      -- t₁ is a value
      | inl ht₁ =>
        cases ih₂ rfl with
        -- t₂ is a value
        | inl ht₂ =>
          apply canonical_forms_of_arrow_types at h₁
          let ⟨x, σ, v, hv⟩ := h₁ ht₁
          exists <{ [x := t₂] v }>; simp [hv]
          apply_rules using StlcSubEval
        -- t₂ is not a value
        | inr ht₂ =>
          obtain ⟨t₂', ht₂⟩ := ht₂
          exists <{t₁ t₂'}>; apply_rules using StlcSubEval
      -- t₁ is not a value
      | inr ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exists <{t₁' t₂}>; apply_rules using StlcSubEval
  | ite Γ t₁ t₂ t₃ τ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    right; cases ih₁ rfl with
    -- t₁ is a value
    | inl ht₁ =>
      apply canonical_forms_of_bool at h₁
      obtain h₁ | h₁ := h₁ ht₁ <;> subst_vars
      · exists t₂; apply_rules using StlcSubEval
      · exists t₃; apply_rules using StlcSubEval
    -- t₁ is not a value
    | inr ht₁ =>
      obtain ⟨t₁', ht₁⟩ := ht₁
      exists <{if t₁' then t₂ else t₃}>; apply_rules using StlcSubEval
  | sub Γ t₁ τ₁ τ₂ ht hs ih => apply ih; rfl
-- Fill in products here later
--  FILL IN HERE

--  ### Inversion Lemmas for Typing

--  We also need to prove an inversion lemma corresponding
--  to a structural fact about the typing relation that is
--  "obvious from the definition" in pure STLC.
--
--  *Lemma*: If `Γ ⊢ λ x : σ₁ . t₂ ⦂ τ`, then there is a
--  type `σ₂` such that `x ↦ σ₁ ;  Γ ⊢ t₂ ⦂ σ₂` and
--  `σ₁ → σ₂ <: τ`.
--
--  *Proof*: Let `Γ`, `x`, `σ₁`, `t₂` and `τ` be given as
--  described. Proceed by induction on the derivation of
--  `Γ ⊢ λ x : σ₁ . t₂ ⦂ τ`. The cases for `var` and `app`
--  are vacuous as those rules cannot be used to give a type
--  to a syntactic abstraction.
--  - If the last step of the derivation is a use of `abs`
--    then there is a type `τ₁₂` such that `τ = σ₁ → τ₁₂`
--    and `x ↦ σ₁; Γ ⊢ t₂ ⦂ τ₁₂`. Picking `τ₁₂` for `σ₂`
--    gives us what we need, since `σ₁ → τ₁₂ <: σ₁ → τ₁₂`
--    follows from `rfl`.
--  - If the last step of the derivation is a use of `sub`
--    then there is a type `σ` such that `σ <: τ` and
--    `Γ ⊢ λx : σ₁, t₂ ⦂ σ`. The IH for the typing
--    subderivation tells us that there is some type `σ₂`
--    with `σ₁ → σ₂ <: σ` and `x↦σ₁; Γ ⊢ t₂ ⦂ σ₂`. Picking
--    type `σ₂` gives us what we need, since `σ₁ → σ₂ <: τ`
--    then follows by `trans`.
--
--  Formally:

theorem typing_inversion_abs {Γ : Context} {x : String} {σ₁ : Ty} {t₂ : Tm} {τ : Ty}
  (h : <{ Γ ⊢ λ x : σ₁ . t₂ ⦂ τ }>) :
    ∃ σ₂, <{ σ₁ → σ₂ }> <: τ ∧ <{ x ↦ σ₁ ; Γ ⊢ t₂ ⦂ σ₂ }> := by

  generalize heq : <{ λ x : σ₁ . t₂ }> = t at h
  induction h with (subst_vars; try contradiction)
  | abs Γ x τ₁ τ₂ t₁ h i =>
      inversion heq; exists τ₁; solve_by_elim using StlcSubTyping
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      obtain ⟨σ₂, hs', ht'⟩ := ih rfl
      exists σ₂; solve_by_elim using StlcSubTyping

--  Similarly:

theorem typing_inversion_unit (Γ : Context) (τ : Ty)
  (h : <{ Γ ⊢ unit ⦂ τ }>) :
  <{ Unit }> <: τ := by

  generalize heq : Tm.unit = t at h
  induction h with (subst_vars; try contradiction)
  | unit => inversion heq; solve_by_elim using StlcSubTyping
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      specialize ih rfl
      solve_by_elim using StlcSubTyping

--  -- Add your lemmas for products here when you get to
--  that exercise

--  FILL IN HERE

--  The inversion lemmas for typing and for subtyping
--  between arrow types can be packaged up as a useful
--  "combination lemma" telling us exactly what we'll
--  actually require below.

theorem abs_arrow {x : String} {t₂ : Tm} {σ₁ τ₁ τ₂ : Ty}
  (h : <{ ∅ ⊢ λ x : σ₁ . t₂ ⦂ τ₁ → τ₂ }> ) :
  τ₁ <: σ₁ ∧ <{ x ↦ σ₁ ; ∅ ⊢ t₂ ⦂ τ₂ }> := by
    obtain ⟨σ₂, hs, ht⟩ := typing_inversion_abs h; clear h
    obtain ⟨_, _, heq, hs₁, hs₂⟩ := sub_inversion_arrow hs; clear hs
    inversion heq; constructor
    · solve_by_elim using StlcSubTyping
    · apply HasType.sub <;> solve_by_elim using StlcSubTyping

--  ### Weakening

--  The weakening lemma is proved as in pure STLC, with the
--  exception of the `sub` case, which requires a manual use
--  of the `sub` rule.

theorem weakening {Γ Γ' : Context} {t : Tm} {τ: Ty}
    (hi : Γ ⊆ Γ')
    (ht : <{ Γ ⊢ t ⦂ τ }>) :
     <{ Γ' ⊢ t ⦂ τ }> := by
  induction ht generalizing Γ' with (try apply_rules [PartialMap.update_subset] using StlcSubTyping)
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
    apply HasType.sub <;> solve_by_elim using StlcSubTyping

theorem weakening_empty {Γ : Context} {t : Tm} {τ: Ty}
    (ht :<{ ∅ ⊢ t ⦂ τ }>) :
    <{ Γ ⊢ t ⦂ τ }> := by
  apply weakening _ ht
  intro _ _ h
  rw [PartialMap.getElem_empty] at h
  contradiction

--  ### Substitution

--  The *substitution lemma* is stated exactly as in pure
--  STLC.
--
--  The proof is also the same except that here it is easier
--  to use induction on typing derivations rather than on
--  terms.

theorem substitution_preserves_typing {Γ : Context} {x : String} {τ₁ : Ty} {t v : Tm} {τ : Ty}
    (ht : <{ x ↦ τ₁ ; Γ ⊢ t ⦂ τ }>)
    (hv : <{ ∅ ⊢ v ⦂ τ₁ }>) :
    <{ Γ ⊢ [x := v] t ⦂ τ }> := by

  generalize heq : x →ₚ τ₁ ; Γ = Γ' at ht
  induction ht generalizing x Γ with (
    subst_vars; try rw [subst]; try (apply_rules using StlcSubTyping; done))
  | var Γ y σ h =>
      by_cases h₁ : x = y
      · subst h₁; simp at h; subst h;
        apply weakening_empty at hv
        simp; assumption
      · rw [PartialMap.update_neq] at h <;> simp_all
        apply_rules using StlcSubTyping
  | abs _ y _ _ _ h ih =>
      by_cases h₁ : x = y
      · simp_all [PartialMap.update_shadow]; apply_rules using StlcSubTyping
      · simp_all; constructor; apply ih; rw [PartialMap.update_permute]; lia
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      apply HasType.sub <;> solve_by_elim using StlcSubTyping

--  ### Preservation

--  The proof of preservation now proceeds pretty much as in
--  earlier chapters, using the substitution lemma at the
--  appropriate point and the inversion lemma from above to
--  extract structural information from typing assumptions.
--
--  *Theorem* (Preservation): If `t`, `t'` are terms and `τ`
--  is a type such that `∅ ⊢ t ⦂ τ` and `t ⟶ t'`, then
--  `∅ ⊢ t' ⦂ τ`.
--
--  *Proof*: Let `t` and `τ` be given such that `∅ ⊢ t ⦂ τ`.
--  We proceed by induction on the structure of this typing
--  derivation. The `abs`, `unit`, `tru`, and `fls` cases
--  are vacuous because abstractions and constants don't
--  step. Case `var` is vacuous as well, since the context
--  is empty.
--  - If the final step of the derivation is by `app`, then
--    there are terms `t₁` and `t₂` and types `τ₁` and `τ₂`
--    such that `t = t₁ t₂`, `τ = τ₂`, `∅ ⊢ t₁ ⦂ τ₁ → τ₂`,
--    and `∅ ⊢ t₂ ⦂ τ₁`.
--
--    By the definition of the step relation, there are
--    three ways `t₁ t₂` can step. Cases `app₁'` and `app₂`
--    follow immediately by the induction hypotheses for the
--    typing subderivations and a use of `app`.
--
--    Suppose instead `t₁ t₂` steps by `appAbs`. Then
--    `t₁ = λ x:σ . t₁₂` for some type `σ` and term `t₁₂`,
--    and `t' = [x:=t₂] t₁₂`.
--
--    By lemma `abs_arrow`, we have `τ₁ <: σ` and
--    `x ↦ σ ; ∅ ⊢ t₁₂ ⦂ τ₂`. It then follows by the
--    substitution lemma (`substitution_preserves_typing`)
--    that `∅ ⊢ [x:=t₂] t₁₂ ⦂ τ₂` as desired.
--
--  - If the final step of the derivation uses rule `if`,
--    then there are terms `t₁`, `t₂`, and `t₃` such that
--    `t = if t₁ then t₂ else t₃`, with `∅ ⊢ t₁ ⦂ Bool` and
--    with `∅ ⊢ t₂ ⦂ τ` and `∅ ⊢ t₃ ⦂ τ`. Moreover, by the
--    induction hypothesis, if `t₁` steps to `t₁'` then
--    `∅ ⊢ t₁' : Bool`. There are three cases to consider,
--    depending on which rule was used to show `t ⟶ t'`.
--    - If `t ⟶ t'` by rule `if`, then
--      `t' = if t₁' then t₂ else t₃` with `t₁ ⟶ t₁'`. By
--      the induction hypothesis, `∅ ⊢ t₁' ⦂ Bool`, and so
--      `∅ ⊢ t' ⦂ τ` by `if`.
--    - If `t ⟶ t'` by rule `ifTrue` or `ifFalse`, then
--      either `t' = t₂` or `t' = t₃`, and `∅ ⊢ t' ⦂ τ`
--      follows by assumption.
--
--  - If the final step of the derivation is by `sub`, then
--    there is a type `σ` such that `σ <: τ` and
--    `∅ ⊢ t ⦂ σ`. The result is immediate by the induction
--    hypothesis for the typing subderivation and an
--    application of `sub`.
--
--  Qed.

theorem preservation {t t' : Tm} {τ : Ty}
  (ht : <{ ∅ ⊢ t ⦂ τ }>)
  (hs : t ⟶ t') :
  <{ ∅ ⊢ t' ⦂ τ }> := by

  generalize heq : (∅ : Context) = Γ at ht
  induction ht generalizing t' with (subst_vars; first
    -- discharge the goals where `t` doesn't step
    | inversion hs <;> constructor <;> simp_all; done
    | try (inversion hs; apply_rules using StlcSubTyping; done))
  | app Γ τ₁' τ₂' t₁' t₂ h₁ h₂ ih₁ ih₂ =>
    inversion hs with (try (constructor <;> apply_rules; done))
    | appAbs _ τ₂ t₁ h =>
        obtain ⟨h₁, h₂⟩ := abs_arrow h₁
        apply substitution_preserves_typing (τ₁:=τ₂)
        · assumption
        · apply HasType.sub <;> apply_rules using StlcSubTyping
  | ite Γ t₁ t₂ t₃ τ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    inversion hs with (try (constructor <;> solve_by_elim using StlcSubEval))
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      apply HasType.sub <;> solve_by_elim using StlcSubTyping
--  FILL IN HERE

end StlcSub

-- Source revision: 2d86b23, committed 2026-10-01 22:21 UTC

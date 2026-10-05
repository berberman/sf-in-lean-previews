import TS.StlcProp
import LF.CustomTactics

import SFLCompat

--  # MoreStlc: More on the Simply Typed Lambda-Calculus

--  ## Simple Extensions to STLC

--  The simply typed lambda-calculus has a rich enough
--  structure to make its theoretical properties
--  interesting, but it is not much of a programming
--  language!
--
--  In this chapter, we begin to close the gap with
--  real-world languages by introducing a number of familiar
--  features that have straightforward treatments at the
--  level of typing.

--  ### Numbers

--  Adding types, constants, and primitive operations for
--  natural numbers is easy (as we saw in the `StlcExtended`
--  exercises).
--
--  A more interesting extension... let-bindings.
--
--  When writing a complex expression, it is often useful to
--  give names to some of its subexpressions: this avoids
--  repetition and often increases readability.
--
--  Syntax:
--
--        t ::=                   Terms
--            | ...                 (other terms same as before)
--            | let x = t₁ in t₂    let-binding
--
--  Reduction:
--
--                                       t₁ ⟶ t₁'
--                           -------------------------------------        (let₁)
--                           let x = t₁ in t₂ ⟶ let x = t₁' in t₂
--
--                              ---------------------------------         (letValue)
--                              let x = v₁ in t₂ ⟶ [x := v₁] t₂
--
--  Typing:
--
--                   Γ ⊢ t₁ ⦂ τ₁      x ↦ τ₁ ; Γ ⊢ t₂ ⦂ τ₂
--                   -------------------------------------------      (let)
--                           Γ ⊢ let x = t₁ in t₂ ⦂ τ₂

--  ### Pairs

--  In Lean, there are two ways of extracting the components
--  of a pair: *pattern matching* and the projection
--  operators `fst` and `snd`. Just for fun, let's do our
--  pairs the latter way. For example, here's how we'd write
--  a function that takes a pair of numbers and returns the
--  pair of their sum and difference:
--
--             λX : Nat × Nat.
--                let Sum = fst X + snd X in
--                let Diff = fst X - snd X in
--                (Sum, Diff)
--
--  Syntax:
--
--             t ::=                Terms
--                 | ...
--                 | (t₁, t₂)         pair
--                 | fst t            first projection
--                 | snd t            second projection
--
--             v ::=                Values
--                 | ...
--                 | (v₁, v₂)         pair value
--
--             τ ::=                Types
--                 | ...
--                 | τ₁ × τ₂          product type
--
--  Reduction...
--
--                                    t₁ ⟶ t₁'
--                               --------------------                        (pair₁)
--                               (t₁,t₂) ⟶ (t₁',t₂)
--
--                                    t₂ ⟶ t₂'
--                               --------------------                        (pair₂)
--                               (v₁,t₂) ⟶ (v₁,t₂')
--
--                                     t ⟶ t'
--                                 ------------------                        (fst₁)
--                                 fst t ⟶ fst t'
--
--                                ------------------                       (fstPair)
--                                 fst (v₁,v₂) ⟶ v₁
--
--                                     t ⟶ t'
--                                 ------------------                      (snd₁)
--                                 snd t ⟶ snd t'
--
--                                ------------------                       (sndPair)
--                                snd (v₁,v₂) ⟶ v₂
--
--  Typing:
--
--                           Γ ⊢ t₁ ⦂ τ₁     Γ t₂ ⦂ τ₂
--                          ------------------------------              (pair)
--                            Γ ⊢(t₁, t₂) ⦂ τ₁ × τ₂
--
--                                 Γ ⊢ t ⦂ τ₁ × τ₂
--                              -----------------------                  (fst)
--                                  Γ ⊢ fst t ⦂ τ₁
--
--                                  Γ ⊢ t ⦂ τ₁ × τ₂
--                              -----------------------                   (snd)
--                                   Γ ⊢ snd t ⦂ τ₂

--  ### Unit

--  Another handy base type is the singleton type `Unit`.
--
--  Syntax:
--
--             t ::=                Terms
--                 | ...               (other terms same as before)
--                 | unit              unit
--
--             v ::=                Values
--                 | ...
--                 | unit              unit value
--
--             τ ::=                Types
--                 | ...
--                 | Unit              unit type
--
--  Typing:
--
--                               ----------------                       (unit)
--                               Γ ⊢ unit ⦂ Unit

--   ----------------------------------------

--  _Quiz:_

--  Is `unit` the only term of type `Unit`?
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  ### Sums

--  Many programs need to deal with values that can take two
--  distinct forms. For example, we might identify students
--  in a university database using *either* their name *or*
--  their id number. A search function might return *either*
--  a matching value *or* an error code.
--
--  These are specific examples of a binary *sum type*
--  (sometimes called a *disjoint union*), which describes a
--  set of values drawn from one of two given types, e.g.:
--
--             Nat + Bool
--
--  We create elements of these types by tagging elements of
--  the component types, telling on which side of the sum we
--  are putting them. E.g.,
--
--         inl 42   ⦂ Nat + Bool
--         inr true ⦂ Nat + Bool
--
--  In general, the elements of a type `τ₁ + τ₂` consist of
--  the elements of `τ₁` tagged with the token `inl`, plus
--  the elements of `τ₂` tagged with `inr`.
--
--  (As we've seen in Lean programming, one important use of
--  sums is signaling errors:
--
--            Div ⦂ Nat → Nat → (Nat + Unit)
--            Div =
--              λX:Nat. λY:Nat,
--                if iszero Y then
--                  inr unit
--                else
--                  inl ...
--
--  Values of sum type are "destructed" by case analysis:
--
--          GetNat ⦂ Nat + Bool → Nat
--          GetNat =
--            λX:Nat + Bool,
--              case X of
--                inl N => N
--              | inr B => if B then 1 else 0
--
--  More formally...
--
--  Syntax:
--
--             t ::=                Terms
--                 | ...               (other terms same as before)
--                 | inl τ₂ t₁         tagging (left)
--                 | inr τ₁ t₂         tagging (right)
--                 | case t of         case analysis
--                     inl x₁ => t₁
--                   | inr x₂ => t₂
--
--             v ::=                Values
--                 | ...
--                 | inl τ₂ v₁         tagged value (left)
--                 | inr τ₁ v₂         tagged value (right)
--
--             τ ::=                Types
--                 | ...
--                 | τ₁ + τ₂           sum type
--
--  Reduction:
--
--                                     t₁ ⟶ t₁'
--                              ------------------------                       (inl)
--                              inl τ₂ t₁ ⟶ inl τ₂ t₁'
--
--                                     t₂ ⟶ t₂'
--                              ------------------------                       (inr)
--                              inr τ₁ t₂ ⟶ inr τ₁ t₂'
--
--                                     t ⟶ t'
--                     -------------------------------------------            (case)
--                      case t of inl x₁ => t₁ | inr x₂ => t₂ ⟶
--                     case t' of inl x₁ => t₁ | inr x₂ => t₂
--
--                  -----------------------------------------------        (caseInl)
--                  case (inl τ₂ v₁) of inl x₁ => t₁ | inr x₂ => t₂
--                                 ⟶  [x₁ := v₁]t₁
--
--                  -----------------------------------------------        (caseInr)
--                  case (inr τ₁ v₂) of inl x₁ => t₁ | inr x₂ => t₂
--                                 ⟶  [x₂ := v₂]t₂
--
--  Typing:
--
--                                  Γ ⊢ t₁ ⦂ τ₁
--                         ----------------------------                      (inl)
--                             Γ ⊢ inl τ₂ t₁ ⦂ τ₁ + τ₂
--
--
--                                Γ ⊢ t₂ ⦂ τ₂
--                         ---------------------------                       (inr)
--                           Γ ⊢ inr τ₁ t₂ ⦂ τ₁ + τ₂
--
--
--                              Γ ⊢ t ⦂ τ₁ + τ₂
--                           x₁ ↦ τ₁; Γ ⊢ t₁ ⦂ τ₃
--                           x₂ ↦ τ₂; Γ ⊢ t₂ ⦂ τ₃
--               ----------------------------------------------------        (case)
--                   Γ ⊢ case t of inl x₁ => t₁ | inr x₂ => t₂ ⦂ τ₃
--
--  We use the type annotations on `inl` and `inr` to make
--  the typing relation deterministic (each term has at most
--  one type), as we did for functions.

--   ----------------------------------------

--  _Quiz:_

--  What does the following term step to (in one step)?
--
--            let F = λX : Nat + Bool.
--               case X of
--                 inl N => N + 3
--                 | inr B => 0 in
--            F (inl Bool 4)
--
--          (A)  (λX : Nat + Bool.
--                  case X of
--                    inl N => N + 3
--                    | inr B => 0
--               ) (inl Bool 4)
--
--          (B) 7
--
--          (C)  case inl Bool 4 of
--                 inl N => N + 3
--               | inr B => 0
--
--          (D) F (inl Bool 4)

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--        (λX : Nat + Bool.
--           case X of
--           inl N => N + 3
--           | inr B => 0
--        ) (inl Bool 4)
--
--         (A)  7
--
--         (B)  case inl Bool 4 of
--                inl N => N + 3
--              | inr B => 0
--
--         (C)  4 + 3

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--             case inl Bool 4 of
--               inl N => N + 3
--               | inr B => 0
--
--         (A)  4 + 3
--
--         (B)  7
--
--         (C)  0

--   ----------------------------------------

--  ### Lists

--  Syntax:
--
--             t ::=                Terms
--                 | ...
--                 | nil τ             ∅ list
--                 | t₁ :: t₂          cons
--                 | case t₁ of        case analysis
--                     nil      => t₂
--                     | xh::xt => t₃
--
--             v ::=                Values
--                 | ...
--                 | nil τ             nil value
--                 | v₁ :: v₂          cons value
--
--             τ ::=                Types
--                 | ...
--                 | List τ            list of τs
--
--  Reduction:
--
--                                      t₁ ⟶ t₁'
--                             --------------------------                    (cons₁)
--                               t₁ :: t₂ ⟶ t₁' :: t₂
--
--                                      t₂ ⟶ t₂'
--                             --------------------------                    (cons₂)
--                               v₁ :: t₂ ⟶ v₁ :: t₂'
--
--                                    t₁ ⟶ t₁'
--                      -------------------------------------------         (listCase₁)
--                       (case t₁ of nil => t₂ | xh :: xt => t₃) ⟶
--                      (case t₁' of nil => t₂ | xh :: xt => t₃)
--
--                     ------------------------------------------          (listCaseNil)
--                     (case nil τ₁ of nil => t₂ | xh :: xt => t₃)
--                                      ⟶ t₂
--
--                    -------------------------------------------         (listCaseCons)
--                    (case (vh :: vt) of nil => t₂ | xh :: xt => t₃)
--                                ⟶ [xh:=vh][xt:=vt] t₃
--
--  Typing:
--
--                              ----------------------------                    (nil)
--                              Γ ⊢ nil τ₁ ⦂ List τ₁
--
--                           Γ ⊢ t₁ ⦂ τ₁      Γ ⊢ t₂ ⦂ List τ₁
--                  -------------------------------------------------           (cons)
--                               Γ ⊢ t₁ :: t₂ ⦂ List τ₁
--
--                              Γ ⊢ t₁ ⦂ List τ₁
--                              Γ ⊢ t₂ ⦂ τ₂
--                        (xh ↦ τ₁; xt ↦ List τ₁; Γ) ⊢ t₃ ⦂ τ₂
--                ----------------------------------------------------         (listCase)
--                   Γ ⊢ (case t₁ of nil => t₂ | xh :: xt => t₃) ⦂ τ₂

--  ### General Recursion

--  Another facility found in most programming languages
--  (including Lean) is the ability to define recursive
--  functions. For example, we would like to be able to
--  define and use the factorial function like this:
--
--            let Fact = λX:Nat.
--                         if X=0 then 1 else X * (Fact (pred X))) in
--            Fact 3.
--
--  Note that the right-hand side of this binder mentions
--  `Fact`, the variable being bound - something that is not
--  allowed according to the way we defined `let` above.
--
--  Extending our formalization of `let`s to handle
--  "recursive definitions" would require non-trivial
--  effort.

--  Here is another way of presenting recursive functions
--  that is a bit more verbose but equally powerful and much
--  more straightforward to formalize: instead of writing
--  recursive definitions, we will define a *fixed-point
--  operator* called `fix` that performs the "unfolding" of
--  the recursive definition in the right-hand side as
--  needed, during reduction.
--
--  For example, instead of
--
--            Fact = λX:Nat.
--                      if X=0 then 1 else X * (Fact (pred X)))
--
--  we will write:

--  Fact =
--            fix
--              (λF:Nat → Nat.
--                 λX:Nat.
--                    if X=0 then 1 else X * (F (pred X)))

--  Syntax:
--
--             t ::=                Terms
--                 | ...
--                 | fix t₁            fixed-point operator
--
--  Reduction:
--
--                                      t₁ ⟶ t₁'
--                                  ------------------                   (fix₁)
--                                  fix t₁ ⟶ fix t₁'
--
--                     --------------------------------------------      (fixAbs)
--                     fix (λxf:τ₁.t₁) ⟶ [xf:=fix (λxf:τ₁.t₁)] t₁
--
--  Typing:
--
--                                 Γ ⊢ t₁ ⦂ τ₁ → τ₁
--                                 ------------------                    (fix)
--                                 Γ ⊢ fix t₁ ⦂ τ₁

--  Let's see how `fixAbs` works by reducing
--  `Fact 3 = fix F 3`, where
--
--          F = (λF. λX. if X=0 then 1 else X * (F (pred X)))
--
--  (type annotations are omitted for brevity).
--
--          fix F 3
--
--      ⟶ fixAbs + app₁
--
--          (λX. if X=0 then 1 else X * (fix F (pred X))) 3
--
--      ⟶ appAbs
--
--          if 3=0 then 1 else 3 * (fix F (pred 3))
--
--      ⟶ if0Nonzero
--
--          3 * (fix F (pred 3))
--
--      ⟶ fixAbs + mult₂ + app₁
--
--          3 * ((λX. if X=0 then 1 else X * (fix F (pred X))) (pred 3))
--
--      ⟶ predNat + mult₂ + app₂
--
--          3 * ((λX. if X=0 then 1 else X * (fix F (pred X))) 2)
--
--      ⟶ appAbs + mult₂
--
--          3 * (if 2=0 then 1 else 2 * (fix F (pred 2)))
--
--      ⟶ if0Nonzero + mult₂
--
--          3 * (2 * (fix F (pred 2)))
--
--      ⟶ fixAbs + 2 × mult₂ + app₁
--
--          3 * (2 * ((λX. if X=0 then 1 else X * (fix F (pred X))) (pred 2)))
--
--      ⟶ predNat + 2 x mult₂ + app₂
--
--          3 * (2 * ((λX. if X=0 then 1 else X * (fix F (pred X))) 1))
--
--      ⟶ appAbs + 2 x mult₂
--
--          3 * (2 * (if 1=0 then 1 else 1 * (fix F (pred 1))))
--
--      ⟶ if0Nonzero + 2 x mult₂
--
--          3 * (2 * (1 * (fix F (pred 1))))
--
--      ⟶ fixAbs + 3 x mult₂ + app₁
--
--          3 * (2 * (1 * ((λX. if X=0 then 1 else X * (fix F (pred X))) (pred 1))))
--
--      ⟶ predNat + 3 × mult₂ + app₂
--
--          3 * (2 * (1 * ((λX. if X=0 then 1 else X * (fix F (pred X))) 0)))
--
--      ⟶ appAbs + 3 × mult₂
--
--          3 * (2 * (1 * (if 0=0 then 1 else 0 * (fix F (pred 0)))))
--
--      ⟶ if0Zero + 3 x mult₂
--
--          3 * (2 * (1 * 1))
--
--      ⟶ multNats + 2 x mult₂
--
--          3 * (2 * 1)
--
--      ⟶ multNats + mult₂
--
--          3 * 2
--
--      ⟶ multNats
--
--          6
--
--  The simply typed lambda-calculus with fixed points is a
--  famous and extensively studied system. It is often
--  called *PCF* because it is a simple language of "partial
--  computable functions".
--
--  One important point to note is that, unlike definitions
--  in Lean, there is nothing to prevent functions defined
--  using `fix` from diverging.

--   ----------------------------------------

--  _Quiz:_

--  Is this a well-typed Stlc term? What does it evaluate
--  to?
--
--              fix (λF: Nat→Nat. λX:Nat. F X) 0
--
--         (A) no
--
--         (B) yes, diverges
--
--         (C) yes, [42]
--
--         (D) yes, [0]

--   ----------------------------------------

--  _Quiz:_

--  Which of the following are (intuitively) true for Stlc +
--  fixpoints.
--
--  (A) deterministic
--
--  (B) progress
--
--  (C) preservation
--
--  (D) normalizing (i.e. every well-typed term reduces to a
--  normal form)

--   ----------------------------------------

--  ## Records

--  As a final example, records can be presented as a
--  generalization of pairs:
--  - they are n-ary (rather than binary);
--  - they are accessed by *label* (rather than position).

--  Syntax:
--
--             t ::=                          Terms
--                 | ...
--                 | {i₁=t₁, ..., iₙ=tₙ}        record
--                 | t.i                        projection
--
--             v ::=                          Values
--                 | ...
--                 | {i₁=v₁, ..., iₙ=vₙ}        record value
--
--             τ ::=                          Types
--                 | ...
--                 | {i₁:τ₁, ..., iₙ:τₙ}        record type
--
--  Note that this is a quite informal definition compared
--  to previous ones:
--  - it uses "`...`" in the syntax for records
--  - it omits a usual side condition that the labels of a
--    record should not contain repetitions.
--
--  Reduction:
--
--                                    ti ⟶ ti'
--                       ------------------------------------                  (rcd)
--                           {i₁=v₁, ..., im=vm, in=ti , ...}
--                       ⟶ {i₁=v₁, ..., im=vm, in=ti', ...}
--
--                                    t ⟶ t'
--                                  --------------                           (proj₁)
--                                  t.i ⟶ t'.i
--
--                            -------------------------                    (projRcd)
--                            {..., i=vi, ...}.i ⟶ vi
--
--  - In the first rule, `ti` must be the leftmost field
--    that is not a value;
--  - In the last rule, there should be only one field
--    called `i`, and all the other fields must contain
--    values.
--
--  The typing rules are also simple:
--
--                     Γ ⊢ t₁ ⦂ τ₁     ...     Γ ⊢ tₙ ⦂ τₙ
--                -----------------------------------------------------        (rcd)
--                Γ ⊢ {i₁=t₁, ..., iₙ=tₙ} ⦂ {i₁:τ₁, ..., iₙ:τₙ}
--
--
--                            Γ ⊢ t ⦂ {..., i:τᵢ, ...}
--                          ---------------------------------                  (proj)
--                                Γ ⊢ t.i ⦂ τᵢ
--
--  Formalizing all this would take some work.

--  ### Exercise: Formalizing the Extensions

--  Syntax:

namespace StlcExtended

open scoped MyGetElem

inductive Ty : Type where
  | arrow : Ty → Ty → Ty
  | nat  : Ty
  | sum  : Ty → Ty → Ty
  | list : Ty → Ty
  | unit : Ty
  | prod : Ty → Ty → Ty

inductive Tm : Type where
  -- pure STLC
  | var : String → Tm
  | app : Tm → Tm → Tm
  | abs : String → Ty → Tm → Tm
  -- numbers
  | const: Nat → Tm
  | succ : Tm → Tm
  | pred : Tm → Tm
  | mult : Tm → Tm → Tm
  | ite0  : Tm → Tm → Tm → Tm
  -- sums
  | sumInl : Ty → Tm → Tm
  | sumInr : Ty → Tm → Tm
  | sumCase : Tm → String → Tm → String → Tm → Tm
          -- i.e., `case t of inl x₁ => t₁ | inr x₂ => t₂`
  -- lists
  | listNil : Ty → Tm
  | listCons : Tm → Tm → Tm
  | listCase : Tm → Tm → String → String → Tm → Tm
          -- i.e., [case t₁ of | nil => t₂ | x::y => t₃]
  -- unit
  | unit : Tm

  -- You are going to be working on the following extensions:

  -- pairs
  | pair : Tm → Tm → Tm
  | fst : Tm → Tm
  | snd : Tm → Tm
  -- let
  | letIn : String → Tm → Tm → Tm
         -- i.e., [let x = t₁ in t₂]
  -- fix
  | fix  : Tm → Tm

--  Note that, for brevity, we've omitted booleans and
--  instead provided a single `if0` form combining a zero
--  test and a conditional. That is, instead of writing
--
--             if x = 0 then ... else ...
--
--  we'll write this:
--
--             if0 x then ... else ...
--
--  As in Stlc, terms, types, contexts, and typing judgments
--  use `<{ … }>` brackets. Capital Latin identifiers are
--  object-language names; lowercase and Greek identifiers
--  refer directly to in-scope Lean variables; arbitrary
--  Lean expressions require `~` antiquotation.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation)
scoped syntax:50 stlcTy:51 " × " stlcTy:50 : stlcTy
scoped syntax:50 stlcTy:51 " + " stlcTy:50 : stlcTy
scoped syntax:51 " [ " stlcTy:50  " ] " : stlcTy

scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:60 " * " stlcTm:61 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

scoped syntax:60 " inr " stlcTy:60 ppSpace stlcTm:60 : stlcTm
scoped syntax:60 " inl " stlcTy:60 ppSpace stlcTm:60 : stlcTm
scoped syntax:50 "case " stlcTm:50 " of " "inl" stlcVar " => " stlcTm:50 " | "
  "inr" stlcVar " => " stlcTm:50 : stlcTm

scoped syntax:60 " nil " stlcTy:60 : stlcTm
scoped syntax:60 stlcTm:61 " :: " stlcTm:60 : stlcTm
scoped syntax:50 "case " stlcTm:50 " of " "nil" " => " stlcTm:50 " | "
  stlcVar " :: " stlcVar " => " stlcTm:50 : stlcTm

scoped syntax:max " ( " stlcTm:60 " , " stlcTm:60 " ) " : stlcTm

scoped syntax:50 "let " stlcVar " = " stlcTm:50 " in " stlcTm:50 : stlcTm

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
  subst := `StlcExtended.subst
  hasType := `StlcExtended.HasType

def extendedTyHandler : TyElabHandler :=
  fun recur k T => do
    match T with
    | `(stlcTy| Nat) =>
        return mkConst ``Ty.nat
    | `(stlcTy| Unit) =>
        return mkConst ``Ty.unit
    | `(stlcTy| $T₁:stlcTy + $T₂:stlcTy) => do
        let T₁ ← recur T₁
        let T₂ ← recur T₂
        return mkApp2 (mkConst ``Ty.sum) T₁ T₂
    | `(stlcTy| [$T:stlcTy]) => do
        let T ← recur T
        return mkApp (mkConst ``Ty.list) T
    | `(stlcTy| $T₁:stlcTy × $T₂:stlcTy) => do
        let T₁ ← recur T₁
        let T₂ ← recur T₂
        return mkApp2 (mkConst ``Ty.prod) T₁ T₂
    | _ => k T

def tyHandlers : TyElabHandler :=
  extendedTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy <| unsupportedTy language

def extendedTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| $n:num) => do
        return (mkApp (mkConst ``Tm.const) (mkNatLit n.getNat), free )

    | `(stlcTm| Nat) => do
        throwError "`Nat` is not a valid term."

    | `(stlcTm| succ $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.succ) t, free)

    | `(stlcTm| pred $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.pred) t, free)

    | `(stlcTm| $t₁:stlcTm * $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.mult) t₁ t₂, free)

    | `(stlcTm| if0 $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite0) c t e, free)

    | `(stlcTm| inl $T:stlcTy $t:stlcTm) => do
        let T ← elabTy T
        let (t, free) ← recur Γ free t
        return (mkApp2 (mkConst ``Tm.sumInl) T t, free)

    | `(stlcTm| inr $T:stlcTy $t:stlcTm) => do
        let T ← elabTy T
        let (t, free) ← recur Γ free t
        return (mkApp2 (mkConst ``Tm.sumInr) T t, free)

    | `(stlcTm|
        case $t:stlcTm of
          inl $x₁:stlcVar => $t₁:stlcTm |
          inr $x₂:stlcVar => $t₂:stlcTm) => do

        let (t, free) ← recur Γ free t

        -- The branches start from the same lexical Γ
        -- Only `free` is threaded from branch 1 into branch 2
        let (x₁, Γ₁) ← elabStlcBinder language Γ x₁
        let (t₁, free) ← recur Γ₁ free t₁

        let (x₂, Γ₂) ← elabStlcBinder language Γ x₂
        let (t₂, free) ← recur Γ₂ free t₂

        return (mkAppN (mkConst ``Tm.sumCase) #[t, x₁, t₁, x₂, t₂], free)

    | `(stlcTm| nil $T:stlcTy) => do
        let T ← elabTy T
        return (mkApp (mkConst ``Tm.listNil) T, free)

    | `(stlcTm| $t₁:stlcTm :: $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.listCons) t₁ t₂,  free)

    | `(stlcTm|
        case $t₁:stlcTm of
          nil => $t₂:stlcTm |
          $x:stlcVar :: $xs:stlcVar => $t₃:stlcTm) => do

        let (t₁, free) ← recur Γ free t₁

        -- nil branch has no binders
        let (t₂, free) ← recur Γ free t₂

        -- cons branch has two binders
        let (x, Γ) ← elabStlcBinder language Γ x
        let (xs, Γ) ← elabStlcBinder language Γ xs

        let (t₃, free) ← recur Γ free t₃

        return (mkAppN (mkConst ``Tm.listCase) #[t₁, t₂, x, xs, t₃], free)

    | `(stlcTm| Unit) => do
        throwError "`Unit` is not a valid term."

    | `(stlcTm| unit) => do
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

    | `(stlcTm|
        let $x:stlcVar = $t₁:stlcTm
        in $t₂:stlcTm) => do

        -- x is NOT in scope in t₁
        let (t₁, free) ← recur Γ free t₁

        -- but in scope in t₂
        let (x, Γ₂) ← elabStlcBinder language Γ x

        let (t₂, free) ← recur Γ₂ free t₂

        return (mkApp3 (mkConst ``Tm.letIn) x t₁ t₂, free)

    | `(stlcTm| fix $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.fix) t, free)

    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  extendedTmHandler.orElse (commonTmHandler language elabTy)


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

open StlcCommon Elab Delab
open Lean PrettyPrinter Delaborator

@[app_unexpander Ty.nat]
private def Ty.unexpandNat : Unexpander
  | stx => do
    let Nat := mkObjectIdentFrom stx "Nat"
    let T ← `(stlcTy| $Nat:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.unit]
private def Ty.unexpandUnit : Unexpander
  | stx => do
    let Unit := mkObjectIdentFrom stx "Unit"
    let T ← `(stlcTy| $Unit:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Ty.sum]
private def Ty.unexpandSum : Unexpander
  | `($_ $T₁ $T₂) => do
      let T₁' := getTy T₁
      let T₂' := getTy T₂
      `(<{ $T₁':stlcTy + $T₂':stlcTy }>)
  | _ => throw ()


@[app_unexpander Ty.list]
private def Ty.unexpandList : Unexpander
  | `($_ $T) => do
      let T' := getTy T
      `(<{ [$T':stlcTy] }>)
  | _ => throw ()

@[app_unexpander Ty.prod]
private def Ty.unexpandProd : Unexpander
  | `($_ $T₁ $T₂) => do
      let T₁' := getTy T₁
      let T₂' := getTy T₂
      `(<{ $T₁':stlcTy × $T₂':stlcTy }>)
  | _ => throw ()

private def reservedNames : String → Bool
  | "Nat" | "Unit" | "succ" | "pred"
  | "if0" | "inl" | "inr" | "nil"
  | "unit" | "fst" | "snd" | "let"
  | "fix" | "case" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var


@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var


@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp


@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.const]
private def Tm.unexpandConst : Unexpander
  | `($_ $n:num) => `(<{ $n:num }>)
  | _ => throw ()

@[app_unexpander Tm.succ]
private def Tm.unexpandSucc : Unexpander
  | stx@`($_ $t) => do
      let succ := mkObjectIdentFrom stx "succ"
      let t' := getTm t
      `(<{ $succ:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.pred]
private def Tm.unexpandPred : Unexpander
  | stx@`($_ $t) => do
      let pred := mkObjectIdentFrom stx "pred"
      let t' := getTm t
      `(<{ $pred:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.mult]
private def Tm.unexpandMult : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm * $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.ite0]
private def Tm.unexpandIte0 : Unexpander
  | `($_ $c $t $e) => do
      let c' := getTm c
      let t' := getTm t
      let e' := getTm e
      `(<{ if0 $c':stlcTm then $t':stlcTm else $e':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.sumInl]
private def Tm.unexpandSumInl : Unexpander
  | `($_ $T $t) => do
      let T' := getTy T
      let t' := getTm t
      `(<{ inl $T':stlcTy $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.sumInr]
private def Tm.unexpandSumInr : Unexpander
  | `($_ $T $t) => do
      let T' := getTy T
      let t' := getTm t
      `(<{ inr $T':stlcTy $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.sumCase]
private def Tm.unexpandSumCase : Unexpander
  | `($_ $t $x₁ $t₁ $x₂ $t₂) => do
      let t' := getTm t
      let x₁' := getVar x₁
      let t₁' := getTm t₁
      let x₂' := getVar x₂
      let t₂' := getTm t₂

      `(<{
        case $t':stlcTm of
          inl $x₁':stlcVar => $t₁':stlcTm |
          inr $x₂':stlcVar => $t₂':stlcTm
      }>)
  | _ => throw ()


@[app_unexpander Tm.listNil]
private def Tm.unexpandListNil : Unexpander
  | `($_ $T) => do
      let T' := getTy T
      `(<{ nil $T':stlcTy }>)
  | _ => throw ()

@[app_unexpander Tm.listCons]
private def Tm.unexpandListCons : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm :: $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.listCase]
private def Tm.unexpandListCase : Unexpander
  | `($_ $t₁ $t₂ $x $xs $t₃) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      let x' := getVar x
      let xs' := getVar xs
      let t₃' := getTm t₃
      `(<{
        case $t₁':stlcTm of
          nil => $t₂':stlcTm |
          $x':stlcVar :: $xs':stlcVar => $t₃':stlcTm
      }>)
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
  | _ =>
      throw ()

@[app_unexpander Tm.letIn]
private def Tm.unexpandLetIn : Unexpander
  | `($_ $x $t₁ $t₂) => do
      let x' := getVar x
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{
        let $x':stlcVar =
          $t₁':stlcTm
        in
          $t₂':stlcTm
      }>)
  | _ => throw ()


@[app_unexpander Tm.fix]
private def Tm.unexpandFix : Unexpander
  | stx@`($_ $t) => do
      let fix := mkObjectIdentFrom stx "fix"
      let t' := getTm t
      `(<{ $fix:ident $t':stlcTm }>)
  | _ => throw ()

end Delab
--  END DETAILS

--  Next we define the values of our language.

inductive Tm.IsValue : Tm → Prop where
  -- In pure STLC, function abstractions are values:
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) : IsValue <{λ x : τ₂ . t₁}>
  -- Numbers are values:
  | nat (n : Nat) : IsValue (.const n)
  -- A tagged value is a value:
  | sumInl (v : Tm) (τ₁ : Ty) :
      IsValue v →
      IsValue <{inl τ₁ v}>
  | sumInr  (v : Tm) (τ₁ : Ty) :
      IsValue v →
      IsValue <{inr τ₁ v}>
  -- A list is a value iff its head and tail are values:
  | listNil (τ₁ : Ty) : IsValue <{nil τ₁}>
  | listCons (v₁ v₂ : Tm) :
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{v₁ :: v₂}>
  -- A unit is always a value
  | unit : IsValue <{unit}>
  -- A pair is a value if both components are:
  | pair (v₁ v₂ : Tm) :
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{(v₁, v₂)}>

attribute [ExtStlcEval] Tm.IsValue.abs Tm.IsValue.nat Tm.IsValue.sumInl Tm.IsValue.sumInr
    Tm.IsValue.listNil Tm.IsValue.listCons Tm.IsValue.unit Tm.IsValue.pair

--  The proofs of progress and preservation for this
--  enriched system are essentially the same (though of
--  course longer) as for the pure STLC.

end StlcExtended

-- Source revision: 699b86f, committed 2026-10-05 13:15 UTC

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

--  A more interesting extension... let-bindings.
--
--  When writing a complex expression, it is often useful to
--  give names to some of its subexpressions: this avoids
--  repetition and often increases readability.

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
--             λx : Nat × Nat.
--                let sum = fst x + snd x in
--                let diff = fst x - snd x in
--                (sum, diff)
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

--  Reduction...

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

--  Typing:

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

--  We create elements of these types by tagging elements of
--  the component types, telling on which side of the sum we
--  are putting them. E.g.,
--
--         inl 42   ⦂ Nat + Bool
--         inr true ⦂ Nat + Bool

--  In general, the elements of a type `τ₁ + τ₂` consist of
--  the elements of `τ₁` tagged with the token `inl`, plus
--  the elements of `τ₂` tagged with `inr`.
--
--  (As we've seen in Lean programming, one important use of
--  sums is signaling errors:
--
--            div ⦂ Nat → Nat → (Nat + Unit)
--            div =
--              λx:Nat. λy:Nat,
--                if iszero y then
--                  inr unit
--                else
--                  inl ...

--  Values of sum type are "destructed" by case analysis:

--          getNat ⦂ Nat+Bool → Nat
--          getNat =
--            λx:Nat+Bool,
--              case x of
--                inl n => n
--              | inr b => if b then 1 else 0
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
--            let f = λx : Nat + Bool.
--               case x of
--                 inl n => n + 3
--                 | inr b => 0 in
--            f (inl Bool 4)
--
--          (A)  (λx : Nat + Bool.
--                  case x of
--                    inl n => n + 3
--                    | inr b => 0
--               ) (inl Bool 4)
--
--          (B) 7
--
--          (C)  case inl Bool 4 of
--                 inl n => n + 3
--               | inr b => 0
--
--          (D) f (inl Bool 4)

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--        (λx : Nat + Bool.
--           case x of
--           inl n => n + 3
--           | inr b => 0
--        ) (inl Bool 4)
--
--         (A)  7
--
--         (B)  case inl Bool 4 of
--                inl n => n + 3
--              | inr b => 0
--
--         (C)  4 + 3

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--             case inl Bool 4 of
--               inl n => n + 3
--               | inr b => 0
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
--            let fact = λx:Nat.
--                         if x=0 then 1 else x * (fact (pred x))) in
--            fact 3.
--
--  Note that the right-hand side of this binder mentions
--  `fact`, the variable being bound - something that is not
--  allowed according to the way we defined `let` above.

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
--            fact = λax:Nat.
--                      if x=0 then 1 else x * (fact (pred x)))
--
--  we will write:

--  fact =
--            fix
--              (λaf:Nat → Nat.
--                 λx:Nat.
--                    if x=0 then 1 else x * (f (pred x)))

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
--  `fact 3 = fix F 3`, where
--
--          F = (λf. λx. if x=0 then 1 else x * (f (pred x)))
--
--  (type annotations are omitted for brevity).
--
--          fix F 3
--
--      ⟶ fixAbs + app₁
--
--          (λx. if x=0 then 1 else x * (fix F (pred x))) 3
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
--          3 * ((λx. if x=0 then 1 else x * (fix F (pred x))) (pred 3))
--
--      ⟶ predNat + mult₂ + app₂
--
--          3 * ((λx. if x=0 then 1 else x * (fix F (pred x))) 2)
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
--          3 * (2 * ((λx. if x=0 then 1 else x * (fix F (pred x))) (pred 2)))
--
--      ⟶ predNat + 2 x mult₂ + app₂
--
--          3 * (2 * ((λx. if x=0 then 1 else x * (fix F (pred x))) 1))
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
--          3 * (2 * (1 * ((λx. if x=0 then 1 else x * (fix F (pred x))) (pred 1))))
--
--      ⟶ predNat + 3 × mult₂ + app₂
--
--          3 * (2 * (1 * ((λx. if x=0 then 1 else x * (fix F (pred x))) 0)))
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

--  One important point to note is that, unlike definitions
--  in Lean, there is nothing to prevent functions defined
--  using `fix` from diverging.

--   ----------------------------------------

--  _Quiz:_

--  Is this a well-typed Stlc term? What does it evaluate
--  to?
--
--              fix (λf: Nat→Nat. λx:Nat. f x) 0
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
--
--  - they are n-ary (rather than binary);
--  - they are accessed by *label* (rather than position).

--  Syntax:
--
--             t ::=                          Terms
--                 | ...
--                 | {i₁=t₁, ..., in=tn}        record
--                 | t.i                        projection
--
--             v ::=                          Values
--                 | ...
--                 | {i₁=v₁, ..., in=vn}         record value
--
--             τ ::=                          Types
--                 | ...
--                 | {i₁:τ₁, ..., in:τn}         record type

--  Note that this is a quite informal definition compared
--  to previous ones:
--
--  - it uses "`...`" in the syntax for records
--
--  - it omits a usual side condition that the labels of a
--    record should not contain repetitions.

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

--  - In the first rule, `ti` must be the leftmost field
--    that is not a value;
--
--  - In the last rule, there should be only one field
--    called `i`, and all the other fields must contain
--    values.

--  The typing rules are also simple:
--
--                     Γ ⊢ t₁ ⦂ τ₁     ...     Γ ⊢ tn ⦂ Tn
--                -----------------------------------------------------        (rcd)
--                Γ ⊢ {i₁=t₁, ..., in=tn} ⦂ {i₁:τ₁, ..., in:Tn}
--
--
--                            Γ ⊢ t ⦂ {..., i:Ti, ...}
--                          ---------------------------------                  (proj)
--                                Γ ⊢ t.i ⦂ Ti

--  Formalizing all this would take some work.

--  ### Exercise: Formalizing the Extensions

-- Built on 2026-09-02 02:50 UTC

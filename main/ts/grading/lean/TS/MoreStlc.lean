import TS.StlcProp
import LF.CustomTactics

import ComparatorAutograderLib
import SFLCompat

--  # MoreStlc: More on the Simply Typed Lambda-Calculus

--  ## Simple Extensions to STLC

--  The simply typed lambda-calculus has a rich enough structure to make
--  its theoretical properties interesting, but it is not much of a
--  programming language!
--
--  In this chapter, we begin to close the gap with real-world languages by
--  introducing a number of familiar features that have straightforward
--  treatments at the level of typing.

--  ### Numbers

--  As we saw in the `StlcExtended` exercises at the end of the StlcProp
--  chapter, adding types, constants, and primitive operations for natural
--  numbers is easy - basically just a matter of combining the Types and
--  Stlc chapters. Adding more realistic numeric types like machine
--  integers and floats is also straightforward, though of course the
--  specifications of the numeric primitives become more fiddly.

--  When writing a complex expression, it is useful to be able to give
--  names to some of its subexpressions to avoid repetition and increase
--  readability. Most languages provide one or more ways of doing this. In
--  OCaml and Haskell, for example, we can write `let x = t₁ in t₂` to mean
--  "reduce the expression `t₁` to a value and bind the name `x` to this
--  value while reducing `t₂`."
--
--  Our `let`-binder follows OCaml in choosing a standard *call-by-value*
--  evaluation order, where the `let`-bound term must be fully reduced
--  before reduction of the `let`-body can begin. The typing rule `let`
--  tells us that the type of a `let` can be calculated by calculating the
--  type of the `let`-bound term, extending the context with a binding with
--  this type, and in this enriched context calculating the type of the
--  body (which is then the type of the whole `let` expression).
--
--  At this point in the book, it's probably easier simply to look at the
--  rules defining this new feature than to wade through a lot of English
--  text conveying the same information. Here they are:

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

--  Our functional programming examples in Lean have made frequent use of
--  *pairs* of values. The type of such a pair is called a *product type*.
--
--  The formalization of pairs is almost too simple to be worth discussing.
--  However, let's look briefly at the various parts of the definition to
--  emphasize the common pattern.

--  In Lean, there are two ways of extracting the components of a pair:
--  *pattern matching* and the projection operators `fst` and `snd`. Just
--  for fun, let's do our pairs the latter way. For example, here's how
--  we'd write a function that takes a pair of numbers and returns the pair
--  of their sum and difference:
--
--             λx : Nat × Nat.
--                let sum = fst x + snd x in
--                let diff = fst x - snd x in
--                (sum, diff)

--  Adding pairs to the simply typed lambda-calculus, then, involves adding
--  two new forms of term - pairing, written `(t₁,t₂)`, and projection,
--  written `fst t` for the first projection from `t` and `snd t` for the
--  second projection - plus one new type constructor, `τ₁ × τ₂`, called
--  the *product* of `τ₁` and `τ₂`.

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

--  For reduction, we need several new rules specifying how pairs and
--  projection behave.

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

--  Rules `fstPair` and `sndPair` say that, when a fully reduced pair meets
--  a first or second projection, the result is the appropriate component.
--  The congruence rules `fst₁` and `snd₁` allow reduction to proceed under
--  projections, when the term being projected from has not yet been fully
--  reduced. `pair₁` and `pair₂` reduce the parts of pairs: first the left
--  part, and then - when a value appears on the left - the right part. The
--  ordering arising from the use of the metavariables `v` and `t` in these
--  rules enforces a left-to-right evaluation strategy for pairs. (Note the
--  implicit convention that metavariables like `v` and `v₁` can only
--  denote values.) We've also added a clause to the definition of values,
--  above, specifying that `(v₁,v₂)` is a value. The fact that the
--  components of a pair value must themselves be values ensures that a
--  pair passed as an argument to a function will be fully reduced before
--  the function body starts executing.

--  The typing rules for pairs and projections are straightforward.

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

--  `pair` says that `(t₁, t₂)` has type `τ₁ × τ₂` if `t₁` has type `τ₁`
--  and `t₂` has type `τ₂`. Conversely, `fst` and `snd` tell us that, if
--  `t` has a product type `τ₁ × τ₂` (i.e., if it will reduce to a pair),
--  then the types of the projections from this pair are `τ₁` and `τ₂`.

--  ### Unit

--  Another handy base type is the singleton type `Unit`.

--  It has a single element - the term constant `unit` (with a small `u`) -
--  and a typing rule making `unit` an element of `Unit`. We also add
--  `unit` to the set of possible values - indeed, `unit` is the *only*
--  possible result of reducing an expression of type `Unit`.

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

--  It may seem a little strange to bother defining a type that has just
--  one element -- after all, wouldn't every computation living in such a
--  type be trivial?
--
--  This is a fair question, and indeed in the STLC the `Unit` type is not
--  especially critical (though we'll see two uses for it below). Where
--  `Unit` really comes in handy is in richer languages with *side effects*
--  -- e.g., assignment statements that mutate variables or pointers,
--  exceptions and other sorts of nonlocal control structures, etc. In such
--  languages, it is convenient to have a type for the (trivial) result of
--  an expression that is evaluated only for its effect.

--   ----------------------------------------

--  _Quiz:_

--  Is `unit` the only term of type `Unit`?
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  ### Sums

--  Many programs need to deal with values that can take two distinct
--  forms. For example, we might identify students in a university database
--  using *either* their name *or* their id number. A search function might
--  return *either* a matching value *or* an error code.
--
--  These are specific examples of a binary *sum type* (sometimes called a
--  *disjoint union*), which describes a set of values drawn from one of
--  two given types, e.g.:
--
--             Nat + Bool

--  We create elements of these types by *tagging* elements of the
--  component types. For example, if `n` is a `Nat` then `inl n` is an
--  element of `Nat + Bool`; similarly, if `b` is a `Bool` then `inr b` is
--  a `Nat + Bool`. The names of the tags `inl` and `inr` arise from
--  thinking of them as functions
--
--             inl ⦂ Nat  → Nat + Bool
--             inr ⦂ Bool → Nat + Bool
--
--  that "inject" elements of `Nat` or `Bool` into the left and right
--  components of the sum type `Nat + Bool`. (But note that we don't
--  actually treat them as functions in the way we formalize them: `inl`
--  and `inr` are keywords, and `inl t` and `inr t` are primitive syntactic
--  forms, not function applications.)

--  In general, the elements of a type `τ₁ + τ₂` consist of the elements of
--  `τ₁` tagged with the token `inl`, plus the elements of `τ₂` tagged with
--  `inr`.
--
--  (As we've seen in Lean programming, one important use of sums is
--  signaling errors:
--
--            div ⦂ Nat → Nat → (Nat + Unit)
--            div =
--              λx:Nat. λy:Nat,
--                if iszero y then
--                  inr unit
--                else
--                  inl ...

--  The type `Nat + Unit` above is in fact isomorphic to `Option Nat` in
--  Lean - i.e., it's easy to write functions that translate back and
--  forth.
--
--  To *use* elements of sum types, we introduce a `case` construct (a very
--  simplified form of Lean's `match`) to destruct them. For example, the
--  following procedure converts a `Nat + Bool` into a `Nat`:

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
--  We use the type annotations on `inl` and `inr` to make the typing
--  relation deterministic (each term has at most one type), as we did for
--  functions.

--  Without this extra information, the typing rule `inl`, for example,
--  would have to say that, once we have shown that `t₁` is an element of
--  type `τ₁`, we can derive that `inl t₁` is an element of `τ₁ + τ₂` for
--  *any* type `τ₂`. For example, we could derive both
--  `inl 5 : Nat + Nat`and `inl 5 : Nat + Bool` (and infinitely many other
--  types). This peculiarity (technically, a failure of uniqueness of
--  types) would mean t hat we cannot build a typechecking algorithm simply
--  by "reading the rules from bottom to top" as we could for all the other
--  features seen so far.
--
--  There are various ways to deal with this difficulty. One simple one --
--  which we've adopted here -- forces the programmer to explicitly
--  annotate the "other side" of a sum type when performing an injection.
--  This is a bit heavy for programmers (so real languages adopt other
--  solutions), but it is easy to understand and formalize.

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

--  The typing features we have seen can be classified into *base types*
--  like `Bool`, and *type constructors* like `→` and `×` that build new
--  types from old ones. Another useful type constructor is `List`. For
--  every type `τ`, the type `List τ` describes finite-length lists whose
--  elements are drawn from `τ`.
--
--  In principle, we could encode lists using pairs, sums, unit, and
--  *recursive* types. But giving semantics to recursive types is
--  non-trivial. Instead, we'll just discuss the special case of lists
--  directly.
--
--  Below we give the syntax, semantics, and typing rules for lists. Except
--  for the fact that explicit type annotations are mandatory on `nil` and
--  cannot appear on `cons`, these lists are essentially identical to those
--  we built in Rocq. We use `case`, rather than `head` and `tail`
--  operators, to destruct lists, to avoid dealing with questions like
--  "what is the `head` of the ∅ list?"
--
--  For example, here is a function that calculates the sum of the first
--  two elements of a list of numbers:
--
--  λ x:List Nat. case x of nil => 0 | a :: x' => case x' of nil => a | b
--  :: x'' => a + b

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

--  Another facility found in most programming languages (including Lean)
--  is the ability to define recursive functions. For example, we would
--  like to be able to define and use the factorial function like this:
--
--            let fact = λx:Nat.
--                         if x=0 then 1 else x * (fact (pred x))) in
--            fact 3.
--
--  Note that the right-hand side of this binder mentions `fact`, the
--  variable being bound - something that is not allowed according to the
--  way we defined `let` above.

--  (The body of a `let` is typechecked in the same context as the `let`
--  itself, which means that the recursive occurrence of `fact` in the body
--  will not have a type in the context when it is looked up by the `var`
--  rule.)

--  Changing the `let` rule to handle "recursive definitions" like this is
--  possible, but it requires some extra effort -- e.g., passing around an
--  extra "environment" of recursive function definitions in the definition
--  of the `step` relation. We're going to take a simpler path here.

--  Here is another way of presenting recursive functions that is a bit
--  more verbose but equally powerful and much more straightforward to
--  formalize: instead of writing recursive definitions, we will define a
--  *fixed-point operator* called `fix` that performs the "unfolding" of
--  the recursive definition in the right-hand side as needed, during
--  reduction.
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

--  We can derive the latter from the former as follows:
--
--  - In the right-hand side of the definition of `fact`, replace recursive
--    references to `fact` by a fresh variable `f`.
--
--  - Add an abstraction binding `f` at the front, with an appropriate type
--    annotation. (Since we are using `f` in place of `fact`, which had
--    type `Nat→Nat`, we should require `f` to have the same type.) The new
--    abstraction has type `(Nat→Nat) → (Nat→Nat)`.
--
--  - Apply `fix` to this abstraction. This application has type `Nat→Nat`.
--
--  - Use all of this as the right-hand side of an ordinary `let`-binding
--    for `fact`.

--  For the mathematically inclined, the intuition here is that the
--  higher-order function `f` passed to `fix` is a *generator* for the
--  `fact` function: if `f` is applied to a function that "approximates"
--  the desired behavior of `fact` up to some number `n` (that is, a
--  function that returns correct results on inputs less than or equal to
--  `n` but we don't care what it does on inputs greater than `n`), then
--  `f` returns a slightly better approximation to `fact` -- a function
--  that returns correct results for inputs up to `n+1`. Applying `fix` to
--  this generator returns its *fixed point*, which is a function that
--  gives the desired behavior for all inputs `n`.
--
--  (The term "fixed point" is used here in exactly the same sense as in
--  ordinary mathematics, where a fixed point of a function `f` is an input
--  `x` such that `f(x) = x`. Here, a fixed point of a function `F` of type
--  `(Nat→Nat)→(Nat→Nat)` is a function `f` of type `Nat→Nat` such that
--  `F f` behaves the same as `f`.)

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

--  Let's see how `fixAbs` works by reducing `fact 3 = fix F 3`, where
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
--  The simply typed lambda-calculus with fixed points is a famous and
--  extensively studied system. It is often called *PCF* because it is a
--  simple language of "partial computable functions".

--   ----------------------------------------

--  _Quiz:_

--  Is this a well-typed Stlc term? What does it evaluate to?
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

--  Which of the following are (intuitively) true for Stlc + fixpoints.
--
--  (A) deterministic
--
--  (B) progress
--
--  (C) preservation
--
--  (D) normalizing (i.e. every well-typed term reduces to a normal form)

--   ----------------------------------------

--  ### Exercise (1 star): halve_fix (Optional) ⭐

--  Translate this informal recursive definition into one using `fix`:
--
--            halve =
--              λx:Nat.
--                 if x=0 then 0
--                 else if (pred x)=0 then 0
--                 else 1 + (halve (pred (pred x)))

--            halve =
--                fix
--                  (λf:Nat→Nat.
--                     λx:Nat.
--                        if x=0 then 0
--                        else if (pred x)=0 then 0
--                        else 1 + (f (pred (pred x))))

--  ### Exercise (1 star): fact_steps (Optional) ⭐

--  Write down the sequence of steps that the term `fact 1` goes through to
--  reduce to a normal form (assuming the usual reduction rules for
--  arithmetic operations.

--              fact 1
--            = fix (λf:Nat→Nat. λx:Nat. if x=0 then 1 else x * (f (pred x))) 1
--          ⟶ (λx: Nat, if x = 0 then 1 else x * (fact (pred x))) 1
--          ⟶ if 1 = 0 then 1 else 1 * (fact (pred 1))
--          ⟶ 1 * (fact (pred 1))
--          ⟶ 1 * ((λx:Nat. if x=0 then 1 else x * (fact (pred x))) (pred 1))
--          ⟶ 1 * ((λx:Nat. if x=0 then 1 else x * (fact (pred x))) 0)
--          ⟶ 1 * (if 0=0 then 1 else 0 * (fact (pred 0)))
--          ⟶ 1 * 1
--          ⟶ 1
--
--  Also see the solution to exercise `fact_example` below.

--  The ability to form the fixed point of a function of type `τ→τ` for any
--  `τ` has some surprising consequences. In particular, it implies that
--  *every* type is inhabited by some term. To see this, observe that, for
--  every type `τ`, we can define the term:
--
--          fix (λx:τ,x)
--
--  By `fix` and `abs`, this term has type `τ`. By `fixAbs` it reduces to
--  itself, over and over again. Thus it is a *diverging element* of `τ`.
--
--  More usefully, here's an example using `fix` to define a two-argument
--  recursive function:
--
--          equal =
--            fix
--              (\eq:Nat→Nat→Bool.
--                 \m:Nat. \n:Nat.
--                   if m=0 then iszero n
--                   else if n=0 then false
--                   else eq (pred m) (pred n))
--
--  And finally, here is an example where `fix` is used to define a *pair*
--  of recursive functions (illustrating the fact that the type `τ₁` in the
--  rule `fix` need not be a function type):
--
--          let evenodd =
--               fix
--                 (\eo: ((Nat → Nat) * (Nat → Nat)).
--                    (\n:Nat. if0 n then 1 else (snd eo (pred n)),
--                     \n:Nat. if0 n then 0 else (fst eo (pred n)))) in
--          let even = fst evenodd in
--          let odd  = snd evenodd in
--          (even 3, even 4)}

--  ## Records

--  As a final example of a basic extension of the STLC, let's look briefly
--  at how to define *records* and their types. Intuitively, records can be
--  obtained from pairs by two straightforward generalizations: they are
--  n-ary (rather than just binary) and their fields are accessed by
--  *label* (rather than position).

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

--  The generalization from products should be pretty obvious. But it's
--  worth noticing the ways in which what we've actually written is even
--  *more* informal than the informal syntax we've used in previous
--  sections and chapters: we've used "`...`" in several places to mean
--  "any number of these," and we've omitted explicit mention of the usual
--  side condition that the labels of a record should not contain any
--  repetitions.

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

--  Again, these rules are a bit informal. For example, the first rule is
--  intended to be read "if `ti` is the leftmost field that is not a value
--  and if `ti` steps to `ti'`, then the whole record steps..." In the last
--  rule, the intention is that there should be only one field called `i`,
--  and that all the other fields must contain values.

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

--  There are several ways to approach formalizing the above definitions.
--
--  - We can directly formalize the syntactic forms and inference rules,
--    staying as close as possible to the form we've given them above. This
--    is conceptually straightforward, and it's probably what we'd want to
--    do if we were building a real compiler (in particular, it will allow
--    us to print error messages in the form that programmers will find
--    easy to understand). But the formal versions of the rules will not be
--    very pretty or easy to work with, because all the `...`s above will
--    have to be replaced with explicit quantifications or comprehensions.
--    For this reason, records are not included in the extended exercise at
--    the end of this chapter. (It is still useful to discuss them
--    informally here because they will help motivate the addition of
--    subtyping to the type system when we get to the Sub chapter.)
--
--  - Alternatively, we could look for a smoother way of presenting records
--    -- for example, a binary presentation with one constructor for the ∅
--    record and another constructor for adding a single field to an
--    existing record, instead of a single monolithic constructor that
--    builds a whole record at once. This is the right way to go if we are
--    primarily interested in studying the metatheory of the calculi with
--    records, since it leads to clean and elegant definitions and proofs.
--
--  - Finally, if we like, we can avoid formalizing records altogether, by
--    stipulating that record notations are just informal shorthands for
--    more complex expressions involving pairs and product types. We sketch
--    this approach in the next section.

--  Let's see how records can be encoded using just pairs and `unit`. (This
--  clever encoding, as well as the observation that it also extends to
--  systems with subtyping, is due to Luca Cardelli.)
--
--  First, observe that we can encode arbitrary-size *tuples* using nested
--  pairs and the `unit` value. To avoid overloading the pair notation
--  `(t₁,t₂)`, we'll use curly braces without labels to write down tuples,
--  so `{}` is the ∅ tuple, `{5}` is a singleton tuple, `{5,6}]`is a
--  2-tuple (morally the same as a pair), `{5,6,7}` is a triple, etc.
--
--            {}                 ⟶  unit
--            {t₁, t₂, ..., tn}  ⟶  (t₁, trest)
--                                      where {t₂, ..., tn} ⟶ trest
--
--  Similarly, we can encode tuple types using nested product types:
--
--            {}                 ⟶  Unit
--            {τ₁, τ₂, ..., Tn}  ⟶  τ₁ * TRest
--                                      where {τ₂, ..., τn} ⟶ τn
--
--  The operation of projecting a field from a tuple can be encoded using a
--  sequence of second projections followed by a first projection:
--
--            t.0        ⟶  fst t
--            t.(n+1)    ⟶  (snd t).n
--
--  Next, suppose that there is some total ordering on record labels, so
--  that we can associate each label with a unique natural number. This
--  number is called the *position* of the label. For example, we might
--  assign positions like this:
--
--            LABEL   POSITION
--            a       0
--            b       1
--            c       2
--            ...     ...
--            bar     1395
--            ...     ...
--            foo     4460
--            ...     ...
--
--  We use these positions to encode record values as tuples (i.e., as
--  nested pairs) by sorting the fields according to their positions. For
--  example:
--
--            {a=5,b=6}       ⟶   {5,6}
--            {a=5,c=7}       ⟶   {5,unit,7}
--            {c=7,a=5}       ⟶   {5,unit,7}
--            {c=5,b=3}       ⟶   {unit,3,5}
--            {f=8,c=5,a=7}   ⟶   {7,unit,5,unit,unit,8}
--            {f=8,c=5}       ⟶   {unit,unit,5,unit,unit,8}
--
--  Note that each field appears in the position associated with its label,
--  that the size of the tuple is determined by the label with the highest
--  position, and that we fill in unused positions with `unit`.
--
--  We do exactly the same thing with record types:
--
--            {a:Nat,b:Nat}       ⟶   {Nat,Nat}
--            {c:Nat,a:Nat}       ⟶   {Nat,Unit,Nat}
--            {f:Nat,c:Nat}       ⟶   {Unit,Unit,Nat,Unit,Unit,Nat}
--
--  Finally, record projection is encoded as a tuple projection from the
--  appropriate position:
--
--            t.l ⟶ t.(position of l)
--
--  It is not hard to check that all the typing rules for the original
--  "direct" presentation of records are validated by this encoding. (The
--  reduction rules are "almost validated" -- not quite, because the
--  encoding reorders fields.)

--  Of course, this encoding will not be very efficient if we happen to use
--  a record with label `foo`! But things are not actually as bad as they
--  might seem: for example, if we assume that our compiler can see the
--  whole program at the same time, we can *choose* the numbering of labels
--  so that we assign small positions to the most frequently used labels.
--  Indeed, there are industrial compilers that essentially do this!

--  Just as products can be generalized to records, sums can be generalized
--  to n-ary labeled types called *variants*. Instead of `τ₁+τ₂`, we can
--  write something like `<l₁:τ₁,l₂:τ₂,...ln:τn>` where `l₁`,`l₂`,... are
--  field labels which are used both to build instances and as case arm
--  labels.
--
--  These n-ary variants give us almost enough mechanism to build arbitrary
--  inductive data types like lists and trees from scratch -- the only
--  thing missing is a way to allow *recursion* in type definitions. We
--  won't cover this here, but detailed treatments can be found in many
--  textbooks -- e.g., Types and Programming Languages (Pierce, 2002).

--  ### Exercise: Formalizing the Extensions

--  In this series of exercises, you will formalize some of the extensions
--  described in this chapter. We've provided the necessary additions to
--  the syntax of terms and types, and we've included a few examples that
--  you can test your definitions with to make sure they are working as
--  expected. You'll fill in the rest of the definitions and extend all the
--  proofs accordingly.
--
--  To get you started, we've provided implementations for:
--
--  - numbers
--  - sums
--  - lists
--  - unit
--
--  You need to complete the implementations for:
--
--  - pairs
--  - let (which involves binding)
--  - fix
--
--  A good strategy is to work on the extensions one at a time (first
--  pairs, then let, then fix), in separate passes, rather than trying to
--  do all three at once in a single pass. For each definition or proof,
--  begin by reading carefully through the parts that are provided for you,
--  referring to the text in the Stlc chapter for high-level intuitions and
--  the embedded comments for detailed mechanics.

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

--  Note that, for brevity, we've omitted booleans and instead provided a
--  single `if0` form combining a zero test and a conditional. That is,
--  instead of writing
--
--             if x = 0 then ... else ...
--
--  we'll write this:
--
--             if0 x then ... else ...

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation)
syntax:50 stlcTy:51 " × " stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " + " stlcTy:50 : stlcTy
syntax:51 " [ " stlcTy:50  " ] " : stlcTy

scoped macro_rules (kind := Stlc.tyBracket)
  | `(<{ ~$τ:term }>)    => pure τ
  | `(<{ ($τ:stlcTy) }>) => `(<{ $τ:stlcTy }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat" => `(Ty.nat)
      | "Unit" => `(Ty.unit)
      | _ => `(($x : Ty))
  | `(<{ [ $τ₁:stlcTy ] }>) => `(Ty.list <{ $τ₁:stlcTy }>)
  | `(<{ $τ₁:stlcTy → $τ₂:stlcTy }>)  => `(Ty.arrow <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
  | `(<{ $τ₁:stlcTy × $τ₂:stlcTy }>)  => `(Ty.prod <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
  | `(<{ $τ₁:stlcTy + $τ₂:stlcTy }>)  => `(Ty.sum <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
  | `(<{ $τ₁:stlcTy -> $τ₂:stlcTy }>) => `(Ty.arrow <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)

#check <{ Nat -> Nat }>
#check <{ List Nat }>
#check <{ (Nat × Nat) -> Nat }>
#check <{ (Nat + Nat) → Nat }>

scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:61 " * " stlcTm:60 : stlcTm
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

open Lean in
scoped macro_rules (kind := Stlc.tmBracket)
  | `(<{ ~$e:term }>)    => pure e
  | `(<{ ($t:stlcTm) }>) => `(<{ $t:stlcTm }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat"  => Macro.throwErrorAt x "`Nat` is a type, not a term"
      | "Unit"  => Macro.throwErrorAt x "`Unit` is a type, not a term"
      | "succ" => Macro.throwErrorAt x "`succ` must be applied to an argument"
      | "fst" => Macro.throwErrorAt x "`fst` must be applied to an argument"
      | "snd" => Macro.throwErrorAt x "`snd` must be applied to an argument"
      | "nil" => Macro.throwErrorAt x  "`nil` must be applied to an argument"
      | "pred" => Macro.throwErrorAt x "`pred` must be applied to an argument"
      | "inl" => Macro.throwErrorAt x "`inl` must be applied to two arguments"
      | "inr" => Macro.throwErrorAt x "`inr` must be applied to two arguments"
      | "fix" => Macro.throwErrorAt x  "`fix` must be applied to an argument"
      | "unit" =>  `(Tm.unit)
      | _      => `(Tm.var $(quote x.getId.toString))
  | `(<{ λ $x : $τ . $t }>) => do
      `(Tm.abs $(← Stlc.varStr x) <{ $τ:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ $t₁:stlcTm $t₂:stlcTm }>) =>
      match t₁ with
      | `(stlcTm| $f:ident) =>
          match f.getId.toString with
          | "succ" => `(Tm.succ <{ $t₂:stlcTm }>)
          | "pred" => `(Tm.pred <{ $t₂:stlcTm }>)
          | "fst" => `(Tm.fst <{ $t₂:stlcTm }>)
          | "snd" => `(Tm.snd <{ $t₂:stlcTm }>)
          | "inl" => Macro.throwErrorAt f  "`inl` must be applied to two arguments"
          | "inr" => Macro.throwErrorAt f  "`inr` must be applied to two arguments"
          | "fix" =>  `(Tm.fix  <{ $t₂:stlcTm }>)
          | _      => `(Tm.app  <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
      | _ => `(Tm.app <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)

  | `(<{ $n:num }>)      => `(Tm.const $n)
  | `(<{ $t₁:stlcTm * $t₂:stlcTm }>) => `(Tm.mult <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ if0 $c then $t else $e }>) =>
      `(Tm.ite0 <{ $c:stlcTm }> <{ $t:stlcTm }> <{ $e:stlcTm }>)

  | `(<{ inl $τ $t}>) => `(Tm.sumInl <{ $τ:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ inr $τ $t}>) => `(Tm.sumInr <{ $τ:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ case $t of inl $x₁ => $t₁ | inr $x₂ => $t₂}>) => do
      `(Tm.sumCase <{ $t:stlcTm }> $(← Stlc.varStr x₁) <{ $t₁:stlcTm }>
          $(← Stlc.varStr x₂) <{ $t₂:stlcTm }>)

  | `(<{ nil $τ }>) => `(Tm.listNil <{ $τ:stlcTy }>)
  | `(<{ $t₁:stlcTm :: $t₂:stlcTm }>) => `(Tm.listCons <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ case $t of nil => $t₁ | $x₁ :: $x₂ => $t₂}>) => do
      `(Tm.listCase <{ $t:stlcTm }> <{ $t₁:stlcTm }>
          $(← Stlc.varStr x₁) $(← Stlc.varStr x₂) <{ $t₂:stlcTm }>)

  | `(<{ ( $t₁:stlcTm , $t₂:stlcTm ) }>) => `(Tm.pair <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)

  | `(<{ let $x = $t₁ in $t₂ }>) => do
    `(Tm.letIn $(← Stlc.varStr x) <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)

#check <{ case x :: y of nil => 0 | x :: y => 1 }>
#check <{ inl Nat (3, 4) }>

open Lean in
/-- Is `s` usable as a bare variable in `stlcTm` rather than as reserved syntax? -/
def isPlainTmVarName (s : String) : Bool :=
  Stlc.isPlainName s && s != "Nat" && s != "succ" && s != "pred" && s != "unit"
    && s != "Unit" && s != "inl" && s != "inr" && s != "if0" && s != "case" && s != "nil"
    && s != "fix"

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTy` concrete syntax from a `Ty` value. -/
partial def delabTyInner : DelabM (TSyntax `stlcTy) := do
  let stx ←
    match_expr ← getExpr with
    | Ty.nat => `(stlcTy| $(mkIdent `Nat):ident)
    | Ty.unit => `(stlcTy| $(mkIdent `Unit):ident)
    | Ty.arrow _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a → $b)
    | Ty.prod _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a × $b)
    | Ty.sum _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a + $b)
    | Ty.list _ => do
        let b ← withAppArg delabTyInner
        `(stlcTy| [$b] )
    | _ => do
        match ← delab with
        | `($i:ident) => `(stlcTy| $i:ident)
        | e => `(stlcTy| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTm` concrete syntax from a `Tm` value. -/
partial def delabTmInner : DelabM (TSyntax `stlcTm) := do
  let stx ←
    match_expr ← getExpr with
    | Tm.var _ => do
        let x ← withAppArg delab
        match x with
        | `($s:str) =>
            if isPlainTmVarName s.getString then
              `(stlcTm| $(mkIdent (Name.mkSimple s.getString)):ident)
            else
              let var : Term := mkIdent ``Tm.var
              `(stlcTm| ~($var $x))
        | _ =>
            let var : Term := mkIdent ``Tm.var
            `(stlcTm| ~($var $x))
    | Tm.const _ => do
        let n ← withAppArg delab
        match n with
        | `($n:num) => `(stlcTm| $n:num)
        | _ =>
            let const : Term := mkIdent ``Tm.const
            `(stlcTm| ~($const $n))
    | Tm.app _ _ => do
        let f ← withAppFn <| withAppArg delabTmInner
        let a ← withAppArg delabTmInner
        `(stlcTm| $f $a)
    | Tm.abs _ _ _ => do
        let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let τ ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| λ $x : $τ . $t)
    | Tm.letIn _ _ _ => do
        let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let t₁ ← withAppFn <| withAppArg delabTmInner
        let t₂ ← withAppArg delabTmInner
        `(stlcTm| let $x = $t₁ in $t₂)
    | Tm.succ _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `succ):ident $t)
    | Tm.pred _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `pred):ident $t)
    | Tm.mult _ _ => do
        let a ← withAppFn <| withAppArg delabTmInner
        let b ← withAppArg delabTmInner
        `(stlcTm| $a * $b)
    | Tm.ite0 _ _ _ => do
        let c ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let t ← withAppFn <| withAppArg delabTmInner
        let e ← withAppArg delabTmInner
        `(stlcTm| if0 $c then $t else $e)
    | Tm.sumInl _ _ => do
        let τ ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| inl $τ $t)
    | Tm.sumInr _ _ => do
        let τ ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| inr $τ $t)
    | Tm.sumCase _ _ _ _ _ => do
        let c  ← withAppFn <| withAppFn <| withAppFn <| withAppFn <| withAppArg delabTmInner
        let x₁ ← withAppFn <| withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let t₁ ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let x₂ ← withAppFn <| withAppArg Stlc.delabVarInner
        let t₂ ← withAppArg delabTmInner
        `(stlcTm| case $c of inl $x₁ => $t₁ | inr $x₂ => $t₂)
    | Tm.listNil _ => do
        let t ← withAppArg delabTyInner
        `(stlcTm| nil $t)
    | Tm.listCons _ _ => do
        let a ← withAppFn <| withAppArg delabTmInner
        let b ← withAppArg delabTmInner
        `(stlcTm| $a :: $b)
    | Tm.pair _ _ => do
        let a ← withAppFn <| withAppArg delabTmInner
        let b ← withAppArg delabTmInner
        `(stlcTm| ( $a , $b ) )
    | Tm.fst _ => do
        let b ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `fst):ident $b )
    | Tm.snd _ => do
        let b ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `snd):ident $b )
    | Tm.listCase _ _ _ _ _ => do
        let c ←  withAppFn <| withAppFn <| withAppFn <| withAppFn <| withAppArg delabTmInner
        let t₁ ← withAppFn <| withAppFn <| withAppFn <| withAppArg delabTmInner
        let x₁ ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let x₂ ← withAppFn <| withAppArg Stlc.delabVarInner
        let t₂ ← withAppArg delabTmInner
        `(stlcTm| case $c of nil => $t₁ | $x₁ :: $x₂ => $t₂)
    | Tm.fix _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `fix):ident $t)
    | Tm.unit => do
        `(stlcTm| $(mkIdent `unit):ident)
    | _ => do
        -- `subst` is defined below, so it is matched by name rather than with
        -- `match_expr`; a substitution prints in its own bracket notation.
        let e ← getExpr
        if e.getAppFn.constName? == some `SltcExtended.subst && e.getAppNumArgs == 3 then
          let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
          let s ← withAppFn <| withAppArg delabTmInner
          let t ← withAppArg delabTmInner
          `(stlcTm| [$x := $s] $t)
        else
          match ← delab with
          | `($i:ident) => `(stlcTm| $i:ident)
          | e => `(stlcTm| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcExtended.Ty.nat, delab app.StlcExtended.Ty.arrow, delab app.StlcExtended.Ty.unit,
  delab app.StlcExtended.Ty.prod, delab app.StlcExtended.Ty.sum, delab app.StlcExtended.Ty.list]
def delabTy : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Ty.nat => true | Ty.arrow _ _ => true
    | Ty.prod _ _ => true | Ty.sum _ _ => true
    | Ty.list _ => true | Ty.unit => true | _ => false
  match ← delabTyInner with
  | `(stlcTy| ~$e) => pure e
  | e => `(<{ $e:stlcTy }>)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcExtended.Tm.var, delab app.StlcExtended.Tm.app, delab app.StlcExtended.Tm.abs,
  delab app.StlcExtended.Tm.const, delab app.StlcExtended.Tm.succ, delab app.StlcExtended.Tm.pred,
  delab app.StlcExtended.Tm.mult, delab app.StlcExtended.Tm.ite0, delab app.StlcExtended.Tm.listNil,
  delab app.StlcExtended.Tm.listCons, delab app.StlcExtended.Tm.listCase,
  delab app.StlcExtended.Tm.sumInl, delab app.StlcExtended.Tm.sumInr,
  delab app.StlcExtended.Tm.sumCase, delab app.StlcExtended.Tm.pair,
  delab app.StlcExtended.Tm.fst, delab app.StlcExtended.Tm.snd, delab app.StlcExtended.Tm.unit,
  delab app.StlcExtended.Tm.letIn, delab app.StlcExtended.Tm.fix ]
def delabTm : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Tm.var _ => true | Tm.app _ _ => true | Tm.abs _ _ _ => true
    | Tm.const _ => true | Tm.succ _ => true | Tm.pred _ => true
    | Tm.mult _ _ => true | Tm.ite0 _ _ _ => true
    | Tm.unit => true | Tm.fix _ => true | Tm.letIn _ _ _ => true
    | Tm.sumInl _ _ => true | Tm.sumInr _ _ => true | Tm.sumCase _ _ _ _ _ => true
    | Tm.listNil _ => true | Tm.listCons _ _ => true | Tm.listCase _ _ _ _ _ => true
    | Tm.pair _ _ => true | Tm.fst _ => true | Tm.snd _ => true
    | _ => false
  match ← delabTmInner with
  | `(stlcTm| ~($e)) => pure e
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
--  END DETAILS

--  ### Exercise (3 stars): STLCExtended.subst (Manually graded) ⭐⭐⭐

section
set_option hygiene false in
local macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- pure STLC
  | .var y =>
      if x = y then s else t
  | <{ λ ~y : ~τ . ~t₁}> =>
      if x = y then t else <{ λ ~y : ~τ . [~x := ~s] ~t₁ }>
  | <{ ~t₁ ~t₂ }> =>
      <{ ([~x := ~s] ~t₁) ([~x := ~s] ~t₂) }>
  -- numbers
  | .const _ =>
      t
  | <{ succ ~t₁ }> =>
      <{ succ ([~x := ~s] ~t₁) }>
  | <{ pred ~t₁ }> =>
      <{ pred ([~x := ~s] ~t₁) }>
  | <{ ~t₁ * ~t₂ }> =>
      <{ ([~x := ~s] ~t₁) * ([~x := ~s] ~t₂) }>
  | <{ if0 ~t₁ then ~t₂ else ~t₃ }> =>
      <{ if0 [~x := ~s] ~t₁ then [~x := ~s] ~t₂ else [~x := ~s] ~t₃ }>
  -- sums
  | .sumInl τ₂ t₁ =>
      <{inl ~τ₂ ( [~x:= ~s] ~t₁) }>
  | .sumInr τ₂ t₁ =>
      <{inr ~τ₂ ( [~x:= ~s] ~t₁) }>
  | <{case ~t of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}> =>
      let t₁ := if x = x₁ then t₁ else <{ [~x := ~s] ~t₁ }>
      let t₂ := if x = x₂ then t₂ else <{ [~x := ~s] ~t₂ }>
      <{case ([~x := ~s] ~t) of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂ }>
  -- lists
  | .listNil _ => t
  | <{~t₁ :: ~t₂}> =>
      <{ ([~x := ~s] ~t₁) :: [~x := ~s] ~t₂ }>
  | <{case ~t₁ of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}> =>
      let t₃ := if x = x₁ || x = x₂ then t₃ else <{ [~x := ~s] ~t₃ }>
      <{case ( [~x := ~s] ~t₁ ) of
          nil => [~x := ~s] ~t₂
        | ~x₁ :: ~x₂ =>  ~t₃ }>
  -- unit
  | .unit => <{ unit }>

  -- Complete the following cases.

  -- pairs
  | <{(~t₁, ~t₂)}> =>
      sorry
  | Tm.fst t =>
      sorry
  | Tm.snd t =>
      sorry
  -- let
  | <{let ~y = ~t₁ in ~t₂}> => sorry
  -- fix
  | <{ fix ~t₁ }> => sorry
end

macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

attribute [autogradedHole] StlcExtended.subst

--  Make sure the following tests are valid by reflexivity:

example : <{ [z := 0] (let w = z in z) }> = <{ let w = 0 in 0 }> := by
  sorry

example : <{ [z := 0] (let w = z in w) }> = <{ let w = 0 in w }> := by
  sorry

example : <{  [z := 0] (let y = succ 0 in z) }> = <{ let y = succ 0 in 0 }> := by
  sorry

--  Next we define the values of our language.

inductive Tm.IsValue : Tm → Prop where
  -- In pure STLC, function abstractions are values:
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) : IsValue <{λ ~x : ~τ₂ . ~t₁}>
  -- Numbers are values:
  | nat (n : Nat) : IsValue (.const n)
  -- A tagged value is a value:
  | sumInl (v : Tm) (τ₁ : Ty) :
      IsValue v →
      IsValue <{inl ~τ₁ ~v}>
  | sumInr  (v : Tm) (τ₁ : Ty) :
      IsValue v →
      IsValue <{inr ~τ₁ ~v}>
  -- A list is a value iff its head and tail are values:
  | listNil (τ₁ : Ty) : IsValue <{nil ~τ₁}>
  | listCons (v₁ v₂ : Tm) :
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{~v₁ :: ~v₂}>
  -- A unit is always a value
  | unit : IsValue .unit
  -- A pair is a value if both components are:
  | pair (v₁ v₂ : Tm) :
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{(~v₁, ~v₂)}>

attribute [ExtStlcEval] Tm.IsValue.abs Tm.IsValue.nat Tm.IsValue.sumInl Tm.IsValue.sumInr
    Tm.IsValue.listNil Tm.IsValue.listCons Tm.IsValue.unit Tm.IsValue.pair

--  ### Exercise (3 stars): STLCExtended.step (Manually graded) ⭐⭐⭐

section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
  -- pure STLC
  | appAbs (x : String) (τ₂ : Ty) (t₁ v₂ : Tm) :
        v₂.IsValue →
         <{(λ ~x: ~τ₂ . ~t₁) ~v₂}> ⟶ <{ [~x := ~v₂] ~t₁ }>
  | app₁ (t₁ t₁' t₂ : Tm) :
         t₁ ⟶ t₁' →
         <{~t₁ ~t₂}> ⟶ <{~t₁' ~t₂}>
  | app₂ (v₁ t₂ t₂' : Tm) :
        v₁.IsValue →
         t₂ ⟶ t₂' →
         <{~v₁ ~t₂}> ⟶ <{~v₁  ~t₂'}>
  -- numbers
  | succ (t₁ t₁' : Tm) :
         t₁ ⟶ t₁' →
         <{succ ~t₁}> ⟶ <{succ ~t₁'}>
  | succNat (n : Nat) :
      <{ succ ~(Tm.const n) }> ⟶ Tm.const (n + 1)
  | pred (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') :
      <{ pred ~t₁ }> ⟶ <{ pred ~t₁' }>
  | predConst (n : Nat) :
      <{ pred ~(Tm.const n) }> ⟶ Tm.const (n - 1)
  | multConst (n₁ n₂ : Nat) :
      <{ ~(Tm.const n₁) * ~(Tm.const n₂) }> ⟶ Tm.const (n₁ * n₂)
  | mult₁ (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ ~t₁ * ~t₂ }> ⟶ <{ ~t₁' * ~t₂ }>
  | mult₂ (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ ~v₁ * ~t₂ }> ⟶ <{ ~v₁ * ~t₂' }>
  | if0Step (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if0 ~t₁ then ~t₂ else ~t₃ }> ⟶ <{ if0 ~t₁' then ~t₂ else ~t₃ }>
  | if0Zero (t₂ t₃ : Tm) :
      <{ if0 0 then ~t₂ else ~t₃ }> ⟶ t₂
  | if0Nonzero (n : Nat) (t₂ t₃ : Tm) :
      <{ if0 ~(Tm.const (n + 1)) then ~t₂ else ~t₃ }> ⟶ t₃
  -- sums
  | sumInl (t₁ t₁' : Tm) (τ₂ : Ty) :
        t₁ ⟶ t₁' →
        <{inl ~τ₂ ~t₁}> ⟶ <{inl ~τ₂ ~t₁'}>
  | sumInr (t₂ t₂' : Tm) (τ₁ : Ty) :
        t₂ ⟶ t₂' →
        <{inr ~τ₁ ~t₂}> ⟶ <{inr ~τ₁ ~t₂'}>
  | sumCase (t t' : Tm) (x₁ : String) (t₁ : Tm) (x₂ : String) (t₂ : Tm) :
        t ⟶ t' →
        <{case ~t of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}> ⟶
        <{case ~t' of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}>
  | sumCaseInl (v : Tm) (x₁:String) (t₁ : Tm) (x₂ : String) (t₂ : Tm) (τ₂ : Ty) :
        v.IsValue →
        <{case inl ~τ₂ ~v of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}> ⟶ <{ [~x₁ := ~v] ~t₁ }>
  | sumCaseInr (v : Tm) (x₁:String) (t₁ : Tm) (x₂ : String) (t₂ : Tm) (τ₁ : Ty) :
        v.IsValue →
        <{case inr ~τ₁ ~v of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}> ⟶ <{ [~x₂ := ~v] ~t₂ }>
  -- lists
  | cons₁ (t₁ t₁' t₂ : Tm) :
       t₁ ⟶ t₁' →
       <{~t₁ :: ~t₂}> ⟶ <{~t₁' :: ~t₂}>
  | cons₂ (v₁ t₂ t₂' : Tm) :
       v₁.IsValue →
       t₂ ⟶ t₂' →
       <{~v₁ :: ~t₂}> ⟶ <{~v₁ :: ~t₂'}>
  | listCase₁ (t₁ t₁' t₂ : Tm) (x₁ x₂ : String) (t₃ : Tm) :
       t₁ ⟶ t₁' →
       <{case ~t₁ of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}> ⟶
       <{case ~t₁' of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}>
  | listCaseNil (τ₁ : Ty) (t₂ : Tm) (x₁ x₂ : String) (t₃ : Tm) :
       <{case nil ~τ₁ of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}> ⟶ t₂
  | listCaseCons (v₁ vl t₂ : Tm) (x₁ x₂ : String) (t₃ : Tm) :
       v₁.IsValue →
       vl.IsValue →
       <{case ~v₁ :: ~vl of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}>
         ⟶  <{ [~x₂ := ~vl] ([~x₁ := ~v₁] ~t₃) }>

  -- Add rules for the following extensions.

  -- pairs
  --  FILL IN HERE
  -- let
  --  FILL IN HERE
  -- fix
  --  FILL IN HERE
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

-- Be sure to add your constructors to this list!
attribute [ExtStlcEval] Step.appAbs Step.app₁ Step.app₂
    Step.succ Step.succNat Step.pred Step.predConst
    Step.multConst Step.mult₁ Step.mult₂
    Step.if0Step Step.if0Zero Step.if0Nonzero
    Step.sumInl Step.sumInr Step.sumCase Step.sumCaseInl Step.sumCaseInr
    Step.cons₁ Step.cons₂ Step.listCase₁ Step.listCaseNil
    Step.listCaseCons
--  FILL IN HERE

attribute [autogradedHole] StlcExtended.Step

--  ### Exercise (3 stars): STLCExtended.HasType (Manually graded) ⭐⭐⭐

abbrev Context := PartialMap String Ty

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: contexts and judgments)
--  The context grammar `stlcCtx` is reused as well; only the map it
--  denotes is new, since the types it stores are this language's. As with
--  `subst`, the judgment rule is introduced twice: `local` and
--  hygiene-free while the relation is being declared, then again for real.

open Lean in
/-- The `Context` denoted by a context expression. -/
partial def ctxTerm (G : TSyntax `stlcCtx) : MacroM Term :=
  match G with
  | `(stlcCtx| ∅)   => `((∅ : Context))
  | `(stlcCtx| ~$e) => pure e
  | `(stlcCtx| $x:stlcVar ↦ $τ:stlcTy ; $G:stlcCtx) => do
      `(PartialMap.update $(← ctxTerm G) $(← Stlc.varStr x) <{ $τ:stlcTy }>)
  | _ => Macro.throwUnsupported

section StlcExtended
set_option hygiene false in
local macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $τ:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $τ:stlcTy }>)
--  END DETAILS

inductive HasType : Context → Tm → Ty → Prop where
  -- pure STLC
  | var (Γ : Context) (x : String) (τ₁ : Ty) (h : Γ[x] = some τ₁) :
      <{ ~Γ ⊢ ~(Tm.var x) ⦂ ~τ₁ }>
  | abs (Γ : Context) (x : String) (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ ~x ↦ ~τ₂ ; ~Γ ⊢ ~t₁ ⦂ ~τ₁ }>) :
      <{ ~Γ ⊢ λ ~x : ~τ₂ . ~t₁ ⦂ ~τ₂ → ~τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ ~τ₂ → ~τ₁ }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }>) :
      <{ ~Γ ⊢ ~t₁ ~t₂ ⦂ ~τ₁ }>
  -- numbers
  | const (Γ : Context) (n : Nat) :
      <{ ~Γ ⊢ ~(Tm.const n) ⦂ Nat }>
  | succ (Γ : Context) (t₁ : Tm) (h : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) :
      <{ ~Γ ⊢ succ ~t₁ ⦂ Nat }>
  | pred (Γ : Context) (t₁ : Tm) (h : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) :
      <{ ~Γ ⊢ pred ~t₁ ⦂ Nat }>
  | mult (Γ : Context) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ Nat }>) :
      <{ ~Γ ⊢ ~t₁ * ~t₂ ⦂ Nat }>
  | ite0 (Γ : Context) (t₁ t₂ t₃ : Tm) (τ : Ty)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~τ }>)
      (h₃ : <{ ~Γ ⊢ ~t₃ ⦂ ~τ }>) :
      <{ ~Γ ⊢ if0 ~t₁ then ~t₂ else ~t₃ ⦂ ~τ }>
  -- sums
  | sumInl (Γ : Context) (t₁ : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ }> →
      <{ ~Γ ⊢ (inl ~τ₂ ~t₁) ⦂ ~τ₁ + ~τ₂ }>
  | sumInr (Γ : Context) (t₂ : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }> →
      <{ ~Γ ⊢ (inr ~τ₁ ~t₂) ⦂ ~τ₁ + ~τ₂ }>
  | sumCase (Γ : Context) (x₁ x₂ : String) (τ₁ τ₂ τ₃: Ty) (t t₁ t₂ : Tm) :
      <{ ~Γ ⊢ ~t ⦂ ~τ₁ + ~τ₂ }> →
      <{ ~x₁ ↦ τ₁ ; ~Γ ⊢ ~t₁ ⦂ ~τ₃ }> →
      <{ ~x₂ ↦ τ₂ ; ~Γ ⊢ ~t₂ ⦂ ~τ₃ }> →
      <{ ~Γ ⊢ case ~t of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂ ⦂ ~τ₃ }>
  -- lists
  | listNil (Γ : Context) (τ₁ : Ty) :
      <{ ~Γ ⊢ nil ~τ₁ ⦂ [~τ₁] }>
  | listCons (Γ : Context) (t₁ t₂ : Tm) (τ₁ : Ty) :
      <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ }> →
      <{ ~Γ ⊢ ~t₂ ⦂ [~τ₁] }> →
      <{ ~Γ ⊢ ~t₁ :: ~t₂ ⦂ [~τ₁] }>
  | listCase (Γ : Context) (t₁ t₂ t₃ : Tm) (x₁ x₂ : String) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ ~t₁ ⦂ [τ₁] }> →
      <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }> →
      <{ ~x₁ ↦ τ₁ ; ~x₂ ↦ [~τ₁] ; ~Γ ⊢ ~t₃ ⦂ ~τ₂ }> →
      <{ ~Γ ⊢ case ~t₁ of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃ ⦂ ~τ₂ }>
  -- unit
  | unit (Γ : Context) :
      <{ ~Γ ⊢ unit ⦂ Unit }>

  -- Add rules for the following extensions.

  -- pairs
  --  FILL IN HERE
  -- let
  --  FILL IN HERE
  -- fix
  --  FILL IN HERE

-- Make sure to add your constructors here
attribute [ExtStlcTyping] HasType.var HasType.abs HasType.app
    HasType.const HasType.succ HasType.pred HasType.mult
    HasType.ite0 HasType.sumInl HasType.sumInr HasType.sumCase
    HasType.listNil HasType.listCons HasType.listCase HasType.unit
--  FILL IN HERE

attribute [autogradedHole] StlcExtended.HasType

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: the judgment, for real)
--  Closing the section retires the hygiene-free rule; the same rule is
--  then declared again, hygienically, for every later use, and a pair of
--  unexpanders prints judgments back in their own notation.

end StlcExtended

scoped macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $τ:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $τ:stlcTy }>)

open Lean PrettyPrinter in
/-- Rebuild `stlcCtx` syntax from the term syntax of a `Context`, so that a
context prints as `x ↦ Nat ; Γ` rather than as a chain of map updates. -/
partial def unexpandCtx : Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₚ $τ) => do
      unexpandCtx (← `($x →ₚ $τ ; ∅))
  | `($x:str →ₚ $τ ; $G) => do
      let G' ← unexpandCtx G
      let x' : TSyntax `stlcVar ←
        if Stlc.isPlainName x.getString then
          `(stlcVar| $(mkIdent (Name.mkSimple x.getString)):ident)
        else `(stlcVar| ~$x)
      match τ with
      | `(<{ $T':stlcTy }>) => `(stlcCtx| $x':stlcVar ↦ $T' ; $G')
      | _                   => `(stlcCtx| $x':stlcVar ↦ ~($τ) ; $G')
  | G => `(stlcCtx| ~($G))

open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander
  | `($_ $G <{ $t:stlcTm }> <{ $τ:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ $τ }>)
  | `($_ $G <{ $t:stlcTm }> $τ) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ ~($τ) }>)
  | `($_ $G $t <{ $τ:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ $τ }>)
  | `($_ $G $t $τ) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ ~($τ) }>)
  | _ => throw ()
--  END DETAILS

--  ### Exercise (5 stars): STLCExtended.examples (Optional) ⭐⭐⭐⭐⭐

--  This section presents formalized versions of the examples from above
--  (plus several more).
--
--  For each example, replace `sorry` once you've implemented enough of the
--  definitions for the tests to pass. If you've defined `Step` and
--  `HasType` correctly, these should all be solvable with
--  `apply_rules using ExtStlcTyping` or `normalize using ExtStlcEval`.
--  Make sure to give your new constructors the right attributes so that
--  Lean can find them. If these don't work, try working the proofs by
--  applying constructors manually to see where they go wrong.
--
--  The examples at the beginning focus on specific features; you can use
--  these to make sure your definition of a given feature is reasonable
--  before moving on to extending the proofs later in the file with the
--  cases relating to this feature. The later examples require all the
--  features together, so you'll need to come back to these when you've got
--  all the definitions filled in.

namespace Examples

namespace Numbers

def tm_test := <{if0 (pred (succ (pred (2 * 0)))) then 5 else 6}>

theorem typechecks : <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by
  sorry

theorem reduces : tm_test ⟶* (Tm.const 5) := by
  sorry

end Numbers

namespace Prod

def tm_test := <{ snd (fst ((5, 6), 7)) }>

theorem typechecks : <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by
  sorry

theorem reduces : tm_test ⟶* Tm.const 6 := by
  sorry

end Prod

namespace Let

def tm_test := <{let x = (pred 6) in (succ x)}>

theorem typechecks : <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by
  sorry

theorem reduces :
  tm_test ⟶* Tm.const 6 := by
    sorry

end Let

namespace Let1

def tm_test :=
  <{ let z = pred 6 in
     (succ z) }>

theorem typechecks :
  <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by
  sorry

theorem reduces :
  tm_test ⟶* Tm.const 6 := by
    sorry

end Let1

namespace Sums1

def tm_test :=
  <{ case (inl Nat 5) of
       inl x => x
     | inr y => y }>

theorem typechecks :
  <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by
  sorry

theorem reduces :
  tm_test ⟶* Tm.const 5 := by
    sorry

end Sums1

namespace Sums2

def tm_test :=
  <{ let processSum =
     (λx:Nat + Nat.
       case x of
          inl n => n
        | inr n => (if0 n then 1 else 0)) in
     (processSum (inl Nat 5), processSum (inr Nat 5)) }>

theorem typechecks :
  <{ ∅ ⊢ ~tm_test ⦂ Nat × Nat }> := by
  sorry

theorem reduces :
  tm_test ⟶* <{ (5, ~(Tm.const 0)) }> := by
    sorry

end Sums2

namespace Lists

def tm_test :=
  <{ let l = (5 :: 6 :: (nil Nat)) in
     case l of
       nil => 0
     | x :: y => (x * x) }>

theorem typechecks :
  <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by
  sorry

theorem reduces :
  tm_test ⟶* Tm.const 25 := by
    sorry

end Lists

namespace Fix1

def fact :=
  <{ fix
      (λf:Nat→Nat.
        λa:Nat.
         if0 a then 1 else (a * (f (pred a)))) }>

-- (Warning: you may be able to typecheck `fact` but still have some rules wrong!) *)

theorem typechecks :
  <{ ∅ ⊢ ~fact ⦂ Nat → Nat }> := by
  sorry

theorem reduces :
  <{ ~fact 4 }> ⟶* Tm.const 24 := by
    sorry

end Fix1

namespace Fix2

def map :=
  <{ λg:Nat→Nat.
       fix
         (λf: [Nat] → [Nat].
            λl: [Nat].
               case l of
                 nil => nil Nat
               | x::l => ((g x)::(f l))) }>

theorem typechecks :
  <{ ∅ ⊢ ~map ⦂
     (Nat → Nat) → [Nat] → [Nat] }> := by
  sorry

theorem reduces :
  <{ ~map (λa:Nat. succ a) (1 :: 2 :: (nil Nat)) }>
  ⟶* <{ 2 :: 3 :: (nil Nat) }> := by
    sorry

end Fix2

namespace Fix3

def equal :=
  <{ fix
        (λeq:Nat→Nat→Nat.
           λm:Nat. λn:Nat.
             if0 m then (if0 n then 1 else 0)
             else (if0 n
                   then 0
                   else (eq (pred m) (pred n)))) }>

theorem typechecks :
 <{ ∅ ⊢ ~equal ⦂ Nat → Nat → Nat }> := by
  sorry

theorem reduces :
  <{ ~equal 4 4 }> ⟶* Tm.const 1 := by
  sorry

theorem reduces2 :
  <{ ~equal 4 5 }> ⟶* Tm.const 0 := by
  sorry

end Fix3

namespace Fix4

def eotest :=
  <{ let evenodd =
           fix
           (λeo: (Nat → Nat) × (Nat → Nat).
              ((λn:Nat. if0 n then 1 else (snd eo (pred n))),
               (λn:Nat. if0 n then 0 else (fst eo (pred n))))) in
     let even = fst evenodd in
     let odd  = snd evenodd in
     (even 3, even 4) }>

theorem typechecks :
  <{ ∅ ⊢ ~eotest ⦂ Nat × Nat }> := by
  sorry

theorem reduces :
  eotest ⟶* <{ (0, 1) }> := by
  sorry

end Fix4
end Examples

--  The proofs of progress and preservation for this enriched system are
--  essentially the same (though of course longer) as for the pure STLC.

--  ### Exercise (3 stars): STLCExtended.progress ⭐⭐⭐

--  Complete the proof of `progress`
--
--  Theorem: Suppose `∅ ⊢ t ⦂ τ`. Then either
--
--  1. `t` is a value, or
--  2. `t ⟶ t'` for some `t'`.
--
--  Proof: By induction on the given typing derivation.

theorem canonical_forms_fun (t : Tm) (τ₁ τ₂ : Ty)
    (ht : <{ ∅ ⊢ ~t ⦂ ~τ₁ → ~τ₂ }>) (hv : t.IsValue) :
    ∃ x u, t = <{ λ ~x : ~τ₁ . ~u }> := by
  inversion ht with (inversion hv)
  | abs x t h => exists x, t

theorem canonical_forms_nat (t : Tm)
    (ht : <{ ∅ ⊢ ~t ⦂ Nat }>) (hv : t.IsValue) :
    ∃ n, t = Tm.const n := by
  inversion ht with (inversion hv)
  | nat n => exists n

theorem canonical_forms_sum {t : Tm} {τ₁ τ₂ : Ty}
    (ht : <{ ∅ ⊢ ~t ⦂ ~τ₁ + ~τ₂ }>) (hv : t.IsValue) :
    ∃ v, v.IsValue ∧ (t = <{inl ~τ₂ ~v}> ∨ t = <{inr ~τ₁ ~v}>) := by
  inversion ht with (inversion hv)
  | sumInl v ht hv =>
    exists v; constructor; assumption; left; rfl
  | sumInr v ht hv =>
    exists v; constructor; assumption; right; rfl

theorem canonical_forms_list {t : Tm} {τ : Ty}
    (ht : <{ ∅ ⊢ ~t ⦂ [~τ] }>) (hv : t.IsValue) :
    t = <{ nil τ }> ∨ ∃ v₁ v₂, (v₁.IsValue ∧ v₂.IsValue ∧ t = <{~v₁ :: ~v₂}>) := by
  inversion ht with (inversion hv)
  | listNil _ => left; rfl
  | listCons v₁ v₂ _ _ _ _ => right; exists v₁, v₂

-- Add your own canonical forms lemmas here as needed

--  FILL IN HERE

theorem progress (t : Tm) (τ : Ty) (ht :<{ ∅ ⊢ ~t ⦂ ~τ }>) :
    t.IsValue ∨ exists t', t ⟶ t' := by

    generalize heq : (∅ : Context) = Γ at ht
    induction ht with (subst_vars; first
      -- discharge cases where `t` is obviously a value
      | try (left; constructor; done)
    )
    | var => contradiction
    | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      right; cases ih₁ rfl
      -- t₁ is a value
      case _ ht₁ =>
        cases ih₂ rfl
        -- t₂ is a value
        case _ ht₂ =>
          apply canonical_forms_fun at h₁
          let ⟨x, v, hv⟩ := h₁ ht₁
          exists <{ [~x := ~t₂] ~v }>; simp [hv]
          apply_rules using ExtStlcEval
        -- t₂ is not a value
        case _ ht₂ =>
          obtain ⟨t₂', ht₂⟩ := ht₂
          exists <{~t₁ ~t₂'}>; apply_rules using ExtStlcEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exists <{~t₁' ~t₂}>; apply_rules using ExtStlcEval
    | succ Γ t₁ h ih =>
      right; cases ih rfl
      -- t₁ is a value
      case _ ht₁ =>
        apply canonical_forms_nat at h
        obtain ⟨n, h⟩ := h ht₁; rw [h]
        exists (Tm.const (n + 1)); apply_rules using ExtStlcEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exists <{succ ~t₁'}>; apply_rules using ExtStlcEval
    | pred Γ t₁ h ih =>
      right; cases ih rfl
       -- t₁ is a value
      case _ ht₁ =>
        apply canonical_forms_nat at h
        obtain ⟨n, h⟩ := h ht₁; rw [h]
        exists (Tm.const (n - 1)); apply_rules using ExtStlcEval
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exists <{pred ~t₁'}>; apply_rules using ExtStlcEval
    | mult Γ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      right; cases ih₁ rfl
      -- t₁ is a value
      case _ ht₁ =>
        cases ih₂ rfl
        -- t₂ is a value
        case _ ht₂ =>
          apply canonical_forms_nat at h₁
          apply canonical_forms_nat at h₂
          let ⟨n₁, h₁⟩ := h₁ ht₁
          let ⟨n₂, h₂⟩ := h₂ ht₂
          exists (Tm.const (n₁ * n₂)); simp [h₁, h₂]
          apply_rules using ExtStlcEval
        -- t₂ is not a value
        case _ ht₂ =>
          obtain ⟨t₂', ht₂⟩ := ht₂
          exists <{~t₁ * ~t₂'}>; apply_rules using ExtStlcEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exists <{~t₁' * ~t₂}>; apply_rules using ExtStlcEval
    | ite0 Γ t₁ t₂ t₃ τ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      right; cases ih₁ rfl
      -- t₁ is a value
      case _ ht₁ =>
        apply canonical_forms_nat at h₁
        let ⟨n₁, h₁⟩ := h₁ ht₁
        rw [h₁]; cases n₁
        · exists t₂; apply_rules using ExtStlcEval
        · exists t₃; apply_rules using ExtStlcEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exists <{if0 ~t₁' then ~t₂ else ~t₃}>; apply_rules using ExtStlcEval
    | sumInl Γ t₁ τ₁ τ₂ h ih =>
      cases ih rfl
      -- t₁ is a value
      case _ ht₁ =>
        left; apply_rules using ExtStlcEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        right; exists <{inl ~τ₂ ~t₁'}>; apply_rules using ExtStlcEval
    | sumInr Γ t₂ τ₁ τ₂ h ih =>
      cases ih rfl
      -- t₁ is a value
      case _ ht₁ =>
        left; apply_rules using ExtStlcEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₂', ht₁⟩ := ht₁
        right; exists <{inr ~τ₁ ~t₂'}>; apply_rules using ExtStlcEval
    | sumCase Γ x₁ x₂ τ₁ τ₂ τ₃ t t₁ t₂ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      right; cases ih₁ rfl
      -- t₁ is a value
      case _ ht =>
        apply canonical_forms_sum at h₁
        obtain ⟨v, hv, hl | hr⟩ := h₁ ht
        · rw [hl]; exists <{ [~x₁ := ~v] ~t₁ }>; apply_rules using ExtStlcEval
        · rw [hr]; exists <{ [~x₂ := ~v] ~t₂ }>; apply_rules using ExtStlcEval
      -- t₁ is not a value
      case _ ht =>
        obtain ⟨t', ht⟩ := ht
        exists <{case ~t' of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}>; apply_rules using ExtStlcEval
    | listCons Γ t₁ t₂ τ₁ h₁ h₂ ih₁ ih₂ =>
      cases ih₁ rfl
      -- t₁ is a value
      case _ ht₁ =>
        cases ih₂ rfl
        -- t₂ is a value
        case _ ht₂ =>
          left; apply_rules using ExtStlcEval
        -- t₂ is not a value
        case _ ht₂ =>
          obtain ⟨t₂', ht₂⟩ := ht₂
          right; exists <{~t₁ :: ~t₂'}>; apply_rules using ExtStlcEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        right; exists <{~t₁' :: ~t₂}>; apply_rules using ExtStlcEval
    | listCase Γ t₁ t₂ t₃ x₁ x₂ τ₁ τ₂ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
        right; cases ih₁ rfl
        -- t₁ is a value
        case _ ht =>
          apply canonical_forms_list at h₁
          obtain hnil | ⟨v₁, v₂, hv₁, hv₂, h⟩ := h₁ ht
          · rw [hnil]; exists t₂; apply_rules using ExtStlcEval
          · rw [h]; exists <{ [~x₂ := ~v₂] [~x₁ := ~v₁] ~t₃ }>; apply_rules using ExtStlcEval
        -- t₁ is not a value
        case _ ht =>
          obtain ⟨t', ht⟩ := ht
          exists <{case ~t' of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}>; apply_rules using ExtStlcEval
    -- complete the proof
    --  FILL IN HERE

attribute [autogradedHole] StlcExtended.progress

attribute [autogradedProof 3] StlcExtended.progress

--  Through the power of automation, the weakening proof is exactly the
--  same as for the original STLC.

theorem weakening {Γ Γ' : Context} {t : Tm} {τ: Ty}
    (hi : Γ ⊆ Γ')
    (ht : <{ ~Γ ⊢ ~t ⦂ ~τ }>) :
     <{ ~Γ' ⊢ ~t ⦂ ~τ }> := by
  induction ht generalizing Γ' with (apply_rules [PartialMap.update_subset] using ExtStlcTyping)

theorem weakening_empty {Γ : Context} {t : Tm} {τ: Ty}
    (ht :<{ ∅ ⊢ ~t ⦂ ~τ }>) :
    <{ ~Γ ⊢ ~t ⦂ ~τ }> := by
  apply weakening _ ht
  intro _ _ h
  rw [PartialMap.getElem_empty] at h
  contradiction

--  ### Exercise (2 stars): STLCExtended.substitution_preserves_typing ⭐⭐

--  Complete the proof of `substitution_preserves_typing`

theorem substitution_preserves_typing (Γ : Context) (x : String) (τ₁ : Ty) (t v : Tm) (τ : Ty)
    (ht : <{ ~x ↦ ~τ₁ ; ~Γ ⊢ ~t ⦂ ~τ }>)
    (hv : <{ ∅ ⊢ ~v ⦂ ~τ₁ }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~τ }> := by
  sorry

attribute [autogradedHole] StlcExtended.substitution_preserves_typing

attribute [autogradedProof 2] StlcExtended.substitution_preserves_typing

--  ### Exercise (3 stars): STLCExtended.preservation ⭐⭐⭐

--  Complete the proof of `preservation`:

theorem preservation (t t' : Tm) (τ : Ty)
    (ht : <{ ∅ ⊢ ~t ⦂ ~τ }>)
    (he : t ⟶ t') :
    <{ ∅ ⊢ ~t' ⦂ ~τ }> := by

    generalize heq : (∅ : Context) = Γ at ht
    induction ht generalizing t' with (subst_vars; first
      -- discharge the goals where `t` doesn't step
      | inversion he <;> constructor <;> simp_all; done
      | try (inversion he; apply_rules using ExtStlcTyping; done))
    | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      inversion he with (try (constructor <;> apply_rules; done))
      | appAbs _ h =>
          apply substitution_preserves_typing (τ₁:=τ₂)
          · inversion h₁; assumption
          · simp_all
    | ite0 Γ t₁ t₂ t₃ τ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      inversion he <;> first
      | constructor <;> simp_all
      | simp_all
    | sumCase Γ x₁ x₂ τ₁ τ₂ τ₃ t t₁ t₂ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      inversion he with
      | sumCase => constructor <;> apply_rules
      | sumCaseInl =>
        apply substitution_preserves_typing (τ₁:=τ₁)
        assumption
        inversion h₁; trivial
      | sumCaseInr =>
        apply substitution_preserves_typing (τ₁:=τ₂)
        assumption
        inversion h₁; trivial
    | listCase Γ t₁ t₂ t₃ x₁ x₂ τ₁ τ₂ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      inversion he with
      | listCase₁ => constructor <;> apply_rules
      | listCaseNil => trivial
      | listCaseCons =>
        apply substitution_preserves_typing (τ₁:= <{[ ~τ₁ ]}>)
        apply substitution_preserves_typing (τ₁:=τ₁)
        assumption
        inversion h₁; trivial
        inversion h₁; trivial
    -- Complete the proof...
    --  FILL IN HERE

attribute [autogradedHole] StlcExtended.preservation

attribute [autogradedProof 3] StlcExtended.preservation

end StlcExtended

-- Built on 2026-09-03 16:48 UTC

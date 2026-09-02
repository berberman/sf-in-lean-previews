import TS.Slang
import TS.AttributeDecls

import ComparatorAutograderLib
import SFLCompat

--  # Smallstep: Small-step Operational Semantics

--  Note to developers (Benjamin Pierce @bcpierce00):
--      The `hiding lean` (above in the source file) should not be needed
--      any more and should be removed from all files everywhere it exists.

--  Note to developers (Michael Hicks @mwhicks1):
--      This chapter adapts Smallstep to follow Slang, the initial part of
--      Imp, on just Aexp and Bexp (without variables). This means that
--      parts of this chapter had to adjust: Concurrent Imp is dropped in
--      favor of Nondeterministic Aexp, and the stack machine is simplified
--      to just Aexps without variables.

--  Note to developers (before next release):
--      In this and later chapters, we are not very consistent about
--      presenting computation rules first and congruence rules after...

--  Note to developers:
--      HIDE: Sometime in the early 2010s, we did some mining past exams
--      for exercises...
--
--      - Loris: No interesting exercise in Finals of 2007-2009-2010-2011.
--        Nothing in second midterms except for 2011.
--
--      - 2011 midterm proposes the following exercise: give the small step
--        relation of FLIP X (alternatively HAVOC, ANYTHING). We could then
--        ask to extend the proof of equivalence of big step vs small step
--        (personally don't like it too much).
--
--      - Maybe we can ask how they would adapt the definition of Hoare
--        triple to small step (maybe in the exam).
--
--      HIDE: BCP: I also have a bunch of slides from earlier offerings of
--      CIS500 that might be good additions to the TERSE notes.
--
--      HIDE: Possible major restructuring: This chapter might better be
--      postponed to later in the course. A big-step presentation of STLC
--      (and maybe even some of the extensions like subtyping?) could come
--      first. However, this would invite a much bigger change, where
--      **all** the variants of STLC (with refs, with subtyping, ...) are
--      done in big-step style. This requires more thought...
--
--      HIDE: Wonder whether it would be interesting to show them how to
--      make a correspondence with a "real abstract machine" at a lower
--      level...? There's a start at an exercise along these lines below.

--  ## Big-step and Small-step Evaluation

--  The evaluators we saw for Slang were formulated in a "big-step" style:
--  they specify how a given expression can be evaluated to its final value
--  "all in one big step":

--  2 + 2 + 3 * 4 ⇓ 16

--  This style is simple and natural for many purposes — indeed, Gilles
--  Kahn, who popularized it, called it *natural semantics*. But there are
--  some things it does not do well. In particular, it does not give us a
--  convenient way of talking about *concurrent* programming languages,
--  where the semantics of a program — the essence of how it behaves —
--  includes not just which input states get mapped to which output states,
--  but also the intermediate states that it passes through along the way;
--  this is crucial, since these states can also be observed by
--  concurrently executing code.
--
--  Another shortcoming of the big-step style is more technical but equally
--  critical in many situations. Suppose we want to define a variant of our
--  expression language where a value could be *either* a number *or* a
--  list of numbers. In the syntax of this extended language, it will be
--  possible to write strange expressions like `2 + nil`, and our semantics
--  for arithmetic expressions will then need to say something about how
--  such expressions behave. One possibility is to maintain the convention
--  that every arithmetic expression evaluates to some number by choosing
--  some way of viewing a list as a number — e.g., by specifying that a
--  list should be interpreted as `0` when it occurs in a context expecting
--  a number. But this would be a bit of a hack.
--
--  A much more natural approach is simply to say that the behavior of the
--  expression `2 + nil` is *undefined* — i.e., it doesn't evaluate to any
--  result at all. And we can easily do this: we just have to formulate
--  `aeval` and `beval` as inductive propositions rather than functions, so
--  that we can make them partial functions instead of total ones.
--
--  Now, however, we encounter a subtlety that will become important once
--  we move to a full programming language with looping. There, a program
--  might fail to produce a result for *two quite different reasons*:
--  either because the execution gets into an infinite loop or because, at
--  some point, the program tries to do an operation that makes no sense,
--  such as adding a number to a list, so that none of the evaluation rules
--  can be applied.
--
--  These two outcomes — nontermination vs. getting stuck in an erroneous
--  configuration — should not be confused. In particular, we want to
--  *allow* the first (because permitting the possibility of infinite loops
--  is the price we pay for the convenience of programming with general
--  looping constructs) but *prevent* the second (which is just wrong), for
--  example by adding some form of *typechecking* to the language. Indeed,
--  this will be a major topic of the next chapter, on *types*. As a first
--  step, we need a way of presenting the semantics that allows us to
--  distinguish nontermination from erroneous "stuck states."
--
--  So, for lots of reasons, we'd like to have a finer-grained way of
--  defining and reasoning about program behaviors. This is the topic of
--  the present chapter. Our goal is to replace the "big-step" `Eval`
--  relation with a "small-step" relation that specifies, for a given
--  program, how its atomic steps of computation are performed. In the
--  *small-step* style, we show how to "reduce" an expression to a simpler
--  form by performing a single step of computation:

--  2 + 2 + 3 * 4
--  ⟶ 2 + 2 + 12
--  ⟶ 4 + 12
--  ⟶ 16

--  ## A Toy Language

--  To save space, we start with an incredibly simple language of just
--  constants and addition. (We use single-letter constructors `c` and `p`
--  — for Constant and Plus — for brevity.) The same techniques scale up to
--  richer languages.

inductive Tm where
  | c (n : Nat)          -- Constant
  | p (t₁ t₂ : Tm)       -- Plus

--  A standard big-step evaluator, as a function.

def evalF (t : Tm) : Nat :=
  match t with
  | .c n => n
  | .p t₁ t₂ => evalF t₁ + evalF t₂

--  Here is the same evaluator, written in exactly the same style, but
--  formulated as an inductively defined relation. We use the notation
--  `t ⇓ n` for "`t` evaluates to `n`."
--
--  The `notation` command below is how that is declared: it introduces `⇓`
--  as infix syntax for the `Eval` relation defined with it, with a
--  precedence saying how tightly it binds. This is the lightweight way to
--  name a relation; later chapters, where a whole object language needs a
--  grammar rather than a single operator, reach for `declare_syntax_cat`
--  instead.

--  -------                (const)
--                          c n ⇓ n
--
--                          t₁ ⇓ n₁
--                          t₂ ⇓ n₂
--                      -----------------          (plus)
--                      p t₁ t₂ ⇓ n₁ + n₂

inductive Eval : Tm → Nat → Prop where
  | const (n : Nat) : Eval (.c n) n
  | plus (t₁ t₂ : Tm) (n₁ n₂ : Nat) (h₁ : Eval t₁ n₁) (h₂ : Eval t₂ n₂) : Eval (.p t₁ t₂) (n₁ + n₂)

notation:50 t " ⇓ " n => Eval t n

--  Now, here is the corresponding *small-step* relation, written `t ⟶ t'`:

--  -------------------------------      (plus)
--                  p (c n₁) (c n₂) ⟶ c (n₁ + n₂)
--
--                           t₁ ⟶ t₁'
--                      --------------------             (plusLeft)
--                      p t₁ t₂ ⟶ p t₁' t₂
--
--                           t₂ ⟶ t₂'
--                   ----------------------------        (plusRight)
--                   p (c n₁) t₂ ⟶ p (c n₁) t₂'

namespace SimpleArith1

inductive Step : Tm → Tm → Prop where
  | plus (n₁ n₂ : Nat) :
      Step (.p (.c n₁) (.c n₂)) (.c (n₁ + n₂))
  | plusLeft (t₁ t₁' t₂ : Tm)
      (h : Step t₁ t₁') :
      Step (.p t₁ t₂) (.p t₁' t₂)
  | plusRight (n₁ : Nat) (t₂ t₂' : Tm)
      (h : Step t₂ t₂') :
      Step (.p (.c n₁) t₂) (.p (.c n₁) t₂')

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'

--  Things to notice:
--
--  - We are defining a single reduction step, in which just one `p` node
--    is replaced by its value.
--
--  - Each step finds the *leftmost* `p` node that is ready to go (both of
--    its operands are constants) and rewrites it in place. The first rule
--    tells how to rewrite this `p` node itself; the other two rules tell
--    how to find it.
--
--  - A term that is just a constant cannot take a step.

--  Let's pause and check a couple of examples of reasoning with the step
--  relation.
--
--  If `t₁` steps to `t₁'`, then `p t₁ t₂` steps to `p t₁' t₂`.

example :
    (.p
      (.p (.c 1) (.c 3))
      (.p (.c 2) (.c 4))) ⟶
    (.p
      (.c 4)
      (.p (.c 2) (.c 4))) := by
  apply Step.plusLeft; apply Step.plus

--  ### Exercise (1 star): test_step_2 ⭐

--  Right-hand sides step only once the left side is a value.

example :
    (.p
      (.c 0)
      (.p
        (.c 2)
        (.p
          (.c 1)
          (.c 3))))
      ⟶
    (.p
      (.c 0)
      (.p
        (.c 2)
        (.c 4))) := by
  sorry

--   ----------------------------------------

--  _Quiz:_

--  To what does the following term step?

--  .p
--    (.p
--      (.c 1)
--      (.c 2))
--    (.p
--      (.c 1)
--      (.c 2))

--  (A) `.c 6` (B) `.p (.c 3) (.p (.c 1) (.c 2))` (C)
--  `.p (.p (.c 1) (.c 2)) (.c 3)` (D) `.p (.c 3) (.c 3)` (E) None of the
--  above

--   ----------------------------------------

--  _Quiz:_

--  What about this one?

--  .c 1

--  (A) `.c 1` (B) `.p (.c 0) (.c 1)` (C) None of the above

--   ----------------------------------------

end SimpleArith1

--  ## Relations

--  We will be working with several different single-step relations, so it
--  is helpful to generalize a bit and state a few definitions and theorems
--  about relations in general. (The optional chapter `Rel` in *Logical
--  Foundations* develops some of these ideas in a bit more detail;
--  reviewing that chapter may be useful if the treatment here feels too
--  terse.)
--
--  A *binary relation* on a type `X` is a family of propositions
--  parameterized by two elements of `X` — i.e., a proposition about pairs
--  of elements of `X`.

--  Note to developers (Michael Hicks @mwhicks1, before next release):
--      Should we be getting this (and `Deterministic`, `Multi`, etc. if
--      appropriate) from the Lean standard library? If not, should we
--      match the concepts in CSLib, if they exists there?

def Relation (X : Type) := X → X → Prop

--  Our main examples of such relations in this chapter will be the
--  single-step reduction relation, `⟶`, and its multi-step variant, `⟶*`,
--  defined below, but there are many other examples — e.g., the "equals,"
--  "less than," "less than or equal to," and "is the square of" relations
--  on numbers, and the "prefix of" relation on lists and strings.

--  One simple property a relation may have is being *deterministic*: like
--  Slang's big-step evaluation, each element is related to at most one
--  other.
--
--  *Theorem*: For each `t`, there is at most one `t'` such that `t` steps
--  to `t'`. We prove it by induction on the derivation of the first step.
--
--  *Proof sketch*: We show that if `x` steps to both `y₁` and `y₂`, then
--  `y₁` and `y₂` are equal, by induction on a derivation of `x ⟶ y₁`.
--  There are several cases, depending on the last rule used in this
--  derivation and the last rule in the given derivation of `x ⟶ y₂`.
--
--  - If both are `plus`, the result is immediate.
--
--  - The cases when both derivations end with `plusLeft` or `plusRight`
--    follow by the induction hypothesis.
--
--  - It cannot happen that one is `plus` and the other is
--    `plusLeft`/`plusRight`, since this would imply that `x` has the form
--    `p t₁ t₂` where both `t₁` and `t₂` are constants (by `plus`) *and*
--    one of `t₁` or `t₂` has the form `p _`.
--
--  - Similarly, it cannot happen that one is `plusLeft` and the other is
--    `plusRight`, since this would imply that `x` has the form `p t₁ t₂`
--    where `t₁` has both the form `p t₁₁ t₁₂` and the form `c n`.
--
--  Formally,

def Deterministic {X : Type} (R : Relation X) : Prop :=
  ∀ x y₁ y₂ : X, R x y₁ → R x y₂ → y₁ = y₂

namespace SimpleArith2

theorem step_deterministic : Deterministic SimpleArith1.Step := by
  intro x y₁ y₂ h₁
  induction h₁ generalizing y₂ with
  | plus n₁ n₂ =>
      intro h₂
      cases h₂ <;> first | rfl | cases ‹SimpleArith1.Step (.c _) _›
  | plusLeft t₁ t₁' t₂ hs ih =>
      intro h₂
      cases h₂ <;> first | cases ‹SimpleArith1.Step (.c _) _› | rw [ih _ ‹SimpleArith1.Step t₁ _›]
  | plusRight n₁ t₂ t₂' hs ih =>
      intro h₂
      cases h₂ <;> first | cases ‹SimpleArith1.Step (.c _) _› | rw [ih _ ‹SimpleArith1.Step t₂ _›]

end SimpleArith2

--  Note to developers (Michael Hicks @mwhicks1):
--      In the Rocq there is the development of a special tactic to make
--      this proof simpler. Do we want that here?

--  ### Values

--  Next, it will be useful to slightly reformulate the definition of
--  single-step reduction by stating it in terms of "values."
--
--  It can be useful to think of the `⟶` relation as defining an *abstract
--  machine*:
--
--  - At any moment, the *state* of the machine is a term.
--
--  - A *step* of the machine is an atomic unit of computation — here, a
--    single "add" operation.
--
--  - The *halting states* of the machine are ones where there is no more
--    computation to be done.
--
--  We can then *execute* a term `t` as follows:
--
--  - Take `t` as the starting state of the machine.
--
--  - Repeatedly use the `⟶` relation to find a sequence of machine states,
--    starting with `t`, where each state steps to the next.
--
--  - When no more reduction is possible, "read out" the final state of the
--    machine as the result of execution.
--
--  Intuitively, it is clear that the final states of our machine are
--  always terms of the form `c n` for some `n`. We call such terms
--  *values*.

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)

--  Having introduced the idea of values, we can use it in the definition
--  of the `⟶` relation to write the `plusRight` rule in a slightly more
--  elegant way.

--  ------------------------------      (plus)
--                  p (c n₁) (c n₂) ⟶ c (n₁ + n₂)
--
--                           t₁ ⟶ t₁'
--                      -------------------             (plusLeft)
--                      p t₁ t₂ ⟶ p t₁' t₂
--
--                           IsValue v₁
--                           t₂ ⟶ t₂'
--                      -------------------             (plusRight)
--                      p v₁ t₂ ⟶ p v₁ t₂'

--  Again, the variable names in the informal presentation carry important
--  information: by convention, `v₁` ranges only over values, while `t₁`
--  and `t₂` range over arbitrary terms.
--
--  (Given this convention, the explicit `IsValue` hypothesis is arguably
--  redundant, since the naming convention tells us where to add it when
--  translating the informal rule to Lean. We'll keep it for now, to
--  maintain a close correspondence between the informal and Lean versions
--  of the rules, but later on we'll drop it in informal rules for
--  brevity.)

--  Here are the formal rules.

inductive Step : Tm → Tm → Prop where
  | plus (n₁ n₂ : Nat) :
      Step (.p (.c n₁) (.c n₂)) (.c (n₁ + n₂))
  | plusLeft (t₁ t₁' t₂ : Tm)
      (h : Step t₁ t₁') :
      Step (.p t₁ t₂) (.p t₁' t₂)
  | plusRight (v₁ t₂ t₂' : Tm)
      (hv : IsValue v₁)
      (h : Step t₂ t₂') :
      Step (.p v₁ t₂) (.p v₁ t₂')

notation:40 t:41 " ⟶ " t':41 => Step t t'

--  ### Exercise (3 stars): redo_determinism ⭐⭐⭐

--  As a sanity check on this change, let's re-verify determinism. Here's
--  an informal proof:
--
--  *Proof sketch*: We must show that if `x` steps to both `y₁` and `y₂`,
--  then `y₁` and `y₂` are equal. Consider the final rules used in the
--  derivations of `x ⟶ y₁` and `x ⟶ y₂`.
--
--  - If both are `plus`, the result is immediate.
--
--  - The cases when both derivations end with `plusLeft` or `plusRight`
--    follow by the induction hypothesis.
--
--  - It cannot happen that one is `plus` and the other is
--    `plusLeft`/`plusRight`, since this would imply that `x` has the form
--    `p t₁ t₂` where both `t₁` and `t₂` are constants (by `plus`) *and*
--    one of `t₁` or `t₂` has the form `p _`.
--
--  - Similarly, it cannot happen that one is `plusLeft` and the other is
--    `plusRight`, since this would imply that `x` has the form `p t₁ t₂`
--    where `t₁` both has the form `p t₁₁ t₁₂` and is a value (hence has
--    the form `c n`).
--
--  Most of this proof is the same as the one above. But to get maximum
--  benefit from the exercise you should try to write your formal version
--  from scratch and just use the earlier one if you get stuck. The
--  impossible cross-cases now also use the fact that a `IsValue` (a `c n`)
--  cannot step.

theorem step_deterministic : Deterministic Step := by
  sorry

attribute [autogradedProof 3] step_deterministic

--  ### Strong Progress and Normal Forms

--  The definition of single-step reduction for our toy language is fairly
--  simple, but for a larger language it would be easy to forget one of the
--  rules and accidentally create a situation where some term cannot take a
--  step even though it has not been completely reduced to a value. The
--  following theorem shows that we did not, in fact, make such a mistake
--  here.
--
--  *Theorem* (*Strong Progress*): If `t` is a term, then either `t` is a
--  value or else there exists a term `t'` such that `t ⟶ t'`.
--
--  *Proof*: By induction on `t`.
--
--  - Suppose `t = c n`. Then `t` is a value.
--
--  - Suppose `t = p t₁ t₂`, where (by the IH) `t₁` either is a value or
--    can step to some `t₁'`, and where `t₂` is either a value or can step
--    to some `t₂'`. We must show `p t₁ t₂` is either a value or steps to
--    some `t'`.
--
--    - If `t₁` and `t₂` are both values, then `t` can take a step, by
--      `plus`.
--
--    - If `t₁` is a value and `t₂` can take a step, then so can `t`, by
--      `plusRight`.
--
--    - If `t₁` can take a step, then so can `t`, by `plusLeft`.
--
--  Or, formally:

theorem strong_progress (t : Tm) : IsValue t ∨ ∃ t', t ⟶ t' := by
  induction t with
  | c n => left; exact .const n
  | p t₁ t₂ ih₁ ih₂ =>
      right
      cases ih₁ with
      | inl hv₁ =>
          cases ih₂ with
          | inl hv₂ =>
              cases hv₁ with
              | const n₁ =>
                  cases hv₂ with
                  | const n₂ => exact ⟨.c (n₁ + n₂), .plus n₁ n₂⟩
          | inr h₂ =>
              obtain ⟨t₂', ht₂⟩ := h₂
              exact ⟨.p t₁ t₂', .plusRight t₁ t₂ t₂' hv₁ ht₂⟩
      | inr h₁ =>
          obtain ⟨t₁', ht₁⟩ := h₁
          exact ⟨.p t₁' t₂, .plusLeft t₁ t₁' t₂ ht₁⟩

--  This important property is called *strong progress*, because every term
--  either is a value or can "make progress" by stepping to some other
--  term. (The qualifier "strong" distinguishes it from a more refined
--  version that we'll see in later chapters, called simply *progress*.)
--
--  The idea of "making progress" can be extended to tell us something
--  interesting about values in this language: they are exactly the terms
--  that do *not* make progress in this sense. Let's give a name to "terms
--  that cannot make progress." We'll call them *normal forms*.

def IsNormalForm {X : Type} (R : Relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'

--  Note that this definition specifies what it is to be a normal form for
--  an *arbitrary* relation `R` over an arbitrary type `X`, not just for
--  the particular single-step reduction relation over terms that we are
--  interested in at the moment. We'll re-use the same terminology for
--  talking about other relations later in the course.

--  We can use this terminology to generalize the observation we made in
--  the strong progress theorem: in this language (though not necessarily,
--  in general), normal forms and values are actually the same thing.

theorem value_is_nf (v : Tm) (h : IsValue v) : IsNormalForm Step v := by
  intro hc
  obtain ⟨t', ht⟩ := hc
  cases h with
  | const n => cases ht

theorem nf_is_value (t : Tm) (h : IsNormalForm Step t) : IsValue t := by
  cases strong_progress t with
  | inl hv => exact hv
  | inr hstep => exact absurd hstep h

theorem nf_same_as_value (t : Tm) : IsNormalForm Step t ↔ IsValue t :=
  ⟨nf_is_value t, value_is_nf t⟩

--  Note to developers (Kihong Heo @KihongHeo):
--      Tactic `absurd` is first introduced here. Do we want to explain it?

--  Note to developers (Daniel Sainati @dsainati1):
--      I think some of these proofs were originally Claude-generated, so
--      we probably want to redo them from scratch, in which case
--      introducing absurd is likely not necessary.

--  Why is this interesting? Because `IsValue` is a *syntactic* concept —
--  it is defined by looking at the way a term is written — while
--  `IsNormalForm` is a *semantic* one — it is defined by looking at how
--  the term steps.
--
--  It is not obvious that these concepts should characterize the same set
--  of terms!
--
--  Indeed, we could easily have written the definitions (incorrectly) so
--  that they would *not* coincide.
--
--  Suppose, for example, we define `IsValue` so that it includes some
--  terms that are not finished reducing. (Even if you don't work the
--  exercise `value_not_same_as_normal_form1` below and the following ones,
--  make sure you can think of an example of such a term.)

namespace Temp1

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)
  | funny (t₁ : Tm) (n : Nat) : IsValue (.p t₁ (.c n))     -- <---

inductive Step : Tm → Tm → Prop where
  | plus (n₁ n₂ : Nat) : Step (.p (.c n₁) (.c n₂)) (.c (n₁ + n₂))
  | plusLeft (t₁ t₁' t₂ : Tm) (h : Step t₁ t₁') : Step (.p t₁ t₂) (.p t₁' t₂)
  | plusRight (v₁ t₂ t₂' : Tm) (hv : IsValue v₁) (h : Step t₂ t₂') : Step (.p v₁ t₂) (.p v₁ t₂')

--   ----------------------------------------

--  _Quiz:_

--  Using this wrong definition of `IsValue`, to how many different values
--  does the following term reduce in zero or more steps?

--  .p (.p (.c 1) (.c 2)) (.c 3)

--   ----------------------------------------

--  _Quiz:_

--  To how many different terms does the following term `Step` (in one
--  step)?

--  .p (.p (.c 1) (.c 2)) (.p (.c 3) (.c 4))

--   ----------------------------------------

--  ### Exercise (3 stars): value_not_same_as_normal_form1 (Optional) ⭐⭐⭐

theorem value_not_same_as_normal_form :
    ∃ v, IsValue v ∧ ¬ IsNormalForm Step v := by
  apply Exists.intro (.p (.c 0) (.c 0))
  apply And.intro (.funny _ 0)
  sorry

end Temp1

--  ### Exercise (2 stars): value_not_same_as_normal_form2 (Optional) ⭐⭐

--  Or we might (again, wrongly) define `Step` so that it permits something
--  designated as a value to reduce further. We again lose the property
--  that values are the same as normal forms.

namespace Temp2

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)               -- Original definition

inductive Step : Tm → Tm → Prop where
  | funny (n : Nat) : Step (.c n) (.p (.c n) (.c 0))     -- <--- NEW
  | plus (n₁ n₂ : Nat) : Step (.p (.c n₁) (.c n₂)) (.c (n₁ + n₂))
  | plusLeft (t₁ t₁' t₂ : Tm) (h : Step t₁ t₁') : Step (.p t₁ t₂) (.p t₁' t₂)
  | plusRight (v₁ t₂ t₂' : Tm) (hv : IsValue v₁) (h : Step t₂ t₂') : Step (.p v₁ t₂) (.p v₁ t₂')

--   ----------------------------------------

--  _Quiz:_

--  With this definition, to how many different terms does the following
--  term step (in exactly one step)?

--  .p (.c 1) (.c 3)

--   ----------------------------------------

theorem value_not_same_as_normal_form :
    ∃ v, IsValue v ∧ ¬ IsNormalForm Step v := by
  apply Exists.intro (.c 5)
  apply And.intro (.const 5)
  sorry

end Temp2

--  ### Exercise (3 stars): value_not_same_as_normal_form3 (Optional) ⭐⭐⭐

--  Finally, we might define `IsValue` and `Step` so that there is some
--  term that is *not* a value but that *also* cannot take a step. Such
--  terms are said to be *stuck*. In this case, this is caused by a mistake
--  in the semantics, but we will also see situations where, even in a
--  correct language definition, it makes sense to allow some terms to be
--  stuck. (Note that `plusRight` is missing below.)

namespace Temp3

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)

inductive Step : Tm → Tm → Prop where
  | plus (n₁ n₂ : Nat) : Step (.p (.c n₁) (.c n₂)) (.c (n₁ + n₂))
  | plusLeft (t₁ t₁' t₂ : Tm) (h : Step t₁ t₁') : Step (.p t₁ t₂) (.p t₁' t₂)

--   ----------------------------------------

--  _Quiz:_

--  With this definition, to how many terms does the following term step
--  (in one step)?

--  .p (.c 1) (.p (.c 1) (.c 2))

--   ----------------------------------------

theorem value_not_same_as_normal_form :
    ∃ t, ¬ IsValue t ∧ IsNormalForm Step t := by
  apply Exists.intro (.p (.c 1) (.p (.c 1) (.c 2)))
  apply And.intro
  · sorry
  · sorry

end Temp3

--  ## Multi-Step Reduction

--  We've been working so far with the *single-step reduction* relation
--  `⟶`, which formalizes the individual steps of an abstract machine for
--  executing programs. We can use the same machine to reduce programs to
--  completion — to find out what final result they yield. This can be
--  formalized as follows:
--
--  - First, we define a *multi-step reduction relation* `⟶*`, which
--    relates terms `t` and `t'` if `t` can reach `t'` by any number
--    (including zero) of single reduction steps.
--
--  - Then we define a "result" of a term `t` as a normal form that `t` can
--    reach by multi-step reduction.
--
--  Since we'll want to reuse the idea of multi-step reduction many times
--  with many different single-step relations, let's define the concept
--  generically. Given a relation `R` (e.g., the step relation `⟶`), we
--  define a new relation `Multi R`, called the *multi-step closure of
--  `R`*, as follows.

inductive Multi {X : Type} (R : Relation X) : X → X → Prop where
  | refl (x : X) : Multi R x x
  | step (x y z : X) (h₁ : R x y) (h₂ : Multi R y z) : Multi R x z

--  Note to developers (berberman):
--      I would make some arguments implicit to proivde a cleaner interface
--      (FYI the [mathlib
--      version](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html#Relation.ReflTransGen))

--  The effect of this definition is that `Multi R` relates two elements
--  `x` and `y` if
--
--  - `x = y`, or
--
--  - `R x y`, or
--
--  - there is some nonempty sequence `z₁`, `z₂` , ..., `zₙ` such that
--
--    `R x₁ z₁,
--    R z₁ z₂,
--    ...,
--    R zₙ y.`
--
--  Intuitively, if `R` describes a single-step of computation, then
--  `z₁ ... zₙ` are the intermediate steps of computation that get us from
--  `x` to `y`.

--  We write `⟶*` for the `Multi Step` relation on terms

notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

--  The relation `Multi R` has several crucial properties.

--  First, it is obviously *reflexive* (a term can execute to itself by
--  taking zero steps). That is just what the `Multi.refl` constructor
--  says, so such a goal can always be closed with `exact .refl _`. It
--  comes up often enough that it is worth registering the constructor as a
--  *reflexivity lemma*, with the `@[refl]` attribute. The `rfl` tactic
--  then closes a zero-step execution exactly as it closes `x = x`:

attribute [refl] Multi.refl

example : (.c 5 : Tm) ⟶* .c 5 := by rfl

--  This pays off at the *end* of a reduction sequence too: the final
--  `Multi.step` leaves a goal relating a term to itself, which `rfl`
--  discharges.

example : (.p (.c 1) (.c 2)) ⟶* .c (1 + 2) := by
  apply Multi.step (y := .c (1 + 2))
  · exact .plus 1 2
  · rfl

--  Second, it *contains* `R` — single-step reductions are a particular
--  case of multi-step executions. (It is this fact that justifies the word
--  "closure" in "multi-step closure of `R`.")

theorem multi_single {X : Type} (R : Relation X) (x y : X) (h : R x y) :
    Multi R x y :=
  .step x y y h (.refl y)

--  Third, `Multi R` is *transitive*.

theorem multi_trans {X : Type} (R : Relation X) (x y z : X)
    (g : Multi R x y) (h : Multi R y z) : Multi R x z := by
  induction g with
  | refl a => exact h
  | step a b c h₁ h₂ ih => exact .step a b z h₁ (ih h)

--  In particular, for the `Multi Step` relation on terms, if `t₁ ⟶* t₂`
--  and `t₂ ⟶* t₃`, then `t₁ ⟶* t₃`.

--   ----------------------------------------

--  _Quiz:_

--  Which of the following relations on numbers *cannot* be expressed as
--  `Multi R` for some `R`?
--
--  (A) less than or equal (B) strictly less than (C) equal (D) none of the
--  above

--   ----------------------------------------

--  ### Examples

example :
    (.p (.p (.c 0) (.c 3)) (.p (.c 2) (.c 4))) ⟶* .c ((0 + 3) + (2 + 4)) := by
  apply Multi.step (y := .p (.c (0 + 3)) (.p (.c 2) (.c 4)))
  · exact .plusLeft _ _ _ (.plus 0 3)
  apply Multi.step (y := .p (.c (0 + 3)) (.c (2 + 4)))
  · exact .plusRight _ _ _ (.const _) (.plus 2 4)
  · exact multi_single _ _ _ (.plus (0 + 3) (2 + 4))

--  ### Exercise (1 star): test_multistep_2 (Optional) ⭐

example : (.c 3 : Tm) ⟶* .c 3 := sorry

--  ### Exercise (1 star): test_multistep_3 (Optional) ⭐

example : (.p (.c 0) (.c 3)) ⟶* .p (.c 0) (.c 3) := sorry

--  ### Exercise (2 stars): test_multistep_4 ⭐⭐

example :
    (.p (.c 0) (.p (.c 2) (.p (.c 0) (.c 3))))
      ⟶* (.p (.c 0) (.c (2 + (0 + 3)))) := by
  sorry

--  ### Exercise (2 stars): test_multistep_rfl ⭐⭐

--  Prove the following reduction, ending the chain with `rfl` instead of
--  `multi_single`.

example : (.p (.p (.c 1) (.c 2)) (.c 4)) ⟶* .c ((1 + 2) + 4) := by
  sorry

--  ### Normal Forms Again

--  If `t` reduces to `t'` in zero or more steps and `t'` is a normal form,
--  we say that "`t'` is *a normal form of* `t`."

def IsNormalFormOf {X : Type} (R : Relation X) (t t' : X) : Prop :=
  Multi R t t' ∧ IsNormalForm R t'

--  We have already seen that, for our language, single-step reduction is
--  deterministic — i.e., a given term can take a single step in at most
--  one way. It follows that, if `t` can reach a normal form, then this
--  normal form is unique.
--
--  In other words, we can actually pronounce `IsNormalFormOf t t'` as
--  "`t'` is *the* normal form of `t`."

--  ### Exercise (3 stars): normal_forms_unique (Optional) ⭐⭐⭐

theorem normal_forms_unique : Deterministic (IsNormalFormOf Step) := by
  -- We recommend using this initial setup as-is!
  intro x y₁ y₂ p₁ p₂
  obtain ⟨p₁₁, p₁₂⟩ := p₁
  obtain ⟨p₂₁, p₂₂⟩ := p₂
  sorry

--  Indeed, something stronger is true for this language (though not for
--  all the languages we will see): the reduction of *any* term `t` will
--  eventually reach a normal form in a finite number of steps — i.e.,
--  `IsNormalFormOf` is a *total* function. We say the `Step` relation is
--  *normalizing*. To prove it, we need a couple of congruence lemmas.

def Normalizing {X : Type} (R : Relation X) : Prop :=
  ∀ t, ∃ t', IsNormalFormOf R t t'

theorem multistep_congr_1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶* t₁') : (.p t₁ t₂) ⟶* (.p t₁' t₂) := by
  induction h with
  | refl x => exact .refl _
  | step x y z h₁ h₂ ih => exact .step _ (.p y t₂) _ (.plusLeft x y t₂ h₁) ih

--  ### Exercise (2 stars): multistep_congr_2 ⭐⭐

theorem multistep_congr_2 (v₁ t₂ t₂' : Tm) (hv : IsValue v₁) (h : t₂ ⟶* t₂') :
    (.p v₁ t₂) ⟶* (.p v₁ t₂') := by
  sorry

--  With these lemmas in hand, the main proof is a straightforward
--  induction.
--
--  *Theorem*: The `Step` relation is normalizing — i.e., for every `t`
--  there exists some `t'` such that `t` reduces to `t'` and `t'` is a
--  normal form.
--
--  *Proof sketch*: By induction on terms. There are two cases:
--
--  - `t = c n` for some `n`. Here `t` doesn't take a step, and we have
--    `t' = t`. We derive the left-hand side by reflexivity and the
--    right-hand side by observing (a) that values are normal forms (by
--    `nf_same_as_value`) and (b) that `t` is a value (by `const`).
--
--  - `t = p t₁ t₂` for some `t₁` and `t₂`. By the IH, `t₁` and `t₂` reduce
--    to normal forms `t₁'` and `t₂'`. Recall that normal forms are values
--    (by `nf_same_as_value`); we therefore know that `t₁' = c n₁` and
--    `t₂' = c n₂` for some `n₁` and `n₂`. We combine the `⟶*` derivations
--    for `t₁` and `t₂` using `multistep_congr_1` and `multistep_congr_2`
--    to prove that `p t₁ t₂` reduces in many steps to `t' = c (n₁ + n₂)`.
--    Finally, `c (n₁ + n₂)` is a value, which is in turn a normal form.

theorem step_normalizing : Normalizing Step := by
  intro t
  induction t with
  | c n => exact ⟨.c n, .refl _, (nf_same_as_value _).mpr (.const n)⟩
  | p t₁ t₂ ih₁ ih₂ =>
      obtain ⟨t₁', hs₁, hnf₁⟩ := ih₁
      obtain ⟨t₂', hs₂, hnf₂⟩ := ih₂
      obtain ⟨n₁⟩ := (nf_same_as_value _).mp hnf₁
      obtain ⟨n₂⟩ := (nf_same_as_value _).mp hnf₂
      apply Exists.intro (.c (n₁ + n₂))
      apply And.intro _ ((nf_same_as_value _).mpr (.const _))
      apply multi_trans _ _ _ _ (multistep_congr_1 t₁ (.c n₁) t₂ hs₁)
      apply multi_trans _ _ _ _ (multistep_congr_2 (.c n₁) t₂ (.c n₂) (.const n₁) hs₂)
      exact multi_single _ _ _ (.plus n₁ n₂)

--  ### Equivalence of Big-Step and Small-Step

--  Having defined the operational semantics of our tiny programming
--  language in two different ways (big-step and small-step), it makes
--  sense to ask whether these definitions actually define the same thing!
--
--  They do, though it takes a little work to show it. The details are left
--  as an exercise. We consider the two implications separately. First,
--  big-step evaluation implies multi-step reduction to a value.

--  ### Exercise (3 stars): multistep_of_eval ⭐⭐⭐

theorem multistep_of_eval (t : Tm) (n : Nat) (h : t ⇓ n) : t ⟶* .c n := by
  sorry

--  The key ideas in the proof can be seen in the following picture:

--  p t₁ t₂ ⟶            (by plusLeft)
--  p t₁' t₂ ⟶           (by plusLeft)
--  p t₁'' t₂ ⟶          (by plusLeft)
--  ...
--  p (c n₁) t₂ ⟶        (by plusRight)
--  p (c n₁) t₂' ⟶       (by plusRight)
--  p (c n₁) t₂'' ⟶      (by plusRight)
--  ...
--  p (c n₁) (c n₂) ⟶    (by plus)
--  c (n₁ + n₂)

--  That is, the multi-step reduction of a term of the form `p t₁ t₂`
--  proceeds in three phases:
--
--  - First, we use `plusLeft` some number of times to reduce `t₁` to a
--    normal form, which must (by `nf_same_as_value`) be a term of the form
--    `c n₁` for some `n₁`.
--
--  - Next, we use `plusRight` some number of times to reduce `t₂` to a
--    normal form, which must again be a term of the form `c n₂` for some
--    `n₂`.
--
--  - Finally, we use `plus` one time to reduce `p (c n₁) (c n₂)` to
--    `c (n₁ + n₂)`.
--
--  To formalize this intuition, you'll need the congruence lemmas from
--  above, plus some basic properties of `⟶*` (that it is reflexive,
--  transitive, and includes `⟶`).

--  ### Exercise (3 stars): multistep_of_eval_inf (Optional) ⭐⭐⭐

--  Write a detailed informal version of the proof of `multistep_of_eval`.
--  (A paper exercise — there is no Lean proof to fill in here.)

--  _Theorem_: for all `t`, `n`, if `t ⇓ n` then `t ⟶* c n`.
--
--  _Proof_: By induction on a derivation of `t ⇓ n`.
--
--    - Suppose the final rule used to show `t ⇓ n` is `const`.  Then `t = c n`.
--      We must show `c n ⟶* c n`.  This holds by `refl`.
--
--    - Suppose the final rule used to show `t ⇓ n` is `plus`.  Then
--      `t = p t₁ t₂`, and we know that `t₁ ⇓ c n₁` and `t₂ ⇓ c n₂` for some
--      `n₁` and `n₂`, with `n = n₁ + n₂`.  The IH tells us that `t₁ ⟶* c n₁` and
--      `t₂ ⟶* c n₂`.  We must show that `p t₁ t₂ ⟶* c (n₁ + n₂)`.
--
--      First, `p t₁ t₂ ⟶* p (c n₁) t₂` by `multistep_congr_1` and the multistep
--      derivation for `t₁`.  Observing that `c n₁` is a value, we also have
--      `p (c n₁) t₂ ⟶* p (c n₁) (c n₂)` by `multistep_congr_2` and the multistep
--      derivation for `t₂`.  It's also easy to see by `plus` that
--      `p (c n₁) (c n₂) ⟶ c (n₁ + n₂)`, and so, by `Step` and
--      `refl`, that the same is true for `⟶*`.  We can now use transitivity
--      of `⟶*` to stitch these derivations together, proving
--      `p t₁ t₂ ⟶* c (n₁ + n₂)`.

--  For the converse, we need one lemma, which establishes a relation
--  between single-step reduction and big-step evaluation. A single step
--  preserves the big-step value.

--  ### Exercise (3 stars): eval_of_step ⭐⭐⭐

theorem eval_of_step (t t' : Tm) (n : Nat) (hs : t ⟶ t') (he : t' ⇓ n) : t ⇓ n := by
  sorry

--  The fact that small-step reduction implies big-step evaluation is now
--  straightforward to prove, once we have factored out the observation
--  that every normal form is a value. The proof proceeds by induction on
--  the multi-step reduction sequence that is buried in the hypothesis
--  `IsNormalFormOf t t'`. (Make sure you understand the statement before
--  you start to work on the proof.)

--  ### Exercise (3 stars): eval_of_multistep ⭐⭐⭐

theorem eval_of_multistep (t t' : Tm) (h : IsNormalFormOf Step t t') :
    ∃ n, t' = .c n ∧ t ⇓ n := by
  sorry

--  ### Exercise (3 stars): interp_tm (Optional) ⭐⭐⭐

--  Remember that we also defined big-step evaluation of terms as a
--  function `evalF`. Prove that it is equivalent to the relational
--  semantics. (Hint: we just proved that `Eval` and `multistep` are
--  equivalent, so logically it doesn't matter which you choose. One will
--  be easier than the other, though!)

theorem evalF_eval (t : Tm) (n : Nat) : evalF t = n ↔ t ⇓ n := by
  sorry

--  ## Small-Step Slang

--  Now for a more serious example: a small-step semantics for the richer
--  arithmetic and boolean expressions of the Slang chapter (with
--  subtraction, multiplication, and the boolean operators) rather than the
--  two-constructor toy language we have used so far.
--
--  The small-step reduction relations for these expressions are
--  straightforward extensions of the tiny language we've been working up
--  to now. To make them easier to read, we introduce the symbolic
--  notations `⟶a` and `⟶b` for the arithmetic and boolean step relations.

--  We work in the `Slang` namespace, reusing the arithmetic and boolean
--  expression syntax (`Aexp`, `Bexp`) and the big-step evaluator
--  (`Aexp.eval`) from the `Slang` chapter:

namespace Slang

--  ### Arithmetic Expressions

--  The arithmetic *values* (the normal forms of the small-step relation
--  below) are just the numeric literals:

inductive IsAValue : Aexp → Prop where
  | num (n : Nat) : IsAValue (.num n)

--  Here is the small-step relation for arithmetic expressions. A compound
--  expression reduces its left operand first; once that is a value, it
--  reduces its right operand; once both are values, it computes the
--  result. (We show the rules for `+` in full; those for `−` and `×` have
--  exactly the same shape.)

--  a₁ ⟶a a₁'
--                     --------------------             (plusLeft)
--                     a₁ + a₂ ⟶a a₁' + a₂
--
--                   IsAValue v₁      a₂ ⟶a a₂'
--                   ---------------------------        (plusRight)
--                     v₁ + a₂ ⟶a v₁ + a₂'
--
--                   -------------------------          (plus)
--                   n₁ + n₂ ⟶a num (n₁ + n₂)

inductive AStep : Aexp → Aexp → Prop where
  | plusLeft (a₁ a₁' a₂ : Aexp) (h : AStep a₁ a₁') : AStep (.plus a₁ a₂) (.plus a₁' a₂)
  | plusRight (v₁ a₂ a₂' : Aexp) (hv : IsAValue v₁) (h : AStep a₂ a₂') :
      AStep (.plus v₁ a₂) (.plus v₁ a₂')
  | plus (n₁ n₂ : Nat) :  AStep (.plus (.num n₁) (.num n₂)) (.num (n₁ + n₂))
  | minusLeft (a₁ a₁' a₂ : Aexp) (h : AStep a₁ a₁') : AStep (.minus a₁ a₂) (.minus a₁' a₂)
  | minusRight (v₁ a₂ a₂' : Aexp) (hv : IsAValue v₁) (h : AStep a₂ a₂') :
      AStep (.minus v₁ a₂) (.minus v₁ a₂')
  | minus (n₁ n₂ : Nat) : AStep (.minus (.num n₁) (.num n₂)) (.num (n₁ - n₂))
  | multLeft (a₁ a₁' a₂ : Aexp) (h : AStep a₁ a₁') : AStep (.mult a₁ a₂) (.mult a₁' a₂)
  | multRight (v₁ a₂ a₂' : Aexp) (hv : IsAValue v₁) (h : AStep a₂ a₂') :
      AStep (.mult v₁ a₂) (.mult v₁ a₂')
  | mult (n₁ n₂ : Nat) : AStep (.mult (.num n₁) (.num n₂)) (.num (n₁ * n₂))

scoped notation:40 a:41 " ⟶a " a':41 => AStep a a'

--  Notice that `AStep` has exactly the shape `Aexp → Aexp → Prop` — i.e.,
--  it is a `Relation Aexp` in the sense of the *Relations* section above.
--  So the generic vocabulary from that section (`Deterministic`,
--  `IsNormalForm`, the multi-step closure `Multi`, ...) applies to it
--  directly.

--  Here is a one-step reduction: since the left operand `3` is already a
--  value, the right operand is the one that takes a step.

example :
    (Aexp.plus (.num 3) (.plus (.num 2) (.num 1))) ⟶a (.plus (.num 3) (.num 3)) :=
  .plusRight _ _ _ (.num 3) (.plus 2 1)

--  ### Exercise (2 stars): strong_progress_arith ⭐⭐

--  Every arithmetic expression is either a value or can take a step — the
--  same *strong progress* property we proved for the toy language, now for
--  the richer `Slang` arithmetic expressions.

theorem strong_progress_arith (a : Aexp) : IsAValue a ∨ ∃ a', a ⟶a a' := by
  sorry

--  ### Boolean Expressions

--  The small-step relation for boolean expressions reduces the arithmetic
--  subexpressions of a comparison (using `⟶a`) and then applies the
--  comparison, and it short-circuits `¬` and `∧` on boolean literals.
--
--  We are not actually going to bother to define boolean values, since
--  they aren't needed in the definition of `⟶b` below (why?), though they
--  might be if our language were a bit more complicated (why?).
--
--  Again we show a representative sample; `neq`, `le`, and `gt` follow the
--  same pattern as `eq`.

--  a₁ ⟶a a₁'
--                    --------------------             (eqLeft)
--                    a₁ = a₂ ⟶b a₁' = a₂
--
--                  IsAValue v₁      a₂ ⟶a a₂'
--                  ---------------------------        (eqRight)
--                    v₁ = a₂ ⟶b v₁ = a₂'
--
--                    ---------------------            (eq)
--                    n₁ = n₂ ⟶b (n₁ = n₂)
--
--                          b₁ ⟶b b₁'
--                        --------------               (notStep)
--                        ¬ b₁ ⟶b ¬ b₁'
--
--                      ----------------               (notTrue)
--                      ¬ true ⟶b false
--
--                    ---------------------            (andFalse)
--                    false ∧ b₂ ⟶b false

--  Here are the formal rules.

inductive BStep : Bexp → Bexp → Prop where
  | eqLeft (a₁ a₁' a₂ : Aexp) (h : AStep a₁ a₁') : BStep (.eq a₁ a₂) (.eq a₁' a₂)
  | eqRight (v₁ a₂ a₂' : Aexp) (hv : IsAValue v₁) (h : AStep a₂ a₂') :
      BStep (.eq v₁ a₂) (.eq v₁ a₂')
  | eq (n₁ n₂ : Nat) : BStep (.eq (.num n₁) (.num n₂)) (.bool (decide (n₁ = n₂)))
  | neqLeft (a₁ a₁' a₂ : Aexp) (h : AStep a₁ a₁') : BStep (.neq a₁ a₂) (.neq a₁' a₂)
  | neqRight (v₁ a₂ a₂' : Aexp) (hv : IsAValue v₁) (h : AStep a₂ a₂') :
      BStep (.neq v₁ a₂) (.neq v₁ a₂')
  | neq (n₁ n₂ : Nat) : BStep (.neq (.num n₁) (.num n₂)) (.bool (decide (n₁ ≠ n₂)))
  | leLeft (a₁ a₁' a₂ : Aexp) (h : AStep a₁ a₁') : BStep (.le a₁ a₂) (.le a₁' a₂)
  | leRight (v₁ a₂ a₂' : Aexp) (hv : IsAValue v₁) (h : AStep a₂ a₂') :
      BStep (.le v₁ a₂) (.le v₁ a₂')
  | le (n₁ n₂ : Nat) : BStep (.le (.num n₁) (.num n₂)) (.bool (decide (n₁ ≤ n₂)))
  | gtLeft (a₁ a₁' a₂ : Aexp) (h : AStep a₁ a₁') : BStep (.gt a₁ a₂) (.gt a₁' a₂)
  | gtRight (v₁ a₂ a₂' : Aexp) (hv : IsAValue v₁) (h : AStep a₂ a₂') :
      BStep (.gt v₁ a₂) (.gt v₁ a₂')
  | gt (n₁ n₂ : Nat) : BStep (.gt (.num n₁) (.num n₂)) (.bool (decide (n₁ > n₂)))
  | notStep (b₁ b₁' : Bexp) (h : BStep b₁ b₁') : BStep (.not b₁) (.not b₁')
  | notTrue : BStep (.not (.bool true)) (.bool false)
  | notFalse : BStep (.not (.bool false)) (.bool true)
  | andStep (b₁ b₁' b₂ : Bexp) (h : BStep b₁ b₁') : BStep (.and b₁ b₂) (.and b₁' b₂)
  | andTrueStep (b₂ b₂' : Bexp) (h : BStep b₂ b₂') :
      BStep (.and (.bool true) b₂) (.and (.bool true) b₂')
  | andFalse (b₂ : Bexp) : BStep (.and (.bool false) b₂) (.bool false)
  | andTrueTrue : BStep (.and (.bool true) (.bool true)) (.bool true)
  | andTrueFalse : BStep (.and (.bool true) (.bool false)) (.bool false)

scoped notation:40 b:41 " ⟶b " b':41 => BStep b b'

--  A boolean example — the left comparison operand reduces first:

example :
    (Bexp.le (.plus (.num 1) (.num 1)) (.num 3)) ⟶b (.le (.num 2) (.num 3)) :=
  .leLeft _ _ _ (.plus 1 1)

--   ----------------------------------------

--  _Quiz:_

--  Which of these properties does this small-step semantics for `Slang`
--  expressions satisfy? (Yes or No for each.)
--
--  - determinism
--  - strong progress (every non-value takes a step)
--  - values and normal forms coincide (i.e., there are no "stuck" terms)
--  - the step relation is normalizing (i.e., evaluation always terminates)

--   ----------------------------------------

--  Let us make good on the first of those answers. Both step relations are
--  *deterministic*: the value guards on the "step the right operand" rules
--  mean that at most one rule ever applies to a given term.

--  ### Exercise (3 stars): astep_deterministic ⭐⭐⭐

--  The arithmetic step relation is deterministic. (Structurally this is
--  the value-based determinism proof from the toy language, repeated for
--  `+`, `−`, and `×`; the impossible cross-cases close because a value
--  `num n` cannot step.)

theorem astep_deterministic : Deterministic AStep := by
  sorry

--  ### Exercise (3 stars): bstep_deterministic ⭐⭐⭐

--  The boolean step relation is deterministic too. The comparison cases
--  (`eq`, `neq`, `le`, `gt`) reduce their operands with `⟶a`, so they
--  inherit determinism from `astep_deterministic`; `¬` and the
--  short-circuiting `∧` contribute only base cases.

theorem bstep_deterministic : Deterministic BStep := by
  sorry

--  ### Nondeterministic Evaluation

--  The relation `⟶a` above bakes in a *left-to-right* evaluation order:
--  the rule `plusRight` can fire only once the left operand is already a
--  value (`IsAValue v₁`). But nothing about the *meaning* of `+` requires
--  that order — we could just as well reduce the right operand first, or
--  interleave the two. Different orders are exactly what a concurrent or
--  optimizing implementation might choose, so it is natural to ask whether
--  the choice can affect the final answer.
--
--  Let's find out. We define a second small-step relation, `⟶n`, that is
--  identical to `⟶a` except that we *drop* the `IsAValue` side-condition:
--  either operand may take a step at any time.

inductive ANStep : Aexp → Aexp → Prop where
  | plusLeft (a₁ a₁' a₂ : Aexp) (h : ANStep a₁ a₁') :  ANStep (.plus a₁ a₂) (.plus a₁' a₂)
  | plusRight (a₁ a₂ a₂' : Aexp) (h : ANStep a₂ a₂') : ANStep (.plus a₁ a₂) (.plus a₁ a₂')
  | plus (n₁ n₂ : Nat) : ANStep (.plus (.num n₁) (.num n₂)) (.num (n₁ + n₂))
  | minusLeft (a₁ a₁' a₂ : Aexp) (h : ANStep a₁ a₁') : ANStep (.minus a₁ a₂) (.minus a₁' a₂)
  | minusRight (a₁ a₂ a₂' : Aexp) (h : ANStep a₂ a₂') : ANStep (.minus a₁ a₂) (.minus a₁ a₂')
  | minus (n₁ n₂ : Nat) : ANStep (.minus (.num n₁) (.num n₂)) (.num (n₁ - n₂))
  | multLeft (a₁ a₁' a₂ : Aexp) (h : ANStep a₁ a₁') : ANStep (.mult a₁ a₂) (.mult a₁' a₂)
  | multRight (a₁ a₂ a₂' : Aexp) (h : ANStep a₂ a₂') : ANStep (.mult a₁ a₂) (.mult a₁ a₂')
  | mult (n₁ n₂ : Nat) : ANStep (.mult (.num n₁) (.num n₂)) (.num (n₁ * n₂))

scoped notation:40 a:41 " ⟶n " a':41 => ANStep a a'

--  Unlike `⟶a`, this relation really is nondeterministic: a single term
--  can step in two different ways, depending on which operand we choose to
--  advance.

theorem anstep_not_deterministic : ¬ Deterministic ANStep := by
  intro hd
  have s₁ : ANStep (.plus (.plus (.num 1) (.num 1)) (.plus (.num 2) (.num 2)))
      (.plus (.num 2) (.plus (.num 2) (.num 2))) :=
    .plusLeft _ _ _ (.plus 1 1)
  have s₂ : ANStep (.plus (.plus (.num 1) (.num 1)) (.plus (.num 2) (.num 2)))
      (.plus (.plus (.num 1) (.num 1)) (.num 4)) :=
    .plusRight _ _ _ (.plus 2 2)
  have heq := hd _ _ _ s₁ s₂
  simp at heq

--  Remarkably, this nondeterminism does *not* affect the final answer. The
--  key observation is that a single step never changes the big-step
--  *value* of an expression — whichever operand we advance, `eval` is
--  preserved.

--  ### Exercise (2 stars): anstep_preserves_eval ⭐⭐

--  Prove that one nondeterministic step leaves the big-step value
--  unchanged. *Hint:* induction on the step derivation; each case is
--  immediate from `eval` and, where present, the induction hypothesis.

theorem anstep_preserves_eval (a a' : Aexp) (h : a ⟶n a') : a.eval = a'.eval := by
  sorry

--  This lifts to any number of steps by a routine induction on the
--  multi-step derivation:

theorem multi_anstep_preserves_eval (a a' : Aexp) (h : Multi ANStep a a') : a.eval = a'.eval := by
  induction h with
  | refl x => rfl
  | step x y z h₁ _ ih => rw [anstep_preserves_eval x y h₁]; exact ih

--  Finally we can compare the two semantics. The deterministic relation
--  `⟶a` is a *special case* of `⟶n`: every `⟶a` step is also an `⟶n` step
--  (it merely happens, in addition, to respect the `IsAValue` guard).

theorem astep_imp_anstep (a a' : Aexp) (h : a ⟶a a') : a ⟶n a' := by
  induction h with
  | plusLeft a₁ a₁' a₂ _ ih => exact .plusLeft a₁ a₁' a₂ ih
  | plusRight v₁ a₂ a₂' _ _ ih => exact .plusRight v₁ a₂ a₂' ih
  | plus n₁ n₂ => exact .plus n₁ n₂
  | minusLeft a₁ a₁' a₂ _ ih => exact .minusLeft a₁ a₁' a₂ ih
  | minusRight v₁ a₂ a₂' _ _ ih => exact .minusRight v₁ a₂ a₂' ih
  | minus n₁ n₂ => exact .minus n₁ n₂
  | multLeft a₁ a₁' a₂ _ ih => exact .multLeft a₁ a₁' a₂ ih
  | multRight v₁ a₂ a₂' _ _ ih => exact .multRight v₁ a₂ a₂' ih
  | mult n₁ n₂ => exact .mult n₁ n₂

theorem multi_astep_imp_anstep (a a' : Aexp) (h : Multi AStep a a') : Multi ANStep a a' := by
  induction h with
  | refl x => exact .refl x
  | step x y z h₁ _ ih => exact .step x y z (astep_imp_anstep x y h₁) ih

--  ### Exercise (3 stars): astep_anstep_agree ⭐⭐⭐

--  Now put the pieces together: prove that the deterministic and
--  nondeterministic semantics always compute the *same* final result. That
--  is, if `a` fully reduces to `.num n₁` under `⟶a` and to `.num n₂` under
--  `⟶n`, then `n₁ = n₂`.
--
--  *Hint:* both `.num n₁` and `.num n₂` are reachable by `⟶n` (use
--  `multi_astep_imp_anstep` for the first), and `⟶n` preserves `eval`.

theorem astep_anstep_agree (a : Aexp) (n₁ n₂ : Nat)
    (hd : Multi AStep a (.num n₁)) (hn : Multi ANStep a (.num n₂)) : n₁ = n₂ := by
  sorry

--  So even though `⟶n` is genuinely nondeterministic, the value it
--  eventually produces is completely determined — and it is the same value
--  the deterministic machine (and the big-step evaluator) computes. This
--  *confluence to a unique result* is exactly the property one wants when
--  reordering or parallelizing the evaluation of pure expressions.

--  ### A Small-Step Stack Machine

--  Our last example is a small-step semantics for a *stack machine* that
--  evaluates arithmetic expressions. The machine's instructions push a
--  constant or combine the top two stack entries. The machine's behavior
--  should match the big-step `Aexp.eval` function defined earlier.
--
--  A *program* is a list of instructions, and the *stack* is a list of
--  numbers.

inductive SInstr where
  | push (n : Nat)
  | plus
  | minus
  | mult

abbrev Stack := List Nat
abbrev Prog := List SInstr

--  The compiler emits code in the postfix order sketched above:

def compile : Aexp → Prog
  | .num n => [.push n]
  | .plus a₁ a₂ => compile a₁ ++ compile a₂ ++ [.plus]
  | .minus a₁ a₂ => compile a₁ ++ compile a₂ ++ [.minus]
  | .mult a₁ a₂ => compile a₁ ++ compile a₂ ++ [.mult]

example : compile (.plus (.num 2) (.num 3)) = [.push 2, .push 3, .plus] := rfl

--  Now the small-step machine itself: each step consumes the next
--  instruction and updates the stack.

inductive StackStep : Prog × Stack → Prog × Stack → Prop where
  | push (p : Prog) (stk : Stack) (n : Nat) : StackStep (.push n :: p, stk) (p, n :: stk)
  | plus (p : Prog) (stk : Stack) (n m : Nat) :
      StackStep (.plus :: p, n :: m :: stk) (p, (m + n) :: stk)
  | minus (p : Prog) (stk : Stack) (n m : Nat) :
      StackStep (.minus :: p, n :: m :: stk) (p, (m - n) :: stk)
  | mult (p : Prog) (stk : Stack) (n m : Nat) :
      StackStep (.mult :: p, n :: m :: stk) (p, (m * n) :: stk)

--  The machine is deterministic:

theorem stack_step_deterministic : Deterministic StackStep := by
  intro x y₁ y₂ h₁ h₂
  cases h₁ <;> cases h₂ <;> rfl

--  ### Exercise (3 stars): compiler_is_correct (Advanced) ⭐⭐⭐

--  Prove the compiler correct: running the compiled program from the empty
--  stack reduces, in some number of steps, to a stack holding exactly the
--  value of the expression.
--
--  *Hint:* this will not go through by a direct induction — the induction
--  hypothesis is too weak. Prove a more general statement first, about
--  running `compile a` followed by *any* leftover program `p`, starting
--  from *any* stack `stk`. (Reassociating the `++`s with
--  `List.append_assoc`, and chaining steps with
--  `multi_trans`/`multi_single`, are the moves you need.)

theorem compiler_is_correct (a : Aexp) :
    Multi StackStep (compile a, []) ([], [a.eval]) := by
  sorry

end Slang

--  ### Automation with `solve_by_elim`

--  When experimenting with definitions of programming languages in Lean,
--  we often want to see what a particular term steps to - i.e., we want to
--  find proofs for goals of the form `t ⟶* t'`. Consider, for example,
--  reducing an arithmetic expression using the small-step relation
--  `AStep`.

example : (.p (.c 3) (.p (.c 3) (.c 4))) ⟶* (.c 10) := by
  apply Multi.step (y := .p (.c 3) (.c 7))
  · apply Step.plusRight
    · apply IsValue.const
    · apply Step.plus
  · apply Multi.step (y := .c 10)
    · apply Step.plus
    · apply Multi.refl

--  Proofs that one term normalizes to another must repeatedly apply
--  `Multi.step` until the term reaches a normal form, with some very
--  simple intermediate steps along the way. Thankfully, we can automate
--  this process with a new tactic: `solve_by_elim`. When supplied with a
--  list of constructors, `solve_by_elim [c₁, c₂, c₃, ...]` will attempt to
--  apply these constructors repeatedly to a goal. It will also
--  automatically attempt to use simple tactics like `rfl`, `trivial`,
--  `congr` and hypotheses from the context in order to solve simple goals.
--  So, for example, the proof above also be written:

example : (.p (.c 3) (.p (.c 3) (.c 4))) ⟶* (.c 10) := by
  repeat apply Multi.step <;>
    try solve_by_elim [Step.plusRight, Step.plusLeft, Step.plus, IsValue.const]

--  This one script would suffice to prove most concrete reduction
--  sequences for this simple language. To make it work for others, we
--  would need to supply constructors for those other languages to
--  `solve_by_elim`. The languages we will study in this book can grow to a
--  large number of constructors for their `Step` relations, so we'd like a
--  way to supply all of them to `solve_by_elim` more easily. Luckily, Lean
--  supports this. We can register a constructor (or lemma) for use with
--  `solve_by_elim` with an `attribute` command:

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Attributes)
--  The command below tags all of these constructors with the `SimpleArith`
--  attribute, which we can then use to automatically pull all of these
--  constructors in when we use `solve_by_elim`. However, due to a
--  limitation of Lean, this attribute needs to be pre-declared in a
--  different file; we can't create it here and then immediately use it.
--
--  For this book, we've predeclared all the attributes we'll use in a file
--  called `AttributeDecls.lean`, following the typical pattern from
--  libraries like Mathlib.
--  END DETAILS

attribute [SimpleArith] Step.plusRight Step.plusLeft Step.plus IsValue.const

--  This `using` option then tells `solve_by_elim` to try to use every
--  constructor we've registered with the supplied attribute:

example : (.p (.c 3) (.p (.c 3) (.c 4))) ⟶* (.c 10) := by
  repeat apply Multi.step <;>
    try solve_by_elim using SimpleArith

--  We can package all this up into a dedicated tactic for solving
--  reduction sequences, which we'll call `normalize`:

syntax "normalize" " using " ident,+ : tactic

macro_rules
  | `(tactic| normalize using $xs,*) =>
    `(tactic|
      first
      | apply Multi.refl
      | (apply Multi.step
         · solve_by_elim (maxDepth := 15) (constructor := false) only using $xs,*
         · normalize using $xs,*))

--  And voilà:

example : (.p (.c 3) (.p (.c 3) (.c 4))) ⟶* (.c 10) := by
  normalize using SimpleArith

--  ### Exercise (1 star): normalize_ex ⭐

--  Use the `normalize` tactic to prove the following. You will need to
--  supply the term `e'` yourself.

theorem normalize_ex : exists e', (.p (.c 3) (.p (.c 2) (.c 1))) ⟶* e' ∧ IsValue e' := by
  sorry

attribute [autogradedProof 3] normalize_ex

-- Built on 2026-09-02 17:28 UTC

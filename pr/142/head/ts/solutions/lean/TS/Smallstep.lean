import TS.Slang

import TS.SFLCompat

-- # Smallstep: Small-step Operational Semantics

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     The `hiding lean` (above in the source file) should not be needed any
--     more and should be removed from all files everywhere it exists.

-- Note to developers (Michael Hicks  @mwhicks1):
--     This chapter adapts Smallstep to follow Slang, the initial part of Imp,
--     on just Aexp and Bexp (without variables). This means that parts of
--     this chapter had to adjust: Concurrent Imp is dropped in favor of
--     Nondeterministic Aexp, and the stack machine is simplified to just
--     Aexps without variables.

-- Note to developers (before next release):
--     In this and later chapters, we are not very consistent about presenting
--     computation rules first and congruence rules after...

-- Note to developers:
--     HIDE: Sometime in the early 2010s, we did some mining past exams for
--     exercises...
--
--     - Loris: No interesting exercise in Finals of 2007-2009-2010-2011.
--       Nothing in second midterms except for 2011.
--
--     - 2011 midterm proposes the following exercise: give the small step
--       relation of FLIP X (alternatively HAVOC, ANYTHING). We could then ask
--       to extend the proof of equivalence of big step vs small step
--       (personally don't like it too much).
--
--     - Maybe we can ask how they would adapt the definition of Hoare triple to
--       small step (maybe in the exam).
--
--     HIDE: BCP: I also have a bunch of slides from earlier offerings of
--     CIS500 that might be good additions to the TERSE notes.
--
--     HIDE: Possible major restructuring: This chapter might better be
--     postponed to later in the course. A big-step presentation of STLC (and
--     maybe even some of the extensions like subtyping?) could come first.
--     However, this would invite a much bigger change, where **all** the
--     variants of STLC (with refs, with subtyping, ...) are done in big-step
--     style. This requires more thought...
--
--     HIDE: Wonder whether it would be interesting to show them how to make a
--     correspondence with a "real abstract machine" at a lower level...?
--     There's a start at an exercise along these lines below.

-- ## Big-step and Small-step Evaluation

-- The evaluators we saw for Slang were formulated in a "big-step" style: they
-- specify how a given expression can be evaluated to its final value "all in
-- one big step":

-- 2 + 2 + 3 * 4 ⇓ 16

-- This style is simple and natural for many purposes -- indeed, Gilles Kahn,
-- who popularized it, called it *natural semantics*. But there are some
-- things it does not do well. In particular, it does not give us a convenient
-- way of talking about *concurrent* programming languages, where the
-- semantics of a program -- the essence of how it behaves -- includes not
-- just which input states get mapped to which output states, but also the
-- intermediate states that it passes through along the way; this is crucial,
-- since these states can also be observed by concurrently executing code.

-- Another shortcoming of the big-step style is more technical but equally
-- critical in many situations. Suppose we want to define a variant of our
-- expression language where a value could be *either* a number *or* a list of
-- numbers. In the syntax of this extended language, it will be possible to
-- write strange expressions like `2 + nil`, and our semantics for arithmetic
-- expressions will then need to say something about how such expressions
-- behave. One possibility is to maintain the convention that every arithmetic
-- expression evaluates to some number by choosing some way of viewing a list
-- as a number -- e.g., by specifying that a list should be interpreted as `0`
-- when it occurs in a context expecting a number. But this would be a bit of
-- a hack.

-- A much more natural approach is simply to say that the behavior of the
-- expression `2 + nil` is *undefined* -- i.e., it doesn't evaluate to any
-- result at all. And we can easily do this: we just have to formulate `aeval`
-- and `beval` as inductive propositions rather than functions, so that we can
-- make them partial functions instead of total ones.

-- Now, however, we encounter a subtlety that will become important once we
-- move to a full programming language with looping. There, a program might
-- fail to produce a result for *two quite different reasons*: either because
-- the execution gets into an infinite loop or because, at some point, the
-- program tries to do an operation that makes no sense, such as adding a
-- number to a list, so that none of the evaluation rules can be applied.

-- These two outcomes -- nontermination vs. getting stuck in an erroneous
-- configuration -- should not be confused. In particular, we want to *allow*
-- the first (because permitting the possibility of infinite loops is the
-- price we pay for the convenience of programming with general looping
-- constructs) but *prevent* the second (which is just wrong), for example by
-- adding some form of *typechecking* to the language. Indeed, this will be a
-- major topic of the next chapter, on *types*. As a first step, we need a way
-- of presenting the semantics that allows us to distinguish nontermination
-- from erroneous "stuck states."

-- So, for lots of reasons, we'd like to have a finer-grained way of defining
-- and reasoning about program behaviors. This is the topic of the present
-- chapter. Our goal is to replace the "big-step" `Eval` relation with a
-- "small-step" relation that specifies, for a given program, how its atomic
-- steps of computation are performed. In the *small-step* style, we show how
-- to "reduce" an expression to a simpler form by performing a single step of
-- computation:

-- 2 + 2 + 3 * 4
-- ⟶ 2 + 2 + 12
-- ⟶ 4 + 12
-- ⟶ 16

-- ## A Toy Language

-- To save space, we start with an incredibly simple language of just
-- constants and addition. (We use single-letter constructors `c` and `p` --
-- for Constant and Plus -- for brevity.) The same techniques scale up to
-- richer languages.

inductive Tm where
  | c (n : Nat)          -- Constant
  | p (t1 t2 : Tm)       -- Plus

-- A standard big-step evaluator, as a function.

def evalF (t : Tm) : Nat :=
  match t with
  | .c n => n
  | .p t1 t2 => evalF t1 + evalF t2

-- Here is the same evaluator, written in exactly the same style, but
-- formulated as an inductively defined relation. We use the notation `t ⇓ n`
-- for "`t` evaluates to `n`."

-- -------                (const)
--                         c n ⇓ n

--                         t1 ⇓ n1
--                         t2 ⇓ n2
--                     -----------------          (plus)
--                     p t1 t2 ⇓ n1 + n2

inductive Eval : Tm → Nat → Prop where
  | const (n : Nat) : Eval (.c n) n
  | plus (t1 t2 : Tm) (n1 n2 : Nat) (h1 : Eval t1 n1) (h2 : Eval t2 n2) : Eval (.p t1 t2) (n1 + n2)

notation:50 t " ⇓ " n => Eval t n

-- Now, here is the corresponding *small-step* relation, written `t ⟶ t'`:

-- -------------------------------      (plus)
--                 p (c n1) (c n2) ⟶ c (n1 + n2)

--                          t1 ⟶ t1'
--                     --------------------             (plusLeft)
--                     p t1 t2 ⟶ p t1' t2

--                          t2 ⟶ t2'
--                  ----------------------------        (plusRight)
--                  p (c n1) t2 ⟶ p (c n1) t2'

namespace SimpleArith1

inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) :
      Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm)
      (h : Step t1 t1') :
      Step (.p t1 t2) (.p t1' t2)
  | plusRight (n1 : Nat) (t2 t2' : Tm)
      (h : Step t2 t2') :
      Step (.p (.c n1) t2) (.p (.c n1) t2')

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'

-- Things to notice:

-- - We are defining a single reduction step, in which just one `p` node is
--   replaced by its value.

-- - Each step finds the *leftmost* `p` node that is ready to go (both of its
--   operands are constants) and rewrites it in place. The first rule tells how
--   to rewrite this `p` node itself; the other two rules tell how to find it.

-- - A term that is just a constant cannot take a step.

-- Let's pause and check a couple of examples of reasoning with the step
-- relation.

-- If `t1` steps to `t1'`, then `p t1 t2` steps to `p t1' t2`.

example :
    (.p
      (.p (.c 1) (.c 3))
      (.p (.c 2) (.c 4))) ⟶
    (.p
      (.c 4)
      (.p (.c 2) (.c 4))) := by
  apply Step.plusLeft; apply Step.plus

-- ### Exercise (1 star): test_step_2 ⭐

-- Right-hand sides step only once the left side is a value.

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
  all_goals
    apply Step.plusRight; apply Step.plusRight; apply Step.plus

-- _Quiz:_

-- To what does the following term step?

-- .p
--   (.p
--     (.c 1)
--     (.c 2))
--   (.p
--     (.c 1)
--     (.c 2))

-- (A) `.c 6` (B) `.p (.c 3) (.p (.c 1) (.c 2))` (C)
-- `.p (.p (.c 1) (.c 2)) (.c 3)` (D) `.p (.c 3) (.c 3)` (E) None of the above

-- _Quiz:_

-- What about this one?

-- .c 1

-- (A) `.c 1` (B) `.p (.c 0) (.c 1)` (C) None of the above

end SimpleArith1

-- ## Relations

-- We will be working with several different single-step relations, so it is
-- helpful to generalize a bit and state a few definitions and theorems about
-- relations in general. (The optional chapter `Rel` in *Logical Foundations*
-- develops some of these ideas in a bit more detail; reviewing that chapter
-- may be useful if the treatment here feels too terse.)

-- A *binary relation* on a type `X` is a family of propositions parameterized
-- by two elements of `X` -- i.e., a proposition about pairs of elements of
-- `X`.

-- Note to developers (Michael Hicks  @mwhicks1, before next release):
--     Should we be getting this (and `Deterministic`, `Multi`, etc. if
--     appropriate) from the Lean standard library? If not, should we match
--     the concepts in CSLib, if they exists there?

def Relation (X : Type) := X → X → Prop

-- Our main examples of such relations in this chapter will be the single-step
-- reduction relation, `⟶`, and its multi-step variant, `⟶*`, defined below,
-- but there are many other examples -- e.g., the "equals," "less than," "less
-- than or equal to," and "is the square of" relations on numbers, and the
-- "prefix of" relation on lists and strings.

-- One simple property a relation may have is being *deterministic*: like
-- Slang's big-step evaluation, each element is related to at most one other.

-- *Theorem*: For each `t`, there is at most one `t'` such that `t` steps to
-- `t'`. We prove it by induction on the derivation of the first step.

-- *Proof sketch*: We show that if `x` steps to both `y1` and `y2`, then `y1`
-- and `y2` are equal, by induction on a derivation of `x ⟶ y1`. There are
-- several cases, depending on the last rule used in this derivation and the
-- last rule in the given derivation of `x ⟶ y2`.

-- - If both are `plus`, the result is immediate.

-- - The cases when both derivations end with `plusLeft` or `plusRight` follow
--   by the induction hypothesis.

-- - It cannot happen that one is `plus` and the other is
--   `plusLeft`/`plusRight`, since this would imply that `x` has the form
--   `p t1 t2` where both `t1` and `t2` are constants (by `plus`) *and* one of
--   `t1` or `t2` has the form `p _`.

-- - Similarly, it cannot happen that one is `plusLeft` and the other is
--   `plusRight`, since this would imply that `x` has the form `p t1 t2` where
--   `t1` has both the form `p t11 t12` and the form `c n`.

-- Formally,

def Deterministic {X : Type} (R : Relation X) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

namespace SimpleArith2

theorem step_deterministic : Deterministic SimpleArith1.Step := by
  intro x y1 y2 h1
  induction h1 generalizing y2 with
  | plus n1 n2 =>
      intro h2
      cases h2 <;> first | rfl | cases ‹SimpleArith1.Step (.c _) _›
  | plusLeft t1 t1' t2 hs ih =>
      intro h2
      cases h2 <;> first | cases ‹SimpleArith1.Step (.c _) _› | rw [ih _ ‹SimpleArith1.Step t1 _›]
  | plusRight n1 t2 t2' hs ih =>
      intro h2
      cases h2 <;> first | cases ‹SimpleArith1.Step (.c _) _› | rw [ih _ ‹SimpleArith1.Step t2 _›]

end SimpleArith2

-- Note to developers (Michael Hicks  @mwhicks1):
--     In the Rocq there is the development of a special tactic to make this
--     proof simpler. Do we want that here?

-- ### Values

-- Next, it will be useful to slightly reformulate the definition of
-- single-step reduction by stating it in terms of "values."

-- It can be useful to think of the `⟶` relation as defining an *abstract
-- machine*:

-- - At any moment, the *state* of the machine is a term.

-- - A *step* of the machine is an atomic unit of computation -- here, a single
--   "add" operation.

-- - The *halting states* of the machine are ones where there is no more
--   computation to be done.

-- We can then *execute* a term `t` as follows:

-- - Take `t` as the starting state of the machine.

-- - Repeatedly use the `⟶` relation to find a sequence of machine states,
--   starting with `t`, where each state steps to the next.

-- - When no more reduction is possible, "read out" the final state of the
--   machine as the result of execution.

-- Intuitively, it is clear that the final states of our machine are always
-- terms of the form `c n` for some `n`. We call such terms *values*.

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)

-- Having introduced the idea of values, we can use it in the definition of
-- the `⟶` relation to write the `plusRight` rule in a slightly more elegant
-- way.

-- ------------------------------      (plus)
--                 p (c n1) (c n2) ⟶ c (n1 + n2)

--                          t1 ⟶ t1'
--                     -------------------             (plusLeft)
--                     p t1 t2 ⟶ p t1' t2

--                          IsValue v1
--                          t2 ⟶ t2'
--                     -------------------             (plusRight)
--                     p v1 t2 ⟶ p v1 t2'

-- Again, the variable names in the informal presentation carry important
-- information: by convention, `v1` ranges only over values, while `t1` and
-- `t2` range over arbitrary terms.

-- (Given this convention, the explicit `IsValue` hypothesis is arguably
-- redundant, since the naming convention tells us where to add it when
-- translating the informal rule to Lean. We'll keep it for now, to maintain a
-- close correspondence between the informal and Lean versions of the rules,
-- but later on we'll drop it in informal rules for brevity.)

-- Here are the formal rules.

inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) :
      Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm)
      (h : Step t1 t1') :
      Step (.p t1 t2) (.p t1' t2)
  | plusRight (v1 t2 t2' : Tm)
      (hv : IsValue v1)
      (h : Step t2 t2') :
      Step (.p v1 t2) (.p v1 t2')

notation:40 t:41 " ⟶ " t':41 => Step t t'

-- ### Exercise (3 stars): redo_determinism ⭐⭐⭐

-- As a sanity check on this change, let's re-verify determinism. Here's an
-- informal proof:

-- *Proof sketch*: We must show that if `x` steps to both `y1` and `y2`, then
-- `y1` and `y2` are equal. Consider the final rules used in the derivations
-- of `x ⟶ y1` and `x ⟶ y2`.

-- - If both are `plus`, the result is immediate.

-- - The cases when both derivations end with `plusLeft` or `plusRight` follow
--   by the induction hypothesis.

-- - It cannot happen that one is `plus` and the other is
--   `plusLeft`/`plusRight`, since this would imply that `x` has the form
--   `p t1 t2` where both `t1` and `t2` are constants (by `plus`) *and* one of
--   `t1` or `t2` has the form `p _`.

-- - Similarly, it cannot happen that one is `plusLeft` and the other is
--   `plusRight`, since this would imply that `x` has the form `p t1 t2` where
--   `t1` both has the form `p t11 t12` and is a value (hence has the form
--   `c n`).

-- Most of this proof is the same as the one above. But to get maximum benefit
-- from the exercise you should try to write your formal version from scratch
-- and just use the earlier one if you get stuck. The impossible cross-cases
-- now also use the fact that a `IsValue` (a `c n`) cannot step.

theorem step_deterministic : Deterministic Step := by
  all_goals
    intro x y1 y2 h1
    induction h1 generalizing y2 with
    | plus n1 n2 =>
        intro h2; cases h2 with
        | plus => rfl
        | plusLeft _ _ _ hs => cases hs
        | plusRight _ _ _ hv hs => cases hs
    | plusLeft t1 t1' t2 hs ih =>
        intro h2; cases h2 with
        | plus => cases hs
        | plusLeft _ _ _ hs2 => rw [ih _ hs2]
        | plusRight _ _ _ hv hs2 => cases hv; cases hs
    | plusRight v1 t2 t2' hv hs ih =>
        intro h2; cases h2 with
        | plus => cases hs
        | plusLeft _ _ _ hs2 => cases hv; cases hs2
        | plusRight _ _ _ hv2 hs2 => rw [ih _ hs2]

-- ### Strong Progress and Normal Forms

-- The definition of single-step reduction for our toy language is fairly
-- simple, but for a larger language it would be easy to forget one of the
-- rules and accidentally create a situation where some term cannot take a
-- step even though it has not been completely reduced to a value. The
-- following theorem shows that we did not, in fact, make such a mistake here.

-- *Theorem* (*Strong Progress*): If `t` is a term, then either `t` is a value
-- or else there exists a term `t'` such that `t ⟶ t'`.

-- *Proof*: By induction on `t`.

-- - Suppose `t = c n`. Then `t` is a value.

-- - Suppose `t = p t1 t2`, where (by the IH) `t1` either is a value or can step
--   to some `t1'`, and where `t2` is either a value or can step to some `t2'`.
--   We must show `p t1 t2` is either a value or steps to some `t'`.

--   - If `t1` and `t2` are both values, then `t` can take a step, by `plus`.

--   - If `t1` is a value and `t2` can take a step, then so can `t`, by
--     `plusRight`.

--   - If `t1` can take a step, then so can `t`, by `plusLeft`.

-- Or, formally:

theorem strong_progress (t : Tm) : IsValue t ∨ ∃ t', t ⟶ t' := by
  induction t with
  | c n => left; exact .const n
  | p t1 t2 ih1 ih2 =>
      right
      cases ih1 with
      | inl hv1 =>
          cases ih2 with
          | inl hv2 =>
              cases hv1 with
              | const n1 =>
                  cases hv2 with
                  | const n2 => exact ⟨.c (n1 + n2), .plus n1 n2⟩
          | inr h2 =>
              obtain ⟨t2', ht2⟩ := h2
              exact ⟨.p t1 t2', .plusRight t1 t2 t2' hv1 ht2⟩
      | inr h1 =>
          obtain ⟨t1', ht1⟩ := h1
          exact ⟨.p t1' t2, .plusLeft t1 t1' t2 ht1⟩

-- This important property is called *strong progress*, because every term
-- either is a value or can "make progress" by stepping to some other term.
-- (The qualifier "strong" distinguishes it from a more refined version that
-- we'll see in later chapters, called simply *progress*.)

-- The idea of "making progress" can be extended to tell us something
-- interesting about values in this language: they are exactly the terms that
-- do *not* make progress in this sense. Let's give a name to "terms that
-- cannot make progress." We'll call them *normal forms*.

def IsNormalForm {X : Type} (R : Relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'

-- Note that this definition specifies what it is to be a normal form for an
-- *arbitrary* relation `R` over an arbitrary type `X`, not just for the
-- particular single-step reduction relation over terms that we are interested
-- in at the moment. We'll re-use the same terminology for talking about other
-- relations later in the course.

-- We can use this terminology to generalize the observation we made in the
-- strong progress theorem: in this language (though not necessarily, in
-- general), normal forms and values are actually the same thing.

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

-- Why is this interesting? Because `IsValue` is a *syntactic* concept -- it
-- is defined by looking at the way a term is written -- while `IsNormalForm`
-- is a *semantic* one -- it is defined by looking at how the term steps.

-- It is not obvious that these concepts should characterize the same set of
-- terms!

-- Indeed, we could easily have written the definitions (incorrectly) so that
-- they would *not* coincide.

-- Suppose, for example, we define `IsValue` so that it includes some terms
-- that are not finished reducing. (Even if you don't work the exercise
-- `value_not_same_as_normal_form1` below and the following ones, make sure
-- you can think of an example of such a term.)

namespace Temp1

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)
  | funny (t1 : Tm) (n : Nat) : IsValue (.p t1 (.c n))     -- <---

inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) : Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm) (h : Step t1 t1') : Step (.p t1 t2) (.p t1' t2)
  | plusRight (v1 t2 t2' : Tm) (hv : IsValue v1) (h : Step t2 t2') : Step (.p v1 t2) (.p v1 t2')

-- _Quiz:_

-- Using this wrong definition of `IsValue`, to how many different values does
-- the following term reduce in zero or more steps?

-- .p (.p (.c 1) (.c 2)) (.c 3)

-- _Quiz:_

-- To how many different terms does the following term `Step` (in one step)?

-- .p (.p (.c 1) (.c 2)) (.p (.c 3) (.c 4))

-- ### Exercise (3 stars): value_not_same_as_normal_form1 ⭐⭐⭐

theorem value_not_same_as_normal_form :
    ∃ v, IsValue v ∧ ¬ IsNormalForm Step v := by
  apply Exists.intro (.p (.c 0) (.c 0))
  apply And.intro (.funny _ 0)
  all_goals
    intro h
    exact h ⟨.c (0 + 0), .plus 0 0⟩

end Temp1

-- ### Exercise (2 stars): value_not_same_as_normal_form2 ⭐⭐

-- Or we might (again, wrongly) define `Step` so that it permits something
-- designated as a value to reduce further. We again lose the property that
-- values are the same as normal forms.

namespace Temp2

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)               -- Original definition

inductive Step : Tm → Tm → Prop where
  | funny (n : Nat) : Step (.c n) (.p (.c n) (.c 0))     -- <--- NEW
  | plus (n1 n2 : Nat) : Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm) (h : Step t1 t1') : Step (.p t1 t2) (.p t1' t2)
  | plusRight (v1 t2 t2' : Tm) (hv : IsValue v1) (h : Step t2 t2') : Step (.p v1 t2) (.p v1 t2')

-- _Quiz:_

-- With this definition, to how many different terms does the following term
-- step (in exactly one step)?

-- .p (.c 1) (.c 3)

theorem value_not_same_as_normal_form :
    ∃ v, IsValue v ∧ ¬ IsNormalForm Step v := by
  apply Exists.intro (.c 5)
  apply And.intro (.const 5)
  all_goals
    intro h
    exact h ⟨.p (.c 5) (.c 0), .funny 5⟩

end Temp2

-- ### Exercise (3 stars): value_not_same_as_normal_form3 ⭐⭐⭐

-- Finally, we might define `IsValue` and `Step` so that there is some term
-- that is *not* a value but that *also* cannot take a step. Such terms are
-- said to be *stuck*. In this case, this is caused by a mistake in the
-- semantics, but we will also see situations where, even in a correct
-- language definition, it makes sense to allow some terms to be stuck. (Note
-- that `plusRight` is missing below.)

namespace Temp3

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)

inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) : Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm) (h : Step t1 t1') : Step (.p t1 t2) (.p t1' t2)

-- _Quiz:_

-- With this definition, to how many terms does the following term step (in
-- one step)?

-- .p (.c 1) (.p (.c 1) (.c 2))

theorem value_not_same_as_normal_form :
    ∃ t, ¬ IsValue t ∧ IsNormalForm Step t := by
  apply Exists.intro (.p (.c 1) (.p (.c 1) (.c 2)))
  apply And.intro
  · all_goals
      intro h; cases h
  · all_goals
      intro h
      obtain ⟨t', ht⟩ := h
      cases ht with
      | plusLeft _ _ _ hs => cases hs

end Temp3

-- ## Multi-Step Reduction

-- We've been working so far with the *single-step reduction* relation `⟶`,
-- which formalizes the individual steps of an abstract machine for executing
-- programs. We can use the same machine to reduce programs to completion --
-- to find out what final result they yield. This can be formalized as
-- follows:

-- - First, we define a *multi-step reduction relation* `⟶*`, which relates
--   terms `t` and `t'` if `t` can reach `t'` by any number (including zero) of
--   single reduction steps.

-- - Then we define a "result" of a term `t` as a normal form that `t` can reach
--   by multi-step reduction.

-- Since we'll want to reuse the idea of multi-step reduction many times with
-- many different single-step relations, let's define the concept generically.
-- Given a relation `R` (e.g., the step relation `⟶`), we define a new
-- relation `Multi R`, called the *multi-step closure of `R`*, as follows.

inductive Multi {X : Type} (R : Relation X) : X → X → Prop where
  | refl (x : X) : Multi R x x
  | step (x y z : X) (h1 : R x y) (h2 : Multi R y z) : Multi R x z

-- Note to developers (berberman):
--     I would make some arguments implicit to proivde a cleaner interface
--     (FYI the [mathlib
--     version](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html#Relation.ReflTransGen))

-- The effect of this definition is that `Multi R` relates two elements `x`
-- and `y` if

-- - `x = y`, or

-- - `R x y`, or

-- - there is some nonempty sequence `z₁`, `z₂` , ..., `zₙ` such that

--   `R x₁ z₁,
--   R z₁ z₂,
--   ...,
--   R zₙ y.`

-- Intuitively, if `R` describes a single-step of computation, then
-- `z₁ ... zₙ` are the intermediate steps of computation that get us from `x`
-- to `y`.

-- We write `⟶*` for the `Multi Step` relation on terms

notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

-- The relation `Multi R` has several crucial properties.

-- First, it is obviously *reflexive* (a term can execute to itself by taking
-- zero steps). That is just what the `Multi.refl` constructor says, so such a
-- goal can always be closed with `exact .refl _`. It comes up often enough
-- that it is worth registering the constructor as a *reflexivity lemma*, with
-- the `@[refl]` attribute. The `rfl` tactic then closes a zero-step execution
-- exactly as it closes `x = x`:

attribute [refl] Multi.refl

example : (.c 5 : Tm) ⟶* .c 5 := by rfl

-- This pays off at the *end* of a reduction sequence too: the final
-- `Multi.step` leaves a goal relating a term to itself, which `rfl`
-- discharges.

example : (.p (.c 1) (.c 2)) ⟶* .c (1 + 2) := by
  apply Multi.step (y := .c (1 + 2))
  · exact .plus 1 2
  · rfl

-- Second, it *contains* `R` -- single-step reductions are a particular case
-- of multi-step executions. (It is this fact that justifies the word
-- "closure" in "multi-step closure of `R`.")

theorem multi_single {X : Type} (R : Relation X) (x y : X) (h : R x y) :
    Multi R x y :=
  .step x y y h (.refl y)

-- Third, `Multi R` is *transitive*.

theorem multi_trans {X : Type} (R : Relation X) (x y z : X)
    (g : Multi R x y) (h : Multi R y z) : Multi R x z := by
  induction g with
  | refl a => exact h
  | step a b c h1 h2 ih => exact .step a b z h1 (ih h)

-- In particular, for the `Multi Step` relation on terms, if `t1 ⟶* t2` and
-- `t2 ⟶* t3`, then `t1 ⟶* t3`.

-- _Quiz:_

-- Which of the following relations on numbers *cannot* be expressed as
-- `Multi R` for some `R`?

-- (A) less than or equal (B) strictly less than (C) equal (D) none of the
-- above

-- ### Examples

example :
    (.p (.p (.c 0) (.c 3)) (.p (.c 2) (.c 4))) ⟶* .c ((0 + 3) + (2 + 4)) := by
  apply Multi.step (y := .p (.c (0 + 3)) (.p (.c 2) (.c 4)))
  · exact .plusLeft _ _ _ (.plus 0 3)
  apply Multi.step (y := .p (.c (0 + 3)) (.c (2 + 4)))
  · exact .plusRight _ _ _ (.const _) (.plus 2 4)
  · exact multi_single _ _ _ (.plus (0 + 3) (2 + 4))

-- ### Exercise (1 star): test_multistep_2 ⭐

example : (.c 3 : Tm) ⟶* .c 3 := (.refl _)

-- ### Exercise (1 star): test_multistep_3 ⭐

example : (.p (.c 0) (.c 3)) ⟶* .p (.c 0) (.c 3) := (.refl _)

-- ### Exercise (2 stars): test_multistep_4 ⭐⭐

example :
    (.p (.c 0) (.p (.c 2) (.p (.c 0) (.c 3))))
      ⟶* (.p (.c 0) (.c (2 + (0 + 3)))) := by
  all_goals
    apply Multi.step (y := .p (.c 0) (.p (.c 2) (.c (0 + 3))))
    · exact .plusRight _ _ _ (.const 0) (.plusRight _ _ _ (.const 2) (.plus 0 3))
    · exact multi_single _ _ _ (.plusRight _ _ _ (.const 0) (.plus 2 (0 + 3)))

-- ### Exercise (2 stars): test_multistep_rfl ⭐⭐

-- Prove the following reduction, ending the chain with `rfl` instead of
-- `multi_single`.

example : (.p (.p (.c 1) (.c 2)) (.c 4)) ⟶* .c ((1 + 2) + 4) := by
  all_goals
    apply Multi.step (y := .p (.c (1 + 2)) (.c 4))
    · exact .plusLeft _ _ _ (.plus 1 2)
    apply Multi.step (y := .c ((1 + 2) + 4))
    · exact .plus (1 + 2) 4
    · rfl

-- ### Normal Forms Again

-- If `t` reduces to `t'` in zero or more steps and `t'` is a normal form, we
-- say that "`t'` is *a normal form of* `t`."

def IsNormalFormOf {X : Type} (R : Relation X) (t t' : X) : Prop :=
  Multi R t t' ∧ IsNormalForm R t'

-- We have already seen that, for our language, single-step reduction is
-- deterministic -- i.e., a given term can take a single step in at most one
-- way. It follows that, if `t` can reach a normal form, then this normal form
-- is unique.

-- In other words, we can actually pronounce `IsNormalFormOf t t'` as "`t'` is
-- *the* normal form of `t`."

-- ### Exercise (3 stars): normal_forms_unique ⭐⭐⭐

theorem normal_forms_unique : Deterministic (IsNormalFormOf Step) := by
  -- We recommend using this initial setup as-is!
  intro x y1 y2 p1 p2
  obtain ⟨p11, p12⟩ := p1
  obtain ⟨p21, p22⟩ := p2
  all_goals
    induction p11 generalizing y2 with
    | refl a =>
        cases p21 with
        | refl => rfl
        | step _ b _ h1 _ => exact absurd ⟨b, h1⟩ p12
    | step a b c h1 h2 ih =>
        cases p21 with
        | refl => exact absurd ⟨b, h1⟩ p22
        | step _ b' _ h1' h2' =>
            have hbb : b = b' := step_deterministic _ _ _ h1 h1'
            subst hbb
            exact ih y2 p12 h2' p22

-- Indeed, something stronger is true for this language (though not for all
-- the languages we will see): the reduction of *any* term `t` will eventually
-- reach a normal form in a finite number of steps -- i.e., `IsNormalFormOf`
-- is a *total* function. We say the `Step` relation is *normalizing*. To
-- prove it, we need a couple of congruence lemmas.

def Normalizing {X : Type} (R : Relation X) : Prop :=
  ∀ t, ∃ t', IsNormalFormOf R t t'

theorem multistep_congr_1 (t1 t1' t2 : Tm) (h : t1 ⟶* t1') : (.p t1 t2) ⟶* (.p t1' t2) := by
  induction h with
  | refl x => exact .refl _
  | step x y z h1 h2 ih => exact .step _ (.p y t2) _ (.plusLeft x y t2 h1) ih

-- ### Exercise (2 stars): multistep_congr_2 ⭐⭐

theorem multistep_congr_2 (v1 t2 t2' : Tm) (hv : IsValue v1) (h : t2 ⟶* t2') :
    (.p v1 t2) ⟶* (.p v1 t2') := by
  all_goals
    induction h with
    | refl x => exact .refl _
    | step x y z h1 h2 ih => exact .step _ (.p v1 y) _ (.plusRight v1 x y hv h1) ih

-- With these lemmas in hand, the main proof is a straightforward induction.

-- *Theorem*: The `Step` relation is normalizing -- i.e., for every `t` there
-- exists some `t'` such that `t` reduces to `t'` and `t'` is a normal form.

-- *Proof sketch*: By induction on terms. There are two cases:

-- - `t = c n` for some `n`. Here `t` doesn't take a step, and we have `t' = t`.
--   We derive the left-hand side by reflexivity and the right-hand side by
--   observing (a) that values are normal forms (by `nf_same_as_value`) and (b)
--   that `t` is a value (by `const`).

-- - `t = p t1 t2` for some `t1` and `t2`. By the IH, `t1` and `t2` reduce to
--   normal forms `t1'` and `t2'`. Recall that normal forms are values (by
--   `nf_same_as_value`); we therefore know that `t1' = c n1` and `t2' = c n2`
--   for some `n1` and `n2`. We combine the `⟶*` derivations for `t1` and `t2`
--   using `multistep_congr_1` and `multistep_congr_2` to prove that `p t1 t2`
--   reduces in many steps to `t' = c (n1 + n2)`. Finally, `c (n1 + n2)` is a
--   value, which is in turn a normal form.

theorem step_normalizing : Normalizing Step := by
  intro t
  induction t with
  | c n => exact ⟨.c n, .refl _, (nf_same_as_value _).mpr (.const n)⟩
  | p t1 t2 ih1 ih2 =>
      obtain ⟨t1', hs1, hnf1⟩ := ih1
      obtain ⟨t2', hs2, hnf2⟩ := ih2
      obtain ⟨n1⟩ := (nf_same_as_value _).mp hnf1
      obtain ⟨n2⟩ := (nf_same_as_value _).mp hnf2
      apply Exists.intro (.c (n1 + n2))
      apply And.intro _ ((nf_same_as_value _).mpr (.const _))
      apply multi_trans _ _ _ _ (multistep_congr_1 t1 (.c n1) t2 hs1)
      apply multi_trans _ _ _ _ (multistep_congr_2 (.c n1) t2 (.c n2) (.const n1) hs2)
      exact multi_single _ _ _ (.plus n1 n2)

-- ### Equivalence of Big-Step and Small-Step

-- Having defined the operational semantics of our tiny programming language
-- in two different ways (big-step and small-step), it makes sense to ask
-- whether these definitions actually define the same thing!

-- They do, though it takes a little work to show it. The details are left as
-- an exercise. We consider the two implications separately. First, big-step
-- evaluation implies multi-step reduction to a value.

-- ### Exercise (3 stars): multistep_of_eval ⭐⭐⭐

theorem multistep_of_eval (t : Tm) (n : Nat) (h : t ⇓ n) : t ⟶* .c n := by
  all_goals
    induction h with
    | const n => exact .refl _
    | plus t1 t2 n1 n2 h1 h2 ih1 ih2 =>
        apply multi_trans _ _ _ _ (multistep_congr_1 t1 (.c n1) t2 ih1)
        apply multi_trans _ _ _ _ (multistep_congr_2 (.c n1) t2 (.c n2) (.const n1) ih2)
        exact multi_single _ _ _ (.plus n1 n2)

-- The key ideas in the proof can be seen in the following picture:

-- p t1 t2 ⟶            (by plusLeft)
-- p t1' t2 ⟶           (by plusLeft)
-- p t1'' t2 ⟶          (by plusLeft)
-- ...
-- p (c n1) t2 ⟶        (by plusRight)
-- p (c n1) t2' ⟶       (by plusRight)
-- p (c n1) t2'' ⟶      (by plusRight)
-- ...
-- p (c n1) (c n2) ⟶    (by plus)
-- c (n1 + n2)

-- That is, the multi-step reduction of a term of the form `p t1 t2` proceeds
-- in three phases:

-- - First, we use `plusLeft` some number of times to reduce `t1` to a normal
--   form, which must (by `nf_same_as_value`) be a term of the form `c n1` for
--   some `n1`.

-- - Next, we use `plusRight` some number of times to reduce `t2` to a normal
--   form, which must again be a term of the form `c n2` for some `n2`.

-- - Finally, we use `plus` one time to reduce `p (c n1) (c n2)` to
--   `c (n1 + n2)`.

-- To formalize this intuition, you'll need the congruence lemmas from above,
-- plus some basic properties of `⟶*` (that it is reflexive, transitive, and
-- includes `⟶`).

-- ### Exercise (3 stars): multistep_of_eval_inf ⭐⭐⭐

-- Write a detailed informal version of the proof of `multistep_of_eval`. (A
-- paper exercise -- there is no Lean proof to fill in here.)

-- _Theorem_: for all `t`, `n`, if `t ⇓ n` then `t ⟶* c n`.

-- _Proof_: By induction on a derivation of `t ⇓ n`.

--   - Suppose the final rule used to show `t ⇓ n` is `const`.  Then `t = c n`.
--     We must show `c n ⟶* c n`.  This holds by `refl`.

--   - Suppose the final rule used to show `t ⇓ n` is `plus`.  Then
--     `t = p t1 t2`, and we know that `t1 ⇓ c n1` and `t2 ⇓ c n2` for some
--     `n1` and `n2`, with `n = n1 + n2`.  The IH tells us that `t1 ⟶* c n1` and
--     `t2 ⟶* c n2`.  We must show that `p t1 t2 ⟶* c (n1 + n2)`.

--     First, `p t1 t2 ⟶* p (c n1) t2` by `multistep_congr_1` and the multistep
--     derivation for `t1`.  Observing that `c n1` is a value, we also have
--     `p (c n1) t2 ⟶* p (c n1) (c n2)` by `multistep_congr_2` and the multistep
--     derivation for `t2`.  It's also easy to see by `plus` that
--     `p (c n1) (c n2) ⟶ c (n1 + n2)`, and so, by `Step` and
--     `refl`, that the same is true for `⟶*`.  We can now use transitivity
--     of `⟶*` to stitch these derivations together, proving
--     `p t1 t2 ⟶* c (n1 + n2)`.

-- For the converse, we need one lemma, which establishes a relation between
-- single-step reduction and big-step evaluation. A single step preserves the
-- big-step value.

-- ### Exercise (3 stars): eval_of_step ⭐⭐⭐

theorem eval_of_step (t t' : Tm) (n : Nat) (hs : t ⟶ t') (he : t' ⇓ n) : t ⇓ n := by
  all_goals
    induction hs generalizing n with
    | plus n1 n2 =>
        cases he with
        | const _ => exact .plus _ _ n1 n2 (.const n1) (.const n2)
    | plusLeft t1 t1' t2 h1 ih =>
        cases he with
        | plus _ _ m1 m2 he1 he2 => exact .plus t1 t2 m1 m2 (ih m1 he1) he2
    | plusRight v1 t2 t2' hv h2 ih =>
        cases he with
        | plus _ _ m1 m2 he1 he2 => exact .plus v1 t2 m1 m2 he1 (ih m2 he2)

-- The fact that small-step reduction implies big-step evaluation is now
-- straightforward to prove, once we have factored out the observation that
-- every normal form is a value. The proof proceeds by induction on the
-- multi-step reduction sequence that is buried in the hypothesis
-- `IsNormalFormOf t t'`. (Make sure you understand the statement before you
-- start to work on the proof.)

-- ### Exercise (3 stars): eval_of_multistep ⭐⭐⭐

theorem eval_of_multistep (t t' : Tm) (h : IsNormalFormOf Step t t') :
    ∃ n, t' = .c n ∧ t ⇓ n := by
  all_goals
    obtain ⟨hs, hnf⟩ := h
    obtain ⟨n⟩ := (nf_same_as_value t').mp hnf
    have H : ∀ (a tc : Tm), Multi Step a tc → tc = .c n → a ⇓ n := by
      intro a tc hst
      induction hst with
      | refl b => intro heq; subst heq; exact .const n
      | step b c d h1 h2 ih => intro heq; exact eval_of_step b c n h1 (ih heq)
    exact ⟨n, rfl, H t (.c n) hs rfl⟩

-- ### Exercise (3 stars): interp_tm ⭐⭐⭐

-- Remember that we also defined big-step evaluation of terms as a function
-- `evalF`. Prove that it is equivalent to the relational semantics. (Hint: we
-- just proved that `Eval` and `multistep` are equivalent, so logically it
-- doesn't matter which you choose. One will be easier than the other,
-- though!)

theorem evalF_eval (t : Tm) (n : Nat) : evalF t = n ↔ t ⇓ n := by
  all_goals
    constructor
    · intro hi
      subst hi
      induction t with
      | c n => exact .const n
      | p t1 t2 ih1 ih2 => exact .plus t1 t2 _ _ ih1 ih2
    · intro he
      induction he with
      | const n => rfl
      | plus t1 t2 n1 n2 h1 h2 ih1 ih2 => simp only [evalF]; rw [ih1, ih2]

-- ## Small-Step Slang

-- Now for a more serious example: a small-step semantics for the richer
-- arithmetic and boolean expressions of the Slang chapter (with subtraction,
-- multiplication, and the boolean operators) rather than the two-constructor
-- toy language we have used so far.

-- The small-step reduction relations for these expressions are
-- straightforward extensions of the tiny language we've been working up to
-- now. To make them easier to read, we introduce the symbolic notations `⟶a`
-- and `⟶b` for the arithmetic and boolean step relations.

-- We work in the `Slang` namespace, reusing the arithmetic and boolean
-- expression syntax (`Aexp`, `Bexp`) and the big-step evaluator (`Aexp.eval`)
-- from the `Slang` chapter:

namespace Slang

-- ### Arithmetic Expressions

-- The arithmetic *values* (the normal forms of the small-step relation below)
-- are just the numeric literals:

inductive IsAValue : Aexp → Prop where
  | num (n : Nat) : IsAValue (.num n)

-- Here is the small-step relation for arithmetic expressions. A compound
-- expression reduces its left operand first; once that is a value, it reduces
-- its right operand; once both are values, it computes the result. (We show
-- the rules for `+` in full; those for `−` and `×` have exactly the same
-- shape.)

-- a1 ⟶a a1'
--                    --------------------             (plusLeft)
--                    a1 + a2 ⟶a a1' + a2

--                  IsAValue v1      a2 ⟶a a2'
--                  ---------------------------        (plusRight)
--                    v1 + a2 ⟶a v1 + a2'

--                  -------------------------          (plus)
--                  n1 + n2 ⟶a num (n1 + n2)

inductive AStep : Aexp → Aexp → Prop where
  | plusLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : AStep (.plus a1 a2) (.plus a1' a2)
  | plusRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      AStep (.plus v1 a2) (.plus v1 a2')
  | plus (n1 n2 : Nat) :  AStep (.plus (.num n1) (.num n2)) (.num (n1 + n2))
  | minusLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : AStep (.minus a1 a2) (.minus a1' a2)
  | minusRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      AStep (.minus v1 a2) (.minus v1 a2')
  | minus (n1 n2 : Nat) : AStep (.minus (.num n1) (.num n2)) (.num (n1 - n2))
  | multLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : AStep (.mult a1 a2) (.mult a1' a2)
  | multRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      AStep (.mult v1 a2) (.mult v1 a2')
  | mult (n1 n2 : Nat) : AStep (.mult (.num n1) (.num n2)) (.num (n1 * n2))

scoped notation:40 a:41 " ⟶a " a':41 => AStep a a'

-- Notice that `AStep` has exactly the shape `Aexp → Aexp → Prop` -- i.e., it
-- is a `Relation Aexp` in the sense of the *Relations* section above. So the
-- generic vocabulary from that section (`Deterministic`, `IsNormalForm`, the
-- multi-step closure `Multi`, ...) applies to it directly.

-- Here is a one-step reduction: since the left operand `3` is already a
-- value, the right operand is the one that takes a step.

example :
    (Aexp.plus (.num 3) (.plus (.num 2) (.num 1))) ⟶a (.plus (.num 3) (.num 3)) :=
  .plusRight _ _ _ (.num 3) (.plus 2 1)

-- ### Exercise (2 stars): strong_progress_arith ⭐⭐

-- Every arithmetic expression is either a value or can take a step -- the
-- same *strong progress* property we proved for the toy language, now for the
-- richer `Slang` arithmetic expressions.

theorem strong_progress_arith (a : Aexp) : IsAValue a ∨ ∃ a', a ⟶a a' := by
  all_goals
    induction a with
    | num n => exact .inl (.num n)
    | plus a1 a2 ih1 ih2 =>
        right
        cases ih1 with
        | inr h1 => obtain ⟨a1', ha1⟩ := h1; exact ⟨_, .plusLeft _ _ _ ha1⟩
        | inl hv1 => cases hv1 with
          | num n1 => cases ih2 with
            | inr h2 => obtain ⟨a2', ha2⟩ := h2
                        exact ⟨_, .plusRight _ _ _ (.num n1) ha2⟩
            | inl hv2 => cases hv2 with
              | num n2 => exact ⟨_, .plus n1 n2⟩
    | minus a1 a2 ih1 ih2 =>
        right
        cases ih1 with
        | inr h1 => obtain ⟨a1', ha1⟩ := h1; exact ⟨_, .minusLeft _ _ _ ha1⟩
        | inl hv1 => cases hv1 with
          | num n1 => cases ih2 with
            | inr h2 => obtain ⟨a2', ha2⟩ := h2
                        exact ⟨_, .minusRight _ _ _ (.num n1) ha2⟩
            | inl hv2 => cases hv2 with
              | num n2 => exact ⟨_, .minus n1 n2⟩
    | mult a1 a2 ih1 ih2 =>
        right
        cases ih1 with
        | inr h1 => obtain ⟨a1', ha1⟩ := h1; exact ⟨_, .multLeft _ _ _ ha1⟩
        | inl hv1 => cases hv1 with
          | num n1 => cases ih2 with
            | inr h2 => obtain ⟨a2', ha2⟩ := h2
                        exact ⟨_, .multRight _ _ _ (.num n1) ha2⟩
            | inl hv2 => cases hv2 with
              | num n2 => exact ⟨_, .mult n1 n2⟩

-- ### Boolean Expressions

-- The small-step relation for boolean expressions reduces the arithmetic
-- subexpressions of a comparison (using `⟶a`) and then applies the
-- comparison, and it short-circuits `¬` and `∧` on boolean literals.

-- We are not actually going to bother to define boolean values, since they
-- aren't needed in the definition of `⟶b` below (why?), though they might be
-- if our language were a bit more complicated (why?).

-- Again we show a representative sample; `neq`, `le`, and `gt` follow the
-- same pattern as `eq`.

-- a1 ⟶a a1'
--                   --------------------             (eqLeft)
--                   a1 = a2 ⟶b a1' = a2

--                 IsAValue v1      a2 ⟶a a2'
--                 ---------------------------        (eqRight)
--                   v1 = a2 ⟶b v1 = a2'

--                   ---------------------            (eq)
--                   n1 = n2 ⟶b (n1 = n2)

--                         b1 ⟶b b1'
--                       --------------               (notStep)
--                       ¬ b1 ⟶b ¬ b1'

--                     ----------------               (notTrue)
--                     ¬ true ⟶b false

--                   ---------------------            (andFalse)
--                   false ∧ b2 ⟶b false

-- Here are the formal rules.

inductive BStep : Bexp → Bexp → Prop where
  | eqLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : BStep (.eq a1 a2) (.eq a1' a2)
  | eqRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      BStep (.eq v1 a2) (.eq v1 a2')
  | eq (n1 n2 : Nat) : BStep (.eq (.num n1) (.num n2)) (.bool (decide (n1 = n2)))
  | neqLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : BStep (.neq a1 a2) (.neq a1' a2)
  | neqRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      BStep (.neq v1 a2) (.neq v1 a2')
  | neq (n1 n2 : Nat) : BStep (.neq (.num n1) (.num n2)) (.bool (decide (n1 ≠ n2)))
  | leLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : BStep (.le a1 a2) (.le a1' a2)
  | leRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      BStep (.le v1 a2) (.le v1 a2')
  | le (n1 n2 : Nat) : BStep (.le (.num n1) (.num n2)) (.bool (decide (n1 ≤ n2)))
  | gtLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : BStep (.gt a1 a2) (.gt a1' a2)
  | gtRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      BStep (.gt v1 a2) (.gt v1 a2')
  | gt (n1 n2 : Nat) : BStep (.gt (.num n1) (.num n2)) (.bool (decide (n1 > n2)))
  | notStep (b1 b1' : Bexp) (h : BStep b1 b1') : BStep (.not b1) (.not b1')
  | notTrue : BStep (.not (.bool true)) (.bool false)
  | notFalse : BStep (.not (.bool false)) (.bool true)
  | andStep (b1 b1' b2 : Bexp) (h : BStep b1 b1') : BStep (.and b1 b2) (.and b1' b2)
  | andTrueStep (b2 b2' : Bexp) (h : BStep b2 b2') :
      BStep (.and (.bool true) b2) (.and (.bool true) b2')
  | andFalse (b2 : Bexp) : BStep (.and (.bool false) b2) (.bool false)
  | andTrueTrue : BStep (.and (.bool true) (.bool true)) (.bool true)
  | andTrueFalse : BStep (.and (.bool true) (.bool false)) (.bool false)

scoped notation:40 b:41 " ⟶b " b':41 => BStep b b'

-- A boolean example -- the left comparison operand reduces first:

example :
    (Bexp.le (.plus (.num 1) (.num 1)) (.num 3)) ⟶b (.le (.num 2) (.num 3)) :=
  .leLeft _ _ _ (.plus 1 1)

-- _Quiz:_

-- Which of these properties does this small-step semantics for `Slang`
-- expressions satisfy? (Yes or No for each.)

-- - determinism
-- - strong progress (every non-value takes a step)
-- - values and normal forms coincide (i.e., there are no "stuck" terms)
-- - the step relation is normalizing (i.e., evaluation always terminates)

-- Let us make good on the first of those answers. Both step relations are
-- *deterministic*: the value guards on the "step the right operand" rules
-- mean that at most one rule ever applies to a given term.

-- ### Exercise (3 stars): astep_deterministic ⭐⭐⭐

-- The arithmetic step relation is deterministic. (Structurally this is the
-- value-based determinism proof from the toy language, repeated for `+`, `−`,
-- and `×`; the impossible cross-cases close because a value `num n` cannot
-- step.)

theorem astep_deterministic : Deterministic AStep := by
  all_goals
    intro x y1 y2 h1
    induction h1 generalizing y2 <;> intro h2 <;> cases h2 <;>
      first
        | rfl
        | cases ‹AStep (Aexp.num _) _›
        | (cases ‹IsAValue _›; cases ‹AStep (Aexp.num _) _›)
        | (congr 1 <;> first | rfl | (apply ‹∀ _, AStep _ _ → _ = _› <;> assumption))

-- ### Exercise (3 stars): bstep_deterministic ⭐⭐⭐

-- The boolean step relation is deterministic too. The comparison cases (`eq`,
-- `neq`, `le`, `gt`) reduce their operands with `⟶a`, so they inherit
-- determinism from `astep_deterministic`; `¬` and the short-circuiting `∧`
-- contribute only base cases.

theorem bstep_deterministic : Deterministic BStep := by
  all_goals
    intro x y1 y2 h1
    induction h1 generalizing y2 <;> intro h2 <;> cases h2 <;>
      first
        | rfl
        | cases ‹AStep (Aexp.num _) _›
        | (cases ‹IsAValue _›; cases ‹AStep (Aexp.num _) _›)
        | cases ‹BStep (Bexp.bool _) _›
        | (congr 1 <;> first | rfl | (apply astep_deterministic <;> assumption) | (apply ‹∀ _, BStep _ _ → _ = _› <;> assumption))

-- ### Nondeterministic Evaluation

-- The relation `⟶a` above bakes in a *left-to-right* evaluation order: the
-- rule `plusRight` can fire only once the left operand is already a value
-- (`IsAValue v1`). But nothing about the *meaning* of `+` requires that order
-- -- we could just as well reduce the right operand first, or interleave the
-- two. Different orders are exactly what a concurrent or optimizing
-- implementation might choose, so it is natural to ask whether the choice can
-- affect the final answer.

-- Let's find out. We define a second small-step relation, `⟶n`, that is
-- identical to `⟶a` except that we *drop* the `IsAValue` side-condition:
-- either operand may take a step at any time.

inductive ANStep : Aexp → Aexp → Prop where
  | plusLeft (a1 a1' a2 : Aexp) (h : ANStep a1 a1') :  ANStep (.plus a1 a2) (.plus a1' a2)
  | plusRight (a1 a2 a2' : Aexp) (h : ANStep a2 a2') : ANStep (.plus a1 a2) (.plus a1 a2')
  | plus (n1 n2 : Nat) : ANStep (.plus (.num n1) (.num n2)) (.num (n1 + n2))
  | minusLeft (a1 a1' a2 : Aexp) (h : ANStep a1 a1') : ANStep (.minus a1 a2) (.minus a1' a2)
  | minusRight (a1 a2 a2' : Aexp) (h : ANStep a2 a2') : ANStep (.minus a1 a2) (.minus a1 a2')
  | minus (n1 n2 : Nat) : ANStep (.minus (.num n1) (.num n2)) (.num (n1 - n2))
  | multLeft (a1 a1' a2 : Aexp) (h : ANStep a1 a1') : ANStep (.mult a1 a2) (.mult a1' a2)
  | multRight (a1 a2 a2' : Aexp) (h : ANStep a2 a2') : ANStep (.mult a1 a2) (.mult a1 a2')
  | mult (n1 n2 : Nat) : ANStep (.mult (.num n1) (.num n2)) (.num (n1 * n2))

scoped notation:40 a:41 " ⟶n " a':41 => ANStep a a'

-- Unlike `⟶a`, this relation really is nondeterministic: a single term can
-- step in two different ways, depending on which operand we choose to
-- advance.

theorem anstep_not_deterministic : ¬ Deterministic ANStep := by
  intro hd
  have s1 : ANStep (.plus (.plus (.num 1) (.num 1)) (.plus (.num 2) (.num 2)))
      (.plus (.num 2) (.plus (.num 2) (.num 2))) :=
    .plusLeft _ _ _ (.plus 1 1)
  have s2 : ANStep (.plus (.plus (.num 1) (.num 1)) (.plus (.num 2) (.num 2)))
      (.plus (.plus (.num 1) (.num 1)) (.num 4)) :=
    .plusRight _ _ _ (.plus 2 2)
  have heq := hd _ _ _ s1 s2
  simp at heq

-- Remarkably, this nondeterminism does *not* affect the final answer. The key
-- observation is that a single step never changes the big-step *value* of an
-- expression -- whichever operand we advance, `eval` is preserved.

-- ### Exercise (2 stars): anstep_preserves_eval ⭐⭐

-- Prove that one nondeterministic step leaves the big-step value unchanged.
-- *Hint:* induction on the step derivation; each case is immediate from
-- `eval` and, where present, the induction hypothesis.

theorem anstep_preserves_eval (a a' : Aexp) (h : a ⟶n a') : a.eval = a'.eval := by
  all_goals
    induction h <;> simp only [Aexp.eval, *]

-- This lifts to any number of steps by a routine induction on the multi-step
-- derivation:

theorem multi_anstep_preserves_eval (a a' : Aexp) (h : Multi ANStep a a') : a.eval = a'.eval := by
  induction h with
  | refl x => rfl
  | step x y z h1 _ ih => rw [anstep_preserves_eval x y h1]; exact ih

-- Finally we can compare the two semantics. The deterministic relation `⟶a`
-- is a *special case* of `⟶n`: every `⟶a` step is also an `⟶n` step (it
-- merely happens, in addition, to respect the `IsAValue` guard).

theorem astep_imp_anstep (a a' : Aexp) (h : a ⟶a a') : a ⟶n a' := by
  induction h with
  | plusLeft a1 a1' a2 _ ih => exact .plusLeft a1 a1' a2 ih
  | plusRight v1 a2 a2' _ _ ih => exact .plusRight v1 a2 a2' ih
  | plus n1 n2 => exact .plus n1 n2
  | minusLeft a1 a1' a2 _ ih => exact .minusLeft a1 a1' a2 ih
  | minusRight v1 a2 a2' _ _ ih => exact .minusRight v1 a2 a2' ih
  | minus n1 n2 => exact .minus n1 n2
  | multLeft a1 a1' a2 _ ih => exact .multLeft a1 a1' a2 ih
  | multRight v1 a2 a2' _ _ ih => exact .multRight v1 a2 a2' ih
  | mult n1 n2 => exact .mult n1 n2

theorem multi_astep_imp_anstep (a a' : Aexp) (h : Multi AStep a a') : Multi ANStep a a' := by
  induction h with
  | refl x => exact .refl x
  | step x y z h1 _ ih => exact .step x y z (astep_imp_anstep x y h1) ih

-- ### Exercise (3 stars): astep_anstep_agree ⭐⭐⭐

-- Now put the pieces together: prove that the deterministic and
-- nondeterministic semantics always compute the *same* final result. That is,
-- if `a` fully reduces to `.num n1` under `⟶a` and to `.num n2` under `⟶n`,
-- then `n1 = n2`.

-- *Hint:* both `.num n1` and `.num n2` are reachable by `⟶n` (use
-- `multi_astep_imp_anstep` for the first), and `⟶n` preserves `eval`.

theorem astep_anstep_agree (a : Aexp) (n1 n2 : Nat)
    (hd : Multi AStep a (.num n1)) (hn : Multi ANStep a (.num n2)) : n1 = n2 := by
  all_goals
    have e1 := multi_anstep_preserves_eval a (.num n1)
      (multi_astep_imp_anstep a (.num n1) hd)
    have e2 := multi_anstep_preserves_eval a (.num n2) hn
    simp only [Aexp.eval] at e1 e2
    lia

-- So even though `⟶n` is genuinely nondeterministic, the value it eventually
-- produces is completely determined -- and it is the same value the
-- deterministic machine (and the big-step evaluator) computes. This
-- *confluence to a unique result* is exactly the property one wants when
-- reordering or parallelizing the evaluation of pure expressions.

-- ### A Small-Step Stack Machine

-- Our last example is a small-step semantics for a *stack machine* that
-- evaluates arithmetic expressions. The machine's instructions push a
-- constant or combine the top two stack entries. The machine's behavior
-- should match the big-step `Aexp.eval` function defined earlier.

-- A *program* is a list of instructions, and the *stack* is a list of
-- numbers.

inductive SInstr where
  | push (n : Nat)
  | plus
  | minus
  | mult

abbrev Stack := List Nat
abbrev Prog := List SInstr

-- The compiler emits code in the postfix order sketched above:

def compile : Aexp → Prog
  | .num n => [.push n]
  | .plus a1 a2 => compile a1 ++ compile a2 ++ [.plus]
  | .minus a1 a2 => compile a1 ++ compile a2 ++ [.minus]
  | .mult a1 a2 => compile a1 ++ compile a2 ++ [.mult]

example : compile (.plus (.num 2) (.num 3)) = [.push 2, .push 3, .plus] := rfl

-- Now the small-step machine itself: each step consumes the next instruction
-- and updates the stack.

inductive StackStep : Prog × Stack → Prog × Stack → Prop where
  | push (p : Prog) (stk : Stack) (n : Nat) : StackStep (.push n :: p, stk) (p, n :: stk)
  | plus (p : Prog) (stk : Stack) (n m : Nat) :
      StackStep (.plus :: p, n :: m :: stk) (p, (m + n) :: stk)
  | minus (p : Prog) (stk : Stack) (n m : Nat) :
      StackStep (.minus :: p, n :: m :: stk) (p, (m - n) :: stk)
  | mult (p : Prog) (stk : Stack) (n m : Nat) :
      StackStep (.mult :: p, n :: m :: stk) (p, (m * n) :: stk)

-- The machine is deterministic:

theorem stack_step_deterministic : Deterministic StackStep := by
  intro x y1 y2 h1 h2
  cases h1 <;> cases h2 <;> rfl

-- ### Exercise (3 stars): compiler_is_correct (Advanced) ⭐⭐⭐

-- Prove the compiler correct: running the compiled program from the empty
-- stack reduces, in some number of steps, to a stack holding exactly the
-- value of the expression.

-- *Hint:* this will not go through by a direct induction -- the induction
-- hypothesis is too weak. Prove a more general statement first, about running
-- `compile a` followed by *any* leftover program `p`, starting from *any*
-- stack `stk`. (Reassociating the `++`s with `List.append_assoc`, and
-- chaining steps with `multi_trans`/`multi_single`, are the moves you need.)

theorem compiler_is_correct (a : Aexp) :
    Multi StackStep (compile a, []) ([], [a.eval]) := by
  all_goals
    have gen : ∀ (a : Aexp) (p : Prog) (stk : Stack),
        Multi StackStep (compile a ++ p, stk) (p, a.eval :: stk) := by
      intro a
      induction a with
      | num n =>
          intro p stk
          simp only [compile, Aexp.eval]
          exact multi_single _ _ _ (StackStep.push p stk n)
      | plus a1 a2 ih1 ih2 =>
          intro p stk
          simp only [compile, Aexp.eval, List.append_assoc]
          exact multi_trans _ _ _ _ (ih1 _ stk)
            (multi_trans _ _ _ _ (ih2 _ (a1.eval :: stk))
              (multi_single _ _ _ (StackStep.plus p stk a2.eval a1.eval)))
      | minus a1 a2 ih1 ih2 =>
          intro p stk
          simp only [compile, Aexp.eval, List.append_assoc]
          exact multi_trans _ _ _ _ (ih1 _ stk)
            (multi_trans _ _ _ _ (ih2 _ (a1.eval :: stk))
              (multi_single _ _ _ (StackStep.minus p stk a2.eval a1.eval)))
      | mult a1 a2 ih1 ih2 =>
          intro p stk
          simp only [compile, Aexp.eval, List.append_assoc]
          exact multi_trans _ _ _ _ (ih1 _ stk)
            (multi_trans _ _ _ _ (ih2 _ (a1.eval :: stk))
              (multi_single _ _ _ (StackStep.mult p stk a2.eval a1.eval)))
    have hfin := gen a [] []
    simp only [List.append_nil] at hfin
    exact hfin

end Slang


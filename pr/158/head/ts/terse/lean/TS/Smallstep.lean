import TS.Slang

import TS.SFLCompat

-- # Smallstep: Small-step Operational Semantics

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     The `hiding lean` (above in the source file) should not
--     be needed any more and should be removed from all files
--     everywhere it exists.

-- Note to developers (Michael Hicks  @mwhicks1):
--     This chapter adapts Smallstep to follow Slang, the
--     initial part of Imp, on just Aexp and Bexp (without
--     variables). This means that parts of this chapter had to
--     adjust: Concurrent Imp is dropped in favor of
--     Nondeterministic Aexp, and the stack machine is
--     simplified to just Aexps without variables.

-- Note to developers (before next release):
--     In this and later chapters, we are not very consistent
--     about presenting computation rules first and congruence
--     rules after...

-- Note to developers:
--     HIDE: Sometime in the early 2010s, we did some mining
--     past exams for exercises...
--
--     - Loris: No interesting exercise in Finals of
--       2007-2009-2010-2011. Nothing in second midterms except
--       for 2011.
--
--     - 2011 midterm proposes the following exercise: give the
--       small step relation of FLIP X (alternatively HAVOC,
--       ANYTHING). We could then ask to extend the proof of
--       equivalence of big step vs small step (personally don't
--       like it too much).
--
--     - Maybe we can ask how they would adapt the definition of
--       Hoare triple to small step (maybe in the exam).
--
--     HIDE: BCP: I also have a bunch of slides from earlier
--     offerings of CIS500 that might be good additions to the
--     TERSE notes.
--
--     HIDE: Possible major restructuring: This chapter might
--     better be postponed to later in the course. A big-step
--     presentation of STLC (and maybe even some of the
--     extensions like subtyping?) could come first. However,
--     this would invite a much bigger change, where **all**
--     the variants of STLC (with refs, with subtyping, ...)
--     are done in big-step style. This requires more
--     thought...
--
--     HIDE: Wonder whether it would be interesting to show
--     them how to make a correspondence with a "real abstract
--     machine" at a lower level...? There's a start at an
--     exercise along these lines below.

-- ## Big-step and Small-step Evaluation

-- Our semantics for expressions is written in the so-called
-- "big-step" style. Evaluation rules take an expression to a
-- final answer "all in one step":

-- 2 + 2 + 3 * 4 ⇓ 16

-- But big-step semantics makes it hard to talk about what
-- happens *along the way*.

-- *Small-step* style: alternatively, we can show how to
-- "reduce" an expression to a simpler form by performing a
-- single step of computation:

-- 2 + 2 + 3 * 4
-- ⟶ 2 + 2 + 12
-- ⟶ 4 + 12
-- ⟶ 16

-- Advantages of the small-step style include:

-- - Finer-grained "abstract machine", closer to real
--   implementations.

-- - Extends smoothly to concurrent languages and languages with
--   other sorts of *computational effects*.

-- - Separates *divergence* (nontermination) from *stuckness*
--   (run-time error).

-- ## A Toy Language

inductive Tm where
  | c (n : Nat)          -- Constant
  | p (t1 t2 : Tm)       -- Plus

-- A standard big-step evaluator, as a function.

def evalF (t : Tm) : Nat :=
  match t with
  | .c n => n
  | .p t1 t2 => evalF t1 + evalF t2

-- Here is the same evaluator, written in exactly the same
-- style, but formulated as an inductively defined relation. We
-- use the notation `t ⇓ n` for "`t` evaluates to `n`."

-- The `notation` command below is how that is declared: it
-- introduces `⇓` as infix syntax for the `Eval` relation
-- defined with it, with a precedence saying how tightly it
-- binds. This is the lightweight way to name a relation; later
-- chapters, where a whole object language needs a grammar
-- rather than a single operator, reach for
-- `declare_syntax_cat` instead.

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

-- Notice: each step reduces the *leftmost* `p` node that is
-- ready to go -- the first rule tells how to rewrite it, the
-- second and third tell where to find it -- and constants do
-- not step to anything.

-- Let's pause and check a couple of examples of reasoning with
-- the step relation.

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
  sorry

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
-- `.p (.p (.c 1) (.c 2)) (.c 3)` (D) `.p (.c 3) (.c 3)` (E)
-- None of the above

-- _Quiz:_

-- What about this one?

-- .c 1

-- (A) `.c 1` (B) `.p (.c 0) (.c 1)` (C) None of the above

end SimpleArith1

-- ## Relations

-- The step relation `⟶` is an example of a relation on `Tm`.

-- Note to developers (Michael Hicks  @mwhicks1, before next release):
--     Should we be getting this (and `Deterministic`, `Multi`,
--     etc. if appropriate) from the Lean standard library? If
--     not, should we match the concepts in CSLib, if they
--     exists there?

def Relation (X : Type) := X → X → Prop

-- One simple property a relation may have is being
-- *deterministic*: like Slang's big-step evaluation, each
-- element is related to at most one other.

-- *Theorem*: For each `t`, there is at most one `t'` such that
-- `t` steps to `t'`. We prove it by induction on the
-- derivation of the first step.

-- *Proof sketch*: We show that if `x` steps to both `y1` and
-- `y2`, then `y1` and `y2` are equal, by induction on a
-- derivation of `x ⟶ y1`. There are several cases, depending
-- on the last rule used in this derivation and the last rule
-- in the given derivation of `x ⟶ y2`.

-- - If both are `plus`, the result is immediate.

-- - The cases when both derivations end with `plusLeft` or
--   `plusRight` follow by the induction hypothesis.

-- - It cannot happen that one is `plus` and the other is
--   `plusLeft`/`plusRight`, since this would imply that `x` has
--   the form `p t1 t2` where both `t1` and `t2` are constants
--   (by `plus`) *and* one of `t1` or `t2` has the form `p _`.

-- - Similarly, it cannot happen that one is `plusLeft` and the
--   other is `plusRight`, since this would imply that `x` has
--   the form `p t1 t2` where `t1` has both the form `p t11 t12`
--   and the form `c n`.

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
--     In the Rocq there is the development of a special tactic
--     to make this proof simpler. Do we want that here?

-- ### Values

-- Final states of our machine are terms of the form `c n`. We
-- call such terms *values*.

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)

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

-- As a sanity check on this change, let's re-verify
-- determinism. Here's an informal proof:

-- *Proof sketch*: We must show that if `x` steps to both `y1`
-- and `y2`, then `y1` and `y2` are equal. Consider the final
-- rules used in the derivations of `x ⟶ y1` and `x ⟶ y2`.

-- - If both are `plus`, the result is immediate.

-- - The cases when both derivations end with `plusLeft` or
--   `plusRight` follow by the induction hypothesis.

-- - It cannot happen that one is `plus` and the other is
--   `plusLeft`/`plusRight`, since this would imply that `x` has
--   the form `p t1 t2` where both `t1` and `t2` are constants
--   (by `plus`) *and* one of `t1` or `t2` has the form `p _`.

-- - Similarly, it cannot happen that one is `plusLeft` and the
--   other is `plusRight`, since this would imply that `x` has
--   the form `p t1 t2` where `t1` both has the form `p t11 t12`
--   and is a value (hence has the form `c n`).

-- Most of this proof is the same as the one above. But to get
-- maximum benefit from the exercise you should try to write
-- your formal version from scratch and just use the earlier
-- one if you get stuck. The impossible cross-cases now also
-- use the fact that a `IsValue` (a `c n`) cannot step.

theorem step_deterministic : Deterministic Step := by
  sorry

-- ### Strong Progress and Normal Forms

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

def IsNormalForm {X : Type} (R : Relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'

-- We can use this terminology to generalize the observation we
-- made in the strong progress theorem: in this language
-- (though not necessarily, in general), normal forms and
-- values are actually the same thing.

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

-- Why is this interesting? Because `IsValue` is a *syntactic*
-- concept -- it is defined by looking at the way a term is
-- written -- while `IsNormalForm` is a *semantic* one -- it is
-- defined by looking at how the term steps.

-- It is not obvious that these concepts should characterize
-- the same set of terms!

-- Indeed, we could easily have written the definitions
-- (incorrectly) so that they would *not* coincide.

-- Suppose, for example, we define `IsValue` so that it
-- includes some terms that are not finished reducing. (Even if
-- you don't work the exercise `value_not_same_as_normal_form1`
-- below and the following ones, make sure you can think of an
-- example of such a term.)

namespace Temp1

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)
  | funny (t1 : Tm) (n : Nat) : IsValue (.p t1 (.c n))     -- <---

inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) : Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm) (h : Step t1 t1') : Step (.p t1 t2) (.p t1' t2)
  | plusRight (v1 t2 t2' : Tm) (hv : IsValue v1) (h : Step t2 t2') : Step (.p v1 t2) (.p v1 t2')

-- _Quiz:_

-- Using this wrong definition of `IsValue`, to how many
-- different values does the following term reduce in zero or
-- more steps?

-- .p (.p (.c 1) (.c 2)) (.c 3)

-- _Quiz:_

-- To how many different terms does the following term `Step`
-- (in one step)?

-- .p (.p (.c 1) (.c 2)) (.p (.c 3) (.c 4))

-- ### Exercise (3 stars): value_not_same_as_normal_form1 ⭐⭐⭐

theorem value_not_same_as_normal_form :
    ∃ v, IsValue v ∧ ¬ IsNormalForm Step v := by
  apply Exists.intro (.p (.c 0) (.c 0))
  apply And.intro (.funny _ 0)
  sorry

end Temp1

-- ### Exercise (2 stars): value_not_same_as_normal_form2 ⭐⭐

-- Or we might (again, wrongly) define `Step` so that it
-- permits something designated as a value to reduce further.
-- We again lose the property that values are the same as
-- normal forms.

namespace Temp2

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)               -- Original definition

inductive Step : Tm → Tm → Prop where
  | funny (n : Nat) : Step (.c n) (.p (.c n) (.c 0))     -- <--- NEW
  | plus (n1 n2 : Nat) : Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm) (h : Step t1 t1') : Step (.p t1 t2) (.p t1' t2)
  | plusRight (v1 t2 t2' : Tm) (hv : IsValue v1) (h : Step t2 t2') : Step (.p v1 t2) (.p v1 t2')

-- _Quiz:_

-- With this definition, to how many different terms does the
-- following term step (in exactly one step)?

-- .p (.c 1) (.c 3)

theorem value_not_same_as_normal_form :
    ∃ v, IsValue v ∧ ¬ IsNormalForm Step v := by
  apply Exists.intro (.c 5)
  apply And.intro (.const 5)
  sorry

end Temp2

-- ### Exercise (3 stars): value_not_same_as_normal_form3 ⭐⭐⭐

-- Finally, we might define `IsValue` and `Step` so that there
-- is some term that is *not* a value but that *also* cannot
-- take a step. Such terms are said to be *stuck*. In this
-- case, this is caused by a mistake in the semantics, but we
-- will also see situations where, even in a correct language
-- definition, it makes sense to allow some terms to be stuck.
-- (Note that `plusRight` is missing below.)

namespace Temp3

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)

inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) : Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm) (h : Step t1 t1') : Step (.p t1 t2) (.p t1' t2)

-- _Quiz:_

-- With this definition, to how many terms does the following
-- term step (in one step)?

-- .p (.c 1) (.p (.c 1) (.c 2))

theorem value_not_same_as_normal_form :
    ∃ t, ¬ IsValue t ∧ IsNormalForm Step t := by
  apply Exists.intro (.p (.c 1) (.p (.c 1) (.c 2)))
  apply And.intro
  · sorry
  · sorry

end Temp3

-- ## Multi-Step Reduction

inductive Multi {X : Type} (R : Relation X) : X → X → Prop where
  | refl (x : X) : Multi R x x
  | step (x y z : X) (h1 : R x y) (h2 : Multi R y z) : Multi R x z

-- Note to developers (berberman):
--     I would make some arguments implicit to proivde a
--     cleaner interface (FYI the [mathlib
--     version](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html#Relation.ReflTransGen))

-- We write `⟶*` for the `Multi Step` relation on terms

notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

-- The relation `Multi R` has several crucial properties.

attribute [refl] Multi.refl

example : (.c 5 : Tm) ⟶* .c 5 := by rfl

example : (.p (.c 1) (.c 2)) ⟶* .c (1 + 2) := by
  apply Multi.step (y := .c (1 + 2))
  · exact .plus 1 2
  · rfl

theorem multi_single {X : Type} (R : Relation X) (x y : X) (h : R x y) :
    Multi R x y :=
  .step x y y h (.refl y)

theorem multi_trans {X : Type} (R : Relation X) (x y z : X)
    (g : Multi R x y) (h : Multi R y z) : Multi R x z := by
  induction g with
  | refl a => exact h
  | step a b c h1 h2 ih => exact .step a b z h1 (ih h)

-- _Quiz:_

-- Which of the following relations on numbers *cannot* be
-- expressed as `Multi R` for some `R`?

-- (A) less than or equal (B) strictly less than (C) equal (D)
-- none of the above

-- ### Examples

example :
    (.p (.p (.c 0) (.c 3)) (.p (.c 2) (.c 4))) ⟶* .c ((0 + 3) + (2 + 4)) := by
  apply Multi.step (y := .p (.c (0 + 3)) (.p (.c 2) (.c 4)))
  · exact .plusLeft _ _ _ (.plus 0 3)
  apply Multi.step (y := .p (.c (0 + 3)) (.c (2 + 4)))
  · exact .plusRight _ _ _ (.const _) (.plus 2 4)
  · exact multi_single _ _ _ (.plus (0 + 3) (2 + 4))

-- ### Exercise (1 star): test_multistep_2 ⭐

example : (.c 3 : Tm) ⟶* .c 3 := sorry

-- ### Exercise (1 star): test_multistep_3 ⭐

example : (.p (.c 0) (.c 3)) ⟶* .p (.c 0) (.c 3) := sorry

-- ### Exercise (2 stars): test_multistep_4 ⭐⭐

example :
    (.p (.c 0) (.p (.c 2) (.p (.c 0) (.c 3))))
      ⟶* (.p (.c 0) (.c (2 + (0 + 3)))) := by
  sorry

-- ### Exercise (2 stars): test_multistep_rfl ⭐⭐

-- Prove the following reduction, ending the chain with `rfl`
-- instead of `multi_single`.

example : (.p (.p (.c 1) (.c 2)) (.c 4)) ⟶* .c ((1 + 2) + 4) := by
  sorry

-- ### Normal Forms Again

-- If `t` reduces to `t'` in zero or more steps and `t'` is a
-- normal form, we say that "`t'` is *a normal form of* `t`."

def IsNormalFormOf {X : Type} (R : Relation X) (t t' : X) : Prop :=
  Multi R t t' ∧ IsNormalForm R t'

-- When `R` is deterministic (as for our language's semantics),
-- then its normal form is *unique*.

-- ### Exercise (3 stars): normal_forms_unique ⭐⭐⭐

theorem normal_forms_unique : Deterministic (IsNormalFormOf Step) := by
  -- We recommend using this initial setup as-is!
  intro x y1 y2 p1 p2
  obtain ⟨p11, p12⟩ := p1
  obtain ⟨p21, p22⟩ := p2
  sorry

-- The `Step` relation is *normalizing* it is deterministic and
-- always reaches a normal form in a finite number of steps.

def Normalizing {X : Type} (R : Relation X) : Prop :=
  ∀ t, ∃ t', IsNormalFormOf R t t'

theorem multistep_congr_1 (t1 t1' t2 : Tm) (h : t1 ⟶* t1') : (.p t1 t2) ⟶* (.p t1' t2) := by
  induction h with
  | refl x => exact .refl _
  | step x y z h1 h2 ih => exact .step _ (.p y t2) _ (.plusLeft x y t2 h1) ih

-- ### Exercise (2 stars): multistep_congr_2 ⭐⭐

theorem multistep_congr_2 (v1 t2 t2' : Tm) (hv : IsValue v1) (h : t2 ⟶* t2') :
    (.p v1 t2) ⟶* (.p v1 t2') := by
  sorry

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

-- Having defined the operational semantics of our tiny
-- programming language in two different ways (big-step and
-- small-step), it makes sense to ask whether these definitions
-- actually define the same thing!

-- They do, though it takes a little work to show it. The
-- details are left as an exercise. We consider the two
-- implications separately. First, big-step evaluation implies
-- multi-step reduction to a value.

-- ### Exercise (3 stars): multistep_of_eval ⭐⭐⭐

theorem multistep_of_eval (t : Tm) (n : Nat) (h : t ⇓ n) : t ⟶* .c n := by
  sorry

-- The key ideas in the proof can be seen in the following
-- picture:

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

-- That is, the multi-step reduction of a term of the form
-- `p t1 t2` proceeds in three phases:

-- - First, we use `plusLeft` some number of times to reduce `t1`
--   to a normal form, which must (by `nf_same_as_value`) be a
--   term of the form `c n1` for some `n1`.

-- - Next, we use `plusRight` some number of times to reduce `t2`
--   to a normal form, which must again be a term of the form
--   `c n2` for some `n2`.

-- - Finally, we use `plus` one time to reduce `p (c n1) (c n2)`
--   to `c (n1 + n2)`.

-- To formalize this intuition, you'll need the congruence
-- lemmas from above, plus some basic properties of `⟶*` (that
-- it is reflexive, transitive, and includes `⟶`).

-- ### Exercise (3 stars): multistep_of_eval_inf ⭐⭐⭐

-- Write a detailed informal version of the proof of
-- `multistep_of_eval`. (A paper exercise -- there is no Lean
-- proof to fill in here.)

-- For the converse, we need one lemma, which establishes a
-- relation between single-step reduction and big-step
-- evaluation. A single step preserves the big-step value.

-- ### Exercise (3 stars): eval_of_step ⭐⭐⭐

theorem eval_of_step (t t' : Tm) (n : Nat) (hs : t ⟶ t') (he : t' ⇓ n) : t ⇓ n := by
  sorry

-- The fact that small-step reduction implies big-step
-- evaluation is now straightforward to prove, once we have
-- factored out the observation that every normal form is a
-- value. The proof proceeds by induction on the multi-step
-- reduction sequence that is buried in the hypothesis
-- `IsNormalFormOf t t'`. (Make sure you understand the
-- statement before you start to work on the proof.)

-- ### Exercise (3 stars): eval_of_multistep ⭐⭐⭐

theorem eval_of_multistep (t t' : Tm) (h : IsNormalFormOf Step t t') :
    ∃ n, t' = .c n ∧ t ⇓ n := by
  sorry

-- ### Exercise (3 stars): interp_tm ⭐⭐⭐

-- Remember that we also defined big-step evaluation of terms
-- as a function `evalF`. Prove that it is equivalent to the
-- relational semantics. (Hint: we just proved that `Eval` and
-- `multistep` are equivalent, so logically it doesn't matter
-- which you choose. One will be easier than the other,
-- though!)

theorem evalF_eval (t : Tm) (n : Nat) : evalF t = n ↔ t ⇓ n := by
  sorry

-- ## Small-Step Slang

-- Small-step semantics for the richer `Slang` arithmetic and
-- boolean expressions. Notations: `⟶a` (arithmetic) and `⟶b`
-- (boolean).

-- We work in the `Slang` namespace, reusing the arithmetic and
-- boolean expression syntax (`Aexp`, `Bexp`) and the big-step
-- evaluator (`Aexp.eval`) from the `Slang` chapter:

namespace Slang

-- ### Arithmetic Expressions

-- The arithmetic *values* (the normal forms of the small-step
-- relation below) are just the numeric literals:

inductive IsAValue : Aexp → Prop where
  | num (n : Nat) : IsAValue (.num n)

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

-- Here is a one-step reduction: since the left operand `3` is
-- already a value, the right operand is the one that takes a
-- step.

example :
    (Aexp.plus (.num 3) (.plus (.num 2) (.num 1))) ⟶a (.plus (.num 3) (.num 3)) :=
  .plusRight _ _ _ (.num 3) (.plus 2 1)

-- ### Exercise (2 stars): strong_progress_arith ⭐⭐

-- Every arithmetic expression is either a value or can take a
-- step -- the same *strong progress* property we proved for
-- the toy language, now for the richer `Slang` arithmetic
-- expressions.

theorem strong_progress_arith (a : Aexp) : IsAValue a ∨ ∃ a', a ⟶a a' := by
  sorry

-- ### Boolean Expressions

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

-- A boolean example -- the left comparison operand reduces
-- first:

example :
    (Bexp.le (.plus (.num 1) (.num 1)) (.num 3)) ⟶b (.le (.num 2) (.num 3)) :=
  .leLeft _ _ _ (.plus 1 1)

-- _Quiz:_

-- Which of these properties does this small-step semantics for
-- `Slang` expressions satisfy? (Yes or No for each.)

-- - determinism

-- - strong progress (every non-value takes a step)

-- - values and normal forms coincide (i.e., there are no "stuck"
--   terms)

-- - the step relation is normalizing (i.e., evaluation always
--   terminates)

-- ### Exercise (3 stars): astep_deterministic ⭐⭐⭐

-- The arithmetic step relation is deterministic. (Structurally
-- this is the value-based determinism proof from the toy
-- language, repeated for `+`, `−`, and `×`; the impossible
-- cross-cases close because a value `num n` cannot step.)

theorem astep_deterministic : Deterministic AStep := by
  sorry

-- ### Exercise (3 stars): bstep_deterministic ⭐⭐⭐

-- The boolean step relation is deterministic too. The
-- comparison cases (`eq`, `neq`, `le`, `gt`) reduce their
-- operands with `⟶a`, so they inherit determinism from
-- `astep_deterministic`; `¬` and the short-circuiting `∧`
-- contribute only base cases.

theorem bstep_deterministic : Deterministic BStep := by
  sorry

-- ### Nondeterministic Evaluation

-- `⟶n`: like `⟶a`, but with the `IsAValue` guard on the "step
-- the right operand" rules removed, so the evaluation order is
-- nondeterministic.

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

-- Unlike `⟶a`, this relation really is nondeterministic: a
-- single term can step in two different ways, depending on
-- which operand we choose to advance.

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

-- ### Exercise (2 stars): anstep_preserves_eval ⭐⭐

-- Prove that one nondeterministic step leaves the big-step
-- value unchanged. *Hint:* induction on the step derivation;
-- each case is immediate from `eval` and, where present, the
-- induction hypothesis.

theorem anstep_preserves_eval (a a' : Aexp) (h : a ⟶n a') : a.eval = a'.eval := by
  sorry

-- This lifts to any number of steps by a routine induction on
-- the multi-step derivation:

theorem multi_anstep_preserves_eval (a a' : Aexp) (h : Multi ANStep a a') : a.eval = a'.eval := by
  induction h with
  | refl x => rfl
  | step x y z h1 _ ih => rw [anstep_preserves_eval x y h1]; exact ih

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

-- Now put the pieces together: prove that the deterministic
-- and nondeterministic semantics always compute the *same*
-- final result. That is, if `a` fully reduces to `.num n1`
-- under `⟶a` and to `.num n2` under `⟶n`, then `n1 = n2`.

-- *Hint:* both `.num n1` and `.num n2` are reachable by `⟶n`
-- (use `multi_astep_imp_anstep` for the first), and `⟶n`
-- preserves `eval`.

theorem astep_anstep_agree (a : Aexp) (n1 n2 : Nat)
    (hd : Multi AStep a (.num n1)) (hn : Multi ANStep a (.num n2)) : n1 = n2 := by
  sorry

-- ### A Small-Step Stack Machine

-- Our last example is a small-step semantics for a *stack
-- machine* that evaluates arithmetic expressions. The
-- machine's instructions push a constant or combine the top
-- two stack entries. The machine's behavior should match the
-- big-step `Aexp.eval` function defined earlier.

-- A *program* is a list of instructions, and the *stack* is a
-- list of numbers.

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

-- Now the small-step machine itself: each step consumes the
-- next instruction and updates the stack.

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

-- Prove the compiler correct: running the compiled program
-- from the empty stack reduces, in some number of steps, to a
-- stack holding exactly the value of the expression.

-- *Hint:* this will not go through by a direct induction --
-- the induction hypothesis is too weak. Prove a more general
-- statement first, about running `compile a` followed by *any*
-- leftover program `p`, starting from *any* stack `stk`.
-- (Reassociating the `++`s with `List.append_assoc`, and
-- chaining steps with `multi_trans`/`multi_single`, are the
-- moves you need.)

theorem compiler_is_correct (a : Aexp) :
    Multi StackStep (compile a, []) ([], [a.eval]) := by
  sorry

end Slang


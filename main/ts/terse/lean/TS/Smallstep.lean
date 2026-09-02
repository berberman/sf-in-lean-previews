import TS.Slang
import TS.AttributeDecls

import SFLCompat

--  # Smallstep: Small-step Operational Semantics

--  ## Big-step and Small-step Evaluation

--  Our semantics for expressions is written in the
--  so-called "big-step" style. Evaluation rules take an
--  expression to a final answer "all in one step":

--  2 + 2 + 3 * 4 ⇓ 16

--  But big-step semantics makes it hard to talk about what
--  happens *along the way*.
--
--  *Small-step* style: alternatively, we can show how to
--  "reduce" an expression to a simpler form by performing a
--  single step of computation:

--  2 + 2 + 3 * 4
--  ⟶ 2 + 2 + 12
--  ⟶ 4 + 12
--  ⟶ 16

--  Advantages of the small-step style include:
--
--  - Finer-grained "abstract machine", closer to real
--    implementations.
--
--  - Extends smoothly to concurrent languages and languages
--    with other sorts of *computational effects*.
--
--  - Separates *divergence* (nontermination) from
--    *stuckness* (run-time error).

--  ## A Toy Language

inductive Tm where
  | c (n : Nat)          -- Constant
  | p (t₁ t₂ : Tm)       -- Plus

--  A standard big-step evaluator, as a function.

def evalF (t : Tm) : Nat :=
  match t with
  | .c n => n
  | .p t₁ t₂ => evalF t₁ + evalF t₂

--  Here is the same evaluator, written in exactly the same
--  style, but formulated as an inductively defined
--  relation. We use the notation `t ⇓ n` for "`t` evaluates
--  to `n`."
--
--  The `notation` command below is how that is declared: it
--  introduces `⇓` as infix syntax for the `Eval` relation
--  defined with it, with a precedence saying how tightly it
--  binds. This is the lightweight way to name a relation;
--  later chapters, where a whole object language needs a
--  grammar rather than a single operator, reach for
--  `declare_syntax_cat` instead.

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

--  Notice: each step reduces the *leftmost* `p` node that
--  is ready to go — the first rule tells how to rewrite it,
--  the second and third tell where to find it — and
--  constants do not step to anything.

--  Let's pause and check a couple of examples of reasoning
--  with the step relation.
--
--  If `t₁` steps to `t₁'`, then `p t₁ t₂` steps to
--  `p t₁' t₂`.

example :
    (.p
      (.p (.c 1) (.c 3))
      (.p (.c 2) (.c 4))) ⟶
    (.p
      (.c 4)
      (.p (.c 2) (.c 4))) := by
  apply Step.plusLeft; apply Step.plus

--  ### Exercise (1 star): test_step_2 ⭐

--  Right-hand sides step only once the left side is a
--  value.

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
--  `.p (.p (.c 1) (.c 2)) (.c 3)` (D) `.p (.c 3) (.c 3)`
--  (E) None of the above

--   ----------------------------------------

--  _Quiz:_

--  What about this one?

--  .c 1

--  (A) `.c 1` (B) `.p (.c 0) (.c 1)` (C) None of the above

--   ----------------------------------------

end SimpleArith1

--  ## Relations

--  The step relation `⟶` is an example of a relation on
--  `Tm`.

def Relation (X : Type) := X → X → Prop

--  One simple property a relation may have is being
--  *deterministic*: like Slang's big-step evaluation, each
--  element is related to at most one other.
--
--  *Theorem*: For each `t`, there is at most one `t'` such
--  that `t` steps to `t'`. We prove it by induction on the
--  derivation of the first step.
--
--  *Proof sketch*: We show that if `x` steps to both `y₁`
--  and `y₂`, then `y₁` and `y₂` are equal, by induction on
--  a derivation of `x ⟶ y₁`. There are several cases,
--  depending on the last rule used in this derivation and
--  the last rule in the given derivation of `x ⟶ y₂`.
--
--  - If both are `plus`, the result is immediate.
--
--  - The cases when both derivations end with `plusLeft` or
--    `plusRight` follow by the induction hypothesis.
--
--  - It cannot happen that one is `plus` and the other is
--    `plusLeft`/`plusRight`, since this would imply that
--    `x` has the form `p t₁ t₂` where both `t₁` and `t₂`
--    are constants (by `plus`) *and* one of `t₁` or `t₂`
--    has the form `p _`.
--
--  - Similarly, it cannot happen that one is `plusLeft` and
--    the other is `plusRight`, since this would imply that
--    `x` has the form `p t₁ t₂` where `t₁` has both the
--    form `p t₁₁ t₁₂` and the form `c n`.
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

--  ### Values

--  Final states of our machine are terms of the form `c n`.
--  We call such terms *values*.

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)

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

--  As a sanity check on this change, let's re-verify
--  determinism. Here's an informal proof:
--
--  *Proof sketch*: We must show that if `x` steps to both
--  `y₁` and `y₂`, then `y₁` and `y₂` are equal. Consider
--  the final rules used in the derivations of `x ⟶ y₁` and
--  `x ⟶ y₂`.
--
--  - If both are `plus`, the result is immediate.
--
--  - The cases when both derivations end with `plusLeft` or
--    `plusRight` follow by the induction hypothesis.
--
--  - It cannot happen that one is `plus` and the other is
--    `plusLeft`/`plusRight`, since this would imply that
--    `x` has the form `p t₁ t₂` where both `t₁` and `t₂`
--    are constants (by `plus`) *and* one of `t₁` or `t₂`
--    has the form `p _`.
--
--  - Similarly, it cannot happen that one is `plusLeft` and
--    the other is `plusRight`, since this would imply that
--    `x` has the form `p t₁ t₂` where `t₁` both has the
--    form `p t₁₁ t₁₂` and is a value (hence has the form
--    `c n`).
--
--  Most of this proof is the same as the one above. But to
--  get maximum benefit from the exercise you should try to
--  write your formal version from scratch and just use the
--  earlier one if you get stuck. The impossible cross-cases
--  now also use the fact that a `IsValue` (a `c n`) cannot
--  step.

theorem step_deterministic : Deterministic Step := by
  sorry

--  ### Strong Progress and Normal Forms

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

def IsNormalForm {X : Type} (R : Relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'

--  We can use this terminology to generalize the
--  observation we made in the strong progress theorem: in
--  this language (though not necessarily, in general),
--  normal forms and values are actually the same thing.

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

--  Why is this interesting? Because `IsValue` is a
--  *syntactic* concept — it is defined by looking at the
--  way a term is written — while `IsNormalForm` is a
--  *semantic* one — it is defined by looking at how the
--  term steps.
--
--  It is not obvious that these concepts should
--  characterize the same set of terms!
--
--  Indeed, we could easily have written the definitions
--  (incorrectly) so that they would *not* coincide.
--
--  Suppose, for example, we define `IsValue` so that it
--  includes some terms that are not finished reducing.
--  (Even if you don't work the exercise
--  `value_not_same_as_normal_form1` below and the following
--  ones, make sure you can think of an example of such a
--  term.)

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

--  Using this wrong definition of `IsValue`, to how many
--  different values does the following term reduce in zero
--  or more steps?

--  .p (.p (.c 1) (.c 2)) (.c 3)

--   ----------------------------------------

--  _Quiz:_

--  To how many different terms does the following term
--  `Step` (in one step)?

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

--  Or we might (again, wrongly) define `Step` so that it
--  permits something designated as a value to reduce
--  further. We again lose the property that values are the
--  same as normal forms.

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

--  With this definition, to how many different terms does
--  the following term step (in exactly one step)?

--  .p (.c 1) (.c 3)

--   ----------------------------------------

theorem value_not_same_as_normal_form :
    ∃ v, IsValue v ∧ ¬ IsNormalForm Step v := by
  apply Exists.intro (.c 5)
  apply And.intro (.const 5)
  sorry

end Temp2

--  ### Exercise (3 stars): value_not_same_as_normal_form3 (Optional) ⭐⭐⭐

--  Finally, we might define `IsValue` and `Step` so that
--  there is some term that is *not* a value but that *also*
--  cannot take a step. Such terms are said to be *stuck*.
--  In this case, this is caused by a mistake in the
--  semantics, but we will also see situations where, even
--  in a correct language definition, it makes sense to
--  allow some terms to be stuck. (Note that `plusRight` is
--  missing below.)

namespace Temp3

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)

inductive Step : Tm → Tm → Prop where
  | plus (n₁ n₂ : Nat) : Step (.p (.c n₁) (.c n₂)) (.c (n₁ + n₂))
  | plusLeft (t₁ t₁' t₂ : Tm) (h : Step t₁ t₁') : Step (.p t₁ t₂) (.p t₁' t₂)

--   ----------------------------------------

--  _Quiz:_

--  With this definition, to how many terms does the
--  following term step (in one step)?

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

inductive Multi {X : Type} (R : Relation X) : X → X → Prop where
  | refl (x : X) : Multi R x x
  | step (x y z : X) (h₁ : R x y) (h₂ : Multi R y z) : Multi R x z

--  We write `⟶*` for the `Multi Step` relation on terms

notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

--  The relation `Multi R` has several crucial properties.

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
  | step a b c h₁ h₂ ih => exact .step a b z h₁ (ih h)

--   ----------------------------------------

--  _Quiz:_

--  Which of the following relations on numbers *cannot* be
--  expressed as `Multi R` for some `R`?
--
--  (A) less than or equal (B) strictly less than (C) equal
--  (D) none of the above

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

--  Prove the following reduction, ending the chain with
--  `rfl` instead of `multi_single`.

example : (.p (.p (.c 1) (.c 2)) (.c 4)) ⟶* .c ((1 + 2) + 4) := by
  sorry

--  ### Normal Forms Again

--  If `t` reduces to `t'` in zero or more steps and `t'` is
--  a normal form, we say that "`t'` is *a normal form of*
--  `t`."

def IsNormalFormOf {X : Type} (R : Relation X) (t t' : X) : Prop :=
  Multi R t t' ∧ IsNormalForm R t'

--  When `R` is deterministic (as for our language's
--  semantics), then its normal form is *unique*.

--  ### Exercise (3 stars): normal_forms_unique (Optional) ⭐⭐⭐

theorem normal_forms_unique : Deterministic (IsNormalFormOf Step) := by
  -- We recommend using this initial setup as-is!
  intro x y₁ y₂ p₁ p₂
  obtain ⟨p₁₁, p₁₂⟩ := p₁
  obtain ⟨p₂₁, p₂₂⟩ := p₂
  sorry

--  The `Step` relation is *normalizing* it is deterministic
--  and always reaches a normal form in a finite number of
--  steps.

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

--  Having defined the operational semantics of our tiny
--  programming language in two different ways (big-step and
--  small-step), it makes sense to ask whether these
--  definitions actually define the same thing!
--
--  They do, though it takes a little work to show it. The
--  details are left as an exercise. We consider the two
--  implications separately. First, big-step evaluation
--  implies multi-step reduction to a value.

--  ### Exercise (3 stars): multistep_of_eval ⭐⭐⭐

theorem multistep_of_eval (t : Tm) (n : Nat) (h : t ⇓ n) : t ⟶* .c n := by
  sorry

--  The key ideas in the proof can be seen in the following
--  picture:

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

--  That is, the multi-step reduction of a term of the form
--  `p t₁ t₂` proceeds in three phases:
--
--  - First, we use `plusLeft` some number of times to
--    reduce `t₁` to a normal form, which must (by
--    `nf_same_as_value`) be a term of the form `c n₁` for
--    some `n₁`.
--
--  - Next, we use `plusRight` some number of times to
--    reduce `t₂` to a normal form, which must again be a
--    term of the form `c n₂` for some `n₂`.
--
--  - Finally, we use `plus` one time to reduce
--    `p (c n₁) (c n₂)` to `c (n₁ + n₂)`.
--
--  To formalize this intuition, you'll need the congruence
--  lemmas from above, plus some basic properties of `⟶*`
--  (that it is reflexive, transitive, and includes `⟶`).

--  ### Exercise (3 stars): multistep_of_eval_inf (Optional) ⭐⭐⭐

--  Write a detailed informal version of the proof of
--  `multistep_of_eval`. (A paper exercise — there is no
--  Lean proof to fill in here.)

--  For the converse, we need one lemma, which establishes a
--  relation between single-step reduction and big-step
--  evaluation. A single step preserves the big-step value.

--  ### Exercise (3 stars): eval_of_step ⭐⭐⭐

theorem eval_of_step (t t' : Tm) (n : Nat) (hs : t ⟶ t') (he : t' ⇓ n) : t ⇓ n := by
  sorry

--  The fact that small-step reduction implies big-step
--  evaluation is now straightforward to prove, once we have
--  factored out the observation that every normal form is a
--  value. The proof proceeds by induction on the multi-step
--  reduction sequence that is buried in the hypothesis
--  `IsNormalFormOf t t'`. (Make sure you understand the
--  statement before you start to work on the proof.)

--  ### Exercise (3 stars): eval_of_multistep ⭐⭐⭐

theorem eval_of_multistep (t t' : Tm) (h : IsNormalFormOf Step t t') :
    ∃ n, t' = .c n ∧ t ⇓ n := by
  sorry

--  ### Exercise (3 stars): interp_tm (Optional) ⭐⭐⭐

--  Remember that we also defined big-step evaluation of
--  terms as a function `evalF`. Prove that it is equivalent
--  to the relational semantics. (Hint: we just proved that
--  `Eval` and `multistep` are equivalent, so logically it
--  doesn't matter which you choose. One will be easier than
--  the other, though!)

theorem evalF_eval (t : Tm) (n : Nat) : evalF t = n ↔ t ⇓ n := by
  sorry

--  ## Small-Step Slang

--  Small-step semantics for the richer `Slang` arithmetic
--  and boolean expressions. Notations: `⟶a` (arithmetic)
--  and `⟶b` (boolean).

--  We work in the `Slang` namespace, reusing the arithmetic
--  and boolean expression syntax (`Aexp`, `Bexp`) and the
--  big-step evaluator (`Aexp.eval`) from the `Slang`
--  chapter:

namespace Slang

--  ### Arithmetic Expressions

--  The arithmetic *values* (the normal forms of the
--  small-step relation below) are just the numeric
--  literals:

inductive IsAValue : Aexp → Prop where
  | num (n : Nat) : IsAValue (.num n)

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

--  Here is a one-step reduction: since the left operand `3`
--  is already a value, the right operand is the one that
--  takes a step.

example :
    (Aexp.plus (.num 3) (.plus (.num 2) (.num 1))) ⟶a (.plus (.num 3) (.num 3)) :=
  .plusRight _ _ _ (.num 3) (.plus 2 1)

--  ### Exercise (2 stars): strong_progress_arith ⭐⭐

--  Every arithmetic expression is either a value or can
--  take a step — the same *strong progress* property we
--  proved for the toy language, now for the richer `Slang`
--  arithmetic expressions.

theorem strong_progress_arith (a : Aexp) : IsAValue a ∨ ∃ a', a ⟶a a' := by
  sorry

--  ### Boolean Expressions

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

--  A boolean example — the left comparison operand reduces
--  first:

example :
    (Bexp.le (.plus (.num 1) (.num 1)) (.num 3)) ⟶b (.le (.num 2) (.num 3)) :=
  .leLeft _ _ _ (.plus 1 1)

--   ----------------------------------------

--  _Quiz:_

--  Which of these properties does this small-step semantics
--  for `Slang` expressions satisfy? (Yes or No for each.)
--
--  - determinism
--
--  - strong progress (every non-value takes a step)
--
--  - values and normal forms coincide (i.e., there are no
--    "stuck" terms)
--
--  - the step relation is normalizing (i.e., evaluation
--    always terminates)

--   ----------------------------------------

--  ### Exercise (3 stars): astep_deterministic ⭐⭐⭐

--  The arithmetic step relation is deterministic.
--  (Structurally this is the value-based determinism proof
--  from the toy language, repeated for `+`, `−`, and `×`;
--  the impossible cross-cases close because a value `num n`
--  cannot step.)

theorem astep_deterministic : Deterministic AStep := by
  sorry

--  ### Exercise (3 stars): bstep_deterministic ⭐⭐⭐

--  The boolean step relation is deterministic too. The
--  comparison cases (`eq`, `neq`, `le`, `gt`) reduce their
--  operands with `⟶a`, so they inherit determinism from
--  `astep_deterministic`; `¬` and the short-circuiting `∧`
--  contribute only base cases.

theorem bstep_deterministic : Deterministic BStep := by
  sorry

--  ### Nondeterministic Evaluation

--  `⟶n`: like `⟶a`, but with the `IsAValue` guard on the
--  "step the right operand" rules removed, so the
--  evaluation order is nondeterministic.

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

--  Unlike `⟶a`, this relation really is nondeterministic: a
--  single term can step in two different ways, depending on
--  which operand we choose to advance.

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

--  ### Exercise (2 stars): anstep_preserves_eval ⭐⭐

--  Prove that one nondeterministic step leaves the big-step
--  value unchanged. *Hint:* induction on the step
--  derivation; each case is immediate from `eval` and,
--  where present, the induction hypothesis.

theorem anstep_preserves_eval (a a' : Aexp) (h : a ⟶n a') : a.eval = a'.eval := by
  sorry

--  This lifts to any number of steps by a routine induction
--  on the multi-step derivation:

theorem multi_anstep_preserves_eval (a a' : Aexp) (h : Multi ANStep a a') : a.eval = a'.eval := by
  induction h with
  | refl x => rfl
  | step x y z h₁ _ ih => rw [anstep_preserves_eval x y h₁]; exact ih

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

--  Now put the pieces together: prove that the
--  deterministic and nondeterministic semantics always
--  compute the *same* final result. That is, if `a` fully
--  reduces to `.num n₁` under `⟶a` and to `.num n₂` under
--  `⟶n`, then `n₁ = n₂`.
--
--  *Hint:* both `.num n₁` and `.num n₂` are reachable by
--  `⟶n` (use `multi_astep_imp_anstep` for the first), and
--  `⟶n` preserves `eval`.

theorem astep_anstep_agree (a : Aexp) (n₁ n₂ : Nat)
    (hd : Multi AStep a (.num n₁)) (hn : Multi ANStep a (.num n₂)) : n₁ = n₂ := by
  sorry

--  ### A Small-Step Stack Machine

--  Our last example is a small-step semantics for a *stack
--  machine* that evaluates arithmetic expressions. The
--  machine's instructions push a constant or combine the
--  top two stack entries. The machine's behavior should
--  match the big-step `Aexp.eval` function defined earlier.
--
--  A *program* is a list of instructions, and the *stack*
--  is a list of numbers.

inductive SInstr where
  | push (n : Nat)
  | plus
  | minus
  | mult

abbrev Stack := List Nat
abbrev Prog := List SInstr

--  The compiler emits code in the postfix order sketched
--  above:

def compile : Aexp → Prog
  | .num n => [.push n]
  | .plus a₁ a₂ => compile a₁ ++ compile a₂ ++ [.plus]
  | .minus a₁ a₂ => compile a₁ ++ compile a₂ ++ [.minus]
  | .mult a₁ a₂ => compile a₁ ++ compile a₂ ++ [.mult]

example : compile (.plus (.num 2) (.num 3)) = [.push 2, .push 3, .plus] := rfl

--  Now the small-step machine itself: each step consumes
--  the next instruction and updates the stack.

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

--  Prove the compiler correct: running the compiled program
--  from the empty stack reduces, in some number of steps,
--  to a stack holding exactly the value of the expression.
--
--  *Hint:* this will not go through by a direct induction —
--  the induction hypothesis is too weak. Prove a more
--  general statement first, about running `compile a`
--  followed by *any* leftover program `p`, starting from
--  *any* stack `stk`. (Reassociating the `++`s with
--  `List.append_assoc`, and chaining steps with
--  `multi_trans`/`multi_single`, are the moves you need.)

theorem compiler_is_correct (a : Aexp) :
    Multi StackStep (compile a, []) ([], [a.eval]) := by
  sorry

end Slang

--  ### Automation with `solve_by_elim`

--  Proofs that one expression multisteps to another can be
--  tedious...

example : (.p (.c 3) (.p (.c 3) (.c 4))) ⟶* (.c 10) := by
  apply Multi.step (y := .p (.c 3) (.c 7))
  · apply Step.plusRight
    · apply IsValue.const
    · apply Step.plus
  · apply Multi.step (y := .c 10)
    · apply Step.plus
    · apply Multi.refl

--  We can automate such tedious proofs with
--  `solve_by_elim`:

example : (.p (.c 3) (.p (.c 3) (.c 4))) ⟶* (.c 10) := by
  repeat apply Multi.step <;>
    try solve_by_elim [Step.plusRight, Step.plusLeft, Step.plus, IsValue.const]

--  This one script would suffice to prove most concrete
--  reduction sequences for this simple language. To make it
--  work for others, we would need to supply constructors
--  for those other languages to `solve_by_elim`. The
--  languages we will study in this book can grow to a large
--  number of constructors for their `Step` relations, so
--  we'd like a way to supply all of them to `solve_by_elim`
--  more easily. Luckily, Lean supports this. We can
--  register a constructor (or lemma) for use with
--  `solve_by_elim` with an `attribute` command:

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Attributes)
--  The command below tags all of these constructors with
--  the `SimpleArith` attribute, which we can then use to
--  automatically pull all of these constructors in when we
--  use `solve_by_elim`. However, due to a limitation of
--  Lean, this attribute needs to be pre-declared in a
--  different file; we can't create it here and then
--  immediately use it.
--
--  For this book, we've predeclared all the attributes
--  we'll use in a file called `AttributeDecls.lean`,
--  following the typical pattern from libraries like
--  Mathlib.
--  END DETAILS

attribute [SimpleArith] Step.plusRight Step.plusLeft Step.plus IsValue.const

--  This `using` option then tells `solve_by_elim` to try to
--  use every constructor we've registered with the supplied
--  attribute:

example : (.p (.c 3) (.p (.c 3) (.c 4))) ⟶* (.c 10) := by
  repeat apply Multi.step <;>
    try solve_by_elim using SimpleArith

--  We can package all this up into a dedicated tactic for
--  solving reduction sequences, which we'll call
--  `normalize`:

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

-- Built on 2026-09-02 21:24 UTC

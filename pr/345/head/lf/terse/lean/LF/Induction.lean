import LF.Basics

import SFLCompat

--  # Induction: Proof by Induction

--  This chapter shows how to carry out *proofs by
--  induction*, one of the most fundamental reasoning tools
--  in computer science and mathematics, in Lean.

--  ## Separate Compilation

--  Lean will first need to compile `Basics.lean` so it can
--  be imported here — detailed instructions are in the full
--  version of this chapter...

--  ## Review

--  We reopen the namespace from the previous chapter to
--  group this chapter's definitions and theorems with the
--  custom natural-number development and keep their names
--  distinct from the standard library.
--
--  Now let's review what we learned in Basics using some
--  quiz questions and an exercise.

namespace NatPlayground.Nat

--   ----------------------------------------

--  _Quiz:_

--  To prove the following theorem, which tactics will we
--  need besides `rfl`? (Recall that `||` recurses on its
--  *first* argument: `true || b = true` and
--  `false || b = b`, by definition.)
--
--      theorem review₁ : (true || false) = true
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

--  _Quiz:_

--  What about the next one?
--
--      theorem review₂ (b : Bool) : (true || b) = true
--
--  Which tactics do we need besides `rfl`?
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

--  _Quiz:_

--  What if we change the order of the arguments of `||`?
--
--      theorem review₃ (b : Bool) : (b || true) = true
--
--  Which tactics do we need besides `rfl`?
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

--  _Quiz:_

--  What about this one? (Recall that our `add` function
--  recurses on its *second* argument. Its simplification
--  rules include `n + zero = n` and
--  `n + (m + 1) = (n + m) + 1`.)
--
--      theorem review₄ (n : Nat) : n + zero = n
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

--  _Quiz:_

--  What about this?
--
--      theorem review₅ (n : Nat) : zero + n = n
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

--  ### Exercise (1 star): succ_eq_add_one ⭐

--  One more warm-up exercise. Prove the following theorem,
--  using theorems from Basics:

theorem succ_eq_add_one (n : Nat) : succ n = n + one := by
  sorry

--  ## Proof by Induction

--  We will introduce proofs by induction on natural
--  numbers, first motivating why induction is needed, and
--  then explaining what it is and how you do it in Lean.

--  ### Motivation

--  For the `add_zero` simplification rule, we were able to
--  prove that `zero` is a neutral element for `+` on the
--  *right* using just `rfl`.

--  But the proof that it is also a neutral element on the
--  *left* gets stuck...

sf_expect_failure_in
  example (n : Nat) : zero + n = n := by
    rfl    -- doesn't work here!

--  Output:
--    Tactic `rfl` failed: The left-hand side
--      zero + n
--    is not definitionally equal to the right-hand side
--      n
--
--    n : Nat
--    ⊢ zero + n = n

--  And reasoning by cases using `cases` on `n` doesn't get
--  us much further: the branch of the case analysis where
--  we assume `n = zero` goes through just fine, but in the
--  branch where `n = n' + 1` for some `n'` we get stuck in
--  exactly the same way.

sf_expect_failure_in
  example (n : Nat) : zero + n = n := by
    cases n with
    | zero => /- n = zero -/
      rewrite [add_zero]
      rfl
      -- so far so good...
    | succ n' =>   /- n = succ n' -/
      _     -- ...but we're stuck on zero + n'

--  Output:
--    unsolved goals
--    case succ
--    n' : Nat
--    ⊢ zero + succ n' = succ n'

--  ### Induction: In Principle and in Lean

--  We need a bigger hammer: the *principle of induction*
--  over natural numbers:
--
--  If `P(n)` is some proposition involving a natural number
--  `n`, and we want to show that `P` holds for *all*
--  numbers, we can reason like this:
--
--  - show that `P(zero)` holds
--  - show that, if `P(n')` holds, then so does `P(succ n')`
--  - conclude that `P(n)` holds for all `n`.
--
--  For example...

theorem zero_add (n : Nat) : zero + n = n := by
  induction n with
  | zero => /- n = zero -/
    rewrite [add_zero]
    rfl
  | succ n' ih => /- n = succ n' -/
    /-
      Goal: zero + (succ n') = succ n'
      We can rewrite `zero + (succ n')` to `succ (zero + n')`.
      Then we can rewrite with the induction hypothesis.
    -/
    rewrite [add_succ, ih]
    rfl

--  Let's try this one together:

theorem beq_self (n : Nat) : (n == n) = true := by
  sorry

--  ### Exercise (2 stars): basic_induction ⭐⭐

--  Here's another related fact about addition, which we'll
--  need later. (The proof is left as an exercise.)

theorem add_comm (n m : Nat) :
    n + m = m + n := by
  sorry

--  ### Tip: The `rw` Tactic

--  As you've probably noticed, a common pattern in Lean
--  proofs is `rewrite [...]` followed by `rfl`. Lean also
--  provides a tactic that combines these two steps:
--  `rw [...]` will automatically close the goal if the
--  rewrite makes the goal true by definition. For example,
--  instead of
--
--      rewrite [double_zero]; rfl
--
--  we could write this:
--
--      rw [double_zero]

--  If `rw` leaves a goal that looks definitionally true,
--  try adding `rfl` after it.

--  THE FOLLOWING DETAILS CAN BE SKIPPED
set_option pp.fieldNotation false
--  END DETAILS

--  ## Proofs Within Proofs

--  New tactic: `have`.

theorem mul_zero_add' (n m : Nat) :
    ((zero + n) + zero) * m = n * m := by
  have h : (zero + n) + zero = n := by
    rw [zero_add, add_zero]
  rw [h]

sf_expect_failure_in
  example (n m p q : Nat) :
     (n + m) + (p + q) = (m + n) + (p + q) := by
    /-
      We just need to swap (n + m) for (m + n)... seems
      like add_comm should do the trick!
      But `rw [add_comm]` might rewrite the wrong `+`!
    -/
    rw [add_comm]

--  Output:
--    unsolved goals
--    n m p q : Nat
--    ⊢ p + q + (n + m) = m + n + (p + q)

--  To use `add_comm` at the point where we need it, we can
--  supply explicit arguments: `rw [add_comm n m]` tells
--  Lean exactly which `+` to rewrite. (We can also use
--  `have` to establish the specific equation we want, then
--  rewrite with it.)

theorem add_rearrange (n m p q : Nat) :
    (n + m) + (p + q) = (m + n) + (p + q) := by
  rw [add_comm n m]

--  ## Formal vs. Informal Proof

--  "Informal proofs are algorithms; formal proofs are
--  code."

--  ## Aside: Using Code Actions to Generate Match Skeletons

--  Lean's language server can suggest *code actions*, which
--  are small editor commands that modify the source code.
--
--  In VS Code, a lightbulb icon appears on the left when a
--  code action is available at your cursor.
--
--  Let's look at a code action for `induction`. Suppose we
--  start with the following incomplete proof:

sf_expect_failure_in
  example (n : Nat) : Nat.beq n n = true := by
    induction n

--  Put your cursor on `induction n` and open the code
--  action menu.

--  Click the lightbulb.

--  This gives us the basic structure of the proof without
--  requiring us to write each branch by hand. We can then
--  focus on proving each case.

--  Let's do the proof!

example (n : Nat) : Nat.beq n n = true := by
  sorry

--  The same trick also works for `match` expressions. For
--  example, suppose we start with

sf_expect_failure_in
  def isZero (n : Nat) : Bool :=
    match n

--  Lean can generate the missing branches:

sf_expect_failure_in
  def isZero (n : Nat) : Bool :=
    match n with
    | .zero => _
    | .succ n => _

--  One note: Sometimes the variables the code action
--  chooses are not ideal, so you might want to change them.

--  ## More Exercises

--  ### Exercise (1 star): mul_one ⭐

theorem mul_one (p : Nat) :
    one * p = p := by
  sorry

--  By default, `rewrite` and `rw` rewrite left to right,
--  i.e., they transform the goal (or a hypothesis) from the
--  form on the left side of the equality to the right side.
--  To rewrite from right to left, use `rewrite [← h]` or
--  `rw [← h]`, where `←` is entered as `\l` or `\<-`.

--  These exercises state facts that will be used later. We
--  don't need to work them in class.

--  ### Exercise (3 stars): mul_comm ⭐⭐⭐

--  Use `have` (or `rw` with explicit arguments) to help
--  prove `add_shuffle3`. You don't need to use induction.

theorem add_shuffle3 (n m p : Nat) : n + m + p = n + p + m := by
  sorry

theorem succ_mul (m n : Nat) :
    (succ n) * m = (n * m) + m := by
  sorry

--  Now prove commutativity of multiplication.

theorem mul_comm (m n : Nat) :
    m * n = n * m := by
  sorry

--  ### Exercise (3 stars): more_exercises (Optional) ⭐⭐⭐

--  Take a piece of paper. For each of the following
--  theorems, first *think* about whether (a) it can be
--  proved using only simplification and rewriting, (b) it
--  also requires case analysis (`cases`), or (c) it also
--  requires induction. Write down your prediction. Then
--  fill in the proof. (There is no need to turn in your
--  piece of paper; this is just to encourage you to reflect
--  before you hack!)

theorem ble_refl (n : Nat) :
    Nat.ble n n = true := by
  sorry

theorem andb_false (b : Bool) :
    (b && false) = false := by
  sorry

theorem all3_spec (b c : Bool) :
    ((b && c) || ((!b) || (!c))) = true := by
  sorry

theorem right_distrib (n m p : Nat) :
    (n + m) * p = (n * p) + (m * p) := by
  sorry

theorem left_distrib (n m p : Nat) :
    p * (n + m) = (p * n) + (p * m) := by
  sorry

theorem mul_assoc (n m p : Nat) :
    n * (m * p) = (n * m) * p := by
  sorry

--  ## A New Tactic Combinator: `<;>`

--  New tactic combinator: `t₁ <;> t₂` runs `t₁`, then runs
--  `t₂` on every subgoal produced by `t₁`.

example (b : Bool) : (b || true) = true := by
  cases b <;> rfl

--  This is short for:

example (b : Bool) : (b || true) = true := by
  cases b with
  | false => rfl
  | true  => rfl

--  We can also chain `<;>`s.

example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl

-- Built on 2026-09-01 12:44 UTC

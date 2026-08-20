import LF.Basics

import LF.SFLCompat

-- # Induction: Proof by Induction

-- Note to developers (before next release):
--     `SOONER: We should also consider adding more examples to clarify
--     the concepts introduced in this chapter. This could help in
--     reinforcing the understanding of induction principles.
--
--     LATER: In 3/22, MRC and BCP discussed "inlining" IndPrinciples
--     into earlier chapters, thus eliminating it as a chapter. This
--     chapter, Induction, is the first place a change would occur.  We
--     would present [nat_ind] here. Then in Lists/Poly we'd present
--     [list_ind], and the rest would go in IndProp and ProofObjects. The
--     main wrinkle is that we'd need to introduce [apply] here instead of
--     in Tactics if we want to preserve the presentation. The discussion
--     is preserved here: https://github.com/DeepSpec/sfdev/pull/471.
--
--     LATER: Now that we've added Steve's nice late-policy exercise in
--     Basics.v, the assignment for that chapter is probably hard enough.  Now
--     what about this chapter?  Can/should we make it a notch or two
--     harder?`

-- ## Separate Compilation

-- Lean will first need to compile `Basics.lean` so it can be
-- imported here — detailed instructions are in the full
-- version of this chapter...

-- We reopen the namespace from the previous chapter to group
-- this chapter's definitions and theorems with the custom
-- natural-number development and keep their names distinct
-- from the standard library.

namespace NatPlayground.Nat

-- ## Review

-- _Quiz:_

-- To prove the following theorem, which tactics will we need
-- besides `rfl`? (Recall that `||` recurses on its *first*
-- argument: `true || b = true` and `false || b = b`, by
-- definition.)

--   theorem review₁ : (true || false) = true

-- (A) none

-- (B) `rewrite`

-- (C) `cases`

-- (D) both `rewrite` and `cases`

-- (E) can't be done with the tactics we've seen.

-- _Quiz:_

-- What about the next one?

--   theorem review₂ (b : Bool) : (true || b) = true

-- Which tactics do we need besides `rfl`?

-- (A) none

-- (B) `rewrite`

-- (C) `cases`

-- (D) both `rewrite` and `cases`

-- (E) can't be done with the tactics we've seen.

-- _Quiz:_

-- What if we change the order of the arguments of `||`?

--   theorem review₃ (b : Bool) : (b || true) = true

-- Which tactics do we need besides `rfl`?

-- (A) none

-- (B) `rewrite`

-- (C) `cases`

-- (D) both `rewrite` and `cases`

-- (E) can't be done with the tactics we've seen.

-- _Quiz:_

-- What about this one? (Recall that in Lean, `Nat.add`
-- recurses on the *second* argument: `n + zero = n` by
-- definition, and `n + (m + 1) = (n + m) + 1` by definition.)

--   theorem review₄ (n : Nat) : n + zero = n

-- (A) none

-- (B) `rewrite`

-- (C) `cases`

-- (D) both `rewrite` and `cases`

-- (E) can't be done with the tactics we've seen.

-- _Quiz:_

-- What about this?

--   theorem review₅ (n : Nat) : zero + n = n

-- (A) none

-- (B) `rewrite`

-- (C) `cases`

-- (D) both `rewrite` and `cases`

-- (E) can't be done with the tactics we've seen.

-- ### Exercise (1 star): succ_eq_add_one ⭐

-- One more warm-up exercise. Prove the following theorem,
-- using theorems from Basics:

theorem succ_eq_add_one (n : Nat) : succ n = n + one := by
  sorry

-- ## Proof by Induction

-- But the proof that it is also a neutral element on the
-- *left* gets stuck...

sf_expect_failure
  example (n : Nat) : zero + n = n := by
    rfl    -- doesn't work here!

-- Tactic `rfl` failed: The left-hand side
--   zero + n
-- is not definitionally equal to the right-hand side
--   n

-- n : Nat
-- ⊢ zero + n = n

-- And reasoning by cases using `cases` on `n` doesn't get us
-- much further: the branch of the case analysis where we
-- assume `n = zero` goes through just fine, but in the branch
-- where `n = n' + 1` for some `n'` we get stuck in exactly the
-- same way.

sf_expect_failure
  example (n : Nat) : zero + n = n := by
    cases n with
    | zero => /- n = zero -/
      rewrite [add_zero]
      rfl
      -- so far so good...
    | succ n' =>   /- n = succ n' -/
      _     -- ...but we're stuck on zero + n'

-- unsolved goals
-- case succ
-- n' : Nat
-- ⊢ zero + succ n' = succ n'

-- We need a bigger hammer: the *principle of induction* over
-- natural numbers...

-- - If `P(n)` is some proposition involving a natural number
--   `n`, and we want to show that `P` holds for *all* numbers,
--   we can reason like this:

-- - show that `P(zero)` holds

-- - show that, if `P(n')` holds, then so does `P(succ n')`

-- - conclude that `P(n)` holds for all `n`.

-- For example...

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

-- Let's try this one together:

theorem beq_self (n : Nat) : (n == n) = true := by
  sorry

-- Here's another related fact about addition, which we'll need
-- later. (The proof is left as an exercise.)

theorem add_comm (n m : Nat) :
    n + m = m + n := by
  sorry

theorem add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  sorry

-- Note to developers (Benjamin Pierce @bcpierce00):
--     `We need better typesetting for displays like the following ones:`

-- ### Tip: the `rw` tactic

-- As you've probably noticed, a common pattern in Lean proofs
-- is `rewrite [...]` followed by `rfl`. There is a tactic that
-- combines these two steps: `rw [...]` will automatically
-- close the goal if the rewrite makes the goal true by
-- definition. For example, instead of writing

--   rewrite [double_zero]; rfl

-- We could write this:

--   rw [double_zero]

-- If `rw` leaves a goal that looks definitionally true, try
-- adding `rfl` after it.

-- ### Exercise (2 stars): double_add ⭐⭐

-- Consider the following function, which doubles its argument:

def double (n : Nat) : Nat :=
  match n with
  | zero    => zero
  | succ n' => succ (succ (double n'))

theorem double_zero : double zero = zero := by rfl
theorem double_succ n : double (succ n) = succ (succ (double n)) := by rfl
attribute [irreducible] double

-- Use induction to prove this simple fact about `double`. Try
-- using `rw` instead of `rewrite`.

theorem double_add (n : Nat) : double n = n + n := by
  sorry

-- ## Proofs Within Proofs

-- New tactic: `have`.

theorem mult_zero_add' (n m : Nat) :
    ((zero + n) + zero) * m = n * m := by
  have h : (zero + n) + zero = n := by
    rw [zero_add, add_zero]
  rw [h]

sf_expect_failure
  example (n m p q : Nat) :
     (n + m) + (p + q) = (m + n) + (p + q) := by
    /-
      We just need to swap (n + m) for (m + n)... seems
      like add_comm should do the trick!
      But `rw [add_comm]` might rewrite the wrong `+`!
    -/
    rw [add_comm]

-- unsolved goals
-- n m p q : Nat
-- ⊢ p + q + (n + m) = m + n + (p + q)

-- To use `add_comm` at the point where we need it, we can
-- supply explicit arguments: `rw [add_comm n m]` tells Lean
-- exactly which `+` to rewrite. (We can also use `have` to
-- establish the specific equation we want, then rewrite with
-- it.)

theorem add_rearrange (n m p q : Nat) :
    (n + m) + (p + q) = (m + n) + (p + q) := by
  rw [add_comm n m]

-- ## Formal vs. Informal Proof

-- "Informal proofs are algorithms; formal proofs are code."

-- ### Exercise (2 stars): add_comm_informal (Advanced, manually graded) ⭐⭐

-- Translate your solution for `add_comm` into an informal
-- proof:

-- Theorem: Addition is commutative.

-- Proof:

-- ### Exercise (2 stars): beq_refl_informal ⭐⭐

-- Write an informal proof of the following theorem, using the
-- informal proof of `add_assoc` as a model. Don't just
-- paraphrase the Lean tactics into English!

-- Theorem: `(n == n) = true` for any `n`.

-- Proof:

-- ## More Exercises

-- ### Exercise (1 star): mul_one ⭐

theorem mul_one (p : Nat) :
    one * p = p := by
  sorry

-- ### Aside: Using Code Actions to Generate Match Skeletons

-- Lean's language server can suggest *code actions*, which are
-- small editor commands that modify the source code. In VS
-- Code, a lightbulb icon appears on the left when a code
-- action is available at your cursor. You can click the icon
-- or open the code action menu with `Ctrl + .` on
-- Windows/Linux or `Command + .` on macOS. For more
-- information, see the [Lean 4 VSCode extension
-- manual](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md#code-actions).

-- Some code actions can generate the explicit branches needed
-- for pattern matching. This is especially useful when working
-- with `match` expressions, or with tactics such as `cases`
-- and `induction`, which we saw in previous chapters.

-- You can use code actions freely to fill out `induction`,
-- `case`, and `match` branches in this book.

-- ### Exercise (2 stars): mul_two ⭐⭐

-- Tip: By default, `rewrite` and `rw` rewrite left to right,
-- i.e., they transform the hypothesis or goal being rewritten
-- from the form on the left side of the equality to the right
-- side. To rewrite from right to left, use `rewrite [← h]` or
-- `rw [← h]`, where `←` is entered as `\l` or `\<-`.

theorem mul_two (p : Nat) :
    two * p = p + p := by
  sorry

-- These exercises state facts that will be used later. We
-- don't need to work them in class.

-- ### Exercise (3 stars): mul_comm ⭐⭐⭐

-- Use `have` (or `rw` with explicit arguments) to help prove
-- `add_shuffle3`. You don't need to use induction.

theorem add_shuffle3 (n m p : Nat) :
    add (add n m) p = add (add n p) m := by
  sorry

theorem succ_mul (m n : Nat) :
    (succ n) * m = (n * m) + m := by
  sorry

-- Now prove commutativity of multiplication.

theorem mul_comm (m n : Nat) :
    m * n = n * m := by
  sorry

-- ### Exercise (3 stars): more_exercises ⭐⭐⭐

-- Take a piece of paper. For each of the following theorems,
-- first *think* about whether (a) it can be proved using only
-- simplification and rewriting, (b) it also requires case
-- analysis (`cases`), or (c) it also requires induction. Write
-- down your prediction. Then fill in the proof. (There is no
-- need to turn in your piece of paper; this is just to
-- encourage you to reflect before you hack!)

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

-- ### A New Tactic Combinator

-- New tactic combinator: `t₁ <;> t₂` runs `t₁`, then runs `t₂`
-- on every subgoal produced by `t₁`.

example (b : Bool) : (b || true) = true := by
  cases b <;> rfl

-- This is short for:

example (b : Bool) : (b || true) = true := by
  cases b with
  | false => rfl
  | true  => rfl

-- We can also chain `<;>`s.

example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl

-- ## Nat to Bin and Back to Nat

namespace NatToBin

-- Recall the `Bin` type we defined in Basics:

inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

-- Before you start working on the next exercise, replace the
-- stub definitions of `incr` and `binToNat`, below, with your
-- solution from Basics. That will make it possible for this
-- file to be graded on its own.

def incr (m : Bin) : Bin
  := sorry

theorem incr_z : incr .z = .b1 .z := sorry
theorem incr_b0 m : incr (.b0 m) = .b1 m := sorry
theorem incr_b1 m : incr (.b1 m) = .b0 (incr m) := sorry

def binToNat (m : Bin) : Nat
  := sorry

theorem binToNat_z : binToNat .z = zero := sorry
theorem binToNat_b0 m : binToNat (.b0 m) = mul (binToNat m) two := sorry
theorem binToNat_b1 m : binToNat (.b1 m) = add (mul (binToNat m) two) one := sorry

attribute [pp_nodot] Bin.b0 Bin.b1

-- In Basics, we did some unit testing of `binToNat`, but we
-- didn't prove its correctness. Now we'll do so.

-- ### Exercise (3 stars): binary_commute ⭐⭐⭐

-- Prove that the following diagram commutes — that is,
-- incrementing a binary number and then converting it to a
-- (unary) natural number yields the same result as first
-- converting it to a natural number and then incrementing:

--          incr Bin ----------------------> Bin
--              |                             |
--   binToNat   |                             |  binToNat
--              |                             |
--              v                             v
--             Nat ------------------------> Nat
--                         succ

-- If you want to change your previous definitions of `incr` or
-- `binToNat` to make the property easier to prove, feel free!

theorem bin_to_nat_pres_incr (b : Bin) :
    binToNat (incr b) = (binToNat b) + one := by
  sorry

-- ### Exercise (3 stars): nat_bin_nat ⭐⭐⭐

-- Write a function to convert natural numbers to binary
-- numbers. Also write some simplification lemmas for it.

def natToBin (n : Nat) : Bin := sorry

-- FILL IN HERE

-- Prove that, if we start with any `Nat`, convert it to `Bin`,
-- and convert it back, we get the same `Nat` which we started
-- with.

-- Hint: This proof should go through smoothly using the
-- previous exercise about `incr` as a lemma. If not, revisit
-- your definitions of the functions involved and consider
-- whether they are more complicated than necessary: the shape
-- of a proof by induction will match the recursive structure
-- of the program being verified, so make the recursions as
-- simple as possible.

theorem nat_bin_nat (n : Nat) :
    binToNat (natToBin n) = n := by
  sorry

-- ## Bin to Nat and Back to Bin (Advanced)

-- The opposite direction — starting with a `Bin`, converting
-- to `Nat`, then converting back to `Bin` — turns out to be
-- problematic. That is, the following "theorem" does not hold.

sf_expect_failure
  example (b : Bin) : natToBin (binToNat b) = b := by

-- Let's explore why this theorem fails and how to prove a
-- modified version of it. We'll start with some lemmas that
-- might seem unrelated but will turn out to be relevant.

-- ### Exercise (2 stars): double_bin (Advanced) ⭐⭐

-- Prove this lemma about `double`, which we defined earlier in
-- the chapter.

theorem double_incr (n : Nat) :
    double (succ n) = (double n) + two := by
  sorry

-- Now define a similar doubling function for `Bin`.

def doubleBin (b : Bin) : Bin := sorry

-- Fill in the characterizing lemmas for this definition below:

-- FILL IN HERE

-- Check that your function correctly doubles zero.

theorem double_bin_zero : doubleBin .z = .z := sorry

-- Prove this lemma, which corresponds to `double_incr`.

theorem double_incr_bin (b : Bin) :
    doubleBin (incr b) = incr (incr (doubleBin b)) := by
  sorry

-- Let's return to our desired theorem:

sf_expect_failure
  example (b : Bin) : natToBin (binToNat b) = b := by

-- The theorem fails because there are some `Bin` such that we
-- won't necessarily get back to the *original* `Bin`, but
-- instead to an "equivalent" `Bin`. (We deliberately leave
-- that notion undefined here for you to think about.)

-- Explain in a comment, below, why this failure occurs. Your
-- explanation will not be graded, but it's important that you
-- get it clear in your mind before going on to the next part.
-- If you're stuck on this, think about alternative
-- implementations of `doubleBin` that might have failed to
-- satisfy `double_bin_zero` yet otherwise seem correct.

-- To solve that problem, we can introduce a *normalization*
-- function that selects the simplest `Bin` out of all the
-- equivalent `Bin`. Then we can prove that the conversion from
-- `Bin` to `Nat` and back again produces that normalized,
-- simplest `Bin`.

-- ### Exercise (4 stars): bin_nat_bin (Advanced) ⭐⭐⭐⭐

-- Define `normalize`. You will need to keep its definition as
-- simple as possible for later proofs to go smoothly. Do not
-- use `binToNat` or `natToBin`, but do use `doubleBin`.

-- Hint: Structure the recursion such that it *always* reaches
-- the end of the `Bin` and *only* processes each bit once. Do
-- not try to "look ahead" at future bits.

def normalize (b : Bin) : Bin := sorry

-- Also specify the characterizing lemmas for this definition:

-- FILL IN HERE

-- It would be wise to do some `example` proofs to check that
-- your definition of `normalize` works the way you intend
-- before you proceed. They won't be graded, but do fill in a
-- few below.

-- FILL IN HERE

-- Now that we have defined all of our functions and their
-- relevant characterizing lemmas, we mark them irreducible as
-- usual. From here on out, our proofs about these definitions
-- should use `rewrite` or `rw`.

attribute [irreducible] normalize doubleBin natToBin incr binToNat

-- Finally, prove the main theorem. The inductive cases could
-- be a bit tricky.

-- Hint: Start by trying to prove the main statement, see where
-- you get stuck, and see if you can find a lemma — perhaps
-- requiring its own inductive proof — that will allow the main
-- proof to make progress. We have one lemma for the `b0` case
-- (which also makes use of `double_incr_bin`) and another for
-- the `b1` case.

-- FILL IN HERE

theorem bin_nat_bin (b : Bin) :
    natToBin (binToNat b) = normalize b := by
  sorry

end NatToBin
end NatPlayground.Nat


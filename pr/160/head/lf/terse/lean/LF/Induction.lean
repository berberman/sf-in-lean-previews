import LF.Basics

import LF.SFLCompat

-- # Induction: Proof by Induction

-- Note to developers (Jonathan Chan  @ionathanch):
--     [BCP: Old comment -- might be out of date?] A lot of the
--     proofs on the naturals rely on how operations on
--     naturals were defined in `Basics.lean`, but in the
--     stdlib they're slightly different (e.g. `sub` is defined
--     via `pred` rather than directly by recursion), and the
--     notations all go through typeclasses, which makes the
--     proofs a lot less direct (e.g. the existing `0 + n`
--     proof refers to `Nat.add_succ`). We should do one of the
--     following:
--
--     1. Not use `+`, `-`, `*` notation and instead use `add`,
--        `sub`, `mul` directly; or
--
--     2. Override stdlib notation with ones pointing to the
--        definitions in `Basics.lean`.

-- Note to developers (Harrison Goldstein  @hgoldstein95):
--     Option 1 is a very reasonable way to go about this if
--     we're attached to arithmetic being the way we teach
--     induction. My primary concern is that operators and type
--     classes are already so confusing that adding another
--     meaning of `+` is liable to throw someone way off. Is
--     there another context we can teach induction in that
--     also doesn't require a ton of background?

-- Note to developers (Jonathan Chan  @ionathanch):
--     `Basics.lean` now overrides the typeclasses for `-`,
--     `*`, and `^`, but not `+`, since that one is pervasive
--     throughout the stdlib and causes problems; I think this
--     works okay and isn't too confusing.
--
--     If we continue doing arithmetic proofs, this is a good
--     place to introduce equational reasoning via `calc`.

-- Note to developers (before next release):
--     `Readers might expect us to add eqn:H annotations to uses of
--     induction, but this changes the shape of the IH in a nasty way! :-(
--     We should at least comment.  (BCP: Is this still relevant in Lean?)
--
--     SOONER: We should also consider adding more examples to clarify
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

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `This section will need some tidying and rewriting...`

-- Lean will first need to compile `Basics.lean` so it can be
-- imported here -- detailed instructions are in the full
-- version of this chapter...

namespace NatPlayground.Nat

-- ## Review

-- _Quiz:_

-- To prove the following theorem, which tactics will we need
-- besides `intro` and `rfl`? (A) none, (B) `rewrite`, (C)
-- `cases`, (D) both `rewrite` and `cases`, or (E) can't be
-- done with the tactics we've seen.

--       theorem review1 : (true || false) = true

-- _Quiz:_

-- What about the next one?

--       theorem review2 : ∀ b, (true || b) = true

-- Which tactics do we need besides `intro` and `rfl`? (A) none
-- (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`,
-- or (E) can't be done with the tactics we've seen.

-- _Quiz:_

-- What if we change the order of the arguments of `||`?

--       theorem review3 : ∀ b, (b || true) = true

-- Which tactics do we need besides `intro` and `rfl`? (A) none
-- (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`,
-- or (E) can't be done with the tactics we've seen.

-- _Quiz:_

-- What about this one? (Recall that in Lean, `Nat.add`
-- recurses on the *second* argument: `n + zero = n` by
-- definition, and `n + (m + 1) = (n + m) + 1` by definition.)

--       theorem review4 : ∀ n : Nat, n + zero = n

-- (A) none, (B) `rewrite`, (C) `cases`, (D) both `rewrite` and
-- `cases`, or (E) can't be done with the tactics we've seen.

-- _Quiz:_

-- What about this?

--       theorem review5 : ∀ n : Nat, zero + n = n

-- (A) none, (B) `rewrite`, (C) `cases`, (D) both `rewrite` and
-- `cases`, or (E) can't be done with the tactics we've seen.

-- ### Exercise (1 star): succ_eq_add_one ⭐

-- Prove the following theorem, using theorems from Basics.

theorem succ_eq_add_one : ∀ n : Nat, succ n = n + one := by
  sorry

-- ### Proof by Induction

-- But the proof that it is also a neutral element on the
-- *left* gets stuck...

example : ∀ n : Nat, zero + n = n := by
  intro n
  -- `rfl` doesn't work here!
  sorry

-- And reasoning by cases using `cases n` doesn't get us much
-- further: the branch of the case analysis where we assume
-- `n = zero` goes through just fine, but in the branch where
-- `n = n' + 1` for some `n'` we get stuck in exactly the same
-- way.

example : ∀ n : Nat, zero + n = n := by
  intro n
  cases n with
  | zero => /- n = zero -/
    rewrite [add_zero]
    rfl
    -- so far so good...
  | succ n' =>   /- n = succ n' -/
    -- ...but we're stuck on zero + n'
    sorry

-- We need a bigger hammer: the *principle of induction* over
-- natural numbers...

-- - If `P(n)` is some proposition involving a natural number
--   `n`, and we want to show that `P` holds for *all* numbers,
--   we can reason like this:

-- - show that `P(zero)` holds

-- - show that, if `P(n')` holds, then so does `P(succ n')`

-- - conclude that `P(n)` holds for all `n`.

-- For example...

theorem zero_add : ∀ n : Nat, zero + n = n := by
  intro n
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

theorem beq_self : ∀ n : Nat,
    (n == n) = true := by
  sorry

-- Note to developers (Roger Burtonpatel  @rogerburtonpatel):
--     `We need to make sure this section below is true! It won't be once we switch
--          to the indexed style.`

-- Here's another related fact about addition, which we'll need
-- later. (The proof is left as an exercise.)

theorem add_comm (n m : Nat) :
    n + m = m + n := by
  sorry

theorem add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  sorry

-- ### Exercise (2 stars): double_plus ⭐⭐

-- Consider the following function, which doubles its argument:

-- Note to developers (NOW):
--     `Rule rewrite
--
--     BCP: What is "ASSUME HIDDEN"??
--     ASSUME HIDDEN`

def double (n : Nat) : Nat :=
  match n with
  | zero    => zero
  | succ n' => succ (succ (double n'))

theorem double_zero : double zero = zero := by rfl
theorem double_succ : ∀ n, double (succ n) = succ (succ (double n)) := by
  intro n; rfl

attribute [irreducible] double

-- Note to developers (Claude, NOW):
--     The `ASSUME HIDDEN` / `END ASSUME` region markers around
--     this exercise are unhandled: `ASSUME HIDDEN` got swept
--     into the developer note above, and this bare
--     `END ASSUME` line renders as stray book prose in **all
--     three** build products. (See BCP's "What is ASSUME
--     HIDDEN??" note above.) Either implement the marker or
--     delete both lines.

-- END ASSUME

-- Note to developers (Benjamin Pierce  @bcpierce00):
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

-- Using `rw` in your proofs is optional, but it will save you
-- time (and is better style).

-- If `rw` leaves a goal that looks definitionally true, try
-- adding `rfl` after it.

-- Use induction to prove this simple fact about `double`.
-- Experiment with using `rw` instead of `rewrite` as well.

theorem double_add (n : Nat) : double n = n + n := by
  sorry

-- ### Exercise (2 stars): beq_refl ⭐⭐

-- The following theorem relates the computational equality
-- `beq` on `Nat` with the definitional equality `=` on `Bool`.

theorem beq_refl (n : Nat) :
    (n == n) = true := by
  sorry

-- ## Proofs Within Proofs

-- New tactic: `have`.

theorem mult_zero_plus' (n m : Nat) :
    ((zero + n) + zero) * m = n * m := by
  have h : (zero + n) + zero = n := by
    rw [zero_add, add_zero]
  rw [h]

example (n m p q : Nat) :
   (n + m) + (p + q) = (m + n) + (p + q) := by
  /-
    We just need to swap (n + m) for (m + n)... seems
    like add_comm should do the trick!
    But `rw [add_comm]` might rewrite the wrong `+`!
  -/
  rw [add_comm]
  sorry

-- To use `add_comm` at the point where we need it, we can
-- supply explicit arguments: `rw [add_comm n m]` tells Lean
-- exactly which `+` to rewrite. (We can also use `have` to
-- establish the specific equation we want, then rewrite with
-- it.)

theorem plus_rearrange (n m p q : Nat) :
    (n + m) + (p + q) = (m + n) + (p + q) := by
  rw [add_comm n m]

-- ## Formal vs. Informal Proof

-- "Informal proofs are algorithms; formal proofs are code."

-- ## More Exercises

-- Tip: By default, `rewrite` and `rw` rewrite left to right,
-- i.e., they transform the hypothesis or goal being rewritten
-- from the form on the left side of the equality to the right
-- side. To rewrite from right to left, use `rewrite [← h]` or
-- `rw [← h]`, where `←` is entered as `\l` or `\<-`.

-- ### Exercise (1 star): mul_one ⭐

theorem mul_one (p : Nat) :
    one * p = p := by
  sorry

-- ### Exercise (2 stars): mul_two ⭐⭐

theorem mul_two (p : Nat) :
    two * p = p + p := by
  sorry

-- These exercises state facts that will be used in later
-- chapters. We don't need to work them in class.

-- ### Exercise (3 stars): mul_comm ⭐⭐⭐

-- Use `have` (or `rw` with explicit arguments) to help prove
-- `add_shuffle3`. You don't need to use induction yet.

-- Note: By default, `rewrite` and `rw` rewrite left-to-right.
-- To rewrite from right to left, use `rw [← h]`, where `←` is
-- typed as `\l` or `\<-`.

theorem add_shuffle3 : ∀ n m p : Nat,
    add (add n m) p = add (add n p) m := by
  sorry

-- Note to developers (Claude, NOW):
--     Rendering bug (all three build products look wrong).
--     This helper-lemma block wraps its **entire** contents in
--     the `-- SOLUTION`/`-- END SOLUTION` comment-marker
--     idiom, which the Verso HTML build does not process (only
--     the `solution!` tactic is handled). Result: in
--     **student** and **terse** the block renders empty with a
--     spurious `unexpected end of input` error and a doubled
--     `-- FILL IN HERE`; in **solutions** the lemma is shown
--     but the literal `-- SOLUTION` / `-- END SOLUTION`
--     comment lines leak into the displayed code. (The
--     generated `.lean` files are correct.) Fix by expressing
--     `succ_mul` with the `solution!` tactic instead of the
--     comment markers.

-- FILL IN HERE

-- Now prove commutativity of multiplication.

theorem mul_comm (m n : Nat) :
    m * n = n * m := by
  sorry

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `This comment is placed a bit awkwardly: In the terse version, we
--     usually skim past these exercises, but now we'll need to pause and look
--     at how <;> works...
--     TERSE`

-- New tactic combinator: `t₁ <;> t₂` runs `t₁`, then runs `t₂`
-- on every subgoal produced by `t₁`.

example (b : Bool) : (b || true) = true := by
  cases b <;> rfl

-- ### Exercise (3 stars): more_exercises ⭐⭐⭐

-- Take a piece of paper. For each of the following theorems,
-- first *think* about whether (a) it can be proved using only
-- simplification and rewriting, (b) it also requires case
-- analysis (`cases`), or (c) it also requires induction. Write
-- down your prediction. Then fill in the proof. (There is no
-- need to turn in your piece of paper; this is just to
-- encourage you to reflect before you hack!) Some of these
-- proofs can be shortened with `<;>` when several generated
-- subgoals have the same proof.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `Is that the main reason for introducing <;> here?  Seems weak if so.
--     Could we consider moving it later?`

theorem ble_refl (n : Nat) :
    ble n n = true := by
  sorry

theorem andb_false (b : Bool) :
    (b && false) = false := by
  sorry

theorem all3_spec (b c : Bool) :
    (b && c) || ((!b) || (!c)) = true := by
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

-- ### Nat to Bin and Back to Nat

-- ### Bin to Nat and Back to Bin (Advanced)

end NatPlayground.Nat


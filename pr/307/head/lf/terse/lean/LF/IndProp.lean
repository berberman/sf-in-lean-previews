import LF.Logic
import LF.CustomTactics

import SFLCompat

--  # IndProp: Inductively Defined Propositions

--  ## Inductively Defined Propositions

--  In the Logic chapter, we looked at several ways of
--  writing propositions, including conjunction,
--  disjunction, and existential quantification.

--  In this chapter, we bring yet another new tool into the
--  mix: *inductively defined propositions*.

--  To begin, some examples...

--  ### Example: The Collatz Conjecture

--  The *Collatz Conjecture* is a famous open problem in
--  number theory.

--  Its statement is quite simple. First, we define a
--  function `collatzStep` on numbers as follows:

def div2 (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | 1      => 0
  | n' + 2 => div2 n' + 1

def collatzStep (n : Nat) : Nat :=
  bif n.even then div2 n
  else (3 * n) + 1

--  Next, we look at what happens when we repeatedly apply
--  `collatzStep` to some given starting number. For
--  example, `collatzStep 12` is `6`, and `collatzStep 6` is
--  `3`, so by repeatedly applying `collatzStep` we get the
--  sequence `12, 6, 3, 10, 5, 16, 8, 4, 2, 1`.

--  Similarly, if we start with `19`, we get the longer
--  sequence
--  `19,
--  58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
--  4, 2, 1`.

--  Both of these sequences eventually reach `1`. The
--  question posed by Collatz was: Is the sequence starting
--  from *any* positive natural number guaranteed to reach
--  `1` eventually?

--  To formalize this question in Lean, we might try to
--  define a recursive *function* that calculates the total
--  number of steps that it takes for such a sequence to
--  reach `1`. You can write this definition in a standard
--  programming language, but it is rejected by Lean's
--  termination checker, since the argument to the recursive
--  call, `collatzStep n`, is not "obviously smaller" than
--  `n`.

sf_expect_failure_in
  def reaches1In (n : Nat) : Nat :=
    bif n == 1 then 0
    else 1 + reaches1In (collatzStep n)

--  Output:
--    fail to show termination for
--      reaches1In
--    with errors
--    failed to infer structural recursion:
--    Cannot use parameter n:
--      failed to eliminate recursive application
--        reaches1In (collatzStep n)
--
--
--    failed to prove termination, possible solutions:
--      - Use `have`-expressions to prove the remaining goals
--      - Use `termination_by` to specify a different well-founded relation
--      - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
--    n : Nat
--    ⊢ collatzStep n < n

--  Indeed, this isn't just a pointless limitation:
--  functions in Lean are required to be total, to ensure
--  logical consistency.

--  Moreover, we can't fix it by devising a more clever
--  termination checker: deciding whether this particular
--  function is total would be equivalent to settling the
--  Collatz conjecture!

--  Another idea could be to express the concept "eventually
--  reaches `1` in the Collatz sequence" as a *recursively
--  defined property* of numbers
--  `CollatzHoldsFor : Nat → Prop`. This is also rejected by
--  the termination checker. In principle, we could convince
--  Lean that `div2 n` is smaller than `n` by supplying an
--  appropriate proof. However, we still can't convince it
--  that `(3 * n) + 1` is smaller than `n`!

sf_expect_failure_in
  def CollatzHoldsFor (n : Nat) : Prop :=
    match n with
    | 0 => False
    | 1 => True
    | _ => bif n.even then CollatzHoldsFor (div2 n)
                     else CollatzHoldsFor ((3 * n) + 1)

--  Output:
--    fail to show termination for
--      CollatzHoldsFor
--    with errors
--    failed to infer structural recursion:
--    Cannot use parameter n:
--      failed to eliminate recursive application
--        CollatzHoldsFor (div2 n)
--
--
--    failed to prove termination, possible solutions:
--      - Use `have`-expressions to prove the remaining goals
--      - Use `termination_by` to specify a different well-founded relation
--      - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
--    n x✝ : Nat
--    ⊢ div2 n < x✝

--  Fortunately, there is another way to do it: We can
--  express the concept "reaches `1` eventually in the
--  Collatz sequence" as an *inductively defined property*
--  of numbers. Intuitively, this property is defined by a
--  set of rules:

--                  ─────────────────── (one)
--                   CollatzHoldsFor 1

--    n.even = true     CollatzHoldsFor (div2 n)
--    ─────────────────────────────────────────── (even)
--                   CollatzHoldsFor n

--    n.even = false    CollatzHoldsFor ((3 * n) + 1)
--    ─────────────────────────────────────────────── (odd)
--                   CollatzHoldsFor n

--  So there are three ways to prove that a number `n`
--  eventually reaches `1` in the Collatz sequence:

--  - `n` is `1`;
--  - `n` is even and `div2 n` eventually reaches `1`;
--  - `n` is odd and `(3 * n) + 1` eventually reaches `1`.

--  We can prove that a number reaches `1` by constructing a
--  (finite) derivation using these rules. For instance,
--  here is the derivation proving that `12` reaches `1`
--  (where we leave out the evenness/oddness premises):

--    ─────────────────────── (one)
--      CollatzHoldsFor 1
--    ─────────────────────── (even)
--      CollatzHoldsFor 2
--    ─────────────────────── (even)
--      CollatzHoldsFor 4
--    ─────────────────────── (even)
--      CollatzHoldsFor 8
--    ─────────────────────── (even)
--      CollatzHoldsFor 16
--    ─────────────────────── (odd)
--      CollatzHoldsFor 5
--    ─────────────────────── (even)
--      CollatzHoldsFor 10
--    ─────────────────────── (odd)
--      CollatzHoldsFor 3
--    ─────────────────────── (even)
--      CollatzHoldsFor 6
--    ─────────────────────── (even)
--      CollatzHoldsFor 12

--  Formally in Lean, the `CollatzHoldsFor` property is
--  *inductively defined*:

inductive CollatzHoldsFor : Nat → Prop where
  | one  : CollatzHoldsFor 1
  | even {n : Nat} (h₁ : n.even = true)
    (h₂ : CollatzHoldsFor (div2 n)) : CollatzHoldsFor n
  | odd  {n : Nat} (h₁ : n.even = false)
    (h₂ : CollatzHoldsFor ((3 * n) + 1)) : CollatzHoldsFor n

--  For particular numbers, we can now prove that the
--  Collatz sequence reaches `1` (we'll look more closely at
--  how it works a bit later in the chapter). Each step
--  applies a rule and discharges the boolean evenness
--  premise by `rfl`; the recursive premise is then reduced
--  by the kernel from `CollatzHoldsFor (div2 12)` to
--  `CollatzHoldsFor 6`, etc.

example : CollatzHoldsFor 12 := by
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.odd;   rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.odd;   rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.even;  rfl
  exact CollatzHoldsFor.one

--  The Collatz conjecture then states that the sequence
--  beginning from *any* positive number reaches `1`:

def Collatz := ∀ n : Nat, n ≠ 0 → CollatzHoldsFor n

--  If you succeed in proving this conjecture, you've got a
--  bright future as a number theorist! But don't spend too
--  long on it ─ it's been open since 1937.

--  ### Example: Binary Relation for Comparing Numbers

--  A binary *relation* on a set `α` has Lean type
--  `α → α → Prop`. This is a family of propositions
--  parameterized by two elements of `α` ─ i.e., a
--  proposition about pairs of elements of `α`.

--  For example, one familiar binary relation on `Nat` is
--  `Le : Nat → Nat → Prop`, the less-than-or-equal-to
--  relation, which can be inductively defined by the
--  following two rules:

--      ─────── (le_refl)
--      Le n n

--      Le n m
--    ──────────── (le_step)
--    Le n (m + 1)

namespace LePlayground

inductive Le : Nat → Nat → Prop where
  | refl {n : Nat}                : Le n n
  | step {n m : Nat} (h : Le n m) : Le n (m + 1)

scoped infix:50 (priority := high) " ≤ " => Le

example : 3 ≤ 5 := by
  apply Le.step; apply Le.step; exact Le.refl

end LePlayground

--  ### Example: Transitive Closure

--  Another example: The *transitive closure* of a relation
--  `r` is the smallest relation that contains `r` and that
--  is transitive. This can be defined by the following two
--  rules:

--                  r x y
--             ─────────────── (t_step)
--             TransGen r x y

--    TransGen r x y    TransGen r y z
--    ──────────────────────────────────── (t_trans)
--             TransGen r x z

--  In Lean this looks as follows:

inductive TransGen {α : Type} (r : α → α → Prop) : α → α → Prop where
  | step {x y : α} (h : r x y) : TransGen r x y
  | trans {x y z : α}
    (h₁ : TransGen r x y)
    (h₂ : TransGen r y z) :
    TransGen r x z

--  "Gen" is short for generated by — `TransGen r` means the
--  smallest transitive relation generated by `r`.

--  For example, suppose we define a "parent of" relation on
--  a group of people...

inductive Person : Type where
  | sage
  | cleo
  | ridley
  | moss

inductive ParentOf : Person → Person → Prop where
  | sage_cleo : ParentOf .sage .cleo
  | sage_ridley : ParentOf .sage .ridley
  | cleo_moss : ParentOf .cleo .moss

--  The `ParentOf` relation is not transitive, but we can
--  define an "ancestor of" relation as its transitive
--  closure:

def AncestorOf : Person → Person → Prop := TransGen ParentOf

--  Here is a derivation showing that `Person.sage` is an
--  ancestor of `moss`:

--     ——————————————————— (sage_cleo) ——————————————————— (cleo_moss)
--     ParentOf .sage .cleo            ParentOf .cleo .moss
--    ————————————————————— (step)    ————————————————————— (step)
--    AncestorOf .sage .cleo          AncestorOf .cleo .moss
--    ———————————————————————————————————————————————————— (trans)
--                    AncestorOf .sage .moss

example : AncestorOf .sage .moss := by
  apply TransGen.trans
  · apply TransGen.step; apply ParentOf.sage_cleo
  · apply TransGen.step; apply ParentOf.cleo_moss

--  ### Example: Reflexive and Transitive Closure

--  As another example, the *reflexive and transitive
--  closure* of a relation `r` is the smallest relation that
--  contains `r` and that is reflexive and transitive. This
--  can be defined by the following three rules (where we
--  added a reflexivity rule to `TransGen`):

--                       r x y
--             ——————————————————————— (step)
--               ReflTransGen r x y

--             ——————————————————————— (refl)
--               ReflTransGen r x x

--       ReflTransGen r x y    ReflTransGen r y z
--    —————————————————————————————————————————————— (trans)
--               ReflTransGen r x z

inductive ReflTransGen {α : Type} (r : α → α → Prop) : α → α → Prop where
  | step {x y : α} (h : r x y) : ReflTransGen r x y
  | refl {x : α} : ReflTransGen r x x
  | trans {x y z : α}
    (h₁ : ReflTransGen r x y)
    (h₂ : ReflTransGen r y z) :
    ReflTransGen r x z

--  For instance, this enables an equivalent definition of
--  the Collatz conjecture. First we define a binary
--  relation corresponding to the "Collatz step function"
--  `collatzStep`:

def CollatzStep (n m : Nat) : Prop := collatzStep n = m

--  This Collatz step relation can be used in conjunction
--  with the reflexive and transitive closure operation to
--  define a *Collatz multi-step* relation, expressing that
--  a number `n` reaches another number `m` in zero or more
--  Collatz steps:

def CollatzStepMulti (n m : Nat) : Prop := ReflTransGen CollatzStep n m
def Collatz' : Prop := ∀ (n : Nat), n ≠ 0 → CollatzStepMulti n 1

--  ### Example: Permutations

--  The familiar mathematical concept of *permutation* also
--  has an elegant formulation as an inductive relation. For
--  simplicity, let's focus on permutations of lists with
--  exactly three elements.

--  We can define such permutations by the following rules:

--       ───────────────────────── (swap12)
--       Perm3 [a, b, c] [b, a, c]

--       ───────────────────────── (swap23)
--       Perm3 [a, b, c] [a, c, b]

--    Perm3 l₁ l₂       Perm3 l₂ l₃
--    ───────────────────────────── (trans)
--             Perm3 l₁ l₃

--  For instance we can derive `Perm3 [1, 2, 3] [3, 2, 1]`
--  as follows:

--    ───────────────────────── (swap12)  ─────────────────────── (swap23)
--    Perm3 [1, 2, 3] [2, 1, 3]            Perm3 [2, 1, 3] [2, 3, 1]
--    ─────────────────────────────────────────────────────────────────(trans)    ───────────────────── (swap12)
--    Perm3 [1, 2, 3] [2, 3, 1]                                                    Perm3 [2, 3, 1] [3, 2, 1]
--    ───────────────────────────────────────────────────────────────────────────────────────────────────────── (trans)
--    Perm3 [1, 2, 3] [3, 2, 1]

--  In Lean, we can define `Perm3` as follows:

inductive Perm3 {α : Type} : List α → List α → Prop where
  | swap12 {x y z : α} : Perm3 [x, y, z] [y, x, z]
  | swap23 {x y z : α} : Perm3 [x, y, z] [x, z, y]
  | trans {l₁ l₂ l₃ : List α}
    (h₁₂ : Perm3 l₁ l₂)
    (h₂₃ : Perm3 l₂ l₃) :
    Perm3 l₁ l₃

--  ### Example: Evenness (yet again)

--  We've already seen two ways of stating a proposition
--  that a number `n` is even: We can say

--  (1) `Nat.even n = true` (using the recursive boolean
--  function `Nat.even`), or

--  (2) `∃ k, n = Nat.double k` (using an existential
--  quantifier).

--  A third possibility, which we'll use as a simple running
--  example in this chapter, is to say that a number is even
--  if we can *establish* its evenness from the following
--  two rules:

--      ────────── (zero)
--        Even 0

--        Even n
--    —————————————— (succ_succ)
--      Even (n + 2)

--  To illustrate how this new definition of evenness works,
--  let's imagine using it to show that `4` is even:

--                     ──────── (zero)
--                      Even 0
--              ─────────────────────── (succ_succ)
--              Even (.succ (.succ 0))
--    ────────────────────────────────────────────── (succ_succ)
--    Even (.succ (.succ (.succ (.succ 0))))

--  We can translate the informal definition of evenness
--  from above into a formal `inductive` declaration, where
--  each "way that a number can be even" corresponds to a
--  separate constructor:

inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ {n : Nat} (h : Even n) : Even (n + 2)

--  There are both similarities and a few differences
--  between inductive *properties* like `Even` and the
--  inductive *types* like `Nat` or `List` that we have been
--  using throughout the course:

sf_expect_failure_in
  inductive List (α : Type) : Type where
    | nil                       : List α
    | cons (x : α) (l : List α) : List α

--  The most important difference is that the constructors
--  of `Even`, `Even.zero` and `Even.succ_succ`, yield
--  different types (`Even 0` and `Even (n + 2)`), whereas
--  the `List` constructors both build `List α` values.

--  We can think of the inductive definition of `Even` as
--  defining a Lean property `Even : Nat → Prop`, together
--  with two "evidence constructors":

#check (Even)
#check Even.zero
#check Even.succ_succ

--  Output:
--    Even : Nat → Prop

--  Output:
--    Even.zero : Even 0

--  Output:
--    Even.succ_succ {n : Nat} (h : Even n) : Even (n + 2)

--  These evidence constructors can be thought of as
--  "primitive evidence of evenness", and they can be used
--  later on just like proven theorems. In particular, we
--  can use Lean's `apply` and `exact` tactics with the
--  constructor names to obtain evidence for `Even` of
--  particular numbers...

namespace Even

example : Even 4 := by
  apply succ_succ; apply succ_succ; exact zero

--  ... or we can use function application syntax to combine
--  several constructors:

example : Even 4 := by
  exact succ_succ (succ_succ zero)

--  ... or we can also use the `constructor` tactic we saw
--  earlier to select the appropriate inductive constructor:

example : Even 4 := by
  constructor; constructor; constructor

--  In this way, we can also prove theorems that have
--  hypotheses involving `Even`.

theorem plus4 (n : Nat) (h : Even n) : Even (4 + n) := by
  rw [Nat.add_comm]
  exact (succ_succ (succ_succ h))

end Even

--  ### Constructing Evidence for Permutations

--  Similarly we can apply the evidence constructors to
--  obtain evidence of `Perm3 [1, 2, 3] [3, 2, 1]`:

namespace Perm3

theorem rev : Perm3 [1, 2, 3] [3, 2, 1] := by
  apply trans (l₂:= [2, 3, 1])
  · apply trans (l₂ := [2, 1, 3])
    · apply swap12
    · apply swap23
  · apply swap12

--  And again we can equivalently use function application
--  syntax to combine several constructors. (Note that the
--  Lean type checker can infer not only types, but also
--  `Nat`s and `List`s, when they are clear from the
--  context.)

theorem rev' : Perm3 [1, 2, 3] [3, 2, 1] := by
  exact (trans (trans swap12 swap23) swap12)

--  So the informal derivation trees we drew above are not
--  too far from what's happening formally. Formally we're
--  using the evidence constructors to build *evidence
--  trees*, similar to the finite trees we built using the
--  constructors of data types such as `Nat`, `List`, binary
--  trees, etc.

end Perm3

--  ## Using Evidence in Proofs

--  Besides *constructing* evidence that numbers are even,
--  we can also *destruct* such evidence, reasoning about
--  how it could have been built.

--  Defining `Even` with an `inductive` declaration tells
--  Lean not only that the constructors `Even.zero` and
--  `Even.succ_succ` are valid ways to build evidence that
--  some number is `Even`, but also that these two
--  constructors are the *only* ways to build evidence that
--  numbers are `Even`.

--  In other words, if someone gives us evidence `e` for the
--  proposition `Even n`, then we know that `e` must be one
--  of two things:

--  - `e = Even.zero` and `n = 0`, or

--  - `e = Even.succ_succ n' e'` and `n = n' + 2`, where
--    `e'` is evidence for `Even n'`.

--  This suggests that it should be possible to do *case
--  analysis* and even *induction* on evidence of
--  evenness...

--  ### Destructing and Inverting Evidence

--  We can prove our characterization of evidence for
--  `Even n`, using `cases`.

theorem Even.even_inversion (n : Nat) (h : Even n) :
    (n = 0) ∨ ∃ n', n = n' + 2 ∧ Even n' := by
  cases h with
  | zero => left; rfl
  | @succ_succ n h => right; exists n

--  Facts like this are often called "inversion lemmas"
--  because they allow us to "invert" some given information
--  to reason about all the different ways it could have
--  been derived.

--  _Quiz:_

--  Which tactics are needed to prove this goal?

--    ∀ (n : Nat), Ev n → n = 1 → true = false

--  (A) `cases` (B) `contradiction` (C) Both `cases` and
--  `contradiction` (D) these tactics are not sufficient to
--  solve the goal.

--  We can use the inversion lemma that we proved above to
--  help structure proofs:

theorem Even.succ_succ_even (n : Nat) (h : Even (n + 2)) : Even n := by
  apply even_inversion at h
  obtain ⟨⟨⟩⟩ | ⟨n', ⟨h₁,  h₂⟩⟩ := h
  injections h₁ heq
  subst heq
  exact h₂

--  We've provided a handy tactic called `inversion` that
--  does the work of our inversion lemma and more besides.

example (n : Nat) (h : Even (n + 2)) : Even n := by
  inversion h; assumption

--  Recall that equality (`Eq`) is itself an inductively
--  defined proposition, so `inversion` can also be used on
--  equality propositions.

--  We can use `inversion` to re-prove some theorems from
--  Tactics.

example (n m o : Nat) (h : [n, m] = [o, o]) : [n] = [m] := by
  inversion h; rfl

example (n : Nat) (h : n + 1 = 0) : 2 + 2 = 5 := by
  inversion h

--  For the inductively defined propositions we use,
--  `inversion` behaves much like `cases`: it performs case
--  analysis on the constructors of the hypothesis's
--  inductive type. However, when the case analysis on an
--  indexed proposition gives *unsolvable* equations between
--  its indices, `cases` itself fails, whereas `inversion`
--  leaves such equations in the context.

--  For example, `cases` would immediately fail on `h`:

sf_expect_failure_in
  example (n : Nat) (h : Even (n * n)) :
    n * n = 0 ∨ ∃ m, n * n = m + 2 := by
    cases h

--  Output:
--    Dependent elimination failed: Failed to solve equation
--      n.mul n = 0

--  `inversion` instead leaves the equations in the context,
--  where we can use them directly:

example (n : Nat) (h : Even (n * n)) :
  n * n = 0 ∨ ∃ m, n * n = m + 2 := by
  inversion h with
  | zero => left; assumption
  | succ_succ m' _ _ _ => right; exists m'

--  _Quiz:_

--  Which tactics are needed to prove this goal, in addition
--  to `apply` or `exact`?

--    ∀ n, Even (2 + n) → Even n

--  (A) `inversion` (B) `inversion`, `injections` (C)
--  `inversion`, `rw [Nat.add_comm]` (D) `inversion`,
--  `rw [Nat.add_comm]`, `injections`

--  Let's try to show that our new notion of evenness
--  implies our earlier notion (the one based on
--  `Nat.double`).

sf_expect_failure_in
  example (n : Nat) (h : Even n) : Nat.Even n := by
    /- We could try to proceed by case analysis or induction on `n`.  But
        since `Even` is mentioned in a premise, this strategy seems
        unpromising, because (as we've noted before) the induction
        hypothesis will talk about `n-1` (which is _not_ even!).  Thus, it
        seems better to first try `inversion` on the evidence for `Even`.
        Indeed, the first case can be solved trivially. -/
    inversion h with
    | zero => exists 0
    | succ_succ n' h' =>
      /- Unfortunately, the second case is harder.  We need to show
      `∃ n₀, n' + 2 = double n₀`, but the only available assumption is
      `h'`, which states that `Even n'` holds.
      In other words, what we need here is precisely the result we
      are trying to prove, but applied to the smaller evidence `h'`.
      -/

--  ### Induction on Evidence

--  If this story feels familiar, it is no coincidence: We
--  encountered similar problems in the Induction chapter,
--  when trying to use case analysis to prove results that
--  required induction. And once again the solution is...
--  induction!

--  Let's try proving that lemma again:

theorem even_even (n : Nat) (h : Even n) : Nat.Even n := by
  induction h with
  | zero => exists 0 -- (`0 = double 0` is closed by `exists`'s final `rfl`)
  | succ_succ h' ih =>
    let ⟨k, hk⟩ := ih
    exists k + 1; rw [Nat.double_succ, hk]


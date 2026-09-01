import LF.Logic
import LF.CustomTactics

import SFLCompat

--  # IndProp: Inductively Defined Propositions

--  ## Inductively Defined Propositions

--  In the Logic chapter, we looked at several ways of
--  writing propositions, including conjunction,
--  disjunction, and existential quantification.
--
--  In this chapter, we bring yet another new tool into the
--  mix: *inductively defined propositions*.
--
--  To begin, some examples...

--  ### Example: The Collatz Conjecture

--  The *Collatz Conjecture* is a famous open problem in
--  number theory.
--
--  Its statement is quite simple. First, we define a
--  function `csf` on numbers, as follows (where `csf`
--  stands for "Collatz step function"):

def div2 (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | 1      => 0
  | n' + 2 => div2 n' + 1

def csf (n : Nat) : Nat :=
  bif n.even then div2 n
  else (3 * n) + 1

--  Next, we look at what happens when we repeatedly apply
--  `csf` to some given starting number. For example,
--  `csf 12` is `6`, and `csf 6` is `3`, so by repeatedly
--  applying `csf` we get the sequence
--  `12, 6, 3, 10, 5, 16, 8, 4, 2, 1`.
--
--  Similarly, if we start with `19`, we get the longer
--  sequence
--  `19,
--  58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
--  4, 2, 1`.
--
--  Both of these sequences eventually reach `1`. The
--  question posed by Collatz was: Is the sequence starting
--  from *any* positive natural number guaranteed to reach
--  `1` eventually?
--
--  To formalize this question in Lean, we might try to
--  define a recursive *function* that calculates the total
--  number of steps that it takes for such a sequence to
--  reach `1`. You can write this definition in a standard
--  programming language, but it is rejected by Lean's
--  termination checker, since the argument to the recursive
--  call, `csf n`, is not "obviously smaller" than `n`.

sf_expect_failure_in
  def reaches1In (n : Nat) : Nat :=
    bif n == 1 then 0
    else 1 + reaches1In (csf n)

--  Output:
--    fail to show termination for
--      reaches1In
--    with errors
--    failed to infer structural recursion:
--    Cannot use parameter n:
--      failed to eliminate recursive application
--        reaches1In (csf n)
--
--
--    failed to prove termination, possible solutions:
--      - Use `have`-expressions to prove the remaining goals
--      - Use `termination_by` to specify a different well-founded relation
--      - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
--    n : Nat
--    ⊢ csf n < n

--  Indeed, this isn't just a pointless limitation:
--  functions in Lean are required to be total, to ensure
--  logical consistency.
--
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
--
--                    ─────────────────── (chf_one)
--                     CollatzHoldsFor 1
--
--      even n = true     CollatzHoldsFor (div2 n)
--      ─────────────────────────────────────────── (chf_even)
--                     CollatzHoldsFor n
--
--      even n = false    CollatzHoldsFor ((3 * n) + 1)
--      ─────────────────────────────────────────────── (chf_odd)
--                     CollatzHoldsFor n
--
--  So there are three ways to prove that a number `n`
--  eventually reaches `1` in the Collatz sequence:
--
--  - `n` is `1`;
--  - `n` is even and `div2 n` eventually reaches `1`;
--  - `n` is odd and `(3 * n) + 1` eventually reaches `1`.

--  We can prove that a number reaches `1` by constructing a
--  (finite) derivation using these rules. For instance,
--  here is the derivation proving that `12` reaches `1`
--  (where we leave out the evenness/oddness premises):
--
--      ─────────────────────── (chf_one)
--        CollatzHoldsFor 1
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 2
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 4
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 8
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 16
--      ─────────────────────── (chf_odd)
--        CollatzHoldsFor 5
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 10
--      ─────────────────────── (chf_odd)
--        CollatzHoldsFor 3
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 6
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 12

--  Formally in Lean, the `CollatzHoldsFor` property is
--  *inductively defined*:

inductive CollatzHoldsFor : Nat → Prop where
  | chf_one  : CollatzHoldsFor 1
  | chf_even {n : Nat} (h₁ : n.even = true)
    (h₂ : CollatzHoldsFor (div2 n)) : CollatzHoldsFor n
  | chf_odd  {n : Nat} (h₁ : n.even = false)
    (h₂ : CollatzHoldsFor ((3 * n) + 1)) : CollatzHoldsFor n

--  For particular numbers, we can now prove that the
--  Collatz sequence reaches `1` (we'll look more closely at
--  how it works a bit later in the chapter). Each step
--  applies a rule and discharges the boolean evenness
--  premise by `rfl`; the recursive premise is then reduced
--  by the kernel from `CollatzHoldsFor (div2 12)` to
--  `CollatzHoldsFor 6`, etc.

example : CollatzHoldsFor 12 := by
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_odd;   rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_odd;   rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  exact CollatzHoldsFor.chf_one

--  The Collatz conjecture then states that the sequence
--  beginning from *any* positive number reaches `1`:

def Collatz := ∀ n, n ≠ 0 → CollatzHoldsFor n

--  If you succeed in proving this conjecture, you've got a
--  bright future as a number theorist! But don't spend too
--  long on it ─ it's been open since 1937.

--  ### Example: Binary Relation for Comparing Numbers

--  A binary *relation* on a set `α` has Lean type
--  `α → α → Prop`. This is a family of propositions
--  parameterized by two elements of `α` ─ i.e., a
--  proposition about pairs of elements of `α`.
--
--  For example, one familiar binary relation on `Nat` is
--  `Le : Nat → Nat → Prop`, the less-than-or-equal-to
--  relation, which can be inductively defined by the
--  following two rules:
--
--        ─────── (le_refl)
--        Le n n
--
--        Le n m
--      ──────────── (le_step)
--      Le n (m + 1)

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
--  `R` is the smallest relation that contains `R` and that
--  is transitive. This can be defined by the following two
--  rules:
--
--                    R x y
--               ─────────────── (t_step)
--               ClosTrans R x y
--
--      ClosTrans R x y    ClosTrans R y z
--      ──────────────────────────────────── (t_trans)
--               ClosTrans R x z
--
--  In Lean this looks as follows:

inductive ClosTrans {α : Type} (R : α → α → Prop) : α → α → Prop where
  | t_step {x y : α} (h : R x y) : ClosTrans R x y
  | t_trans {x y z : α}
    (h₁ : ClosTrans R x y)
    (h₂ : ClosTrans R y z) :
    ClosTrans R x z

--  For example, suppose we define a "parent of" relation on
--  a group of people...

inductive Person : Type where
  | sage
  | cleo
  | ridley
  | moss

inductive ParentOf : Person → Person → Prop where
  | po_SC : ParentOf .sage .cleo
  | po_SR : ParentOf .sage .ridley
  | po_CM : ParentOf .cleo .moss

--  The `ParentOf` relation is not transitive, but we can
--  define an "ancestor of" relation as its transitive
--  closure:

def AncestorOf : Person → Person → Prop := ClosTrans ParentOf

--  Here is a derivation showing that `sage` is an ancestor
--  of `moss`:
--
--       ——————————————————— (po_SC)     ——————————————————— (po_CM)
--       ParentOf .sage .cleo            ParentOf .cleo .moss
--      ————————————————————— (t_step)  ————————————————————— (t_step)
--      AncestorOf .sage .cleo          AncestorOf .cleo .moss
--      ———————————————————————————————————————————————————— (t_trans)
--                      AncestorOf .sage .moss

example : AncestorOf .sage .moss := by
  apply ClosTrans.t_trans
  . apply ClosTrans.t_step; apply ParentOf.po_SC
  . apply ClosTrans.t_step; apply ParentOf.po_CM

--  ### Example: Reflexive and Transitive Closure

--  As another example, the *reflexive and transitive
--  closure* of a relation `R` is the smallest relation that
--  contains `R` and that is reflexive and transitive. This
--  can be defined by the following three rules (where we
--  added a reflexivity rule to `ClosTrans`):
--
--                         R x y
--               ——————————————————————— (rt_step)
--                 ClosReflTrans R x y
--
--               ——————————————————————— (rt_refl)
--                 ClosReflTrans R x x
--
--         ClosReflTrans R x y    ClosReflTrans R y z
--      —————————————————————————————————————————————— (rt_trans)
--                 ClosReflTrans R x z

inductive ClosReflTrans {α : Type} (R : α → α → Prop) : α → α → Prop where
  | rt_step {x y : α} (h : R x y) : ClosReflTrans R x y
  | rt_refl {x : α} : ClosReflTrans R x x
  | rt_trans {x y z : α}
    (h₁ : ClosReflTrans R x y)
    (h₂ : ClosReflTrans R y z) :
    ClosReflTrans R x z

--  For instance, this enables an equivalent definition of
--  the Collatz conjecture. First we define a binary
--  relation corresponding to the "Collatz step function"
--  `csf`:

def CS (n m : Nat) : Prop := csf n = m

--  This Collatz step relation can be used in conjunction
--  with the reflexive and transitive closure operation to
--  define a *Collatz multi-step* (`CMS`) relation,
--  expressing that a number `n` reaches another number `m`
--  in zero or more Collatz steps:

def CMS (n m : Nat) : Prop := ClosReflTrans CS n m
def Collatz' : Prop := ∀ (n : Nat), n ≠ 0 → CMS n 1

--  ### Example: Permutations

--  The familiar mathematical concept of *permutation* also
--  has an elegant formulation as an inductive relation. For
--  simplicity, let's focus on permutations of lists with
--  exactly three elements.
--
--  We can define such permutations by the following rules:
--
--         ───────────────────────── (perm3_swap12)
--         Perm3 [a, b, c] [b, a, c]
--
--         ───────────────────────── (perm3_swap23)
--         Perm3 [a, b, c] [a, c, b]
--
--      Perm3 l₁ l₂       Perm3 l₂ l₃
--      ───────────────────────────── (perm3_trans)
--               Perm3 l₁ l₃
--
--  For instance we can derive `Perm3 [1, 2, 3] [3, 2, 1]`
--  as follows:
--
--      ───────────────────────── (perm3_swap12)   ───────────────────────── (perm3_swap23)
--      Perm3 [1, 2, 3] [2, 1, 3]                  Perm3 [2, 1, 3] [2, 3, 1]
--      ──────────────────────────────────────────────────────────────────── (perm3_trans)   ───────────────────────── (perm3_swap12)
--      Perm3 [1, 2, 3] [2, 3, 1]                                                            Perm3 [2, 3, 1] [3, 2, 1]
--      ────────────────────────────────────────────────────────────────────────────────────────────────────────────── (perm3_trans)
--      Perm3 [1, 2, 3] [3, 2, 1]

--  In Lean, we can define `Perm3` as follows:

inductive Perm3 {α : Type} : List α → List α → Prop where
  | perm3_swap12 {x y z : α} : Perm3 [x, y, z] [y, x, z]
  | perm3_swap23 {x y z : α} : Perm3 [x, y, z] [x, z, y]
  | perm3_trans {l₁ l₂ l₃ : List α}
    (h₁₂ : Perm3 l₁ l₂)
    (h₂₃ : Perm3 l₂ l₃) :
    Perm3 l₁ l₃

--  ### Example: Evenness (yet again)

--  We've already seen two ways of stating a proposition
--  that a number `n` is even: We can say
--
--  (1) `Nat.even n = true` (using the recursive boolean
--  function `Nat.even`), or
--
--  (2) `∃ k, n = Nat.double k` (using an existential
--  quantifier).

--  A third possibility, which we'll use as a simple running
--  example in this chapter, is to say that a number is even
--  if we can *establish* its evenness from the following
--  two rules:
--
--          ———— (ev_0)
--          Ev 0
--
--          Ev n
--      —————————————— (ev_succ_succ)
--        Ev (n + 2)
--
--  To illustrate how this new definition of evenness works,
--  let's imagine using it to show that `4` is even:
--
--                    ———— (ev_0)
--                    Ev 0
--             ———————————————————— (ev_succ_succ)
--             Ev (.succ (.succ 0))
--      ——————————————————————————————————— (ev_succ_succ)
--      Ev (.succ (.succ (.succ (.succ 0))))

--  We can translate the informal definition of evenness
--  from above into a formal `inductive` declaration, where
--  each "way that a number can be even" corresponds to a
--  separate constructor:

inductive Ev : Nat → Prop where
  | ev_0                              : Ev 0
  | ev_succ_succ {n : Nat} (h : Ev n) : Ev (n + 2)

--  There are both similarities and a few differences
--  between inductive *properties* like `Ev` and the
--  inductive *types* like `Nat` or `List` that we have been
--  using throughout the course:

sf_expect_failure_in
  inductive List (α : Type) : Type where
    | nil                       : List α
    | cons (x : α) (l : List α) : List α

--  The most important difference is that the constructors
--  of `Ev`, `Ev.ev_0` and `Ev.ev_succ_succ`, yield
--  different types (`Ev 0` and `Ev (n + 2)`), whereas the
--  `List` constructors both build `List α` values.

--  We can think of the inductive definition of `Ev` as
--  defining a Lean property `Ev : Nat → Prop`, together
--  with two "evidence constructors":

#check Ev.ev_0         -- Ev 0
#check Ev.ev_succ_succ -- ∀ (n : Nat) (h : Ev n) : Ev (n + 2)

--  These evidence constructors can be thought of as
--  "primitive evidence of evenness", and they can be used
--  later on just like proven theorems. In particular, we
--  can use Lean's `apply` and `exact` tactics with the
--  constructor names to obtain evidence for `Ev` of
--  particular numbers...

namespace Ev

example : Ev 4 := by
  apply ev_succ_succ; apply ev_succ_succ; exact ev_0

--  ... or we can use function application syntax to combine
--  several constructors:

example : Ev 4 := by
  exact ev_succ_succ (ev_succ_succ ev_0)

--  ... or we can also use the `constructor` tactic we saw
--  earlier to select the appropriate inductive constructor:

example : Ev 4 := by
  constructor; constructor; constructor

--  In this way, we can also prove theorems that have
--  hypotheses involving `Ev`.

theorem plus4 (n : Nat) (h : Ev n) : Ev (4 + n) := by
  rw [Nat.add_comm]
  exact (ev_succ_succ (ev_succ_succ h))

end Ev

--  ### Constructing Evidence for Permutations

--  Similarly we can apply the evidence constructors to
--  obtain evidence of `Perm3 [1, 2, 3] [3, 2, 1]`:

namespace Perm3

theorem rev : Perm3 [1, 2, 3] [3, 2, 1] := by
  apply perm3_trans (l₂:= [2, 3, 1])
  . apply perm3_trans (l₂ := [2, 1, 3])
    . apply perm3_swap12
    . apply perm3_swap23
  . apply perm3_swap12

--  And again we can equivalently use function application
--  syntax to combine several constructors. (Note that the
--  Lean type checker can infer not only types, but also
--  `Nat`s and `List`s, when they are clear from the
--  context.)

theorem rev' : Perm3 [1, 2, 3] [3, 2, 1] := by
  exact (perm3_trans
          (perm3_trans perm3_swap12 perm3_swap23)
          perm3_swap12)

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
--
--  Defining `Ev` with an `inductive` declaration tells Lean
--  not only that the constructors `Ev.ev_0` and
--  `Ev.ev_succ_succ` are valid ways to build evidence that
--  some number is `Ev`, but also that these two
--  constructors are the *only* ways to build evidence that
--  numbers are `Ev`.

--  In other words, if someone gives us evidence `e` for the
--  proposition `Ev n`, then we know that `e` must be one of
--  two things:
--
--  - `e = ev_0` and `n = 0`, or
--
--  - `e = ev_succ_succ n' e'` and `n = n' + 2`, where `e'`
--    is evidence for `Ev n'`.

--  This suggests that it should be possible to do *case
--  analysis* and even *induction* on evidence of
--  evenness...

--  ### Destructing and Inverting Evidence

--  We can prove our characterization of evidence for
--  `Ev n`, using `cases`.

theorem ev_inversion (n : Nat) (h : Ev n) :
    (n = 0) ∨ ∃ n', n = n' + 2 ∧ Ev n' := by
  cases h with
  | ev_0 => left; rfl
  | @ev_succ_succ n h => right; exists n

--  Facts like this are often called "inversion lemmas"
--  because they allow us to "invert" some given information
--  to reason about all the different ways it could have
--  been derived.

--   ----------------------------------------

--  _Quiz:_

--  Which tactics are needed to prove this goal?
--
--      ∀ (n : Nat), Ev n → n = 1 → true = false
--
--  (A) `cases` (B) `contradiction` (C) Both `cases` and
--  `contradiction` (D) these tactics are not sufficient to
--  solve the goal.

--   ----------------------------------------

--  We can use the inversion lemma that we proved above to
--  help structure proofs:

theorem ev_succ_succ_ev (n : Nat) (h : Ev (n + 2)) : Ev n := by
  apply ev_inversion at h
  obtain ⟨⟨⟩⟩ | ⟨n', ⟨h₁,  h₂⟩⟩ := h
  injections h₁ heq
  subst heq
  exact h₂

--  We've provided a handy tactic called `inversion` that
--  does the work of our inversion lemma and more besides.

theorem ev_succ_succ_ev' (n : Nat) (h : Ev (n + 2)) : Ev n := by
  inversion h; assumption

--  We can use `inversion` to re-prove some theorems from
--  Tactics.
--
--  Note that `inversion` also works on equality
--  propositions.

theorem inversion_ex1 (n m o : Nat) (h : [n, m] = [o, o]) : [n] = [m] := by
  inversion h; rfl

theorem inversion_ex2 n (h : n + 1 = 0) : 2 + 2 = 5 := by
  inversion h

--  The `inversion` tactic works on any `h : p` where `p` is
--  defined inductively:
--
--  - For each constructor of `p`, make a subgoal where `h`
--    is constrained by the form of this constructor.
--
--  - Discard contradictory subgoals (such as `ev_0` above).
--
--  - Generate auxiliary equalities (as with `ev_succ_succ`
--    above).

--   ----------------------------------------

--  _Quiz:_

--  Which tactics are needed to prove this goal, in addition
--  to `apply` or `exact`?
--
--      ∀ n, Ev (2 + n) → Ev n
--
--  (A) `inversion` (B) `inversion`, `injections` (C)
--  `inversion`, `rw [Nat.add_comm]` (D) `inversion`,
--  `rw [Nat.add_comm]`, `injections`

--   ----------------------------------------

--  Let's try to show that our new notion of evenness
--  implies our earlier notion (the one based on
--  `Nat.double`).

sf_expect_failure_in
  example (n : Nat) : Ev n → Nat.Even n := by
    /- We could try to proceed by case analysis or induction on `n`.  But
        since `Ev` is mentioned in a premise, this strategy seems
        unpromising, because (as we've noted before) the induction
        hypothesis will talk about `n-1` (which is _not_ even!).  Thus, it
        seems better to first try `inversion` on the evidence for `Ev`.
        Indeed, the first case can be solved trivially. -/
    intro h
    inversion h with
    /- h = ev_0 -/
    | ev_0 => exists 0  -- (`0 = double 0` is closed by `exists`'s final `rfl`)
    /- h = ev_succ_succ n' h' -/
    | ev_succ_succ n' h' =>
    /- Unfortunately, the second case is harder.  We need to show
      `∃ n₀, n' + 2 = double n₀`, but the only available assumption is
      `h'`, which states that `Ev n'` holds.  Since this isn't directly
      useful, it seems that we are stuck and that performing case
      analysis on `h` was a waste of time.
  
      If we look more closely at our second goal, however, we can see
      that something interesting happened: By performing case analysis
      on `h`, we were able to reduce the original result to a similar
      one that involves a _different_ piece of evidence for `Ev`: namely
      `h'`.  More formally, we could finish our proof if we could show
      that
      ```
      ∃ k', n' = double k',
      ```
      which is the same as the original statement, but with `n'` instead
      of `n`.  Indeed, it is not difficult to convince Lean that this
      intermediate result would suffice. -/
      have he : (∃ (k' : Nat), n' = k'.double) → (∃ (n₀ : Nat), n' + 2 = n₀.double) := by
        intro ⟨k, hk⟩; exists (k + 1); rw [Nat.double_succ, hk]
      apply he
      /- Unfortunately, now we are stuck: we are trying to prove another instance
          of the same theorem we set out to prove -- only here we are
          talking about `n'` instead of `n`. -/

--  ### Induction on Evidence

--  If this story feels familiar, it is no coincidence: We
--  encountered similar problems in the Induction chapter,
--  when trying to use case analysis to prove results that
--  required induction. And once again the solution is...
--  induction!
--
--  Let's try proving that lemma again:

theorem Nat.ev_Even (n : Nat) (h : Ev n) : Even n := by
  induction h with
  -- h = ev_0
  | ev_0 => exists 0 -- (`0 = double 0` is closed by `exists`'s final `rfl`)
  -- h = ev_succ_succ n' h', with ih : Even n'
  | ev_succ_succ h' ih =>
    let ⟨k, hk⟩ := ih
    exists k + 1; rw [double_succ, hk]

-- Built on 2026-09-01 12:44 UTC

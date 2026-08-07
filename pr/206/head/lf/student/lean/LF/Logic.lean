import LF.Basics
import LF.Induction
import LF.Poly
import LF.Tactics
import LF.CustomTactics

import LF.SFLCompat

-- # Logic in Lean

-- IMPORTBLOCK import LF.Basics IMPORTBLOCK import LF.Induction IMPORTBLOCK
-- import LF.Poly IMPORTBLOCK import LF.Tactics IMPORTBLOCK import
-- LF.CustomTactics

open Nat hiding add_succ mul_succ beq beq_eq beq_refl

-- (OA) : added these to use Lean's Nat.

open Nat (add add_comm add_assoc add_zero zero_add mul_zero mul_one zero_mul)

-- We have now seen many examples of factual claims (i.e., *propositions*) and
-- ways of presenting evidence of their truth (*proofs*). In particular, we
-- have worked extensively with equality propositions (`e1 = e2`),
-- implications (`P → Q`), and quantified propositions (`∀ x, P`). In this
-- chapter, we will see how Lean can be used to carry out other familiar forms
-- of logical reasoning.

-- Before diving into details, we should talk a bit about the status of
-- mathematical statements in Lean. Lean is a *typed* language, which means
-- that every sensible expression has an associated type. Logical claims are
-- no exception: any statement we might try to prove in Lean has a type,
-- namely `Prop`, the type of *propositions*. We can see this with the
-- `#check` command:

-- -----------------------------------------------------------------------------

-- ## The `Prop` Type

#check (∀ n m : Nat, n + m = m + n : Prop)

-- Note that *all* syntactically well-formed propositions have type `Prop` in
-- Lean, regardless of whether they are true or not.

-- Simply *being* a proposition is one thing; being *provable* is a different
-- thing!

#check (2 = 2 : Prop)
#check (3 = 2 : Prop)
#check (∀ n : Nat, n = 2 : Prop)

-- Indeed, propositions don't just have types -- they are *first-class*
-- entities that can be manipulated in all the same ways as any of the other
-- things in Lean's world.

-- So far, we've seen one primary place where propositions can appear: in
-- `theorem` declarations.

theorem plus_2_2_is_4 : 2 + 2 = 4 := rfl

-- But propositions can be used in other ways. For example, we can give a name
-- to a proposition using a `def`, just as we give names to other kinds of
-- expressions.

def plus_claim : Prop := 2 + 2 = 4

#check (plus_claim : Prop)

-- We can later use this name in any situation where a proposition is expected
-- -- for example, as the claim in a `theorem` declaration.

theorem plus_claim_is_true : plus_claim := rfl

-- We can also write *parameterized* propositions -- that is, functions that
-- take arguments of some type and return a proposition.

-- For instance, the following function takes a number and returns a
-- proposition asserting that this number is equal to three:

def is_three (n : Nat) : Prop := n = 3

#check (is_three : Nat → Prop)

-- In Lean, functions that return propositions are said to define *properties*
-- of their arguments.

-- For instance, here's a (polymorphic) property defining the familiar notion
-- of an *injective function*.

def injective {α β} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

theorem succ_inj' : injective succ := by
  intro x y H; injection H

-- The familiar equality operator `=` is a (binary) function that returns a
-- `Prop`. The expression `n = m` is notation for `Eq n m`. Because `eq` can
-- be used with elements of any type, it is also polymorphic:

#check (Eq : ∀ {α : Type}, α → α → Prop)

#check pred

-- As a convenience, Lean will cast booleans by equating them to `true`, which
-- is why checking them against `Prop` succeeds. It also casts boolean
-- equalities to propositions by equating to `true`, and boolean inequalities
-- by equating to `false`. For clarity, we will avoid relying on these
-- implicit casts.

#check (false : Prop)

#check (true : Prop)

-- _Quiz:_

-- What is the type of the following expression?

--   pred (succ zero) = zero

-- 1. `Prop`
-- 2. `Nat → Prop`
-- 3. `∀ n : Nat, Prop`
-- 4. `Nat → Nat`
-- 5. Not typeable

#check (pred (succ zero) = zero : Prop)

-- _Quiz:_

-- What is the type of the following expression?

--   ∀ n : Nat, pred (succ n) = n

-- 1. `Prop`
-- 2. `Nat → Prop`
-- 3. `∀ n : Nat, Prop`
-- 4. `Nat → Nat`
-- 5. Not typeable

#check (∀ n : Nat, pred (succ n) = n : Prop)

-- _Quiz:_

-- What is the type of the following expression?

--   ∀ n : Nat, succ (pred n)

-- 1. `Prop`
-- 2. `Nat → Prop`
-- 3. `∀ n : Nat, Prop`
-- 4. `Nat → Nat`
-- 5. Not typeable

#check_failure ∀ n : Nat, succ (pred n)

-- _Quiz:_

-- What is the type of the following expression?

--   fun n : Nat => succ (pred n)

-- 1. `Prop`
-- 2. `Nat → Prop`
-- 3. `∀ n : Nat, Prop`
-- 4. `Nat → Nat`
-- 5. Not typeable

#check (fun n : Nat => succ (pred n) : Nat → Nat)

-- _Quiz:_

-- What is the type of the following expression?

--   fun n : Nat => succ (pred n) = n

-- 1. `Prop`
-- 2. `Nat → Prop`
-- 3. `∀ n : Nat, Prop`
-- 4. `Nat → Nat`
-- 5. Not typeable

#check (fun n : Nat => succ (pred n) = n : Nat → Prop)

-- _Quiz:_

-- Which of the following is *not* a proposition?

-- 1. `3 + 2 = 4`
-- 2. `3 + 2 = 5`
-- 3. `3 + 2 == 5`
-- 4. `(3 + 2 == 4) = false`
-- 5. `∀ n, (3 + 2 == n) = true → n = 5`
-- 6. All of these are propositions

#check (3 + 2 == 5 : Bool)

-- -----------------------------------------------------------------------------

-- ## Logical Connectives

-- ### Conjunction

-- The *conjunction*, or *logical and*, of propositions `A` and `B` is written
-- `A ∧ B`; it represents the claim that both `A` and `B` are true.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  /- A proof of a conjunction is a pair of proofs of the two components.
      To prove a conjunction, we build a pair using `constructor`. -/
  constructor
  case left  => /- 3 + 4 = 7 -/ rfl
  case right => /- 2 * 2 = 4 -/ rfl

-- The constructor for conjunction is `And.intro`, which concludes that
-- `A ∧ B` given that `A` and `B` hold individually.

#check (And.intro : ∀ {α β : Prop}, α → β → α ∧ β)

-- We can also apply the constructor for the conjunction explicitly.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  case left  => /- 3 + 4 = 7 -/ rfl
  case right => /- 2 * 2 = 4 -/ rfl

-- Rather than applying the constructor, we can explicitly provide the
-- arguments to the constructor as an `exact` proof.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact And.intro rfl rfl

-- We can also use Lean's anonymous constructor notation ⟨..., ...⟩, which
-- works on constructors for proofs as well.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact ⟨rfl, rfl⟩

-- ### Exercise (2 stars): add_is_zero ⭐⭐

theorem add_is_zero (n m : Nat) : n + m = 0 → n = 0 ∧ m = 0 := by
  sorry

-- So much for proving conjunctive statements. To go in the other direction --
-- i.e., to *use* a conjunctive hypothesis to help prove something else -- we
-- can use `let` to obtain the components.

example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  all_goals
    intro h
    let ⟨hn, hm⟩ := h
    rw [hn, hm]

-- As usual, we can also match on `h` right at the point where we introduce
-- it, instead of introducing and then destructing it:

example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro ⟨hn, hm⟩
  rw [hn, hm]

-- You may wonder why we bothered packing the two hypotheses `n = 0` and
-- `m = 0` into a single conjunction, since we could also have stated the
-- theorem with two separate premises:

example (n m : Nat) : n = 0 → m = 0 → n + m = 0 := by
  intro hn hm
  rw [hn, hm]

-- For this specific theorem, both formulations are fine. But it's important
-- to understand how to work with conjunctive hypotheses because conjunctions
-- often arise from intermediate steps in proofs, especially in larger
-- developments. Here's a simple example:

example (n m : Nat) (h : n + m = 0) : n * m = 0 := by
  all_goals
    apply add_is_zero at h
    let ⟨hn, hm⟩ := h
    rw [hm]; rfl

-- Another common situation is that we know `A /\ B` but in some context we
-- need just `A` or just `B`. In such cases we can use an underscore pattern
-- `_` to indicate that the unneeded conjunct should just be thrown away.

theorem proj1 (P Q : Prop) (h : P ∧ Q) : P := by
  let ⟨hP, _⟩ := h
  exact hP

-- Conjunctions come with their own built-in projections, `.left` and
-- `.right`, which we can use instead of pattern matching.

theorem left (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

-- ### Exercise (1 star): proj2 ⭐

theorem right (P Q : Prop) (h : P ∧ Q) : Q := by
  sorry

-- Finally, we sometimes need to rearrange the order of conjunctions and/or
-- the grouping of multi-way conjunctions. We can see this at work in the
-- proofs of the following commutativity and associativity theorems.

theorem and_commute (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  case left  => exact h.right
  case right => exact h.left

-- The anonymous constructor allows us to write a much terser proof.

theorem and_commute' (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  exact ⟨h.right, h.left⟩

-- In the following proof of associativity, notice how projections can be
-- chained in sequence to obtain components of nested conjunctions. Complete
-- the proof.

-- ### Exercise (1 star): and_associate ⭐

theorem and_associate (P Q R : Prop) (h : P ∧ (Q ∧ R)) : (P ∧ Q) ∧ R := by
  constructor
  case left =>
    sorry
  case right => exact h.right.right

-- The infix notation `∧` is actually just syntactic sugar for `And A B`. That
-- is, `And` is a Lean operator that takes two propositions as arguments and
-- yields a proposition.

#check (And : Prop → Prop → Prop)

-- ### Disjunction

-- Another important connective is the *disjunction*, or *logical or*, of two
-- propositions: `A ∨ B` is true when either `A` or `B` is. This infix
-- notation stands for `Or A B`, where `Or : Prop -> Prop -> Prop`.

-- To use a disjunctive hypothesis in a proof, we proceed by case analysis --
-- which, as with other data types like `Nat`, is done using `cases`. The two
-- cases are `inl` (for "left injection", or "in the left case") and `inr`
-- (for "right injection", or "in the right case").

theorem factor_is_zero (n m : Nat) (h : n = 0 ∨ m = 0) : n * m = 0 := by
  cases h
  /- `n = 0` -/
  case inl hn => rw [hn, zero_mul]
  /- `m = 0` -/
  case inr hm => rw [hm, mul_zero]

-- We can see in this example that, when we perform case analysis on a
-- disjunction `P ∨ Q`, we must separately discharge two proof obligations,
-- each showing that the conclusion holds under a different assumption -- `P`
-- in the first subgoal and `Q` in the second.

-- Rather than performing case analysis via `cases`, we can also use `obtain`
-- to match on the two possible injections, much like with `let`.

theorem and_is_false (b1 b2 : Bool) (h : (b1 = false) ∨ (b2 = false)) :
    (b1 && b2) = false := by
  obtain hb1 | hb2 := h
  case inl => rw [hb1, Bool.false_and]
  case inr => rw [hb2, Bool.and_false]

-- Conversely, to show that a disjunction holds, it suffices to show that one
-- of its sides holds. This can be done via the tactics `left` and `right`. As
-- their names imply, the first one requires proving the left side of the
-- disjunction, while the second requires proving the right side. Here is a
-- trivial use...

theorem or_intro_l (P Q : Prop) (h : P) : P ∨ Q := by
  left; exact h

-- ... and here is a slightly more interesting example requiring both `left`
-- and `right`:

theorem zero_or_succ (n : Nat) : n = 0 ∨ n = pred (succ n) := by
  all_goals
    cases n
    case zero => left; rfl
    case succ n => right; rw [Nat.pred_succ]

-- ### Exercise (2 stars): mul_is_zero ⭐⭐

theorem mul_is_zero (n m : Nat) (h : n * m = 0) : n = 0 ∨ m = 0 := by
  sorry

-- ### Exercise (1 star): or_commute ⭐

theorem or_commute (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  sorry

-- ### Falsehood and Negation

-- Up to this point, we have mostly been concerned with proving "positive"
-- statements -- addition is commutative, appending lists is associative, etc.
-- We are sometimes also interested in negative results, demonstrating that
-- some proposition is *not* true. Such statements are expressed with the
-- logical negation operator `¬`, which a prefix notation for `Not`.

-- To see how negation works, recall the *principle of explosion* from the
-- `Tactics` chapter, which asserts that, if we assume a contradiction, then
-- any other proposition can be derived.

-- Following this intuition, we could define `¬ P` ("not `P`") as
-- `∀ Q, P → Q`. Lean makes an equivalent but slightly different choice,
-- defining `~ P` as `P → False`, where `False` is a specific unprovable
-- proposition defined in the standard library.

#check (Not : Prop → Prop)
#print Not

example : ∀ P, Not P = (P → False) := by intro; rfl
example : ∀ P, (¬ P) = (P → False) := by intro; rfl

-- Since `False` is a contradictory proposition, the principle of explosion
-- also applies to it. If we can get `False` into the context, we can use
-- `cases` on it to complete any goal:

theorem ex_falso_quodlibet (P : Prop) (h : False) : P := by
  cases h

-- The Latin *ex falso quodlibet* means, literally, "from falsehood follows
-- whatever you like"; this is another common name for the principle of
-- explosion.

-- ### Exercise (2 stars): not_implies_other_not ⭐⭐

theorem not_implies_other_not (P : Prop) (h : ¬ P) :
    (∀ Q : Prop, P → Q) := by
  sorry

-- Inequality is a very common form of negated statement, so there is a
-- special notation for it: `≠`, which is infix notation for `Ne`.

#print Ne

theorem zero_not_one : 0 ≠ 1 := by
  /- FULL: The proposition `0 ≠ 1` is exactly the same as `¬ (0 = 1)`
      -- that is, `Not (0 = 1)` -- which unfolds to `(0 = 1) → False`. -/
  /- FULL: To prove an inequality, we may assume the opposite equality... -/
  intro contra
  /- FULL: ...and deduce a contradiction from it. Here, the equality
      `0 = 1` corresponds to `zero = succ zero`, which contradicts
      disjointness of constructors `zero` and `succ`, so `contradiction`
      takes care of it. -/
  contradiction
  -- JC: `cases contra` and `injection contra` both also work,
  -- but is probably harder to explain.

-- It takes a little practice to get used to working with negation in Lean.
-- Even though *you* may see perfectly well why a claim involving negation
-- holds, it can be a little tricky at first to see how to make Lean
-- understand it!

-- Here are proofs of a few familiar facts to help get you warmed up.

theorem not_False : ¬ False := by
  intro h; exact h

theorem contradiction_implies_anything (P Q : Prop) (h : P ∧ ¬ P) : Q := by
  all_goals
    let ⟨hP, hnP⟩ := h
    apply hnP at hP; cases hP

theorem double_neg (P : Prop) (hP : P) : ¬ ¬ P := by
  all_goals
    intro h; apply h; exact hP

-- ### Exercise (2 stars): double_neg_informal (Advanced, manually graded) ⭐⭐

-- Write an *informal* proof of `double_neg`: *Theorem*: `P` implies `¬ ¬ P`,
-- for any proposition `P`.

-- ### Exercise (1 star): contrapositive ⭐

theorem contrapositive (P Q : Prop) (h : P → Q) : (¬ Q → ¬ P) := by
  sorry

-- ### Exercise (1 star): not_PNP_informal (Advanced, manually graded) ⭐

-- Write an informal proof of the proposition `∀ P : Prop, ¬ (P ∧ ¬ P)`.

-- ### Exercise (2 stars): de_morgan_not_or ⭐⭐

-- *De Morgan's Laws*, named for Augustus De Morgan, describe how negation
-- interacts with conjunction and disjunction. The following law says that
-- "the negation of a disjunction is the conjunction of the negations." There
-- is a dual law `de_morgan_not_and_not` to which we will return at the end of
-- this chapter.

theorem de_morgan_not_or (P Q : Prop) (h : ¬ (P ∨ Q)) : ¬ P ∧ ¬ Q := by
  sorry

-- ### Exercise (1 star): not_succ_inverse_pred ⭐

-- Since we are working with natural numbers, we can disprove that `succ` and
-- `pred` are inverses of each other:

theorem not_succ_pred_n : ¬ (∀ n : Nat, succ (pred n) = n) := by
  sorry

-- Since inequality involves a negation, it also requires a little practice to
-- be able to work with it fluently. Here is one useful trick.

-- If you are trying to prove a goal that is nonsensical (e.g., the goal state
-- is `false = true`), apply `ex_falso_quodlibet` to change the goal to
-- `False`.

-- This makes it easier to use assumptions of the form `¬ P` that may be
-- available in the context -- in particular, assumptions of the form `x ≠ y`.

theorem not_true_is_false (b : Bool) (h : b ≠ true) : b = false := by
  -- FOLD
  cases b
  case false => rfl
  case true =>
    unfold Ne Not at h
    apply ex_falso_quodlibet
    apply h; rfl
  -- /FOLD

-- Since reasoning with `ex_falso_quodlibet` is quite common, Lean provides a
-- tactic, `exfalso`, for applying it.

theorem not_true_is_false' (b : Bool) (h : b ≠ true) : b = false := by
  cases b
  case false => rfl
  case true =>
    unfold Ne Not at h
    exfalso -- ⟵ here
    apply h; rfl

-- _Quiz:_

-- To prove the following proposition, which tactics will we need besides
-- `intro`, `apply`, and `exact`?

--   ∀ X : Prop, ∀ a b : X, a = b ∧ a ≠ b → False

-- 1. `cases`, `unfold`, `left`, and `right`
-- 2. `cases` and `unfold`
-- 3. only `cases`
-- 4. `left` and/or `right`
-- 5. only `unfold`
-- 6. none of the above

example (X : Prop) (a b : X) : a = b ∧ a ≠ b → False := by
  intro ⟨h, hn⟩; apply hn; exact h

-- _Quiz:_

-- To prove the following proposition, which tactics will we need besides
-- `intro`, `apply`, and `exact`?

--   ∀ P Q : Prop, P ∨ Q → ¬ ¬ (P ∨ Q)

-- 1. `cases`, `unfold`, `left`, and `right`
-- 2. `cases` and `unfold`
-- 3. only `cases`
-- 4. `left` and/or `right`
-- 5. only `unfold`
-- 6. none of the above

example (P Q : Prop) (h : P ∨ Q) : ¬ ¬ (P ∨ Q) := by
  intro hn; apply hn; exact h

-- _Quiz:_

-- To prove the following proposition, which tactics will we need besides
-- `intro`, `apply`, and `exact`?

--   ∀ P Q : Prop, P → (P ∨ ¬ ¬ Q)

-- 1. `cases`, `unfold`, `left`, and `right`
-- 2. `cases` and `unfold`
-- 3. only `cases`
-- 4. `left` and/or `right`
-- 5. only `unfold`
-- 6. none of the above

example (P Q : Prop) (h : P) : P ∨ ¬ ¬ Q := by
  left; exact h

-- _Quiz:_

-- To prove the following proposition, which tactics will we need besides
-- `intro`, `apply`, and `exact`?

--   ∀ P Q : Prop, P ∨ Q → (¬ ¬ P) ∨ (¬ ¬ Q)

-- 1. `cases`, `unfold`, `left`, and `right`
-- 2. `cases` and `unfold`
-- 3. only `cases`
-- 4. `left` and/or `right`
-- 5. only `unfold`
-- 6. none of the above

example (P Q : Prop) (h : P ∨ Q) : (¬ ¬ P) ∨ (¬ ¬ Q) := by
  cases h
  case inl hP => left; intro hnP; apply hnP; exact hP
  case inr hQ => right; intro hnQ; apply hnQ; exact hQ

-- _Quiz:_

-- To prove the following proposition, which tactics will we need besides
-- `intro`, `apply`, and `exact`?

--   ∀ A : Prop, 1 = 0 → (A ∨ ¬ A)

-- 1. `contradiction`, `unfold`, `left`, and `right`
-- 2. `contradiction` and `unfold`
-- 3. only `contradiction`
-- 4. `left` and/or `right`
-- 5. only `unfold`
-- 6. none of the above

example (A : Prop) (h : 1 = 0) : (A ∨ ¬ A) := by
  contradiction

-- ## Truth

-- Besides `False`, Lean's standard library also defines `True`, a proposition
-- that is trivially true. To prove it, we use the constructor `True.intro`
-- explicitly, or the anonymous constructor `⟨⟩`, or the `constructor` tactic.

example : True := by exact True.intro
example : True := True.intro
example : True := by exact ⟨⟩
example : True := ⟨⟩
example : True := by constructor

-- Unlike `False`, which is used extensively, `True` is used relatively
-- rarely: it is trivial (and therefore uninteresting) to prove as a goal, and
-- it provides no useful information when it appears as a hypothesis.

-- However, `True` can be quite useful when defining complex `Prop`s using
-- conditionals or as a parameter to higher-order `Prop`s. We'll come back to
-- this later.

-- For now, let's take a look at how we can use `True` and `False` to achieve
-- an effect similar to that of the `contradiction` tactic, without literally
-- using `contradiction`.

-- Pattern-matching lets us do different things for different constructors. If
-- the result of applying two different constructors were hypothetically
-- equal, then we could use `match` to convert an unprovable statement (like
-- `False`) to one that is provable (like `True`).

def discr_fun (n : Nat) : Prop :=
  match n with
  | 0 => True
  | _ + 1 => False

theorem discr_fun_zero : discr_fun 0 = True := rfl

theorem discr_fun_succ n : discr_fun (n + 1) = False := rfl

theorem discr_example (n : Nat) : ¬ (0 = n + 1) := by
  intro h
  have hd : discr_fun 0 := by rw [discr_fun_zero]; exact ⟨⟩
  rw [h, discr_fun_succ] at hd; exact hd

-- To generalize this to other constructors, we simply have to provide an
-- appropriate variant of `discr_fun`. To generalize it to other conclusions,
-- we can use `exfalso` to replace them with `False`. The `contradiction`
-- tactic takes care of all of this for us.

-- ### Exercise (2 stars): nil_is_not_cons (Advanced, manually graded) ⭐⭐

-- Use the same technique as above to show that `[] ≠ x :: xs`. Do not use the
-- `contradiction` tactic.

-- FILL IN HERE

theorem nil_is_not_cons {α : Type} (x : α) (xs : List α) :
    ¬ ([] = x :: xs) := by
  sorry

-- ### Logical Equivalence

-- The handy "if and only if" connective, which asserts that two propositions
-- have the same truth value, is a structure containing the two implication
-- directions. `P ↔ Q` is notation for `Iff P Q`.

#print Iff

#check (fun α β : Prop => α ↔ β : Prop → Prop → Prop)

theorem iff_sym (P Q : Prop) (h : P ↔ Q) : (Q ↔ P) := by
  all_goals
    constructor
    case mp => exact h.mpr
    case mpr => exact h.mp

theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  constructor
  case mp => apply not_true_is_false
  case mpr => intro h; rw [h]; intro h'; contradiction

-- ### Exercise (1 star): iff_properties ⭐

-- Using the above proof that `↔` is symmetric (`iff_sym`) as a guide, prove
-- that it is also reflexive and transitive.

theorem iff_refl (P : Prop) : P ↔ P := by
  sorry

theorem iff_trans (P Q R : Prop) (h1 : P ↔ Q) (h2 : Q ↔ R) : (P ↔ R) := by
  sorry

theorem or_associate (P Q R : Prop) : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  constructor
  case mp =>
    intro h
    obtain hP | (hQ | hR) := h
    case inl     => left; left; exact hP
    case inr.inl => left; right; exact hQ
    case inr.inr => right; exact hR
  case mpr =>
    intro h
    obtain (hP | hQ) | hR := h
    case inl.inl => left; exact hP
    case inl.inr => right; left; exact hQ
    case inr     => right; right; exact hR

-- ### Exercise (3 stars): or_distributes_over_and ⭐⭐⭐

theorem or_distributes_over_and (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

theorem mul_eq_0 (n m : Nat) :
    n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  case mp => apply mul_is_zero
  case mpr => apply factor_is_zero

-- ### Existential Quantification

-- Another fundamental logical connective is *existential quantification*. To
-- say that there is some `x` of type `T` such that some property `P` holds of
-- `x`, we write `∃ x : T, P`. This is notation for the `Exists` connective,
-- and is defined as `Exists (fun (x : T) => P)`. As with `∀ x : T`, the type
-- annotation `: T` can be omitted if Lean is able to infer from the context
-- what the type of `x` should be.

-- To prove a statement of the form `∃ x, P`, we must show that `P` holds for
-- some specific choice for `x`, known as the *witness* of the existential.
-- This is done in two steps: First, we explicitly tell Lean which witness `t`
-- we have in mind by invoking the tactic `exists t`. Then we prove that `P`
-- holds after all occurrences of `x` are replaced by `t`. The `exists` tactic
-- tries to close the proof with simple tactics such as `rfl` or
-- `contradiction`, so we may not have to prove `P` explicitly.

#check (Exists : ∀ {T : Type}, (T → Prop) → Prop)

abbrev Even x := ∃ n : Nat, x = double n

#check (Even : Nat → Prop)

example : Even 4 := by exists 2
  -- `4 = double 2` holds by `rfl`,
  -- but is proven automatically by `exists`

-- Conversely, if we have an existential hypothesis `∃ x, P` in the context,
-- can destruct it to obtain a witness `x` and a hypothesis stating that `P`
-- holds of `x`.

example n : (∃ m, n = m + 4) → (∃ o, n = o + 2) := by
  intro ⟨m, hm⟩
  exists (m + 2)

-- ### Exercise (1 star): dist_not_exists ⭐

-- Prove that "`P` holds for all `x` implies "there is no `x` for which `P`
-- does not hold." (Hint: `cases` works on existential assumptions!)

theorem dist_not_exists (X : Type) (P : X → Prop) (h : ∀ x, P x) :
    ¬ (∃ x, ¬ P x) := by
  sorry

-- ### Exercise (2 stars): dist_exists_or ⭐⭐

-- Prove that existential quantification distributes over disjunction.

theorem dist_exists_or (X : Type) (P Q : X → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

-- ### Exercise (3 stars): ble_plus_exists ⭐⭐⭐

theorem ble_plus_exists : ∀ n m : Nat, (n ≤? m = true) → ∃ x, m = x + n := by
  sorry

-- FILL IN HERE

theorem add_exists_ble (n m : Nat) (h : ∃ x, m = x + n) : n ≤? m = true := by
  sorry

-- -----------------------------------------------------------------------------

-- ## Recap: Logical Connectives in Lean

-- Connectives introduced in this chapter:

-- - `A ∧ B` (conjunction):

--   - introduced with `constructor`
--   - eliminated with `intro ⟨HA, HB⟩` or `let ⟨HA, HB⟩ := H`

-- - `A ∨ B` (disjunction):

--   - introduced with `left` and `right`
--   - eliminated with `cases`

-- - `False` (falsehood):

--   - eliminated with `cases` or `contradiction`

-- - `¬ A` (negation):

--   - defined as `A → False`

-- - `True` (truthhood):

--   - introduced as`True.intro` or with `constructor`

-- - `A ↔ B` (iff):

--   - introduced with `constructor`
--   - eliminated with `intro ⟨HAB, HBA⟩` or `let ⟨HAB, HBA⟩ := H`

-- - `∃ x : A, P` (existential):

--   - introduced with `exists t`
--   - eliminated with `intro ⟨x, Hx⟩` or `let ⟨x, Hx⟩ := H`

-- Fundamental connectives we've been using since the beginning:

-- - equality (`e1 = e2`)
-- - implication (`P → Q`)
-- - universal quantification (`∀ x, P`)

-- -----------------------------------------------------------------------------

-- ## Programming with Propositions

-- The logical connectives that we have seen provide a rich vocabulary for
-- defining complex propositions from simpler ones. To illustrate, let's look
-- at how to express teh claim that an element `x` occurs in a list `l`.
-- Notice that this property has a simple recursive structure:

-- We can translate this directly into a straightforward recursive function
-- taken an element and a list and returning... a proposition!

def In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'

theorem In_nil {α} (x : α) : In x [] = False := rfl

theorem In_cons {α} (x x' : α) (xs : List α) : In x (x' :: xs) = (x = x' ∨ In x xs) := rfl

-- When `In` is applied to a concrete list, it exapnds into a concrete
-- sequence of nested disjunctions.

example : In 4 [1, 2, 3, 4, 5] := by
  all_goals
    dsimp [In]; right; right; right; left; rfl

example (n : Nat) (h : In n [2, 4]) : ∃ n' : Nat, n = 2 * n' := by
  all_goals
    dsimp [In] at h
    obtain h | h | ⟨⟨⟩⟩ := h
    case inl => exists 1
    case inr.inl => exists 2
    /- (Notice the use of the empty pattern to discharge the last case.) -/

-- We can also reason about more generic statements involving `In`.

theorem In_map (α β : Type) (f : α → β) (xs : List α) (x : α) (h : In x xs) :
    In (f x) (List.map f xs) := by
  -- TERSE: FOLD
  induction xs
  case nil => rw [In_nil] at h; contradiction
  case cons x' xs' ih =>
    rw [In_cons] at h
    obtain h | h := h
    case inl => rw [h, List.map_cons, In_cons]; left; rfl
    case inr => rw [List.map_cons, In_cons]; right; exact ih h
  -- TERSE: /FOLD

-- This way of defining propositions recursively is very convenient in some
-- cases, less so in others. In particular, it is subject to the usual
-- restrictions regarding definitions of recursive functions, e.g., the
-- requirement that they be "obviously terminating."

-- In the next chapter, we will see how to define propositions *inductively*
-- -- a different technique with its own strengths and limitations.

-- ### Exercise (2 stars): In_map_iff ⭐⭐

theorem In_map_iff (α β : Type) (f : α → β) (xs : List α) (y : β) :
    In y (List.map f xs) ↔ ∃ x, f x = y ∧ In x xs := by
  constructor
  case mp =>
    sorry
  case mpr =>
    sorry

-- ### Exercise (3 stars): All ⭐⭐⭐

-- We noted above that functions returning propositions can be seen as
-- *properties* of their arguments. For instance, if `P` has type
-- `Nat -> Prop`, then `P n` says that property `P` holds of `n`.

-- Drawing inspiration from `In`, write a recursive function `All` stating
-- that some property `P` holds of all elements of a list `xs`. To make sure
-- your definition is correct, prove the `All_In` lemma below. (Of course,
-- your definition should *not* just restate the left-hand side of `All_In`.)

def All {α : Type} (P : α → Prop) (xs : List α) : Prop := sorry

theorem All_nil {α} (P : α → Prop) : All P [] = True := sorry

theorem All_cons {α} (P : α → Prop) x xs : All P (x :: xs) = (P x ∧ All P xs) := sorry

theorem All_In α (P : α → Prop) (xs : List α) :
    (∀ x, In x xs → P x) ↔ All P xs := by
  sorry

-- ### Exercise (2 stars): combine_odd_even ⭐⭐

-- Complete the definition of `combine_odd_even` below. It takes as arguments
-- two properties of numbers, `Podd` and `Peven`, and it should return a
-- property `P` such that `P n` is equivalent to `Podd n` when `n` is odd and
-- equivalent to `Peven n` otherwise.

abbrev combine_odd_even (Podd Peven : Nat → Prop) : Nat → Prop := sorry

-- To test your definition, prove the following facts:

theorem combined_odd_even_intro Podd Peven n
    (hodd : odd n = true → Podd n)
    (heven : odd n = false → Peven n) :
    combine_odd_even Podd Peven n := by
  sorry

theorem combined_odd_even_elim_odd Podd Peven n
    (h : combine_odd_even Podd Peven n)
    (hodd : odd n = true) : Podd n := by
  sorry

theorem combined_odd_even_elim_even Podd Peven n
    (h : combine_odd_even Podd Peven n)
    (hodd : odd n = false) : Peven n := by
  sorry

-- ## Applying Theorems to Arguments

-- Lean treats *proofs* as first-class objects. There is a great deal to be
-- said about this, but it is not necessary to understand it all to use Lean.
-- This section gives just a taste, leaving a deeper exploration for the
-- optional chapters `ProofObjects` and `IndPrinciples`.

-- We have seen that we can use `#check` to ask Lean whether an expression has
-- a given type:

#check (add : Nat → Nat → Nat)

-- We can also use it to check what theorem a particular identifier refers to:

#check add_comm

#check add_assoc

-- Lean checks the *statements* of the `add_comm` and `add_assoc` theorems in
-- the same way that it checks the *type* of any term (e.g. `add`). Leaving
-- off the colon and the type, Lean prints these types in the infoview for us.

-- Why?

-- The reason is that the identifier `add_comm` actually refers to a *proof
-- object* -- a logical derivation establishing the truth of the statement
-- `∀ n m, n + m = m + n`. The type of this object is the proposition that it
-- is a proof of.

-- The type of an ordinary function tells us what we can do with it.

-- - If we have a term of type `Nat → Nat → Nat`, we can give it two `Nat`s as
--   arguments and get a `Nat` back. Similarly, the statement of a theorem tells
--   us what we can use that theorem for.

-- - If we have a term of type `∀ n m, n = m → n + n = m + n`, and we provide it
--   two numbers `n` and `m` and a third "arugment" of type `n = m`, we get back
--   a proof object of type `n + n = m + m`.

-- Operationally, this analogy goes even further: by applying a theorem as if
-- it were a function, i.e., applying it to values and hypotheses with
-- matching types, we can specialize its result without having to resort to
-- intermediate assertions. For example, suppose we wanted to prove the
-- follwing result:

example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm]
  rw [add_comm]
  sorry

-- It appears at first sight that we ought to be able to prove this be
-- rewriting with `add_comm` twice to make the two sides match. The problem is
-- that the second rewrite undoes the effect of the first, leaving us back
-- where we started...

-- We can fix this by applying `add_comm` to the arguments we want it to be
-- instantiated with, in much the same way as we apply a polymorphic function
-- to a type argument. Then the rewrite is forced to happen exactly where we
-- want it.

example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm]
  rw [add_comm z y]

-- If we really wanted, we could in fact do it for both rewrites.

example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm x (y + z)]
  rw [add_comm z y]

-- The fact that implications are functions means we can prove them by
-- explicitly providing a function.

theorem identity {P : Prop} : P → P := fun h => h

-- _Quiz:_

-- Suppose we have

--   n m : Nat
--   H1 : n = m
--   H2 : b = 42
--   trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c

-- What is the type of this "proof object"?

--   trans_eq Nat n m 42 H1 H2

-- 1. `n = m`
-- 2. `42 = n`
-- 3. `n = 42`
-- 4. Does not typecheck

-- example (n m : Nat) (h1 : n = m) (h2 : m = 42) (trans*eq : ∀ (α : Type) (a
-- b c : α), a = b → b = c → a = c) : True := by have : n = 42 := trans*eq Nat
-- n m 42 h1 h2

-- _Quiz:_

-- Suppose, again, we have

--   n m : Nat
--   H1 : n = m
--   H2 : b = 42
--   trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c

-- What is the type of this proof object?

--   trans_eq _ _ _ _ H1 H2

-- 1. `n = m`
-- 2. `42 = n`
-- 3. `n = 42`
-- 4. Does not typecheck

-- _Quiz:_

-- Suppose, again, we have

--   n m : Nat
--   H1 : n = m
--   H2 : b = 42
--   trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c

-- What is the type of this proof object?

--   trans_eq Nat m 42 n H2

-- 1. `m = n`
-- 2. `m = n → 42 = n`
-- 3. `42 = n → m = n`
-- 4. Does not typecheck

-- _Quiz:_

-- Suppose, again, we have

--   n m : Nat
--   H1 : n = m
--   H2 : b = 42
--   trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c

-- What is the type of this proof object?

--   trans_eq _ 42 n m

-- 1. `n = m → m = 42 → n = 42`
-- 2. `42 = n → n = m → 42 = m`
-- 3. `n = 42 → 42 = m → n = m`
-- 4. Does not typecheck

-- _Quiz:_

-- Suppose, again, we have

--   n m : Nat
--   H1 : n = m
--   H2 : b = 42
--   trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c

-- What is the type of this proof object?

--   trans_eq _ _ _ _ H2 H1

-- 1. `b = a`
-- 2. `42 = a`
-- 3. `a = 42`
-- 4. Does not typecheck

-- ## Working with Decidable Properties

-- We've seen two different ways of expressing logical claims in Lean: with
-- *booleans* (of type `Bool`), and with *propositions* (of type `Prop`). Here
-- are the key differences between `Bool` and `Prop`:

-- | | `Bool` | `Prop` | | ------------------- | ------ | ------ | |
-- decidable? | yes | no | | useable with match? | yes | no |

-- FULL: The crucial difference between the two worlds is *decidability*.
-- Every (closed) expression of type `Bool` can be simplified in a finite
-- number of steps to either `true` or `false` -- i.e., there is a terminating
-- mechanical procedure for deciding whether or not it is `true`.

-- This means that, for example, the type `Nat → Bool` is inhabited only by
-- functions that, given a `Nat`, always yield either `true` or `false` in
-- finite time; this, in turn, means (by a standard computability argument)
-- that there is *no* function in `Nat → Bool` that checks whether a given
-- number is the code of a terminating Turing machine.

-- By contrast, the type `Prop` includes both decidable and undecidable
-- mathematical propositions; in particular, the type `Nat → Prop` does
-- contain functions representing properties like "the nth Turing machine
-- halts."

-- The second table row follows directly from this essential difference. To
-- evaluate a pattern match (or conditional) on a boolean, we need to know
-- whether the scrutinee evaluates to `true` or `false`; this only works for
-- `bool`, not `Prop`.

-- Since `Prop` includes *both* decidable and undecidable properties, we have
-- two options when we want to formalize a property that happens to be
-- decidable: we can express it either as a boolean computation, or as a
-- function into `Prop`.

-- For instance, to claim that a number `n` is even, we can say either that
-- `even n` evaluates to `true`...

example : even 42 = true := rfl

-- ... or that there exists some `k` such that `n = double k`.

example : Even 42 := by dsimp [Even]; exists 21

-- Of course, it would be deeply strange if these two characterizations of
-- evenness did not describe the same set of natural numbers! Fortunately,
-- they do!

-- To prove this, we first need two helper lemmas.

theorem even_double (k : Nat) :
    even (double k) = true := by
  -- FOLD
  induction k
  case zero => rw [double_zero]; rfl
  case succ k' ih => rw [double_succ]; exact ih
  -- /FOLD

theorem even_double_conv (n : Nat) : ∃ k : Nat,
    n = bif even n then double k else succ (double k) := by
  sorry

-- Now the main theorem:

theorem even_bool_prop (n : Nat) : even n = true ↔ Even n := by
  -- FOLD
  constructor
  case mp =>
    intro h
    let ⟨k, hk⟩ := even_double_conv n
    rw [h] at hk; dsimp at hk; dsimp [Even]; exists k
  case mpr =>
    intro ⟨k, hk⟩; rw [hk]; apply even_double
  -- /FOLD

-- In view of this theorem, we can say that the boolean computation `even n`
-- is *reflected* in the truth of the proposition `∃ k, n = double k`.

-- Similarly, to state that two numbers `n` and `m` are equal, we can say
-- either

-- 1. that `n == m` returns `true`, or
-- 2. that `n = m`.

-- Again, these two notions are equivalent:

-- (For the reverse direction we need the simple fact that `==` is reflexive.)

theorem beq_refl (n : Nat) : (n == n) = true := decide_eq_true rfl

theorem beq_eq_true (n1 n2 : Nat) :
    (n1 == n2) = true ↔ n1 = n2 := by
  -- FOLD
  constructor
  case mp => apply beq_eq
  case mpr => intro H; rw [H, beq_refl]
  -- /FOLD

-- So what should we do in situations where some claim could be formalized as
-- either a proposition or a boolean computation? Which should we choose?

-- In general, *both* can be useful. For example, booleans are more useful for
-- defining functions, since we can test whether they are true using
-- conditional expressions.

abbrev is_even_prime (n : Nat) : Bool :=
  bif n == 2 then true else false

-- FULL: Beyond the fact that non-computable properties are possible in
-- general to phrase as boolean computations, even many *computable*
-- properties are easier to express using `Prop` than `bool`, since recursive
-- function definitions are subject to significant restrictions. For instance,
-- the next chapter shows how to define the property that a regular expression
-- matches a given string using `Prop`. Doing the same with `Bool` would
-- amount to writing a regular expression matching algorithm, which would be
-- more complicated, harder to understand, and harder to reason about than a
-- simple (non-algorithmic) definition of this property.

-- Conversely, an important side benefit of stating facts using booleans is
-- enabling some proof automation through computation with terms, a technique
-- known as *proof by reflection*.

-- Consider the following statement:

-- The most direct way to prove this is to give the value of `k` explicitly.

example : Even 100 := by
  exists 50

-- The proof of the corresponding boolean statement is simpler, because we
-- don't have to invent the witness `50`: computation does it for us!

example : even 100 := rfl

-- Now, the useful observation is that, since the two notions are equivalent,
-- we can use the boolean formulation to prove the other one without
-- mentioning the value 500 explicitly:

example : Even 100 := by
  let ⟨H, _⟩ := even_bool_prop 100
  apply H; rfl

-- Although we haven't gained much in terms of proof-script simplicity in this
-- case, larger proofs can often be made considerably simpler by the use of
-- reflection.

-- As an extreme example, a famous mechanized proof of the even more famous
-- *four colour theorem* uses reflection ot reduce the analysis of hundreds of
-- different cases to a boolean computation.

-- Another advantage of booleans is that the *negation* of a claim about
-- booleans is straightforward to state and (when true) to prove: simply slip
-- the expected boolean result.

example : even 101 = false := rfl

-- In contrast, propositional negation can be difficult to work with directly.
-- For example, suppose we state the nonevenness of `101` propositionally:

-- Proving this directly -- by assuming that there is some `n` such that
-- `101 = double n` and then somehow reasoning to a contradiction -- would be
-- rather complicated.

-- But if we convert it to a claim about the boolean `even` function, we can
-- let Lean do the work for us.

example : ¬ Even 101 := by
  all_goals
    intro h; apply (even_bool_prop 101).mpr at h
    dsimp [even] at h; contradiction

-- Conversely, there are situations where it can be easier to work with
-- propositions rather than booleans. In particular, knowing that
-- `(n == m) = true` is generally of little direct help in the middle of a
-- proof involving `n` and `m`. But if we convert the statement to the
-- equivalent form `n = m`, then we can easily rewrite with it.

theorem add_beq_true (n m p : Nat) (h : (n == m) = true) :
    (n + p == m + p) = true := by
  all_goals
    apply (beq_eq_true n m).mp at h
    rw [h, beq_refl]

-- We won't discuss reflection any further for the moment, but it serves as a
-- good example showing the different strengths of booleans and general
-- propositions. Being able to cross back and forth between the boolean and
-- propositional worlds will often be convenient in later chapters.

-- ### Exercise (2 stars): logical connectives ⭐⭐

-- The following theorems relate the propositional connectives studied in this
-- chapter to the corresponding boolean operations.

theorem andb_true_iff (b1 b2 : Bool) :
    (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by
  sorry

theorem orb_true_iff (b1 b2 : Bool) :
    (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by
  sorry

-- ### Exercise (3 stars): beq_list ⭐⭐⭐

-- Given a boolean operator `beq` for testing equality of elements of some
-- type `α`, we can define a function `beq_list` for testing equality of lists
-- with elements in `α`. Complete the definition of the `beq_list` function
-- below. to make sure that your definition is correct, prove the lemma
-- `beq_list_true_iff`.

def beq_list {α : Type} (beq : α → α → Bool) (xs1 xs2 : List α) : Bool := sorry

theorem beq_list_nil_nil {α} (beq : α → α → Bool) :
    beq_list beq [] [] = true := sorry

theorem beq_list_cons_cons {α} (beq : α → α → Bool) x1 x2 xs1 xs2 :
    beq_list beq (x1 :: xs1) (x2 :: xs2) =
    (beq x1 x2 && beq_list beq xs1 xs2) := sorry

theorem beq_list_nil_cons {α} (beq : α → α → Bool) x xs :
    beq_list beq [] (x :: xs) = false := sorry

theorem beq_list_cons_nil {α} (beq : α → α → Bool) x xs :
    beq_list beq (x :: xs) [] = false := sorry

theorem beq_list_true_iff α (beq : α → α → Bool)
    (h : ∀ x1 x2, beq x1 x2 = true ↔ x1 = x2) :
    ∀ xs1 xs2, beq_list beq xs1 xs2 = true ↔ xs1 = xs2 := by
  sorry

-- ### Exercise (2 stars): All_forallb ⭐⭐

-- Prove the theorem below, which relates `forallb`, from the exercise
-- `Tactics.forall_exists_challenge`, to the `All` property defined above.

-- Copy the definition of `forallb` from Tactics here so that this file can be
-- graded on its own.

def Logic.forallb {α : Type} (test : α → Bool) (xs : List α) : Bool := sorry

theorem forallb_nil {α} (test : α → Bool) : Logic.forallb test [] = true := sorry

theorem forallb_cons {α} (test : α → Bool) x xs :
    Logic.forallb test (x :: xs) = (test x && Logic.forallb test xs) := sorry

theorem forallb_true_iff α (test : α → Bool) (xs : List α) :
    Logic.forallb test xs = true ↔ All (fun x => test x = true) xs := by
  sorry

-- (Ungraded thought question) Are there any important properties often the
-- function `forallb` which are not captured by this specification?

-- -----------------------------------------------------------------------------

-- ## The Logic of Lean

-- Lean's logical core differs in some important ways from other formal
-- systems that are used by mathematicians to write down precise and rigorous
-- definitions and proofs -- in particular from Zermelo–Fraenkel Set Theory
-- (ZFC), the most popular foundation for paper-and-pencil mathematics.

-- We conclude this chapter with a brief discussion of some of the most
-- significant differences between these two worlds.

-- ### Propositional Extensionality

-- Lean's logic is quite minimalistic. This means that on occasionally
-- encounters cases where translating standard mathematical reasoning into
-- Lean is cumbersome -- or even impossible -- unless we enrich its core logic
-- with additional axioms.

-- For example, the equality assertions that we have seen so far mostly have
-- concerned elements of inductive types (`Nat`, `Bool`, etc.). But since the
-- equality operator is polymorphic, we can use it at *any* type -- in
-- particular, we can write propositions claiming that two *propositions* are
-- equal to each other:

#check (∀ P Q : Prop, (P ∧ Q) = (Q ∧ P) : Prop)

-- This is an equality between two conjunctions, which itself is also a
-- proposition. It states that commuted conjunctions are equal propositions.
-- However, we cannot prove this equality by reflexivity, as the two sides
-- don't compute to the same term, and we cannot proceed by cases on `P` or
-- `Q`, as they are not inductive.

/-- Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example (P Q : Prop) : P ∧ Q = Q ∧ P := by rfl

/-- Tactic `cases` failed -/
#guard_msgs (substring := true) in
example (P Q : Prop) : P ∧ Q = Q ∧ P := by cases P

-- However, we *can* prove that P ∧ Q implies Q ∧ P, and vice versa -- this is
-- the commutativity of conjunction that we have seen earlier.

#check (@and_comm : ∀ P Q : Prop, P ∧ Q ↔ Q ∧ P)

-- Since it would be convenient to be able to rewrite propositions from one
-- side of `↔` to the other, Lean provides an axiom to turn `↔` into `=`,
-- which is called *propositional extensionality* (`propext`).

#print propext

-- (Informally, an *extensional* property is one that pertains to observable
-- behavior. Thus, propositional extensionality means that a proposition's
-- identity is completely determined by what we can observe from it -- i.e.,
-- whether the proposition holds. We can state this more explicitly:)

theorem prop_true (P : Prop) (h : P) : P = True := by
  apply propext; exact ⟨fun _ => ⟨⟩, fun _ => h⟩

-- Lean provides an `ext` tactic that applies `propext` for us. We can use it
-- to show that commuted conjoined propositions are equal. Similarly, we can
-- use it to show that reassociated conjoined propositions are equal as well.

theorem and_comm_eq (P Q : Prop) : (P ∧ Q) = (Q ∧ P) := by
  ext; apply and_comm

theorem and_assoc_eq (P Q R : Prop) : ((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R)) := by
  ext; apply and_assoc

-- Here is an example of where using `=` instead of `↔` is more convenient: we
-- show that it's possible to "flip" three conjoined propositions.

-- This can be proven by constructing the `↔`, then destructing the `↔` in
-- `add_comm` and `add_assoc`, then applying them a few times. But this is a
-- lot of hassle, when the proof is conceptually simple: we flip `Q` and `R`,
-- then we flip that conjunction with `P`, and we finish by associativity. By
-- using `and_comm_eq`, this is easily done by rewriting equal propositions.

theorem and_comm_flip (P Q R : Prop) : (P ∧ Q ∧ R) ↔ (R ∧ Q ∧ P) := by
  rw [and_comm_eq Q R, and_comm_eq P, and_assoc_eq]

-- The pattern of deriving an equality of propositions out of `↔` then
-- rewriting by that equality is so common that Lean will implicitly cast `↔`
-- to `=`, allowing you to rewrite on `↔` directly. Notice that `rw` is also
-- close goals of the form `P ↔ P` by reflexivity.

theorem and_comm_flip' (P Q R : Prop) : (P ∧ Q ∧ R) ↔ (R ∧ Q ∧ P) := by
  rw [@and_comm Q R, @and_comm P, and_assoc]

-- Under the hood, this proof still uses `propext`, which you can check by
-- asking for all of the axioms used by a declaration.

#print axioms and_comm_flip

#print axioms and_comm_flip'

-- ### Exercise (1 star): mul_eq_0_ternary ⭐

theorem mul_eq_0_ternary (n m p : Nat) :
    n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  sorry

-- ### Exercise (2 stars): In_app_iff ⭐⭐

theorem In_app_iff (α : Type) (xs xs' : List α) (x : α) :
    In x (xs ++ xs') ↔ In x xs ∨ In x xs' := by
  sorry

-- ### Exercise (1 star): beq_neq ⭐

-- The following theorem is an alternative "negative" formulation of `beq_eq`
-- that is more convenient in certain situations. (We'll see examples in later
-- chapters.) Hint: `not_true_iff_false`.

theorem beq_neq_false (n m : Nat) : (n == m) = false ↔ n ≠ m := by
  sorry

-- ### Functional Extensionality

-- We can also write propositions claiming that two *functions* are equal to
-- each other. In some cases, we can also prove that two functions are equal
-- by reflexivity when both reduce to the same expression:

example : (fun x => x + 2) = (fun x => x + (pred 3)) := rfl

-- In general, functions can be equal for more interesting reasons. In common
-- mathematical practice, two functions `f` and `g` are considered equal if
-- they produce the same output on every input:

--   (∀ x, f x = g x) → f = g

-- This is known as *functional extensionality*, which Lean provides as
-- `funext`.

#check (fun f g => funext (f := f) (g := g) :
    ∀ {α β : Type} (f g : α → β), (∀ x, f x = g x) → f = g)

-- Here, functional extensionality means that a function's identity is
-- completely determined by what we can observe from it -- i.e., the results
-- we obtain after applying it. (Its full type is actually slightly more
-- general, and is defined in terms of a more fundamental concept called
-- *quotients* rather than added directly as an axiom, but we will only
-- discuss `funext` here. This is also why, when printing axioms for theorems
-- using `funext`, it will instead display a `Quot.sound` axiom.)

#print axioms funext

-- Now we can prove some intuitively obvious equalities about functions that
-- would otherwise not be provable without `funext`.

theorem add_comm_fun : (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
  apply funext; intro n
  apply funext; intro m
  exact add_comm n m

-- The `ext` tactic will also apply `funext` as many times as possible,
-- introducing all variables in one go. (The singular version of the tactic is
-- `ext1`.)

theorem add_comm_fun' : (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
  ext n m; exact add_comm n m

-- ### Exercise (4 stars): tr_rev_correct ⭐⭐⭐⭐

-- One problem with the definition of the list-reversing function `List.rev`
-- is that it performs a call to `++` on each step. Running `++` takes time
-- asymptotically linear in the size of the list, which means that `List.rev`
-- is asymptotically quadratic.

-- We can improve this with the following two-argument definition:

def rev_append {α} (xs1 xs2 : List α) : List α :=
  match xs1 with
  | [] => xs2
  | x1 :: xs1' => rev_append xs1' (x1 :: xs2)

theorem rev_append_nil {α} (xs : List α) : rev_append [] xs = xs := rfl

theorem rev_append_cons {α} (x : α) xs1 xs2 :
    rev_append (x :: xs1) xs2 = rev_append xs1 (x :: xs2) := rfl

abbrev tr_rev {α} (xs : List α) : List α := rev_append xs []

-- This version of `rev` is said to be *tail recursive*, because the recursive
-- call to the function is the last operation that needs to be performed
-- (i.e., we don't have to execute `++` after the recursive call); a decent
-- compiler will generate very efficient code in this case.

-- Prove that the two definitions are indeed equivalent.

-- FILL IN HERE

theorem tr_rev_correct {α} : @tr_rev α = @List.rev α := by
  sorry

-- ### Classical vs. Constructive Logic

-- We have seen that it is not possible to test whether or not a proposition
-- `P` holds while defining a Lean function. You may be surprised to learn
-- that a similar restriction applies in *proofs*! In other words, the
-- following intuitive reasoning principle is not derivable in Lean:

abbrev excluded_middle := ∀ P : Prop, P ∨ ¬ P

-- To understand operationally why this is the case, recall that, to prove a
-- statement of the form `P ∨ Q`, we use the `left` and `right` tactics, which
-- effectively require knowing which side of the disjunction holds. But the
-- universally quantified `P` in `excluded_middle` is an *arbitrary*
-- proposition, which we know nothing about. We don't have enough information
-- to choose which of `left` or `right` to apply.

-- However, in the special case where we happen to know that `P` is reflected
-- in some boolean term `b`, knowing whether it holds or not is trivial: we
-- just have to check the value of `b`.

theorem restricted_excluded_middle (P : Prop) (b : Bool) (h : P ↔ b = true) :
    P ∨ ¬ P := by
  cases b
  case false => right; rw [h]; intro; contradiction
  case true => left; rw [h]

-- In partiuclar, the excluded middle is valid for equations `n = m` between
-- natural numbers `n` and `m`.

theorem excluded_middle_nat_eq (n m : Nat) : n = m ∨ n ≠ m := by
  apply restricted_excluded_middle (n = m) (n == m)
  symm; apply beq_eq_true

-- Sadly, this trick only works for decidable propositions.

-- Logical systems in which excluded middle does not hold are referred to as
-- *constructive logics*. They are so called because to prove a proposition,
-- we must give a construction for it; for instance, a proof of `∃ x, P x` is
-- proven by providing a particular value of `x`.

-- Logical systems in which excluded middle does hold, such as ZFC set theory,
-- are referred to as *classical*. Lean provides classical reasoning
-- principles in the `Classical` library, including excluded middle.

#check (Classical.em : ∀ P, P ∨ ¬ P)

-- All classical reasoning principles in `Classical` are derived from one
-- axiom, the axiom of choice. This is the C in ZFC.

#print Classical.choice

/-- Classical.choice -/
#guard_msgs (substring := true) in
#print axioms Classical.em

-- Lean also provides a `by_cases` tactic that applies `Classical.em` on a
-- given proposition. Theorems proven using this tactic implicitly use
-- classical axioms.

theorem em : ∀ P, P ∨ ¬ P := by
  intro P; by_cases h : P
  /- h : P -/
  case pos => left; exact h
  /- h : ¬ P -/
  case neg => right; exact h

/-- Classical.choice -/
#guard_msgs (substring := true) in
#print axioms em

-- The following example illustrates why assuming the excluded middle may lead
-- to nonconstructive proofs:

-- *Claim*: There exist irrational numbers `a` and `b` such that `a ^ b` (`a`
-- to the power `b`) is rational.

-- *Proof*: It is not difficult to show that `sqrt 2` is irrational. So if
-- `sqrt 2 ^ sqrt 2` is rational, it suffices to take `a = b = sqrt 2` and we
-- are done. Otherwise, `sqrt 2 ^ sqrt 2` is irrational. In this case, we can
-- take `a = sqrt 2 ^ sqrt 2` and `b = sqrt 2`, since
-- `a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2`. QED.

-- Do you see what happened here? We used the excluded middle to consider
-- separately the cases where `sqrt 2 ^ sqrt 2` is rational and where it is
-- not, without knowing which one actually holds! Because of this, we finish
-- the proof knowing that such `a` and `b` exist, but not being sure of their
-- actual values.

-- As useful as constructive logic is, it does have its limitations: There are
-- many statements that can easily be proven in classical logic but that have
-- only much more complicated constructive proofs, and there are some that are
-- known to have no constructive proof at all! Fortunately, like functional
-- extensionality, the excluded middle is known to be compatible with Lean's
-- logic, allowing it to be added safely as an axiom. However, the results
-- that we cover in Logical Foundations can be developed entirely within
-- constructive logic.

-- It takes some practice to understand which proof techniques must be avoided
-- in constructive reasoning, but arguments by contradiction, in particular,
-- are infamous for leading to nonconstructive proofs. Here's a typical
-- example: suppose that we want to show that there exists `x` with some
-- property `P`, i.e., such that `P x`. We start by assuming that our
-- conclusion is false; that is, `¬ ∃ x, P x`. From this premise, it is not
-- hard to derive `∀ x, ¬ P x`. If we manage to show that this results in a
-- contradiction, we arrive at an existence proof without ever exhibiting a
-- value of `x` for which `P x` holds!

-- The technical flaw here, from a constructive standpoint, is that we claimed
-- to prove `∃ x, P x` using a proof of `¬ ¬ ∃ x, P x`. Allowing ourselves to
-- remove double negations from arbitrary statements is equivalent to assuming
-- the excluded middle law, as shown in one of the exercises below.

-- Once again, Lean's `Classical` library provides double negation
-- elimination, which relies on the `Classical.choice` axiom.

#check Classical.not_not

/-- Classical.choice -/
#guard_msgs (substring := true) in
#print axioms Classical.not_not

-- ### Exercise (3 stars): excluded_middle_irrefutable ⭐⭐⭐

-- The following theorem implies that it is always save to assume a
-- decidability axiom (i.e., an instance of excluded middle) for any
-- *particular* proposition `P`. Why? Because the negation of such an axiom
-- leands to a contradiction. If `¬ (P ∨ ¬ P)` were provable, then by
-- `de_morgan_not_or` as proven above, `P ∧ ¬ P` would be provable, which
-- would be a contradiction. So, it is safe to add `P ∨ ¬ P` as an axiom for
-- any particular `P`.

theorem excluded_middle_irrefutable (P : Prop) : ¬ ¬ (P ∨ ¬ P) := by
  sorry

-- ### Exercise (3 stars): not_exists_dist (Advanced) ⭐⭐⭐

-- It is a theorem of classical logic that the following two assertions are
-- equivalent:

--   ¬ ∃ x, ¬ P x
--   ∀ x, P x

-- The `dist_not_exists` theorem proves one side of this equivalence.
-- Interestingly, the other direction cannot be proven in constructive logic,
-- but we can prove it here using `by_cases`.

theorem not_exists_dist (α : Type) (P : α → Prop) :
    (¬ ∃ x, ¬ P x) → (∀ x, P x) := by
  sorry

-- ### Exercise (5 stars): classical_axioms ⭐⭐⭐⭐⭐

-- For those who like a challenge, here is an exercise adapted from the
-- Coq'Art book by Bertot and Casteran (p. 123). Each of the following five
-- statements, together with `excluded_middle`, can be considered as
-- characterizing classical logic. We can't prove any one of them in Lean
-- without `Classical`, but adding any *one* of them as an axiom allows us to
-- work classically.

-- To see this, prove that all six propositions (these five plus
-- `excluded_middle`) are equivalent.

-- Hint: Rather than considering all pairs of statements pairwise, prove a
-- single circular chain of implications that connects them all. You should
-- not use `by_cases`, as this implicitly introduces a dependency on
-- `excluded_middle`.

abbrev peirce := ∀ P Q : Prop, ((P → Q) → P) → P

abbrev not_not := ∀ P : Prop, ¬ ¬ P → P

abbrev de_morgan_not_and_not := ∀ P Q : Prop, ¬ (¬ P ∧ ¬ Q) → P ∨ Q

abbrev imp_or := ∀ P Q : Prop, (P → Q) → (¬ P ∨ Q)

abbrev consequentia_mirabilis := ∀ P : Prop, (¬ P → P) → P

-- FILL IN HERE


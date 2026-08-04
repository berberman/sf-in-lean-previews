import LF.Basics
import LF.Induction
import LF.Poly
import LF.Tactics
import LF.CustomTactics

import LF.SFLCompat

-- # Logic in Lean

-- Note to developers (before next release):
--     Unlike earlier chapters, there are probably too many
--     WORKINCLASSes in this chapter. BCP 20: But conversely
--     some more quizzes would be great!

-- Note to developers (Jonathan Chan  @ionathanch):
--     Classical axioms are more pervasive in Lean and the
--     section from Rocq needs to be rewritten to acknowledge
--     this and teach idiomatic style.
--     `BCP: Old comment -- might be out of date?`

-- Note to developers (Chris Henson  @chenson2018):
--     There's several style things to mention here like
--     `classical` vs. `open Classical`. `BCP: This one too?`

-- IMPORTBLOCK import LF.Basics IMPORTBLOCK import LF.Induction
-- IMPORTBLOCK import LF.Poly IMPORTBLOCK import LF.Tactics
-- IMPORTBLOCK import LF.CustomTactics

open Nat hiding add_succ mul_succ beq beq_eq beq_refl

-- (OA) : added these to use Lean's Nat.

open Nat (add add_comm add_assoc add_zero zero_add mul_zero mul_one zero_mul)

-- So far, we have seen:

-- - *propositions*: mathematical statements, so far only of 3
--   kinds:

--   - equality propositions (`e1 = e2`)
--   - implications (`P -> Q`)
--   - quantified propositions (`∀ x, P`)

-- - *proofs*: ways of presenting evidence for the truth of a
--   proposition

-- In this chapter we will introduce several more flavors of
-- both propositions and proofs.

-- Like everything in Lean, well-formed propositions have a
-- *type*:

-- -----------------------------------------------------------------------------

-- ## The `Prop` Type

#check (∀ n m : Nat, n + m = m + n : Prop)

-- Note that *all* syntactically well-formed propositions have
-- type `Prop` in Lean, regardless of whether they are true or
-- not.

-- Simply *being* a proposition is one thing; being *provable*
-- is a different thing!

#check (2 = 2 : Prop)
#check (3 = 2 : Prop)
#check (∀ n : Nat, n = 2 : Prop)

-- So far, we've seen one primary place where propositions can
-- appear: in `theorem` declarations.

theorem plus_2_2_is_4 : 2 + 2 = 4 := rfl

-- Propositions are first-class entities. For example, we can
-- name them:

def plus_claim : Prop := 2 + 2 = 4

#check (plus_claim : Prop)

theorem plus_claim_is_true : plus_claim := rfl

-- We can also write *parameterized* propositions -- that is,
-- functions that take arguments of some type and return a
-- proposition.

def is_three (n : Nat) : Prop := n = 3

#check (is_three : Nat → Prop)

-- In Lean, functions that return propositions are said to
-- define *properties* of their arguments.

-- For instance, here's a (polymorphic) property defining the
-- familiar notion of an *injective function*.

def injective {α β} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

theorem succ_inj' : injective succ := by
  intro x y H; injection H

-- The familiar equality operator `=` is a (binary) function
-- that returns a `Prop`. The expression `n = m` is notation
-- for `Eq n m`. Because `eq` can be used with elements of any
-- type, it is also polymorphic:

-- Note to developers (Jonathan Chan  @ionathanch):
--     Actually it quantifies over `Sort`, where
--     `Prop = Sort 0` and `Type u = Sort (u + 1)`. Not
--     something that needs teaching right at this moment, but
--     they'll see `Sort` when hovering.

#check (Eq : ∀ {α : Type}, α → α → Prop)

#check pred

-- As a convenience, Lean will cast booleans by equating them
-- to `true`, which is why checking them against `Prop`
-- succeeds. It also casts boolean equalities to propositions
-- by equating to `true`, and boolean inequalities by equating
-- to `false`. For clarity, we will avoid relying on these
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

-- The *conjunction*, or *logical and*, of propositions `A` and
-- `B` is written `A ∧ B`; it represents the claim that both
-- `A` and `B` are true.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  /- A proof of a conjunction is a pair of proofs of the two components.
      To prove a conjunction, we build a pair using `constructor`. -/
  constructor
  case left  => /- 3 + 4 = 7 -/ rfl
  case right => /- 2 * 2 = 4 -/ rfl

-- The constructor for conjunction is `And.intro`, which
-- concludes that `A ∧ B` given that `A` and `B` hold
-- individually.

#check (And.intro : ∀ {α β : Prop}, α → β → α ∧ β)

-- We can also apply the constructor for the conjunction
-- explicitly.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  case left  => /- 3 + 4 = 7 -/ rfl
  case right => /- 2 * 2 = 4 -/ rfl

-- Rather than applying the constructor, we can explicitly
-- provide the arguments to the constructor as an `exact`
-- proof.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact And.intro rfl rfl

-- We can also use Lean's anonymous constructor notation ⟨...,
-- ...⟩, which works on constructors for proofs as well.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact ⟨rfl, rfl⟩

-- So much for proving conjunctive statements. To go in the
-- other direction -- i.e., to *use* a conjunctive hypothesis
-- to help prove something else -- we can use `let` to obtain
-- the components.

example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  sorry

-- As usual, we can also match on `h` right at the point where
-- we introduce it, instead of introducing and then destructing
-- it:

example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro ⟨hn, hm⟩
  rw [hn, hm]

-- For the present example, both ways work. But in other
-- situations, we may wind up with a conjunctive hypothesis in
-- the middle of a proof...

example (n m : Nat) (h : n + m = 0) : n * m = 0 := by
  sorry

-- The infix notation `∧` is actually just syntactic sugar for
-- `And A B`. That is, `And` is a Lean operator that takes two
-- propositions as arguments and yields a proposition.

#check (And : Prop → Prop → Prop)

-- ### Disjunction

-- Another important connective is the *disjunction*, or
-- *logical or*, of two propositions: `A ∨ B` is true when
-- either `A` or `B` is. This infix notation stands for
-- `Or A B`, where `Or : Prop -> Prop -> Prop`.

-- To use a disjunctive hypothesis in a proof, we proceed by
-- case analysis -- which, as with other data types like `Nat`,
-- is done using `cases`. The two cases are `inl` (for "left
-- injection", or "in the left case") and `inr` (for "right
-- injection", or "in the right case").

theorem factor_is_zero (n m : Nat) (h : n = 0 ∨ m = 0) : n * m = 0 := by
  cases h
  /- `n = 0` -/
  case inl hn => rw [hn, zero_mul]
  /- `m = 0` -/
  case inr hm => rw [hm, mul_zero]

-- Rather than performing case analysis via `cases`, we can
-- also use `obtain` to match on the two possible injections,
-- much like with `let`.

theorem and_is_false (b1 b2 : Bool) (h : (b1 = false) ∨ (b2 = false)) :
    (b1 && b2) = false := by
  obtain hb1 | hb2 := h
  case inl => rw [hb1, Bool.false_and]
  case inr => rw [hb2, Bool.and_false]

-- Conversely, to show that a disjunction holds, it suffices to
-- show that one of its sides holds. This can be done via the
-- tactics `left` and `right`. As their names imply, the first
-- one requires proving the left side of the disjunction, while
-- the second requires proving the right side. Here is a
-- trivial use...

theorem or_intro_l (P Q : Prop) (h : P) : P ∨ Q := by
  left; exact h

-- ... and here is a slightly more interesting example
-- requiring both `left` and `right`:

theorem zero_or_succ (n : Nat) : n = 0 ∨ n = pred (succ n) := by
  sorry

-- ### Exercise (2 stars): mul_is_zero ⭐⭐

theorem mul_is_zero (n m : Nat) (h : n * m = 0) : n = 0 ∨ m = 0 := by
  sorry

-- ### Exercise (1 star): or_commute ⭐

theorem or_commute (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  sorry

-- ### Falsehood and Negation

-- Up to this point, we have mostly been concerned with proving
-- "positive" statements -- addition is commutative, appending
-- lists is associative, etc. We are sometimes also interested
-- in negative results, demonstrating that some proposition is
-- *not* true. Such statements are expressed with the logical
-- negation operator `¬`, which a prefix notation for `Not`.

-- To see how negation works, recall the *principle of
-- explosion* from the `Tactics` chapter, which asserts that,
-- if we assume a contradiction, then any other proposition can
-- be derived.

-- Following this intuition, we could define `¬ P` ("not `P`")
-- as `∀ Q, P → Q`. Lean makes an equivalent but slightly
-- different choice, defining `~ P` as `P → False`, where
-- `False` is a specific unprovable proposition defined in the
-- standard library.

#check (Not : Prop → Prop)
#print Not

example : ∀ P, Not P = (P → False) := by intro; rfl
example : ∀ P, (¬ P) = (P → False) := by intro; rfl

-- Since `False` is a contradictory proposition, the principle
-- of explosion also applies to it. If we can get `False` into
-- the context, we can use `cases` on it to complete any goal:

theorem ex_falso_quodlibet (P : Prop) (h : False) : P := by
  cases h

-- Inequality is a very common form of negated statement, so
-- there is a special notation for it: `≠`, which is infix
-- notation for `Ne`.

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

-- It takes a little practice to get used to working with
-- negation in Lean. Even though *you* may see perfectly well
-- why a claim involving negation holds, it can be a little
-- tricky at first to see how to make Lean understand it!

-- Here are proofs of a few familiar facts to help get you
-- warmed up.

theorem not_False : ¬ False := by
  intro h; exact h

theorem contradiction_implies_anything (P Q : Prop) (h : P ∧ ¬ P) : Q := by
  sorry

theorem double_neg (P : Prop) (hP : P) : ¬ ¬ P := by
  sorry

-- Since inequality involves a negation, getting comfortable
-- with it also often requires a little practice.

-- A useful trick: if you are trying to prove a nonsensical
-- goal, apply `ex_falso_quodlibet` to change the goal to
-- `False`. This makes it easier to use assumptions of the form
-- `¬ P`, and in particular of the form `x ≠ y`.

theorem not_true_is_false (b : Bool) (h : b ≠ true) : b = false := by
  -- FOLD
  cases b
  case false => rfl
  case true =>
    unfold Ne Not at h
    apply ex_falso_quodlibet
    apply h; rfl
  -- /FOLD

-- Note to developers:
--     HIDE: CH: I don't think this was the original intention,
--     but some of these quizzes got unnecessarily tricky and
--     pedantic. For instance, the first quiz below makes a big
--     distinction between using the destruct tactic and
--     destructing using an intro pattern, even if conceptually
--     there is no difference. Could it be that these quizzes
--     were devised when intro patterns were not taught in the
--     course and an update would be helpful now? Since I don't
--     see the gain in tricking a majority of students in
--     giving the "wrong" answer, even if it's a perfectly
--     sensible one.

-- _Quiz:_

-- To prove the following proposition, which tactics will we
-- need besides `intro`, `apply`, and `exact`?

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

-- To prove the following proposition, which tactics will we
-- need besides `intro`, `apply`, and `exact`?

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

-- To prove the following proposition, which tactics will we
-- need besides `intro`, `apply`, and `exact`?

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

-- To prove the following proposition, which tactics will we
-- need besides `intro`, `apply`, and `exact`?

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

-- To prove the following proposition, which tactics will we
-- need besides `intro`, `apply`, and `exact`?

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

-- Besides `False`, Lean's standard library also defines
-- `True`, a proposition that is trivially true. To prove it,
-- we use the constructor `True.intro` explicitly, or the
-- anonymous constructor `⟨⟩`, or the `constructor` tactic.

example : True := by exact True.intro
example : True := True.intro
example : True := by exact ⟨⟩
example : True := ⟨⟩
example : True := by constructor

-- Unlike `False`, which is used extensively, `True` is used
-- relatively rarely: it is trivial (and therefore
-- uninteresting) to prove as a goal, and it provides no useful
-- information when it appears as a hypothesis.

-- ### Logical Equivalence

-- The handy "if and only if" connective, which asserts that
-- two propositions have the same truth value, is a structure
-- containing the two implication directions. `P ↔ Q` is
-- notation for `Iff P Q`.

#print Iff

#check (fun α β : Prop => α ↔ β : Prop → Prop → Prop)

theorem iff_sym (P Q : Prop) (h : P ↔ Q) : (Q ↔ P) := by
  sorry

theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  constructor
  case mp => apply not_true_is_false
  case mpr => intro h; rw [h]; intro h'; contradiction

-- ### Exercise (1 star): iff_properties ⭐

-- Using the above proof that `↔` is symmetric (`iff_sym`) as a
-- guide, prove that it is also reflexive and transitive.

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

theorem mul_eq_0 (n m : Nat) :
    n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  case mp => apply mul_is_zero
  case mpr => apply factor_is_zero

-- ### Existential Quantification

#check (Exists : ∀ {T : Type}, (T → Prop) → Prop)

abbrev Even x := ∃ n : Nat, x = double n

#check (Even : Nat → Prop)

example : Even 4 := by exists 2
  -- `4 = double 2` holds by `rfl`,
  -- but is proven automatically by `exists`

-- Conversely, if we have an existential hypothesis `∃ x, P` in
-- the context, can destruct it to obtain a witness `x` and a
-- hypothesis stating that `P` holds of `x`.

example n : (∃ m, n = m + 4) → (∃ o, n = o + 2) := by
  intro ⟨m, hm⟩
  exists (m + 2)

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

-- Fundamental connectives we've been using since the
-- beginning:

-- - equality (`e1 = e2`)
-- - implication (`P → Q`)
-- - universal quantification (`∀ x, P`)

-- -----------------------------------------------------------------------------

-- ## Programming with Propositions

-- What does it mean to say that "an element `x` occurs in a
-- list `l`"?

-- - If `l` is the empty list, then `x` cannot occur in it, so
--   the property "`x` appears in `l`" is simply false.

-- - Otherwise, `l` has the form `[x' :: l']`. In this case, `x`
--   occurs in `l` if it is equal to `x'` or if it occurs in
--   `l'`.

-- We can translate this directly into a straightforward
-- recursive function taken an element and a list and
-- returning... a proposition!

def In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'

theorem In_nil {α} (x : α) : In x [] = False := rfl

theorem In_cons {α} (x x' : α) (xs : List α) : In x (x' :: xs) = (x = x' ∨ In x xs) := rfl

-- When `In` is applied to a concrete list, it exapnds into a
-- concrete sequence of nested disjunctions.

example : In 4 [1, 2, 3, 4, 5] := by
  sorry

example (n : Nat) (h : In n [2, 4]) : ∃ n' : Nat, n = 2 * n' := by
  sorry
    /- (Notice the use of the empty pattern to discharge the last case.) -/

-- We can also reason about more generic statements involving
-- `In`.

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

-- ## Applying Theorems to Arguments

-- Lean also treats *proofs* as first-class objects!

-- We have seen that we can use `#check` to ask Lean whether an
-- expression has a given type:

#check (add : Nat → Nat → Nat)

-- We can also use it to check what theorem a particular
-- identifier refers to:

#check add_comm

#check add_assoc

-- Lean checks the *statements* of the `add_comm` and
-- `add_assoc` theorems in the same way that it checks the
-- *type* of any term (e.g. `add`). Leaving off the colon and
-- the type, Lean prints these types in the infoview for us.

-- Why?

-- The reason is that the identifier `add_comm` actually refers
-- to a *proof object* -- a logical derivation establishing the
-- truth of the statement `∀ n m, n + m = m + n`. The type of
-- this object is the proposition that it is a proof of.

-- The type of an ordinary function tells us what we can do
-- with it.

-- - If we have a term of type `Nat → Nat → Nat`, we can give it
--   two `Nat`s as arguments and get a `Nat` back. Similarly, the
--   statement of a theorem tells us what we can use that theorem
--   for.

-- - If we have a term of type `∀ n m, n = m → n + n = m + n`,
--   and we provide it two numbers `n` and `m` and a third
--   "arugment" of type `n = m`, we get back a proof object of
--   type `n + n = m + m`.

-- Lean actually allows us to *apply* a theorem as if it were a
-- function. This is often handy in proof scripts -- e.g.,
-- suppose we want to prove the following:

example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm]
  rw [add_comm]
  sorry

-- It appears at first sight that we ought to be able to prove
-- this be rewriting with `add_comm` twice to make the two
-- sides match. The problem is that the second rewrite undoes
-- the effect of the first, leaving us back where we started...

-- We can fix this by applying `add_comm` to the arguments we
-- want it to be instantiated with, in much the same way as we
-- apply a polymorphic function to a type argument. Then the
-- rewrite is forced to happen exactly where we want it.

example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm]
  rw [add_comm z y]

-- The fact that implications are functions means we can prove
-- them by explicitly providing a function.

theorem identity {P : Prop} : P → P := fun h => h

namespace FunctionTheoremQuiz

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

-- example (n m : Nat) (h1 : n = m) (h2 : m = 42) (trans*eq : ∀
-- (α : Type) (a b c : α), a = b → b = c → a = c) : True := by
-- have : n = 42 := trans*eq Nat n m 42 h1 h2

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

end FunctionTheoremQuiz

-- ## Working with Decidable Properties

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     This will need better typesetting...

-- We've seen two different ways of expressing logical claims
-- in Lean: with *booleans* (of type `Bool`), and with
-- *propositions* (of type `Prop`). Here are the key
-- differences between `Bool` and `Prop`:

-- | | `Bool` | `Prop` | | ------------------- | ------ |
-- ------ | | decidable? | yes | no | | useable with match? |
-- yes | no |

-- Since functions in Lean by default must terminate on all
-- inputs, a terminating function of type `Nat → Bool` is a
-- *decision procedure* -- i.e., it yields `true` or `false` on
-- all inputs.

-- For example, `even : Nat → Bool` is a decision procedure for
-- the property "is even".

-- Since `Prop` includes *both* decidable and undecidable
-- properties, we have two options when we want to formalize a
-- property that happens to be decidable: we can express it
-- either as a boolean computation, or as a function into
-- `Prop`.

-- For instance, to claim that a number `n` is even, we can say
-- either that `even n` evaluates to `true`...

example : even 42 = true := rfl

-- ... or that there exists some `k` such that `n = double k`.

example : Even 42 := by dsimp [Even]; exists 21

-- Of course, it would be deeply strange if these two
-- characterizations of evenness did not describe the same set
-- of natural numbers! Fortunately, they do!

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

-- In view of this theorem, we can say that the boolean
-- computation `even n` is *reflected* in the truth of the
-- proposition `∃ k, n = double k`.

-- Similarly, to state that two numbers `n` and `m` are equal,
-- we can say either

-- 1. that `n == m` returns `true`, or
-- 2. that `n = m`.

-- Again, these two notions are equivalent:

-- (For the reverse direction we need the simple fact that `==`
-- is reflexive.)

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     @dsainati1 wonders whether this tactic has been
--     explained.

theorem beq_refl (n : Nat) : (n == n) = true := decide_eq_true rfl

theorem beq_eq_true (n1 n2 : Nat) :
    (n1 == n2) = true ↔ n1 = n2 := by
  -- FOLD
  constructor
  case mp => apply beq_eq
  case mpr => intro H; rw [H, beq_refl]
  -- /FOLD

-- So what should we do in situations where some claim could be
-- formalized as either a proposition or a boolean computation?
-- Which should we choose?

-- In general, *both* can be useful. For example, booleans are
-- more useful for defining functions, since we can test
-- whether they are true using conditional expressions.

abbrev is_even_prime (n : Nat) : Bool :=
  bif n == 2 then true else false

-- Note to developers (Jonathan Chan  @ionathanch):
--     This was originally 1000 but Lean's default recursion
--     depth is not large enough to reduce `double 50` lol

-- The most direct way to prove this is to give the value of
-- `k` explicitly.

example : Even 100 := by
  exists 50

-- The proof of the corresponding boolean statement is simpler,
-- because we don't have to invent the witness `50`:
-- computation does it for us!

example : even 100 := rfl

-- Now, the useful observation is that, since the two notions
-- are equivalent, we can use the boolean formulation to prove
-- the other one without mentioning the value 500 explicitly:

example : Even 100 := by
  let ⟨H, _⟩ := even_bool_prop 100
  apply H; rfl

-- Although we haven't gained much in terms of proof-script
-- simplicity in this case, larger proofs can often be made
-- considerably simpler by the use of reflection.

-- Note to developers (Jonathan Chan  @ionathanch):
--     Is there a Lean version? Or maybe just mention Rocq?

-- As an extreme example, a famous mechanized proof of the even
-- more famous *four colour theorem* uses reflection ot reduce
-- the analysis of hundreds of different cases to a boolean
-- computation.

-- Another advantage of booleans is that the *negation* of a
-- claim about booleans is straightforward to state and (when
-- true) to prove: simply slip the expected boolean result.

example : even 101 = false := rfl

-- In contrast, propositional negation can be difficult to work
-- with directly. For example, suppose we state the nonevenness
-- of `101` propositionally:

-- Proving this directly -- by assuming that there is some `n`
-- such that `101 = double n` and then somehow reasoning to a
-- contradiction -- would be rather complicated.

-- But if we convert it to a claim about the boolean `even`
-- function, we can let Lean do the work for us.

example : ¬ Even 101 := by
  sorry

-- Conversely, there are situations where it can be easier to
-- work with propositions rather than booleans. In particular,
-- knowing that `(n == m) = true` is generally of little direct
-- help in the middle of a proof involving `n` and `m`. But if
-- we convert the statement to the equivalent form `n = m`,
-- then we can easily rewrite with it.

theorem add_beq_true (n m p : Nat) (h : (n == m) = true) :
    (n + p == m + p) = true := by
  sorry

-- -----------------------------------------------------------------------------

-- ## The Logic of Lean

-- Lean's logical core is a "metalanguage for mathematics" in
-- the same sense as familiar foundations for paper-and-pencil
-- math, like Zermelo–Fraenkel Set Theory (ZFC).

-- Mostly, the differences are not too important, but a few
-- points are useful to understand.

-- ### Propositional Extensionality

-- Lean's logic is quite minimalistic. This means that on
-- occasionally encounters cases where translating standard
-- mathematical reasoning into Lean is cumbersome -- or even
-- impossible -- unless we enrich its core logic with
-- additional axioms.

-- A first instance has to do with equality of propositions.

#check (∀ P Q : Prop, (P ∧ Q) = (Q ∧ P) : Prop)

-- This is an equality between two conjunctions, which itself
-- is also a proposition. It states that commuted conjunctions
-- are equal propositions. However, we cannot prove this
-- equality by reflexivity, as the two sides don't compute to
-- the same term, and we cannot proceed by cases on `P` or `Q`,
-- as they are not inductive.

/-- Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example (P Q : Prop) : P ∧ Q = Q ∧ P := by rfl

/-- Tactic `cases` failed -/
#guard_msgs (substring := true) in
example (P Q : Prop) : P ∧ Q = Q ∧ P := by cases P

-- However, we *can* prove that P ∧ Q implies Q ∧ P, and vice
-- versa -- this is the commutativity of conjunction that we
-- have seen earlier.

#check (@and_comm : ∀ P Q : Prop, P ∧ Q ↔ Q ∧ P)

-- Since it would be convenient to be able to rewrite
-- propositions from one side of `↔` to the other, Lean
-- provides an axiom to turn `↔` into `=`, which is called
-- *propositional extensionality* (`propext`).

#print propext

-- Lean provides an `ext` tactic that applies `propext` for us.
-- We can use it to show that commuted conjoined propositions
-- are equal. Similarly, we can use it to show that
-- reassociated conjoined propositions are equal as well.

theorem and_comm_eq (P Q : Prop) : (P ∧ Q) = (Q ∧ P) := by
  ext; apply and_comm

theorem and_assoc_eq (P Q R : Prop) : ((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R)) := by
  ext; apply and_assoc

-- Here is an example of where using `=` instead of `↔` is more
-- convenient: we show that it's possible to "flip" three
-- conjoined propositions.

-- This can be proven by constructing the `↔`, then destructing
-- the `↔` in `add_comm` and `add_assoc`, then applying them a
-- few times. But this is a lot of hassle, when the proof is
-- conceptually simple: we flip `Q` and `R`, then we flip that
-- conjunction with `P`, and we finish by associativity. By
-- using `and_comm_eq`, this is easily done by rewriting equal
-- propositions.

theorem and_comm_flip (P Q R : Prop) : (P ∧ Q ∧ R) ↔ (R ∧ Q ∧ P) := by
  rw [and_comm_eq Q R, and_comm_eq P, and_assoc_eq]

-- The pattern of deriving an equality of propositions out of
-- `↔` then rewriting by that equality is so common that Lean
-- will implicitly cast `↔` to `=`, allowing you to rewrite on
-- `↔` directly. Notice that `rw` is also close goals of the
-- form `P ↔ P` by reflexivity.

theorem and_comm_flip' (P Q R : Prop) : (P ∧ Q ∧ R) ↔ (R ∧ Q ∧ P) := by
  rw [@and_comm Q R, @and_comm P, and_assoc]

-- Under the hood, this proof still uses `propext`, which you
-- can check by asking for all of the axioms used by a
-- declaration.

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

-- The following theorem is an alternative "negative"
-- formulation of `beq_eq` that is more convenient in certain
-- situations. (We'll see examples in later chapters.) Hint:
-- `not_true_iff_false`.

theorem beq_neq_false (n m : Nat) : (n == m) = false ↔ n ≠ m := by
  sorry

-- ### Functional Extensionality

-- We can also write propositions claiming that two *functions*
-- are equal to each other. In some cases, we can also prove
-- that two functions are equal by reflexivity when both reduce
-- to the same expression:

example : (fun x => x + 2) = (fun x => x + (pred 3)) := rfl

-- In general, functions can be equal for more interesting
-- reasons. In common mathematical practice, two functions `f`
-- and `g` are considered equal if they produce the same output
-- on every input:

--   (∀ x, f x = g x) → f = g

-- This is known as *functional extensionality*, which Lean
-- provides as `funext`.

#check (fun f g => funext (f := f) (g := g) :
    ∀ {α β : Type} (f g : α → β), (∀ x, f x = g x) → f = g)

-- Now we can prove some intuitively obvious equalities about
-- functions that would otherwise not be provable without
-- `funext`.

theorem add_comm_fun : (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
  apply funext; intro n
  apply funext; intro m
  exact add_comm n m

-- The `ext` tactic will also apply `funext` as many times as
-- possible, introducing all variables in one go. (The singular
-- version of the tactic is `ext1`.)

theorem add_comm_fun' : (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
  ext n m; exact add_comm n m

-- ### Classical vs. Constructive Logic

-- The following reasoning principle is *not* derivable in
-- Lean:

abbrev excluded_middle := ∀ P : Prop, P ∨ ¬ P

-- Logical systems in which excluded middle does not hold are
-- referred to as *constructive logics*. They are so called
-- because to prove a proposition, we must give a construction
-- for it; for instance, a proof of `∃ x, P x` is proven by
-- providing a particular value of `x`.

-- Logical systems in which excluded middle does hold, such as
-- ZFC set theory, are referred to as *classical*. Lean
-- provides classical reasoning principles in the `Classical`
-- library, including excluded middle.

#check (Classical.em : ∀ P, P ∨ ¬ P)


import LF.Basics
import LF.Induction
import LF.Poly
import LF.Tactics
import LF.CustomTactics

import SFLCompat

--  # Logic in Lean

--  We have now seen many examples of factual claims (i.e., *propositions*)
--  and ways of presenting evidence of their truth (*proofs*). In
--  particular, we have worked extensively with equality propositions
--  (`e1 = e2`), implications (`a → b`), and quantified propositions
--  (`∀ x, a`). In this chapter, we will see how Lean can be used to carry
--  out other familiar forms of logical reasoning.
--
--  Before diving into details, we should talk a bit about the status of
--  mathematical statements in Lean. Lean is a *typed* language, which
--  means that every sensible expression has an associated type. Logical
--  claims are no exception: any statement we might try to prove in Lean
--  has a type, namely `Prop`, the type of *propositions*. We can see this
--  with the `#check` command:

--  ## The `Prop` Type

#check (∀ n m : Nat, n + m = m + n : Prop)

--  Note that *all* syntactically well-formed propositions have type `Prop`
--  in Lean, regardless of whether they are true or not.
--
--  Simply *being* a proposition is one thing; being *provable* is a
--  different thing!

#check (2 = 2 : Prop)
#check (3 = 2 : Prop)
#check (∀ n : Nat, n = 2 : Prop)

--  Indeed, propositions don't just have types — they are *first-class*
--  entities that can be manipulated in all the same ways as any of the
--  other things in Lean's world.

--  So far, we've seen one primary place where propositions can appear: in
--  `theorem` declarations.

theorem plus_2_2_is_4 : 2 + 2 = 4 := rfl

--  But propositions can be used in other ways. For example, we can give a
--  name to a proposition using a `def`, just as we give names to other
--  kinds of expressions.

def PlusClaim : Prop := 2 + 2 = 4

#check PlusClaim

--  Output:
--    PlusClaim : Prop

--  We can later use this name in any situation where a proposition is
--  expected — for example, as the claim in a `theorem` declaration.

theorem plusClaim_is_true : PlusClaim := rfl

--  We can also write *parameterized* propositions — that is, functions
--  that take arguments of some type and return a proposition.

--  For instance, the following function takes a number and returns a
--  proposition asserting that this number is equal to three:

def Nat.IsThree (n : Nat) : Prop := n = 3

#check (Nat.IsThree)

--  Output:
--    Nat.IsThree : Nat → Prop

--  In Lean, functions that return propositions are said to define
--  *properties* of their arguments.
--
--  For instance, here's a (polymorphic) property defining the familiar
--  notion of an *injective function*.

def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

theorem succ_inj' : Injective Nat.succ := by
  intro x y h
  injection h

--  The familiar equality operator `=` is a (binary) function that returns
--  a `Prop`. The expression `n = m` is notation for `Eq n m`. Because `Eq`
--  can be used with elements of any type, it is also polymorphic:

#check Eq

--  Output:
--    Eq.{u_1} {α : Sort u_1} : α → α → Prop

--  As a convenience, Lean will cast booleans by equating them to `true`,
--  which is why checking them against `Prop` succeeds. It also casts
--  boolean equalities to propositions by equating to `true`, and boolean
--  inequalities by equating to `false`. For clarity, we will avoid relying
--  on these implicit casts.

#check (false : Prop)

--  Output:
--    false = true : Prop

#check (true : Prop)

--  Output:
--    true = true : Prop

--   ----------------------------------------

--  _Quiz:_

--  What is the type of the following expression?
--
--      Nat.pred 1 = 0
--
--  1. `Prop`
--  2. `Nat → Prop`
--  3. `∀ n : Nat, Prop`
--  4. `Nat → Nat`
--  5. Not typeable

--   ----------------------------------------

--  _Quiz:_

--  What is the type of the following expression?
--
--      ∀ n : Nat, (n + 1).pred = n
--
--  1. `Prop`
--  2. `Nat → Prop`
--  3. `∀ n : Nat, Prop`
--  4. `Nat → Nat`
--  5. Not typeable

--   ----------------------------------------

--  _Quiz:_

--  What is the type of the following expression?
--
--      ∀ n : Nat, n.pred + 1
--
--  1. `Prop`
--  2. `Nat → Prop`
--  3. `∀ n : Nat, Prop`
--  4. `Nat → Nat`
--  5. Not typeable

--   ----------------------------------------

--  _Quiz:_

--  What is the type of the following expression?
--
--      fun n : Nat => n.pred + 1
--
--  1. `Prop`
--  2. `Nat → Prop`
--  3. `∀ n : Nat, Prop`
--  4. `Nat → Nat`
--  5. Not typeable

--   ----------------------------------------

--  _Quiz:_

--  What is the type of the following expression?
--
--      fun n : Nat => n.pred + 1 = n
--
--  1. `Prop`
--  2. `Nat → Prop`
--  3. `∀ n : Nat, Prop`
--  4. `Nat → Nat`
--  5. Not typeable

--   ----------------------------------------

--  _Quiz:_

--  Which of the following is *not* a proposition?
--
--  1. `3 + 2 = 4`
--  2. `3 + 2 = 5`
--  3. `3 + 2 == 5`
--  4. `(3 + 2 == 4) = false`
--  5. `∀ n, (3 + 2 == n) = true → n = 5`
--  6. All of these are propositions

--   ----------------------------------------

--  ## Logical Connectives

--  ### Conjunction

--  The *conjunction*, or *logical and*, of propositions `a` and `b` is
--  written `a ∧ b`; it represents the claim that both `a` and `b` are
--  true.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  /- A proof of a conjunction is a pair of proofs of the two components.
      To prove a conjunction, we build a pair using `constructor`. -/
  constructor
  · rfl /- 3 + 4 = 7 -/
  · rfl /- 2 * 2 = 4 -/

--  The constructor for conjunction is `And.intro`, which concludes that
--  `a ∧ b` given that `a` and `b` hold individually.

#check And.intro

--  Output:
--    And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

--  We can also apply the constructor for the conjunction explicitly.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  · rfl /- 3 + 4 = 7 -/
  · rfl /- 2 * 2 = 4 -/

--  Rather than applying the constructor, we can explicitly provide the
--  arguments to the constructor as an `exact` proof.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact And.intro rfl rfl

--  We can also use Lean's anonymous constructor notation `⟨..., ...⟩`,
--  which works on constructors for proofs as well.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact ⟨rfl, rfl⟩

--  ### Exercise (2 stars): add_is_zero ⭐⭐

theorem Nat.add_is_zero (n m : Nat) : n + m = 0 → n = 0 ∧ m = 0 := by
  sorry

--  So much for proving conjunctive statements. To go in the other
--  direction — i.e., to *use* a conjunctive hypothesis to help prove
--  something else — we can use `obtain` to obtain the components.

example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro h
  obtain ⟨hn, hm⟩ := h
  rw [hn, hm]

--  We can also match on `h` right at the point where we introduce it,
--  instead of introducing and then destructing it:

example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro ⟨hn, hm⟩
  rw [hn, hm]

--  You may wonder why we bothered packing the two hypotheses `n = 0` and
--  `m = 0` into a single conjunction, since we could also have stated the
--  theorem with two separate premises:

example (n m : Nat) : n = 0 → m = 0 → n + m = 0 := by
  intro hn hm
  rw [hn, hm]

--  For this specific theorem, both formulations are fine. But it's
--  important to understand how to work with conjunctive hypotheses because
--  conjunctions often arise from intermediate steps in proofs, especially
--  in larger developments. Here's a simple example:

example (n m : Nat) (h : n + m = 0) : n * m = 0 := by
  apply Nat.add_is_zero at h
  obtain ⟨hn, hm⟩ := h
  rw [hm]
  rfl

--  Another common situation is that we know `a ∧ b` but in some context we
--  need just `a` or just `b`. In such cases we can use an underscore
--  pattern `_` to indicate that the unneeded conjunct should just be
--  thrown away.

theorem proj1 (a b : Prop) (h : a ∧ b) : a := by
  obtain ⟨hP, _⟩ := h
  exact hP

--  Conjunctions come with their own built-in projections, `.left` and
--  `.right`, which we can use instead of pattern matching.

theorem left (a b : Prop) (h : a ∧ b) : a := by
  exact h.left

--  ### Exercise (1 star): proj2 (Optional) ⭐

theorem right (a b : Prop) (h : a ∧ b) : b := by
  sorry

--  Finally, we sometimes need to rearrange the order of conjunctions
--  and/or the grouping of multi-way conjunctions. We can see this at work
--  in the proofs of the following commutativity and associativity
--  theorems.

theorem and_commute (a b : Prop) (h : a ∧ b) : b ∧ a := by
  constructor
  · exact h.right
  · exact h.left

--  The anonymous constructor allows us to write a much terser proof.

theorem and_commute' (a b : Prop) (h : a ∧ b) : b ∧ a := by
  exact ⟨h.right, h.left⟩

--  In the following proof of associativity, notice how projections can be
--  chained in sequence to obtain components of nested conjunctions.
--  Complete the proof.

--  ### Exercise (1 star): and_associate ⭐

theorem and_associate (a b c : Prop) (h : a ∧ (b ∧ c)) : (a ∧ b) ∧ c := by
  constructor
  · sorry
  · exact h.right.right

--  The infix notation `∧` is actually just syntactic sugar for `And a b`.
--  That is, `And` is a Lean operator that takes two propositions as
--  arguments and yields a proposition.

#check And

--  Output:
--    And (a b : Prop) : Prop

--  ### Disjunction

--  Another important connective is the *disjunction*, or *logical or*, of
--  two propositions: `a ∨ b` is true when either `a` or `b` is. This infix
--  notation stands for `Or a b`, where `Or : Prop -> Prop -> Prop`.
--
--  To use a disjunctive hypothesis in a proof, we proceed by case analysis
--  — which, as with other data types like `Nat`, is done using `cases`.
--  The two cases are `inl` (for "left injection", or "in the left case")
--  and `inr` (for "right injection", or "in the right case").

theorem Nat.factor_is_zero (n m : Nat) (h : n = 0 ∨ m = 0) : n * m = 0 := by
  cases h with
  /- `n = 0` -/
  | inl hn => rw [hn, Nat.zero_mul]
  /- `m = 0` -/
  | inr hm => rw [hm, Nat.mul_zero]

--  We can see in this example that, when we perform case analysis on a
--  disjunction `a ∨ b`, we must separately discharge two proof
--  obligations, each showing that the conclusion holds under a different
--  assumption - `a` in the first subgoal and `b` in the second.

--  Rather than performing case analysis via `cases`, we can also use
--  `obtain` to match on the two possible injections, much like with
--  `obtain` and `∧`.

theorem and_is_false (b1 b2 : Bool) (h : (b1 = false) ∨ (b2 = false)) :
    (b1 && b2) = false := by
  obtain hb1 | hb2 := h
  · rw [hb1, Bool.false_and]
  · rw [hb2, Bool.and_false]

--  Conversely, to show that a disjunction holds, it suffices to show that
--  one of its sides holds. This can be done via the tactics `left` and
--  `right`. As their names imply, the first one requires proving the left
--  side of the disjunction, while the second requires proving the right
--  side. Here is a trivial use...

theorem or_intro_l (a b : Prop) (h : a) : a ∨ b := by
  left; exact h

--  ... and here is a slightly more interesting example requiring both
--  `left` and `right`:

theorem Nat.zero_or_succ (n : Nat) : n = 0 ∨ n = (n + 1).pred := by
  cases n with
  | zero => left; rfl
  | succ n => right; rw [Nat.pred_succ]

--  ### Exercise (2 stars): mul_is_zero ⭐⭐

theorem Nat.mul_is_zero (n m : Nat) (h : n * m = 0) : n = 0 ∨ m = 0 := by
  sorry

--  ### Exercise (1 star): or_commute ⭐

theorem or_commute (a b : Prop) (h : a ∨ b) : b ∨ a := by
  sorry

--  ### Falsehood and Negation

--  Up to this point, we have mostly been concerned with proving "positive"
--  statements — addition is commutative, appending lists is associative,
--  etc. We are sometimes also interested in negative results,
--  demonstrating that some proposition is *not* true. Such statements are
--  expressed with the logical negation operator `¬`, which is a prefix
--  notation for `Not`.
--
--  To see how negation works, recall the *principle of explosion* from the
--  `Tactics` chapter, which asserts that, if we assume a contradiction,
--  then any other proposition can be derived.
--
--  Following this intuition, we could define `¬ a` ("not `a`") as
--  `∀ c, a → c`. Lean makes an equivalent but slightly different choice,
--  defining `¬ a` as `a → False`, where `False` is a specific unprovable
--  proposition defined in the standard library.

#check Not
#print Not

example (a : Prop) : Not a = (a → False) := rfl
example (a : Prop) : (¬ a) = (a → False) := rfl

--  Output:
--    Not (a : Prop) : Prop

--  Output:
--    @[implicit_reducible] def Not : Prop → Prop :=
--    fun a => a → False

--  Since `False` is a contradictory proposition, the principle of
--  explosion also applies to it. If we can get `False` into the context,
--  we can use `cases` on it to complete any goal:

theorem ex_falso_quodlibet (a : Prop) (h : False) : a := by
  cases h

--  The Latin *ex falso quodlibet* means, literally, "from falsehood
--  follows whatever you like"; this is another common name for the
--  principle of explosion.

--  ### Exercise (2 stars): not_implies_other_not (Optional) ⭐⭐

theorem not_implies_other_not (a : Prop) (h : ¬ a) :
    (∀ c : Prop, a → c) := by
  sorry

--  Inequality is a very common form of negated statement, so there is a
--  special notation for it: `≠`, which is infix notation for `Ne`.

#print Ne

--  Output:
--    @[reducible] def Ne.{u} : {α : Sort u} → α → α → Prop :=
--    fun {α} a b => ¬a = b

theorem zero_not_one : 0 ≠ 1 := by
  /- The proposition `0 ≠ 1` is exactly the same as `¬ (0 = 1)`
      — that is, `Not (0 = 1)` — which unfolds to `(0 = 1) → False`. -/
  /- To prove an inequality, we may assume the opposite equality... -/
  intro contra
  /- ...and deduce a contradiction from it. Here, the equality
      `0 = 1` corresponds to `zero = succ zero`, which contradicts
      disjointness of constructors `zero` and `succ`, so `contradiction`
      takes care of it. -/
  contradiction

--  It takes a little practice to get used to working with negation in
--  Lean. Even though *you* may see perfectly well why a claim involving
--  negation holds, it can be a little tricky at first to see how to make
--  Lean understand it!
--
--  Here are proofs of a few familiar facts to help get you warmed up.

theorem not_False : ¬ False := by
  intro h; exact h

theorem contradiction_implies_anything (a b : Prop) (h : a ∧ ¬ a) : b := by
  obtain ⟨ha, hna⟩ := h
  apply hna at ha
  cases ha

theorem double_neg (a : Prop) (ha : a) : ¬ ¬ a := by
  intro h; apply h; exact ha

--  ### Exercise (2 stars): double_neg_informal (Advanced, Optional, manually graded) ⭐⭐

--  Write an *informal* proof of `double_neg`: *Theorem*: `a` implies
--  `¬ ¬ a`, for any proposition `a`.

--  ### Exercise (1 star): contrapositive ⭐

theorem contrapositive (a b : Prop) (h : a → b) : (¬ b → ¬ a) := by
  sorry

--  ### Exercise (1 star): not_PNP_informal (Advanced, manually graded) ⭐

--  Write an informal proof of the proposition `∀ a : Prop, ¬ (a ∧ ¬ a)`.

--  ### Exercise (2 stars): de_morgan_not_or ⭐⭐

--  *De Morgan's Laws*, named for Augustus De Morgan, describe how negation
--  interacts with conjunction and disjunction. The following law says that
--  "the negation of a disjunction is the conjunction of the negations."
--  There is a dual law `de_morgan_not_and_not` to which we will return at
--  the end of this chapter.

theorem de_morgan_not_or {a b : Prop} (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b := by
  sorry

--  ### Exercise (1 star): not_succ_inverse_pred (Optional) ⭐

--  Since we are working with natural numbers, we can disprove that
--  `Nat.succ` and `Nat.pred` are inverses of each other. This proof will
--  require you to come up with a specific *counterexample* to the claim
--  being disproved:

theorem not_succ_pred_n : ¬ (∀ n : Nat, n.pred + 1 = n) := by
  sorry

--  Since inequality involves a negation, it also requires a little
--  practice to be able to work with it fluently. Here is one useful trick.
--
--  If you are trying to prove a goal that is nonsensical (e.g., the goal
--  state is `false = true`), apply `ex_falso_quodlibet` to change the goal
--  to `False`.
--
--  This makes it easier to use assumptions of the form `¬ a` that may be
--  available in the context — in particular, assumptions of the form
--  `x ≠ y`.

theorem not_true_is_false (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true =>
    rw [Ne, Not] at h
    apply ex_falso_quodlibet
    apply h
    rfl

--  Since reasoning with `ex_falso_quodlibet` is quite common, Lean
--  provides a tactic, `exfalso`, for applying it.

theorem not_true_is_false' (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true =>
    exfalso
    rw [Ne, Not] at h
    apply h
    rfl

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will we need besides
--  `intro`, `apply`, and `exact`?
--
--      ∀ α : Type, ∀ x y : α, x = y ∧ x ≠ y → False
--
--  1. `cases`, `left`, and `right`
--  2. only `cases`
--  3. `left` and/or `right`
--  4. none of the above

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will we need besides
--  `intro`, `apply`, and `exact`?
--
--      ∀ a b : Prop, a ∨ b → ¬ ¬ (a ∨ b)
--
--  1. `cases`, `left`, and `right`
--  2. only `cases`
--  3. `left` and/or `right`
--  4. none of the above

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will we need besides
--  `intro`, `apply`, and `exact`?
--
--      ∀ a b : Prop, a → (a ∨ ¬ ¬ b)
--
--  1. `cases`, `left`, and `right`
--  2. only `cases`
--  3. `left` and/or `right`
--  4. none of the above

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will we need besides
--  `intro`, `apply`, and `exact`?
--
--      ∀ a b : Prop, a ∨ b → (¬ ¬ a) ∨ (¬ ¬ b)
--
--  1. `cases`, `left`, and `right`
--  2. only `cases`
--  3. `left` and/or `right`
--  4. none of the above

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will we need besides
--  `intro`, `apply`, and `exact`?
--
--      ∀ a : Prop, 1 = 0 → (a ∨ ¬ a)
--
--  1. `contradiction` `left`, and `right`
--  2. only `contradiction`
--  3. `left` and/or `right`
--  4. none of the above

--   ----------------------------------------

--  ## Truth

--  Besides `False`, Lean's standard library also defines `True`, a
--  proposition that is trivially true. To prove it, we use the constructor
--  `True.intro` explicitly, or the anonymous constructor `⟨⟩`, or the
--  `constructor` tactic.

example : True := by exact True.intro
example : True := True.intro
example : True := by exact ⟨⟩
example : True := ⟨⟩
example : True := by constructor

--  Unlike `False`, which is used extensively, `True` is used relatively
--  rarely: it is trivial (and therefore uninteresting) to prove as a goal,
--  and it provides no useful information when it appears as a hypothesis.

--  However, `True` can be quite useful when defining complex `Prop`s using
--  conditionals or as a parameter to higher-order `Prop`s. We'll come back
--  to this later.
--
--  For now, let's take a look at how we can use `True` and `False` to
--  achieve an effect similar to that of the `contradiction` tactic,
--  without literally using `contradiction`.
--
--  Pattern-matching lets us do different things for different
--  constructors. If the result of applying two different constructors were
--  hypothetically equal, then we could use `match` to convert an
--  unprovable statement (like `False`) to one that is provable (like
--  `True`).

def DiscrFun (n : Nat) : Prop :=
  match n with
  | 0 => True
  | _ + 1 => False

theorem discrFun_zero : DiscrFun 0 := by constructor

theorem discrFun_succ (n : Nat) : ¬ DiscrFun (n + 1) := by
  rw [DiscrFun]; intro h; assumption

theorem discr_example (n : Nat) : ¬ (0 = n + 1) := by
  intro h
  have hd : DiscrFun 0 := discrFun_zero
  apply discrFun_succ 0
  rw [h] at hd
  exact hd

--  To generalize this to other constructors, we simply have to provide an
--  appropriate variant of `DiscrFun`. To generalize it to other
--  conclusions, we can use `exfalso` to replace them with `False`. The
--  `contradiction` tactic takes care of all of this for us.

--  ### Exercise (2 stars): nil_is_not_cons (Advanced, Optional, manually graded) ⭐⭐

--  Use the same technique as above to show that `[] ≠ x :: xs`. Do not use
--  the `contradiction` tactic.

--  FILL IN HERE

theorem nil_is_not_cons {α : Type} (x : α) (xs : List α) :
    ¬ ([] = x :: xs) := by
  sorry

--  ### Logical Equivalence

--  The handy "if and only if" connective, which asserts that two
--  propositions have the same truth value, is a structure containing the
--  two implication directions. `a ↔ b` is notation for `Iff a b`.

--  In Lean, `Iff` is a structure packaging two fields and a constructor,
--  which allow you to access its component implications. Given an `Iff`
--  hypothesis, you can access the "forward direction" implication via the
--  `Iff.mp` (short for *modus ponens*, the Latin name for reasoning by
--  implication) field, and the "reverse direction" via the `Iff.mpr`
--  (*modus ponens reverse*) field.
--
--  If your goal is an `Iff`, you can convert it into two goals, one for
--  each direction of the implication, via the `Iff.intro` constructor. Or
--  you can just use the `constructor` tactic.

#check (fun α β : Prop => α ↔ β : Prop → Prop → Prop)

#check Iff
#check Iff.intro
#check Iff.mp
#check Iff.mpr

--  Output:
--    Iff (a b : Prop) : Prop

--  Output:
--    Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b

--  Output:
--    Iff.mp {a b : Prop} (self : a ↔ b) : a → b

--  Output:
--    Iff.mpr {a b : Prop} (self : a ↔ b) : b → a

theorem iff_sym (a b : Prop) (h : a ↔ b) : b ↔ a := by
  constructor
  · exact h.mpr
  · exact h.mp

theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  constructor
  · apply not_true_is_false
  · intro h; rw [h]; intro h'; contradiction

--  ### Exercise (1 star): iff_properties (Optional) ⭐

--  Using the above proof that `↔` is symmetric (`iff_sym`) as a guide,
--  prove that it is also reflexive and transitive.

theorem iff_refl (a : Prop) : a ↔ a := by
  sorry

theorem iff_trans (a b c : Prop) (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c := by
  sorry

--  ### Exercise (3 stars): iff_practice ⭐⭐⭐

--  Prove the following theorems about `Iff`:

theorem or_associate (a b c : Prop) : a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c := by
  sorry

theorem mul_eq_0 (n m : Nat) :
    n * m = 0 ↔ n = 0 ∨ m = 0 := by
  sorry

theorem or_distributes_over_and (a b c : Prop) :
    a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) := by
  sorry

--  ### Existential Quantification

--  Another fundamental logical connective is *existential quantification*.
--  To say that there is some `x` of type `α` such that some property `a`
--  holds of `x`, we write `∃ x : α, a`. This is notation for the `Exists`
--  connective, and is defined as `Exists (fun (x : α) => a)`. As with
--  `∀ x : α`, the type annotation `: α` can be omitted if Lean is able to
--  infer from the context what the type of `x` should be.
--
--  To prove a statement of the form `∃ x, a`, we must show that `a` holds
--  for some specific choice for `x`, known as the *witness* of the
--  existential. This is done in two steps: First, we explicitly tell Lean
--  which witness `y` we have in mind by invoking the tactic `exists y`.
--  Then we prove that `a` holds after all occurrences of `x` are replaced
--  by `y`. The `exists` tactic tries to close the proof with simple
--  tactics such as `rfl` or `contradiction`, so we may not have to prove
--  `a` explicitly.

#check Exists

--  Output:
--    Exists.{u} {α : Sort u} (p : α → Prop) : Prop

def Nat.Even x := ∃ n : Nat, x = Nat.double n

#check (Nat.Even)

--  Output:
--    Nat.Even : Nat → Prop

open Nat in
example : Even 4 := by exists 2
  -- `4 = double 2` holds by `rfl`,
  -- but is proven automatically by `exists`

--  Conversely, if we have an existential hypothesis `∃ x, a` in the
--  context, we can destructure it to obtain a witness `x` and a hypothesis
--  stating that `a` holds of `x`.

example n : (∃ m, n = m + 4) → (∃ o, n = o + 2) := by
  intro ⟨m, hm⟩
  exists (m + 2)

--  ### Exercise (1 star): dist_not_exists ⭐

--  Prove that if `a` holds for all `x`, then there is no `x` for which `a`
--  does not hold. (Hint: `cases` and `obtain` work on existential
--  assumptions!)

theorem dist_not_exists (α : Type) (p : α → Prop) (h : ∀ x, p x) :
    ¬ (∃ x, ¬ p x) := by
  sorry

--  ### Exercise (2 stars): dist_exists_or ⭐⭐

--  Prove that existential quantification distributes over disjunction.

theorem dist_exists_or (α : Type) (p q : α → Prop) :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  sorry

--  ## Recap: Logical Connectives in Lean

--  Connectives introduced in this chapter:
--
--  - `a ∧ b` (conjunction):
--
--    - introduced with `constructor`
--    - eliminated with `intro ⟨ha, hb⟩` or `obtain ⟨ha, hb⟩ := h`
--
--  - `a ∨ b` (disjunction):
--
--    - introduced with `left` and `right`
--    - eliminated with `cases` or `obtain h | h := h`
--
--  - `False` (falsehood):
--
--    - eliminated with `cases` or `contradiction`
--
--  - `¬ a` (negation):
--
--    - defined as `a → False`
--
--  - `True` (truthhood):
--
--    - introduced as `True.intro` or with `constructor`
--
--  - `a ↔ b` (iff):
--
--    - introduced with `constructor`
--
--    - eliminated with `intro ⟨hab, hba⟩`, `obtain ⟨hab, hba⟩ := h`, or
--      `Iff.mp` and `Iff.mpr`
--
--  - `∃ x : α, a` (existential):
--
--    - introduced with `exists y`
--    - eliminated with `intro ⟨x, Hx⟩` or `obtain ⟨x, Hx⟩ := H`
--
--  Fundamental connectives we've been using since the beginning:
--
--  - equality (`x = y`)
--  - implication (`a → b`)
--  - universal quantification (`∀ x, a`)

--  ## Programming with Propositions

--  The logical connectives that we have seen provide a rich vocabulary for
--  defining complex propositions from simpler ones. To illustrate, let's
--  look at how to express the claim that an element `x` occurs in a list
--  `l`. Notice that this property has a simple recursive structure:

--  We can translate this directly into a straightforward recursive
--  function taking an element and a list and returning... a proposition!

def List.In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'

theorem List.In_nil {α : Type} {x : α} : ¬ (List.In x []) := by
  rw [List.In]; intro h; assumption

theorem List.In_cons {α : Type} {x x' : α} {xs : List α} : List.In x (x' :: xs) = (x = x' ∨ List.In x xs) := rfl

--  When `List.In` is applied to a concrete list, it expands into a
--  concrete sequence of nested disjunctions.

example : List.In 4 [1, 2, 3, 4, 5] := by
  rw [List.In]; right; right; right; left; rfl

example (n : Nat) (h : List.In n [2, 4]) : ∃ n' : Nat, n = 2 * n' := by
  rw [List.In] at h
  obtain h | h | ⟨⟨⟩⟩ := h
  · exists 1
  · exists 2
    /- (Notice the use of the empty pattern to discharge the last case.) -/

--  We can also reason about more generic statements involving `List.In`.

theorem List.In_map {α β : Type} {f : α → β} {xs : List α} {x : α} (h : In x xs) :
    In (f x) (map f xs) := by
  induction xs with
  | nil =>
    exfalso; apply In_nil; assumption
  | cons x' xs' ih =>
    rw [In_cons] at h
    obtain h | h := h
    · rw [h, map_cons, In_cons]; left; rfl
    · rw [map_cons, In_cons]; right; exact ih h

--  This way of defining propositions recursively is very convenient in
--  some cases, less so in others. In particular, it is subject to the
--  usual restrictions regarding definitions of recursive functions, e.g.,
--  the requirement that they be "obviously terminating."
--
--  In the next chapter, we will see how to define propositions
--  *inductively* — a different technique with its own strengths and
--  limitations.

--  ### Exercise (2 stars): In_map_iff ⭐⭐

theorem List.In_map_iff {α β : Type} {f : α → β} {xs : List α} {y : β} :
    In y (map f xs) ↔ ∃ x, f x = y ∧ In x xs := by
  constructor
  · sorry
  · sorry

--  ### Exercise (3 stars): All ⭐⭐⭐

--  We noted above that functions returning propositions can be seen as
--  *properties* of their arguments. For instance, if `p` has type
--  `Nat → Prop`, then `p n` says that property `p` holds of `n`.
--
--  Drawing inspiration from `List.In`, write a recursive function `All`
--  stating that some property `p` holds of all elements of a list `l`. To
--  make sure your definition is correct, prove the `All_In` lemma below.
--  (Of course, your definition should *not* just restate the left-hand
--  side of `All_In`.)

def List.All {α : Type} (p : α → Prop) (l : List α) : Prop := sorry
theorem List.All_nil {α : Type} {a : α → Prop} : List.All a [] := sorry

theorem List.All_cons {α : Type} {p : α → Prop} {x : α} {l : List α} :
    List.All p (x :: l) = (p x ∧ All p l) := sorry

theorem List.All_In {α : Type} {p : α → Prop} {l : List α} :
    (∀ x : α, In x l → p x) ↔ All p l := by
  sorry

--  Note to developers (Yipeng Liu @berberman, NOW):
--      I found this exercise combining too many awkward details for too
--      little conceptual payoff:
--
--      1. the construction is artificial
--
--      2. before `simp` is introduced, `bif` requires noisy `rw` and
--         Boolean case equations
--
--      3. I don't know how to nicely avoid `cases h : ...` syntax which
--         IIRC we didn't mention before

--  ### Exercise (2 stars): CombineOddEven (Optional) ⭐⭐

--  Complete the definition of `CombineOddEven` below. It takes as
--  arguments two properties of numbers, `Odd` and `Even`, and it should
--  return a predicate `p` such that `p n` is equivalent to `Odd n` when
--  `n` is odd and equivalent to `Even n` otherwise.

def CombineOddEven (Odd Even : Nat → Prop) : Nat → Prop := sorry

--  To test your definition, prove the following facts:

theorem combineOddEven_intro (Odd Even : Nat → Prop)
    (n : Nat)
    (hOdd : Nat.odd n = true → Odd n)
    (hEven : Nat.odd n = false → Even n) :
    CombineOddEven Odd Even n := by
  sorry

theorem combineOddEven_elim_odd
    (Odd Even : Nat → Prop)
    (n : Nat)
    (h : CombineOddEven Odd Even n)
    (hOdd : Nat.odd n = true) : Odd n := by
  sorry

theorem combineOddEven_elim_even
    (Odd Even : Nat → Prop)
    (n : Nat)
    (h : CombineOddEven Odd Even n)
    (hOdd : Nat.odd n = false) : Even n := by
  sorry

--  ## Applying Theorems to Arguments

--  Lean treats *proofs* as first-class objects. There is a great deal to
--  be said about this, but it is not necessary to understand it all to use
--  Lean. This section gives just a taste.

--  We have seen that we can use `#check` to ask Lean whether an expression
--  has a given type:

#check (Nat.add : Nat → Nat → Nat)

--  We can also use it to check what theorem a particular identifier refers
--  to:

#check Nat.add_comm

--  Output:
--    Nat.add_comm (n m : Nat) : n + m = m + n

#check Nat.add_assoc

--  Output:
--    Nat.add_assoc (n m k : Nat) : n + m + k = n + (m + k)

--  Lean checks the *statements* of the `Nat.add_comm` and `Nat.add_assoc`
--  theorems in the same way that it checks the *type* of any term (e.g.
--  `Nat.add`). Leaving off the colon and the type, Lean prints these types
--  in the infoview for us.
--
--  Why?
--
--  The reason is that the identifier `Nat.add_comm` actually refers to a
--  *proof object* — a logical derivation establishing the truth of the
--  statement `∀ n m : Nat, n + m = m + n`. The type of this object is the
--  proposition that it is a proof of.
--
--  The type of an ordinary function tells us what we can do with it.
--
--  - If we have a term of type `Nat → Nat → Nat`, we can give it two
--    `Nat`s as arguments and get a `Nat` back. Similarly, the statement of
--    a theorem tells us what we can use that theorem for.
--
--  - If we have a term of type `∀ n m : Nat, n = m → n + n = m + m`, and
--    we provide it two numbers `n` and `m` and a third "argument" of type
--    `n = m`, we get back a proof object of type `n + n = m + m`.

--  Operationally, this analogy goes even further: by applying a theorem as
--  if it were a function, i.e., applying it to values and hypotheses with
--  matching types, we can specialize its result without having to resort
--  to intermediate assertions. For example, suppose we wanted to prove the
--  following result:

sf_expect_failure_in
  example (x y z : Nat) : x + (y + z) = (z + y) + x := by
    rw [Nat.add_comm]
    rw [Nat.add_comm]

--  Output:
--    unsolved goals
--    a b c : Prop
--    n m : Nat
--    α✝ : Type
--    e1 e2 x✝¹ y✝¹ : α✝
--    α β : Type
--    x✝ x' y✝ : α
--    l l' : List α
--    f g : α → β
--    p : α → Prop
--    x y z : Nat
--    ⊢ x + (y + z) = z + y + x

--  It appears at first sight that we ought to be able to prove this by
--  rewriting with `Nat.add_comm` twice to make the two sides match. The
--  problem is that the second rewrite undoes the effect of the first,
--  leaving us back where we started...
--
--  We encountered similar issues back in the Induction chapter, and we saw
--  that we can fix them by applying `Nat.add_comm` to the arguments we
--  want it to be instantiated with, in much the same way as we apply a
--  polymorphic function to a type argument. Then the rewrite is forced to
--  happen exactly where we want it.

example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm]
  rw [Nat.add_comm z y]

--  If we really wanted, we could in fact do it for both rewrites.

example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm x (y + z)]
  rw [Nat.add_comm z y]

--  The fact that implications are functions means we can prove them by
--  explicitly providing a function.

theorem identity {a : Prop} : a → a := fun h => h

--   ----------------------------------------

--  _Quiz:_

--  Suppose we have
--
--      n m : Nat
--      h₁ : n = m
--      h₂ : m = 42
--      trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
--
--  What is the type of this "proof object"?
--
--      @trans_eq Nat n m 42 h₁ h₂
--
--  1. `n = m`
--  2. `42 = n`
--  3. `n = 42`
--  4. Does not typecheck

--   ----------------------------------------

--  _Quiz:_

--  Suppose, again, we have
--
--      n m : Nat
--      h₁ : n = m
--      h₂ : m = 42
--      trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
--
--  What is the type of this proof object?
--
--      trans_eq h₁ h₂
--
--  1. `n = m`
--  2. `42 = n`
--  3. `n = 42`
--  4. Does not typecheck

--   ----------------------------------------

--  _Quiz:_

--  Suppose, again, we have
--
--      n m : Nat
--      h₁ : n = m
--      h₂ : m = 42
--      trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
--
--  What is the type of this proof object?
--
--      @trans_eq Nat m 42 n h₂
--
--  1. `m = n`
--  2. `m = n → 42 = n`
--  3. `42 = n → m = n`
--  4. Does not typecheck

--   ----------------------------------------

--  _Quiz:_

--  Suppose, again, we have
--
--      n m : Nat
--      h₁ : n = m
--      h₂ : m = 42
--      trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
--
--  What is the type of this proof object?
--
--      @trans_eq _ 42 n m
--
--  1. `n = m → m = 42 → n = 42`
--  2. `42 = n → n = m → 42 = m`
--  3. `n = 42 → 42 = m → n = m`
--  4. Does not typecheck

--   ----------------------------------------

--  _Quiz:_

--  Suppose, again, we have
--
--      n m : Nat
--      h₁ : n = m
--      h₂ : m = 42
--      trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
--
--  What is the type of this proof object?
--
--      trans_eq h₂ h₁
--
--  1. `m = n`
--  2. `42 = n`
--  3. `n = 42`
--  4. Does not typecheck

--   ----------------------------------------

--  ## Working with Decidable Properties

--  We've seen two different ways of expressing logical claims in Lean:
--  with *booleans* (of type `Bool`), and with *propositions* (of type
--  `Prop`). Here are the key differences between `Bool` and `Prop`:
--
--      |                     | `Bool` | `Prop` |
--      | ------------------- | ------ | ------ |
--      | decidable?          | yes    | no     |
--      | useable with match? | yes    | no     |

--  The crucial difference between the two worlds is *decidability*. Every
--  (closed) expression of type `Bool` can be simplified in a finite number
--  of steps to either `true` or `false` — i.e., there is a terminating
--  mechanical procedure for deciding whether or not it is `true`.
--
--  This means that, for example, the type `Nat → Bool` is inhabited only
--  by functions that, given a `Nat`, always yield either `true` or `false`
--  in finite time; this, in turn, means (by a standard computability
--  argument) that there is *no* function in `Nat → Bool` that checks
--  whether a given number is the code of a terminating Turing machine.
--
--  By contrast, the type `Prop` includes both decidable and undecidable
--  mathematical propositions; in particular, the type `Nat → Prop` does
--  contain functions representing properties like "the nth Turing machine
--  halts."
--
--  The second table row follows directly from this essential difference.
--  To evaluate a pattern match (or conditional) on a boolean, we need to
--  know whether the scrutinee evaluates to `true` or `false`; this only
--  works for `Bool`, not `Prop`.

--  Since `Prop` includes *both* decidable and undecidable properties, we
--  have two options when we want to formalize a property that happens to
--  be decidable: we can express it either as a boolean computation, or as
--  a function into `Prop`.
--
--  For instance, to claim that a number `n` is even, we can say either
--  that `Nat.even n` evaluates to `true`...

example : Nat.even 42 = true := rfl

--  ... or that there exists some `k` such that `n = double k`.

example : Nat.Even 42 := by rw [Nat.Even]; exists 21

--  Of course, it would be deeply strange if these two characterizations of
--  evenness did not describe the same set of natural numbers! Fortunately,
--  they do!
--
--  To prove this, we first need two helper lemmas.

theorem even_double (k : Nat) :
    Nat.even (Nat.double k) = true := by
  induction k with
  | zero => rw [Nat.double_zero]; rfl
  | succ k' ih => rw [Nat.double_succ]; exact ih

theorem even_double_conv (n : Nat) : ∃ k : Nat,
    n = bif Nat.even n then Nat.double k else Nat.double k + 1 := by
  sorry

--  Now the main theorem:

theorem Nat.even_bool_prop (n : Nat) : Nat.even n = true ↔ Even n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := even_double_conv n
    rw [h] at hk; rw [cond_true] at hk; rw [Even]; exists k
  · intro ⟨k, hk⟩; rw [hk]; apply even_double

--  In view of this theorem, we can say that the boolean computation
--  `Nat.even n` is *reflected* in the truth of the proposition
--  `∃ k, n = Nat.double k`.

--  Similarly, to state that two numbers `n` and `m` are equal, we can say
--  either
--
--  1. that `n == m` returns `true`, or
--  2. that `n = m`.
--
--  Again, these two notions are equivalent:
--
--  (For the reverse direction we need the simple fact that `==` is
--  reflexive.)
--
--  Don't worry too much about `Nat.beq_eq_true_eq` yet, we need this from
--  Lean because `n == m` is a wrapper of `DecidableEq Nat`. We will go
--  over this in the Typeclasses chapter.

theorem beq_eq_true (n m : Nat) :
    (n == m) = true ↔ n = m := by
  rw [Nat.beq_eq_true_eq]

--  So what should we do in situations where some claim could be formalized
--  as either a proposition or a boolean computation? Which should we
--  choose?
--
--  In general, *both* can be useful. For example, booleans are more useful
--  for defining functions, since we can test whether they are true using
--  conditional expressions.

def is_even_prime (n : Nat) : Bool :=
  bif n == 2 then true else false

--  Beyond the fact that non-computable properties are possible in general
--  to phrase as boolean computations, even many *computable* properties
--  are easier to express using `Prop` than `Bool`, since recursive
--  function definitions are subject to significant restrictions. For
--  instance, the next chapter shows how to define the property that a
--  regular expression matches a given string using `Prop`. Doing the same
--  with `Bool` would amount to writing a regular expression matching
--  algorithm, which would be more complicated, harder to understand, and
--  harder to reason about than a simple (non-algorithmic) definition of
--  this property.
--
--  Conversely, an important side benefit of stating facts using booleans
--  is enabling some proof automation through computation with terms, a
--  technique known as *proof by reflection*.
--
--  Consider the following statement:

--  The most direct way to prove this is to give the value of `k`
--  explicitly.

example : Nat.Even 100 := by
  exists 50

--  The proof of the corresponding boolean statement is simpler, because we
--  don't have to invent the witness `50`: computation does it for us!

example : Nat.even 100 = true := rfl

--  Now, the useful observation is that, since the two notions are
--  equivalent, we can use the boolean formulation to prove the other one
--  without mentioning the value 50 explicitly:

example : Nat.Even 100 := by
  obtain ⟨h, _⟩ := Nat.even_bool_prop 100
  apply h; rfl

--  Although we haven't gained much in terms of proof-script simplicity in
--  this case, larger proofs can often be made considerably simpler by the
--  use of reflection.
--
--  As an extreme example, a famous mechanized proof of the even more
--  famous *four colour theorem* uses reflection to reduce the analysis of
--  hundreds of different cases to a boolean computation.
--
--  Another advantage of booleans is that the *negation* of a claim about
--  booleans is straightforward to state and (when true) to prove: simply
--  flip the expected boolean result.

example : Nat.even 101 = false := rfl

--  In contrast, propositional negation can be difficult to work with
--  directly. For example, suppose we state the nonevenness of `101`
--  propositionally:
--
--  Proving this directly — by assuming that there is some `n` such that
--  `101 = Nat.double n` and then somehow reasoning to a contradiction —
--  would be rather complicated.
--
--  But if we convert it to a claim about the boolean `Nat.even` function,
--  we can let Lean do the work for us.

example : ¬ Nat.Even 101 := by
  intro h; apply (Nat.even_bool_prop 101).mpr at h
  rw [Nat.even] at h; contradiction

--  Conversely, there are situations where it can be easier to work with
--  propositions rather than booleans. In particular, knowing that
--  `(n == m) = true` is generally of little direct help in the middle of a
--  proof involving `n` and `m`. But if we convert the statement to the
--  equivalent form `n = m`, then we can easily rewrite with it.

theorem add_beq_true (n m p : Nat) (h : (n == m) = true) :
    (n + p == m + p) = true := by
  apply (beq_eq_true n m).mp at h
  rw [h, BEq.rfl]

--  We'll come back to reflection and decidable propositions in a later
--  chapter, but it serves as a good example showing the different
--  strengths of booleans and general propositions. Being able to cross
--  back and forth between the boolean and propositional worlds will often
--  be convenient in later chapters.

--  ### Exercise (2 stars): logical connectives ⭐⭐

--  The following theorems relate the propositional connectives studied in
--  this chapter to the corresponding boolean operations.

theorem andb_true_iff (b1 b2 : Bool) :
    (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by
  sorry

theorem orb_true_iff (b1 b2 : Bool) :
    (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by
  sorry

--  ### Exercise (3 stars): beqList ⭐⭐⭐

--  Given a boolean operator `beq` for testing equality of elements of some
--  type `α`, we can define a function `beqList` for testing equality of
--  lists with elements in `α`. Complete the definition of the `beqList`
--  function below. To make sure that your definition is correct, prove the
--  lemma `beqList_true_iff`.

def beqList {α : Type} (beq : α → α → Bool) (xs ys : List α) : Bool := sorry

theorem beqList_nil_nil {α : Type} {beq : α → α → Bool} :
    beqList beq [] [] = true := sorry

theorem beqList_cons_cons {α : Type} {beq : α → α → Bool}
    {x y : α} {xs ys : List α} :
    beqList beq (x :: xs) (y :: ys) = (beq x y && beqList beq xs ys) :=
  sorry

theorem beqList_nil_cons {α : Type} {beq : α → α → Bool}
    {x : α} {xs : List α} : beqList beq [] (x :: xs) = false := sorry

theorem beqList_cons_nil {α : Type} {beq : α → α → Bool}
    {x : α} {xs : List α} : beqList beq (x :: xs) [] = false := sorry

theorem beqList_true_iff α (beq : α → α → Bool)
    (h : ∀ (x y : α), beq x y = true ↔ x = y) :
    ∀ {xs ys : List α}, beqList beq xs ys = true ↔ xs = ys := by
  sorry

--  ### Exercise (2 stars): List.allb ⭐⭐

--  Prove the theorem below, which relates `List.allb`, from the exercise
--  `Tactics.forall_exists_challenge`, to the `List.All` property defined
--  above.
--
--  Copy the definition of `List.allb` from Tactics here so that this file
--  can be graded on its own.

def List.allb {α : Type} (test : α → Bool) (l : List α) : Bool := sorry

theorem List.allb_nil {α : Type} {test : α → Bool} : allb test [] = true := sorry

theorem List.allb_cons {α : Type} {test : α → Bool} {x : α} {l : List α} :
    allb test (x :: l) = (test x && allb test l) := sorry

theorem List.allb_true_iff α {test : α → Bool} {l : List α} :
    allb test l = true ↔ All (fun x => test x = true) l := by
  sorry

--  (Ungraded thought question) Are there any important properties of the
--  function `List.allb` which are not captured by this specification?

--  ## The Logic of Lean

--  Lean's logical core differs in some important ways from other formal
--  systems that are used by mathematicians to write down precise and
--  rigorous definitions and proofs – in particular from Zermelo–Fraenkel
--  Set Theory (ZFC), the most popular foundation for paper-and-pencil
--  mathematics.
--
--  We conclude this chapter with a brief discussion of some of the most
--  significant differences between these two worlds.

--  ### Propositional Extensionality

--  Lean's logic is quite minimalistic. This means that one occasionally
--  encounters cases where translating standard mathematical reasoning into
--  Lean is cumbersome - or even impossible - unless we enrich its core
--  logic with additional axioms.

--  For example, the equality assertions that we have seen so far mostly
--  have concerned elements of inductive types (`Nat`, `Bool`, etc.). But
--  since the equality operator is polymorphic, we can use it at *any* type
--
--  - in particular, we can write propositions claiming that two
--    *propositions* are equal to each other:

#check (∀ a b : Prop, (a ∧ b) = (b ∧ a) : Prop)

--  This is an equality between two conjunctions, which itself is also a
--  proposition. It states that commuted conjunctions are equal
--  propositions. However, we cannot prove this equality by reflexivity, as
--  the two sides don't compute to the same term, and we cannot proceed by
--  cases on `a` or `b`, as they are not inductive.

sf_expect_failure_in
  example (a b : Prop) : a ∧ b = b ∧ a := by rfl

--  Output:
--    Tactic `rfl` failed: The left-hand side
--      a
--    is not definitionally equal to the right-hand side
--      b = b ∧ a
--
--    a✝ b✝ c : Prop
--    n m : Nat
--    α✝ : Type
--    e1 e2 x✝ y✝ : α✝
--    α β : Type
--    x x' y : α
--    l l' : List α
--    f g : α → β
--    p : α → Prop
--    a b : Prop
--    ⊢ a ∧ b = b ∧ a

sf_expect_failure_in
  example (a b : Prop) : a ∧ b = b ∧ a := by cases a

--  Output:
--    Tactic `cases` failed: major premise type is not an inductive type
--      Prop
--
--    Explanation: the `cases` tactic is for constructor-based reasoning as well as for applying custom cases principles with a 'using' clause or a registered '@[cases_eliminator]' theorem. The above type neither is an inductive type nor has a registered theorem.
--
--    Consider using the 'by_cases' tactic, which does true/false reasoning for propositions.
--
--    a✝ b✝ c : Prop
--    n m : Nat
--    α✝ : Type
--    e1 e2 x✝ y✝ : α✝
--    α β : Type
--    x x' y : α
--    l l' : List α
--    f g : α → β
--    p : α → Prop
--    a b : Prop
--    ⊢ a ∧ b = b ∧ a

--  However, we *can* prove that `a ∧ b` implies `b ∧ a`, and vice versa --
--  this is the commutativity of conjunction that we have seen earlier.

#check and_comm

--  Output:
--    and_comm {a b : Prop} : a ∧ b ↔ b ∧ a

--  Since it would be convenient to be able to rewrite propositions from
--  one side of `↔` to the other, Lean provides an axiom to turn `↔` into
--  `=`, which is called *propositional extensionality* (`propext`).

#print propext

--  Output:
--    axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b

--  (Informally, an *extensional* property is one that pertains to
--  observable behavior. Thus, propositional extensionality means that a
--  proposition's identity is completely determined by what we can observe
--  from it — i.e., whether the proposition holds. We can state this more
--  explicitly:)

theorem prop_true (a : Prop) (h : a) : a = True := by
  apply propext
  constructor
  · intro _
    exact ⟨⟩
  · intro _
    exact h

--  Lean provides an `ext` tactic that applies `propext` for us. We can use
--  it to show that commuted conjoined propositions are equal. Similarly,
--  we can use it to show that reassociated conjoined propositions are
--  equal as well.

theorem and_comm_eq (a b : Prop) : (a ∧ b) = (b ∧ a) := by
  ext; apply and_comm

theorem and_assoc_eq (a b c : Prop) : ((a ∧ b) ∧ c) = (a ∧ (b ∧ c)) := by
  ext; apply and_assoc

--  Here is an example of where using `=` instead of `↔` is more
--  convenient: we show that it's possible to "flip" three conjoined
--  propositions.
--
--  One way to prove this is to construct the `↔`, destruct the `↔`s
--  provided by `and_comm` and `and_assoc`, and apply the resulting
--  implications a few times. But this is a lot of hassle, when the proof
--  is conceptually simple: we flip `b` and `c`, then we flip that
--  conjunction with `a`, and we finish by associativity. By using
--  `and_comm_eq`, this is easily done by rewriting equal propositions.

theorem and_comm_flip (a b c : Prop) : (a ∧ b ∧ c) ↔ (c ∧ b ∧ a) := by
  rw [and_comm_eq b c, and_comm_eq a, and_assoc_eq]

--  The pattern of deriving an equality of propositions out of `↔` then
--  rewriting by that equality is so common that Lean will implicitly cast
--  `↔` to `=`, allowing you to rewrite on `↔` directly. Notice that `rw`
--  is also able to close goals of the form `a ↔ a` by reflexivity.

theorem and_comm_flip' (a b c : Prop) : (a ∧ b ∧ c) ↔ (c ∧ b ∧ a) := by
  rw [@and_comm b c, @and_comm a, and_assoc]

--  Under the hood, this proof still uses `propext`, which you can check by
--  asking for all of the axioms used by a declaration.

#print axioms and_comm_flip

--  Output:
--    'and_comm_flip' depends on axioms: [propext]

#print axioms and_comm_flip'

--  Output:
--    'and_comm_flip'' depends on axioms: [propext]

--  ### Exercise (1 star): mul_eq_0_ternary ⭐

theorem mul_eq_0_ternary (n m p : Nat) :
    n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  sorry

--  ### Exercise (2 stars): In_append_iff ⭐⭐

theorem In_append_iff (α : Type) (l l' : List α) (x : α) :
    List.In x (l ++ l') ↔ List.In x l ∨ List.In x l' := by
  sorry

--  ### Exercise (1 star): beq_neq_false ⭐

--  The following theorem is an alternative "negative" formulation of
--  `beq_eq_true` that is more convenient in certain situations. (We'll see
--  examples in later chapters.) Hint: `not_true_iff_false`.

theorem beq_neq_false (n m : Nat) : (n == m) = false ↔ n ≠ m := by
  sorry

--  ### Functional Extensionality

--  We can also write propositions claiming that two *functions* are equal
--  to each other. In some cases, we can also prove that two functions are
--  equal by reflexivity when both reduce to the same expression:

example : (fun x => x + 2) = (fun x => x + (Nat.pred 3)) := rfl

--  In general, functions can be equal for more interesting reasons. In
--  common mathematical practice, two functions `f` and `g` are considered
--  equal if they produce the same output on every input:
--
--      (∀ x, f x = g x) → f = g
--
--  This is known as *functional extensionality*, which Lean provides as
--  `funext`.

#check (fun f g => funext (f := f) (g := g) :
    ∀ {α β : Type} (f g : α → β), (∀ x, f x = g x) → f = g)

--  Here, functional extensionality means that a function's identity is
--  completely determined by what we can observe from it — i.e., the
--  results we obtain after applying it. (Its full type is actually
--  slightly more general, and is defined in terms of a more fundamental
--  concept called *quotients* rather than added directly as an axiom, but
--  we will only discuss `funext` here. This is also why, when printing
--  axioms for theorems using `funext`, it will instead display a
--  `Quot.sound` axiom.)

#print axioms funext

--  Output:
--    'funext' depends on axioms: [Quot.sound]

--  Now we can prove some intuitively obvious equalities about functions
--  that would otherwise not be provable without `funext`.

theorem add_comm_fun : (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
  apply funext; intro n
  apply funext; intro m
  exact Nat.add_comm n m

--  The `ext` tactic will also apply `funext` as many times as possible,
--  introducing all variables in one go. (The singular version of the
--  tactic is `ext1`.)

theorem add_comm_fun' : (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
  ext n m; exact Nat.add_comm n m

--   ----------------------------------------

--  _Quiz:_

--  Is the following statement provable by just `rfl`, without `funext`?
--
--      (fun xs => 1 :: xs) = (fun xs => [1] ++ xs)
--
--  1. Yes
--  2. No

--   ----------------------------------------

--  #### Other Extensionality Principles

--  Functions and propositions are not the only things that have
--  extensionality principles. Many structures like pairs also have them:

example {n : Nat} {p : Nat × Nat} (hx_fst : p.fst = n + 1) (hx_snd : p.snd = 0) :
    (n + 1, 0) = p := by
  ext -- uses the `Prod.ext` lemma
  · rw [hx_fst]
  · rw [hx_snd]

--  ### Exercise (2 stars): prod_ext_example ⭐⭐

--  Now, use `ext1` to prove the following. Remember that `dsimp only`
--  simplifies projections like `(a, b).fst` to `a`.

example {m : Nat} {p : Nat × Nat} (hp_snd : p.snd = 4) (hp_fst : p.fst = m) :
    ((p.fst + 1, 2), (p.fst, 4)) = ((m + 1, p.snd - 2), p) := by
  sorry

--  ### Exercise (4 stars): trRev_correct ⭐⭐⭐⭐

--  One problem with the definition of the list-reversing function
--  `List.rev` is that it performs a call to `++` on each step. Running
--  `++` takes time asymptotically linear in the size of the list, which
--  means that `List.rev` is asymptotically quadratic.
--
--  We can improve this with the following two-argument definition:

def revAppend {α} (xs ys : List α) : List α :=
  match xs with
  | [] => ys
  | x :: xs => revAppend xs (x :: ys)

theorem revAppend_nil {α : Type} {xs : List α} : revAppend [] xs = xs := rfl

theorem revAppend_cons {α : Type} {x : α} {xs ys : List α} :
    revAppend (x :: xs) ys = revAppend xs (x :: ys) := rfl

def trRev {α} (xs : List α) : List α := revAppend xs []

--  This version of `List.rev` is said to be *tail recursive*, because the
--  recursive call to the function is the last operation that needs to be
--  performed (i.e., we don't have to execute `++` after the recursive
--  call); a decent compiler will generate very efficient code in this
--  case.
--
--  Prove that the two definitions are indeed equivalent.

--  FILL IN HERE

theorem trRev_correct {α : Type} : @trRev α = @List.rev α := by
  sorry

--  ### Classical vs. Constructive Logic

--  We have seen that it is not possible to test whether or not a
--  proposition `a` holds while defining a Lean function. You may be
--  surprised to learn that a similar restriction applies in *proofs*! In
--  other words, the following intuitive reasoning principle is not
--  derivable in Lean with the tools we've seen so far:

def ExcludedMiddle := ∀ a : Prop, a ∨ ¬ a

--  To understand operationally why this is the case, recall that, to prove
--  a statement of the form `a ∨ b`, we use the `left` and `right` tactics,
--  which effectively require knowing which side of the disjunction holds.
--  But the universally quantified `a` in `ExcludedMiddle` is an
--  *arbitrary* proposition, which we know nothing about. We don't have
--  enough information to choose which of `left` or `right` to apply.
--
--  However, in the special case where we happen to know that `a` is
--  reflected in some boolean term `b`, knowing whether it holds or not is
--  trivial: we just have to check the value of `b`.

theorem restricted_excluded_middle (a : Prop) (b : Bool) (h : a ↔ b = true) :
    a ∨ ¬ a := by
  cases b with
  | false => right; rw [h]; intro; contradiction
  | true => left; rw [h]

--  In particular, the excluded middle is valid for equations `n = m`
--  between natural numbers `n` and `m`.

theorem excluded_middle_nat_eq (n m : Nat) : n = m ∨ n ≠ m := by
  apply restricted_excluded_middle (n = m) (n == m)
  symm; apply beq_eq_true

--  Sadly, this trick only works for decidable propositions.

--  Logical systems in which excluded middle does not hold are referred to
--  as *constructive logics*. They are so called because to prove a
--  proposition, we must give a construction for it; for instance, a proof
--  of `∃ x, p x` is proven by providing a particular value of `x`.
--
--  Logical systems in which excluded middle does hold, such as ZFC set
--  theory, are referred to as *classical*. Lean provides classical
--  reasoning principles in the `Classical` library, including excluded
--  middle.

#check Classical.em

--  Output:
--    Classical.em (p : Prop) : p ∨ ¬p

--  All classical reasoning principles in `Classical` are derived from one
--  axiom, the axiom of choice. This is the C in ZFC.

#print Classical.choice

--  Output:
--    axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α

#print axioms Classical.em

--  Output:
--    'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]

--  Lean also provides a `by_cases` tactic that applies `Classical.em` on a
--  given proposition. Theorems proven using this tactic implicitly use
--  classical axioms.

theorem em : ∀ a, a ∨ ¬ a := by
  intro a
  by_cases h : a
  /- h : a -/
  · left; exact h
  /- h : ¬ a -/
  · right; exact h

#print axioms em

--  Output:
--    'em' depends on axioms: [propext, Classical.choice, Quot.sound]

--  The following example illustrates why assuming the excluded middle may
--  lead to nonconstructive proofs:
--
--  *Claim*: There exist irrational numbers `n` and `m` such that `n ^ m`
--  (`n` to the power `m`) is rational.
--
--  *Proof*: It is not difficult to show that `sqrt 2` is irrational. So if
--  `sqrt 2 ^ sqrt 2` is rational, it suffices to take `n = m = sqrt 2` and
--  we are done. Otherwise, `sqrt 2 ^ sqrt 2` is irrational. In this case,
--  we can take `a = sqrt 2 ^ sqrt 2` and `b = sqrt 2`, since
--  `a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2`. QED.
--
--  Do you see what happened here? We used the excluded middle to consider
--  separately the cases where `sqrt 2 ^ sqrt 2` is rational and where it
--  is not, without knowing which one actually holds! Because of this, we
--  finish the proof knowing that such `n` and `m` exist, but not being
--  sure of their actual values.
--
--  As useful as constructive logic is, it does have its limitations: There
--  are many statements that can easily be proven in classical logic but
--  that have only much more complicated constructive proofs, and there are
--  some that are known to have no constructive proof at all! Fortunately,
--  like functional extensionality, the excluded middle is known to be
--  compatible with Lean's logic, allowing it to be added safely as an
--  axiom. However, the results that we cover in Logical Foundations can be
--  developed entirely within constructive logic.
--
--  It takes some practice to understand which proof techniques must be
--  avoided in constructive reasoning, but arguments by contradiction, in
--  particular, are infamous for leading to nonconstructive proofs. Here's
--  a typical example: suppose that we want to show that there exists `x`
--  with some property `p`, i.e., such that `p x`. We start by assuming
--  that our conclusion is false; that is, `¬ ∃ x, p x`. From this premise,
--  it is not hard to derive `∀ x, ¬ p x`. If we manage to show that this
--  results in a contradiction, we arrive at an existence proof without
--  ever exhibiting a value of `x` for which `p x` holds!
--
--  The technical flaw here, from a constructive standpoint, is that we
--  claimed to prove `∃ x, p x` using a proof of `¬ ¬ ∃ x, p x`. Allowing
--  ourselves to remove double negations from arbitrary statements is
--  equivalent to assuming the excluded middle law, as shown in one of the
--  exercises below.

--  Once again, Lean's `Classical` library provides double negation
--  elimination, which relies on the `Classical.choice` axiom.

#check Classical.not_not

#print axioms Classical.not_not

--  Output:
--    Classical.not_not {a : Prop} : ¬¬a ↔ a

--  Output:
--    'Classical.not_not' depends on axioms: [propext, Classical.choice, Quot.sound]

--  ### Exercise (3 stars): excluded_middle_irrefutable ⭐⭐⭐

--  The following theorem implies that it is always safe to assume a
--  decidability axiom (i.e., an instance of excluded middle) for any
--  *particular* proposition `a`. Why? Because the negation of such an
--  axiom leads to a contradiction. If `¬ (a ∨ ¬ a)` were provable, then by
--  `de_morgan_not_or` as proven above, `a ∧ ¬ a` would be provable, which
--  would be a contradiction. So, it is safe to add `a ∨ ¬ a` as an axiom
--  for any particular `a`.

theorem excluded_middle_irrefutable (a : Prop) : ¬ ¬ (a ∨ ¬ a) := by
  sorry

--  ### Exercise (3 stars): not_exists_dist (Advanced) ⭐⭐⭐

--  It is a theorem of classical logic that the following two assertions
--  are equivalent:
--
--      ¬ ∃ x, ¬ p x
--      ∀ x, p x
--
--  The `dist_not_exists` theorem proves one side of this equivalence.
--  Interestingly, the other direction cannot be proven in constructive
--  logic, but we can prove it here using `by_cases`.

theorem not_exists_dist (α : Type) (p : α → Prop) :
    (¬ ∃ x : α, ¬ p x) → (∀ x : α, p x) := by
  sorry

--  ### Exercise (5 stars): classical_axioms (Optional) ⭐⭐⭐⭐⭐

--  For those who like a challenge, here is an exercise adapted from the
--  Coq'Art book by Bertot and Casteran (p. 123). Each of the following
--  five statements, together with `ExcludedMiddle`, can be considered as
--  characterizing classical logic. We can't prove any one of them in Lean
--  without `Classical`, but adding any *one* of them as an axiom allows us
--  to work classically.
--
--  To see this, prove that all six propositions (these five plus
--  `ExcludedMiddle`) are equivalent.
--
--  Hint: Rather than considering all pairs of statements pairwise, prove a
--  single circular chain of implications that connects them all. You
--  should not use `by_cases`, as this implicitly introduces a dependency
--  on `ExcludedMiddle`.

def Peirce := ∀ a b : Prop, ((a → b) → a) → a

def NotNot := ∀ a : Prop, ¬ ¬ a → a

def DeMorganNotAndNot := ∀ a b : Prop, ¬ (¬ a ∧ ¬ b) → a ∨ b

def ImpOr := ∀ a b : Prop, (a → b) → (¬ a ∨ b)

def ConsequentiaMirabilis := ∀ a : Prop, (¬ a → a) → a

--  FILL IN HERE

-- Built on 2026-08-31 12:07 UTC

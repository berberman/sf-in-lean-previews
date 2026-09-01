import LF.Basics
import LF.Induction
import LF.Poly
import LF.Tactics
import LF.CustomTactics

import SFLCompat

--  # Logic in Lean

--  So far, we have seen:
--
--  - *propositions*: mathematical statements, so far only
--    of 3 kinds:
--
--    - equality propositions (`e1 = e2`)
--    - implications (`a -> b`)
--    - quantified propositions (`∀ x, a`)
--
--  - *proofs*: ways of presenting evidence for the truth of
--    a proposition
--
--  In this chapter we will introduce several more flavors
--  of both propositions and proofs.
--
--  Like everything in Lean, well-formed propositions have a
--  *type*:

--  ## The `Prop` Type

#check (∀ n m : Nat, n + m = m + n : Prop)

--  Note that *all* syntactically well-formed propositions
--  have type `Prop` in Lean, regardless of whether they are
--  true or not.
--
--  Simply *being* a proposition is one thing; being
--  *provable* is a different thing!

#check (2 = 2 : Prop)
#check (3 = 2 : Prop)
#check (∀ n : Nat, n = 2 : Prop)

--  So far, we've seen one primary place where propositions
--  can appear: in `theorem` declarations.

theorem plus_2_2_is_4 : 2 + 2 = 4 := rfl

--  Propositions are first-class entities. For example, we
--  can name them:

def PlusClaim : Prop := 2 + 2 = 4

#check PlusClaim

--  Output:
--    PlusClaim : Prop

theorem plusClaim_is_true : PlusClaim := rfl

--  We can also write *parameterized* propositions — that
--  is, functions that take arguments of some type and
--  return a proposition.

def Nat.IsThree (n : Nat) : Prop := n = 3

#check (Nat.IsThree)

--  Output:
--    Nat.IsThree : Nat → Prop

--  In Lean, functions that return propositions are said to
--  define *properties* of their arguments.
--
--  For instance, here's a (polymorphic) property defining
--  the familiar notion of an *injective function*.

def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

theorem succ_inj' : Injective Nat.succ := by
  intro x y h
  injection h

--  The familiar equality operator `=` is a (binary)
--  function that returns a `Prop`. The expression `n = m`
--  is notation for `Eq n m`. Because `Eq` can be used with
--  elements of any type, it is also polymorphic:

#check Eq

--  Output:
--    Eq.{u_1} {α : Sort u_1} : α → α → Prop

--  As a convenience, Lean will cast booleans by equating
--  them to `true`, which is why checking them against
--  `Prop` succeeds. It also casts boolean equalities to
--  propositions by equating to `true`, and boolean
--  inequalities by equating to `false`. For clarity, we
--  will avoid relying on these implicit casts.

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

--  The *conjunction*, or *logical and*, of propositions `a`
--  and `b` is written `a ∧ b`; it represents the claim that
--  both `a` and `b` are true.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  /- A proof of a conjunction is a pair of proofs of the two components.
      To prove a conjunction, we build a pair using `constructor`. -/
  constructor
  · rfl /- 3 + 4 = 7 -/
  · rfl /- 2 * 2 = 4 -/

--  The constructor for conjunction is `And.intro`, which
--  concludes that `a ∧ b` given that `a` and `b` hold
--  individually.

#check And.intro

--  Output:
--    And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

--  We can also apply the constructor for the conjunction
--  explicitly.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  · rfl /- 3 + 4 = 7 -/
  · rfl /- 2 * 2 = 4 -/

--  Rather than applying the constructor, we can explicitly
--  provide the arguments to the constructor as an `exact`
--  proof.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact And.intro rfl rfl

--  We can also use Lean's anonymous constructor notation
--  `⟨..., ...⟩`, which works on constructors for proofs as
--  well.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact ⟨rfl, rfl⟩

--  So much for proving conjunctive statements. To go in the
--  other direction — i.e., to *use* a conjunctive
--  hypothesis to help prove something else — we can use
--  `obtain` to obtain the components.

example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  sorry

--  We can also match on `h` right at the point where we
--  introduce it, instead of introducing and then
--  destructing it:

example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro ⟨hn, hm⟩
  rw [hn, hm]

--  For the present example, both ways work. But in other
--  situations, we may wind up with a conjunctive hypothesis
--  in the middle of a proof...

example (n m : Nat) (h : n + m = 0) : n * m = 0 := by
  sorry

--  The infix notation `∧` is actually just syntactic sugar
--  for `And a b`. That is, `And` is a Lean operator that
--  takes two propositions as arguments and yields a
--  proposition.

#check And

--  Output:
--    And (a b : Prop) : Prop

--  ### Disjunction

--  Another important connective is the *disjunction*, or
--  *logical or*, of two propositions: `a ∨ b` is true when
--  either `a` or `b` is. This infix notation stands for
--  `Or a b`, where `Or : Prop -> Prop -> Prop`.
--
--  To use a disjunctive hypothesis in a proof, we proceed
--  by case analysis — which, as with other data types like
--  `Nat`, is done using `cases`. The two cases are `inl`
--  (for "left injection", or "in the left case") and `inr`
--  (for "right injection", or "in the right case").

theorem Nat.factor_is_zero (n m : Nat) (h : n = 0 ∨ m = 0) : n * m = 0 := by
  cases h with
  /- `n = 0` -/
  | inl hn => rw [hn, Nat.zero_mul]
  /- `m = 0` -/
  | inr hm => rw [hm, Nat.mul_zero]

--  Rather than performing case analysis via `cases`, we can
--  also use `obtain` to match on the two possible
--  injections, much like with `obtain` and `∧`.

theorem and_is_false (b1 b2 : Bool) (h : (b1 = false) ∨ (b2 = false)) :
    (b1 && b2) = false := by
  obtain hb1 | hb2 := h
  · rw [hb1, Bool.false_and]
  · rw [hb2, Bool.and_false]

--  Conversely, to show that a disjunction holds, it
--  suffices to show that one of its sides holds. This can
--  be done via the tactics `left` and `right`. As their
--  names imply, the first one requires proving the left
--  side of the disjunction, while the second requires
--  proving the right side. Here is a trivial use...

theorem or_intro_l (a b : Prop) (h : a) : a ∨ b := by
  left; exact h

--  ... and here is a slightly more interesting example
--  requiring both `left` and `right`:

theorem Nat.zero_or_succ (n : Nat) : n = 0 ∨ n = (n + 1).pred := by
  sorry

--  ### Exercise (2 stars): mul_is_zero ⭐⭐

theorem Nat.mul_is_zero (n m : Nat) (h : n * m = 0) : n = 0 ∨ m = 0 := by
  sorry

--  ### Exercise (1 star): or_commute ⭐

theorem or_commute (a b : Prop) (h : a ∨ b) : b ∨ a := by
  sorry

--  ### Falsehood and Negation

--  Up to this point, we have mostly been concerned with
--  proving "positive" statements — addition is commutative,
--  appending lists is associative, etc. We are sometimes
--  also interested in negative results, demonstrating that
--  some proposition is *not* true. Such statements are
--  expressed with the logical negation operator `¬`, which
--  is a prefix notation for `Not`.
--
--  To see how negation works, recall the *principle of
--  explosion* from the `Tactics` chapter, which asserts
--  that, if we assume a contradiction, then any other
--  proposition can be derived.
--
--  Following this intuition, we could define `¬ a` ("not
--  `a`") as `∀ c, a → c`. Lean makes an equivalent but
--  slightly different choice, defining `¬ a` as
--  `a → False`, where `False` is a specific unprovable
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

--  Since `False` is a contradictory proposition, the
--  principle of explosion also applies to it. If we can get
--  `False` into the context, we can use `cases` on it to
--  complete any goal:

theorem ex_falso_quodlibet (a : Prop) (h : False) : a := by
  cases h

--  Inequality is a very common form of negated statement,
--  so there is a special notation for it: `≠`, which is
--  infix notation for `Ne`.

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

--  It takes a little practice to get used to working with
--  negation in Lean. Even though *you* may see perfectly
--  well why a claim involving negation holds, it can be a
--  little tricky at first to see how to make Lean
--  understand it!
--
--  Here are proofs of a few familiar facts to help get you
--  warmed up.

theorem not_False : ¬ False := by
  intro h; exact h

theorem contradiction_implies_anything (a b : Prop) (h : a ∧ ¬ a) : b := by
  sorry

theorem double_neg (a : Prop) (ha : a) : ¬ ¬ a := by
  sorry

--  Since inequality involves a negation, getting
--  comfortable with it also often requires a little
--  practice.
--
--  A useful trick: if you are trying to prove a nonsensical
--  goal, apply `ex_falso_quodlibet` to change the goal to
--  `False`. This makes it easier to use assumptions of the
--  form `¬ a`, and in particular of the form `x ≠ y`.

theorem not_true_is_false (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true =>
    rw [Ne, Not] at h
    apply ex_falso_quodlibet
    apply h
    rfl

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will
--  we need besides `intro`, `apply`, and `exact`?
--
--      ∀ α : Type, ∀ x y : α, x = y ∧ x ≠ y → False
--
--  1. `intro`, `apply`, and `exact` suffice
--  2. `cases`
--  3. `left` and/or `right`
--  4. `cases` and `left` and/or `right`
--  5. none of the above

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will
--  we need besides `intro`, `apply`, and `exact`?
--
--      ∀ a b : Prop, a ∨ b → ¬ ¬ (a ∨ b)
--
--  1. `intro`, `apply`, and `exact` suffice
--  2. `cases`
--  3. `left` and/or `right`
--  4. `cases` and `left` and/or `right`
--  5. none of the above

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will
--  we need besides `intro`, `apply`, and `exact`?
--
--      ∀ a b : Prop, a → (a ∨ ¬ ¬ b)
--
--  1. `intro`, `apply`, and `exact` suffice
--  2. `cases`
--  3. `left` and/or `right`
--  4. `cases` and `left` and/or `right`
--  5. none of the above

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will
--  we need besides `intro`, `apply`, and `exact`?
--
--      ∀ a b : Prop, a ∨ b → (¬ ¬ a) ∨ (¬ ¬ b)
--
--  1. `intro`, `apply`, and `exact` suffice
--  2. `cases`
--  3. `left` and/or `right`
--  4. `cases` and `left` and/or `right`
--  5. none of the above

--   ----------------------------------------

--  _Quiz:_

--  To prove the following proposition, which tactics will
--  we need besides `intro`, `apply`, and `exact`?
--
--      ∀ a : Prop, 1 = 0 → (a ∨ ¬ a)
--
--  1. `intro`, `apply`, and `exact` suffice
--  2. `contradiction`
--  3. `left` and/or `right`
--  4. `contradiction` and `left` and/or `right`
--  5. none of the above

--   ----------------------------------------

--  ## Truth

--  Besides `False`, Lean's standard library also defines
--  `True`, a proposition that is trivially true. To prove
--  it, we use the constructor `True.intro` explicitly, or
--  the anonymous constructor `⟨⟩`, or the `constructor`
--  tactic.

example : True := by exact True.intro
example : True := True.intro
example : True := by exact ⟨⟩
example : True := ⟨⟩
example : True := by constructor

--  Unlike `False`, which is used extensively, `True` is
--  used relatively rarely: it is trivial (and therefore
--  uninteresting) to prove as a goal, and it provides no
--  useful information when it appears as a hypothesis.

--  ### Logical Equivalence

--  The handy "if and only if" connective, which asserts
--  that two propositions have the same truth value, is a
--  structure containing the two implication directions.
--  `a ↔ b` is notation for `Iff a b`.

--  You can use `Iff.mp` to access the forward direction of
--  the iff, `Iff.mpr` to access the backwards direction,
--  and `Iff.intro` to convert a goal of the form `a ↔ b` to
--  two goals of the form `a → b` and `b → a`.

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
  sorry

theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  constructor
  · apply not_true_is_false
  · intro h; rw [h]; intro h'; contradiction

--  ### Exercise (1 star): iff_properties (Optional) ⭐

--  Using the above proof that `↔` is symmetric (`iff_sym`)
--  as a guide, prove that it is also reflexive and
--  transitive.

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

--  Conversely, if we have an existential hypothesis
--  `∃ x, a` in the context, we can destructure it to obtain
--  a witness `x` and a hypothesis stating that `a` holds of
--  `x`.

example n : (∃ m, n = m + 4) → (∃ o, n = o + 2) := by
  intro ⟨m, hm⟩
  exists (m + 2)

--  ## Recap: Logical Connectives in Lean

--  Connectives introduced in this chapter:
--
--  - `a ∧ b` (conjunction):
--
--    - introduced with `constructor`
--
--    - eliminated with `intro ⟨ha, hb⟩` or
--      `obtain ⟨ha, hb⟩ := h`
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
--    - eliminated with `intro ⟨hab, hba⟩`,
--      `obtain ⟨hab, hba⟩ := h`, or `Iff.mp` and `Iff.mpr`
--
--  - `∃ x : α, a` (existential):
--
--    - introduced with `exists y`
--
--    - eliminated with `intro ⟨x, Hx⟩` or
--      `obtain ⟨x, Hx⟩ := H`
--
--  Fundamental connectives we've been using since the
--  beginning:
--
--  - equality (`x = y`)
--  - implication (`a → b`)
--  - universal quantification (`∀ x, a`)

--  ## Programming with Propositions

--  What does it mean to say that "an element `x` occurs in
--  a list `l`"?
--
--  - If `l` is the empty list, then `x` cannot occur in it,
--    so the property "`x` appears in `l`" is simply false.
--
--  - Otherwise, `l` has the form `[x' :: l']`. In this
--    case, `x` occurs in `l` if it is equal to `x'` or if
--    it occurs in `l'`.

--  We can translate this directly into a straightforward
--  recursive function taking an element and a list and
--  returning... a proposition!

def List.In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'

theorem List.In_nil {α : Type} {x : α} : ¬ (List.In x []) := by
  rw [List.In]; intro h; assumption

theorem List.In_cons {α : Type} {x x' : α} {xs : List α} : List.In x (x' :: xs) = (x = x' ∨ List.In x xs) := rfl

--  When `List.In` is applied to a concrete list, it expands
--  into a concrete sequence of nested disjunctions.

example : List.In 4 [1, 2, 3, 4, 5] := by
  sorry

example (n : Nat) (h : List.In n [2, 4]) : ∃ n' : Nat, n = 2 * n' := by
  sorry
    /- (Notice the use of the empty pattern to discharge the last case.) -/

--  We can also reason about more generic statements
--  involving `List.In`.

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

--  ## Applying Theorems to Arguments

--  Lean also treats *proofs* as first-class objects!

--  We have seen that we can use `#check` to ask Lean
--  whether an expression has a given type:

#check (Nat.add : Nat → Nat → Nat)

--  We can also use it to check what theorem a particular
--  identifier refers to:

#check Nat.add_comm

--  Output:
--    Nat.add_comm (n m : Nat) : n + m = m + n

#check Nat.add_assoc

--  Output:
--    Nat.add_assoc (n m k : Nat) : n + m + k = n + (m + k)

--  Lean checks the *statements* of the `Nat.add_comm` and
--  `Nat.add_assoc` theorems in the same way that it checks
--  the *type* of any term (e.g. `Nat.add`). Leaving off the
--  colon and the type, Lean prints these types in the
--  infoview for us.
--
--  Why?
--
--  The reason is that the identifier `Nat.add_comm`
--  actually refers to a *proof object* — a logical
--  derivation establishing the truth of the statement
--  `∀ n m : Nat, n + m = m + n`. The type of this object is
--  the proposition that it is a proof of.
--
--  The type of an ordinary function tells us what we can do
--  with it.
--
--  - If we have a term of type `Nat → Nat → Nat`, we can
--    give it two `Nat`s as arguments and get a `Nat` back.
--    Similarly, the statement of a theorem tells us what we
--    can use that theorem for.
--
--  - If we have a term of type
--    `∀ n m : Nat, n = m → n + n = m + m`, and we provide
--    it two numbers `n` and `m` and a third "argument" of
--    type `n = m`, we get back a proof object of type
--    `n + n = m + m`.

--  Lean actually allows us to *apply* a theorem as if it
--  were a function. This is often handy in proof scripts —
--  e.g., suppose we want to prove the following:

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

--  It appears at first sight that we ought to be able to
--  prove this by rewriting with `Nat.add_comm` twice to
--  make the two sides match. The problem is that the second
--  rewrite undoes the effect of the first, leaving us back
--  where we started...
--
--  We encountered similar issues back in the Induction
--  chapter, and we saw that we can fix them by applying
--  `Nat.add_comm` to the arguments we want it to be
--  instantiated with, in much the same way as we apply a
--  polymorphic function to a type argument. Then the
--  rewrite is forced to happen exactly where we want it.

example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm]
  rw [Nat.add_comm z y]

--  The fact that implications are functions means we can
--  prove them by explicitly providing a function.

theorem identity {a : Prop} : a → a := fun h => h

namespace FunctionTheoremQuiz

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

end FunctionTheoremQuiz

--  ## Working with Decidable Properties

--  We've seen two different ways of expressing logical
--  claims in Lean: with *booleans* (of type `Bool`), and
--  with *propositions* (of type `Prop`). Here are the key
--  differences between `Bool` and `Prop`:
--
--      |                     | `Bool` | `Prop` |
--      | ------------------- | ------ | ------ |
--      | decidable?          | yes    | no     |
--      | useable with match? | yes    | no     |

--  Since functions in Lean by default must terminate on all
--  inputs, a terminating function of type `Nat → Bool` is a
--  *decision procedure* — i.e., it yields `true` or `false`
--  on all inputs.
--
--  For example, `Nat.even` is a decision procedure for the
--  property "is even".

--  Since `Prop` includes *both* decidable and undecidable
--  properties, we have two options when we want to
--  formalize a property that happens to be decidable: we
--  can express it either as a boolean computation, or as a
--  function into `Prop`.
--
--  For instance, to claim that a number `n` is even, we can
--  say either that `Nat.even n` evaluates to `true`...

example : Nat.even 42 = true := rfl

--  ... or that there exists some `k` such that
--  `n = double k`.

example : Nat.Even 42 := by rw [Nat.Even]; exists 21

--  Of course, it would be deeply strange if these two
--  characterizations of evenness did not describe the same
--  set of natural numbers! Fortunately, they do!
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

--  In view of this theorem, we can say that the boolean
--  computation `Nat.even n` is *reflected* in the truth of
--  the proposition `∃ k, n = Nat.double k`.

--  Similarly, to state that two numbers `n` and `m` are
--  equal, we can say either
--
--  1. that `n == m` returns `true`, or
--  2. that `n = m`.
--
--  Again, these two notions are equivalent:
--
--  (For the reverse direction we need the simple fact that
--  `==` is reflexive.)

--  Don't worry too much about `Nat.beq_eq_true_eq` yet, we
--  need this from Lean because `n == m` is a wrapper of
--  `DecidableEq Nat`. We will go over this in the
--  Typeclasses chapter.

theorem beq_eq_true (n m : Nat) :
    (n == m) = true ↔ n = m := by
  rw [Nat.beq_eq_true_eq]

--  So what should we do in situations where some claim
--  could be formalized as either a proposition or a boolean
--  computation? Which should we choose?
--
--  In general, *both* can be useful. For example, booleans
--  are more useful for defining functions, since we can
--  test whether they are true using conditional
--  expressions.

def is_even_prime (n : Nat) : Bool :=
  bif n == 2 then true else false

--  The most direct way to prove this is to give the value
--  of `k` explicitly.

example : Nat.Even 100 := by
  exists 50

--  The proof of the corresponding boolean statement is
--  simpler, because we don't have to invent the witness
--  `50`: computation does it for us!

example : Nat.even 100 = true := rfl

--  Now, the useful observation is that, since the two
--  notions are equivalent, we can use the boolean
--  formulation to prove the other one without mentioning
--  the value 50 explicitly:

example : Nat.Even 100 := by
  obtain ⟨h, _⟩ := Nat.even_bool_prop 100
  apply h; rfl

--  Although we haven't gained much in terms of proof-script
--  simplicity in this case, larger proofs can often be made
--  considerably simpler by the use of reflection.
--
--  As an extreme example, a famous mechanized proof of the
--  even more famous *four colour theorem* uses reflection
--  to reduce the analysis of hundreds of different cases to
--  a boolean computation.
--
--  Another advantage of booleans is that the *negation* of
--  a claim about booleans is straightforward to state and
--  (when true) to prove: simply flip the expected boolean
--  result.

example : Nat.even 101 = false := rfl

--  In contrast, propositional negation can be difficult to
--  work with directly. For example, suppose we state the
--  nonevenness of `101` propositionally:
--
--  Proving this directly — by assuming that there is some
--  `n` such that `101 = Nat.double n` and then somehow
--  reasoning to a contradiction — would be rather
--  complicated.
--
--  But if we convert it to a claim about the boolean
--  `Nat.even` function, we can let Lean do the work for us.

example : ¬ Nat.Even 101 := by
  sorry

--  Conversely, there are situations where it can be easier
--  to work with propositions rather than booleans. In
--  particular, knowing that `(n == m) = true` is generally
--  of little direct help in the middle of a proof involving
--  `n` and `m`. But if we convert the statement to the
--  equivalent form `n = m`, then we can easily rewrite with
--  it.

theorem add_beq_true (n m p : Nat) (h : (n == m) = true) :
    (n + p == m + p) = true := by
  sorry

--  ## The Logic of Lean

--  Lean's logical core is a "metalanguage for mathematics"
--  in the same sense as familiar foundations for
--  paper-and-pencil math, like Zermelo–Fraenkel Set Theory
--  (ZFC).
--
--  Mostly, the differences are not too important, but a few
--  points are useful to understand.

--  ### Propositional Extensionality

--  Lean's logic is quite minimalistic. This means that one
--  occasionally encounters cases where translating standard
--  mathematical reasoning into Lean is cumbersome - or even
--  impossible - unless we enrich its core logic with
--  additional axioms.

--  A first instance has to do with equality of
--  propositions.

#check (∀ a b : Prop, (a ∧ b) = (b ∧ a) : Prop)

--  This is an equality between two conjunctions, which
--  itself is also a proposition. It states that commuted
--  conjunctions are equal propositions. However, we cannot
--  prove this equality by reflexivity, as the two sides
--  don't compute to the same term, and we cannot proceed by
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

--  However, we *can* prove that `a ∧ b` implies `b ∧ a`,
--  and vice versa -- this is the commutativity of
--  conjunction that we have seen earlier.

#check and_comm

--  Output:
--    and_comm {a b : Prop} : a ∧ b ↔ b ∧ a

--  Since it would be convenient to be able to rewrite
--  propositions from one side of `↔` to the other, Lean
--  provides an axiom to turn `↔` into `=`, which is called
--  *propositional extensionality* (`propext`).

#print propext

--  Output:
--    axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b

--  Lean provides an `ext` tactic that applies `propext` for
--  us. We can use it to show that commuted conjoined
--  propositions are equal. Similarly, we can use it to show
--  that reassociated conjoined propositions are equal as
--  well.

theorem and_comm_eq (a b : Prop) : (a ∧ b) = (b ∧ a) := by
  ext; apply and_comm

theorem and_assoc_eq (a b c : Prop) : ((a ∧ b) ∧ c) = (a ∧ (b ∧ c)) := by
  ext; apply and_assoc

--  Here is an example of where using `=` instead of `↔` is
--  more convenient: we show that it's possible to "flip"
--  three conjoined propositions.
--
--  One way to prove this is to construct the `↔`, destruct
--  the `↔`s provided by `and_comm` and `and_assoc`, and
--  apply the resulting implications a few times. But this
--  is a lot of hassle, when the proof is conceptually
--  simple: we flip `b` and `c`, then we flip that
--  conjunction with `a`, and we finish by associativity. By
--  using `and_comm_eq`, this is easily done by rewriting
--  equal propositions.

theorem and_comm_flip (a b c : Prop) : (a ∧ b ∧ c) ↔ (c ∧ b ∧ a) := by
  rw [and_comm_eq b c, and_comm_eq a, and_assoc_eq]

--  The pattern of deriving an equality of propositions out
--  of `↔` then rewriting by that equality is so common that
--  Lean will implicitly cast `↔` to `=`, allowing you to
--  rewrite on `↔` directly. Notice that `rw` is also able
--  to close goals of the form `a ↔ a` by reflexivity.

theorem and_comm_flip' (a b c : Prop) : (a ∧ b ∧ c) ↔ (c ∧ b ∧ a) := by
  rw [@and_comm b c, @and_comm a, and_assoc]

--  Under the hood, this proof still uses `propext`, which
--  you can check by asking for all of the axioms used by a
--  declaration.

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

--  The following theorem is an alternative "negative"
--  formulation of `beq_eq_true` that is more convenient in
--  certain situations. (We'll see examples in later
--  chapters.) Hint: `not_true_iff_false`.

theorem beq_neq_false (n m : Nat) : (n == m) = false ↔ n ≠ m := by
  sorry

--  ### Functional Extensionality

--  We can also write propositions claiming that two
--  *functions* are equal to each other. In some cases, we
--  can also prove that two functions are equal by
--  reflexivity when both reduce to the same expression:

example : (fun x => x + 2) = (fun x => x + (Nat.pred 3)) := rfl

--  In general, functions can be equal for more interesting
--  reasons. In common mathematical practice, two functions
--  `f` and `g` are considered equal if they produce the
--  same output on every input:
--
--      (∀ x, f x = g x) → f = g
--
--  This is known as *functional extensionality*, which Lean
--  provides as `funext`.

#check (fun f g => funext (f := f) (g := g) :
    ∀ {α β : Type} (f g : α → β), (∀ x, f x = g x) → f = g)

--  Now we can prove some intuitively obvious equalities
--  about functions that would otherwise not be provable
--  without `funext`.

theorem add_comm_fun : (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
  apply funext; intro n
  apply funext; intro m
  exact Nat.add_comm n m

--  The `ext` tactic will also apply `funext` as many times
--  as possible, introducing all variables in one go. (The
--  singular version of the tactic is `ext1`.)

theorem add_comm_fun' : (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
  ext n m; exact Nat.add_comm n m

--   ----------------------------------------

--  _Quiz:_

--  Is the following statement provable by just `rfl`,
--  without `funext`?
--
--      (fun xs => 1 :: xs) = (fun xs => [1] ++ xs)
--
--  1. Yes
--  2. No

--   ----------------------------------------

--  #### Other Extensionality Principles

--  We can use `ext` on pairs as:

example {n : Nat} {p : Nat × Nat} (hx_fst : p.fst = n + 1) (hx_snd : p.snd = 0) :
    (n + 1, 0) = p := by
  ext -- uses the `Prod.ext` lemma
  · rw [hx_fst]
  · rw [hx_snd]

--  ### Exercise (2 stars): prod_ext_example ⭐⭐

--  Now, use `ext1` to prove the following. Remember that
--  `dsimp only` simplifies projections like `(a, b).fst` to
--  `a`.

example {m : Nat} {p : Nat × Nat} (hp_snd : p.snd = 4) (hp_fst : p.fst = m) :
    ((p.fst + 1, 2), (p.fst, 4)) = ((m + 1, p.snd - 2), p) := by
  sorry

--  ### Classical vs. Constructive Logic

--  The following reasoning principle is *not* derivable
--  with the tools we've seen so far:

def ExcludedMiddle := ∀ a : Prop, a ∨ ¬ a

--  Logical systems in which excluded middle does not hold
--  are referred to as *constructive logics*. They are so
--  called because to prove a proposition, we must give a
--  construction for it; for instance, a proof of `∃ x, p x`
--  is proven by providing a particular value of `x`.
--
--  Logical systems in which excluded middle does hold, such
--  as ZFC set theory, are referred to as *classical*. Lean
--  provides classical reasoning principles in the
--  `Classical` library, including excluded middle.

#check Classical.em

--  Output:
--    Classical.em (p : Prop) : p ∨ ¬p

-- Built on 2026-09-01 13:18 UTC

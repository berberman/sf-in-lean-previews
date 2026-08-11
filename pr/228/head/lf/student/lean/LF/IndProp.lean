import LF.Logic
import LF.CustomTactics

import LF.SFLCompat

-- # IndProp: Inductively Defined Propositions

-- ## Inductively Defined Propositions

-- In the Logic chapter, we looked at several ways of writing propositions,
-- including conjunction, disjunction, and existential quantification.

-- In this chapter, we bring yet another new tool into the mix: *inductively
-- defined propositions*.

-- To begin, some examples...

-- ### Example: The Collatz Conjecture

-- The *Collatz Conjecture* is a famous open problem in number theory.

-- Its statement is quite simple. First, we define a function `csf` on
-- numbers, as follows (where `csf` stands for "Collatz step function"):

def div2 (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | 1      => 0
  | n' + 2 => div2 n' + 1

def csf (n : Nat) : Nat :=
  if n.even then div2 n
  else (3 * n) + 1

-- Next, we look at what happens when we repeatedly apply `csf` to some given
-- starting number. For example, `csf 12` is `6`, and `csf 6` is `3`, so by
-- repeatedly applying `csf` we get the sequence
-- `12, 6, 3, 10, 5, 16, 8, 4, 2, 1`.

-- Similarly, if we start with `19`, we get the longer sequence
-- `19,
-- 58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
-- 4, 2, 1`.

-- Both of these sequences eventually reach `1`. The question posed by Collatz
-- was: Is the sequence starting from *any* positive natural number guaranteed
-- to reach `1` eventually?

-- To formalize this question in Lean, we might try to define a recursive
-- *function* that calculates the total number of steps that it takes for such
-- a sequence to reach `1`. You can write this definition in a standard
-- programming language, but it is rejected by Lean's termination checker,
-- since the argument to the recursive call, `csf n`, is not "obviously
-- smaller" than `n`.

/--
error: fail to show termination for
  reaches1In
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    reaches1In (csf n)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬(n == 1) = true
⊢ csf n < n
-/
#guard_msgs in
def reaches1In (n : Nat) : Nat :=
  if n == 1 then 0
  else 1 + reaches1In (csf n)

-- You can write this definition in a standard programming language. This
-- definition is, however, rejected by Lean's termination checker, since the
-- argument to the recursive call, `csf n`, is not "obviously smaller" than
-- `n`. Indeed, this isn't just a pointless limitation: functions in Lean are
-- required to be total, to ensure logical consistency.

-- Moreover, we can't fix it by devising a more clever termination checker:
-- deciding whether this particular function is total would be equivalent to
-- settling the Collatz conjecture!

-- Another idea could be to express the concept "eventually reaches `1` in the
-- Collatz sequence" as a *recursively defined property* of numbers
-- `CollatzHoldsFor' : Nat → Prop`. This is also rejected: while we could in
-- principle convince Lean that `div2 n` is smaller than `n`, we certainly
-- can't convince it that `(3 * n) + 1` is smaller than `n`!

/--
error: fail to show termination for
  CollatzHoldsFor'
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    CollatzHoldsFor' (div2 n)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n x✝ : Nat
h✝ : n.even = true
⊢ div2 n < x✝
-/
#guard_msgs in
def CollatzHoldsFor' (n : Nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if n.even then CollatzHoldsFor' (div2 n)
                   else CollatzHoldsFor' ((3 * n) + 1)

-- This recursive function is also rejected by the termination checker. In
-- principle, we could convince Lean that `div2 n` is smaller than `n` by
-- supplying an appropriate proof. However, we still can't convince it that
-- `(3 * n) + 1` is smaller than `n`!

-- Fortunately, there is another way to do it: We can express the concept
-- "reaches `1` eventually in the Collatz sequence" as an *inductively defined
-- property* of numbers. Intuitively, this property is defined by a set of
-- rules:

--                 ─────────────────── (chf_one)
--                 CollatzHoldsFor 1

--   even n = true     CollatzHoldsFor (div2 n)
--   ─────────────────────────────────────────── (chf_even)
--                  CollatzHoldsFor n

--   even n = false    CollatzHoldsFor ((3 * n) + 1)
--   ─────────────────────────────────────────────── (chf_odd)
--                  CollatzHoldsFor n

-- So there are three ways to prove that a number `n` eventually reaches `1`
-- in the Collatz sequence:

-- - `n` is `1`;
-- - `n` is even and `div2 n` eventually reaches `1`;
-- - `n` is odd and `(3 * n) + 1` eventually reaches `1`.

-- We can prove that a number reaches `1` by constructing a (finite)
-- derivation using these rules. For instance, here is the derivation proving
-- that `12` reaches `1` (where we leave out the evenness/oddness premises):

--   ─────────────────────── (chf_one)
--   CollatzHoldsFor 1
--   ─────────────────────── (chf_even)
--   CollatzHoldsFor 2
--   ─────────────────────── (chf_even)
--   CollatzHoldsFor 4
--   ─────────────────────── (chf_even)
--   CollatzHoldsFor 8
--   ─────────────────────── (chf_even)
--   CollatzHoldsFor 16
--   ─────────────────────── (chf_odd)
--   CollatzHoldsFor 5
--   ─────────────────────── (chf_even)
--   CollatzHoldsFor 10
--   ─────────────────────── (chf_odd)
--   CollatzHoldsFor 3
--   ─────────────────────── (chf_even)
--   CollatzHoldsFor 6
--   ─────────────────────── (chf_even)
--   CollatzHoldsFor 12

-- Formally in Lean, the `CollatzHoldsFor` property is *inductively defined*:

inductive CollatzHoldsFor : Nat → Prop where
  | chf_one  : CollatzHoldsFor 1
  | chf_even (n : Nat) : n.even = true →
                         CollatzHoldsFor (div2 n) →
                         CollatzHoldsFor n
  | chf_odd  (n : Nat) : n.even = false →
                         CollatzHoldsFor ((3 * n) + 1) →
                         CollatzHoldsFor n

-- What we've done here is to use Lean's `inductive` definition mechanism to
-- characterize the property "Collatz holds for..." by stating three different
-- ways in which it can hold: (1) Collatz holds for `1`, (2) if Collatz holds
-- for `div2 n` and `n` is even then Collatz holds for `n`, and (3) if Collatz
-- holds for `(3 * n) + 1` and `n` is odd then Collatz holds for `n`. This
-- Lean definition directly corresponds to the three rules we wrote informally
-- above.

-- For particular numbers, we can now prove that the Collatz sequence reaches
-- `1` (we'll look more closely at how it works a bit later in the chapter).
-- Each step applies a rule and discharges the boolean evenness premise by
-- `rfl`; the recursive premise is then reduced by the kernel from
-- `CollatzHoldsFor (div2 12)` to `CollatzHoldsFor 6`, etc.

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

-- The Collatz conjecture then states that the sequence beginning from *any*
-- positive number reaches `1`:

def collatz := ∀ n, n ≠ 0 → CollatzHoldsFor n

-- If you succeed in proving this conjecture, you've got a bright future as a
-- number theorist! But don't spend too long on it -- it's been open since
-- 1937.

-- ### Example: Binary relation for comparing numbers

-- A binary *relation* on a set `α` has Lean type `α → α → Prop`. This is a
-- family of propositions parameterized by two elements of `α` -- i.e., a
-- proposition about pairs of elements of `α`.

-- For example, one familiar binary relation on `Nat` is
-- `Le : Nat
-- → Nat → Prop`, the less-than-or-equal-to relation, which can be
-- inductively defined by the following two rules:

--     ─────── (le_refl)
--     Le n n

--      Le n m
--   ───────────── (le_step)
--   Le n (m + 1)

-- These rules say that there are two ways to show that a number is less than
-- or equal to another: either observe that they are the same number, or, if
-- the second has the form `m + 1`, give evidence that the first is less than
-- or equal to `m`.

namespace LePlayground

inductive Le : Nat → Nat → Prop where
  | refl (n : Nat)              : Le n n
  | step (n m : Nat) : Le n m → Le n (m + 1)

scoped infix:50 (priority := high) " ≤ " => Le

-- This definition is a bit simpler and more elegant than the Boolean function
-- `ble` we defined in `Basics`. As usual, `Le` and `ble` are equivalent, and
-- there is an exercise about that later.

example : 3 ≤ 5 := by
  apply Le.step; apply Le.step; exact Le.refl 3

end LePlayground

-- ### Example: Transitive Closure

-- Another example: The *transitive closure* of a relation `R` is the smallest
-- relation that contains `R` and that is transitive. This can be defined by
-- the following two rules:

--                 R x y
--            ---------------- (t_step)
--            ClosTrans R x y

--   ClosTrans R x y    ClosTrans R y z
--   ------------------------------------ (t_trans)
--            ClosTrans R x z

-- In Lean this looks as follows:

inductive ClosTrans {α: Type} (R: α→α→Prop) : α → α → Prop where
  | t_step (x y : α) :
      R x y →
      ClosTrans R x y
  | t_trans (x y z : α) :
      ClosTrans R x y →
      ClosTrans R y z →
      ClosTrans R x z

-- For example, suppose we define a "parent of" relation on a group of
-- people...

inductive Person : Type where
  | sage
  | cleo
  | ridley
  | moss

inductive ParentOf : Person → Person → Prop where
  | po_SC : ParentOf .sage .cleo
  | po_SR : ParentOf .sage .ridley
  | po_CM : ParentOf .cleo .moss

-- In this example, `sage` is a parent of both `cleo` and `ridley`; and `cleo`
-- is a parent of `moss`.

-- The `parent_of` relation is not transitive, but we can define an "ancestor
-- of" relation as its transitive closure:

def AncestorOf : Person → Person → Prop := ClosTrans ParentOf

-- Here is a derivation showing that Sage is an ancestor of Moss:

--    ———————————————————(po_SC)     ———————————————————(po_CM)
--    ParentOf .sage .cleo            ParentOf .cleo .moss
--   —————————————————————(t_step)  —————————————————————(t_step)
--   AncestorOf .sage .cleo          AncestorOf .cleo .moss
--   ————————————————————————————————————————————————————(t_trans)
--                   AncestorOf .sage .moss

example : AncestorOf .sage .moss := by
  apply ClosTrans.t_trans
  . apply ClosTrans.t_step; apply ParentOf.po_SC
  . apply ClosTrans.t_step; apply ParentOf.po_CM

-- Computing the transitive closure can be undecidable even for a relation R
-- that is decidable (e.g., the `cms` relation below), so in general we can't
-- expect to define transitive closure as a boolean function. Fortunately,
-- Lean allows us to define transitive closure as an inductive relation.

-- The transitive closure of a binary relation cannot, in general, be
-- expressed in first-order logic. The logic of Lean is, however, much more
-- powerful, and can easily define such inductive relations.

-- ### Example: Reflexive and Transitive Closure

-- As another example, the *reflexive and transitive closure* of a relation
-- `R` is the smallest relation that contains `R` and that is reflexive and
-- transitive. This can be defined by the following three rules (where we
-- added a reflexivity rule to `ClosTrans`):

--                      R x y
--              --------------------- (rt_step)
--              ClosReflTrans R x y

--              --------------------- (rt_refl)
--              ClosReflTrans R x x

--      ClosReflTrans R x y    ClosReflTrans R y z
--   ---------------------------------------------- (rt_trans)
--              ClosReflTrans R x z

inductive ClosReflTrans {α: Type} (R: α → α → Prop) : α → α → Prop where
  | rt_step (x y : α) :
      R x y →
      ClosReflTrans R x y
  | rt_refl (x : α) :
      ClosReflTrans R x x
  | rt_trans (x y z : α) :
      ClosReflTrans R x y →
      ClosReflTrans R y z →
      ClosReflTrans R x z

-- For instance, this enables an equivalent definition of the Collatz
-- conjecture. First we define a binary relation corresponding to the "Collatz
-- step function" `csf`:

def cs (n m : Nat) : Prop := csf n = m

-- This Collatz step relation can be used in conjunction with the reflexive
-- and transitive closure operation to define a *Collatz multi-step* (`cms`)
-- relation, expressing that a number `n` reaches another number `m` in zero
-- or more Collatz steps:

def cms (n m : Nat) : Prop := ClosReflTrans cs n m
def collatz' : Prop := ∀ (n : Nat), n ≠ 0 → cms n 1

-- This `cms` relation defined in terms of `ClosReflTrans` allows for more
-- interesting derivations than the linear ones of the directly-defined
-- `CollatzHoldsFor` relation:

--   csf 16 = 8         csf 8 = 4         csf 4 = 2         csf 2 = 1
--   ————————(rt_step)  ———————(rt_step)  ———————(rt_step)  ———————(rt_step)
--   cms 16 8           cms 8 4           cms 4 2           cms 2 1
--   —————————————————————————(rt_trans)  ————————————————————————(rt_trans)
--       cms 16 4                              cms 4 1
--       —————————————————————————————————————————————(rt_trans)
--                          cms 16 1

-- ### Exercise (1 star): clos_refl_trans_sym (manually graded) ⭐

-- How would you modify the `ClosReflTrans` definition above so as to define
-- the reflexive, symmetric, and transitive closure?

-- FILL IN HERE

-- ### Example: Permutations

-- The familiar mathematical concept of *permutation* also has an elegant
-- formulation as an inductive relation. For simplicity, let's focus on
-- permutations of lists with exactly three elements.

-- We can define such permutations by the following rules:

--      ───────────────────────── (perm3_swap12)
--      Perm3 [a, b, c] [b, a, c]

--      ───────────────────────── (perm3_swap23)
--      Perm3 [a, b, c] [a, c, b]

--   Perm3 l₁ l₂       Perm3 l₂ l₃
--   ───────────────────────────── (perm3_trans)
--            Perm3 l₁ l₃

-- For instance we can derive `Perm3 [1, 2, 3] [3, 2, 1]` as follows:

--   ─────────────────────────(perm3_swap12)   ─────────────────────────(perm3_swap23)
--   Perm3 [1, 2, 3] [2, 1, 3]                 Perm3 [2, 1, 3] [2, 3, 1]
--   ──────────────────────────────────────────────────(perm3_trans)   ─────────────────────────(perm3_swap12)
--   Perm3 [1, 2, 3] [2, 3, 1]                                          Perm3 [2, 3, 1] [3, 2, 1]
--   ──────────────────────────────────────────────────────────────────────────(perm3_trans)
--   Perm3 [1, 2, 3] [3, 2, 1]

-- This definition says:

-- - If `l₂` can be obtained from `l₁` by swapping the first and second
--   elements, then `l₂` is a permutation of `l₁`.

-- - If `l₂` can be obtained from `l₁` by swapping the second and third
--   elements, then `l₂` is a permutation of `l₁`.

-- - If `l₂` is a permutation of `l₁` and `l₃` is a permutation of `l₂`, then
--   `l₃` is a permutation of `l₁`.

-- In Lean, we can define `Perm3` as follows:

inductive Perm3 {α : Type} : List α → List α → Prop where
  | perm3_swap12 (a b c : α) :
      Perm3 [a, b, c] [b, a, c]
  | perm3_swap23 (a b c : α) :
      Perm3 [a, b, c] [a, c, b]
  | perm3_trans (l₁ l₂ l₃ : List α) :
      Perm3 l₁ l₂ → Perm3 l₂ l₃ → Perm3 l₁ l₃

-- ### Exercise (1 star): perm (manually graded) ⭐

-- According to this definition, is `[1, 2, 3]` a permutation of itself?

-- ### Example: Evenness (yet again)

-- We've already seen two ways of stating a proposition that a number `n` is
-- even: We can say

-- (1) `even n = true` (using the recursive boolean function `even`), or

-- (2) `∃ k, n = double k` (using an existential quantifier).

-- A third possibility, which we'll use as a simple running example in this
-- chapter, is to say that a number is even if we can *establish* its evenness
-- from the following two rules:

--       ---- (ev_0)
--       Ev 0

--       Ev n
--   ------------ (ev_succ_succ)
--   Ev (n + 2)

-- Intuitively these rules say that:

-- - The number `0` is even.
-- - If `n` is even, then `n + 2` is even.

-- (Defining evenness in this way may seem a bit confusing, since we have
-- already seen two perfectly good ways of doing it. It makes a convenient
-- running example because it is simple and compact, but we will soon return
-- to the more compelling examples above.)

-- To illustrate how this new definition of evenness works, let's imagine
-- using it to show that `4` is even:

--           ———— (ev_0)
--           Ev 0
--       ———————————— (ev_succ_succ)
--       Ev (S (S 0))
--   ———————————————————— (ev_succ_succ)
--   Ev (S (S (S (S 0))))

-- In words, to show that `4` is even, by rule `ev_succ_succ`, it suffices to
-- show that `2` is even. This, in turn, is again guaranteed by rule
-- `ev_succ_succ`, as long as we can show that `0` is even. But this last fact
-- follows directly from the `ev_0` rule.

-- We can translate the informal definition of evenness from above into a
-- formal `inductive` declaration, where each "way that a number can be even"
-- corresponds to a separate constructor:

inductive Ev : Nat → Prop where
  | ev_0                       : Ev 0
  | ev_succ_succ (n : Nat) (H : Ev n) : Ev (n + 2)

-- Such definitions are interestingly different from previous uses of
-- `inductive` for defining inductive datatypes like `Nat` or `List`. For one
-- thing, we are defining not a `Type` (like `Nat`) or a function yielding a
-- `Type` (like `List`), but rather a function from `Nat` to `Prop` -- that
-- is, a property of numbers. But what is really new is that, because the
-- `Nat` argument of `Ev` appears to the *right* of the colon on the first
-- line, it is allowed to take *different* values in the types of different
-- constructors: `0` in the type of `ev_0` and `(n + 2)` in the type of
-- `ev_succ_succ`. Accordingly, the type of each constructor must be specified
-- explicitly (after a colon), and each constructor's type must have the form
-- `Ev n` for some natural number `n`.

-- In contrast, recall the definition of `List`:

sf_expect_failure
  inductive List (α:Type) : Type where
    | nil
    | cons (x : α) (l : List α)

-- or (equivalently but more explicitly):

sf_expect_failure
  inductive List (α:Type) : Type where
    | nil                       : List α
    | cons (x : α) (l : List α) : List α

-- This definition introduces the `α` parameter *globally*, to the *left* of
-- the colon, forcing the result of `nil` and `cons` to be the same type
-- (i.e., `List α`). But if we had tried to bring `Nat` to the left of the
-- colon in defining `Ev`, we would have seen an error:

/--
error: Mismatched inductive type parameter in
  WrongEv 0
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
-/
#guard_msgs in
inductive WrongEv (n : Nat) : Prop where
  | wrong_ev_0 : WrongEv 0
  | wrong_ev_succ_succ (H: WrongEv n) : WrongEv (n + 2)

-- In an `inductive` definition, an argument to the type constructor on the
-- left of the colon is called a "parameter", whereas an argument on the right
-- is called an "index" or "annotation."

-- For example, in `inductive List (α : Type) := ...`, the `α` is a parameter,
-- while in `inductive Ev : Nat → Prop := ...`, the unnamed `Nat` argument is
-- an index.

-- We can think of the inductive definition of `Ev` as defining a Lean
-- property `Ev : Nat → Prop`, together with two "evidence constructors":

#check (Ev.ev_0) -- Ev 0
#check Ev.ev_succ_succ -- ∀ (n : Nat) (H : Ev n) : Ev (n + 2)

-- Indeed, Lean also accepts the following equivalent definition of `Ev`

namespace EvPlayground

inductive Ev : Nat → Prop where
  | ev_0  : Ev 0
  | ev_succ_succ : ∀ (n : Nat), Ev n → Ev (n + 2)

end EvPlayground

-- These evidence constructors can be thought of as "primitive evidence of
-- evenness", and they can be used later on just like proven theorems. In
-- particular, we can use Lean's `apply` and `exact` tactics with the
-- constructor names to obtain evidence for `Ev` of particular numbers...

theorem ev_4 : Ev 4 := by
  apply Ev.ev_succ_succ; apply Ev.ev_succ_succ; exact Ev.ev_0

-- ... or we can use function application syntax to combine several
-- constructors:

theorem ev_4' : Ev 4 := by
  exact Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)

-- ... or we can also use the `constructor` tactic we saw earlier to select
-- the appropriate inductive constructor

theorem ev_4'' : Ev 4 := by
  constructor; constructor; constructor

-- In this way, we can also prove theorems that have hypotheses involving
-- `Ev`.

theorem ev_plus4 (n : Nat) (h : Ev n) : Ev (4 + n) := by
  rw [Nat.add_comm]
  exact (Ev.ev_succ_succ _ (Ev.ev_succ_succ _ h))

-- ### Exercise (1 star): ev_double ⭐

theorem ev_double (n : Nat) : Ev n.double := by
  sorry

-- ### Constructing Evidence for Permutations

-- Similarly we can apply the evidence constructors to obtain evidence of
-- `Perm3 [1, 2, 3] [3, 2, 1]`:

theorem Perm3_rev : Perm3 [1, 2, 3] [3, 2, 1] := by
  apply Perm3.perm3_trans (l₂:= [2, 3, 1])
  . apply Perm3.perm3_trans (l₂:=[2, 1, 3])
    . apply Perm3.perm3_swap12
    . apply Perm3.perm3_swap23
  . apply Perm3.perm3_swap12

-- And again we can equivalently use function application syntax to combine
-- several constructors. (Note that the Lean type checker can infer not only
-- types, but also Nats and List, when they are clear from the context.)

theorem Perm3_rev' : Perm3 [1, 2, 3] [3, 2, 1] := by
  exact (Perm3.perm3_trans _ [2, 3, 1] _
          (Perm3.perm3_trans _ [2, 1, 3] _
            (Perm3.perm3_swap12 _ _ _)
            (Perm3.perm3_swap23 _ _ _))
          (Perm3.perm3_swap12 _ _ _))

-- So the informal derivation trees we drew above are not too far from what's
-- happening formally. Formally we're using the evidence constructors to build
-- *evidence trees*, similar to the finite trees we built using the
-- constructors of data types such as Nat, List, binary trees, etc.

-- ### Exercise (1 star): Perm3 ⭐

theorem Perm3_ex1 : Perm3 [1, 2, 3] [2, 3, 1] := by
  sorry

theorem Perm3_refl : ∀ (α : Type) (a b c : α ), Perm3 [a, b, c] [a, b, c] := by
  sorry

-- ## Using Evidence in Proofs

-- Besides *constructing* evidence that numbers are even, we can also
-- *destruct* such evidence, reasoning about how it could have been built.

-- Defining `Ev` with an `inductive` declaration tells Lean not only that the
-- constructors `ev_0` and `ev_succ_succ` are valid ways to build evidence
-- that some number is `Ev`, but also that these two constructors are the
-- *only* ways to build evidence that numbers are `Ev`.

-- In other words, if someone gives us evidence `E` for the proposition
-- `Ev n`, then we know that `E` must be one of two things:

-- - `E = ev_0` and `n = 0`, or

-- - `E = ev_succ_succ n' E'` and `n = n' + 2`, where `E'` is evidence for
--   `Ev n'`.

-- This suggests that it should be possible to analyze a hypothesis of the
-- form `Ev n` much as we do inductively defined data structures; in
-- particular, it should be possible to argue either by *case analysis* or by
-- *induction* on such evidence. Let's look at a few examples to see what this
-- means in practice.

-- ### Destructing and Inverting Evidence

-- Suppose we are proving some fact involving a number `n`, and we are given
-- `Ev n` as a hypothesis. We already know how to perform case analysis on `n`
-- using `cases` or `induction`, generating separate subgoals for the case
-- where `n = 0` and the case where `n = n' + 1` for some `n'`. But for some
-- proofs we may instead want to analyze the evidence for `Ev n` *directly*.

-- As a tool for such proofs, we can formalize the intuitive characterization
-- that we gave above for evidence of `Ev n`, using `cases`.

theorem ev_inversion : ∀ (n : Nat),
    Ev n →
    (n = 0) ∨ ∃ n', n = n' + 2 ∧ Ev n' := by
    intro n H
    cases H
    case ev_0 =>
      left; rfl
    case ev_succ_succ n H =>
      right; exists n

-- Facts like this are often called "inversion lemmas" because they allow us
-- to "invert" some given information to reason about all the different ways
-- it could have been derived.

-- Here there are two ways to prove `Ev n`, and the inversion lemma makes this
-- explicit.

-- ### Exercise (1 star): le_inversion ⭐

-- Let's prove a similar inversion lemma for `le`.

namespace LePlayground
theorem le_inversion : ∀ (n m : Nat),
  Le n m →
  (n = m) ∨ (∃ m', m = m' + 1 ∧ Le n m') := by
  sorry

end LePlayground

-- We can use the inversion lemma that we proved above to help structure
-- proofs:

theorem ev_succ_succ_ev : ∀ n, Ev (n + 2) → Ev n := by
  intro n H
  apply ev_inversion at H
  cases H
  case inl _ => contradiction
  case inr h =>
    let ⟨n', ⟨h₁,  h₂⟩⟩ := h
    injections h₁ heq
    subst heq
    exact  h₂

-- Note how the inversion lemma produces two subgoals, which correspond to the
-- two ways of proving `Ev`. The first subgoal is a contradiction that is
-- discharged with `contradiction`. The second subgoal makes use of
-- `injections` and `subst`.

-- We've defined a handy tactic called `inversion` that factors out this
-- common pattern, saving us the trouble of explicitly stating and proving an
-- inversion lemma for every `inductive` definition we make.

-- Here, the `inversion` tactic can detect (1) that the first case, where
-- `n = 0`, does not apply and (2) that the `n'` that appears in the
-- `ev_succ_succ` case must be the same as `n`.

-- The details of how `inversion` is implemented are beyond the scope of this
-- course, but suffice to say Lean's metaprogramming capabilities are such
-- that almost any sequence of reasoning steps can be implemented as a new
-- tactic.

theorem ev_succ_succ_ev' : ∀ n, Ev (n + 2) → Ev n := by
  intro n h
  inversion h; assumption

-- The `inversion` tactic can apply the principle of explosion to "obviously
-- contradictory" hypotheses involving inductively defined properties,
-- something that takes a bit more work using our inversion lemma. Compare:

theorem one_not_even : ¬ Ev 1 := by
  intro H; apply ev_inversion at H; cases H
  /- HIDE: OL20: Someone asked here before "Why doesn't eqn:EE work
         here??".  It has to do with the use of _ in the pattern.
         Anyway when destructing \/,/\, or exists, what we get from
         eqn:EE is only confusing for students. I think that we should
         remove all "eqn"s in these cases. I did it in this file. -/
  case inl _ => contradiction
  case inr h =>
    let ⟨n', ⟨h₁,  h₂⟩⟩ := h
    injections

theorem one_not_even' : ¬ Ev 1 := by
  intro h; inversion h

-- ### Exercise (1 star): inversion_practice ⭐

-- Prove the following result using `inversion`. (For extra practice, you can
-- also prove it using the inversion lemma.)

theorem ev_4_ev_n : ∀ n,
  Ev (n + 4) → Ev n := by
  -- ADMITTED -/
  intros n h
  inversion h
  case ev_succ_succ h' => apply ev_succ_succ_ev; exact h'

-- ### Exercise (1 star): ev5_nonsense ⭐

-- Prove the following result using `inversion`.

theorem ev5_nonsense : Ev 5 → 2 + 2 = 9 := by
  sorry

-- We can use `inversion` to re-prove some theorems from `Tactics.lean`.

-- Note that `inversion` also works on equality propositions.

theorem inversion_ex1 : ∀ (n m o : Nat),
  [n, m] = [o, o] → [n] = [m] := by
  intro n m o h
  inversion h; rfl

theorem inversion_ex2 : ∀ (n : Nat),
  n + 1 = 0 → 2 + 2 = 5 := by
  intro n h
  inversion h

-- Here's how `inversion` works in general.

-- - Suppose the name `H` refers to an assumption `P` in the current context,
--   where `P` has been defined by an `inductive` declaration.

-- - Then, for each of the constructors of `P`, `inversion h` generates a
--   subgoal in which `H` has been replaced by the specific conditions under
--   which this constructor could have been used to prove `P`.

-- - Some of these subgoals will be self-contradictory; `inversion` throws these
--   away.

-- - The ones that are left represent the cases that must be proved to establish
--   the original goal. For those, `inversion` adds to the proof context all
--   equations that must hold of the arguments given to `P` -- e.g., `n' = n` in
--   the proof of `ev_succ_succ_ev`).

-- The `ev_double` exercise above allows us to easily show that our new notion
-- of evenness is implied by the two earlier ones (since, by `even_bool_prop`
-- in chapter Logic, we already know that those are equivalent to each other).
-- To show that all three coincide, we just need the following lemma.

example (n : Nat) : Ev n → Nat.Even n := by
  /- We could try to proceed by case analysis or induction on `n`.  But
      since `Ev` is mentioned in a premise, this strategy seems
      unpromising, because (as we've noted before) the induction
      hypothesis will talk about `n-1` (which is _not_ even!).  Thus, it
      seems better to first try `inversion` on the evidence for `Ev`.
      Indeed, the first case can be solved trivially. -/
  intro h
  inversion h
  /- h = ev_0 -/
  case ev_0 => exists 0  -- (`0 = double 0` is closed by `exists`'s final `rfl`)
  /- h = ev_succ_succ n' h' -/
  case ev_succ_succ n' h' =>
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
[[
        ∃ k', n' = double k',
]]
    which is the same as the original statement, but with `n'` instead
    of `n`.  Indeed, it is not difficult to convince Lean that this
    intermediate result would suffice. -/
    have he : (∃ (k' : Nat), n' = k'.double) → (∃ (n₀ : Nat), n' + 2 = n₀.double) := by
      intro ⟨k, hk⟩; exists (k + 1); rw [Nat.double_succ, hk]
    apply he
    /- Unfortunately, now we are stuck: we are trying to prove another instance
        of the same theorem we set out to prove -- only here we are
        talking about `n'` instead of `n`. -/
    sorry

-- ### Induction on Evidence

-- If this story feels familiar, it is no coincidence: We encountered similar
-- problems in the Induction chapter, when trying to use case analysis to
-- prove results that required induction. And once again the solution is...
-- induction!

-- The behavior of `induction` on evidence is the same as its behavior on
-- data: It causes Lean to generate one subgoal for each constructor that
-- could have been used to build that evidence, while providing an induction
-- hypothesis for each recursive occurrence of the property in question.

-- To prove that a property of `n` holds for all even numbers (i.e., those for
-- which `Ev n` holds), we can use induction on `Ev n`. This requires us to
-- prove two things, corresponding to the two ways in which `Ev n` could have
-- been constructed. If it was constructed by `ev_0`, then `n=0` and the
-- property must hold of `0`. If it was constructed by `ev_succ_succ`, then
-- the evidence of `Ev n` is of the form `ev_succ_succ n' E'`, where
-- `n = n' + 2` and `h'` is evidence for `Ev n'`. In this case, the inductive
-- hypothesis says that the property we are trying to prove holds for `n'`.

-- Let's try proving that lemma again:

theorem Nat.ev_Even : ∀ n, Ev n → Even n := by
  intro n h
  induction h
  /- h = ev_0 -/
  case ev_0 => exists 0  -- (`0 = double 0` is closed by `exists`'s final `rfl`)
  /- h = ev_succ_succ n' h',  with ih : Even n' -/
  case ev_succ_succ n' h' ih =>
    let ⟨k, hk⟩ := ih
    exists k + 1; rw [double_succ, hk]

-- Here, we can see that Lean produced an `ih` that corresponds to `h`, the
-- single recursive occurrence of `Ev` in its own definition. Since `h'`
-- mentions `n'`, the induction hypothesis talks about `n'`, as opposed to `n`
-- or some other number.

-- The equivalence between the second and third definitions of evenness now
-- follows.

theorem Nat.ev_Even_iff : ∀ n, Ev n ↔ Even n := by
  intro n; apply Iff.intro
  . intro h; exact Nat.ev_Even _ h
  . intro ⟨k, hk⟩; rw [hk]; exact ev_double k

-- As we will see in later chapters, induction on evidence is a recurring
-- technique across many areas -- in particular for formalizing the semantics
-- of programming languages.

-- The following exercises provide simpler examples of this technique, to help
-- you familiarize yourself with it.

-- ### Exercise (2 stars): ev_sum ⭐⭐

theorem ev_sum : ∀ n m, Ev n → Ev m → Ev (n + m) := by
  sorry

-- ### Exercise (3 stars): ev_ev__ev (Advanced) ⭐⭐⭐

theorem ev_ev__ev : ∀ n m, Ev (n + m) → Ev n → Ev m := by
  /- Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. -/
  sorry

-- ### Exercise (3 stars): ev_plus_plus ⭐⭐⭐

-- This exercise can be completed without induction or case analysis. But, you
-- will need a clever `have` and some tedious rewriting. Hint: Is
-- `(n+m) + (n+p)` even?

theorem ev_plus_plus : ∀ n m p,
  Ev (n+m) → Ev (n+p) → Ev (m+p) := by
  sorry

-- Another example of a proposition that can be characterized both recursively
-- and inductively is the `In` predicate we defined in the Logic chapter. As a
-- reminder, the recursive definition we saw looked like this:

-- Recall the definition of `In` from last chapter:

def In' {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In' x xs'

-- We can also write this definition inductively like so:

inductive In_Inductive {α : Type} (a : α) : List α → Prop
  | head (as : List α) : In_Inductive a (a::as)
  | tail (b : α) {as : List α} : In_Inductive a as → In_Inductive a (b::as)

-- In fact, this is exactly how Lean defines this proposition, which it calls
-- `Mem` and which is written `x ∈ l` (the Unicode symbol is written in). A
-- good exercise to test your understanding of induction on evidence is to
-- prove the equivalence of these definitions:

-- ### Exercise (2 stars): in_mem ⭐⭐

theorem in_mem α (x : α) (l : List α) : List.In x l ↔ x ∈ l := by
  sorry

-- The characterizing lemmas for `∈` are called `List.mem_nil_iff` and
-- `List.mem_cons`

-- ### Multiple Induction Hypotheses

-- Recall the definition of the reflexive, transitive, closure of a relation:

namespace ClosReflTransRemainder

inductive ClosReflTrans {α: Type} (R: α → α → Prop) : α → α → Prop where
  | rt_step (x y : α) :
      R x y →
      ClosReflTrans R x y
  | rt_refl (x : α) :
      ClosReflTrans R x x
  | rt_trans (x y z : α) :
      ClosReflTrans R x y →
      ClosReflTrans R y z →
      ClosReflTrans R x z
end ClosReflTransRemainder

-- Let's say that a relation on a type `α` is *diagonal* if it refines the
-- identity relation -- i.e., if `R x y` implies `x = y`.

def isDiagonal {α : Type} (R: α → α → Prop) := ∀ x y, R x y → x = y

-- Now consider the following lemma about diagonal relations:

theorem closure_of_diagonal_is_diagonal : ∀ α (R: α → α → Prop),
  isDiagonal R →
  isDiagonal (ClosReflTrans R) := by

  intro α R hDiag x y h
  induction h
  /- The two first cases go as you'd expect... -/
  case rt_step x' y' hr =>
    rw [hDiag x' y' hr]
  case rt_refl => rfl
  /- ...  but something interesting happens here: there are two
       induction hypotheses, `ih` and `ih'`! If you think about it, it
       is not that weird: we are in the case `rt_trans`, which has
       two recursive components, `hxy`, relating `x` to `y` and `hyz`,
       relating `y` to `z`. Hence we may want (and will actually need)
       an induction hypothesis for `hxy` and one for `hyz` -- they are
       called `ihxy` and `ihyz` here. In general, Lean will always
       generate one induction hypothesis per recursive constructor of
       the type being inducted over. -/
  case rt_trans x' y' z' hxy hyz ihxy ihyz =>
    rw [ihxy, ihyz]

-- ### Exercise (4 stars): ev'_ev (Advanced) ⭐⭐⭐⭐

-- In general, there may be multiple ways of defining a property inductively.
-- For example, here's a (slightly contrived) alternative definition for `Ev`:

inductive Ev' : Nat → Prop where
  | ev'_0 : Ev' 0
  | ev'_2 : Ev' 2
  | ev'_sum n m (Hn : Ev' n) (Hm : Ev' m) : Ev' (n + m)

-- Prove that this definition is logically equivalent to the old one. To
-- streamline the proof, use the technique (from the Logic chapter) of
-- applying theorems to arguments, and note that the same technique works with
-- constructors of inductively defined propositions.

theorem ev'_ev : ∀ n, Ev' n ↔ Ev n := by
  sorry

-- We can do similar inductive proofs on the `Perm3` relation, which we
-- defined earlier as follows:

namespace Perm3Reminder

inductive Perm3 {α : Type} : List α → List α → Prop where
  | perm3_swap12 (a b c : α) :
      Perm3 [a, b, c] [b, a, c]
  | perm3_swap23 (a b c : α) :
      Perm3 [a, b, c] [a, c, b]
  | perm3_trans (l₁ l₂ l₃ : List α) :
      Perm3 l₁ l₂ → Perm3 l₂ l₃ → Perm3 l₁ l₃

end Perm3Reminder

theorem Perm3_symm : ∀ (α : Type) (l₁ l₂ : List α),
  Perm3 l₁ l₂ → Perm3 l₂ l₁ := by

  intro α l₁ l₂ h; induction h
  case perm3_swap12 => constructor
  case perm3_swap23 => constructor
  case perm3_trans _ _ _ _ _ ih₁2 ih₂3 =>
    exact Perm3.perm3_trans _ _ _ ih₂3 ih₁2

-- ### Exercise (2 stars): Perm3_In ⭐⭐

-- If you find yourself dealing with deeply nested `cases` in this proof,
-- think back to `Logic` where you learned about the `obtain` tactic

theorem Perm3_In : ∀ (α : Type) (x : α) (l₁ l₂ : List α),
    Perm3 l₁ l₂ → x ∈ l₁ → x ∈ l₂ := by
  sorry
  /- HIDE: CH: The base cases are a bit stupid without [tauto] -/

-- ### Exercise (1 star): Perm3_NotIn ⭐

theorem Perm3_NotIn : ∀ (α : Type) (x : α) (l₁ l₂ : List α),
    Perm3 l₁ l₂ → ¬x ∈ l₁ → ¬x ∈ l₂ := by
  sorry

-- ### Exercise (2 stars): NotPerm3 ⭐⭐

-- Proving that something is NOT a permutation is quite tricky. Some of the
-- lemmas above, like `Perm3_In` can be useful for this.

example : ¬ Perm3 [1, 2, 3] [1, 2, 4] := by
  sorry

-- ## Exercising with Inductive Relations

-- Just as a single-argument proposition defines a *property*, a two-argument
-- proposition defines a *relation*.

-- A proposition parameterized by a number (such as `Ev`) can be thought of as
-- a *property* -- i.e., it defines a subset of `Nat`, namely those numbers
-- for which the proposition is provable. In the same way, a two-argument
-- proposition can be thought of as a *relation* -- i.e., it defines a set of
-- pairs for which the proposition is provable.

namespace Playground

-- Just like properties, relations can be defined inductively. One useful
-- example is the "less than or equal to" relation on numbers that we briefly
-- saw above.

inductive Le : Nat → Nat → Prop where
  | refl (n : Nat)                : Le n n
  | succ (n m : Nat) (H : Le n m) : Le n (m + 1)

-- (We've written the definition a bit differently this time, giving explicit
-- names to the arguments to the constructors and moving them to the left of
-- the colons.)

-- Proofs of facts about `≤` using the constructors `Nat.le.refl` and
-- `Nat.le.step` follow the same patterns as proofs about properties, like
-- `ev` above. We can `apply` the constructors to prove `≤` goals (e.g., to
-- show that `3≤3` or `3≤6`), and we can use tactics like `inversion` to
-- extract information from `≤` hypotheses in the context (e.g., to prove that
-- `(2 ≤ 1) → 2+2=5`.)

-- Here are some sanity checks on the definition. (Notice that, although these
-- are the same kind of simple "unit tests" as we gave for the testing
-- functions we wrote in the first few lectures, we must construct their
-- proofs explicitly -- `rw`, `dsimp` and `rfl` don't do the job, because the
-- proofs aren't just a matter of simplifying computations.)

-- Some sanity checks...

theorem test_le1 : 3 ≤ 3 := by
  all_goals
    apply Nat.le.refl

theorem test_le2 : 3 ≤ 6 := by
  all_goals
    apply Nat.le.step; apply Nat.le.step; apply Nat.le.step; apply Nat.le.refl

theorem test_le3 : (2 ≤ 1) → 2 + 2 = 5 := by
  all_goals
    intros h
    inversion h
    case step h' => inversion h'

-- The "strictly less than" relation `n < m` can now be defined in terms of
-- `Nat.le`.

def lt (n m : Nat) : Prop := Nat.le (n + 1) m

-- The `≥` operation is defined in terms of `≤`. Lean provides a theorem
-- `ge_iff_le` allowing us to rewrite between them.

def ge (m n : Nat) : Prop := Nat.le n m

example : ∀ (m n : Nat), m ≥ n → n ≤ m := by
  intro m n h
  rw [←ge_iff_le]; assumption

end Playground

-- From the definition of `le`, we can sketch the behaviors of `cases` and
-- `induction` on a hypothesis `h` providing evidence of the form `le e1 e2`.
-- Doing `cases h` will generate two cases. In the first case, `e1 = e2`, and
-- it will replace instances of `e2` with `e1` in the goal and context. In the
-- second case, `e2 = n' + 1` for some `n'` for which `le e1 n'` holds, and it
-- will replace instances of `e2` with `n' + 1`. Doing `inversion H` will
-- remove impossible cases and add generated equalities to the context for
-- further use. Doing `induction h` will, in the second case, add the
-- induction hypothesis that the goal holds when `e2` is replaced with `n'`.

-- Here are a number of facts about the `≤` and `<` relations that we are
-- going to need later in the course. The proofs make good practice exercises.

-- ### Exercise (3 stars): le_facts ⭐⭐⭐

theorem le_trans : ∀ (m n o : Nat), m ≤ n → n ≤ o → m ≤ o := by
  sorry

theorem zero_le_n : ∀ n, 0 ≤ n := by
  sorry

theorem n_le_m__succ_n_le_succ_m : ∀ n m,
  n ≤ m → n + 1 ≤ m + 1 := by
  sorry

theorem succ_n_le_succ_m__n_le_m : ∀ n m,
  n + 1 ≤ m + 1 → n ≤ m := by
  sorry

theorem le_add_l : ∀ (a b : Nat), a ≤ a + b := by
  sorry

-- ### Exercise (2 stars): plus_le_facts1 ⭐⭐

theorem add_le : ∀ (n₁ n₂ m : Nat),
    n₁ + n₂ ≤ m →
    n₁ ≤ m ∧ n₂ ≤ m := by
   -- ADMITTED
    intros n₁ n₂ m h
    induction h
    case refl =>
      constructor
      . apply le_add_l
      . rw [Nat.add_comm]; apply le_add_l
    case step m' h' ih =>
      obtain ⟨h₁, h₂⟩ := ih
      constructor
      . apply le_trans (n := n₁ + n₂)
        . apply le_add_l
        . apply Nat.le.step; assumption
      . apply le_trans (n := n₁ + n₂)
        . rw [Nat.add_comm]; apply le_add_l
        . apply Nat.le.step; assumption

theorem add_le_cases : ∀ (n m p q : Nat),
  n + m ≤ p + q → n ≤ p ∨ m ≤ q := by
  /- Hint: May be easiest to prove by induction on `n`. -/
  sorry

-- ### Exercise (2 stars): plus_le_facts2 ⭐⭐

theorem add_le_compat_l : ∀ (n m p : Nat),
  n ≤ m →
  p + n ≤ p + m := by
  sorry

theorem plus_le_compat_r : ∀ (n m p : Nat),
  n ≤ m →
  n + p ≤ m + p := by
  sorry

theorem le_plus_trans : ∀ (n m p : Nat),
  n ≤ m →
  n ≤ m + p := by
  sorry

-- ### Exercise (3 stars): lt_facts ⭐⭐⭐

theorem lt_ge_cases : ∀ (n m : Nat),
  n < m ∨ n ≥ m := by
  sorry

theorem n_lt_m__n_le_m : ∀ (n m : Nat),
  n < m →
  n ≤ m := by
  sorry

theorem plus_lt : ∀ (n₁ n₂ m : Nat),
  n₁ + n₂ < m →
  n₁ < m ∧ n₂ < m := by
  sorry

-- ### Exercise (4 stars): ble_le ⭐⭐⭐⭐

theorem ble_complete : ∀ (n m : Nat),
  n ≤? m = true → n ≤ m := by
  sorry

theorem ble_correct : ∀ n m,
  n ≤ m →
  n ≤? m = true := by
  sorry

-- Hint: The next two can easily be proved without using `induction`.

theorem ble_iff : ∀ n m,
  n ≤? m = true ↔ n ≤ m := by
  sorry

theorem ble_true_trans : ∀ n m o,
  n ≤? m = true → m ≤? o = true → n ≤? o = true := by
  sorry
-- /HIDE

namespace R

-- ### Exercise (3 stars): R_provability (manually graded) ⭐⭐⭐

-- We can define three-place relations, four-place relations, etc., in just
-- the same way as binary relations. For example, consider the following
-- three-place relation on numbers:

inductive R : Nat → Nat → Nat → Prop where
  | c1                                       : R 0     0     0
  | c2 m n o (h : R m     n     o        )   : R (m + 1) n     (o + 1)
  | c3 m n o (h : R m     n     o        )   : R m     (n + 1) (o + 1)
  | c4 m n o (h : R (m + 1) (n + 1) (o + 2)) : R m     n     o
  | c5 m n o (h : R m     n     o        )   : R n     m     o

-- - Which of the following propositions are provable?

-- - `R 1 1 2`

-- - `R 2 2 6`

-- - If we dropped constructor `c5` from the definition of `R`, would the set of
--   provable propositions change? Briefly (1 sentence) explain your answer.

-- - If we dropped constructor `c4` from the definition of `R`, would the set of
--   provable propositions change? Briefly (1 sentence) explain your answer.

-- ### Exercise (3 stars): R_fact ⭐⭐⭐

-- The relation `R` above actually encodes a familiar function. Figure out
-- which function; then state and prove this equivalence in Lean.

-- Note to developers (Daniel Sainati @dsainati1, NOW):
--     They really need to use (+) here, not Nat.add, or there's some
--     typeclass nonsense in the proofs

def fR : Nat → Nat → Nat
  := sorry

theorem R_equiv_fR : ∀ m n o, R m n o ↔ fR m n = o := by
  sorry
  /- HIDE: And here's a somewhat nicer version using some automation,
     but we haven't covered that yet...

  From Stdlib Require Import Lia.

  theorem R_plus: forall m n o, R m n o↔  m + n = o.
  Proof.
    intros m n o; split; intros.
    - induction H; try reflexivity; try lia.
    - generalize dependent n. generalize dependent m.
      induction o as [|o']; intros m n H.
      + destruct m; try inversion H.
        destruct n; try inversion H0.
        apply c1.
      + destruct m as [|m'].
        * destruct n; try inversion H. apply c3.
          apply IHo'. reflexivity.
        * apply c2. apply IHo'. lia.
  Qed.
  -/

end R

-- ### Exercise (4 stars): subsequence (Advanced) ⭐⭐⭐⭐

-- A list is a *subsequence* of another list if all of the elements in the
-- first list occur in the same order in the second list, possibly with some
-- extra elements in between. For example,

--   [1,2,3]

-- is a subsequence of each of the lists

--   [1,2,3]
--   [1,1,1,2,2,3]
--   [1,2,7,3]
--   [5,6,1,9,9,2,7,3,8]

-- but it is *not* a subsequence of any of the lists

--   [1,2]
--   [1,3]
--   [5,6,2,1,7,3,8].

-- - Define an inductive proposition `subseq` on `List Nat` that captures what
--   it means to be a subsequence. There are a number of correct ways to do
--   this. You should make sure that your definition behaves correctly on all
--   the positive and negative examples above, but you do not need to prove this
--   formally.

-- - Prove `subseq_refl` that subsequence is reflexive, that is, any list is a
--   subsequence of itself.

-- - Prove `subseq_app` that for any lists `l₁`, `l₂`, and `l₃`, if `l₁` is a
--   subsequence of `l₂`, then `l₁` is also a subsequence of `l₂ ++ l₃`.

-- - (Harder) Prove `subseq_trans` that subsequence is transitive -- that is, if
--   `l₁` is a subsequence of `l₂` and `l₂` is a subsequence of `l₃`, then `l₁`
--   is a subsequence of `l₃`.

inductive subseq : List Nat → List Nat → Prop where
-- FILL IN HERE

theorem subseq_refl : ∀ (l : List Nat), subseq l l := by
  sorry

theorem subseq_app : ∀ (l₁ l₂ l₃ : List Nat),
  subseq l₁ l₂ →
  subseq l₁ (l₂ ++ l₃) := by
  sorry

theorem subseq_trans : ∀ (l₁ l₂ l₃ : List Nat),
  subseq l₁ l₂ →
  subseq l₂ l₃ →
  subseq l₁ l₃ := by
  /- Hint: be careful about what you are doing induction on and which
     other things need to be generalized... -/
  sorry

-- ### Exercise (2 stars): R_provability2 (manually graded) ⭐⭐

-- Suppose we give Lean the following definition:

--   inductive R : Nat → List Nat → Prop where
--     | c1                    : R 0     []
--     | c2 n l (H: R n     l) : R (n + 1) (n :: l)
--     | c3 n l (H: R (n + 1) l) : R n     l

-- Which of the following propositions are provable?

-- - `R 2 [1,0]`
-- - `R 1 [1,2,1,0]`
-- - `R 6 [3,2,1,0]`

-- ### Exercise (2 stars): total_relation ⭐⭐

-- Define an inductive binary relation `total_relation` that holds between
-- every pair of natural numbers.

inductive TotalRelation : Nat → Nat → Prop where
  -- FILL IN HERE

theorem total_relation_is_total : ∀ n m, TotalRelation n m := by
  sorry

-- ### Exercise (2 stars): empty_relation ⭐⭐

-- Define an inductive binary relation `empty_relation` (on numbers) that
-- never holds.

inductive EmptyRelation : Nat → Nat → Prop where
  -- FILL IN HERE

-- Note to developers (NOW):
--     @dsainati1 replace with inversion once
--     https://github.com/plclub/sf-in-lean/issues/52 is fixed

theorem empty_relation_is_empty : ∀ n m, ¬ EmptyRelation n m := by
  sorry

-- ## Additional Exercises

-- ### Exercise (3 stars): nostutter_defn ⭐⭐⭐

-- Formulating inductive definitions of properties is an important skill
-- you'll need in this course. Try to solve this exercise without any help.

-- We say that a list "stutters" if it repeats the same element consecutively.
-- (This is different from not containing duplicates: the sequence `[1, 4, 1]`
-- has two occurrences of the element `1` but does not stutter.) The property
-- "`nostutter mylist`" means that `mylist` does not stutter. Formulate an
-- inductive definition for `nostutter`.

inductive NoStutter {α:Type} : List α → Prop where
 -- FILL IN HERE

-- Make sure each of these tests succeeds, but feel free to change the
-- suggested proof (in comments) if the given one doesn't work for you. Your
-- definition might be different from ours and still be correct, in which case
-- the examples might need a different proof. (You'll notice that the
-- suggested proofs use a number of tactics we haven't talked about, to make
-- them more robust to different possible ways of defining `nostutter`. You
-- can probably just uncomment and use them as-is, but you can also prove each
-- example with more basic tactics.)

example : NoStutter [3, 1, 4, 1, 5, 6] := by
  sorry
  /- Suggested proof — uncomment and adapt:
    constructor; intro contra; contradiction
    constructor; intro contra; contradiction
    constructor; intro contra; contradiction
    constructor; intro contra; contradiction
    constructor; intro contra; contradiction
    constructor
  -/

example : NoStutter (@List.nil Nat) := by
  sorry
  /- Suggested proof — uncomment and adapt:
    constructor
  -/

example :  NoStutter [5] := by
  sorry
  /- Suggested proof — uncomment and adapt:
    constructor
  -/

example : ¬ (NoStutter [3, 1, 1, 4]) := by
  sorry
  /- Suggested proof — uncomment and adapt:
    intro contra; inversion contra with
    | nostutter2 _ contra =>
      inversion contra with
      | nostutter2 _ h _ =>
        apply h
        rfl
  -/

-- ### Exercise (4 stars): filter_challenge (Advanced) ⭐⭐⭐⭐

-- Let's prove that our definition of `filter` from the `Poly` chapter matches
-- an abstract specification. Here is the specification, written out
-- informally in English:

-- A list `l` is an "in-order merge" of `l₁` and `l₂` if it contains all the
-- same elements as `l₁` and `l₂`, in the same order as `l₁` and `l₂`, but
-- possibly interleaved. For example,

--   [1, 4, 6, 2, 3]

-- is an in-order merge of

--   [1, 6, 2]

-- and

--   [4, 3].

-- Now, suppose we have a type `α`, a function `test : α → Bool`, and a list
-- `l` of type `List α`. Suppose further that `l` is an in-order merge of two
-- lists, `l₁` and `l₂`, such that every item in `l₁` satisfies `test` and no
-- item in `l₂` satisfies test. Then `filter test l = l₁`.

-- First define what it means for one list to be a merge of two others. Do
-- this with an `inductive` relation, not a `def`.

inductive Merge {α:Type} : List α → List α → List α → Prop where
-- FILL IN HERE

theorem merge_filter : ∀ (α : Type) (test: α→ Bool) (l l₁ l₂ : List α),
  Merge l₁ l₂ l →
  List.all l₁ (fun n => test n) →
  List.all l₂ (fun n => !test n) →
  List.filter test l = l₁ := by
  sorry

-- ### Exercise (5 stars): filter_challenge_2 (Advanced) ⭐⭐⭐⭐⭐

-- A different way to characterize the behavior of `filter` goes like this:
-- Among all subsequences of `l` with the property that `test` evaluates to
-- `true` on all their members, `filter test l` is the longest. Formalize this
-- claim and prove it.

-- FILL IN HERE

-- ### Exercise (4 stars): palindromes ⭐⭐⭐⭐

-- A palindrome is a sequence that reads the same backwards as forwards.

-- - Define an inductive proposition `Pal` on `List α` that captures what it
--   means to be a palindrome. (Hint: You'll need three cases.)

-- - Prove `pal_app_reverse`, which states that

--   ∀ l, Pal (l ++ l.reverse).

-- - Prove `pal_reverse`, which states that

--   ∀ l, Pal l → l = l.reverse.

-- For extra credit, try proving the same theorems with an alternate
-- definition with a *single* constructor of this type:

--   ∀ l, l = l.reverse → Pal l

inductive Pal {α:Type} : List α → Prop where
-- FILL IN HERE

theorem pal_app_reverse : ∀ (α:Type) (l : List α),
  Pal (l ++ l.reverse) := by
  sorry

theorem pal_reverse : ∀ (α:Type) (l: List α) , Pal l → l = l.reverse := by

  sorry

-- Note to developers (Daniel Sainati @dsainati1, NOW):
--     This one is super annoying without simp. I propose we move it to the
--     simp chapter

-- ### Exercise (5 stars): palindrome_converse ⭐⭐⭐⭐⭐

-- Again, the converse direction is significantly more difficult, due to the
-- lack of evidence. Using your definition of `Pal` from the previous
-- exercise, prove that

--   ∀ l, l = l.reverse → Pal l.

-- FILL IN HERE

-- ### Exercise (4 stars): NoDup (Advanced) ⭐⭐⭐⭐

-- Use the `∈` property to define a proposition `disjoint l₁ l₂`, which should
-- be provable exactly when `l₁` and `l₂` are lists (with elements of type
-- `α`) that have no elements in common.

-- FILL IN HERE

-- Next, use `∈` to define an inductive proposition `NoDup l`, which should be
-- provable exactly when `l` is a list (with elements of type `α`) where every
-- member is different from every other. For example,
-- `NoDup ([1, 2, 3, 4] : List Nat)` and `NoDup ([] : List Bool)` should be
-- provable, while `NoDup ([1, 2, 1] : List Nat)` and
-- `NoDup ([true, true] : List Bool)` should not be.

-- FILL IN HERE

-- Finally, state and prove one or more interesting theorems relating
-- `disjoint`, `NoDup` and `++` (list append).

-- FILL IN HERE

-- ### Exercise (5 stars): pigeonhole_principle (Advanced) ⭐⭐⭐⭐⭐

-- The *pigeonhole principle* states a basic fact about counting: if we
-- distribute more than `n` items into `n` pigeonholes, some pigeonhole must
-- contain at least two items. As often happens, this apparently trivial fact
-- about numbers requires non-trivial machinery to prove, but we now have
-- enough...

-- First prove an easy and useful lemma.

theorem mem_split : ∀ (α:Type) (x:α) (l:List α),
  x ∈ l →
  ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  sorry

-- Now define a property `repeats` such that `repeats α l` asserts that `l`
-- contains at least one repeated element (of type `α`).

inductive Repeats {α:Type} : List α → Prop where
  -- FILL IN HERE

-- Now, here's a way to formalize the pigeonhole principle. Suppose list `l₂`
-- represents a list of pigeonhole labels, and list `l₁` represents the labels
-- assigned to a list of items. If there are more items than labels, at least
-- two items must have the same label -- i.e., list `l₁` must contain repeats.

-- This proof is much easier if you use the excluded middle to show that `∈`
-- is decidable, i.e., `∀ x l, (x ∈ l) \/ ~ (x ∈ l)`. Remember the `by_cases`
-- tactic from Logic!

theorem pigeonhole_principle:
  ∀ (α:Type) (l₁  l₂:List α),
  (∀ x, x ∈ l₁ → x ∈ l₂) →
  l₂.length < l₁.length →
  Repeats l₁ := by
  sorry
    /-.
        destruct (EM (In x l1')) as [H | H].
        + /- In x l1' -/
          apply rep_here. apply H.
        + /- ~ In x l1' -/
          apply rep_later.
          assert (INX: In x l₂).
          {  apply INC. left. reflexivity. }
          destruct (in_split _ _ _ INX) as [l2a [l2b EQ]].
          remember (l2a ++ l2b) as l2' eqn:Heql2'.
          assert (IN2: forall x0 : α, In x0 l1' → In x0 l2').
          { intros x0 AI.
            assert (H0: x <> x0).
            { intros Heq. apply H. rewrite  Heq. apply AI. }
            assert (h₁: In x0 l₂).
            { apply INC. simpl. right. apply AI. }
            rewrite EQ in h₁. apply In_app_iff in h₁.
            rewrite Heql2'. apply In_app_iff.
            simpl in h₁. destruct h₁ as [h₁ | [h₁ | h₁]].
            - left. apply h₁.
            - exfalso. apply H0. apply h₁.
            - right. apply h₁.  }
          assert (LEN2: length l2' < length l1').
          { assert (LS: length l₂ = S(length (l2a ++ l2b))).
            { rewrite EQ.
              rewrite app_length. rewrite app_length. rewrite add_comm.
              simpl. rewrite add_comm. reflexivity. }
            rewrite LS in NR. rewrite <- Heql2' in NR. simpl in NR.
            apply Sn_le_Sm__n_le_m.  apply NR.
          }
          apply (IHl1' l2' IN2 LEN2).
  Qed. -/


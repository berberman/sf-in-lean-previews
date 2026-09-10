import LF.Poly
import LF.CustomTactics

import SFLCompat

--  # Tactics: More Basic Tactics

--  This chapter introduces several additional proof strategies and tactics
--  that will allow us to begin proving more interesting properties of
--  functional programs.
--
--  We will see:
--  - how to reason about data constructors -- in particular, how to use
--    the fact that they are injective and disjoint;
--  - more on how to reason by case analysis;
--  - how to use auxiliary lemmas in both "forward-" and "backward-style"
--    proofs; and
--  - how to strengthen an induction hypothesis, and when such
--    strengthening is required.

--  ## Tactics `injection` and `contradiction`

--  Recall the definition of natural numbers:

sf_recall
  inductive Nat : Type where
    | zero
    | succ (n : Nat)

--  By this definition, every number has exactly one of two forms: either
--  it is the constructor `0` or it is built by applying the constructor
--  `.succ` to another number. There are two important consequences of this
--  definition:
--  - The constructor `.succ` is *injective* (or *one-to-one*). That is, if
--    `n + 1 = m + 1`, it must also be that `n = m`.
--  - The constructors `0` and `.succ` are *disjoint*. That is, `0` is not
--    equal to `n + 1` for any `n`.
--
--  Similar principles apply to every inductively defined type: all
--  constructors are injective, and the values built from distinct
--  constructors are never equal. For lists, the `List.cons` constructor is
--  injective and the empty list `List.nil` is different from every
--  non-empty list. For booleans, `true` and `false` are different. (Since
--  `true` and `false` take no arguments, their injectivity is neither here
--  nor there.) And so on.

--  ### Injectivity

--  We can *prove* the injectivity of `Nat.succ` by using the `Nat.pred`
--  function:

example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  have : n = Nat.pred (n + 1) := by rfl
  /- The hypothesis name defaults to `this` when unspecified. -/
  rewrite [this, h]
  rw [Nat.pred_succ]

--  This technique for proving injectivity can be generalized to any
--  constructor by writing the equivalent of `Nat.pred` — i.e., writing a
--  function that "undoes" one application of the constructor.
--
--  As a more convenient alternative, Lean provides a tactic called
--  `injection` that allows us to directly exploit the injectivity of any
--  constructor. Here is an alternate proof of the above theorem using
--  `injection`:

example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  injection h

--  Writing `injection h` directs Lean to generate all equations that
--  follow from `h` using the injectivity of constructors, adding them to
--  the context. In the present example, Lean can infer that `n = m` from
--  `n + 1 = m + 1`.
--
--  When a generated equation matches the goal, as is the case here,
--  `injection` automatically closes the goal.
--
--  When the generated equations do *not* immediately close the goal, the
--  equations are added to the context instead; adding `with` allows us to
--  explicitly name the equations (otherwise Lean generates names for us).

example (n m o : Nat)
    (h : [n, m] = [o, o]) :
    n = m := by
  injection h with h₁ h₂
  injection h₂ with h₃
  rw [h₁, h₃]

--  There is also a related tactic, `injections`, that applies the
--  `injection` tactic to all hypotheses, repeatedly. Using it simplifies
--  the proof of the above example.

example (n m o : Nat)
    (h : [n, m] = [o, o]) :
    n = m := by
  injections h₁ _ h₃
  rw [h₁, h₃]

--  ### Exercise (3 stars): injection_ex3 ⭐⭐⭐

theorem injection_ex3 {α : Type} (x y z : α) (l j : List α)
    (h₁ : x :: y :: l = z :: j)
    (h₂ : j = z :: l) :
    x = y := by
  sorry

--  (End of exercise)

--  So much for injectivity of constructors. What about disjointness?
--
--  The principle of disjointness says that two terms beginning with
--  different constructors (like `0` and `Nat.succ`, or `true` and `false`)
--  can never be equal. Therefore, any time we find ourselves in a context
--  where we've *assumed* that two such terms are equal, we are justified
--  in concluding anything we want, since the assumption is nonsensical.
--
--  The `contradiction` tactic embodies this principle. If the context
--  contains a contradictory hypothesis, such as `false = true`,
--  `contradiction` solves the current goal immediately. Some examples:

example (n m : Nat)
    (h : false = true) :
    n = m := by
  contradiction

example (n : Nat)
    (h : n + 1 = 0) :
    2 + 2 = 5 := by
  contradiction

--  These examples are instances of a logical principle known as the
--  *principle of explosion*, which asserts that a contradictory hypothesis
--  entails anything — even manifestly false things!
--
--  In the above example, `n + 1` is shorthand for a constructor
--  application `Nat.succ n` so contradiction applies to it directly.
--
--  Sometimes you need to do a little work to expose a contradictory
--  hypothesis involving constructors.
--
--  For example, recall that `Nat.add` recurses on its second argument, so
--  deriving a contradiction from `1 + n = 0` is not direct.

sf_expect_failure_in
  example (n : Nat)
      (h : 1 + n = 0) :
      2 + 2 = 5 := by
    contradiction -- doesn't work because `1 + n` doesn't reduce to `n.succ`.

--  To fix it, rewriting with `Nat.one_add` changes the hypothesis from
--  `1 + n = 0` to `n.succ = 0`. Then Lean can immediately recognize this
--  as impossible.

example (n : Nat)
    (h : 1 + n = 0) :
    2 + 2 = 5 := by
  rw [Nat.one_add] at h
  contradiction

--  If you find the principle of explosion confusing, remember that these
--  proofs are *not* simply showing that the conclusion of the statement
--  holds. Rather, they are showing that, *if* the nonsensical situation
--  described by the premise did somehow hold, *then* the nonsensical
--  conclusion would hold too (because we'd be living in an inconsistent
--  universe where every statement is true).
--
--  We'll explore the principle of explosion in more detail in the next
--  chapter.

--  ### Exercise (1 star): disjoint_ex3 ⭐

theorem disjoint_ex3 {α : Type} (x y z : α) (l : List α)
    (h : x :: y :: l = []) :
    x = z := by
  sorry

--  ### Quizzes

--  Recall our `RGB` and `Color` types:

sf_recall
  inductive RGB : Type where
    | red
    | green
    | blue

sf_recall
  inductive Color : Type where
    | black
    | white
    | primary (p: RGB)

--   ----------------------------------------

--  _Quiz:_

--  Suppose Lean's proof state looks like
--
--      x : RGB
--      y : RGB
--      h : .primary x = .primary y
--      ------------------------------
--      ⊢ y = x
--
--  and we apply the tactic `injection h with hxy`. What will happen?
--
--  (1) "No goals."
--
--  (2) The tactic fails.
--
--  (3) Lean adds a hypothesis `hxy : x = y`, while the goal remains
--  `y = x`.
--
--  (4) None of the above.

--   ----------------------------------------

--  _Quiz:_

--  Suppose Lean's proof state looks like
--
--      x : Bool
--      y : Bool
--      h : !x = !y
--      --------------
--      ⊢ y = x
--
--  and we apply the tactic `injection h with hxy`. What will happen?
--
--  (A) "No more goals."
--
--  (B) The tactic fails.
--
--  (C) Hypothesis `h` becomes `hxy : x = y`.
--
--  (D) None of the above.

--   ----------------------------------------

--  _Quiz:_

--  Now suppose Lean's proof state looks like
--
--      x : Nat
--      y : Nat
--      h : x + 1 = y + 1
--      -------------------
--      ⊢ y = x
--
--  and we apply the tactic `injection h with hxy`. What will happen?
--
--  (A) "No more goals."
--
--  (B) The tactic fails.
--
--  (C) Hypothesis `h` becomes `hxy : x = y`.
--
--  (D) None of the above.

--   ----------------------------------------

--  _Quiz:_

--  Finally, suppose Lean's proof state looks like
--
--      x : Nat
--      y : Nat
--      h : 1 + x = 1 + y
--      -------------------
--      ⊢ y = x
--
--  and we apply the tactic `injection h with hxy`. What will happen?
--
--  (A) "No more goals."
--
--  (B) The tactic fails.
--
--  (C) Hypothesis `h` becomes `hxy : x = y`.
--
--  (D) None of the above.

--   ----------------------------------------

--  ### Tactic `congr`

--  The injectivity of constructors allows us to reason that
--  `∀ (n m : Nat), n + 1 = m + 1 → n = m`. The converse of this
--  implication also holds:

example (n m : Nat) (h : n = m) :
    n + 1 = m + 1 := by
  rw [h]

--  This is an instance of a more general fact about both constructors and
--  functions:

example {α β : Type} (f : α → β) (x y : α)
    (h : x = y) : f x = f y := by
  rw [h]

--  There is a tactic named `congr` that can prove such goals directly.
--  Given a goal of the form `f a₁ ... aₙ = g b₁ ... bₙ`, writing `congr`
--  will produce subgoals of the form `f = g`, `a₁ = b₁`, ..., `aₙ = bₙ`.
--  If any of these subgoals that are simple enough to be discharged
--  automatically (e.g., immediately provable by `rfl`), they will
--  disappear.

example (n m : Nat) (h : n = m) :
    n + 1 = m + 1 := by
  congr

--  The `congr` tactic accepts an optional numerical argument, which tells
--  Lean how deeply to decompose the goal. So, given a goal like
--  `((a, b), (c, d)) = ((e, f), (g, h))`, `congr 1` only applies `congr`
--  just once to the goal to produce two subgoals: `(a, b) = (e, f)` and
--  `(c, d) = (g, h)`, while `congr 2` would apply `congr` again to both
--  these subgoals and produce four subgoals: `a = e`, `b = f`, `c = g` and
--  `d = h`. Using `congr` without an argument decomposes the goal as
--  deeply as possible.
--
--  Why might we want this level of control? Because, depending on what we
--  are trying to prove, deeper applications of `congr` may sometimes make
--  our goal unprovable. Consider:

sf_expect_failure_in
  example (a b c d : Nat) (hab : a = b) (hcd : c = d) :
      (a, c + 1) = (b, 1 + d) := by
    congr

--  We now have three goals: `c = 1`, `1 = d`, and `1 = d`, but these are
--  not provable from our hypotheses! `congr` has gone too deep.

--  Output:
--    unsolved goals
--    case e_snd.e_a
--    a b c d : Nat
--    hab : a = b
--    hcd : c = d
--    ⊢ c = 1
--
--    case e_snd.e_a.e_2
--    a b c d : Nat
--    hab : a = b
--    hcd : c = d
--    ⊢ 1 = d
--
--    case e_snd.e_a.e_3
--    a b c d : Nat
--    hab : a = b
--    hcd : c = d
--    ⊢ 1 = d

example (a b c d : Nat) (hab : a = b) (hcd : c = d) :
    (a, c + 1) = (b, 1 + d) := by
  /- Using `congr` shallowly allows us to complete the proof -/
  congr 1
  rw [Nat.add_comm]
  congr

--  ## Using `cases` on Expressions

--  We've seen many examples where the `cases` tactic is used to perform
--  case analysis of the value of some *variable*, such as one of type
--  `Bool` or `Nat`. Sometimes we need to reason by cases on the result of
--  some *expression*. We can do so with `cases`, directly. Here is an
--  example:

def chooseIf {α : Type} (test : α → Bool) (x y : α) : α :=
  if test x then x else y

theorem chooseIf_self {α : Type} (test : α → Bool) (x : α) :
    chooseIf test x x = x := by
  rw [chooseIf]
  cases test x <;> rfl

--  After unfolding `chooseIf` in the above proof, we find that we are
--  stuck on `(if test x = true then x else x) = x`. But either `test x` is
--  `true` or it isn't, so we can use `cases (test x)` to let us reason
--  about the two cases.
--
--  In general, the `cases` tactic can perform case analysis on the results
--  of arbitrary computations. If `e` has an inductively defined type `T`,
--  then `cases e` generates one subgoal for each constructor of `T`,
--  specializing the goal to that constructor. It does not necessarily
--  rewrite occurrences of `e` in hypotheses; when that information is
--  needed, we can save an equation as described below.

--  ### Destructing Tuples

--  The `cases` tactic is useful when we are dealing with values that can
--  be one of a list of things (a `Bool` is either a `false` or a `true`, a
--  `Nat` is either `0` or `succ n`, etc.). When we want more information
--  about a value that is a tuple of *multiple* things, we instead want a
--  way to extract the pieces of that value.
--
--  If we have a value `v : α × β` in our context, we can extract the first
--  and second components of `v` and give them names using this tactic:
--
--      let ⟨a, b⟩ := v

--  ### Exercise (3 stars): zip_unzip' ⭐⭐⭐

--  Here is an implementation of the `unzip` function from chapter Poly:

def unzip' {α β : Type} (l : List (α × β)) : List α × List β := sorry

--  Prove that `unzip'` and `zip` are inverses in the following sense.
--  Remember that you can use `dsimp only` to simplify expressions
--  involving pairs and `fst` and `snd`.

theorem zip_unzip' {α β : Type} (l : List (α × β))
    (l₁ : List α) (l₂ : List β)
    (h : unzip' l = (l₁, l₂)) :
    zip l₁ l₂ = l := by
  sorry

--  ### Splitting with Equations

--  When using `cases`, we can specify to Lean that it should remember an
--  equality between a compound expression and what we are decomposing it
--  into, using `cases h : ...` syntax. This step can actually be critical:
--  if we leave it out, we might lack information we need to complete a
--  proof.
--
--  For example, suppose we define a function `keepIf` like this:

def keepIf {α : Type} (test : α → Bool) (x : α) : Option α :=
  if test x then some x else none

--  Now suppose that we want to prove that, if `keepIf` returns a result of
--  the form `some y`, then `x = y`. If we start the proof like this (with
--  no `h : ⋯` on the `cases`)...

sf_expect_failure_in
  theorem keepIf_some {α : Type} (test : α → Bool) (x y : α)
      (h : keepIf test x = some y) :
      x = y := by
    rw [keepIf] at h
    cases (test x)

--  Output:
--    unsolved goals
--    case false
--    α : Type
--    test : α → Bool
--    x y : α
--    h : (if test x = true then some x else none) = some y
--    ⊢ x = y
--
--    case true
--    α : Type
--    test : α → Bool
--    x y : α
--    h : (if test x = true then some x else none) = some y
--    ⊢ x = y

--  ... then we are stuck because the context does not contain enough
--  information to prove the goal. Because `test x` appears in the
--  hypothesis rather than the goal, `cases (test x)` does not
--  automatically replace the expression with `false` or `true` like it did
--  during the proof of `chooseIf`. We want to add an equation to the
--  context that records which case we are in. This is precisely what the
--  `h : ⋯` qualifier does.

theorem keepIf_some {α : Type} (test : α → Bool) (x y : α)
    (h : keepIf test x = some y) :
    x = y := by
  rw [keepIf] at h
  cases hTest : test x
  -- Now we have the same state as at the point where we got stuck
  -- above, except that the context contains an extra equality
  -- assumption, which is exactly what we need to make progress.
  · rw [hTest] at h
    contradiction
  · rw [hTest] at h
    injections

--  ### Exercise (2 stars): bool_fn_iterate_three_eq_one ⭐⭐

theorem bool_fn_iterate_three_eq_one (f : Bool → Bool) (b : Bool) :
    f (f (f b)) = f b := by
  sorry

--  ## The `apply` Tactic

--  We often encounter situations where the goal to be proved is *exactly*
--  the same as some hypothesis in the context or some previously proved
--  lemma.
--
--  The `apply` tactic is useful when the goal is instead the conclusion of
--  an implication. If the conclusion of the implication matches the
--  current goal, its premises become new subgoals to be proved.
--
--  For example, suppose we have a hypothesis `h : p → q` and our goal is
--  `q`. We can use `apply h` to replace the goal `q` with the premise `p`:

example (p q : Prop) (h : p → q) (hp : p) : q := by
  apply h
  exact hp

--  Another example:

example (n m o p : Nat) (hnm : n = m) (h : n = m → [n, o] = [m, p]) :
    [n, o] = [m, p] := by
  apply h
  exact hnm

--  This process is called *backward reasoning*. We are trying to prove
--  some goal `⊢ b` and we know some fact `h : a → b`. So we work backwards
--  by applying that fact, which replaces the goal with `⊢ a`.
--
--  When we use `apply h`, Lean tries to match the conclusion of the type
--  of `h` with the current goal. Here `h : n = m → [n, o] = [m, p]` has
--  conclusion `[n, o] = [m, p]`, which matches the current goal. Lean
--  replaces the goal with the premise `n = m`. Then we close the goal with
--  `exact hnm`.
--
--  Even more generally, the type of a theorem or hypothesis used with
--  `apply` may also have universally quantified variables and premises.
--  Lean tries to match its conclusion with the current goal to determine
--  appropriate values for the quantified variables.

example (n m : Nat) (h₁ : (n, n) = (m, m))
    (h₂ : ∀ (q r : Nat), (q, q) = (r, r) → [q] = [r]) :
    [n] = [m] := by
  apply h₂
  exact h₁

--  ### Exercise (2 stars): apply_exercise (Optional) ⭐⭐

--  Complete the following proof using only `apply`.

theorem apply_exercise (m : Nat)
    (h₁ : ∀ (n : Nat), n.even = true → (n + 1).even = false)
    (h₂ : ∀ (n : Nat), n.even = false → n.odd = true)
    (hEven : m.even = true) :
    (m + 1).odd = true := by
  sorry

--  (End of exercise)

--  To use `apply`, the conclusion of the fact being applied must match the
--  goal. For example, `apply` will not work if the left and right sides of
--  the equality are swapped.

example (n m : Nat) (h : n = 0 → n = m) (hn : n = 0) : m = n := by
  /- Here we cannot use `apply` directly...
    ...but we can use the `symm` tactic, which switches the left
    and right sides of an equality in the goal. -/
  symm
  apply h
  exact hn

--  ### Exercise (2 stars): apply_exercise1 ⭐⭐

--  The `apply` tactic can be used with previously defined theorems, not
--  just hypotheses in the context. For this exercise, use a
--  previously-defined theorem about `rev` from chapter Poly as part of
--  your (fairly short) solution. You do not need `induction`.

theorem rev_exercise1 {α : Type} (l l' : List α) (h : l = l'.rev) :
    l' = l.rev := by
  sorry

--  ### Exercise (1 star): apply_rewrite (Optional, Manually graded) ⭐

--  Briefly explain the difference between the tactics `apply` and `rw`.
--  What are the situations where both can usefully be applied?

--  ### Supplying arguments to `apply`

--  The following silly example uses two rewrites in a row to get from
--  `[u, v]` to `[y, z]`.

example (u v w x y z : Nat)
    (h₁ : [u, v] = [w, x])
    (h₂ : [w, x] = [y, z]) :
    [u, v] = [y, z] := by
  rw [h₁, h₂]

--  Since this is a common pattern, we might like to pull it out as a lemma
--  that records, once and for all, the fact that equality is *transitive*.

theorem trans_eq {α : Type} (a b c : α) :
    a = b → b = c → a = c := by
  intro h₁ h₂
  rw [h₁, h₂]

--  Lean already provides exactly this theorem as `Eq.trans`:

#check Eq.trans

--  Output:
--    Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c

--  Notice that in Lean's version, the arguments `a`, `b`, and `c` are
--  implicit.
--
--  This is because they can usually be inferred from the equality
--  hypotheses and the goal.
--
--  Now let's use our `trans_eq` to prove the example above.
--
--  If we simply write `apply trans_eq`, Lean can infer some arguments from
--  the goal, but not the intermediate list or the hypotheses needed for
--  the lemma's premises.

sf_expect_failure_in
  example (u v w x y z : Nat)
      (h₁ : [u, v] = [w, x])
      (h₂ : [w, x] = [y, z]) :
      [u, v] = [y, z] := by
    apply trans_eq

--  Here is the proof state after `apply`:

--  Output:
--    unsolved goals
--    case a
--    u v w x y z : Nat
--    h₁ : [u, v] = [w, x]
--    h₂ : [w, x] = [y, z]
--    ⊢ [u, v] = ?b
--
--    case a
--    u v w x y z : Nat
--    h₁ : [u, v] = [w, x]
--    h₂ : [w, x] = [y, z]
--    ⊢ ?b = [y, z]
--
--    case b
--    u v w x y z : Nat
--    h₁ : [u, v] = [w, x]
--    h₂ : [w, x] = [y, z]
--    ⊢ List Nat

--  Notice that there are three goals:
--  1. `[u, v] = ?b`
--  2. `?b = [y, z]`
--  3. `List Nat`
--
--  Recall that `trans_eq` has five arguments. From the goal, Lean can
--  infer the endpoints `a` and `c`, namely `[u, v]` and `[y, z]`. But it
--  still needs the intermediate term `b`.
--
--  We want to prove `[u, v] = [y, z]`. By transitivity, it's enough to
--  prove `[u, v] = ?b` and `?b = [y, z]`, for some intermediate list `?b`.
--  Here `?b` is a *metavariable*: a placeholder for a value Lean has not
--  yet determined. Before we provide the hypothesis `h₂`, Lean doesn't
--  know that this intermediate list should be `[w, x]`.
--
--  One way to make progress is to supply the arguments and hypotheses
--  explicitly:

example (u v w x y z : Nat)
    (h₁ : [u, v] = [w, x])
    (h₂ : [w, x] = [y, z]) :
    [u, v] = [y, z] := by
  apply trans_eq [u, v] [w, x] [y, z] h₁ h₂

--  Here, we had to specify the `a` and `c` arguments to `trans_eq` before
--  we could supply `[w, x]` for `b` or `h₁` and `h₂` for the premises.
--  However, we just said that Lean was able to infer these arguments, so
--  it's a bit redundant (and wordy) for us to do it.
--
--  Thankfully, Lean allows us to use `_`s for positional arguments that it
--  can infer.

example (u v w x y z : Nat)
    (h₁ : [u, v] = [w, x])
    (h₂ : [w, x] = [y, z]) :
    [u, v] = [y, z] := by
  apply trans_eq _ _ _ h₁ h₂

--  Alternatively, if we know the name of the argument we are supplying (in
--  this case `b`), we can name it directly and avoid typing any `_`s. Such
--  *named arguments* can be used in function applications generally, not
--  just with `apply`.

example (u v w x y z : Nat)
    (h₁ : [u, v] = [w, x])
    (h₂ : [w, x] = [y, z]) :
    [u, v] = [y, z] := by
  apply trans_eq (b := [w, x])
  apply h₁
  apply h₂

--  When fully applying another theorem or hypothesis to conclude a proof,
--  it is good practice to use the `exact` tactic instead of `apply`. Doing
--  so signals to a reader that the proof is solved *exactly* by this fact,
--  and nothing more.

example (u v w x y z : Nat)
    (h₁ : [u, v] = [w, x])
    (h₂ : [w, x] = [y, z]) :
    [u, v] = [y, z] := by
  exact trans_eq _ _ _ h₁ h₂

--  A final alternative for this situation is the `calc` tactic we saw in
--  the UsingLean chapter. It works by chaining equalities together using
--  transitivity, serving the same purpose here as applying `trans_eq`.

example (u v w x y z : Nat)
    (h₁ : [u, v] = [w, x])
    (h₂ : [w, x] = [y, z]) :
    [u, v] = [y, z] := by
  calc
  [u, v] = [w, x] := by rw [h₁]
  _ = [y, z] := by rw [h₂]

--  ### Exercise (3 stars): trans_eq_exercise (Optional) ⭐⭐⭐

theorem trans_eq_exercise (n m o p : Nat)
    (h₁ : m = o.minusTwo)
    (h₂ : (n + p) = m) :
    (n + p) = o.minusTwo := by
  sorry

--  ### Forward Reasoning with `apply`

--  We can also use the `apply` tactic to rewrite *hypotheses*.
--
--  The tactic `apply t at h` matches an implication `t` (say, of the form
--  `a → b`) against a hypothesis `h` in the local context. Unlike ordinary
--  `apply`, which matches the goal against `b` and replaces it with the
--  subgoal `a`, `apply t at h` matches the type of `h` against `a` and, if
--  successful, replaces `h` with a hypothesis of type `b`. In other words,
--  `apply t at h` is a form of "forward reasoning" from the hypotheses
--  toward the goal.
--
--  In other words, `apply t at h` gives us a form of "forward reasoning":
--  given `t : a → b` and `h : a`, it replaces `h` with a proof of `b`.
--
--  By contrast, ordinary `apply t` is "backward reasoning": given
--  `t : a → b` and a goal `⊢ b`, it replaces the goal with `⊢ a`.
--
--  Here is a proof that uses forward reasoning rather than backward
--  reasoning:

example (n m p q : Nat)
    (h : n = m → p = q)
    (hnm : n = m) :
    p = q := by
  apply h at hnm
  exact hnm

--  Forward reasoning begins with what is already known — premises and
--  previously proven theorems — and derives new facts from them until the
--  goal is reached. Backward reasoning begins with the goal and works
--  backward through implications that would prove it, until the remaining
--  goals are facts that are already known or assumed.
--
--  Informal proofs in mathematics and computer science often use forward
--  reasoning. In Lean, backward reasoning is generally more idiomatic,
--  though forward reasoning can sometimes be easier to follow or more
--  natural for particular proofs.
--
--  You may be interested to know that the `apply ... at ...` tactic is not
--  part of Lean's core set of tactics. Lean makes it very easy for users
--  to define new tactics that suit their particular proof style, and so
--  the developers of the
--  [Mathlib](https://github.com/leanprover-community/mathlib4) library
--  defined the `apply ... at ...` tactic to better support forward
--  reasoning. Mathlib is a very large development, so we do not import the
--  whole thing in this book, but we do import `apply ... at ...` because
--  it is particularly useful.

--  ## Specializing Hypotheses

--  We've already seen how we can use `have` to do forward reasoning, by
--  letting us state and prove useful facts that get us closer to the main
--  goal we're trying to prove. Often, though, these facts are just special
--  cases of more general hypotheses we already have. If `h` is a
--  quantified hypothesis in the current context — i.e.,
--  `h : ∀ (x : α), P x` — then we can use `have` to obtain a special case
--  of `h` by supplying a value for `x`. For example, `have h := h e`
--  introduces a new `h` which `x` has been instantiated with `e`.
--
--  For example:

example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  have h := h 1
  rw [Nat.mul_one] at h
  exact h

--  One thing to notice here is that the original `h` is still present in
--  the context, although it is shadowed by the new `h`. Often we don't
--  care to keep this old hypothesis around, in which case we can use the
--  `replace` tactic instead. This behaves like `have`, except that it gets
--  rid of the old hypothesis afterwards when possible:

example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  replace h := h 1
  rw [Nat.mul_one] at h
  exact h

--  Specializing a hypothesis in this way is common enough that Lean
--  provides a separate `specialize` tactic for it. For example,
--  `specialize h 1` is a more concise way of writing `replace h := h 1`:

example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  specialize h 1
  rw [Nat.mul_one] at h
  exact h

--  ### Exercise (3 stars): nth?_always_none ⭐⭐⭐

--  Use `have`, `replace`, or `specialize` to prove the following lemma,
--  following the model of the examples above. Do not use `induction`.

theorem nth?_always_none {l : List α} (h : ∀ i, nth? l i = none) :
    l = [] := by
  sorry

--  (End of exercise)

--  Tactics like `have` and `replace` can also be used with lemmas and
--  theorems we've already proven, not just things in the immediate proof
--  context. Using these tactics before `apply` gives us yet another way to
--  control where `apply` does its work.

example (u v w x y z : Nat)
    (h₁ : [u, v] = [w, x])
    (h₂ : [w, x] = [y, z]) :
    [u, v] = [y, z] := by
  have h := trans_eq (b := [w, x])
  apply h
  /- This tactic closes a goal if it appears anywhere in the context.
     In this case we could also write `exact h₁` ... -/
  assumption
  /- .. and here we could also write `exact h₂` -/
  assumption

--  ## Generalizing the Induction Hypothesis

--  Recall this function for doubling a natural number from the Induction
--  chapter:

sf_recall
  def Nat.double (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | n' + 1 => double n' + 2

--  Sometimes `induction` gives us an induction hypothesis that is too
--  specific to be useful. This can happen when another variable in the
--  theorem is fixed during the induction but the induction step needs to
--  use it at different values.
--
--  For example, suppose we want to show that `Nat.double` is injective —
--  i.e., that it maps different arguments to different results:

sf_experiment
  theorem double_injective (n m : Nat) (h : n.double = m.double) : n = m := sorry

--  The way we start this proof is a bit delicate: if we begin it like
--  this...

sf_expect_failure_in
  theorem double_injective (n m : Nat) (h : n.double = m.double) : n = m := by
    induction n with
    | zero =>
      cases m with
      | zero => rfl
      | succ m' =>
        rw [Nat.double_zero, Nat.double_succ] at h
        contradiction
    | succ n' ih =>
      cases m with
      | zero =>
        rw [Nat.double_zero, Nat.double_succ] at h
        contradiction
      | succ m' =>
        congr

--  Output:
--    unsolved goals
--    case succ.succ.e_a
--    n' m' : Nat
--    ih : n'.double = (m' + 1).double → n' = m' + 1
--    h : (n' + 1).double = (m' + 1).double
--    ⊢ n' = m'

--  ...we get stuck: `m` is fixed during whole the induction because it was
--  already in the context when we applied the `induction` tactic. In the
--  successor case, the induction hypothesis `ih` is specialized to the
--  current value of `m`. After the case split, that value is `m' + 1`, and
--  the induction hypothesis has the form:
--
--      ih : n'.double = (m' + 1).double → n' = m' + 1
--
--  From `h`, using the definition of `Nat.double` we can obtain

--  n'.double = m'.double

--  and to prove the goal we would like to apply an induction hypothesis at
--  `m'`. But `ih` is specialized to `m' + 1` — it requires

--  n'.double = (m' + 1).double

--  and would allow us to conclude

--  n' = m' + 1

--  which is not what we need.
--
--  What went wrong?
--
--  The problem is that `m` is already in the context when we invoke
--  `induction n`. Since `m` is an ordinary argument of the theorem, this
--  is exactly what we normally want — we are considering some particular
--  `n` and `m`, together with the hypothesis `n.double = m.double` and
--  trying to prove `n = m`.
--
--  The claim itself makes perfect sense, but keeping `m` fixed during
--  induction causes trouble: we are proving, for *all* `n`, the
--  proposition
--  - `P n` = "if `n.double = m.double`, then `n = m`"
--
--  by showing
--  - `P 0`
--
--    (i.e., "if `Nat.double 0 = m.double` then `0 = m`") and
--
--  - `P n → P (n + 1)`
--
--    (i.e., "if `n.double = m.double` then `n = m`" implies "if
--    `(n + 1).double = m.double` then `n + 1 = m`").
--
--  If we look closely at the inductive step, it is saying something rather
--  strange: that, for a *particular* `m`, if we know
--  - "if `n.double = m.double` then `n = m`"
--
--  then we can prove
--  - "if `(n + 1).double = m.double` then `n + 1 = m`".
--
--  To see why this is strange, let's choose a particular `m` — say, `5`.
--  The statement is then saying that, if we know
--  - `Q` = "if `n.double = 10` then `n = 5`"
--
--  then we can prove
--  - `R` = "if `(n + 1).double = 10` then `n + 1 = 5`".
--
--  But knowing `Q` doesn't give us any help at all with proving `R`. If we
--  tried to prove `R` from `Q`, we would start with something like
--  "Suppose `(n + 1).double = 10`..." but then we would be stuck: the
--  induction hypothesis `Q` only tells us what happens if `n.double = 10`,
--  whereas our assumption says `(n + 1).double = 10`, so `Q` is useless
--  here.
--
--  This is exactly what we saw in the proof state.
--
--  Trying to carry out this proof by induction on `n` with `m` fixed
--  doesn't work, because we are then trying to prove a statement involving
--  *every* `n` but just a *particular* `m`.
--
--  A successful proof of `double_injective` needs to *generalize* `m` when
--  carrying out the induction on `n`, so that the induction hypothesis
--  holds for every `m`, rather than for just the particular `m` in the
--  context. That is, we want an induction hypothesis like this:
--
--      ih : ∀ m, n'.double = m.double → n' = m
--
--  We can obtain this generalized induction hypothesis by writing
--
--      induction n generalizing m with

theorem double_injective (n m : Nat) (h : n.double = m.double) : n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m' => contradiction
  | succ n' ih =>
    cases m with
    | zero => contradiction
    | succ m' =>
      congr
      apply ih -- now works
      rw [Nat.double_succ, Nat.double_succ] at h
      injections

--  Let's look at an informal proof of this theorem. Notice that the
--  induction hypothesis is generalized over `m`, corresponding to the use
--  of `generalizing m`.
--
--  *Theorem*: For any natural numbers `n` and `m`, if
--  `n.double = m.double`, then `n = m`.
--
--  *Proof*: We prove by induction on `n` that, for *any* `m`, if
--  `n.double = m.double` then `n = m`.
--  - First, suppose `n = 0`. We must show that, for any `m`, if
--    `Nat.double 0 = m.double`, then `0 = m`.
--
--    There are two cases to consider for `m`:
--    1. If `m = 0`, we are done.
--    2. Otherwise if `m = m' + 1` for some `m'`, then by definition of
--       `Nat.double` we have `Nat.double 0 = 0` and
--       `(m' + 1).double = m'.double + 2`. Clearly `0` cannot equal
--       `m'.double + 2`, so this case is impossible.
--
--  - Second, suppose `n = n' + 1`. The induction hypothesis says that, for
--    every `m`, if `n'.double = m.double` then `n' = m`. Again there are
--    two cases to consider for `m`:
--    1. If `m = 0`, then by the definition of `Nat.double` our assumption
--       says `n'.double + 2 = 0`, which is impossible.
--    2. Otherwise suppose `m = m' + 1`. Our assumption is then that
--       `(n' + 1).double = (m' + 1).double`. By the definition of
--       `Nat.double`, this gives `n'.double + 2 = m'.double + 2`. By
--       injectivity of `Nat.succ`, we obtain `n'.double = m'.double`. We
--       can now instantiate the induction hypothesis with `m'`, obtaining
--       `n' = m'`. Now we can conclude `n' + 1 = m' + 1`, which is exactly
--       what we wanted to show.
--
--  *Qed*.
--
--  The thing to take away from all this is that you need to be careful,
--  when using induction, that your induction hypothesis is not too
--  specific. When proving a proposition quantified over variables `n` and
--  `m` by induction on `n`, it is sometimes crucial to *generalize* `m`,
--  so that the induction hypothesis applies to every `m` rather than just
--  the particular `m` in the context.

--  ### Exercise (3 stars): add_self_injective ⭐⭐⭐

--  The following theorem follows the same pattern as `double_injective`.

theorem add_self_injective (n m : Nat)
    (h : n + n = m + m) :
    n = m := by
  sorry

--  ### Exercise (2 stars): add_self_injective_informal (Manually graded) ⭐⭐

--  Give a careful informal proof of `add_self_injective`, stating the
--  induction hypothesis explicitly and being as explicit as possible about
--  quantifiers, everywhere.

--  ## Rewriting with Conditional Statements

--  Rewriting with a conditional theorem is similar in spirit to backward
--  reasoning with `apply`, introduced earlier in this chapter: both let a
--  theorem's premises become new subgoals. Here, though, it is `rw` doing
--  the work, using the theorem's conclusion to transform the goal rather
--  than closing it outright.
--
--  Suppose that we know two numbers have the same double, and we want to
--  use this fact to rewrite one of them into the other. Recall the theorem
--  `double_injective` from the previous section:

#check double_injective

--  Output:
--    double_injective (n m : Nat) (h : n.double = m.double) : n = m

--  For example, we can prove:

example (n m p q : Nat)
    (h : n.double = m.double)
    (hm : m + p = q) :
    n + p = q := by
  rw [double_injective n m]
  · assumption
  · assumption

--  The use of `rw` here is a little different from the examples we have
--  seen so far. The theorem `double_injective` says `n = m` *provided
--  that* `n.double = m.double`, not just `n = m`. When we write
--  `rw [double_injective n m]`, Lean uses the conclusion `n = m` to
--  rewrite the goal, and then asks us to prove the hypothesis needed by
--  `double_injective`. Thus we get two goals: the updated main goal,
--  `m + p = q`, and the condition from `double_injective`,
--  `n.double = m.double`. These goals follow by assumption from `hm` and
--  `h`, respectively.
--
--  If we rewrite with a conditional statement of the form `P → a = b`,
--  then Lean tries to rewrite with `a = b`, and then asks us to prove `P`
--  in a new subgoal. If the statement has more than one assumption, then
--  we get one subgoal for each assumption.

--  ## Review

--  We've now talked about many of Lean's most fundamental tactics. We'll
--  introduce a few more in the coming chapters, and later on we'll see
--  some more powerful *automation* tactics that make Lean help us with
--  low-level details. But basically we've got what we need to get work
--  done.
--
--  Here are the tactics we've seen so far.
--
--  Managing goals and hypotheses:
--  - `intro h`: move an assumption/quantified variable from the goal into
--    the local context
--  - `apply thm`: use a theorem, hypothesis, or constructor whose
--    conclusion matches the goal; its premises become new goals
--  - `apply thm at h`: use a theorem on a hypothesis in the context,
--    replacing `h` by the resulting fact (forward reasoning)
--  - `specialize h ...`: instantiate quantified variables in a hypothesis,
--    modifying `h` in place
--  - `replace h := ...`: replace a hypothesis with a newly proved fact
--  - `have h : P := ...`: prove a local fact `P` and add it to the context
--    with the name `h`
--  - `contradiction`: close the current goal when the context contains
--    contradictory assumptions
--
--  Equality, rewriting, and unfolding:
--  - `rfl`: close an equality that holds by reflexivity (possibly after
--    computation)
--  - `rw [h]`: rewrite the goal using an equality hypothesis or theorem
--  - `rw [d]`: unfold a definition in the goal
--  - `rw [h] at h'`: rewrite a hypothesis using an equality hypothesis or
--    theorem
--  - `rw [d] at h'`: unfold a definition in a hypothesis
--  - `symm`: reverse an equality goal, changing `t = u` to `u = t`
--  - `symm at h`: reverse an equality hypothesis
--  - `calc`: prove a goal about equality or another transitive relation by
--    giving a sequence of intermediate steps
--  - `congr`: use congruence to reduce an equality between expressions
--    with the same outer form; for example, a goal `f x = f y` may be
--    reduced to `x = y`
--  - `injection h with ...`: use injectivity of constructors to extract
--    equalities from equations between constructor applications
--  - `injections`: repeatedly use constructor injectivity on suitable
--    equalities in the context
--
--  Case analysis:
--  - `cases x`: reason separately about the possible constructors of an
--    inductively defined value
--  - `cases h : e`: perform case analysis on an expression `e` and add an
--    equation named `h` recording the result of the case analysis
--
--  Induction:
--  - `induction x`: prove the goal by induction on an inductively defined
--    value
--  - `induction x generalizing y`: induction on `x` while generalizing the
--    listed local variables, giving a more general induction hypothesis

--  ## Additional Exercises

--  ### Exercise (3 stars): nth?_after_last ⭐⭐⭐

--  Prove this by induction on `l`.

theorem nth?_after_last {α : Type}
    {n : Nat} {l : List α} (h : l.length = n) :
    nth? l n = none := by
  sorry

--  ### Exercise (3 stars): length_append_cons (Optional) ⭐⭐⭐

--  Prove this by induction on `l₁`, without using `List.length_append`.

theorem length_append_cons {α : Type} {l₁ l₂ : List α} {x : α} {n : Nat}
    (h : (l₁ ++ (x :: l₂)).length = n) :
    ((l₁ ++ l₂).length) + 1 = n := by
  sorry

--  ### Exercise (3 stars): length_append_self (Optional) ⭐⭐⭐

--  Prove this by induction on `l`, without using `List.length_append`.
--  Hint: you might need to use `length_append_cons` you just proved.

theorem length_append_self {α : Type} {n : Nat} {l : List α}
    (h : l.length = n) :
    (l ++ l).length = n + n := by
  sorry

--  ### Exercise (3 stars): list_ext ⭐⭐⭐

--  Prove the *extensionality principle* for lists. `nth?_always_none`
--  should be useful.

theorem list_ext {l₁ l₂ : List α} (h : ∀ n, nth? l₁ n = nth? l₂ n) : l₁ = l₂ := by
  sorry

--  ### Exercise (3 stars): diagonal_induction (Optional) ⭐⭐⭐

--  Prove the following principle of induction over two naturals.

theorem diagonal_induction (p : Nat → Nat → Prop)
    (hzz : p 0 0)
    (hsz : ∀ m, p m 0 → p (m + 1) 0)
    (hzs : ∀ n, p 0 n → p 0 (n + 1))
    (hss : ∀ m n, p m n → p (m + 1) (n + 1)) :
    ∀ m n, p m n := by
  sorry

--  ### Exercise (2 stars): append_left_cancel ⭐⭐

theorem append_left_cancel {α : Type} (l₁ l₂ l₃ : List α)
    (h : l₁ ++ l₂ = l₁ ++ l₃) :
    l₂ = l₃ := by
  sorry

--  ### Exercise (3 stars): map_injective_of_injective ⭐⭐⭐

--  Recall the `map` we've defined in Poly:

sf_recall
  def map {α β : Type} (f : α → β) (l : List α) : List β :=
    match l with
    | [] => []
    | head :: tail => f head :: map f tail

--  Prove that `map` is injective whenever the function is injective.

theorem map_injective_of_injective {α β : Type}
    (f : α → β)
    (hf : ∀ x y, f x = f y → x = y)
    (l₁ l₂ : List α)
    (h : map f l₁ = map f l₂) :
    l₁ = l₂ := by
  sorry

--  ### Exercise (3 stars): unzip_zip (Advanced, Manually graded) ⭐⭐⭐

--  We proved in `zip_unzip'` that `zip`ping the result of `unzip'`
--  recovers the original list. What about the other direction? Complete
--  and prove the following `unzip_zip`:
--
--      theorem unzip_zip {α β : Type}
--          {l₁ : List α} {l₂ : List β}
--          /- add appropriate parameters and hypotheses here -/ :
--          unzip (zip l₁ l₂) = (l₁, l₂) := sorry
--
--  Hint: Take a look at the definition of `zip` in Poly. Your definition
--  will need to account for the behavior of `zip` in its base cases, which
--  possibly drop some list elements.

--  FILL IN HERE

--  ### Exercise (3 stars): test_pos_of_filter_cons (Advanced) ⭐⭐⭐

theorem test_pos_of_filter_cons {α : Type}
    (test : α → Bool) (x : α) (l l' : List α)
    (h : filter test l = x :: l') :
    test x = true := by
  sorry

--  ### Exercise (4 stars): forall_exists_challenge (Advanced) ⭐⭐⭐⭐

--  Define two recursive functions, `allTrue` and `anyTrue`.
--
--  The first checks whether the given Boolean test returns `true` for
--  every element of the list.

def allTrue {α : Type} (test : α → Bool) (l : List α) : Bool := sorry

example : allTrue Nat.odd [1, 3, 5, 7, 9] = true := sorry
example : allTrue not [false, false] = true := sorry
example : allTrue Nat.even [0, 2, 4, 5] = false := sorry
example : allTrue Nat.even [] = true := sorry

--  The second checks whether it returns `true` for at least one element.

def anyTrue {α : Type} (test : α → Bool) (l : List α) : Bool := sorry

example : anyTrue Nat.even [1, 3, 4, 7] = true := sorry
example : anyTrue Nat.odd [0, 2, 4, 6] = false := sorry
example : anyTrue not [true, true, false] = true := sorry
example : anyTrue Nat.even [] = false := sorry

--  Next, define a *nonrecursive* version of `anyTrue` — call it `anyTrue'`
--  — using `allTrue` and `not`.

def anyTrue' {α : Type} (test : α → Bool) (l : List α) : Bool := sorry

--  Finally, prove a theorem `anyTrue_eq_anyTrue` stating that `anyTrue'`
--  and `anyTrue` have the same behavior.

theorem anyTrue_eq_anyTrue (α : Type) (test : α → Bool) (l : List α) :
    anyTrue test l = anyTrue' test l := by
  sorry

-- Built on 2026-09-10 14:27 UTC

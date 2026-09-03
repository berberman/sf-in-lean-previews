import LF.Poly
import LF.CustomTactics

import SFLCompat

--  # Tactics: More Basic Tactics

--  Note to developers (before next release):
--      This chapter could maybe use one or two more WORKINCLASS tags...

--  Note to developers (Benjamin Pierce @bcpierce00, before next release, 2025):
--      General comment: All the previous chapters have felt pretty smooth.
--      This one suddenly feels like we're throwing a huge amount of
--      information at them, with little scaffolding -- just a bunch of
--      miscellaneous tactics and examples. Wish it flowed better, somehow.

--  This chapter introduces several additional proof strategies and tactics
--  that allow us to begin proving more interesting properties of
--  functional programs.
--
--  We will see:
--
--  - how to use auxiliary lemmas in both "forward-" and "backward-style"
--    proofs;
--
--  - how to reason about data constructors -- in particular, how to use
--    the fact that they are injective and disjoint;
--
--  - how to strengthen an induction hypothesis, and when such
--    strengthening is required; and
--
--  - more details on how to reason by case analysis.

--  ## The `apply` Tactic

--  We often encounter situations where the goal to be proved is *exactly*
--  the same as some hypothesis in the context or some previously proved
--  lemma.

--  The `apply` tactic is useful when the goal is instead the conclusion of
--  an implication.

--  For example, suppose we have a hypothesis `h : p → q` and our goal is
--  `q`. We can use `apply h` to replace the goal `q` with the premise `p`:

example (p q : Prop) (h : p → q) (hp : p) : q := by
  apply h
  exact hp

--  The `apply` tactic also works with hypotheses and lemmas whose types
--  are implications. If the conclusion of the implication matches the
--  current goal, its premises become new subgoals to be proved.

example (n m o p : Nat) (hnm : n = m) (h : n = m → [n, o] = [m, p]) :
    [n, o] = [m, p] := by
  apply h
  exact hnm

--  When we use `apply h`, Lean tries to match the conclusion of the type
--  of `h` with the current goal. Here `h : n = m → [n, o] = [m, p]` has
--  conclusion `[n, o] = [m, p]`, which matches the current goal. Lean then
--  replaces the goal with the premise that is still needed, `n = m`. Then
--  we close the goal with `exact hnm`.
--
--  More generally, the type of a theorem or hypothesis used with `apply`
--  may have universally quantified variables and premises. Lean tries to
--  match its conclusion with the current goal to determine appropriate
--  values for the quantified variables.

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
  apply h₂
  apply h₁
  exact hEven

--  To use the `apply` tactic, the conclusion of the fact being applied
--  must match the goal. For example, `apply` will not work if the left and
--  right sides of the equality are swapped.

example (n m : Nat) (h : n = 0 → n = m) (hn : n = 0) : m = n := by
  /- Here we cannot use `apply` directly...
    ...but we can use the `symm` tactic, which switches the left
    and right sides of an equality in the goal. -/
  symm
  apply h
  exact hn

--  ### Exercise (2 stars): apply_exercise1 ⭐⭐

--  You can use `apply` with previously defined theorems, not just
--  hypotheses in the context. Use a previously-defined theorem about `rev`
--  from Poly. Use that theorem as part of your (relatively short) solution
--  to this exercise. You do not need `induction`.

theorem rev_exercise1 {α : Type} (l l' : List α) (h : l = l'.rev) :
    l' = l.rev := by
  rw [h]
  symm
  apply reverse_reverse

--  ### Exercise (1 star): apply_rewrite (Optional, Manually graded) ⭐

--  Briefly explain the difference between the tactics `apply` and `rw`.
--  What are the situations where both can usefully be applied?

--  The `rw` tactic is used to apply a known **equality** (a hypothesis
--  from the context or a previously proved lemma) to modify the goal,
--  replacing all occurrences of one side by the other.
--
--  The `apply` tactic works backward from a known fact. It takes a
--  hypothesis, theorem, or constructor whose conclusion can be matched
--  with the current goal. Lean uses the goal to infer as many of its
--  arguments as possible, and any remaining premises that still need to be
--  proved become new subgoals.

--  ### Supplying arguments to `apply`

--  The following silly example uses two rewrites in a row to get from
--  `[a, b]` to `[e, f]`.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  rw [h₁, h₂]

--  Since this is a common pattern, we might like to pull it out as a lemma
--  that records, once and for all, the fact that equality is *transitive*.

theorem trans_eq {α : Type} (x y z : α) :
    x = y → y = z → x = z := by
  intro h₁ h₂
  rw [h₁, h₂]

--  Lean already provides exactly this theorem as `Eq.trans`:

#check Eq.trans

--  Output:
--    Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c

--  In Lean's version, the arguments corresponding to `x`, `y`, and `z` are
--  implicit, since they can usually be inferred from the equality
--  hypotheses and the goal.
--
--  Now let's use our `trans_eq` to prove the example above.

--  If we simply write `apply trans_eq`, Lean can infer some arguments from
--  the goal, but not the intermediate list or the hypotheses needed for
--  the lemma's premises. If you inspect the proof state after `apply`, you
--  will see that Lean has created three goals:
--
--  1. `[a, b] = ?y`
--  2. `?y = [e, f]`
--  3. `List Nat`
--
--  Recall that `trans_eq` has five arguments. From the goal, Lean can
--  infer the endpoints `x` and `z`, namely `[a, b]` and `[e, f]`. But it
--  still needs an intermediate term `y`.
--
--  We want to prove `[a, b] = [e, f]`. By transitivity, it's enough to
--  prove `[a, b] = ?y` and `?y = [e, f]`, for some intermidiate list `?y`.
--  Here `?y` is a *metavariable*: a place holder for a value Lean has not
--  yet determined. Before we provide the hypothesis `h₂`, Lean doesn't
--  know that this intermediate list shoud be `[c, d]`.

sf_expect_failure_in
  example (a b c d e f : Nat)
      (h₁ : [a, b] = [c, d])
      (h₂ : [c, d] = [e, f]) :
      [a, b] = [e, f] := by
    apply trans_eq

--  Output:
--    unsolved goals
--    case a
--    a b c d e f : Nat
--    h₁ : [a, b] = [c, d]
--    h₂ : [c, d] = [e, f]
--    ⊢ [a, b] = ?y
--
--    case a
--    a b c d e f : Nat
--    h₁ : [a, b] = [c, d]
--    h₂ : [c, d] = [e, f]
--    ⊢ ?y = [e, f]
--
--    case y
--    a b c d e f : Nat
--    h₁ : [a, b] = [c, d]
--    h₂ : [c, d] = [e, f]
--    ⊢ List Nat

--  One way to resolve this is to supply all the arguments and hypotheses
--  explicity:

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq [a, b] [c, d] [e, f] h₁ h₂

--  In the previous example, we had to specify the `x` and `z` arguments to
--  `trans_eq` before we could supply `[c, d]` for `y` or `eq1` and `eq2`
--  for the premises. However, we just said that Lean was able to infer
--  these arguments, so it's a bit redundant (and wordy) for us to do it.

--  Thankfully, Lean allows us to use `_`s for positional arguments that it
--  can infer.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq _ _ _ h₁ h₂

--  If we know the name of the argument we are supplying (in this case
--  `y`), we can name it directly and avoid typing any `_`s. This feature
--  is called *named arguments*. Named arguments can be used in function
--  applications generally, not just with `apply`.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq (y := [c, d])
  apply h₁
  apply h₂

--  Like any other kind of software, there are conventions and best
--  practices associated with writing proofs in Lean. One of these
--  conventions concerns the use of the `exact` tactic. When fully applying
--  another theorem like in the previous examples, it is considered good
--  practice to use the `exact` tactic instead of `apply`.This signals to a
--  reader of the proof that the proof is "exactly" an instance of another
--  lemma, and that nothing of particular interest is happening here. This
--  achieves a similar goal as when a mathematician says that one result is
--  "just" an instance of another.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  exact trans_eq _ _ _ h₁ h₂

--  Recall the `calc` we have learned in the UsingLean chapter. It works by
--  chaining equalities together using transitivity, serving the same
--  purpose here as applying `trans_eq`.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  calc
  [a, b] = [c, d] := by rw [h₁]
  [c, d] = [e, f] := by rw [h₂]

--  ### Exercise (3 stars): trans_eq_exercise (Optional) ⭐⭐⭐

theorem trans_eq_exercise (n m o p : Nat)
    (h₁ : m = o.minusTwo)
    (h₂ : (n + p) = m) :
    (n + p) = o.minusTwo := by
  calc n + p
  _ = m := by rw [h₂]
  _ = o.minusTwo := by rw [h₁]

--  ## The `injection` and `contradiction` Tactics

--  Recall the definition of natural numbers:

sf_recall
  inductive Nat : Type where
    | zero
    | succ (n : Nat)

--  It is obvious from this definition that every number has one of two
--  forms: either it is the constructor `0` or it is built by applying the
--  constructor `.succ` to another number. But there is more here than
--  meets the eye: implicit in the definition are two additional facts:
--
--  - The constructor `.succ` is *injective* (or *one-to-one*). That is, if
--    `n + 1 = m + 1`, it must also be that `n = m`.
--
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

--  This technique for injectivity can be generalized to any constructor by
--  writing the equivalent of `pred` — i.e., writing a function that
--  "undoes" one application of the constructor.
--
--  As a convenient alternative, Lean provides a tactic called `injection`
--  that allows us to exploit the injectivity of any constructor. Here is
--  an alternate proof of the above theorem using `injection`:

example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  injection h with hmn

--  By writing `injection h with hmn` at this point, we are asking Lean to
--  generate all equations that it can infer from `h` using the injectivity
--  of constructors (in the present example, the equation `n = m`). This
--  equation is added as a hypothesis (called `hmn` in this case) into the
--  context. Because this equation is exactly our goal, in this case the
--  `injection` tactic is able to automatically close the goal.

--  `with ...` can be omitted if the generated equations are not used.

example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  injection h

--  Here's a more interesting example that shows how `injection` can derive
--  multiple equations at once.

example (n m o : Nat)
    (h : [n, m] = [o, o]) :
    n = m := by
  injection h with h₁ h₂
  injection h₂ with h₃
  rw [h₁, h₃]

--  There is also a related tactic, `injections`, that applies the
--  `injection` tactic to all your hypotheses at once, as many times in a
--  row as it can. Using this tactic can avoid needing to repeatedly use
--  `injection` on lists. For example:

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
  injections hxz hyl_j
  rw [h₂] at hyl_j
  injection hyl_j with hyz
  rw [hyz, hxz]

--  So much for injectivity of constructors. What about disjointness?

--  The principle of disjointness says that two terms beginning with
--  different constructors (like `0` and `Nat.succ`, or `true` and `false`)
--  can never be equal. This means that, any time we find ourselves in a
--  context where we've *assumed* that two such terms are equal, we are
--  justified in concluding anything we want, since the assumption is
--  nonsensical.

--  The `contradiction` tactic, which we've already seen for handling cases
--  where we have assumed `False`, also embodies this principle: if we have
--  a a hypothesis involving an equality between different constructors
--  (e.g., `false = true`), `contradiction` solves the current goal
--  immediately. Some examples:

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
--  entails anything (even manifestly false things!).
--
--  Notice that due to the way addition on naturals is defined, deriving a
--  contradiction from `1 + n = 0` is not as trivial as it seems.

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
  contradiction

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
--  (3) Hypothesis `h` becomes `hxy : x = y`.
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

--  The injectivity of constructors allows us to reason that
--  `∀ (n m : Nat), n + 1 = m + 1 → n = m`. The converse of this
--  implication is an instance of a more general fact about both
--  constructors and functions:

example {α β : Type} (f : α → β) (x y : α)
    (h : x = y) : f x = f y := by
  rw [h]

example (n m : Nat) (h : n = m) :
    n + 1 = m + 1 := by
  rw [h]

--  Indeed, there is also a tactic named `congr` that can prove such goals
--  directly. Given a goal of the form `f a₁ ... aₙ = g b₁ ... bₙ`, the
--  tactic `congr` will produce subgoals of the form `f = g`, `a₁ = b₁`,
--  ..., `aₙ = bₙ`. At the same time, any of these subgoals that are simple
--  enough (e.g., immediately provable by `rfl`) will be automatically
--  discharged.

example (n m : Nat) (h : n = m) :
    n + 1 = m + 1 := by
  congr

--  The `congr` tactic also accepts a numerical argument, which tells Lean
--  how deeply to decompose the goal. So, given a goal like
--  `((a, b), (c, d)) = ((e, f), (g, h))`, `congr 1` only applies `congr`
--  once to the goal, and would produce two subgoals: `(a, b) = (e, f)` and
--  `(c, d) = (g, h)`. `congr 2`, meanwhile, would apply `congr` again to
--  both these subgoals, and produce four subgoals: `a = e`, `b = f`,
--  `c = g` and `d = h`. Using `congr` without an argument always
--  decomposes the goal as deeply as possible.
--
--  Why does Lean provide this level of flexibility? Depending on what we
--  are trying to prove, deeper applications of `congr` may make our goal
--  unprovable. Consider this example:

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
  /- Only shallowly using `congr` here allows us to complete the proof -/
  congr 1
  rw [Nat.add_comm]
  congr

--  Note to developers (Niklas Halonen @xhalo32):
--      The above proof can be made simpler by just rewriting before the
--      `congr`, so arguably it doesn't require limiting the depth.
--
--      `example (a b c d : Nat) (hab : a = b) (hcd : c = d) :
--          (a, c + 1) = (b, 1 + d) := by
--        rw [Nat.add_comm]
--        congr`

--  ## Using `apply` on Hypotheses

--  The tactic `apply t at h` matches an implication `t` (say, of the form
--  `a → b`) against a hypothesis `h` in the local context. Unlike ordinary
--  `apply`, which matches the goal against `b` and replaces it with the
--  subgoal `a`), `apply t at h` matches the type of `h` against `a` and,
--  if successful, replaces `h` with a hypothesis of type `b`.
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
--  goal is reached. Backward reasoning begins with the *goal* and works
--  backward through implications that would prove it, until remaining
--  goals are facts that are already known.
--
--  The informal proofs in mathematics and computer science often use
--  forward reasoning. In Lean, however, backward reasoning is often more
--  idiomatic, though forward reasoning can sometimes be easier to follow
--  or more natural for particular proofs.
--
--  You may be interested to know that the `apply ... at ...` tactic is not
--  part of Lean's core set of tactics. However, Lean makes it very easy
--  for users to define new tactics that suit their particular proof style,
--  and so the developers of the
--  [Mathlib](https://github.com/leanprover-community/mathlib4) library
--  defined the `apply ... at ...` tactic to better support forward
--  reasoning. Mathlib is a very large development, so we will not import
--  the whole thing here, but we have made `apply ... at ...` available
--  because it is quite useful.

--  To apply a tactic in multiple places at the same time, you can list
--  multiple hypotheses in a row after the `at`. You can also explicitly
--  use a tactic on the goal (usually because you are applying the tactic
--  to both a hypothesis and the goal) by including it after the `at` with
--  the turnstile symbol `⊢`, written `\|-`, `\goal` or `\vdash`.

example (n m : Nat) (h : n + 0 = m) : n = m + 0 := by
  rw [Nat.add_zero] at h ⊢
  assumption

--  ## Specializing Hypotheses

--  We've already seen how we can use `have` to do forward reasoning, by
--  letting us state and prove useful facts that get us closer to the main
--  goal we're trying to prove. Often, though, these facts are just special
--  cases of more general hypotheses we already have.
--
--  If `h` is a quantified hypothesis in the current context — i.e.,
--  `h : ∀ (x : α), P x` — then we can use `have` to obtain a special case
--  of `h` by supplying a value for `x`. For example, `have h := h e`
--  introduces a new `h` which `x` has been instantiated with `e`.
--
--  For example:

example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  have h := h 1
  rw [Nat.mul_one] at h
  exact h

--  You may notice that, in the above proof, the original `h` is still
--  present in the context, although it is shadowed by the new `h`. Often
--  we don't care to keep this old hypothesis around, and so we can use the
--  `replace` tactic instead. It behaves like `have`, except that it gets
--  rid of the old hypothesis afterwards when possible:

example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  replace h := h 1
  rw [Nat.mul_one] at h
  exact h

--  Specializing a hypothesis in this way is common enough that Lean
--  provides the `specialize` tactic for it. For example, `specialize h 1`
--  is a more concise way of writing `replace h := h 1`:

example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  specialize h 1
  rw [Nat.mul_one] at h
  exact h

--  ### Exercise (3 stars): nth?_always_none ⭐⭐⭐

--  Use `have`, `replace`, or `specialize` to prove the the following
--  lemma, following the model of the examples above. Do not use
--  `induction`.

theorem nth?_always_none (l : List Nat) (h : ∀ i, nth? l i = none) :
    l = [] := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have h := h 0
    rw [nth?] at h
    contradiction

--  Tactics like `have` and `replace` can also be used with lemmas and
--  theorems we've already proven, not just things in our context. Using
--  these tactis before `apply` gives us yet another way to control where
--  `apply` does its work.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  have h := trans_eq (y := [c, d])
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

--  Sometimes `induction` gives us an an induction hypothesis too specific
--  to be useful. This can happen when another varaible in the theorem is
--  fixed during the induction, even though the induction step might need
--  to use it with different values of that variables.
--
--  For example, suppose we want to show that `Nat.double` is injective —
--  i.e., that it maps different arguments to different results:

sf_experiment
  theorem double_injective (n m : Nat) (h : n.double = m.double) : n = m := sorry

--  The way we start this proof is a bit delicate: if we begin it with

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

--  We get stuck — `m` is fixed during the induction, so in the successor
--  case the induction hypothesis `ih` is specialized to the current value
--  of `m`. After the case split, that value is `m' + 1`, and the induction
--  hypothesis has the form:
--
--      ih : n'.double = (m' + 1).double → n' = m' + 1
--
--  From `h`, using the definition of `Nat.double` we can obtain

--  n'.double = m'.double

--  and to prove the goal we would like to apply an induction hypothesis at
--  `m'`. Nevertheless, `ih` is specialized to `m' + 1` — it would require

--  n'.double = (m' + 1).double

--  and would conclude

--  n' = m' + 1

--  which is not what we need. Instead, we need an induction hypothesis
--  that is general in `m`:
--
--      ih : ∀ m, n'.double = m.double → n' = m
--
--  Then in this branch we can instantiate it with `m'`.

--  We can obtain a more generalized induction hypothesis by writing
--
--      induction n generalizing m with
--
--  What went wrong?

--  The problem is that `m` is already in the context when we invoke
--  `induction n`. Since `m` is an ordinary argument of the theorem, this
--  is exactly what we normally want — we are considering some particular
--  `n` and `m`, together with the hypothesis `n.double = m.double` and
--  trying to prove `n = m`.
--
--  The claim itself makes perfect sense, but for the induction, however,
--  keeping `m` fixed causes the trouble: we are proving, for *all* `n`,
--  the proposition
--
--  - `P n` = "if `n.double = m.double`, then `n = m`"
--
--  by showing
--
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
--
--  - "if `n.double = m.double` then `n = m`"
--
--  then we can prove
--
--  - "if `(n + 1).double = m.double` then `n + 1 = m`".
--
--  To see why this is strange, let's choose of a particular `m` — say,
--  `5`. The statement is then saying that, if we know
--
--  - `Q` = "if `n.double = 10` then `n = 5`"
--
--  then we can prove
--
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

--  Trying to carry out this proof by induction on `n` with `m` fixed
--  doesn't work, because we are then trying to prove a statement involving
--  *every* `n` but just a *particular* `m`.
--
--  A successful proof of `double_injective` *generalizes* `m` when
--  carrying out the induction on `n`, so that the induction hypothesis
--  holds for every `m`, rather than for just the particular `m` in the
--  context.

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
--
--  - First, suppose `n = 0`. We must show that, for any `m`, if
--    `Nat.double 0 = m.double`, then `0 = m`.
--
--    There are two cases to consider for `m`:
--
--    1. If `m = 0`, we are done.
--
--    2. Otherwise if `m = m' + 1` for some `m'`, then by definition of
--       `Nat.double` we have `Nat.double 0 = 0` and
--       `(m' + 1).double = m'.double + 2`. Clearly `0` cannot equal
--       `m'.double + 2`, so this case is impossible.
--
--  - Second, suppose `n = n' + 1`. The induction hypothesis says that, for
--    every `m`, if `(n' + 1).double = m.double` then `n' + 1 = m`. Again
--    there are two cases to consider for `m`:
--
--    1. If `m = 0`, then by the definition of `Nat.double` our assumption
--       says `n'.double + 2 = 0`, which is impossible.
--
--    2. Otherwise suppose `m = m' + 1`. Our assumption is then that
--       `(n' + 1).double = (m' + 1).double`. By the definition of
--       `Nat.double`, this gives `n'.double + 2 = m'.double + 2`. By
--       injectivity of `Nat.succ`, we obtain `n'.double = m'.double`. We
--       can now instantiate the induction hypothesis with `m'`, obtaining
--       `n' = m'`. Now we can conclude `n' + 1 = m' + 1`, which is exactly
--       what we wanted to show.
--
--  *Qed*.

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
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m' => rw [Nat.add_zero] at h; contradiction
  | succ n' ih =>
    cases m with
    | zero => rw [Nat.add_zero, Nat.add_zero 0] at h; contradiction
    | succ m' =>
      congr
      apply ih
      rw [Nat.add_succ, Nat.add_succ (m' + 1)] at h
      injection h with h
      rw [Nat.add_comm, Nat.add_comm (m' + 1)] at h
      injections h

--  ### Exercise (2 stars): add_self_injective_informal ⭐⭐

--  Give a careful informal proof of `add_self_injective`, stating the
--  induction hypothesis explicitly and being as explicit as possible about
--  quantifiers, everywhere.

--  *Theorem*: For any natural numbers `n` and `m`, if `n + n = m + m`,
--  then `n = m`. *Proof*: We prove by induction on `n` that for *every*
--  natrual number `m`, if `n + n = m + m`, then `n = m`.
--
--  - First, suppose that `n = 0`. We must show that for every `m`, if
--    `0 + 0 = m + m` then `0 = m`. There are two cases for `m`. If
--    `m = 0`, we are done. Otherwise `m = m' + 1` for some `m'`. Then
--    `m + m` cannot equal `0 + 0`. Thus this case is impossible.
--
--  - Now suppose that `n = n' + 1`. The induction hypothesis says that,
--    for every natrual number `m`, `n' + n' = m + m` implies `n' = m`. We
--    must show, for every `m`, that `(n' + 1) + (n' + 1) = m + m` implies
--    `n' + 1 = m`. Again there are two cases for `m`. If `m = 0`, then the
--    assumed equality is impossible — `(n' + 1) + (n' + 1)` cannot equal
--    to `0`. Otherwise `m = m' + 1` for some `m'`. Cancelling one
--    successor from each side of the equality and rearranging the
--    additions gives `n' + n' = m' + m'`. We can now apply the induction
--    hypothesis with `m'` to obtain `n' = m'`. Then it follows that
--    `n' + 1 = m' + 1`, which is our final goal.
--
--  *Qed*.

--  ## Rewriting with Conditional Statements

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
--  `m + p = q`, which follows from `hm`, and the condition from
--  `double_injective`, `n.double = m.double`, whicch follows from `h`.

--  If we rewrite with a conditional statement of the form `P → a = b`,
--  then Lean tries to rewrite with `a = b`, and then asks us to prove `P`
--  in a new subgoal. If the statement has more than one assumption, then
--  we get one subgoal for each assumption.

--  ### Exercise (3 stars): nth?_after_last ⭐⭐⭐

--  Prove this by induction on `l`.

theorem nth?_after_last {α : Type}
    {n : Nat} {l : List α} (h : l.length = n) :
    nth? l n = none := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons] at h
    rw [← h]
    rw [nth?]
    apply ih
    rfl

--  ### Exercise (3 stars): length_append_cons (Optional) ⭐⭐⭐

--  Prove this by induction on `l₁`, without using `List.length_append`.

theorem length_append_cons {α : Type} {l₁ l₂ : List α} {x : α} {n : Nat}
    (h : (l₁ ++ (x :: l₂)).length = n) :
    ((l₁ ++ l₂).length) + 1 = n := by
  induction l₁ generalizing n with
  | nil => assumption
  | cons y ys ih =>
    rw [List.cons_append, List.length_cons] at *
    /- A trick here: by using `rfl` to close `(ys ++ x :: l₂).length = n`
       we effectively choose `n` to be `(ys ++ x :: l₂).length`
    -/
    rw [ih rfl]
    assumption

--  ### Exercise (3 stars): length_append_self (Optional) ⭐⭐⭐

--  Prove this by induction on `l₁`, without using `List.length_append`.
--  Hint: you might need to use `length_append_cons` you just proved.

theorem length_append_self {α : Type} {n : Nat} {l : List α}
    (h : l.length = n) :
    (l ++ l).length = n + n := by
  induction l generalizing n with
  | nil =>
    rw [List.append_nil,  List.length_nil] at *
    rw [← h]
  | cons x xs ih =>
    rw [List.cons_append, List.length_cons] at *
    rw [← length_append_cons rfl]
    rw [ih rfl, ← h]
    rw [Nat.add_add_add_comm]

--  ### Exercise (3 stars): diagonal_induction (Optional) ⭐⭐⭐

--  Prove the following principle of induction over two naturals.

theorem diagonal_induction (p : Nat → Nat → Prop)
    (hzz : p 0 0)
    (hsz : ∀ m, p m 0 → p (m + 1) 0)
    (hzs : ∀ n, p 0 n → p 0 (n + 1))
    (hss : ∀ m n, p m n → p (m + 1) (n + 1)) :
    ∀ m n, p m n := by
  intro m n
  induction m generalizing n with
  | zero =>
    induction n with
    | zero => exact hzz
    | succ n' ih =>
      apply hzs
      apply ih
  | succ m' ih =>
    induction n with
    | zero =>
      apply hsz
      apply ih
    | succ n' ih' =>
      apply hss
      apply ih

--  ## Using `cases` on Expressions

--  We have seen many examples where `cases` is used to perform case
--  analysis of the value of some variable. Sometimes we need to reason by
--  cases on the result of some *expression*. We can also do this with
--  `cases`.
--
--  Here are some examples:

def chooseIf {α : Type} (test : α → Bool) (x y : α) : α :=
  if test x then x else y

theorem chooseIf_self {α : Type} (test : α → Bool) (x : α) :
    chooseIf test x x = x := by
  rw [chooseIf]
  cases test x <;> rfl

--  After *unfolding* `chooseIf` in the above proof, we find that we are
--  stuck on `(if test x = true then x else x) = x`. But either `test x` is
--  `true` or it isn't, so we can use `cases (test x)` to let us reason
--  about the two cases.
--
--  In general, the `cases` tactic can be used to perform case analysis of
--  the results of arbitrary computations. If `e` is an expression whose
--  type is some inductively defined type `T`, then, for each constructor
--  `c` of `T`, `cases e` generates a subgoal in which all occurrences of
--  `e` (in the goal and in the context) are replaced by `c`.

--  ### Destructing Tuples

--  `cases` is useful when we are dealing with inductively defined types
--  that can be one thing or another; a `Bool` is either a `false` or a
--  `true`, and a `Nat` is either `0` or `succ n`. When we want more
--  information about inductively defined types that are products of
--  multiple things, we instead want a way to get the pieces of that value
--  out from it.
--
--  When we have a value `v : α × β` in our context, we can get the first
--  and second projections of `v` using this tactic:
--
--      let ⟨a, β⟩ := v

--  ### Exercise (3 stars): zip_unzip' ⭐⭐⭐

--  Here is an implementation of the `unzip` function mentioned in chapter
--  Poly:

def unzip' {α β : Type} (l : List (α × β)) : List α × List β := (
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    let (lx, ly) := unzip' t
    (x :: lx, y :: ly))

--  Prove that `unzip'` and `zip` are inverses in the following sense.
--  Remember that you can use `dsimp only` to simplify expressions
--  involving pairs and `fst` and `snd`.

theorem zip_unzip' {α β : Type} (l : List (α × β))
    (l₁ : List α) (l₂ : List β)
    (h : unzip' l = (l₁, l₂)) :
    zip l₁ l₂ = l := by
  induction l generalizing l₁ l₂ with
  | nil =>
    rw [unzip'] at h
    injections h₁ h₂
    rw [← h₁, ← h₂, zip]
  | cons x xs ih =>
    let ⟨a, b⟩ := x
    rw [unzip'] at h
    injections h₁ h₂
    rw [← h₁, ← h₂, zip, ih]
    dsimp only

--  ### Splitting with Equations

--  When using `cases`, we can specify to Lean that it should remember an
--  equality between a compound expression and what we are decomposing it
--  into, using `cases h : ...` syntax. This information can actually be
--  critical, and, if we leave it out, we might lack information we need to
--  complete a proof.

--  For example, suppose we define a function `keepIf` like this:

def keepIf {α : Type} (test : α → Bool) (x : α) : Option α :=
  if test x then some x else none

--  Now suppose that we want to prove `keepIf_some`. If we start the proof
--  like this (with no `h : ⋯` on the `cases`)...

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

--  ... then we are stuck at this point because the context does not
--  contain enough information to prove the goal. Because `test x` appears
--  in our hypothesis, rather than in our goal, `cases (test x)` does not
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
  cases b with
  | false =>
    cases h₁ : f false with
    | false => rw [h₁]; assumption
    | true =>
      cases h₂ : f true with
      | false => assumption
      | true => assumption
  | true =>
    cases h₁ : f true with
    | false =>
      cases h₂ : f false with
      | false => assumption
      | true => assumption
    | true => rw [h₁]; assumption

--  ## Review

--  We've now talked about many of Lean's most fundamental tactics. We'll
--  introduce a few more in the coming chapters, and later on we'll see
--  some more powerful *automation* tactics that make Lean help us with
--  low-level details. But basically we've got what we need to get work
--  done.
--
--  Here are the ones we've seen so far.
--
--  Managing goals and hypotheses:
--
--  - `intro h`: move an assumption/quantified variable from the goal into
--    the local context
--
--  - `apply thm`: use a theorem, hypothesis, or constructor whose
--    conclusion matches the goal; its premises become new goals
--
--  - `apply thm at h`: use a theorem on a hypothesis in the context,
--    replacing `h` by the resulting
--
--    fact (forward reasoning)
--
--  - `specialize h ...`: instantiate quantified variables in a hypothesis,
--    modifying `h` in place
--
--  - `replace h := ...`: replace a hypothesis with a newly proved fact
--
--  - `have h : P := ...`: prove a local fact `P` and add it to the context
--    with the name `h`
--
--  - `contradiction`: close the current goal when the context contains
--    contradictory assumptions
--
--  Equality, rewriting, and unfolding:
--
--  - `rfl`: close an equality that holds by reflexivity (possibly after
--    computation)
--
--  - `rw [h]`: rewrite the goal using an equality hypothesis or theorem
--
--  - `rw [d]`: unfold a definition in the goal
--
--  - `rw [h] at h'`: rewrite a hypothesis using an equality hypothesis or
--    theorem
--
--  - `rw [d] at h'`: unfold a definition in a hypothesis
--
--  - `symm`: reverse an equality goal, changing `t = u` to `u = t`
--
--  - `symm at h`: reverse an equality hypothesis
--
--  - `calc`: prove a goal about equality or another transitive relation by
--    giving a sequence of intermediate steps
--
--  - `congr`: use congruence to reduce an equality between expressions
--    with the same outer form; for example, a goal `f x = f y` may be
--    reduced to `x = y`
--
--  - `injection h with ...`: use injectivity of constructors to extract
--    equalities from constructor applications equations
--
--  - `injections`: repeatedly use constructor injectivity on suitable
--    equalities in the context
--
--  Case analysis:
--
--  - `cases x`: reason separately about the possible constructors of an
--    inductively defined value
--
--  - `cases h : e`: perform case analysis on an expression `e` and add an
--    equation named `h` recording the result of the case analysis
--
--  Induction:
--
--  - `induction x`: prove the goal by induction on an inductively defined
--    value
--
--  - `induction x generalizing y`: induction on `x` while generalizing the
--    listed local variables, giving a more general induction hypothesis

--  ### Additional Exercises

--  ### Exercise (2 stars): append_left_cancel ⭐⭐

--  Note to developers (Niklas Halonen @xhalo32):
--      After `injections _ eq`, `eq`'s type uses `.append` rather than
--      `++` which is a bit confusing. Not sure why that happens.

theorem append_left_cancel {α : Type} (l₁ l₂ l₃ : List α)
    (h : l₁ ++ l₂ = l₁ ++ l₃) :
    l₂ = l₃ := by
  induction l₁ with
  | nil => assumption
  | cons x xs ih =>
    injections _ eq
    exact ih eq

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
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons y ys =>
      rw [map_cons, map_nil] at h
      contradiction
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      rw [map_cons, map_nil] at h
      contradiction
    | cons y ys =>
      rw [map_cons, map_cons] at h
      injection h with hxy hxs
      rw [hf x y hxy, ih ys hxs]

--  ### Exercise (3 stars): unzip_zip (Advanced, Manually graded) ⭐⭐⭐

--  We proved `zip_unzip'` that `zip`ping the result of `unzip` recovers
--  the original list. What about the other direction? Complete and prove
--  the following `unzip_zip`:
--
--      theorem unzip_zip {α β : Type}
--          {l₁ : List α} {l₂ : List β}
--          /- add appropriate parameters and hypotheses here -/ :
--          unzip (zip l₁ l₂) = (l₁, l₂) := sorry
--
--  Hint: Take a look at the definition of `zip` in Poly. Your definition
--  will need to account for the behavior of `zip` in its base cases, which
--  possibly drop some list elements.

theorem unzip_zip {α β : Type}
    {l₁ : List α} {l₂ : List β}
    (h : l₁.length = l₂.length) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons => contradiction
  | cons x xs ih =>
    cases l₂ with
    | nil => contradiction
    | cons y ys =>
      rw [zip_cons_cons, unzip]
      rewrite [ih]
      · rfl
      · injections

/- Here is one more approach -/
theorem unzip_zip' {α β : Type}
    {l₁ : List α} {l₂ : List β}
    {l : List (α × β)} (h : (l₁, l₂) = unzip l) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  induction l generalizing l₁ l₂ with
  | nil =>
    rw [unzip_nil] at h
    injections h₁ h₂
    rw [h₁, h₂, zip, unzip]
  | cons x xs ih =>
    let ⟨a, b⟩ := x
    rw [unzip] at h
    injections h₁ h₂
    rewrite [h₁, h₂, zip, unzip, ih]
    · rfl
    · rfl

--  ### Exercise (3 stars): test_pos_of_filter_cons (Advanced) ⭐⭐⭐

theorem test_pos_of_filter_cons {α : Type}
    (test : α → Bool) (x : α) (l l' : List α)
    (h : filter test l = x :: l') :
    test x = true := by
  induction l generalizing x l' test with
  | nil => contradiction
  | cons y ys ih =>
    rw [filter] at h
    cases hy : (test y)
    · rw [hy] at h
      rw [cond_false] at h
      exact ih _ _ _ h
    · rw [hy] at h
      rw [cond_true] at h
      injections h1 h2
      rw [← h1]
      exact hy

--  ### Exercise (4 stars): forall_exists_challenge (Advanced) ⭐⭐⭐⭐

--  Define two recursive functions, `allTrue` and `anyTrue`.
--
--  The first checks whether the given Boolean test returns `true` for
--  every element of the list.

def allTrue {α : Type} (test : α → Bool) (l : List α) : Bool := (
  match l with
  | [] => true
  | x :: xs => (test x) && (allTrue test xs))

example : allTrue Nat.odd [1, 3, 5, 7, 9] = true := (by rfl)
example : allTrue not [false, false] = true := (by rfl)
example : allTrue Nat.even [0, 2, 4, 5] = false := (by rfl)
example : allTrue Nat.even [] = true := (by rfl)

--  The second checks whether it returns `true` for at least one element.

def anyTrue {α : Type} (test : α → Bool) (l : List α) : Bool := (
  match l with
  | [] => false
  | x :: xs => (test x) || (anyTrue test xs))

example : anyTrue Nat.even [1, 3, 4, 7] = true := (by rfl)
example : anyTrue Nat.odd [0, 2, 4, 6] = false := (by rfl)
example : anyTrue not [true, true, false] = true := (by rfl)
example : anyTrue Nat.even [] = false := (by rfl)

--  Next, define a *nonrecursive* version of `anyTrue` — call it `anyTrue'`
--  — using `allTrue` and `not`.

def anyTrue' {α : Type} (test : α → Bool) (l : List α) : Bool := (
  !(allTrue (fun x => !(test x)) l))

--  Finally, prove a theorem `anyTrue_eq_anyTrue` stating that `anyTrue'`
--  and `anyTrue` have the same behavior.

theorem anyTrue_eq_anyTrue (α : Type) (test : α → Bool) (l : List α) :
    anyTrue test l = anyTrue' test l := by
  induction l generalizing test with
  | nil => rfl
  | cons x xs ih =>
    rw [anyTrue, ih, anyTrue', anyTrue', allTrue]
    rw [Bool.not_and, Bool.not_not]

-- Built on 2026-09-03 11:55 UTC

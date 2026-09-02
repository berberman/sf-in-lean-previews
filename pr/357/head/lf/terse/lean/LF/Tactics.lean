import LF.Poly
import LF.CustomTactics

import SFLCompat

--  # Tactics: More Basic Tactics

--  ## The `apply` Tactic

--  The `apply` tactic is useful when the goal is instead
--  the conclusion of an implication.

example (p q : Prop) (h : p → q) (hp : p) : q := by
  apply h
  exact hp

--  `apply` also works with hypotheses whose types are
--  implications:

example (n m o p : Nat) (hnm : n = m) (h : n = m → [n, o] = [m, p]) :
    [n, o] = [m, p] := by
  apply h
  exact hnm

--  Observe how Lean picks appropriate values for the
--  universally quantified variables of the hypothesis:

example (n m : Nat) (h₁ : (n, n) = (m, m))
    (h₂ : ∀ (q r : Nat), (q, q) = (r, r) → [q] = [r]) :
    [n] = [m] := by
  apply h₂
  exact h₁

--  The goal must match the hypothesis for `apply` to work:

example (n m : Nat) (h : n = 0 → n = m) (hn : n = 0) : m = n := by
  /- Here we cannot use `apply` directly...
    ...but we can use the `symm` tactic, which switches the left
    and right sides of an equality in the goal. -/
  symm
  apply h
  exact hn

--  ### Supplying arguments to `apply`

--  The following silly example uses two rewrites in a row
--  to get from `[a, b]` to `[e, f]`.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  rw [h₁, h₂]

--  Since this is a common pattern, we might like to pull it
--  out as a lemma that records, once and for all, the fact
--  that equality is *transitive*.

theorem trans_eq {α : Type} (x y z : α) :
    x = y → y = z → x = z := by
  intro h₁ h₂
  rw [h₁, h₂]

--  Lean already provides exactly this theorem as
--  `Eq.trans`:

#check Eq.trans

--  Output:
--    Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c

--  In Lean's version, the arguments corresponding to `x`,
--  `y`, and `z` are implicit, since they can usually be
--  inferred from the equality hypotheses and the goal.
--
--  Now let's use our `trans_eq` to prove the example above.

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

--  One way to resolve this is to supply all the arguments
--  and hypotheses explicity:

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq [a, b] [c, d] [e, f] h₁ h₂

--  Thankfully, Lean allows us to use `_`s for positional
--  arguments that it can infer.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq _ _ _ h₁ h₂

--  If we know the name of the argument we are supplying (in
--  this case `y`), we can name it directly and avoid typing
--  any `_`s. This feature is called *named arguments*.
--  Named arguments can be used in function applications
--  generally, not just with `apply`.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq (y := [c, d])
  apply h₁
  apply h₂

--  By convention, we use `exact` for situations when we can
--  completely finish the proof with a single application.

example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  exact trans_eq _ _ _ h₁ h₂

--  We can also use `calc`.

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
  sorry

--  ## The `injection` and `contradiction` Tactics

--  The constructors of inductive types are *injective* (or
--  *one-to-one*) and *disjoint*.
--
--  E.g., for `Nat`:
--
--  - if `n + 1 = m + 1` then it must be that `n = m`
--  - `0` is not equal to `n + 1` for any `n`

--  ### Injectivity

--  We can *prove* the injectivity of `Nat.succ` by using
--  the `Nat.pred` function:

example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  have : n = Nat.pred (n + 1) := by rfl
  /- The hypothesis name defaults to `this` when unspecified. -/
  rewrite [this, h]
  rw [Nat.pred_succ]

--  As a convenience, the `injection` tactic allows us to
--  exploit injectivity of any constructor (not just
--  `Nat.succ`).

example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  injection h with hmn

--  `with ...` can be omitted if the generated equations are
--  not used.

example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  injection h

--  Here's a more interesting example that shows how
--  `injection` can derive multiple equations at once.

example (n m o : Nat)
    (h : [n, m] = [o, o]) :
    n = m := by
  sorry

--  There is also a related tactic, `injections`, that
--  applies the `injection` tactic to all your hypotheses at
--  once, as many times in a row as it can. Using this
--  tactic can avoid needing to repeatedly use `injection`
--  on lists. For example:

example (n m o : Nat)
    (h : [n, m] = [o, o]) :
    n = m := by
  sorry

--  ### Exercise (3 stars): injection_ex3 ⭐⭐⭐

theorem injection_ex3 {α : Type} (x y z : α) (l j : List α)
    (h₁ : x :: y :: l = z :: j)
    (h₂ : j = z :: l) :
    x = y := by
  sorry

--  So much for injectivity of constructors. What about
--  disjointness?

--  Two terms beginning with different constructors (like
--  like `0` and `Nat.succ`, or `true` and `false`) can
--  never be equal.

--  The `contradiction` tactic, which we've already seen for
--  handling cases where we have assumed `False`, also
--  embodies this principle: if we have a a hypothesis
--  involving an equality between different constructors
--  (e.g., `false = true`), `contradiction` solves the
--  current goal immediately. Some examples:

example (n m : Nat)
    (h : false = true) :
    n = m := by
  contradiction

example (n : Nat)
    (h : n + 1 = 0) :
    2 + 2 = 5 := by
  contradiction

--  These examples are instances of a logical principle
--  known as the *principle of explosion*, which asserts
--  that a contradictory hypothesis entails anything (even
--  manifestly false things!).
--
--  Notice that due to the way addition on naturals is
--  defined, deriving a contradiction from `1 + n = 0` is
--  not as trivial as it seems.

sf_expect_failure_in
  example (n : Nat)
      (h : 1 + n = 0) :
      2 + 2 = 5 := by
    contradiction -- doesn't work because `1 + n` doesn't reduce to `n.succ`.

--  To fix it, rewriting with `Nat.one_add` changes the
--  hypothesis from `1 + n = 0` to `n.succ = 0`. Then Lean
--  can immediately recognize this as impossible.

example (n : Nat)
    (h : 1 + n = 0) :
    2 + 2 = 5 := by
  rw [Nat.one_add] at h
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
--  and we apply the tactic `injection h with hxy`. What
--  will happen?
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
--  and we apply the tactic `injection h with hxy`. What
--  will happen?
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
--  and we apply the tactic `injection h with hxy`. What
--  will happen?
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
--  and we apply the tactic `injection h with hxy`. What
--  will happen?
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
--  `∀ (n m : Nat), n + 1 = m + 1 → n = m`. The converse of
--  this implication is an instance of a more general fact
--  about both constructors and functions:

example {α β : Type} (f : α → β) (x y : α)
    (h : x = y) : f x = f y := by
  rw [h]

example (n m : Nat) (h : n = m) :
    n + 1 = m + 1 := by
  rw [h]

--  Lean also provides `congr` as a tactic.

example (n m : Nat) (h : n = m) :
    n + 1 = m + 1 := by
  congr

--  We can specify the recursion-depth with `congr n`.

sf_expect_failure_in
  example (a b c d : Nat) (hab : a = b) (hcd : c = d) :
      (a, c + 1) = (b, 1 + d) := by
    congr

--  We now have three goals: `c = 1`, `1 = d`, and `1 = d`,
--  but these are not provable from our hypotheses! `congr`
--  has gone too deep.

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

--  ## Using `apply` on Hypotheses

--  The ordinary `apply` tactic is a form of "backward
--  reasoning." It says "We are trying to prove `a` and we
--  know `b → a`, so if we can prove `b` we'll be done."
--
--  By contrast, the variant `apply ... at ...` is "forward
--  reasoning": it says "We know `b` and we know `b → a`, so
--  we also know `a`."

example (n m p q : Nat)
    (h : n = m → p = q)
    (hnm : n = m) :
    p = q := by
  apply h at hnm
  exact hnm

--  You can apply tactics in multiple places at the same
--  time, including the goal:

example (n m : Nat) (h : n + 0 = m) : n = m + 0 := by
  rw [Nat.add_zero] at h ⊢
  assumption

--  ## Specializing Hypotheses

--  We've already seen how we can use `have` to do forward
--  reasoning, by letting us state and prove useful facts
--  that get us closer to the main goal we're trying to
--  prove. Often, though, these facts are just special cases
--  of more general hypotheses we already have.
--
--  If `h` is a quantified hypothesis in the current context
--  — i.e., `h : ∀ (x : α), P x` — then we can use `have` to
--  obtain a special case of `h` by supplying a value for
--  `x`. For example, `have h := h e` introduces a new `h`
--  which `x` has been instantiated with `e`.
--
--  For example:

example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  have h := h 1
  rw [Nat.mul_one] at h
  exact h

--  You may notice that, in the above proof, the original
--  `h` is still present in the context, although it is
--  shadowed by the new `h`. Often we don't care to keep
--  this old hypothesis around, and so we can use the
--  `replace` tactic instead. It behaves like `have`, except
--  that it gets rid of the old hypothesis afterwards when
--  possible:

example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  replace h := h 1
  rw [Nat.mul_one] at h
  exact h

--  Specializing a hypothesis in this way is common enough
--  that Lean provides the `specialize` tactic for it. For
--  example, `specialize h 1` is a more concise way of
--  writing `replace h := h 1`:

example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  specialize h 1
  rw [Nat.mul_one] at h
  exact h

--  Tactics like `have` and `replace` can also be used with
--  lemmas and theorems we've already proven, not just
--  things in our context. Using these tactis before `apply`
--  gives us yet another way to control where `apply` does
--  its work.

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

--  Recall this function for doubling a natural number from
--  the Induction chapter:

sf_recall
  def Nat.double (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | n' + 1 => double n' + 2

--  Suppose we want to show that `Nat.double` is injective
--  (i.e., it maps different arguments to different
--  results).

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

--  We get stuck, because the induction hypothesis `ih` is
--  too specific to be useful.

--  We can obtain a more generalized induction hypothesis by
--  writing
--
--      induction n generalizing m with

--  What went wrong?
--
--  Trying to carry out this proof by induction on `n` with
--  `m` fixed doesn't work, because we are then trying to
--  prove a statement involving *every* `n` but just a
--  *particular* `m`.

--  A successful proof of `double_injective` *generalizes*
--  `m` when carrying out the induction on `n`, so that the
--  induction hypothesis holds for every `m`, rather than
--  for just the particular `m` in the context.

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

--  The thing to take away from all this is that you need to
--  be careful, when using induction, that your induction
--  hypothesis is not too specific. When proving a
--  proposition quantified over variables `n` and `m` by
--  induction on `n`, it is sometimes crucial to
--  *generalize* `m`, so that the induction hypothesis
--  applies to every `m` rather than just the particular `m`
--  in the context.

--  ### Exercise (3 stars): add_self_injective ⭐⭐⭐

--  The following theorem follows the same pattern as
--  `double_injective`.

theorem add_self_injective (n m : Nat)
    (h : n + n = m + m) :
    n = m := by
  sorry

--  ### Exercise (2 stars): add_self_injective_informal ⭐⭐

--  Give a careful informal proof of `add_self_injective`,
--  stating the induction hypothesis explicitly and being as
--  explicit as possible about quantifiers, everywhere.

--  ## Rewriting with Conditional Statements

example (n m p q : Nat)
    (h : n.double = m.double)
    (hm : m + p = q) :
    n + p = q := by
  rw [double_injective n m]
  · assumption
  · assumption

--  If we rewrite with a conditional statement of the form
--  `P → a = b`, then Lean tries to rewrite with `a = b`,
--  and then asks us to prove `P` in a new subgoal. If the
--  statement has more than one assumption, then we get one
--  subgoal for each assumption.

--  ### Exercise (3 stars): length_append_cons (Optional) ⭐⭐⭐

--  Prove this by induction on `l₁`, without using
--  `List.length_append`.

theorem length_append_cons {α : Type} {l₁ l₂ : List α} {x : α} {n : Nat}
    (h : (l₁ ++ (x :: l₂)).length = n) :
    ((l₁ ++ l₂).length) + 1 = n := by
  sorry

--  ### Exercise (3 stars): length_append_self (Optional) ⭐⭐⭐

--  Prove this by induction on `l₁`, without using
--  `List.length_append`. Hint: you might need to use
--  `length_append_cons` you just proved.

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

--  Prove the following principle of induction over two
--  naturals.

theorem diagonal_induction (p : Nat → Nat → Prop)
    (hzz : p 0 0)
    (hsz : ∀ m, p m 0 → p (m + 1) 0)
    (hzs : ∀ n, p 0 n → p 0 (n + 1))
    (hss : ∀ m n, p m n → p (m + 1) (n + 1)) :
    ∀ m n, p m n := by
  sorry

--  ## Using `cases` on Expressions

--  The `cases` tactic can be used on expressions as well as
--  variables:

def chooseIf {α : Type} (test : α → Bool) (x y : α) : α :=
  if test x then x else y

theorem chooseIf_self {α : Type} (test : α → Bool) (x : α) :
    chooseIf test x x = x := by
  rw [chooseIf]
  cases test x <;> rfl

--  ### Destructing Tuples

--  `cases` is useful when we are dealing with inductively
--  defined types that can be one thing or another; a `Bool`
--  is either a `false` or a `true`, and a `Nat` is either
--  `0` or `succ n`. When we want more information about
--  inductively defined types that are products of multiple
--  things, we instead want a way to get the pieces of that
--  value out from it.
--
--  When we have a value `v : α × β` in our context, we can
--  get the first and second projections of `v` using this
--  tactic:
--
--      let ⟨a, β⟩ := v

--  ### Splitting with Equations

--  When using `cases`, we can specify to Lean that it
--  should remember an equality between a compound
--  expression and what we are decomposing it into, using
--  `cases h : ...` syntax. This information can actually be
--  critical, and, if we leave it out, we might lack
--  information we need to complete a proof.

def keepIf {α : Type} (test : α → Bool) (x : α) : Option α :=
  if test x then some x else none

--  Adding the `h : ⋯ ` qualifier saves this information so
--  we can use it.

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

-- Built on 2026-09-02 18:12 UTC

import LF.Poly
import LF.CustomTactics

import LF.SFLCompat

-- # Tactics: More Basic Tactics

-- This chapter introduces several additional proof strategies and tactics
-- that allow us to begin proving more interesting properties of functional
-- programs.

-- We will see:

-- - how to use auxiliary lemmas in both "forward-" and "backward-style" proofs;

-- - how to reason about data constructors -- in particular, how to use the fact
--   that they are injective and disjoint;

-- - how to strengthen an induction hypothesis, and when such strengthening is
--   required; and

-- - more details on how to reason by case analysis.

-- OA: added these to use Lean's Nat.

open Nat (add_comm add_assoc add_zero add_succ mul_one succ_sub_succ)

-- ## The `apply` Tactic

-- We often encounter situations where the goal to be proved is *exactly* the
-- same as some hypothesis in the context or some previously proved lemma.

theorem silly1 (n m : Nat) : n = m → n = m := by
  intro eq
  /- Here, we could finish with `rw [eq]` as we
    have done several times before.  Or we can finish
    by using `apply`: -/
  apply eq

-- The `apply` tactic also works with *conditional* hypotheses and lemmas: if
-- the statement being applied is an implication, then the premises of this
-- implication will be added to the list of subgoals needing to be proved.

theorem silly2 (n m o p : Nat) :
    n = m →
    (n = m → [n, o] = [m, p]) →
    [n, o] = [m, p] := by
  intro eq1 eq2
  apply eq2
  apply eq1

-- Typically, when we use `apply h`, the statement `h` will begin with a
-- `forall` that introduces some *universally quantified variables*.

-- When Lean matches the current goal against the conclusion of `h`, it will
-- try to find appropriate values for these variables. For example, when we do
-- `apply eq2` in the following proof, the universal variable `q` in `eq2`
-- gets instantiated with `n`, and `r` gets instantiated with `m`.

theorem silly2a (n m : Nat) :
    (n, n) = (m, m)  →
    (∀ (q r : Nat), (q, q) = (r, r) → [q] = [r]) →
    [n] = [m] := by
  intro eq1 eq2
  apply eq2
  apply eq1

-- ### Exercise (2 stars): silly_ex ⭐⭐

-- Complete the following proof using only `intros` and `apply`.

theorem silly_ex p :
    (∀ (n : Nat), n.even = true → (n + 1).even = false) →
    (∀ (n : Nat), n.even = false → n.odd = true) →
    p.even = true →
    (p + 1).odd = true := by
  sorry

-- To use the `apply` tactic, the (conclusion of the) fact being applied must
-- match the goal exactly (perhaps after simplification) -- for example,
-- `apply` will not work if the left and right sides of the equality are
-- swapped.

theorem silly3 (n m : Nat) :
    n = m →
    m = n := by
  intro H
  -- Here we cannot use `apply` directly...
  /- ...but we can use the `symm` tactic, which switches the left
      and right sides of an equality in the goal. -/
  symm; apply H

-- ### Exercise (2 stars): apply_exercise1 ⭐⭐

-- You can use `apply` with previously defined theorems, not just hypotheses
-- in the context. Use a previously-defined theorem about `rev` from Poly. Use
-- that theorem as part of your (relatively short) solution to this exercise.
-- You do not need `induction`.

theorem rev_exercise1 {α} (l l' : List α) :
    l = l'.rev →
    l' = l.rev := by
  intro eq
  rw [eq]; symm
  apply reverse_reverse
  -- /ADMITTED

-- ### Exercise (1 star): apply_rewrite (manually graded) ⭐

-- Briefly explain the difference between the tactics `apply` and `rw`. What
-- are the situations where both can usefully be applied?

-- ### Supplying arguments to `apply`

-- The following silly example uses two rewrites in a row to get from `\[a;b`]
-- to `\[e;f`].

theorem trans_eq_example (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  rw [eq1, eq2]

-- Since this is a common pattern, we might like to pull it out as a lemma
-- that records, once and for all, the fact that equality is transitive.

theorem trans_eq {α : Type} (x y z : α) :
    x = y → y = z → x = z := by
  intro eq1 eq2
  rw [eq1, eq2]

-- Nowwe **should** be able to use `trans_eq` to prove the above example.

-- But it doesn't *quite* work. If we simply tell Lean `apply
-- trans_eq` after
-- the `intro`, it can tell (by matching the goal against the conclusion of
-- the lemma) that it should instantiate `α` with `List Nat`, `x` with
-- `[a, b]`, and `z` with `[e,f]`. However, the matching process doesn't
-- determine an instantiation for `y`, nor does it know which hypothese to use
-- for the premises to `trans_eq`.

theorem trans_eq_example' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  apply trans_eq
  sorry
  sorry
  sorry

-- As we saw earlier, `apply` would generate new goals for these premises, and
-- we could finish the proof by explicitly applying these hypotheses to those
-- new goals. But we can also be more direct by supplying those hypotheses
-- directly to `apply`.

theorem trans_eq_example'' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  apply trans_eq [a, b] [c, d] [e, f] eq1 eq2

-- Note to developers (Daniel Sainati @dsainati1, NOW):
--     This and below are new (my addition), thoughts?

-- In the previous example, we had to specify the `x` and `z` arguments to
-- `trans_eq` before we could supply `[c, d]` for `y` or `eq1` and `eq2` for
-- the premises. However, we just said that Lean was able to infer these
-- arguments, so it's a bit redundant (and wordy) for us to do it. Thankfully,
-- Lean allows us to use `_`s for positional arguments that it can infer.

theorem trans_eq_example''' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  apply trans_eq _ _ _ eq1 eq2

-- Aside: if we know the name of the argument we are supplying (in this case
-- `y`), we can just name it directly and avoid typing any `_`s.

theorem trans_eq_example'''' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  apply trans_eq (y := [c, d])
  apply eq1
  apply eq2

-- Like any other kind of software, there are conventions and best practices
-- associated with writing proofs in Lean. One of these conventions concerns
-- the use of the `exact` tactic. When fully applying another theorem like in
-- the previous examples, it is considered good practice to use the `exact`
-- tactic instead of `apply`. This signals to a reader of the proof that the
-- proof is "exactly" an instance of another lemma, and that nothing of
-- particular interest is happening here. This achieves a similar goal as when
-- a mathematician says that one result is "just" an instance of another.

theorem trans_eq_example_exact (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  exact trans_eq _ _ _ eq1 eq2

-- Note to developers (Daniel Sainati @dsainati1, NOW):
--     if we decide we want to introduce `calc` earlier, we can remove this
--     explanation or tweak it. BCP: I think we did introduce it earlier...

-- Lean also has a built-in tactic `calc` that accomplishes the same purpose
-- as applying `trans_eq`. The tactic allows us to specify the in-between
-- states of any transitive relation. The notation is reminiscent of the
-- proofs you might see in a mathematics textbook.

theorem trans_eq_example''''' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  calc
  [a, b] = [c, d] := by rw [eq1]
  [c, d] = [e, f] := by rw [eq2]

-- ### Exercise (3 stars): trans_eq_exercise ⭐⭐⭐

theorem trans_eq_exercise (n m o p : Nat) :
    m = o.minustwo →
    (n + p) = m →
    (n + p) = o.minustwo := by
  sorry

-- ## The `injection` and `contradiction` Tactics

-- Recall the definition of natural numbers:

--   inductive Nat : Type :=
--     | zero
--     | succ (n : Nat).

-- It is obvious from this definition that every number has one of two forms:
-- either it is the constructor `0` or it is built by applying the constructor
-- `.succ` to another number. But there is more here than meets the eye:
-- implicit in the definition are two additional facts:

-- - The constructor `.succ` is *injective* (or *one-to-one*). That is, if
--   `n + 1 = m + 1`, it must also be that `n = m`.

-- - The constructors `0` and `.succ` are *disjoint*. That is, `0` is not equal
--   to `n + 1` for any `n`.

-- Similar principles apply to every inductively defined type: all
-- constructors are injective, and the values built from distinct constructors
-- are never equal. For lists, the `cons` constructor is injective and the
-- empty list `nil` is different from every non-empty list. For booleans,
-- `true` and `false` are different. (Since `true` and `false` take no
-- arguments, their injectivity is neither here nor there.) And so on.

-- SOON: FSR'25 - I wrote an explanation for `have` here, though I feel its
-- inclusion here breaks the flow.

-- Lean's `have` tactic, used above, adds the given hypothesis to the context,
-- but it first requires you to prove the hypothesis as a new goal.

-- This technique for injectivity can be generalized to any constructor by
-- writing the equivalent of `pred` -- i.e., writing a function that "undoes"
-- one application of the constructor.

-- As a convenient alternative, Lean provides a tactic called `injection` that
-- allows us to exploit the injectivity of any constructor. Here is an
-- alternate proof of the above theorem using `injection`:

theorem succ_injective' (n m : Nat) :
    n + 1 = m + 1 →
    n = m := by
  intro h
  injection h with hmn

-- By writing `injection h with hmn` at this point, we are asking Lean to
-- generate all equations that it can infer from `h` using the injectivity of
-- constructors (in the present example, the equation `n = m`). This equation
-- is added as a hypothesis (called `hmn` in this case) into the context.
-- Because this equation is exactly our goal, in this case the `injection`
-- tactic is able to automatically close the goal.

-- Here's a more interesting example that shows how `injection` can derive
-- multiple equations at once.

theorem injection_ex1 (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  all_goals
    injection h with h1 h2
    injection h2 with h3
    rw [h1, h3]

-- There is also a related tactic, `injections`, that applies the `injection`
-- tactic to all your hypotheses at once, as many times in a row as it can.
-- Using this tactic can avoid needing to repeatedly use `injection` on lists,
-- for example.

theorem injection_ex2 (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  all_goals
    injections h1 _ h3
    rw [h1, h3]

-- ### Exercise (3 stars): injection_ex3 ⭐⭐⭐

theorem injection_ex3 {α : Type} (x y z : α) (l j : List α) :
    x :: y :: l = z :: j →
    j = z :: l →
    x = y := by
  intro eq1 eq2
  injections hxz hyl_j
  have hyl_zl : y :: l = z :: l := by rw [hyl_j, eq2]
  injections hyz
  rw [hxz, hyz]

-- So much for injectivity of constructors. What about disjointness?

-- The principle of disjointness says that two terms beginning with different
-- constructors (like `0` and `succ`, or `true` and `false`) can never be
-- equal. This means that, any time we find ourselves in a context where we've
-- *assumed* that two such terms are equal, we are justified in concluding
-- anything we want, since the assumption is nonsensical.

-- The `contradiction` tactic, which we've already seen for handling cases
-- where we have assumed `False`, also embodies this principle: if we have a a
-- hypothesis involving an equality between different constructors (e.g.,
-- `false = true`), `contradiction` solves the current goal immediately. Some
-- examples:

theorem disjoint_ex1 (n m : Nat) :
    false = true →
    n = m := by
  intro contra
  contradiction

theorem disjoint_ex2 (n : Nat) :
    n + 1 = 0 →
    2 + 2 = 5 := by
  intro contra
  contradiction

-- These examples are instances of a logical principle known as the *principle
-- of explosion*, which asserts that a contradictory hypothesis entails
-- anything (even manifestly false things!).

-- If you find the principle of explosion confusing, remember that these
-- proofs are *not* simply showing that the conclusion of the statement holds.
-- Rather, they are showing that, *if* the nonsensical situation described by
-- the premise did somehow hold, *then* the nonsensical conclusion would hold
-- too (because we'd be living in an inconsistent universe where every
-- statement is true).

-- We'll explore the principle of explosion in more detail in the next
-- chapter.

-- ### Exercise (1 star): disjoint_ex3 ⭐

theorem disjoint_ex3 {α : Type} (x y z : α) (l : List α) :
    x :: y :: l = [] →
    x = z := by
  sorry

-- For a more useful example, we can use `contradiction` to make a connection
-- between the two different notions of equality (`=` and `==`) that we have
-- seen for natural numbers.

theorem beq_0_l (n : Nat) :
    (0 == n) = true →
    n = 0 := by
  intro h
  -- We can proceed by case analysis on `n`. The first case is trivial.
  cases n
  case zero => rfl
    -- However, the second one doesn't look so simple: assuming
    -- `(0 == n' + 1) = true`, we must show `n' + 1 = 0`!  The way forward
    -- is to observe that the assumption itself is nonsensical:
  case succ n' =>
    -- If we use `contradiction` here, Lean confirms that the subgoal
    -- we are working on is impossible and removes it from further
    -- consideration.
    contradiction

-- _Quiz:_

-- Recall our `RGB` and `Color` types:

-- inductive RGB : Type where | red | green | blue inductive Color : Type
-- where | black | white | primary (p: RGB)

-- Suppose Lean's proof state looks like

--   x : RGB
--   y : RGB
--   h : .primary x = .primary y

--   ⊢ y = x

-- and we apply the tactic `injection h with hxy`. What will happen?

-- (1) "No goals."

-- (2) The tactic fails.

-- (3) Hypothesis `h` becomes `hxy : x = y`.

-- (4) None of the above.

-- _Quiz:_

-- Suppose Lean's proof state looks like

--   x : Bool
--   y : Bool
--   h : !x = !y

--   ⊢ y = x

-- and we apply the tactic `injection h with hxy` What will happen?

-- (A) "No more goals."

-- (B) The tactic fails.

-- (C) Hypothesis `h` becomes `hxy : x = y`.

-- (D) None of the above.

-- _Quiz:_

-- Now suppose Lean's proof state looks like

--   x : Nat
--   y : Nat
--   h : x + 1 = y + 1

--   ⊢ y = x

-- and we apply the tactic `injection h with hxy`. What will happen?

-- (A) "No more goals."

-- (B) The tactic fails.

-- (C) Hypothesis `h` becomes `hxy : x = y`.

-- (D) None of the above.

-- _Quiz:_

-- Finally, suppose Lean's proof state looks like

--   x : Nat
--   y : Nat
--   h : 1 + x = 1 + y

--   ⊢ y = x

-- and we apply the tactic `injection h with hxy`. What will happen?

-- (A) "No more goals."

-- (B) The tactic fails.

-- (C) Hypothesis `h` becomes `hxy : x = y`.

-- (D) None of the above.

-- The injectivity of constructors allows us to reason that
-- `∀ (n m : Nat), n + 1 = m + 1 → n = m`. The converse of this implication is
-- an instance of a more general fact about both constructors and functions,
-- which we will find useful below:

theorem function_congruence {α β : Type} (f : α → β) (x y : α) :
    x = y → f x = f y := by
  intro eq
  rw [eq]

theorem eq_implies_succ_equal (n m : Nat) :
    n = m → n + 1 = m + 1 := by
  intro eq
  rw [eq]

-- Note to developers (Daniel Sainati @dsainati1, NOW):
--     can someone double check me on this? I think `congr` works this way but
--     I want to be sure

-- Indeed, there is also a tactic named `congr` that can prove such theorems
-- directly. Given a goal of the form `f a1 ... an = g b1 ... bn`, the tactic
-- `congr` will produce subgoals of the form `f = g`, `a1 = b1`, ...,
-- `an = bn`. At the same time, any of these subgoals that are simple enough
-- (e.g., immediately provable by `rfl`) will be automatically discharged.

theorem eq_implies_succ_equal' (n m : Nat) :
    n = m → n + 1 = m + 1 := by
  intro eq
  congr

-- Note to developers (Daniel Sainati @dsainati1, NOW):
--     how is this explanation of `congr`?

-- The `congr` tactic also accepts a numerical argument, which tells Lean how
-- deeply to decompose the goal. So, given a goal like
-- `((a, b), (c, d)) = ((e, f), (g, h))`, `congr 1` only applies `congr` once
-- to the goal, and would produce two subgoals: `(a, b) = (e, f)` and
-- `(c, d) = (g, h)`. `congr 2`, meanwhile, would apply `congr` again to both
-- these subgoals, and produce four subgoals: `a = e`, `b = f`, `c = g` and
-- `d = h`. Using `congr` without an argument always decomposes the goal as
-- deeply as possible.

-- Why does Lean provide this level of flexibility? Depending on what we are
-- trying to prove, deeper applications of `congr` may make our goal
-- unprovable. Consider this example:

example (a b c d : Nat) :
    a = b → c = d → (a, c + 1) = (b, 1 + d) := by
  intro eq1 eq2
  congr
  /- We now have three goals: `c = 1`, `1 = d`, and `1 = d`,
     but these are not provable from our hypotheses! `congr`
     has gone too deep. -/
  sorry
  sorry
  sorry

theorem eq_implies_succ_proj_equal (a b c d : Nat) :
    a = b → c = d → (a, c + 1) = (b, 1 + d) := by
  intro eq1 eq2
  /- Only shallowly using `congr` here allows us to complete the proof -/
  congr 1
  rw [add_comm]
  congr

-- ## Using Tactics on Hypotheses

-- By default, most tactics work on the goal formula and leave the context
-- unchanged. However, most tactics also have a variant that performs a
-- similar operation on a statement in the context.

-- For example, the tactic "`dsimp at H`" performs simplification on the
-- hypothesis `H` in the context.

theorem beq_succ (n m : Nat) : (n + 1 == m + 1) = (n == m) :=
  decide_eq_decide.mpr Nat.succ_inj

theorem succ_inj (n m : Nat) :
    n + 1 == m + 1 → n == m := by
  intro h
  rw [beq_succ] at h
  exact h

-- Similarly, `apply L at H` matches some conditional statement `L` (of the
-- form `X → Y`, say) against a hypothesis `H` in the context. However, unlike
-- ordinary `apply` (which rewrites a goal matching `Y` into a subgoal `X`),
-- `apply L at H` matches `H` against `X` and, if successful, replaces it with
-- `Y`.

-- In other words, `apply L at H` gives us a form of "forward reasoning":
-- given `X → Y` and a hypothesis matching `X`, it produces a hypothesis
-- matching `Y`.

-- By contrast, `apply L` is "backward reasoning": it says that if we know
-- `X → Y` and we are trying to prove `Y`, it suffices to prove `X`.

-- Here is a variant of a proof that uses forward reasoning throughout instead
-- of backward reasoning.

theorem silly4 (n m p q : Nat) :
    (n = m → p = q) →
    n = m →
    p = q := by
  intro eq1 eq2
  apply eq1 at eq2
  exact eq2

-- Forward reasoning starts from what is *given* (premises, previously proven
-- theorems) and iteratively draws conclusions from them until the goal is
-- reached. Backward reasoning starts from the *goal* and iteratively reasons
-- about what would imply the goal, until premises or previously proven
-- theorems are reached.

-- The informal proofs seen in math or computer science classes tend to use
-- forward reasoning. By contrast, idiomatic use of Lean generally favors
-- backward reasoning, though in some situations the forward style can be
-- easier to think about.

-- You may be interested to know that the `apply ... at ...` tactic is not
-- part of Lean's base set of tactics. However, Lean makes it very easy for
-- users to define new tactics that suit their particular proof style, and so
-- the developers of the popular Mathlib library defined the
-- `apply ... at ...` tactic to better enable forward reasoning. Mathlib is a
-- very large development, so we won't import the whole thing here, but we
-- have provided you `apply ... at ...` because it is quite useful.

-- To apply a tactic in multiple places at the same time, you can list
-- multiple hypotheses in a row after the `at`. You can also explicitly use a
-- tactic on the goal (usually because you are applying the tactic to both a
-- hypothesis and the goal) by including it after the `at` with the turnstile
-- symbol `⊢`, written `\|-`, `\goal` or `\vdash`.

example (n m : Nat) (h₁ : n = 1 + 1) (h₂ : m = 1 + 2) :
  Nat.ble (n, m).1 (n, m).2 := by
  dsimp at h₁ h₂ ⊢
  rw [h₁, h₂]
  rfl

-- ## Specializing Hypotheses

-- We've already seen how we can use `have` to do forward reasoning, by
-- letting us state and prove useful facts that get us closer to the main goal
-- we're trying to prove. Often, though, these facts are just special cases of
-- more general hypotheses we already have.

-- If `h` is a quantified hypothesis in the current context -- i.e.,
-- `h : forall (x : α), P` -- then `have h := h (x := e)` will change `h` so
-- that it looks like `P` with `x` replaced by `e`.

-- For example:

theorem have_example m :
    (∀ n, m * n = 0) → m = 0 := by
  intro h
  have h := h (n := 1)
  rw [mul_one] at h
  exact h

-- You may notice that, in the above proof, after using `have` we were left
-- with a leftover hypothesis in the context, the old `h`, so to speak. Often
-- we don't care to keep this old hypothesis around, and so we can use the
-- `replace` tactic instead. It behaves the same as `have`, except it gets rid
-- of the old hypothesis afterwards:

theorem replace_example m :
    (∀ n, m * n = 0) → m = 0 := by
  intro h
  replace h := h (n := 1)
  rw [mul_one] at h
  exact h

-- ### Exercise (3 stars): nth_error_always_none ⭐⭐⭐

-- Use `have` or `replace` to prove the the following lemma, following the
-- model of the examples above. Do not use `induction`.

theorem nth?_always_none (l : List Nat) :
    (∀ i, nth? l i = none) →
    l = [] := by
  sorry

-- Tactics like `have` and `replace` can also be used with lemmas and theorems
-- we've already proven, not just things in our context. Using these tactis
-- before `apply` gives us yet another way to control where `apply` does its
-- work.

theorem trans_eq_example'''''' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intros eq1 eq2
  have h := trans_eq (y:= [c, d])
  apply h
  /- This tactic closes a goal if it appears anywhere in the context.
     In this case we could also write `exact eq1` ... -/
  assumption
  /- .. and here we could also write `exact eq2` -/
  assumption

-- ## Varying the Induction Hypothesis

-- Sometimes it is important to control the exact form of the induction
-- hypothesis when carrying out inductive proofs in Lean. In particular, we
-- may need to be careful about which of the assumptions we move (using
-- `intro`) from the goal to the context before invoking the `induction`
-- tactic.

-- For example, suppose we want to show that `double` is injective -- i.e.,
-- that it maps different arguments to different results:

--   theorem double_injective: forall n m,
--     double n = double m →
--     n = m

-- The way we start this proof is a bit delicate: if we begin it with

--   intro n; induction n

-- then all will be well. But if we begin it with introducing *both* variables

--   intros n m; induction n

-- we get stuck in the middle of the inductive case...

example (n m : Nat) :
    n.double = m.double →
    n = m := by
  induction n
  case zero =>
    rw [Nat.double_zero]
    intro eq
    cases m
    case zero => rfl
    case succ _ => rw [Nat.double_succ] at eq; contradiction
  case succ n' ih =>
    intro eq
    cases m
    case zero => rw [Nat.double_zero, Nat.double_succ] at eq; contradiction
    case succ m' =>
      congr
      /- At this point, the induction hypothesis `ih` does _not_ give us
      `n' = m'` -- there is an extra `succ` in the way -- so the goal is
      not provable. -/
      sorry

-- What went wrong?

-- The problem is that, at the point where we invoke the induction hypothesis,
-- we have already introduced `m` into the context -- intuitively, we have
-- told Lean, "Let's consider some particular `n` and `m`..." and we now have
-- to prove that, if `double n = double m` for *these particular* `n` and `m`,
-- then `n = m`.

-- The next tactic, `induction n` says to Lean: We are going to show the goal
-- by induction on `n`. That is, we are going to prove, for *all* `n`, that
-- the proposition

-- - `P n` = "if `double n = double m`, then `n = m`"

-- holds, by showing

-- - `P 0`

--   (i.e., "if `double 0 = double m` then `0 = m`") and

-- - `P n → P (.succ n)`

--   (i.e., "if `double n = double m` then `n = m`" implies "if
--   `double (.succ n) = double m` then `.succ n = m`").

-- If we look closely at the second statement, it is saying something rather
-- strange: that, for a *particular* `m`, if we know

-- - "if `double n = double m` then `n = m`"

-- then we can prove

-- - "if `double (.succ n) = double m` then `.succ n = m`".

-- To see why this is strange, let's think of a particular `m` -- say, `5`.
-- The statement is then saying that, if we know

-- - `Q` = "if `double n = 10` then `n = 5`"

-- then we can prove

-- - `R` = "if `double (.succ n) = 10` then `.succ n = 5`".

-- But knowing `Q` doesn't give us any help at all with proving `R`! If we
-- tried to prove `R` from `Q`, we would start with something like "Suppose
-- `double (.succ n) = 10`..." but then we'd be stuck: knowing that
-- `double (.succ n)` is `10` tells us nothing helpful about whether
-- `double n` is `10` (indeed, it strongly suggests that `double n` is *not*
-- `10`!!), so `Q` is useless.

-- Trying to carry out this proof by induction on `n` when `m` is already in
-- the context doesn't work because we are then trying to prove a statement
-- involving *every* `n` but just a *particular* `m`.

-- A successful proof of `double_injective` keeps `m` universally quantified
-- in the goal statement at the point where the `induction` tactic is invoked
-- on `n`.

theorem double_injective : ∀ (n m : Nat),
    n.double = m.double →
    n = m := by
  intro n
  induction n
  case zero =>
    rw [Nat.double_zero]
    intro m eq
    cases m
    case zero => rfl
    case succ _ =>
      rw [Nat.double_succ] at eq
      contradiction
  case succ n' ih =>
  -- Notice that both the goal and the induction hypothesis are
  -- different this time: the goal asks us to prove something more
  -- general (i.e., we must prove the statement for _every_ `m`), but
  -- the induction hypothesis `ih` is correspondingly more flexible,
  -- allowing us to choose any `m` we like when we apply it.
  intro m eq
  -- Now we've introduced the assumption that `double n = double m`.
  -- Since we are doing a case analysis on `n`, we also need a case
  -- analysis on `m` to keep the two in sync.
  cases m
  case zero =>
    -- The 0 case is trivial:
    rw [Nat.double_zero, Nat.double_succ] at eq
    contradiction
  case succ m' =>
    congr
    -- Since we are now in the second branch of the `cases m`, the
    -- `m'` mentioned in the context is the predecessor of the `m` we
    -- started out talking about.  Since we are also in the `succ` branch of
    -- the induction, this is perfect: if we instantiate the generic `m`
    -- in the IH with the current `m'` (this instantiation is performed
    -- automatically by the `apply` in the next step), then `ih` gives
    -- us exactly what we need to finish the proof.
    apply ih; rw [Nat.double_succ, Nat.double_succ] at eq; injections

-- The thing to take away from all this is that you need to be careful, when
-- using induction, that you are not trying to prove something too specific:
-- When proving a property quantified over variables `n` and `m` by induction
-- on `n`, it is sometimes crucial to leave `m` "generic."

-- The following exercise, which further strengthens the link between `==` and
-- `=`, follows the same pattern.

theorem beq_eq : ∀ (n m : Nat),
    (n == m) = true → n = m := by
  sorry

-- ### Exercise (2 stars): beq_eq_informal ⭐⭐

-- Give a careful informal proof of `beq_eq`, stating the induction hypothesis
-- explicitly and being as explicit as possible about quantifiers, everywhere.

-- ### Exercise (3 stars): plus_n_n_injective ⭐⭐⭐

-- In addition to being careful about how you use `intro`, practice using "at"
-- variants in this proof. (Hint: use `plus_n_Sm`.)

theorem plus_n_n_injective : ∀ (n m : Nat),
    n + n = m + m →
    n = m := by
  sorry

-- The strategy of doing fewer `intros` before an `induction` to obtain a more
-- general IH doesn't always work; sometimes some *rearrangement* of
-- quantified variables is needed. Suppose, for example, that we wanted to
-- prove `double_injective` by induction on `m` instead of `n`.

theorem double_injective_take2_FAILED (n m : Nat) :
    n.double = m.double →
    n = m := by
  induction m
  case zero =>
    intro eq
    cases n
    case zero => rfl
    case succ =>
      rw [Nat.double_zero, Nat.double_succ] at eq
      contradiction
  case succ =>
    intro eq
    cases n
    case zero =>
      rw [Nat.double_zero, Nat.double_succ] at eq
      contradiction
    case succ =>
      congr
    -- We are stuck here, just like before.
      sorry

-- The problem is that, to do induction on `m`, we must first introduce `n`.

-- What can we do about this? One possibility is to rewrite the statement of
-- the lemma so that `m` is quantified before `n`. This works, but it's not
-- nice: We don't want to have to twist the statements of lemmas to fit the
-- needs of a particular strategy for proving them! Rather we want to state
-- them in the clearest and most natural way.

-- What we can do instead is to first introduce all the quantified variables
-- and then explicitly generalize one or more of them The `generalizing`
-- option for the `induction` tactic does this.

theorem double_injective_take2 (n m : Nat) :
    n.double = m.double →
    n = m := by
  intro eq
  -- `n` and `m` are both in the context
  -- This lets us do induction on `m` and get a sufficiently general IH
  induction m generalizing n
  case zero =>
    cases n
    case zero => rfl
    case succ =>
      rw [Nat.double_zero, Nat.double_succ] at eq
      contradiction
  case succ _ ih =>
    cases n
    case zero =>
      rw [Nat.double_zero, Nat.double_succ] at eq
      contradiction
    case succ =>
      congr
      rw [Nat.double_succ, Nat.double_succ] at eq
      injections _ eq; exact ih _ eq

-- Let's look at an informal proof of this theorem. Note that the proposition
-- we prove by induction leaves `n` quantified, corresponding to the use of
-- generalize dependent in our formal proof.

-- *Theorem*: For any nats `n` and `m`, if `double n = double m`, then
-- `n = m`.

-- *Proof*: Let `m` be a `Nat`. We prove by induction on `m` that, for any
-- `n`, if `double n = double m` then `n = m`.

-- - First, suppose `m = 0`, and suppose `n` is a number such that
--   `double n = double m`. We must show that `n = 0`.

--   Since `m = 0`, by the definition of `double` we have [double n = 0]. There
--   are two cases to consider for `n`. If `n = 0` we are done, since
--   `m = 0 = n`, as required. Otherwise, if `n = .succ n'` for some `n'`, we
--   derive a contradiction: by the definition of `double`, we can calculate
--   `double n = .succ (.succ (double n'))`, but this contradicts the assumption
--   that `double n = 0`.

-- - Second, suppose `m = .succ m'` and that `n` is again a number such that
--   `double n = double m`. We must show that `n = .succ m'`, with the induction
--   hypothesis that for every number `s`, if [double s = double m'] then
--   `s = m'`.

--   By the fact that `m = .succ m'` and the definition of `double`, we have
--   `double n = .succ (.succ (double m'))`. There are two cases to consider for
--   `n`.

--   If `n = 0`, then by definition `double n = 0`, a contradiction.

--   Thus, we may assume that `n = .succ n'` for some `n'`, and again by the
--   definition of `double` we have
--   `.succ (.succ (double n')) = .succ (.succ (double m'))`, which implies by
--   injectivity that `double n' = double m'`. Instantiating the induction
--   hypothesis with `n'` thus allows us to conclude that `n' = m'`, and it
--   follows immediately that `.succ n' = .succ m'`. Since `.succ n' = n` and
--   `.succ m' = m`, this is just what we wanted to show. []

-- ## Rewriting with Conditional Statements

-- We'll use a boolean "less or equal" test on numbers, written `n ≤? m` (the
-- library function `Nat.ble`), together with the fact that it commutes with
-- successor on both sides.

infix:52 " ≤? " => Nat.ble

theorem zero_ble (m : Nat) : (0 ≤? m) = true := rfl
theorem succ_ble_succ (n m : Nat) : ((n + 1) ≤? (m + 1)) = (n ≤? m) := rfl

-- Suppose that we want to show that `add` is the inverse of `sub`. Since we
-- are working with natural numbers, we need an assumption to prevent `sub`
-- from truncating its result. With this assumption, the induction hypothesis
-- becomes `forall m, n' ≤? m = true → (m - n') + n' = m`. The beginning of
-- the proof uses techniques we have already seen -- in particular, notice how
-- we induct on `n` before introducing `m`, so that the induction hypothesis
-- becomes sufficiently general.

theorem sub_add_ble : ∀ (n m : Nat),
    n ≤? m = true → (m - n) + n = m := by
  intro n
  induction n
  case zero =>
    intro m h; rw [add_zero]; cases m
    case zero => rfl
    case succ => rfl
  case succ n' ih =>
    intro m h; cases m
    case zero => contradiction
    case succ m' =>
      rw [succ_ble_succ] at h
      rw [succ_sub_succ, add_succ]
    -- At this point, we need to show `(m' - n') + n' + 1 = m' + 1`
    -- from the assumption `(n' <= m') = true`.  We could use the
    -- `have` tactic to prove `(m' - n') + n' = m'` from the IH.
    -- However, we can also just use `rw` directly...
      rw [ih]
      assumption

-- if we rewrite with a conditional statement of the form `P → a = b`, then
-- Lean tries to rewrite with `a = b`, and then asks us to prove `P` in a new
-- subgoal. If the statement has more than one assumption, then we get one
-- subgoal for each assumption.

-- ### Exercise (3 stars): gen_dep_practice ⭐⭐⭐

-- Prove this by induction on `l`.

theorem nth_error_after_last {α : Type} (n : Nat) (l : List α) :
    l.length = n →
    nth? l n = none := by
  sorry

-- ## Using `cases` on Compound Expressions

-- We have seen many examples where `cases` is used to perform case analysis
-- of the value of some variable. Sometimes we need to reason by cases on the
-- result of some *expression*. We can also do this with `cases`.

-- Here are some examples:

def sillyfun (n : Nat) : Bool :=
  if n == 3 then false
  else if n == 5 then false
  else false

theorem sillyfun_false (n : Nat) :
    sillyfun n = false := by
  unfold sillyfun
  cases (n == 3)
  case false =>
    dsimp; cases (n == 5)
    case false => rfl
    case true => rfl
  case true => rfl

-- After unfolding `sillyfun` in the above proof, we find that we are stuck on
-- `if (n == 3) then ... else ...`. But either `n` is equal to `3` or it
-- isn't, so we can use `cases (n == 3)` to let us reason about the two cases.

-- In general, the `cases` tactic can be used to perform case analysis of the
-- results of arbitrary computations. If `e` is an expression whose type is
-- some inductively defined type `T`, then, for each constructor `c` of `T`,
-- `cases e` generates a subgoal in which all occurrences of `e` (in the goal
-- and in the context) are replaced by `c`.

-- ### Destructing Tuples

-- `cases` is useful when we are dealing with inductively defined types that
-- can be one thing or another; a `Bool` is either a `false` or a `true`, and
-- a `Nat` is either `0` or `succ n`. When we want more information about
-- inductively defined types that are products of multiple things, we instead
-- want a way to get the pieces of that value out from it.

-- When we have a value `v : α × β` in our context, we can get the first and
-- second projections of `v` using this tactic:

--   let ⟨a, β⟩ := v

-- ### Exercise (3 stars): combine_split ⭐⭐⭐

-- Here is an implementation of the `unzip` function mentioned in chapter
-- Poly. We'll call it `split` so as not to confuse Lean.

def split {α β : Type} (l : List (α × β)) : (List α) × (List β) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)

-- Prove that `split` and `zip` are inverses in the following sense:

theorem split_zip {α β : Type} (l : List (α × β)) l1 l2 :
    split l = (l1, l2) →
    zip l1 l2 = l := by
  sorry

-- For example, suppose we define a function `sillyfun1` like this:

def sillyfun1 (n : Nat) : Bool :=
  if n == 3 then true
  else if n == 5 then true
  else false

-- Now suppose that we want to convince Lean that `sillyfun1 n` yields `true`
-- only when `n` is odd. If we start the proof like this (with no `h:` on the
-- `cases`)...

example (n : Nat) :
    sillyfun1 n = true →
    n.odd = true := by
  intro eq
  unfold sillyfun1 at eq
  cases (n == 3)
  case false => sorry
  case true => sorry

-- ... then we are stuck at this point because the context does not contain
-- enough information to prove the goal! Because `n == 3` appears in our
-- hypothesis, rather than in our goal, `cases (n == 3)` does not
-- automatically replace the expression with `false` or `true` like it did
-- during the proof of `sillyfun_false`. We want to add an equation to the
-- context that records which case we are in. This is precisely what the `h:`
-- qualifier does.

theorem sillyfun1_odd (n : Nat) :
    sillyfun1 n = true →
    n.odd = true := by
  intro eq
  unfold sillyfun1 at eq
  cases h : (n == 3)
  case false =>
    -- Now we have the same state as at the point where we got stuck
    -- above, except that the context contains an extra equality
    -- assumption, which is exactly what we need to make progress.
    rw [h] at eq; dsimp at eq
    cases h': (n == 5)
    case false =>
      rw [h'] at eq; dsimp at eq
      contradiction
    case true =>
      apply beq_eq at h'
      rw [h']; rfl
      -- When we come to the second equality test in the body
      -- of the function we are reasoning about, we can use
      -- `h:` again in the same way, allowing us to finish the
      -- proof.
  case true =>
    apply beq_eq at h
    rw [h]; rfl

-- ### Exercise (2 stars): destruct_eqn_practice ⭐⭐

theorem bool_fn_applied_thrice (f : Bool → Bool) (b : Bool) :
    f (f (f b)) = f b := by
  sorry

-- ## Review

-- We've now talked about many of Lean's most fundamental tactics. We'll
-- introduce a few more in the coming chapters, and later on we'll see some
-- more powerful *automation* tactics that make Lean help us with low-level
-- details. But basically we've got what we need to get work done.

-- Here are the ones we've seen:

-- - `intro`: move hypotheses/variables from goal to context

-- - `rfl`: finish the proof (when the goal looks like [e = e])

-- - `apply`: prove goal using a hypothesis, lemma, or constructor

-- - `apply... at H`: apply a hypothesis, lemma, or constructor to a hypothesis
--   in the context (forward reasoning)

-- - `apply... with...`: explicitly specify values for variables that cannot be
--   determined by pattern matching

-- - `replace h (x:= ...)`: refine a hypothesis by fixing some of its variables

-- - `dsimp`: simplify computations in the goal

-- - `dsimp at H`: ... or a hypothesis

-- - `rw`: use an equality hypothesis (or lemma) to rewrite the goal

-- - `rw ... at H`: ... or a hypothesis

-- - `symm`: changes a goal of the form `t=u` into `u=t`

-- - `symm at H`: changes a hypothesis of the form `t=u` into `u=t`

-- - `calc`: prove a goal about a transitive relation via a number of
--   intermediate steps

-- - `unfold`: replace a defined constant by its right-hand side in the goal

-- - `unfold... at H`: ... or a hypothesis

-- - `cases ...`: case analysis on values of inductively defined types

-- - `cases h:...`: specify the name of an equation to be added to the context,
--   recording the result of the case analysis

-- - `induction ...`: induction on values of inductively defined types

-- - `induction ... generalizing ...`: hold some variables general while doing
--   induction

-- - `injection ... with ...`: reason by injectivity on an equality between
--   values of inductively defined types

-- - `injections ... `: reason by injectivity on all the equalities in the
--   context

-- - `contradiction`: conclude a proof when there's a false hypothesis in the
--   context

-- - `have h : e := ... ` : introduce a "local lemma" `e` and call it `h`

-- - `congr`: change a goal of the form `f x = f y` into `x = y`

-- Additional Exercises

-- ### Exercise (3 stars): beq_symm ⭐⭐⭐

theorem beq_symm (n m : Nat) :
    (n == m) = (m == n) := by
  induction n generalizing m
  case zero =>
    cases m
    case zero => rfl
    case succ => rfl
  case succ n' ih =>
    cases m
    case zero => rfl
    case succ =>
      rw [beq_succ, beq_succ]
      exact ih _

-- ### Exercise (3 stars): beq_symm_informal ⭐⭐⭐

-- Give an informal proof of this lemma that corresponds to your formal proof
-- above:

-- Theorem: For any `Nat`s `n` `m`, `(n == m) = (m == n)`.

-- Proof:

-- ### Exercise (3 stars): beq_trans ⭐⭐⭐

theorem beq_trans (n m p : Nat) :
    (n == m) = true →
    (m == p) = true →
    (n == p) = true := by
  sorry

-- ### Exercise (3 stars): split_combine (Advanced, manually graded) ⭐⭐⭐

-- We proved, in an exercise above, that `combine` is the inverse of `split`.
-- Complete the definition of `split_combine_statement` below with a property
-- that states that `split` is the inverse of `combine`. Then, prove that the
-- property holds.

-- Hint: Take a look at the definition of `combine` in Poly. Your property
-- will need to account for the behavior of `combine` in its base cases, which
-- possibly drop some list elements.

def split_combine_statement : Prop :=
  /- ("`: Prop`" means that we are giving a name to a
     logical proposition here.) -/
  ∀ (α β : Type) (l1 : List α) (l2 : List β),
    l1.length = l2.length →
    split (zip l1 l2) = (l1, l2)

theorem split_combine : split_combine_statement := by
  sorry
-- FILL IN HERE

-- ### Exercise (3 stars): filter_exercise (Advanced) ⭐⭐⭐

theorem filter_exercise {α : Type} (test : α → Bool) (a : α) (l lf : List α) :
    filter test l = a :: lf →
    test a = true := by
  sorry

-- ### Exercise (4 stars): forall_exists_challenge (Advanced) ⭐⭐⭐⭐

-- Define two recursive `Fixpoints`, `forallb` and `existsb`. The first checks
-- whether every element in a list satisfies a given predicate:

--   forallb Nat.odd [1,3,5,7,9] = true
--   forallb negb [false,false] = true
--   forallb Nat.even [0,2,4,5] = false
--   forallb (beq 5) [] = true

-- The second checks whether there exists an element in the list that
-- satisfies a given predicate:

--   existsb (beq 5) [0,2,3,6] = false
--   existsb (andb true) [true,true,false] = true
--   existsb Nat.odd [1,0,0,0,0,3] = true
--   existsb even [] = false

-- Next, define a *nonrecursive* version of `existsb` -- call it `existsb'` --
-- using `forallb` and `negb`.

-- Finally, prove a theorem `existsb_existsb'` stating that `existsb'` and
-- `existsb` have the same behavior.

def forallb {α : Type} (test : α → Bool) (l : List α) : Bool := sorry

example : forallb (Nat.odd) [1,3,5,7,9] = true := sorry
example : forallb not [false,false] = true := sorry
example : forallb (Nat.even) [0,2,4,5] = false := sorry
example : forallb (· == 5) [] = true := sorry

def existsb {α : Type} (test : α → Bool) (l : List α) : Bool := sorry

example : existsb (· == 5) [0,2,3,6] = false := sorry
example : existsb (· && true) [true,true,false] = true := sorry
example : existsb (Nat.odd) [1,0,0,0,0,3] = true := sorry
example : existsb (Nat.even) ([] : List Nat) = false := sorry

def existsb' {α : Type} (test : α → Bool) (l : List α) : Bool := sorry

theorem existsb_existsb' (α : Type) (test : α → Bool) (l : List α) :
    existsb test l = existsb' test l := by
  sorry


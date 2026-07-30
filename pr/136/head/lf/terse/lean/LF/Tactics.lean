import LF.Poly
import LF.CustomTactics

import LF.SFLCompat

-- # Tactics: More Basic Tactics

-- Note to developers (Daniel Sainati  @dsainati1):
--     [BCP: Old comment -- might be out of date?] There is a
--     section here on unfolding definitions that should
--     probably move earlier, to `Basics` or `Induction`, once
--     those chapters are rewritten to not use arithmetic. This
--     will also require changing the examples.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     (Old and possibly out of date -- check!) Many exercises
--     in this chapter are based on defining and proving
--     properties about Nat.ble and BEq.eq, which are not
--     idiomatic in Lean. We should consider replacing these
--     with a different set of exercises.

-- Note to developers (before next release):
--     This chapter could maybe use one or two more WORKINCLASS
--     tags...

-- Note to developers (Benjamin Pierce  @bcpierce00, before next release, 2025):
--     General comment: All the previous chapters have felt
--     pretty smooth. This one suddenly feels like we're
--     throwing a huge amount of information at them, with
--     little scaffolding -- just a bunch of miscellaneous
--     tactics and examples. Wish it flowed better, somehow.

-- OA: added these to use Lean's Nat.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     Deserves a comment. (In general, the reader should be
--     given enough information to understand every line in the
--     files we give them. This will not always be possible,
--     but when it is not we should mark it explicitly.)

open Nat (add_comm add_assoc add_zero add_succ mul_one succ_sub_succ)

-- ## The `apply` Tactic

-- The `apply` tactic is useful when some hypothesis or an
-- earlier lemma exactly matches the goal:

theorem silly1 (n m : Nat) : n = m → n = m := by
  intro eq
  /- Here, we could finish with `rw [eq]` as we
    have done several times before.  Or we can finish
    by using `apply`: -/
  apply eq

-- `apply` also works with *conditional* hypotheses:

theorem silly2 (n m o p : Nat) :
    n = m →
    (n = m → [n, o] = [m, p]) →
    [n, o] = [m, p] := by
  intro eq1 eq2
  apply eq2
  apply eq1

-- Observe how Lean picks appropriate values for the
-- `forall`-quantified variables of the hypothesis:

theorem silly2a (n m : Nat) :
    (n, n) = (m, m)  →
    (∀ (q r : Nat), (q, q) = (r, r) → [q] = [r]) →
    [n] = [m] := by
  intro eq1 eq2
  apply eq2
  apply eq1

-- The goal must match the hypothesis *exactly* for `apply` to
-- work:

theorem silly3 (n m : Nat) :
    n = m →
    m = n := by
  intro H
  -- Here we cannot use `apply` directly...
  /- ...but we can use the `symm` tactic, which switches the left
      and right sides of an equality in the goal. -/
  symm; apply H

-- ### Supplying arguments to `apply`

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     This note is probably dead...
--
--     AAA dislikes the `...with...` variants of tactics, which
--     he feels don't work very well. But we (Arthur and BCP)
--     decided to leave things alone for now, since removing
--     `...with...` would require changing MANY proofs.

-- The following silly example uses two rewrites in a row to
-- get from `\[a;b`] to `\[e;f`].

theorem trans_eq_example (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  rw [eq1, eq2]

-- Since this is a common pattern, we might like to pull it out
-- as a lemma that records, once and for all, the fact that
-- equality is transitive.

-- Note to developers:
--     `HIDE: Robert Rand: I found using m, n and o throughout this discussion
--     super confusing -- m doesn't come between n and o! Rocq's eq_trans uses
--     x, y and z, which is what I wanted to change this too anyhow.`

theorem trans_eq {α : Type} (x y z : α) :
    x = y → y = z → x = z := by
  intro eq1 eq2
  rw [eq1, eq2]

-- Nowwe **should** be able to use `trans_eq` to prove the
-- above example.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `Is this still true?
--
--     Robert Rand: This one makes a nice workinclass. You can show
--     the various ways around the problem, including named "with",
--     unnamed "with", and (if you desire), explicitly providing the
--     arguments to trans_eq.`

-- But doing `apply trans_eq` doesn't finish the proof!

theorem trans_eq_example' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  apply trans_eq
  sorry
  sorry
  sorry

-- This does:

theorem trans_eq_example'' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  apply trans_eq [a, b] [c, d] [e, f] eq1 eq2

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     This and below are new (my addition), thoughts?

-- In the previous example, we had to specify the `x` and `z`
-- arguments to `trans_eq` before we could supply `[c, d]` for
-- `y` or `eq1` and `eq2` for the premises. However, we just
-- said that Lean was able to infer these arguments, so it's a
-- bit redundant (and wordy) for us to do it. Thankfully, Lean
-- allows us to use `_`s for positional arguments that it can
-- infer.

theorem trans_eq_example''' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  apply trans_eq _ _ _ eq1 eq2

-- Aside: if we know the name of the argument we are supplying
-- (in this case `y`), we can just name it directly and avoid
-- typing any `_`s.

theorem trans_eq_example'''' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  apply trans_eq (y := [c, d])
  apply eq1
  apply eq2

-- By convention, we use `exact` for situations when we can
-- completely finish the proof with a single application

theorem trans_eq_example_exact (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  exact trans_eq _ _ _ eq1 eq2

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     if we decide we want to introduce `calc` earlier, we can
--     remove this explanation or tweak it. BCP: I think we did
--     introduce it earlier...

-- `calc` is also available as a tactic.

theorem trans_eq_example''''' (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro eq1 eq2
  calc
  [a, b] = [c, d] := by rw [eq1]
  [c, d] = [e, f] := by rw [eq2]

-- ## The `injection` and `contradiction` Tactics

-- The constructors of inductive types are *injective* (or
-- *one-to-one*) and *disjoint*.

-- E.g., for `Nat`...

-- - if `n + 1 = m + 1` then it must be that `n = m`
-- - `0` is not equal to `n + 1` for any `n`

-- We can *prove* the injectivity of `succ` by using the `pred`
-- function

theorem succ_injective (n m : Nat) :
    n + 1 = m + 1 →
    n = m := by
  intros h1
  have h2 : n = Nat.pred (n + 1) := by rfl
  rewrite [h2, h1]
  rfl

-- SOON: FSR'25 - I wrote an explanation for `have` here,
-- though I feel its inclusion here breaks the flow.

-- As a convenience, the `injection` tactic allows us to
-- exploit injectivity of any constructor (not just `succ`).

theorem succ_injective' (n m : Nat) :
    n + 1 = m + 1 →
    n = m := by
  intro h
  injection h with hmn

-- Here's a more interesting example that shows how `injection`
-- can derive multiple equations at once.

theorem injection_ex1 (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  sorry

-- There is also a related tactic, `injections`, that applies
-- the `injection` tactic to all your hypotheses at once, as
-- many times in a row as it can. Using this tactic can avoid
-- needing to repeatedly use `injection` on lists, for example.

theorem injection_ex2 (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  sorry

-- So much for injectivity of constructors. What about
-- disjointness?

-- Two terms beginning with different constructors (like `0`
-- and `succ`, or `true` and `false`) can never be equal!

-- The `contradiction` tactic, which we've already seen for
-- handling cases where we have assumed `False`, also embodies
-- this principle: if we have a a hypothesis involving an
-- equality between different constructors (e.g.,
-- `false = true`), `contradiction` solves the current goal
-- immediately. Some examples:

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

-- These examples are instances of a logical principle known as
-- the *principle of explosion*, which asserts that a
-- contradictory hypothesis entails anything (even manifestly
-- false things!).

-- For a more useful example, we can use `contradiction` to
-- make a connection between the two different notions of
-- equality (`=` and `==`) that we have seen for natural
-- numbers.

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

-- Note to developers:
--     HIDE: APT: Could add an advanced exercise asking them to
--     show somthing like `true = false → 0 = 1` using
--     `rewrite` and a function definition and using
--     `discriminate`. BCP: This might be nice, but not sure
--     this is a critical point to make.
--
--     HIDE: "There should be more discussion and practice with
--     how to deal with subexpressions that do not allow
--     application of hypotheses, for example how to deal with
--     the `.succ m` in `m + (.succ m)`. Again, I sort of
--     understand what to do with `destruct` and induction, but
--     it would help to have more exercises that break down the
--     process of making this connection." BCP 9/18: Not sure
--     exactly what to add, but if anybody has good ideas...
--
--     HIDE: This relies on the fact that `injection` only
--     works with constructors. Should this be discussed
--     earlier? Or is this the right place to mention it
--     briefly? BCP 20: I think here is OK, though a longer
--     explanation (including a remark on why you would not
--     want this in general!) would be welcome...
--
--     HIDE: Robert Rand: I think it's nice to start them off
--     with a easy question and also to use more datatypes than
--     Nat and Bool.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     All these quizzes (here and elsewhere) need to be
--     checked!

-- _Quiz:_

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     In Rocq, there was a line of = signs between premises
--     and conclusion. They've gotten lost here. There are
--     probably more instances of this elsewhere!

-- Recall our `RGB` and `Color` types:

-- inductive RGB : Type where | red | green | blue inductive
-- Color : Type where | black | white | primary (p: RGB)

-- Suppose Lean's proof state looks like

--   x : RGB
--   y : RGB
--   h : .primary x = .primary y

--   ⊢ y = x

-- and we apply the tactic `injection h with hxy`. What will
-- happen?

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

-- and we apply the tactic `injection h with hxy` What will
-- happen?

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

-- and we apply the tactic `injection h with hxy`. What will
-- happen?

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

-- and we apply the tactic `injection h with hxy`. What will
-- happen?

-- (A) "No more goals."

-- (B) The tactic fails.

-- (C) Hypothesis `h` becomes `hxy : x = y`.

-- (D) None of the above.

-- Note to developers:
--     HIDE: BCP 9/16: Not sure this theorem is pulling its
--     weight in SF! It's used relatively few places, and there
--     is nothing too interesting to say about it here --
--     indeed it kind of disrupts the flow. BCP 9/18: I
--     actually found it useful several times in the lecture on
--     this chapter, so I think it's best to leave it.

-- The injectivity of constructors allows us to reason that
-- `∀ (n m : Nat), n + 1 = m + 1 → n = m`. The converse of this
-- implication is an instance of a more general fact about both
-- constructors and functions, which we will find useful below:

theorem function_congruence {α β : Type} (f : α → β) (x y : α) :
    x = y → f x = f y := by
  intro eq
  rw [eq]

theorem eq_implies_succ_equal (n m : Nat) :
    n = m → n + 1 = m + 1 := by
  intro eq
  rw [eq]

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     can someone double check me on this? I think `congr`
--     works this way but I want to be sure

-- Lean also provides `congr` as a tactic.

theorem eq_implies_succ_equal' (n m : Nat) :
    n = m → n + 1 = m + 1 := by
  intro eq
  congr

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     how is this explanation of `congr`?

-- We can specify the recursion-depth with `congr n`.

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

-- Many tactics come with "`... at ...`" variants that work on
-- hypotheses instead of goals.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     This is surely NOT the right way to prove this fact, and
--     I'm not sure that proving it here is what we want to do
--     anyway. Inserting it for now for expediency, to get this
--     file closer to compiling...

-- Note to developers (Claude):
--     NB `rfl` does not prove this: in this chapter `==` on
--     `Nat` elaborates via the generic decidable-equality
--     instance (`n == m` is `decide (n = m)`), and `decide` is
--     stuck on variables. So we reduce to propositional
--     injectivity.

theorem beq_succ (n m : Nat) : (n + 1 == m + 1) = (n == m) :=
  decide_eq_decide.mpr Nat.succ_inj

theorem succ_inj (n m : Nat) :
    n + 1 == m + 1 → n == m := by
  intro h
  rw [beq_succ] at h
  exact h

-- The ordinary `apply` tactic is a form of "backward
-- reasoning." It says "We're trying to prove `X` and we know
-- `Y → X`, so if we can prove `Y` we'll be done."

-- By contrast, the variant `apply... at...` is "forward
-- reasoning": it says "We know `Y` and we know `Y → X`, so we
-- also know `X`."

-- Note to developers:
--     HIDE: Robert Rand: I find the behavior of `apply in` to
--     be hideous. If I have H1 : A and H2: A → B, I don't want
--     to change H1 to B (leaving me with an entirely redundant
--     H2), I want to change H2 to B, leaving me with H1 : A,
--     H2 : B. I tend to point this out and show that
--     `specialize (EQ H)` gives us what we want. This makes
--     for a nice segue to the next section.

theorem silly4 (n m p q : Nat) :
    (n = m → p = q) →
    n = m →
    p = q := by
  intro eq1 eq2
  apply eq1 at eq2
  exact eq2

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     this part has been changed from the original Rocq, let
--     me know what you think

-- ## Specializing Hypotheses

-- We've already seen how we can use `have` to do forward
-- reasoning, by letting us state and prove useful facts that
-- get us closer to the main goal we're trying to prove. Often,
-- though, these facts are just special cases of more general
-- hypotheses we already have.

-- If `h` is a quantified hypothesis in the current context --
-- i.e., `h : forall (x : α), P` -- then `have h := h (x := e)`
-- will change `h` so that it looks like `P` with `x` replaced
-- by `e`.

-- For example:

-- Note to developers:
--     HIDE: Robert Rand: I found this very useful because not
--     all students realize I can get a specific case from the
--     forall in the hypotheses. I've shortened the proof a
--     bit. BCP: Maybe this comment is dead?

theorem have_example m :
    (∀ n, m * n = 0) → m = 0 := by
  intro h
  have h := h (n := 1)
  rw [mul_one] at h
  exact h

-- You may notice that, in the above proof, after using `have`
-- we were left with a leftover hypothesis in the context, the
-- old `h`, so to speak. Often we don't care to keep this old
-- hypothesis around, and so we can use the `replace` tactic
-- instead. It behaves the same as `have`, except it gets rid
-- of the old hypothesis afterwards:

theorem replace_example m :
    (∀ n, m * n = 0) → m = 0 := by
  intro h
  replace h := h (n := 1)
  rw [mul_one] at h
  exact h

-- Tactics like `have` and `replace` can also be used with
-- lemmas and theorems we've already proven, not just things in
-- our context. Using these tactis before `apply` gives us yet
-- another way to control where `apply` does its work.

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

-- Recall this function for doubling a natural number from the
-- Induction chapter:

-- def double (n : Nat) : Nat := match n with | 0 => 0 | .succ
-- n' => (double n') + 2

-- Suppose we want to show that `double` is injective (i.e., it
-- maps different arguments to different results). The way we
-- *start* this proof is a little bit delicate:

example (n m : Nat) :
    n.double = m.double →
    n = m := by
  induction n
  case zero =>
    rw [double_zero]
    intro eq
    cases m
    case zero => rfl
    case succ _ => rw [double_succ] at eq; contradiction
  case succ n' ih =>
    intro eq
    cases m
    case zero => rw [double_zero, double_succ] at eq; contradiction
    case succ m' =>
      congr
      /- At this point, the induction hypothesis `ih` does _not_ give us
      `n' = m'` -- there is an extra `succ` in the way -- so the goal is
      not provable. -/
      sorry

-- What went wrong?

-- Trying to carry out this proof by induction on `n` when `m`
-- is already in the context doesn't work because we are then
-- trying to prove a statement involving *every* `n` but just a
-- *particular* `m`.

-- A successful proof of `double_injective` keeps `m`
-- universally quantified in the goal statement at the point
-- where the `induction` tactic is invoked on `n`.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     The comments in this proof might need trimming --
--     probably not appropriate in the terse version, and
--     probably not nicely typeset in the full version

theorem double_injective : ∀ (n m : Nat),
    n.double = m.double →
    n = m := by
  intro n
  induction n
  case zero =>
    rw [double_zero]
    intro m eq
    cases m
    case zero => rfl
    case succ _ =>
      rw [double_succ] at eq
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
    rw [double_zero, double_succ] at eq
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
    apply ih; rw [double_succ, double_succ] at eq; injections

-- Note to developers:
--     `HIDE: Robert Rand: I found jumping straight to "what if we want to
--     do induction on the second argument" via double_injective_take2_FAILED
--     to be much more natural here.`

-- The thing to take away from all this is that you need to be
-- careful, when using induction, that you are not trying to
-- prove something too specific: When proving a property
-- quantified over variables `n` and `m` by induction on `n`,
-- it is sometimes crucial to leave `m` "generic."

-- The following theorem, which further strengthens the link
-- between `==` and `=`, follows the same pattern.

theorem beq_eq : ∀ (n m : Nat),
    (n == m) = true → n = m := by
  sorry

-- The strategy of doing fewer `intros` before an `induction`
-- to obtain a more general IH doesn't always work; sometimes
-- some *rearrangement* of quantified variables is needed.
-- Suppose, for example, that we wanted to prove
-- `double_injective` by induction on `m` instead of `n`.

theorem double_injective_take2_FAILED (n m : Nat) :
    n.double = m.double →
    n = m := by
  induction m
  case zero =>
    intro eq
    cases n
    case zero => rfl
    case succ =>
      rw [double_zero, double_succ] at eq
      contradiction
  case succ =>
    intro eq
    cases n
    case zero =>
      rw [double_zero, double_succ] at eq
      contradiction
    case succ =>
      congr
    -- We are stuck here, just like before.
      sorry

-- The problem is that, to do induction on `m`, we must first
-- introduce `n`.

-- What we can do instead is to first introduce all the
-- quantified variables and then explicitly generalize one or
-- more of them The `generalizing` option for the `induction`
-- tactic does this.

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
      rw [double_zero, double_succ] at eq
      contradiction
  case succ _ ih =>
    cases n
    case zero =>
      rw [double_zero, double_succ] at eq
      contradiction
    case succ =>
      congr
      rw [double_succ, double_succ] at eq
      injections _ eq; exact ih _ eq

-- ## Rewriting with Conditional Statements

-- We'll use a boolean "less or equal" test on numbers, written
-- `n ≤? m` (the library function `Nat.ble`), together with the
-- fact that it commutes with successor on both sides.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     Added, to make the file compile, on Claude's suggestion.
--     But is this the right way? Answer: No, just replaces
--     uses of it by Nat.ble!

infix:52 " ≤? " => Nat.ble

theorem zero_ble (m : Nat) : (0 ≤? m) = true := rfl
theorem succ_ble_succ (n m : Nat) : ((n + 1) ≤? (m + 1)) = (n ≤? m) := rfl

-- Note to developers (Claude, before next release):
--     Claude-generated note. (BCP: Whoever reviews this part
--     of the chapter next should read and delete it.)
--
--     The `leb_*` → `ble_*` rename is now applied across
--     `Lists`, `Tactics`, and `Logic`, matching the
--     `ble_complete` / `ble_correct` / `ble_iff` names already
--     used in `IndProp`: every one of these is stated over
--     `≤?`, which is notation for `Nat.ble` (declared just
--     above), so the name now tracks the function. Statements
--     keep the `≤?` notation rather than spelling out
--     `Nat.ble`, following `IndProp`.
--
--     One thing to think about: `beq_succ` (above, and used in
--     `Logic`) is a separate `BEq` question: it could likewise
--     be restated via `Nat.beq_eq_true_eq` / `BEq.comm`, which
--     would let the `beq_symm` exercise below drop its
--     induction. Worth a decision, but it changes an
--     exercise's shape, not just a name.

-- Suppose that we want to show that `add` is the inverse of
-- `sub`. Since we are working with natural numbers, we need an
-- assumption to prevent `sub` from truncating its result. With
-- this assumption, the induction hypothesis becomes
-- `forall m, n' ≤? m = true → (m - n') + n' = m`. The
-- beginning of the proof uses techniques we have already seen
-- -- in particular, notice how we induct on `n` before
-- introducing `m`, so that the induction hypothesis becomes
-- sufficiently general.

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

-- ## Using `cases` on Compound Expressions

-- Note to developers:
--     HIDE: CH: If eqn is only useful for compound expressions
--     and those are only discussed here, why has eqn been
--     introduced before this point? It seems that so far its
--     only use was for documentation, and while one might
--     argue that it's good practice to always use eqn, that's
--     not the case, as illustrated by its disappearance in
--     Logics. BCP '19: Fixed Logic.v -- I do think it's good
--     documentation!

-- The `cases` tactic can be used on expressions as well as
-- variables:

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

-- ### Destructing Tuples

-- `cases` is useful when we are dealing with inductively
-- defined types that can be one thing or another; a `Bool` is
-- either a `false` or a `true`, and a `Nat` is either `0` or
-- `succ n`. When we want more information about inductively
-- defined types that are products of multiple things, we
-- instead want a way to get the pieces of that value out from
-- it.

-- When we have a value `v : α × β` in our context, we can get
-- the first and second projections of `v` using this tactic:

--   let ⟨a, β⟩ := v

-- When using `cases`, we can specify to Lean that it should
-- remember an equality between a compound expression and what
-- we are decomposing it into, using `cases h: ...` syntax.
-- This information can actually be critical, and, if we leave
-- it out, we might lack information we need to complete a
-- proof.

def sillyfun1 (n : Nat) : Bool :=
  if n == 3 then true
  else if n == 5 then true
  else false

example (n : Nat) :
    sillyfun1 n = true →
    n.odd = true := by
  intro eq
  unfold sillyfun1 at eq
  cases (n == 3)
  case false => sorry
  case true => sorry

-- Adding the `h:` qualifier saves this information so we can
-- use it.

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

-- Micro Sermon

-- Mindless proof-hacking is a terrible temptation...

-- Try to resist!


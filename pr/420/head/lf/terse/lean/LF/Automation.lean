import LF.IndProp

import SFLCompat

--  # Automation: More Automation

--  Consider the proof below. Notice all the repetition and
--  near-repetition...

theorem Perm3_In_old (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm with
  | swap12 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . right; left; assumption
    . left; assumption
    . right; right; left; assumption
    . contradiction
  | swap23 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . left; assumption
    . right; right; left; assumption
    . right; left; assumption
    . contradiction
  | trans _ _ ih₁₂ ih₂₃ =>
    apply ih₂₃; apply ih₁₂; apply hIn

--  In this chapter, we will introduce tactics that will
--  shrink this proof from around eighteen lines to one.

--  ## The `lia` Tactic

example (m n o p : Nat) :
    m + n ≤ n + o ∧ o + 3 = p + 3 →
    m ≤ p := by
  lia

example (m n : Nat) :
    m + n = n + m := by
  lia

example (m n p : Nat) :
    m + (n + p) = m + n + p := by
  lia

example (a b c d : Prop) :
    (a → b) → (b → c) → (c → d) → (a → d) := by
  lia

example (α : Type) (x : α) (l₁ l₂ l₃ : List α)
  (h₁ : x ∈ l₁ → x ∈ l₂) (h₂ : x ∈ l₂ → x ∈ l₃) : x ∈ l₁ → x ∈ l₃ := by
  lia

--  The `lia` tactic can solve many of the cases of our old
--  `Perm3.In` example.

theorem Perm3_In_better_with_lia (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm with
  | swap12 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    /- In addition to basic arithmetic, `lia` can also discharge goals
      that are simple facts about logic. -/
    . lia -- was right; left; assumption
    . lia -- was left; assumption
    . lia -- was right; right; left; assumption
    . lia -- was contradiction
  | swap23 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . lia -- was left; assumption
    . lia -- was right; right; left; assumption
    . lia -- was right; right; assumption
    . lia -- was contradiction
  | trans _ _ ih₁₂ ih₂₃ =>
    lia -- was apply ih₂₃; apply ih₁₂; apply hIn

--  ## Tactic Combinators

--  Recall the `<;>` combinator...

example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl

--  We can use this combinator to further simplify our
--  `Perm3` proof:

theorem Perm3_In_better_with_lia_semi (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm with
  | swap12 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
  | swap23 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
  | trans _ _ ih₁₂ ih₂₃ => lia

--  ### The `try` Combinator

--  The `try` combinator swallows a tactic's failure.

example {a : Prop} (h : a) : a := by
  try rfl -- `rfl` would fail here, but `try` swallows it...
  exact h -- ...so we can still finish some other way.

example : 1 = 1 := by
  try rfl -- here `try rfl` just does `rfl`

inductive Silly : Nat → Prop where
| mk1 n (h : n > 1) : Silly n
| mk2 n (h : 1 ∈ []) : Silly n
| mk3 n (h : ∃ m, n = m + 2) : Silly n

example {n} (h : Silly n) : n ≠ 1 := by
  inversion h with
  | mk1 => lia
  | mk2 => contradiction
  | mk3 => lia

--  The `try` and `<;>` combinators used together allow you
--  to apply a tactic to some, but not all, goals...

example {n} (h : Silly n) : n ≠ 1 := by
  cases h <;> try lia
  -- `lia` doesn't know that `1 ∈ []` is impossible,
  -- but we can use `contradiction`
  contradiction

--  We can further simplify our `Perm3.In` example with
--  `try`.

theorem Perm3_In_better_with_try (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm with (try rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia)
  | trans => lia

--  Note that `try lia <;> try rw [...] <;> lia` *doesn't*
--  work, because the first time that `try` catches a
--  failure in a `<;>` sequence, the whole sequence will
--  stop executing.

sf_expect_failure_in
  example (α : Type) (x : α) (l₁ l₂ : List α)
      (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
    induction hPerm <;> try lia <;>
      try rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia

--  Output:
--    unsolved goals
--    case swap12
--    α : Type
--    x : α
--    l₁ l₂ : List α
--    x✝ y✝ z✝ : α
--    hIn : x ∈ [x✝, y✝, z✝]
--    ⊢ x ∈ [y✝, x✝, z✝]
--
--    case swap23
--    α : Type
--    x : α
--    l₁ l₂ : List α
--    x✝ y✝ z✝ : α
--    hIn : x ∈ [x✝, y✝, z✝]
--    ⊢ x ∈ [x✝, z✝, y✝]

--  ### The `repeat` Combinator

--  The `repeat` combinator takes another tactic or
--  parenthesized sequence of tactics and keeps applying it
--  until it fails.
--
--  Here is an example proving that `10` is in a long list
--  using `repeat`:

example : 10 ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  repeat
    rw [List.mem_cons]
    try left; rfl
    -- `try` makes this optional, which is necessary for the
    -- last repetition where `left; rfl` succeeds
    try right

--  The `repeat` combinator can loop forever.

sf_expect_failure_in
  example (m n : Nat) : m + n = n + m := by
    /- Uncomment the next line to see the infinite loop occur.  You will
       then need to recomment it to make Lean listen to you again. -/
    -- repeat rewrite [Nat.add_comm]

--  ### The `first` Combinator

--  The `first` combinator applies the first successful
--  tactic in a list:

example (n m : Nat) : n * (m + 1) = n * m + n := by
  first | rfl | left | lia | induction n

--  We can combine `first` with `repeat`:

example : 10 ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  repeat first
    | exact List.mem_cons_self
    | apply List.mem_cons_of_mem

--  With `first`, we can solve the earlier issue with `try`
--  where it would stop executing the sequence on the first
--  failure.

theorem Perm3_In_better_with_first (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm <;>
    first
    | rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
    | lia

--  Our `Perm3.In` example is now quite short! Can we still
--  do better?

--  ## The `simp` Tactic

--  The `simp` tactic is Lean's *simplifier*. It is one of
--  the most powerful tools in the language, and it is used
--  heavily in real Lean developments.
--
--  The tactic simplifies the target (the goal and/or one or
--  more hypotheses) by repeatedly rewriting it using a set
--  of lemmas.
--
--  The `simp` tactic's available set of lemmas begins with
--  a default set and can be extended to include theorems
--  labeled `@[simp]`. Indeed, the characterizing lemmas
--  we've been using for rewriting are good ones to give to
--  `simp`, which is why they are also called
--  *simplification lemmas*.

namespace simp_lemmas_example

/- `add_zero` and `add_succ` are the `simp` lemmas for `+`. -/
@[simp]
theorem add_zero (n : Nat) : n + 0 = n := by rfl

@[simp]
theorem add_succ (n m : Nat) : n + (m + 1) = (n + m) + 1 := by rfl

--  Instead of manually rewriting by the characterizing
--  lemmas in the example below, `simp` does it
--  automatically.

theorem add_succ_nested (n m : Nat) :
    n + (m + 1 + 1) = (n + m + 1) + 1 := by
  simp

--  Writing `simp only` applies `simp` with only the
--  provided theorems:

theorem add_succ_nested_2 (n m : Nat) :
    n + (m + 1 + 1) = (n + m + 1) + 1 := by
  simp only [add_succ, add_zero]

--  If you want to know what `simp` is doing, you can run
--  `simp?`.

theorem add_succ_nested_3 (n m : Nat) :
    n + (m + 1 + 1) = (n + m + 1) + 1 := by
  simp?

end simp_lemmas_example

--  In the InfoView, you will see

--  Output:
--    Try this:
--      [apply] simp only [add_succ, Nat.add_zero, Nat.add_left_cancel_iff]

--  The `simp ... at ...` tactic simplifies in a hypothesis.

example α x (l₁ l₂ l₃ : List α)
    (h₁ : x ∈ l₁ ++ l₂)
    (h₂ : x ∈ l₂ ++ l₃) :
    x ∈ l₁ ++ l₃ ∨ x ∈ l₂ := by
  simp at h₁; simp at h₂; simp; lia

--  We could equally well have written

example α x (l₁ l₂ l₃ : List α)
    (h₁ : x ∈ l₁ ++ l₂)
    (h₂ : x ∈ l₂ ++ l₃) :
    x ∈ l₁ ++ l₃ ∨ x ∈ l₂ := by
  simp at *; lia

--  If we want to *mutually* simplify everywhere, we can use
--  `simp_all`, which simplifies in all hypotheses and in
--  the goal at the same time.
--
--  Here's an example that illustrates the difference:

sf_expect_failure_in
  example (a b : Nat) (h1 : a = 0) (h2 : a + b = 5) : b = 5 := by
    simp at *

--  This fails with:

--  Output:
--    `simp` made no progress

--  But `simp_all` closes the goal:

example (a b : Nat) (h1 : a = 0) (h2 : a + b = 5) : b = 5 := by
  simp_all

--  We can dramatically simplify our `Perm3_In_shortest`
--  theorem using `simp_all`:

theorem Perm3_In_shortest (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm <;> simp_all <;> lia

--  ### Idiomatic `simp` Usage

--  Don't use `simp` without `only` unless you're closing a
--  goal or following with a flexible tactic. The example
--  below breaks this rule:

example α x (l₁ l₂ l₃ : List α)
    (h₁ : x ∈ l₁ ++ l₂)
    (h₂ : x ∈ l₂ ++ l₃) :
    x ∈ l₁ ++ l₃ ∨ x ∈ l₂ := by
  simp at h₁; simp at h₂; simp
  cases h₁ with
  | inl h => left; left; exact h
  | inr h => right; exact h

--  This usage of `simp` is brittle and can break due to
--  upstream changes.
--
--  We can fix the style of this proof by changing the
--  `simp`s to specify which theorems they are using to
--  simplify:

example α x (l₁ l₂ l₃ : List α)
    (h₁ : x ∈ l₁ ++ l₂)
    (h₂ : x ∈ l₂ ++ l₃) :
    x ∈ l₁ ++ l₃ ∨ x ∈ l₂ := by
  -- the * here targets all hypotheses and the goal
  simp only [List.mem_append] at *
  cases h₁ with
  | inl h => left; left; exact h
  | inr h => right; exact h

--  Another rule around proper `simp` usage applies to the
--  appropriate definition of `simp` lemmas.
--
--  Appropriately defined `simp` lemmas simplify left to
--  right.

--  ## The `trivial` Tactic

--  A final automated tactic to have in your toolkit is
--  `trivial`, which tries a number of different simple
--  tactics (such as `rfl` or `contradiction`) to close the
--  current goal. Some examples:

example : 1 = 1 := by trivial
example : (1, 2).fst = 1 := by trivial
example (a b : Prop) : ¬ a → a → b := by intro h₁ h₂; trivial

--  ## Case Study: Regular Expressions

--  ### Definitions

inductive RegExp (α : Type) : Type where
  | EmptySet
  | EmptyStr
  | Char (c : α)
  | App (r1 r2 : RegExp α)
  | Union (r1 r2 : RegExp α)
  | Star (r : RegExp α)
deriving BEq, DecidableEq, Repr

attribute [pp_nodot] RegExp.Char RegExp.App RegExp.Union RegExp.Star

namespace RegExp

--  Note that this definition is *polymorphic*: regular
--  expressions in `RegExp α` describe strings with
--  characters drawn from `α` — which in this exercise we
--  represent as *lists* with elements from `α`.

--  We connect regular expressions and strings by defining
--  when a regular expression *matches* some string.

--  Informally, this looks as follows:
--  - The regular expression `EmptySet` does not match any
--    string.
--
--  - `EmptyStr` matches the empty string `[]`.
--
--  - `Char x` matches the one-character string `[x]`.
--
--  - If `re₁` matches `s₁`, and `re₂` matches `s₂`, then
--    `App re₁ re₂` matches `s₁ ++ s₂`.
--
--  - If at least one of `re₁` and `re₂` matches `s`, then
--    `Union re₁ re₂` matches `s`.
--
--  - Finally, if we can write some string `s` as the
--    concatenation of a sequence of strings
--    `s = s₁ ++ ... ++ sₖ`, and the expression `re` matches
--    each one of the strings `sᵢ`, then `Star re` matches
--    `s`.
--
--    In particular, the sequence of strings may be empty,
--    so `Star re` always matches the empty string `[]` no
--    matter what `re` is.
--
--  We can easily translate this intuition into a set of
--  rules, where we write `s =~ re` to say that `re` matches
--  `s`:
--
--              ─────────────── (mEmpty)
--              [] =~ EmptyStr
--
--              ─────────────── (mChar)
--              [x] =~ (Char x)
--
--          s₁ =~ re₁     s₂ =~ re₂
--        ─────────────────────────── (mApp)
--        (s₁ ++ s₂) =~ (App re₁ re₂)
--
--                 s₁ =~ re₁
--          ───────────────────── (mUnionL)
--          s₁ =~ (Union re₁ re₂)
--
--                 s₂ =~ re₂
--          ───────────────────── (mUnionR)
--          s₂ =~ (Union re₁ re₂)
--
--            ──────────────── (mStar0)
--            [] =~ (Star re)
--
--      s₁ =~ re     s₂ =~ (Star re)
--      ──────────────────────────── (mStarApp)
--        (s₁ ++ s₂) =~ (Star re)
--
--  This directly corresponds to the following inductive
--  definition:

inductive ExpMatch {α : Type} : List α → RegExp α → Prop where
  | mEmpty : ExpMatch [] EmptyStr
  | mChar (c : α) : ExpMatch [c] (Char c)
  | mApp (s₁ s₂ : List α) {re₁ re₂ : RegExp α}
         (h₁ : ExpMatch s₁ re₁) (h₂ : ExpMatch s₂ re₂)
       : ExpMatch (s₁ ++ s₂) (App re₁ re₂)
  | mUnionL (s₁ : List α) {re₁ re₂ : RegExp α}
            (h₁ : ExpMatch s₁ re₁) : ExpMatch s₁ (Union re₁ re₂)
  | mUnionR (s₂ : List α) {re₁ re₂ : RegExp α}
            (h₂ : ExpMatch s₂ re₂) : ExpMatch s₂ (Union re₁ re₂)
  | mStar0 (re : RegExp α) : ExpMatch [] (Star re)
  | mStarApp (s₁ s₂ : List α) {re : RegExp α}
             (h₁ : ExpMatch s₁ re) (h₂ : ExpMatch s₂ (Star re))
           : ExpMatch (s₁ ++ s₂) (Star re)
open ExpMatch

infix:40 " =~ " => ExpMatch

--   ----------------------------------------

--  _Quiz:_

--  Notice that this clause in our informal definition...

--  "The expression `EmptySet` does not match any string."

--  ... is not explicitly reflected in the above definition.
--  Do we need to add something?
--
--  (A) Yes, we should add a rule for this.
--
--  (B) No, one of the other rules already covers this case.
--
--  (C) No, the *lack* of a rule actually gives us the
--  behavior we want.

--   ----------------------------------------

--  ### Examples

example : [1] =~ Char 1 := by
  apply mChar

example : [1, 2] =~ App (Char 1) (Char 2) := by
  apply mApp [1] <;> constructor

example : ¬([1, 2] =~ Char 1) := by
  intro contra; inversion contra

--  We can define helper functions for writing down regular
--  expressions. The `reg_exp_of_list` function constructs a
--  regular expression that matches exactly the string that
--  it receives as an argument:

def reg_exp_of_list {α} (l : List α) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')

example : [1, 2, 3] =~ reg_exp_of_list [1, 2, 3] := by
  apply mApp [1]; constructor
  apply mApp [2]; constructor
  apply mApp [3]; constructor
  constructor

--  Something more interesting:

theorem MStar1 α s (re : RegExp α) (h : s =~ re) : s =~ Star re := by
  sorry

--  The following lemmas show that the intuition about
--  matching given at the beginning of the section can be
--  obtained from the formal inductive definition.
--
--  The next lemma is stated in terms of the `List.foldr`
--  function on lists: if `ss : List (List α)` represents a
--  sequence of strings `s₁, ..., sₙ`, then
--  `List.foldr (· ++ ·) [] ss` is the result of
--  concatenating them all together.
--
--  Naturally, proofs about `ExpMatch` often require
--  induction (on evidence!).
--
--  For example, suppose we want to prove the following
--  intuitive fact: if a string `s` is matched by a regular
--  expression `re`, then all elements of `s` must occur as
--  character literals somewhere in `re`.
--
--  To state this as a theorem, we first define a function
--  `reChars` that lists all characters that occur in a
--  regular expression:

def reChars {α : Type} (re : RegExp α) : List α :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re₁ re₂ => reChars re₁ ++ reChars re₂
  | Union re₁ re₂ => reChars re₁ ++ reChars re₂
  | Star re => reChars re

--  Now, the main theorem:

theorem in_re_match {α : Type} {s : List α} {re : RegExp α} {x : α}
    (hmatch : s =~ re) (hin : x ∈ s) : x ∈ reChars re := by
  induction hmatch with
  | mEmpty => simp at hin
  | mChar c => simp only [reChars]; assumption
  | mApp _ _ _ _ ih₁ ih₂ =>
  /- Something interesting happens in the `mApp` case.  We obtain
    _two_ induction hypotheses: one that applies when `x` occurs in
    `s₁` (which is matched by `re₁`), and a second one that applies
    when `x` occurs in `s₂` (matched by `re₂`). -/
    sorry
  | mUnionL _ _ ih =>
    simp only [reChars, List.mem_append]; left; exact ih hin
  | mUnionR _ _ ih =>
    simp only [reChars, List.mem_append]; right; exact ih hin
  | mStar0 => simp at hin
  | mStarApp _ _ _ _ ih₁ ih₂ =>
  /- Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for `ExpMatch`, rather than
    induction on the regular expression `re`: the latter would only
    provide an induction hypothesis for strings that match `re`, which
    would not allow us to reason about the case `x ∈ s₂`. -/
    sorry

--  ### The `generalize` Tactic

--  One potentially confusing feature of the `induction`
--  tactic is that it won't let you perform an induction
--  over a term that isn't sufficiently general. Here's an
--  example:

sf_expect_failure_in
  example (α : Type) (s₁ s₂ : List α) (re : RegExp α) :
      s₁ =~ Star re →
      s₂ =~ Star re →
      s₁ ++ s₂ =~ Star re := by
    intro h₁
    /- Now, just doing an `inversion` on `h₁` won't get us very far in
      the recursive cases. (Try it!) So we need induction (on
      evidence). We might try this, but Lean won't let us: -/
    induction h₁

--  Output:
--    Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
--      Star re

--  The problem here is that `induction` over a `Prop`
--  hypothesis only works properly with hypotheses that are
--  "fully general," i.e., ones in which all the arguments
--  are just variables, as opposed to more specific
--  expressions like `Star re`.
--
--  A possible, but awkward, way to solve this problem is
--  "manually generalizing" over the problematic expressions
--  by adding explicit equality hypotheses to the lemma:

sf_expect_failure_in
  example α (s₁ s₂ : List α) (re re' : RegExp α) :
      re' = Star re →
      s₁ =~ re' →
      s₂ =~ Star re →
      s₁ ++ s₂ =~ Star re := by
    intro h₁ h₂ h₃
    /- We can now proceed by performing induction over evidence
      directly, because the argument to the first hypothesis is
      sufficiently general, which means that we can discharge most cases
      by inverting the `re' = Star re` equality in the context. -/
    induction h₂
    /- This works, but it makes the statement of the lemma a bit ugly.
      Fortunately, there is a better way... -/

--  The tactic `generalize h : e = x` causes Lean to (1)
--  replace all occurrences of the expression `e` by the
--  variable `x`, and (2) add an equation `h : e = x` to the
--  context. Here's how we can use it to show the above
--  result:

theorem star_app α (s₁ s₂ : List α) (re : RegExp α) :
    s₁ =~ Star re →
    s₂ =~ Star re →
    s₁ ++ s₂ =~ Star re := by
  intro h₁
  generalize heq : Star re = re' at h₁
  /- We now have `heq : Star re = re'`;
    `heq` is contradictory in most cases, allowing us to conclude immediately via `contradiction`. -/
  induction h₁ <;> try contradiction
  -- The interesting cases are those that correspond to `Star`.
  case mStar0 _ => intro h₂; simp only [List.nil_append]; exact h₂
  case mStarApp _ _ _ _ _ _ ih₂ =>
    injections heq; subst heq
    intro h₂; simp only [List.append_assoc]
    apply mStarApp
    . assumption
    . apply ih₂ <;> trivial
  /- Note that the induction hypothesis `ih₂` on the `mStarApp` case
    mentions an additional premise `Star re'' = Star re`, which
    results from the equality generated by `generalize`. -/

--  Do not confuse `generalize` with the `generalizing`
--  clause on `induction` introduced in the Tactics chapter.
--  The `generalizing` clause would not help us here —
--  `induction` on `s₁ =~ Star re` would still fail because
--  `Star re` is a compound expression, not a bare variable.

--  ### The "Weak" Pumping Lemma

--  One of the first really interesting theorems in the
--  theory of regular expressions is the so-called *pumping
--  lemma*, which states, informally, that any sufficiently
--  long string `s` matching a regular expression `re` can
--  be "pumped" by repeating some middle section of `s` an
--  arbitrary number of times to produce a new string also
--  matching `re`. For the sake of simplicity, this exercise
--  considers a slightly weaker theorem than is usually
--  stated in courses on automata theory — hence the name
--  `weak_pumping`. The stronger one can be found below.
--
--  To get started, we need to define "sufficiently long."
--  Since we are working in a constructive logic, we
--  actually need to be able to *calculate*, for each
--  regular expression `re`, a minimum length for strings
--  `s` to guarantee "pumpability."

def pumpingConstant {α : Type} (re : RegExp α) : Nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re₁ re₂ => re₁.pumpingConstant + re₂.pumpingConstant
  | Union re₁ re₂ => re₁.pumpingConstant + re₂.pumpingConstant
  | Star r => r.pumpingConstant

--  You may find these lemmas about the pumping constant
--  useful when proving the pumping lemma below.

theorem pumping_constant_ge_1 {α : Type} (re : RegExp α) :
    re.pumpingConstant ≥ 1 := by
  induction re with (simp_all [pumpingConstant]; try lia)

theorem pumping_constant_0_false {α : Type} (re : RegExp α)
    (h : re.pumpingConstant = 0) : False := by
  have := pumping_constant_ge_1 re; lia

--  Next, it is useful to define an auxiliary function that
--  repeats a string (appends it to itself) some number of
--  times. Note how we define `simp` lemmas for `napp` to go
--  with its definition.

def napp {α : Type} (n : Nat) (l : List α) : List α :=
  match n with
  | 0 => []
  | n' + 1 => l ++ napp n' l

@[simp]
theorem napp_zero {α : Type} (l : List α) : napp 0 l = [] := by rfl

@[simp]
theorem napp_succ {α : Type} (n : Nat) (l : List α) : napp (n + 1) l = l ++ napp n l := by rfl

--  These auxiliary lemmas might also be useful in your
--  proof of the pumping lemma.

@[simp]
theorem napp_plus {α : Type} (n m : Nat) (l : List α) :
    napp (n + m) l = napp n l ++ napp m l := by
  induction n with simp_all [Nat.succ_add]

theorem napp_star {α : Type} (m : Nat) (s₁ s₂ : List α) (re : RegExp α)
    (hs₁ : s₁ =~ re) (hs₂ : s₂ =~ Star re) :
    napp m s₁ ++ s₂ =~ Star re := by
  induction m with
  | zero => simp only [napp_zero, List.nil_append]; trivial
  | succ m ih =>
    simp only [napp_succ]
    rw [List.append_assoc]
    apply mStarApp <;> trivial

--  The (weak) pumping lemma itself says that, if `s =~ re`
--  and if the length of `s` is at least the pumping
--  constant of `re`, then `s` can be split into three
--  substrings `s₁ ++ s₂ ++ s₃` in such a way that `s₂` can
--  be repeated any number of times and the result, when
--  combined with `s₁` and `s₃`, will still match `re`.
--  Since `s₂` is also guaranteed not to be the empty
--  string, this gives us a (constructive!) way to generate
--  strings matching `re` that are as long as we like.
--
--  This proof is quite long, so to make it more tractable
--  we've broken it up into a number of subproofs, which we
--  then assemble to prove the main lemma.
--
--  Your job is to complete the proofs of the helper lemmas;
--  the main lemma relies on these.

--  ### The "Strong" Pumping Lemma

end RegExp

--  ### Palindromes Revisited

-- Source revision: 682a4d8, committed 2026-09-23 12:50 UTC

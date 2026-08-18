import LF.Basics
import LF.Induction

import LF.SFLCompat

-- # UsingLean: Using the Full Power of a Proof Assistant

-- ## More Powerful Natural Numbers

-- Until now, we have been working with our own custom natural numbers, using
-- the `Nat` type that we defined in Basics.

-- However, Lean has a built-in type of natural numbers, which is more
-- powerful and comes with many useful features. They are very slightly
-- different from our custom `Nat`, but these differences are mostly
-- superficial. The built-in natural numbers are defined in the `Init` module,
-- which is automatically imported by Lean. We will refer to them as `Nat` as
-- well, but they are not the same as the `Nat` we defined in Basics.

-- In Lean, programmers and mathematicians don't re-prove the basic properties
-- of natural numbers from scratch, nor do they tend to write out `rewrite`
-- steps for basic properties of natural numbers by hand.

-- Previously, we did computation like this...

open NatPlayground.Nat in
example : (two * two : NatPlayground.Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  rewrite [mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_zero]
  rfl

-- Note to developers (Benjamin Pierce @bcpierce00, NOW):
--     The info viewed in the InfoView during this proof is kind of mysterious
--     (to me) here. Have we already given people enough help to understand it
--     here?

-- This approach is useful in a textbook for understanding the structure of
-- natural numbers and for providing early practice with writing proofs. But
-- it is also tedious in the long term.

-- Instead of doing this, programmers and mathematicians use the built-in
-- `Nat` and the powerful features of Lean to *automatically* prove properties
-- about natural numbers and to compute with them.

example : (3 * 3 : Nat) = 9 := by rfl

-- The annotation `: Nat` tells Lean that we are using its built-in `Nat`
-- type.

-- In this chapter we will learn how to use the built-in `Nat` and some
-- powerful features for computing with and proving properties about natural
-- numbers. Specifically, we will learn about `dsimp`, `calc`, and `simp`
-- annotations, which enable more powerful and concise proofs.

-- In fact, from now on, we will use the built-in `Nat` type and its powerful
-- features, writing `Nat.<theorem>` to reference Lean's version of
-- `<theorem>`. (By convention, theorems about a type live in the namespace of
-- that type, hence the need for the `Nat.` prefix.)

-- ### `rfl` and Computation with `Nat`

-- With Lean's `Nat`, much of the computation happens automatically, and `rfl`
-- suffices to close any equality of computation on literals.

example : (2 * 3 + 4 * 5 : Nat) * 6 = 156 := by
  rfl

-- This quickly becomes necessary, as natural numbers quickly get large!

-- Of course, `rfl` can't close more complicated goals where the values of the
-- terms are unknown.

example (n m : Nat) (h : n = m) : n = m := by
  -- `rfl` will not work here!
  -- First rewrite the goal with `h`; then the two sides are identical.
  rewrite [h]
  rfl

-- The same proof can be written more compactly with `rw`. In this example,
-- `rw [h]` rewrites with `h` and then closes the resulting reflexive goal.

example (n m : Nat) (h : n = m) : n = m := by
  rw [h]

-- We will continue to show more powerful tools for manipulating the context
-- and goal of a proof to bring them closer to what can be solved with `rfl`.

-- ## Using the Standard Library

-- As part of using Lean's standard `Nat` type, we will also begin using
-- theorems about `Nat`s from the standard library. Because we did not write
-- or prove these theorems ourselves, however, we may not know all the
-- available theorems off the top of our heads.

-- Lean provides a few ways to search through the standard library to find
-- theorems that may be useful during a particular proof. The first such way
-- is the `exact?` tactic. This tactic searches the standard library for a
-- theorem that can be applied, along with the hypotheses in the context, to
-- exactly close the current goal.

example (n m : Nat) : n + m = m + n := by
  exact?

-- Try this:
--   [apply] exact Nat.add_comm n m

-- If you are using the Lean extension in VSCode, the InfoView will have a
-- blue `[apply]` button that shows the suggested theorem to close the goal.
-- Alternatively, VSCode may show an inline suggestion (lightbulb) button
-- above the `exact?`. You can click either of these buttons to replace the
-- occurrence of `exact?` with the tactic it found to complete the proof;
-- idiomatic Lean does not leave `exact?` tactics (or any other `?` tactics,
-- as we will see shortly) in the finished versions of proofs and instead
-- replaces them with the tactics they found during search.

-- The `exact?` tactic is useful when we just need a single library theorem to
-- get us over the finish line of a proof, but it is not so helpful when we
-- are deep in the middle of a proof or are wondering how to get started on
-- one. Luckily, there are other tactics that will help us with this.

-- The `rw?` tactic works like `exact?`, except that it searches for any
-- theorems that you could use to rewrite the current goal.

example (n m : Nat) : n + m = m + n := by
  rw?

-- Try this:
--   [apply] rw [Nat.add_comm]

-- However, unlike `exact?`, just because `rw?` suggests a theorem to you does
-- not automatically imply that it will be useful. In the example below, many
-- of the theorems `rw?` suggests will not progress towards completing the
-- proof; you will need to carefully look through its suggestions to see which
-- ones seem useful. We strongly recommend against blindly using `rw?` and
-- accepting its suggestions without due consideration! You will find this a
-- very slow and frustrating way to write proofs. Instead, we suggest figuring
-- out what you would like your next step to be, conceptually, and then using
-- `rw?` to search for a theorem that implements it. If no such theorem
-- exists, that may be a sign that you need to prove it yourself.

sf_expect_failure
  example (n m k : Nat) :
     (n + m) + k = m + (n + k) := by
    -- lots of suggestions to look through here!
    rw?

-- Prove the following theorems about `Nat`s. You should not need induction
-- for any of these; you can find the theorems you need using `rw?` and
-- `exact?`.

theorem mul_three (n : Nat) :
    3 * n = n + n + n := by
  sorry

theorem mul_three_beq (n : Nat) :
    (3 * n == n + n + n) = true := by
  sorry

-- ## Structuring Proofs with `calc`

-- In Lean proofs, long `rw` chains are useful, but they are sometimes hard to
-- read because the intermediate goals are invisible. Furthermore, sometimes
-- we *know* exactly how we want to manipulate the terms of a proof, but don't
-- want to have the tactics like `Nat.add_comm` and `Nat.add_assoc` "guess"
-- which subterms to rewrite.

-- The `calc` tactic writes down the intermediate goals of a proof, and allows
-- us to specify exactly which rewrite rules to apply at each step. It is a
-- powerful tool for structuring proofs, and is often more readable than long
-- `rw` chains.

-- `calc` is designed to mimic the style of proofs in mathematics textbooks,
-- which will often look something like this:

--   n + (m + k)
--   = (n + m) + k        ...   [by associativity of addition]
--   = (m + n) + k        ...   [by commutativity of addition]
--   = m + (n + k)        ...   [by associativity of addition]

-- Note how we can see each intermediate step of this proof when we look at it
-- this way. Let's look at how we might prove this theorem (i.e., that
-- `n + (m + k) = m + (n + k)`) in Lean.

-- First, a proof in the style we already know.

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

-- Here we present the same theorem, written with `calc`. Note how each
-- intermediate goal is visible in the source.

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k) /- one side of the goal is the argument to `calc`...
       ... and each subsequent line is a transformation, with a tactic. -/
    n + (m + k) = (n + m) + k := by rw [Nat.add_assoc]
    (n + m) + k = (m + n) + k := by rw [Nat.add_comm n m]
    /- once a line matches the other side of the equality in the main goal
       (in this case `m + (n + k)`), the calc tactic succeeds. -/
    (m + n) + k = m + (n + k) := by rw [Nat.add_assoc]

-- We can also write the proof like this to be a bit more concise:

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k)
    _ = (n + m) + k := by rw [Nat.add_assoc]
    _ = (m + n) + k := by rw [Nat.add_comm n m]
    _ = m + (n + k) := by rw [Nat.add_assoc]

-- Whereas before, the left-hand side of each equality in the `calc` tactic
-- was repeated from the right-hand side of the previous one, we can replace
-- the left-hand side entirely with an `_`. Now our Lean proof looks quite a
-- bit like the textbook one we saw earlier!

-- ### Exercise (1 star): succ_mul_succ ⭐

theorem succ_mul_succ (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]

-- Given this proof with `rw`, rewrite it with `calc`. Recall that you can use
-- `rw?` to find appropriate rules to rewrite by.

theorem succ_mul_succ' (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  sorry

-- If you prefer `rw` to `calc`, that's fine! Each has particular uses, and
-- both will be tools in your ever-growing toolbox of tactics.

-- ## Definitional Simplification: `dsimp`

-- Often, rather than rewriting by a known equation like
-- `n + succ m = succ (n + m)` using `rw [add_succ]`, we just want to simplify
-- the function (here `Nat.add`) automatically when we can.

-- The `dsimp` tactic ("definitionally simplify") unfolds definitions and
-- performs definitional simplifications. You can give it hints in square
-- brackets: `dsimp [f]` tells it to unfold the definition of `f`. You can
-- also simplify a hypothesis `h` in the context by writing
-- `dsimp [...] at h`. `dsimp` will also close goals by `rfl` when possible.

def square (n : Nat) : Nat := n * n

def triple (n : Nat) : Nat := n + n + n

-- When the goal depends on a fact about an unknown value, `rfl` fails. Here,
-- `dsimp` makes progress, exposing a goal the fact can close.

example (n m : Nat) (h : n + n = m) : triple n = m + n := by
  -- rfl will not work here!
  dsimp [triple]
  -- The goal can now be rewritten by `h`.
  rw [h]

-- As we have seen, `rw` can also unfold definitions. In this example, either
-- style is fine: use `dsimp [triple]` when you want to emphasize definitional
-- simplification, or `rw [triple, h]` when the proof is just a sequence of
-- rewrites.

example (n m : Nat) (h : n + n = m) : triple n = m + n := by
  -- `rw [triple]` unfolds `triple n`.
  rw [triple, h]

-- ### Exercise (2 stars): dsimp1 ⭐⭐

-- Complete this proof, using `dsimp` or `rw` as appropriate.

example (n m : Nat) (h : m = n) : triple m = n + (n + n) := by
  sorry

-- `dsimp at h` also works on hypotheses, which `rfl` can't touch.

example (n : Nat) (h : square n = 16) : n * n = 16 := by
  dsimp [square] at h
  exact h

-- Aside: `rw [...] at h` also works on hypotheses too, as does `rw? at h`

example (n m : Nat) (h : 2 * n = m * 2) : n + n = m + m := by
  rw [Nat.mul_comm, Nat.mul_two, Nat.mul_two] at h
  exact h

-- `dsimp` also takes definitional steps such as `+ 0`, so it can finish goals
-- that `rfl` would close.

example (n : Nat) : square n + 0 = n * n := by
  dsimp [square]

-- Like `rw` and `exact`, `dsimp` also has a `?` version that searches for
-- functions to simplify by. Many Lean tactics have `?` versions; try it out
-- if you are unsure.

-- ### A New Step Towards Automation

-- In the section on Irreducibility, Rewriting, and Proof Engineering in
-- Basics, we hinted at introducing more automated tactics than `rewrite` for
-- writing proofs. The first of these is `dsimp`: by using `dsimp`, we allow
-- Lean to introduce a small amount of its own automatic reasoning using other
-- basic tactics like `rfl`. If you're ever confused by what `dsimp` is doing,
-- don't be afraid to switch back to `rewrite` to examine what's going on.

-- Later in the Automation chapter, we will introduce the more powerful
-- automated tactic `simp`, which can sometimes solve complex goals by itself
-- and is accordingly extremely common in real-world Lean developments.

-- But, using this tactic now does not help (in fact, it hurts!) the process
-- of learning logical reasoning, formal theorem proving, and Lean.
-- Additionally, real Lean programmers are careful when using automation: it
-- can hurt the readability of a proof, and real-world Lean is often used to
-- *communicate* a result as much as to prove it. We will continue to use only
-- simple tactics, like `dsimp` and `rw`, for most of this volume so that you
-- have a firm grasp of both the logic behind the proofs you are writing and
-- the ways to structure those proofs to make your logic clear.

-- ## Redefining Functions and Lemmas over Nats

-- Now that we've switched over to using Lean's standard library, we can
-- redefine some of the functions from the last few chapters on `Nat`s. Note
-- that, for the built-in `Nat` type, the patterns `0` and `n + 1` correspond
-- to `Nat.zero` and `Nat.succ n`. Likewise, the pattern `n + 2` is equivalent
-- to `n + 1 + 1`.

-- Prove some of these theorems using the techniques we've discussed this
-- chapter.

def Nat.even (n : Nat) :=
  match n with
  | 0     => true
  | 1     => false
  | n + 2 => even n

def Nat.odd (n : Nat) := !(even n)

theorem Nat.odd_def (n : Nat) : n.odd = !(n.even) := rfl

def Nat.minustwo (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | 1      => 0
  | n' + 2 => n'

def Nat.double (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => double n' + 2

-- Note that we defined these functions in the `Nat` namespace; Lean's naming
-- conventions advise that functions on a type should be defined in that
-- type's namespace in almost all circumstances.

-- When we define functions this way, something interesting happens to the way
-- Lean's InfoView prints them. Take a look at the InfoView inside the proof
-- of this theorem before the `rfl` tactic:

theorem Nat.even_add_three (n : Nat) : even (n + 3) = even (n + 1) := by
  rfl

-- Instead of printing the goal the way we wrote it in the theorem statement,
-- Lean prints `(n + 3).even = (n + 1).even`! This is an example of Lean's
-- *field notation*, whereby Lean prints functions inside the namespace of a
-- type *after* their first argument, separated by a `.`. At first glance,
-- this may appear similar to how object-oriented methods work, but it's
-- really just a syntactic variation on the normal function-application style
-- we've seen so far. That is, `Nat.even n` and `n.even` are just different
-- ways to write the exact same term.

-- In previous chapters we disabled this notation by putting
-- `set_option pp.fieldNotation false` at the top of each file, but from now
-- on we will leave it enabled, since field notation is recommended in
-- idiomatic Lean developments.

-- As an example, observe the difference in how Lean prints the goal in the
-- following two examples:

set_option pp.fieldNotation false

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

set_option pp.fieldNotation true

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

-- ### Exercise (2 stars): even_succ ⭐⭐

theorem Nat.even_succ (n : Nat) :
    (n + 1).even = !(n.even) := by
  sorry

-- We reprove here for Lean's `Nat` some theorems about `Nat.even` and
-- `Nat.double`, which we had previously proven for our custom
-- `NatPlayground.Nat`.

theorem Nat.even_zero : even 0 = true := by rfl
theorem Nat.double_zero : double 0 = 0 := by rfl
theorem Nat.double_succ (n : Nat) : (n + 1).double = n.double + 2 := by rfl

-- ### Exercise (2 stars): double_add ⭐⭐

theorem Nat.double_add (n : Nat) : n.double = n + n := by
  sorry

-- ### Exercise (2 stars): double_mul ⭐⭐

theorem Nat.double_mul (n : Nat) : n.double = 2 * n := by
  sorry

-- ## Using Code Actions to Generate Match Skeletons

-- Lean's language server can suggest *code actions*, which are small editor
-- commands that modify the source code. In VSCode, a lightbulb icon appears
-- on the left when a code action is available at your cursor. You can click
-- the icon or open the code action menu with `Ctrl + .` on Windows/Linux or
-- `Command + .` on macOS. For more information, see the [Lean 4 VSCode
-- extension
-- manual](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md#code-actions).

-- Some code actions can generate the explicit branches needed for pattern
-- matching. This is especially useful when working with `match` expressions,
-- or with tactics such as `cases` and `induction`, which we saw in previous
-- chapters.

-- Let's look at an example using `induction`. For example, suppose we start
-- with the following incomplete proof:

sf_expect_failure
  example (n : Nat) : Nat.beq n n := by
    induction n

-- Put your cursor on `induction n` and open the code action menu. You should
-- see "Generate an explicit pattern match for 'induction'." in the list. If
-- you choose this action, Lean adds an explicit branch for each constructor:

example (n : Nat) : Nat.beq n n := by
  induction n with
  | zero => sorry
  | succ n _ => sorry

-- This gives us basic structure of the proof without requiring us to write
-- each branch by hand. We can then focus on proving each case.

-- One possible proof is:

example (n : Nat) : Nat.beq n n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.beq, ih]

-- Note that Lean used `_` for the induction hypothesis in the generated
-- `succ` branch. At that point, Lean didn't know whether the unfinished proof
-- would need to refer to the hypothesis. Since we use it in `rw`, we replace
-- `_` with the name `ih`.

-- In later chapters, we will see some tactics that can make such inaccessible
-- names available again.

-- The same trick also works for `match` expressions. For example, suppose we
-- start with

sf_expect_failure
  def isZero (n : Nat) : Bool :=
    match n

-- Lean can generate the missing branches:

sf_expect_failure
  def isZero (n : Nat) : Bool :=
    match n with
    | 0 => _
    | n + 1 => _


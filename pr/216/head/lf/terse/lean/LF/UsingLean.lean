import LF.Basics
import LF.Induction

import LF.SFLCompat

-- # UsingLean: Using the full power of a proof assistant

-- Note to developers (NOW):
--     Chapter goals: Nats dsimp calc

-- Note to developers (Benjamin Pierce @bcpierce00, NOW):
--     Did we intend for this section header to be in a "full"
--     block?

-- Note to developers (Benjamin Pierce @bcpierce00):
--     Is Basics needed explicitly? And why are these here
--     instead of at the top of the file?

-- Until now, we have been working with our own custom natural
-- numbers, using the `Nat` type that we defined in
-- `Basics.lean`.

-- However, Lean has a built-in type of natural numbers, which
-- is more powerful and comes with many useful features. They
-- are very slightly different from our custom `Nat`, but these
-- differences are mostly superficial. The built-in natural
-- numbers are defined in the `Init` module, which is
-- automatically imported by Lean. We will refer to them as
-- `Nat` as well, but they are not the same as the `Nat` we
-- defined in `Basics.lean`.

-- In Lean, programmers and mathematicians don't re-prove the
-- basic properties of natural numbers from scratch, nor do
-- they tend to write out `rewrite` steps for basic properties
-- of natural numbers by hand.

-- Note to developers (Benjamin Pierce @bcpierce00):
--     Just making a note that we need to explain the
--     `zero.succ.succ` notation someplace well before this
--     file!
--
--     Have we already explained sections, and how they differ
--     from namespaces? Will it be clear to readers why we need
--     one here? Can we choose a better name than
--     `long_example`?

-- Note to developers (Daniel Sainati @dsainati1):
--     We turn off the postfix notation for our new definition
--     of succ in `Basics`, should we also turn it off here for
--     Nats? I really find it to be less readable, but maybe
--     that's just me.

section long_example
open NatPlayground.Nat

-- Previously, we did computation like this...

theorem test_mult1' : (two * two : NatPlayground.Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  rewrite [mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_zero]
  rfl
end long_example

-- Note to developers (Benjamin Pierce @bcpierce00, NOW):
--     The info viewed in the InfoView during this proof is
--     kind of mysterious (to me) here. Have we already given
--     people enough help to understand it here?

-- This approach is useful in a textbook for understanding the
-- structure of natural numbers and for providing early
-- practice with writing proofs. But it is also tedious in the
-- long term.

-- Instead of doing this, programmers and mathematicians use
-- the built-in `Nat` and the powerful features of Lean to
-- *automatically* prove properties about natural numbers and
-- to compute with them.

theorem test_mult1_nat : (3 * 3 : Nat) = 9 := by
  rfl

-- The annotation `: Nat` tells Lean that we are using its
-- built-in `Nat` type.

-- In this chapter we will learn how to use the built-in `Nat`
-- and some powerful features for computing with and proving
-- properties about natural numbers. Specifically, we will
-- learn about `dsimp`, `calc`, and `simp` annotations, which
-- enable more powerful and concise proofs.

-- In fact, from now on, we will use the built-in `Nat` type
-- and its powerful features, writing `Nat.<theorem>` to
-- reference Lean's version of `<theorem>`.

-- Note to developers (Benjamin Pierce @bcpierce00):
--     Why can't we just write <theorem>?

-- ### `rfl` and computation with `Nat`

-- With Lean's `Nat`, much of the computation happens
-- automatically, and `rfl` suffices to close any equality of
-- computation on literals.

theorem complicated_computation : (2 * 3 + 4 * 5 : Nat) * 6 = 156 := by
  rfl

-- This quickly becomes necessary, as natural numbers quickly
-- get large!

-- Of course, `rfl` can't close more complicated goals where
-- the values of the terms are unknown.

theorem rfl_not_enough (n m : Nat) (h : n = m) : n = m := by
  -- rfl will not work here!
  /- First rewrite the goal with `h`; then the two sides are identical. -/
  rewrite [h]
  rfl

-- The same proof can be written more compactly with `rw`. In
-- this example, `rw [h]` rewrites with `h` and then closes the
-- resulting reflexive goal.

theorem rfl_not_enough' (n m : Nat) (h : n = m) : n = m := by
  rw [h]

-- We will continue to show more powerful tools for
-- manipulating the context and goal of a proof to bring them
-- closer to what can be solved with `rfl`.

-- ## Using the Standard Library

-- Use the `exact?` tactic to search for relevant theorems in
-- the standard library.

example (a b : Nat) : a + b = b + a := by
  /- this will suggest that we use `exact Nat.add_comm a b` to close this goal -/
  exact?

-- You can also use `rw?` to look for theorems to rewrite by

example (a b : Nat) : a + b = b + a := by
  /- this will suggest that we use `rw [Nat.add_comm]` to close this goal -/
  rw?

example (n m q : Nat) :
   (n + m) + q = m + (n + q) := by
  -- lots of suggestions to look through here!
  rw?
  sorry

-- Prove the following theorems about `Nat`s. You should not
-- need induction for any of these; you can find the theorems
-- you need using `rw?` and `exact?`.

theorem mul_three (p : Nat) :
    3 * p = p + p + p := by
  sorry

theorem mul_three_beq (p : Nat) :
    (3 * p == p + p + p) = true := by
  sorry

-- ## Structuring proofs with `calc`

-- In Lean proofs, long `rw` chains are useful, but they are
-- sometimes hard to read because the intermediate goals are
-- invisible. Furthermore, sometimes we *know* exactly how we
-- want to manipulate the terms of a proof, but don't want to
-- have the tactics like `add_comm` and `add_assoc` "guess"
-- which subterms to rewrite.

-- The `calc` tactic writes down the intermediate goals of a
-- proof, and allows us to specify exactly which rewrite rules
-- to apply at each step. It is a powerful tool for structuring
-- proofs, and is often more readable than long `rw` chains.

-- `calc` is designed to mimic the style of proofs in
-- mathematics textbooks, which will often look something like
-- this:

--   a + (b + c)
--   = (a + b) + c        ...   [by associativity of addition]
--   = (b + a) + c        ...   [by commutativity of addition]
--   = b + (a + c)        ...   [by associativity of addition]

-- Note how we can see each intermediate step of this proof
-- when we look at it this way. Let's look at how we might
-- prove this theorem (i.e., that `a + (b + c) = b + (a + c)`)
-- in Lean.

-- First, a proof in the style we already know.

theorem add_swap (a b c : Nat) : a + (b + c) = b + (a + c) := by
  rw [← Nat.add_assoc, Nat.add_comm a b, Nat.add_assoc]

-- Here we present the same theorem, written with `calc`. Note
-- how each intermediate goal is visible in the source.

theorem add_swap' (a b c : Nat) : a + (b + c) = b + (a + c) := by
  calc a + (b + c) /- one side of the goal is the argument to `calc`... -/
    /- ... and each subsequent line is a transformation, with a tactic. -/
    a + (b + c) = (a + b) + c := by rw [Nat.add_assoc]
    (a + b) + c = (b + a) + c := by rw [Nat.add_comm a b]
    /- once a line matches the other side of the equality in the main goal
       (in this case `(b + (a + c)`), the calc tactic succeeds. -/
    (b + a) + c = b + (a + c) := by rw [Nat.add_assoc]

-- We can also write the proof like this to be a bit more
-- concise:

theorem add_swap'' (a b c : Nat) : a + (b + c) = b + (a + c) := by
  calc a + (b + c)
    _ = (a + b) + c := by rw [Nat.add_assoc]
    _ = (b + a) + c := by rw [Nat.add_comm a b]
    _ = b + (a + c) := by rw [Nat.add_assoc]

-- Whereas before, the left-hand side of each equality in the
-- `calc` tactic was repeated from the right-hand side of the
-- previous one, we can replace the left-hand side entirely
-- with an `_`. Now our Lean proof looks quite a bit like the
-- textbook one we saw earlier!

-- ### Exercise (1 star): succ_mul_succ ⭐

theorem succ_mul_succ (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]

-- Given this proof with `rw`, rewrite it with `calc`. Reminder
-- that you can use `rw?` to find appropriate rules to rewrite
-- by.

theorem succ_mul_succ' (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  sorry

-- If you prefer `rw` to `calc`, that's fine! Each has
-- particular uses, and both will be tools in your ever-growing
-- toolbox of tactics.

-- Note to developers (Benjamin Pierce @bcpierce00):
--     Needs some exercises!!

-- ## Definitional simplification: `dsimp`

-- Often, rather than rewriting by a known equation like

-- `n + succ m = succ (n + m)` using `rw [add_succ]`,

-- we just want to simplify the function (here `add`)
-- automatically when we can.

-- The `dsimp` tactic ("definitionally simplify") unfolds
-- definitions and performs definitional simplifications. You
-- can give it hints in square brackets: `dsimp [f]` tells it
-- to unfold the definition of `f`. You can also simplify a
-- hypothesis `h` in the context by writing `dsimp [...] at h`.
-- `dsimp` will also close goals by `rfl` when possible.

def square (n : Nat) : Nat := n * n

def triple (n : Nat) : Nat := n + n + n

-- When the goal depends on a fact about an unknown value,
-- `rfl` fails. Here, `dsimp` makes progress, exposing a goal
-- the fact can close.

example (n m : Nat) (h : n + n = m) : triple n = m + n := by
  -- rfl will not work here!
  dsimp [triple]
  /- The goal can now be rewritten by `h`. -/
  rw [h]

-- As we have seen, `rw` can also unfold definitions. In this
-- example, either style is fine: use `dsimp [triple]` when you
-- want to emphasize definitional simplification, or
-- `rw [triple, h]` when the proof is just a sequence of
-- rewrites.

example (n m : Nat) (h : n + n = m) : triple n = m + n := by
  /- `rw [triple]` unfolds `triple n`. -/
  rw [triple, h]

-- ### Exercise (2 stars): dsimp1 ⭐⭐

-- Complete this proof, using `dsimp` or `rw` as appropriate.

example (n m : Nat) (h : m = n) : triple m = n + (n + n) := by
  sorry

-- `dsimp at h` also works on hypotheses, which rfl can't
-- touch.

example (n : Nat) (h : square n = 16) : n * n = 16 := by
  dsimp [square] at h
  exact h

-- Aside: `rw [...] at h` also works on hypotheses too, as does
-- `rw? at h`

example (n m : Nat) (h : 2 * n = m * 2) : n + n = m + m := by
  rw [Nat.mul_comm, Nat.mul_two, Nat.mul_two] at h
  exact h

-- `dsimp` also takes definitional steps such as `+ 0`, so it
-- can finish goals that rfl would close.

example (n : Nat) : square n + 0 = n * n := by
  dsimp [square]

-- Like `rw` and `exact`, `dsimp` also has a `?` version that
-- searches for functions to simplify by. Many Lean tactics
-- have `?` versions; try it out if you are unsure.

-- Note to developers (Roger Burtonpatel @rogerburtonpatel, NOW):
--     Hard pointer needed to this section once we versify.
--     Also, we may want a pointer to where we introduce `simp`
--     (and *maybe* `grind` in the next volume).

-- Note to developers (Benjamin Pierce @bcpierce00):
--     This section reference should be a live pointer, at
--     least in the HTML.

-- ## Redefining Functions and Lemmas over Nats

-- Let's redefine some functions on Lean's `Nat`s and prove
-- some theorems about them.

def Nat.even (n : Nat) :=
  match n with
  | 0     => true
  | 1     => false
  | n + 2 => even n

def Nat.odd (n : Nat) := !(even n)

theorem Nat.odd_def (n : Nat) : n.odd = !(n.even) := rfl

def Nat.minusTwo (n : Nat) : Nat :=
  match n with
  | 0    => 0
  | 1    => 0
  | n' + 2 => n'

def Nat.double (n : Nat) : Nat :=
  match n with
  | 0    => 0
  | n' + 1 => double n' + 2

-- Defining functions in the `Nat` namespace changes how they
-- print:

theorem Nat.even_add_three (n : Nat) : even (n + 3) = even (n + 1) := by
  rfl

-- This printing style is called *field notation* and can be
-- disabled with the `pp_nodot` attribute.

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

attribute [pp_nodot] Nat.double

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

-- ### Exercise (2 stars): even_succ ⭐⭐

theorem Nat.even_succ (n : Nat) :
    (n + 1).even = !(n.even) := by
  sorry

-- Note to developers (NOW):
--     talk about using `Nat.add_zero` and friends from now on.

-- (OA) : added lemmas proved for our Nat for Lean's Nat to
-- prevent later files from breaking.

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

-- Lean's language server can suggest *code actions*, which are
-- small editor commands that modify the source code. In
-- VSCode, a light-bulb icon appears on the left when a code
-- action is available at your cursor. You can click the icon
-- or open the code action menu with `Ctrl + .` on
-- Windows/Linux or `Command + .` on macOS.

-- For more information, see [Lean 4 VS Code extension
-- manual](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md#code-actions).

-- Some code actions can generate the explicit branches needed
-- for pattern matching. This is especially useful when working
-- with `match` expressions, or with tactics such as `cases`
-- and `induction`, which we saw in previous chapters.

-- Let's look at an example using `induction`.


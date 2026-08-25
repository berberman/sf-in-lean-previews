import LF.Basics
import LF.Induction

import SFLCompat

-- # UsingLean: Using the Full Power of a Proof Assistant

-- In this chapter, we will learn to write more idiomatic Lean
-- using its more powerful tools. This includes the natural
-- numbers from its standard library, tactics which can search
-- for lemmas from the standard library, namespaces for
-- organizing lemmas, and two new tactics, `calc` and `dsimp`,
-- which enable more readable and concise proofs.

-- ## More Powerful Natural Numbers

-- Until now, we have been working with our own custom natural
-- numbers, using the `Nat` type that we defined in Basics.

-- However, Lean has a built-in type of natural numbers, which
-- is more powerful and comes with many useful features. They
-- are very slightly different from our custom `Nat`, but these
-- differences are mostly superficial. The built-in natural
-- numbers are defined in the `Init` module, which is
-- automatically imported by Lean. We will refer to them as
-- `Nat` as well.

-- In Lean, programmers and mathematicians don't re-prove the
-- basic properties of natural numbers from scratch, nor do
-- they tend to write out `rewrite` steps for basic properties
-- of natural numbers by hand.

-- Previously, we did computation like this...

section OldNats
open NatPlayground.Nat
example : (two * two : NatPlayground.Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  rewrite [mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_zero]
  rfl

-- We made Lean enforce this pedagogical style using the
-- `@irreducible` attribute on definitions like `mul` and
-- `add`. This ensured that definitions be fully simplified
-- using `rw` with simplification rules like `two_eq_succ_one`.

-- Note to developers (Benjamin Pierce @bcpierce00):
--     That last sentence is not very clear. "that definitions
--     be fully simplified" does not parse, but I'm not sure
--     whether to add "will" or "can" or something else...

-- This approach is useful in a textbook for understanding the
-- structure of natural numbers and for providing early
-- practice with writing proofs. But it is also tedious in the
-- long term.

-- Instead of doing this, programmers and mathematicians use
-- the built-in `Nat` and the powerful features of Lean to
-- *automatically* prove properties about natural numbers and
-- to compute with them.

end OldNats
-- Now, we are using Lean's built-in natural numbers.
example : (3 * 3 : Nat) = 9 := by rfl

-- The annotation `: Nat` tells Lean that we are using its
-- built-in `Nat` type. In fact, from now on, we will use the
-- built-in `Nat` type and its powerful features, writing
-- `Nat.<theorem>` to reference Lean's version of `<theorem>`.
-- (By convention, theorems about a type live in the namespace
-- of that type, hence the need for the `Nat.` prefix.)

-- Definitions in the built-in `Nat` library are *not* marked
-- `@[irreducible]`. This lets us use more powerful *automatic
-- simplification* of functions on natural numbers, which is
-- appropriate when their low-level behaviors are not the
-- primary focus of proofs. This will be the case going
-- forward.

-- ### The `rfl` Tactic and Computation with `Nat`

-- With Lean's `Nat`, much of the computation happens
-- automatically, and `rfl` suffices to close any equality of
-- computation on literals.

example : (2 * 3 + 4 * 5 : Nat) * 6 = 156 := by rfl

-- This quickly becomes necessary, as natural numbers quickly
-- get large!

-- Of course, `rfl` can't close more complicated goals where
-- the values of the terms are unknown.

example (n m : Nat) (h : n = m) : n = m := by
  -- `rfl` will not work here!
  -- First rewrite the goal with `h`; then the two sides are identical.
  rw [h]

-- We will continue to show more powerful tools for
-- manipulating the context and goal of a proof to bring them
-- closer to what can be solved with `rfl`.

-- ## Using the Standard Library

-- Use the `exact?` tactic to search for relevant theorems in
-- the standard library.

example (n m : Nat) : n + m = m + n := by
  exact?

-- Try this:
--   [apply] exact Nat.add_comm n m

-- You can also use `rw?` to look for theorems to rewrite by.

example (n m : Nat) : n + m = m + n := by
  rw?

-- Try this:
--   [apply] rw [Nat.add_comm]

-- Just because `rw?` suggests a theorem does not mean that it
-- will be useful; choose carefully from its suggestions (if at
-- all).

sf_expect_failure
  example (n m k : Nat) :
     (n + m) + k = m + (n + k) := by
    -- lots of suggestions to look through here!
    rw?

-- Prove the following theorems about `Nat`s. You should not
-- need induction for any of these; you can find the theorems
-- you need using `rw?` and `exact?`.

theorem mul_three (n : Nat) :
    3 * n = n + n + n := by
  sorry

theorem mul_three_beq (n : Nat) :
    (3 * n == n + n + n) = true := by
  sorry

-- ## Structuring Proofs with `calc`

-- In Lean proofs, long `rw` chains are useful, but they are
-- sometimes hard to read because the intermediate goals are
-- invisible. Furthermore, sometimes we *know* exactly how we
-- want to manipulate the terms of a proof, but don't want to
-- have the tactics like `Nat.add_comm` and `Nat.add_assoc`
-- "guess" which subterms to rewrite.

-- The `calc` tactic writes down the intermediate goals of a
-- proof, and allows us to specify exactly which rewrite rules
-- to apply at each step. It is designed to mimic the style of
-- proofs in mathematics textbooks, which will often look
-- something like this:

--   n + (m + k)
--   = (n + m) + k        ...   [by associativity of addition]
--   = (m + n) + k        ...   [by commutativity of addition]
--   = m + (n + k)        ...   [by associativity of addition]

-- Note how we can see each intermediate step of this proof
-- when we look at it this way. Let's look at how we might
-- prove this theorem (i.e., that `n + (m + k) = m + (n + k)`)
-- in Lean.

-- First, a proof in the style we already know.

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

-- Here we present the same theorem, written with `calc`. Note
-- how each intermediate goal is visible in the source.

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k) /- one side of the goal is the argument to `calc`...
       ... and each subsequent line is a transformation, with a tactic. -/
    n + (m + k) = (n + m) + k := by rw [Nat.add_assoc]
    (n + m) + k = (m + n) + k := by rw [Nat.add_comm n m]
    /- once a line matches the other side of the equality in the main goal
       (in this case `m + (n + k)`), the calc tactic succeeds. -/
    (m + n) + k = m + (n + k) := by rw [Nat.add_assoc]

-- We can also write the proof like this to be a bit more
-- concise:

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k)
    _ = (n + m) + k := by rw [Nat.add_assoc]
    _ = (m + n) + k := by rw [Nat.add_comm n m]
    _ = m + (n + k) := by rw [Nat.add_assoc]

-- Whereas before, the left-hand side of each equality in the
-- `calc` tactic was repeated from the right-hand side of the
-- previous one, we can replace the left-hand side entirely
-- with an `_`. Now our Lean proof looks quite a bit like the
-- textbook one we saw earlier!

-- Note to developers (Niklas Halonen @xhalo32):
--     How to grade that `succ_mul_succ'` uses `calc` without
--     cheating?

-- ### Exercise (1 star): succ_mul_succ ⭐

theorem succ_mul_succ (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]

-- Given this proof with `rw`, rewrite it with `calc`.

theorem succ_mul_succ' (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  sorry

-- If you prefer `rw` to `calc`, that's fine! Each has
-- particular uses, and both will be tools in your ever-growing
-- toolbox of tactics.

-- ## Definitional Simplification: `dsimp`

-- Often, rather than repeatedly rewriting by a known equation
-- like `rw [Nat.mul_zero, Nat.mul_zero]` to solve a goal like
-- `n * (m * 0) = 0`, we just want to simplify the function
-- (here `Nat.mul`) automatically when we can.

-- The `dsimp` ("definitionally simplify") tactic unfolds
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
  -- The goal can now be rewritten by `h`.
  rw [h]

-- As we have seen, `rw` can also unfold definitions. In this
-- example, either style is fine: use `dsimp [triple]` when you
-- want to emphasize definitional simplification, or
-- `rw [triple, h]` when the proof is just a sequence of
-- rewrites.

example (n m : Nat) (h : n + n = m) : triple n = m + n := by
  -- `rw [triple]` unfolds `triple n`.
  rw [triple, h]

-- ### Exercise (2 stars): dsimp1 ⭐⭐

-- Complete this proof, using `dsimp` or `rw` as appropriate.

theorem dsimp1 (n m : Nat) (h : m = n) : triple m = n + (n + n) := by
  sorry

-- `dsimp at h` also works on hypotheses, which `rfl` can't
-- touch.

example (n : Nat) (h : square n = 16) : n * n = 16 := by
  dsimp [square] at h
  exact h

-- Aside: `rw [...] at h` also works on hypotheses too, as does
-- `rw? at h`

example (n m : Nat) (h : 2 * n = m * 2) : n + n = m + m := by
  rw [Nat.mul_comm, Nat.mul_two, Nat.mul_two] at h
  exact h

-- But `rw` rewrites only one instance of a definition at a
-- time. When a hypothesis mentions the same function at
-- several different arguments, each one needs its own rewrite.

example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  rw [square, square, square] at h
  exact h

-- `dsimp` unfolds *every* instance at once, so one hint
-- suffices no matter how many times the definition appears.

example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  dsimp [square] at h
  exact h

-- `dsimp` also takes definitional steps such as `+ 0`, so it
-- can finish goals that `rfl` would close.

example (n : Nat) : square n + 0 = n * n := by
  dsimp [square]

-- In the above example, using `rw` would not have closed the
-- proof:

sf_expect_failure
  example (n : Nat) : square n + 0 = n * n := by
    rw [square]

-- unsolved goals
-- n✝ n : Nat
-- ⊢ n * n + 0 = n * n

-- Like `rw` and `exact`, `dsimp` also has a `?` version that
-- searches for functions to simplify by. Many Lean tactics
-- have `?` versions; try it out if you are unsure.

-- Note to developers (Mike Hicks @mwhicks1):
--     Yipeng said we can pass a theorem, e.g.
--     `dsimp [Nat.mul_zero]`, which would rewrite
--     `Nat.mul_zero` many times and then perform reductions,
--     just like simp `[Nat.mul_zero]`. Also `@[defeq] lemmas`
--     in the `simp` set are always used implicitly.
--
--     Should `dsimp [Nat.mul_zero]` be preferred over
--     `dsimp [Nat.mul]`? An example:
--
--     `example (n : Nat) : n * (n * (n * 0)) = 0 := by
--       rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
--
--     example (n : Nat) : n * (n * (n * 0)) = 0 := by
--       dsimp [Nat.mul]
--
--     example (n : Nat) : n * (n * (n * 0)) = 0 := by
--       dsimp [Nat.mul_zero]`
--
--     This could be confusing though, because rewriting by
--     `dsimp` only works for *definitional* equalities. The
--     following doesn't work
--
--     `example (n : Nat) : (((0 * n) * n) * n) = 0 := by
--       dsimp [Nat.zero_mul]`
--
--     This is because `Nat.zero_mul` is true by induction, not
--     reduction. This is a bit confusing to explain, and also
--     unfortunate since one may not know why an equality
--     holds. Thus I'd prefer not to include this use here.

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
  | 0      => 0
  | 1      => 0
  | n' + 2 => n'

def Nat.double (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => double n' + 2

-- Defining functions in the `Nat` namespace changes how they
-- print:

theorem Nat.even_add_three (n : Nat) : even (n + 3) = even (n + 1) := by
  rfl

-- This printing style is called *field notation* and can be
-- enabled or disabled with the `pp.fieldNotation` option.

set_option pp.fieldNotation false

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

set_option pp.fieldNotation true

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

-- ### Exercise (2 stars): even_succ (Optional) ⭐⭐

-- One inconvenient aspect of our definition of `even n` is the
-- recursive call on `n'` when `n = n' + 2`. This makes proofs
-- about `even n` harder when done by induction on `n`, since
-- we may need an induction hypothesis about `n' + 2`, while
-- induction just gives us one about `n' + 1`. The following
-- lemma proves `even (n + 1)` flips the parity, which gives an
-- alternative characterization that works better with
-- induction. We'll see uses of this theorem in Lists.

theorem Nat.even_succ (n : Nat) :
    (n + 1).even = !(n.even) := by
  sorry

-- We reprove here for Lean's `Nat` some theorems about
-- `Nat.even` and `Nat.double`, which we had previously proven
-- for our custom `NatPlayground.Nat`.

theorem Nat.even_zero : even 0 = true := by rfl
theorem Nat.double_zero : double 0 = 0 := by rfl
theorem Nat.double_succ (n : Nat) : (n + 1).double = n.double + 2 := by rfl

-- ### Exercise (2 stars): double_add ⭐⭐

theorem Nat.double_add (n : Nat) : n.double = n + n := by
  sorry

-- ### Exercise (2 stars): double_mul ⭐⭐

theorem Nat.double_mul (n : Nat) : n.double = 2 * n := by
  sorry

-- In the remainder of the book, we use Lean's built-in natural
-- numbers everywhere. We use `dsimp` and `calc` in examples
-- and solutions, and encourage their use. We also recommend
-- using `rw?` and `exact?` to search for lemmas (though these
-- should not appear in finished proofs).

-- With these tools in hand, we can begin to prove properties
-- about more sophisticated forms of data, beginning with
-- `Lists`.


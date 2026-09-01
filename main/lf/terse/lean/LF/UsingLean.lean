import LF.Basics
import LF.Induction

import SFLCompat

--  # UsingLean: Using the Full Power of a Proof Assistant

--  In this chapter, we will learn to write more idiomatic
--  Lean using its more powerful tools. This includes the
--  natural numbers from its standard library, tactics which
--  can search for lemmas from the standard library,
--  namespaces for organizing lemmas, and a new tactic,
--  `calc`, which enables more readable and concise proofs.

--  ## More Powerful Natural Numbers

--  Until now, we have been working with our own custom
--  natural numbers, using the `Nat` type that we defined in
--  Basics.
--
--  However, Lean has a built-in type of natural numbers,
--  which is more powerful and comes with many useful
--  features. They are very slightly different from our
--  custom `Nat`, but these differences are mostly
--  superficial. The built-in natural numbers are defined in
--  the `Init` module, which is automatically imported by
--  Lean. We will refer to them as `Nat` as well.
--
--  In Lean, programmers and mathematicians don't re-prove
--  the basic properties of natural numbers from scratch,
--  nor do they tend to write out `rewrite` steps for basic
--  properties of natural numbers by hand.
--
--  Previously, we did computation like this...

section OldNats
open NatPlayground.Nat
example : (two * two : NatPlayground.Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  rewrite [mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_zero]
  rfl

--  We made Lean enforce this pedagogical style using
--  `attribute [irreducible]` on definitions like `mul` and
--  `add`. This forced us to write proofs using tactics like
--  `rw` rather than simplifying definitions.
--
--  This approach is useful in a textbook for understanding
--  the structure of natural numbers and for providing early
--  practice with writing proofs. But it is also tedious in
--  the long term.
--
--  Instead of doing this, programmers and mathematicians
--  use the built-in `Nat` and the powerful features of Lean
--  to *automatically* prove properties about natural
--  numbers and to compute with them.

end OldNats
-- Now, we are using Lean's built-in natural numbers.
example : (3 * 3 : Nat) = 9 := by rfl

--  The annotation `: Nat` tells Lean that we are using its
--  built-in `Nat` type. In fact, from now on, we will use
--  the built-in `Nat` type and its powerful features,
--  writing `Nat.<theorem>` to reference Lean's version of
--  `<theorem>`. (By convention, theorems about a type live
--  in the namespace of that type, hence the need for the
--  `Nat.` prefix.)
--
--  Definitions in the built-in `Nat` library are *not*
--  marked `@[irreducible]`. This lets us use more powerful
--  *automatic simplification* of functions on natural
--  numbers, which is appropriate when their low-level
--  behaviors are not the primary focus of proofs. This will
--  be the case going forward.

--  ### The `rfl` Tactic and Computation with `Nat`

--  With Lean's `Nat`, much of the computation happens
--  automatically, and `rfl` suffices to close any equality
--  of computation on literals.

example : (2 * 3 + 4 * 5 : Nat) * 6 = 156 := by rfl

--  This quickly becomes necessary, as natural numbers
--  quickly get large!
--
--  Of course, `rfl` can't close more complicated goals
--  where the values of the terms are unknown.

example (n m : Nat) (h : n = m) : n = m := by
  -- `rfl` will not work here!
  -- First rewrite the goal with `h`; then the two sides are identical.
  rw [h]

--  We will continue to show more powerful tools for
--  manipulating the context and goal of a proof to bring
--  them closer to what can be solved with `rfl`.

--  ## Using the Standard Library

--  Use the `exact?` tactic to search for relevant theorems
--  in the standard library.

example (n m : Nat) : n + m = m + n := by
  exact?

--  Output:
--    Try this:
--      [apply] exact Nat.add_comm n m

--  You can also use `rw?` to look for theorems to rewrite
--  by.

example (n m : Nat) : n + m = m + n := by
  rw?

--  Output:
--    Try this:
--      [apply] rw [Nat.add_comm]

--  Just because `rw?` suggests a theorem does not mean that
--  it will be useful; choose carefully from its suggestions
--  (if at all).

sf_expect_failure_in
  example (n m k : Nat) :
     (n + m) + k = m + (n + k) := by
    -- lots of suggestions to look through here!
    rw?

--  Prove the following theorems about `Nat`s. You should
--  not need induction for any of these; you can find the
--  theorems you need using `rw?` and `exact?`.

theorem mul_three (n : Nat) :
    3 * n = n + n + n := by
  sorry

theorem mul_three_beq (n : Nat) :
    (3 * n == n + n + n) = true := by
  sorry

--  The `calc` can be used to make long chains of rewrites
--  easier to follow:

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

--  Here we present the same theorem, written with `calc`.
--  Note how each intermediate goal is visible in the
--  source.

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k) /- one side of the goal is the argument to `calc`...
       ... and each subsequent line is a transformation, with a tactic. -/
    n + (m + k) = (n + m) + k := by rw [Nat.add_assoc]
    (n + m) + k = (m + n) + k := by rw [Nat.add_comm n m]
    /- once a line matches the other side of the equality in the main goal
       (in this case `m + (n + k)`), the calc tactic succeeds. -/
    (m + n) + k = m + (n + k) := by rw [Nat.add_assoc]

--  We can also write the proof like this to be a bit more
--  concise:

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k)
    _ = (n + m) + k := by rw [Nat.add_assoc]
    _ = (m + n) + k := by rw [Nat.add_comm n m]
    _ = m + (n + k) := by rw [Nat.add_assoc]

--  Whereas before, the left-hand side of each equality in
--  the `calc` tactic was repeated from the right-hand side
--  of the previous one, we can replace the left-hand side
--  entirely with an `_`. Now our Lean proof looks quite a
--  bit like the textbook one we saw earlier!

--  ### Exercise (1 star): succ_mul_succ ⭐

theorem succ_mul_succ (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]

--  Given this proof with `rw`, rewrite it with `calc`.

theorem succ_mul_succ' (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  sorry

--  If you prefer `rw` to `calc`, that's fine! Each has
--  particular uses, and both will be tools in your
--  ever-growing toolbox of tactics.

--  ## Unfolding definitions with `rw`

--  Here are some definitions about `Nat`s:

def addTwice (n : Nat) : Nat := n + n
def addThrice (n : Nat) : Nat := n + n + n

--  A simple example of something we might wish to prove
--  about these two things is that adding `n` to
--  `addTwice n` is the same as `addThrice n`. One might
--  hope to proceed by `rfl`, but this doesn't quite work:

sf_expect_failure_in
  example (n : Nat) : addThrice n = n + addTwice n := by
    rfl

--  Output:
--    Tactic `rfl` failed: The left-hand side
--      addThrice n
--    is not definitionally equal to the right-hand side
--      n + addTwice n
--
--    n✝ n : Nat
--    ⊢ addThrice n = n + addTwice n

--  What happened here? If we are careful with our
--  parentheses here, we can write the goal we'd like to
--  prove as `(addThrice n) = n + (addTwice n)`. Unfolding
--  definitions, we can see that this is equivalent to:
--
--      n + n + n = n + (n + n)
--
--  which, when we are more explicit about parenthesization,
--  is equivalent to:
--
--      (n + n) + n = n + (n + n)
--
--  These two things are not definitionally equal, so we
--  cannot use `rfl` here, hence our error from earlier. The
--  next thing we might want to try is rewriting by
--  `Nat.add_assoc`; which would give us a syntactically
--  equal equality as our goal:

sf_expect_failure_in
  example (n : Nat) : addThrice n = n + addTwice n := by
    rw [Nat.add_assoc]

--  Output:
--    Tactic `rewrite` failed: Did not find an occurrence of the pattern
--      ?n + ?m + ?k
--    in the target expression
--      addThrice n = n + addTwice n
--
--    n✝ n : Nat
--    ⊢ addThrice n = n + addTwice n

--  But again we encounter an error! The expression in which
--  we are trying to rewrite `Nat.add_assoc` isn't of the
--  form `n + m + k`, so we can't proceed. What then, should
--  we do? To proceed here, we need to reveal to Lean the
--  underlying definitions of `addThrice` and `addTwice`, so
--  that `rw`, which only operates on syntax, can see the
--  addition. We can do this by rewriting by those
--  definitions:

example (n : Nat) : addThrice n = n + addTwice n := by
  -- `rw [addThrice]` unfolds `addThrice`, replacing it with its definition
  rw [addThrice]
  -- this likewise unfolds `addTwice`
  rw [addTwice]
  -- Now, proving our goal only requires associativity of additions
  rw [Nat.add_assoc]

--  Unfolding definitions in goals and hypotheses like this
--  let us guide Lean into simplifying expressions and
--  allowing it to rewrite by more theorems in more places.

--  ### Exercise (2 stars): rwUnfold ⭐⭐

--  Complete this proof, using `rw` to unfold the definition
--  of `addThrice` as appropriate.

theorem rwUnfold (n m : Nat) (h : m = n) : addThrice m = n + (n + n) := by
  sorry

--  Rewriting can also be used in places where `rfl` can't,
--  like hypotheses.

def square (n : Nat) : Nat := n * n

example (n : Nat) (h : square n = 16) : n * n = 16 := by
  rw [square] at h
  exact h

--  Aside: `rw? at h` also works on hypotheses:

example (n m : Nat) (h : 2 * n = m * 2) : n + n = m + m := by
  rw [Nat.mul_comm, Nat.mul_two, Nat.mul_two] at h
  exact h

--  But `rw` rewrites only one instance of a definition at a
--  time. When a hypothesis or goal mentions the same
--  function applied to different arguments, each one needs
--  its own rewrite.

example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  rw [square, square, square] at h
  exact h

--  Use `repeat` to repeat a tactic multiple times:

example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  repeat rw [square] at h
  exact h

--  ### Definitional Simplification

--  `dsimp only` can perform basic simplification:

example : (fun x => x + 0) n = n := by
  dsimp only -- applies the function to its argument
  rw [Nat.add_zero]

--  If we did not simplify here before attempting to
--  rewrite, we would get an error:

sf_expect_failure_in
  example : (fun x => x + 0) n = n := by
    rw [Nat.add_zero]

--  Output:
--    Tactic `rewrite` failed: Did not find an occurrence of the pattern
--      ?n + 0
--    in the target expression
--      (fun x => x + 0) n = n
--
--    n : Nat
--    ⊢ (fun x => x + 0) n = n

--  ## Redefining Functions and Lemmas over Nats

--  Let's redefine some functions on Lean's `Nat`s and prove
--  some theorems about them.

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

--  Defining functions in the `Nat` namespace changes how
--  they print:

theorem Nat.even_add_three (n : Nat) : even (n + 3) = even (n + 1) := by
  rfl

--  This printing style is called *field notation* and can
--  be enabled or disabled with the `pp.fieldNotation`
--  option.

set_option pp.fieldNotation false

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

set_option pp.fieldNotation true

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

--  ### Exercise (2 stars): even_succ (Optional) ⭐⭐

--  One inconvenient aspect of our definition of `even n` is
--  the recursive call on `n'` when `n = n' + 2`. This makes
--  proofs about `even n` harder when done by induction on
--  `n`, since we may need an induction hypothesis about
--  `n' + 2`, while induction just gives us one about
--  `n' + 1`. The following lemma proves `even (n + 1)`
--  flips the parity, which gives an alternative
--  characterization that works better with induction. We'll
--  see uses of this theorem in Lists.

theorem Nat.even_succ (n : Nat) :
    (n + 1).even = !(n.even) := by
  sorry

--  We reprove here for Lean's `Nat` some theorems about
--  `Nat.even` and `Nat.double`, which we had previously
--  proven for our custom `NatPlayground.Nat`.

theorem Nat.even_zero : even 0 = true := by rfl
theorem Nat.double_zero : double 0 = 0 := by rfl
theorem Nat.double_succ (n : Nat) : (n + 1).double = n.double + 2 := by rfl

--  ### Exercise (2 stars): double_add ⭐⭐

theorem Nat.double_add (n : Nat) : n.double = n + n := by
  sorry

--  ### Exercise (2 stars): double_mul ⭐⭐

theorem Nat.double_mul (n : Nat) : n.double = 2 * n := by
  sorry

--  In the remainder of the book, we use Lean's built-in
--  natural numbers everywhere. We also recommend using
--  `rw?` and `exact?` to search for lemmas (though these
--  should not appear in finished proofs).
--
--  With these tools in hand, we can begin to prove
--  properties about more sophisticated forms of data,
--  beginning with `Lists`.

-- Built on 2026-08-31 23:56 UTC

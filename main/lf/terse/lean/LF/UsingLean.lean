import LF.Basics
import LF.Induction

import SFLCompat

--  # UsingLean: Using the Full Power of a Proof Assistant

--  In this chapter, we will learn to write more idiomatic
--  Lean using its more powerful tools.

--  ## More Powerful Natural Numbers

--  Whereas we performed manual `rewrite` steps on our
--  custom `Nat`s ...

section OldNats
open NatPlayground.Nat
example : (two * two : NatPlayground.Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  rewrite [mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_zero]
  rfl

--  ... we can simplify Lean's built-in `Nat`s
--  automatically.

end OldNats
-- Now, we are using Lean's built-in natural numbers.
example : (2 * 2 : Nat) = 4 := by rfl

--  Doing so is very helpful for large numbers — we would
--  not want to write out the hundreds or thousands of
--  `rewrite` steps needed for proving examples like the
--  following!

example : (2 * 3 + 4 * 5 : Nat) * 6 = 156 := by rfl

--  Of course, `rfl` still can't close goals where the
--  values of the terms are unknown.

example (n m : Nat) (h : n = m) : n = m := by
  -- `rfl` will not work here!
  -- First rewrite the goal with `h`; then the two sides are identical.
  rw [h]

--  From now on we will use the built-in `Nat` type.

--  ## Searching for Standard Library Theorems

--  Use the `exact?` tactic to search for relevant theorems
--  in the standard library.

example (n m : Nat) : n + m = m + n := by
  exact?

--  You can also use `rw?` to look for theorems to rewrite
--  by.

example (n m : Nat) : n + m = m + n := by
  rw?

--  Just because `rw?` suggests a theorem does not mean that
--  it will be useful; choose carefully from its suggestions
--  (if at all).

sf_expect_failure_in
  example (n m k : Nat) :
     (n + m) + k = m + (n + k) := by
    -- lots of suggestions to look through here!
    rw?

--  ## Structuring Proofs with `calc`

--  In Lean proofs, long `rw` chains are useful, but they
--  are sometimes hard to read because the intermediate
--  goals are invisible.
--
--  The `calc` tactic writes down the intermediate goals of
--  a proof, and allows us to specify exactly which rewrite
--  rules to apply at each step. It is designed to mimic the
--  style of proofs in mathematics textbooks, which will
--  often look something like this:
--
--      n + (m + k)
--      = (n + m) + k        ...   [by associativity of addition]
--      = (m + n) + k        ...   [by commutativity of addition]
--      = m + (n + k)        ...   [by associativity of addition]

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

--  Now, the same theorem written with `calc`. Note how each
--  intermediate goal is visible in the source.

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

--  ## Unfolding definitions using `rw`

--  Here are some definitions about `Nat`s:

def addTwice (n : Nat) : Nat := n + n
def addThrice (n : Nat) : Nat := n + n + n

--  Suppose we wish to prove that `addThrice n` is equal to
--  adding `n` to `addTwice n`. We might hope to proceed by
--  `rfl`, but this doesn't work:

sf_expect_failure_in
  example (n : Nat) : (addThrice n) = n + (addTwice n) := by
    rfl

--  Consulting our definitions, what we are trying to prove
--  amounts to the following equation:
--
--      (n + n) + n = n + (n + n)
--
--  These two things are not definitionally equal, so we
--  cannot use `rfl` alone.

sf_expect_failure_in
  example (n : Nat) : addThrice n = n + addTwice n := by
    rw [Nat.add_assoc]

--  We need to unfold the underlying definitions of
--  `addThrice` and `addTwice` so that `rw`, which only
--  operates on syntax, can see the addition. We can do this
--  using the `rw` tactic.

example (n : Nat) : addThrice n = n + addTwice n := by
  -- `rw [addThrice]` unfolds `addThrice`, replacing it with its definition
  rw [addThrice]
  -- this likewise unfolds `addTwice`
  rw [addTwice]
  -- Now, proving our goal only requires associativity of additions
  rw [Nat.add_assoc]

--  Rewriting can also be used in places where `rfl` can't,
--  like hypotheses.

def square (n : Nat) : Nat := n * n

example (n : Nat) (h : square n = 16) : n * n = 16 := by
  rw [square] at h
  exact h

--  Aside: `rw? at h` also works on hypotheses:

example (n m : Nat) (h : 2 * n = m * 2) : n + n = m + m := by
  -- use rw? to construct the proof
  sorry

--  Unfolding should not be overused; simplification rules
--  are (still) useful proof engineering.

--  ## Definitional Simplification with `dsimp`

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

--  ## A First Automation Tactic: `repeat`

--  When `rw` unfolds a definition, it does so one instance
--  at time. Thus each occurrence of a definition needs its
--  own rewrite.

example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  rw [square, square, square] at h
  exact h

--  Use `repeat` to repeat a tactic multiple times.

example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  repeat rw [square] at h
  exact h

--  There is much more to say about automation, covered in
--  the Automation chapter.

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

--  We reprove here for Lean's `Nat` some theorems about
--  `Nat.even` and `Nat.double`, which we had previously
--  proven for our custom `NatPlayground.Nat`.

theorem Nat.even_zero : even 0 = true := by rfl
theorem Nat.double_zero : double 0 = 0 := by rfl
theorem Nat.double_succ (n : Nat) : (n + 1).double = n.double + 2 := by rfl

-- Built on 2026-09-03 19:08 UTC

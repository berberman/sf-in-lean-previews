import LF.Basics
import LF.Induction

import ComparatorAutograderLib
import SFLCompat

--  # UsingLean: Using the Full Power of a Proof Assistant

--  In this chapter, we will learn to write more idiomatic Lean using its
--  more powerful tools.

--  This includes the natural numbers from its standard library, tactics
--  which can search for lemmas from the standard library, namespaces for
--  organizing lemmas, and a new tactic, `calc`, which enables more
--  readable and concise proofs.

--  ## More Powerful Natural Numbers

--  Until now, we have been working with our own custom natural numbers,
--  using the `Nat` type that we defined in Basics.
--
--  As you might have guessed, Lean has a built-in type of natural numbers,
--  also called `Nat`, which is automatically imported into `.lean` files
--  by default. Its definition is essentially the same as our custom `Nat`,
--  but it comes with a large library of useful theorems. Programmers and
--  mathematicians usually apply these *automatically* rather than by
--  writing out `rewrite` steps by hand. For example, here is a simple
--  proof of equality using our custom `Nat`s.

section OldNats
open NatPlayground.Nat
example : (two * two : NatPlayground.Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  rewrite [mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_zero]
  rfl

--  We made Lean enforce this pedagogical style using
--  `attribute [irreducible]` on definitions like `mul` and `add`. This
--  forced us to write proofs using tactics like `rw` rather than
--  simplifying definitions.
--
--  This approach is useful in a textbook for understanding the structure
--  of natural numbers and for providing early practice with writing
--  proofs. But it is also tedious in the long term.
--
--  Instead of doing this, programmers and mathematicians use the built-in
--  `Nat` and the powerful features of Lean to *automatically* prove
--  properties about natural numbers and to compute with them.

end OldNats
-- Now, we are using Lean's built-in natural numbers.
example : (2 * 2 : Nat) = 4 := by rfl

--  The annotation `: Nat` tells Lean that we are using its built-in `Nat`
--  type. Definitions in the built-in `Nat` library are not marked
--  `@[irreducible]`, so we can perform *automatic simplification* of
--  functions on natural numbers, which is appropriate when their low-level
--  behaviors are not the primary focus of proofs.

--  Doing so is very helpful for large numbers — we would not want to write
--  out the hundreds or thousands of `rewrite` steps needed for proving
--  examples like the following!

example : (2 * 3 + 4 * 5 : Nat) * 6 = 156 := by rfl

--  Of course, `rfl` still can't close goals where the values of the terms
--  are unknown.

example (n m : Nat) (h : n = m) : n = m := by
  -- `rfl` will not work here!
  -- First rewrite the goal with `h`; then the two sides are identical.
  rw [h]

--  From now on we will use the built-in `Nat` type.

--  We will write `Nat.<theorem>` to reference Lean's version of
--  `<theorem>`; by convention, theorems about a type live in the namespace
--  of that type.

--  ## Searching for Standard Library Theorems

--  Because we did not write or prove theorems for built-in `Nat`s
--  ourselves, we may not know (or remember) all the available theorems.
--
--  Lean provides a few ways to search through the standard library to find
--  theorems that may be useful during a particular proof. The first way is
--  the `exact?` tactic. This tactic searches the standard library for a
--  theorem that can be applied, along with the hypotheses in the context,
--  to exactly close the current goal.

example (n m : Nat) : n + m = m + n := by
  exact?

--  Output:
--    Try this:
--      [apply] exact Nat.add_comm n m

--  If you are using the Lean extension in VS Code, the InfoView will have
--  a blue `[apply]` button that shows the suggested theorem to close the
--  goal. Alternatively, VS Code may show an inline suggestion (lightbulb)
--  button above the `exact?`. You can click either of these buttons to
--  replace the occurrence of `exact?` with the tactic it found to complete
--  the proof; idiomatic Lean should not contain `exact?` tactics (or any
--  other `?` tactics) in the finished versions of proofs.
--
--  The `exact?` tactic is useful when we just need a single library
--  theorem to get us over the finish line, but it is not so helpful when
--  we are deep in the middle of a proof or wondering how to get started on
--  one. Fortunately, there are other tactics that can help.
--
--  The `rw?` tactic searches for any theorems that you could use to
--  *rewrite* (rather than *complete*) the current goal.

example (n m : Nat) : n + m = m + n := by
  rw?

--  Output:
--    Try this:
--      [apply] rw [Nat.add_comm]

--  However, unlike `exact?`, just because `rw?` suggests a theorem to you
--  does not automatically imply that it will be useful. In the example
--  below, many of the theorems `rw?` suggests will not progress towards
--  completing the proof; you will need to carefully look through its
--  suggestions to see which ones seem useful.

sf_expect_failure_in
  example (n m k : Nat) :
     (n + m) + k = m + (n + k) := by
    -- lots of suggestions to look through here!
    rw?

--  We strongly recommend against blindly using `rw?` and accepting its
--  suggestions without due consideration! You will find this to be a slow
--  and frustrating way to write proofs. Instead, we suggest figuring out
--  what you would like your next step to be, conceptually, and then using
--  `rw?` to search for a theorem that implements it. If no such theorem
--  exists, you may need to prove it yourself.

--  ### Exercise (1 star): mul_three_beq ⭐

--  Prove the following theorems about `Nat`s. You should not need
--  induction; find the theorems you need using `rw?` and `exact?`.

theorem mul_three (n : Nat) :
    3 * n = n + n + n := by
  sorry

attribute [autogradedProof 1] mul_three

theorem mul_three_beq (n : Nat) :
    (3 * n == n + n + n) = true := by
  sorry

attribute [autogradedProof 1] mul_three_beq

--  ## Structuring Proofs with `calc`

--  In Lean proofs, long `rw` chains are useful, but they are sometimes
--  hard to read because the intermediate goals are invisible.

--  Furthermore, sometimes we *know* exactly how we want to manipulate the
--  terms of a proof, but don't want to have the tactics like
--  `Nat.add_comm` and `Nat.add_assoc` "guess" which subterms to rewrite.

--  The `calc` tactic writes down the intermediate goals of a proof, and
--  allows us to specify exactly which rewrite rules to apply at each step.
--  It is designed to mimic the style of proofs in mathematics textbooks,
--  which will often look something like this:
--
--      n + (m + k)
--      = (n + m) + k        ...   [by associativity of addition]
--      = (m + n) + k        ...   [by commutativity of addition]
--      = m + (n + k)        ...   [by associativity of addition]

--  Note how we can see each intermediate step of this proof when we look
--  at it this way. Let's look at how we might prove this theorem (i.e.,
--  that `n + (m + k) = m + (n + k)`) in Lean.
--
--  First, a proof in the style we already know.

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

--  Now, the same theorem written with `calc`. Note how each intermediate
--  goal is visible in the source.

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k) /- one side of the goal is the argument to `calc`...
       ... and each subsequent line is a transformation, with a tactic. -/
    n + (m + k) = (n + m) + k := by rw [Nat.add_assoc]
    (n + m) + k = (m + n) + k := by rw [Nat.add_comm n m]
    /- once a line matches the other side of the equality in the main goal
       (in this case `m + (n + k)`), the calc tactic succeeds. -/
    (m + n) + k = m + (n + k) := by rw [Nat.add_assoc]

--  We can also write the proof like this to be a bit more concise:

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k)
    _ = (n + m) + k := by rw [Nat.add_assoc]
    _ = (m + n) + k := by rw [Nat.add_comm n m]
    _ = m + (n + k) := by rw [Nat.add_assoc]

--  Whereas before, the left-hand side of each equality in the `calc`
--  tactic was repeated from the right-hand side of the previous one, we
--  can replace the left-hand side entirely with an `_`. Now our Lean proof
--  looks quite a bit like the textbook one we saw earlier!

--  ### Exercise (1 star): succ_mul_succ ⭐

--  Consider this proof, which uses `rw`.

theorem succ_mul_succ (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]

--  Rewrite the proof using `calc`.

theorem succ_mul_succ' (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  sorry

--  If you prefer `rw` to `calc`, that's fine! Each has particular uses,
--  and both will be tools in your ever-growing toolbox of tactics.

--  Note to developers (Niklas Halonen @xhalo32):
--      How to grade that `succ_mul_succ'` uses `calc` without cheating?

--  ## Unfolding definitions using `rw`

--  Here are some definitions about `Nat`s:

def addTwice (n : Nat) : Nat := n + n
def addThrice (n : Nat) : Nat := n + n + n

--  Suppose we wish to prove that `addThrice n` is equal to adding `n` to
--  `addTwice n`. We might hope to proceed by `rfl`, but this doesn't work:

sf_expect_failure_in
  example (n : Nat) : (addThrice n) = n + (addTwice n) := by
    rfl

--  Output:
--    Tactic `rfl` failed: The left-hand side
--      addThrice n
--    is not definitionally equal to the right-hand side
--      n + addTwice n
--
--    n✝ n : Nat
--    ⊢ addThrice n = n + addTwice n

--  What happened?

--  Consulting our definitions, what we are trying to prove amounts to the
--  following equation:
--
--      (n + n) + n = n + (n + n)
--
--  These two things are not definitionally equal, so we cannot use `rfl`
--  alone.

--  A natural next step is to rewrite by `Nat.add_assoc` so that `rfl`
--  should work on the result.

sf_expect_failure_in
  example (n : Nat) : addThrice n = n + addTwice n := by
    rw [Nat.add_assoc]

--  This doesn't work either.

--  Output:
--    Tactic `rewrite` failed: Did not find an occurrence of the pattern
--      ?n + ?m + ?k
--    in the target expression
--      addThrice n = n + addTwice n
--
--    n✝ n : Nat
--    ⊢ addThrice n = n + addTwice n

--  The reason is that the expression in which we are trying to rewrite
--  `Nat.add_assoc` isn't of the form `n + m + k` precisely; it is
--  `addThrice n`.

--  We need to unfold the underlying definitions of `addThrice` and
--  `addTwice` so that `rw`, which only operates on syntax, can see the
--  addition. We can do this using the `rw` tactic.

example (n : Nat) : addThrice n = n + addTwice n := by
  -- `rw [addThrice]` unfolds `addThrice`, replacing it with its definition
  rw [addThrice]
  -- this likewise unfolds `addTwice`
  rw [addTwice]
  -- Now, proving our goal only requires associativity of additions
  rw [Nat.add_assoc]

--  Since Lean does not unfold most definitions automatically, we use
--  tactics like `rw` to do so selectively, in goals and hypotheses, in
--  order to guide how a proof is carried out.

--  ### Exercise (1 star): rwUnfold ⭐

--  Complete this proof, using `rw` to unfold the definition of `addThrice`
--  as appropriate.

theorem rwUnfold (n m : Nat) (h : m = n) : addThrice m = n + (n + n) := by
  sorry

attribute [autogradedProof 1] rwUnfold

--  Rewriting can also be used in places where `rfl` can't, like
--  hypotheses.

def square (n : Nat) : Nat := n * n

example (n : Nat) (h : square n = 16) : n * n = 16 := by
  rw [square] at h
  exact h

--  Aside: `rw? at h` also works on hypotheses:

example (n m : Nat) (h : 2 * n = m * 2) : n + n = m + m := by
  -- use rw? to construct the proof
  rw [Nat.mul_comm, Nat.mul_two, Nat.mul_two] at h
  exact h

--  With the ability to unfold definitions via rewriting, one may wonder
--  why we need simplification rules like `add_zero` and `add_succ`. As
--  mentioned when motivating these rules, they provide some engineering
--  benefits: The rules tend to stay the same even as definitions change,
--  which helps avoid proof breakages. Avoiding such breakages is
--  particularly important with proofs using parts of Lean's standard
--  library, which are often implemented in ways that are very efficient
--  but less friendly to proofs.

--  ## Definitional Simplification with `dsimp`

--  Sometimes when you unfold a definition your hypothesis or goal may
--  become hard to understand. When that happens, it can be useful to
--  simplify it. To apply simplifications similar to those that `rfl` does,
--  but without also trying to close an equality goal, you can use the
--  tactic `dsimp only` or `dsimp only at h`.

example : (fun x => x + 0) n = n := by
  dsimp only -- applies the function to its argument
  rw [Nat.add_zero]

--  If we did not simplify here before attempting to rewrite, we would get
--  an error:

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

--  When `rw` unfolds a definition, it does so one instance at time. Thus
--  each occurrence of a definition needs its own rewrite.

example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  rw [square, square, square] at h
  exact h

--  We have previously seen the same issue with lemmas like `add_zero`,
--  leading to situations in which we have to rewrite multiple times in a
--  row. To make this situation a bit better, we can use the `repeat`
--  tactic combinator, which takes a tactic as its argument and repeats it
--  as many times as it can.

example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  repeat rw [square] at h
  exact h

--  The `repeat` tactic is a simple source of proof automation in Lean, as
--  is the use of simplification via `dsimp` and `rfl`. Lean's full tactic
--  library, and tactic-writing metaprogramming language, offer much more.
--  The Automation chapter will introduce the powerful, and commonly used,
--  automated tactic `simp`, which can sometimes solve complex goals by
--  itself. We'll also talk about other tactic combinators like `repeat`.
--
--  But, using these tools now does not help (in fact, it hurts!) the
--  process of learning logical reasoning, formal theorem proving, and
--  Lean. Additionally, real Lean programmers are careful when using
--  automation: it can hurt the readability of a proof, and real-world Lean
--  is often used to *communicate* a result as much as to prove it. We will
--  continue to use only simple tactics and `rw`, for most of this volume
--  so that you have a firm grasp of both the logic behind the proofs you
--  are writing and the ways to structure those proofs to make your logic
--  clear.

--  ## Redefining Functions and Lemmas over Nats

--  Now that we've switched to using Lean's standard library, we can
--  redefine some of the functions from the last few chapters on `Nat`s.
--  Note that, for the built-in `Nat` type, the patterns `0` and `n + 1`
--  correspond to `Nat.zero` and `Nat.succ n`. Likewise, the pattern
--  `n + 2` is equivalent to `n + 1 + 1`.
--
--  Prove some of these theorems using the techniques we've discussed this
--  chapter.

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

--  Note that we defined these functions in the `Nat` namespace; Lean's
--  naming conventions advise that functions on a type should be defined in
--  that type's namespace in almost all circumstances.
--
--  When we define functions this way, something interesting happens to the
--  way Lean's InfoView prints them. Take a look at the InfoView inside the
--  proof of this theorem before the `rfl` tactic:

theorem Nat.even_add_three (n : Nat) : even (n + 3) = even (n + 1) := by
  rfl

--  Instead of printing the goal the way we wrote it in the theorem
--  statement, Lean prints `(n + 3).even = (n + 1).even`! This is an
--  example of Lean's *field notation*, whereby Lean prints functions
--  inside the namespace of a type *after* their first argument, separated
--  by a `.`. At first glance, this may appear similar to how
--  object-oriented methods work, but it's really just a syntactic
--  variation on the normal function-application style we've seen so far.
--  That is, `Nat.even n` and `n.even` are just different ways to write the
--  exact same term.
--
--  In previous chapters we disabled this notation by putting
--  `set_option pp.fieldNotation false` at the top of each file, but from
--  now on we will leave it enabled, since field notation is recommended in
--  idiomatic Lean developments.
--
--  As an example, observe the difference in how Lean prints the goal in
--  the following two examples:

set_option pp.fieldNotation false

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

set_option pp.fieldNotation true

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

--  ### Exercise (2 stars): even_succ ⭐⭐

--  One inconvenient aspect of our definition of `even n` is the recursive
--  call on `n'` when `n = n' + 2`. This makes proofs about `even n` harder
--  when done by induction on `n`, since we may need an induction
--  hypothesis about `n' + 2`, while induction just gives us one about
--  `n' + 1`. The following lemma proves `even (n + 1)` flips the parity,
--  which gives an alternative characterization that works better with
--  induction. We'll see uses of this theorem in Lists.

theorem Nat.even_succ (n : Nat) :
    (n + 1).even = !(n.even) := by
  sorry

attribute [autogradedProof 2] Nat.even_succ

--  We reprove here for Lean's `Nat` some theorems about `Nat.even` and
--  `Nat.double`, which we had previously proven for our custom
--  `NatPlayground.Nat`.

theorem Nat.even_zero : even 0 = true := by rfl
theorem Nat.double_zero : double 0 = 0 := by rfl
theorem Nat.double_succ (n : Nat) : (n + 1).double = n.double + 2 := by rfl

--  ### Exercise (2 stars): double_add ⭐⭐

theorem Nat.double_add (n : Nat) : n.double = n + n := by
  sorry

attribute [autogradedProof 2] Nat.double_add

--  ### Exercise (2 stars): double_mul ⭐⭐

theorem Nat.double_mul (n : Nat) : n.double = 2 * n := by
  sorry

attribute [autogradedProof 2] Nat.double_mul

--  In the remainder of the book, we use Lean's built-in natural numbers
--  everywhere. We also recommend using `rw?` and `exact?` to search for
--  lemmas (though these should not appear in finished proofs).
--
--  With these tools in hand, we can begin to prove properties about more
--  sophisticated forms of data, beginning with `Lists`.

-- Built on 2026-09-03 19:08 UTC

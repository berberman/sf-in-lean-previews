import LF.Basics

import SFLCompat

--  # Induction: Proof by Induction

--  This chapter shows how to carry out *proofs by induction*, one of the
--  most fundamental reasoning tools in computer science and mathematics,
--  in Lean.

--  ## Separate Compilation

--  Before getting started on this chapter, we need to import all of our
--  definitions from the previous chapter:

--  For this `import` to work, Lean needs to be able to find a compiled
--  version of the previous chapter (`Basics.lean`). This compiled version,
--  called `Basics.olean`, is analogous to the `.class` files compiled from
--  `.java` source files and the `.o` files compiled from `.c` files.
--
--  When using Lake (Lean's build system), the file `lakefile.toml`
--  specifies dependencies and build configuration. Running `lake build`
--  will compile all necessary files in the correct order.
--
--  If you are using VS Code with the Lean 4 extension, compilation happens
--  automatically in the background. When you open a file, the extension
--  compiles its dependencies as needed.
--
--  Troubleshooting:
--
--  - If you get complaints about missing imports, make sure you have run
--    `lake build` from the project root directory in a terminal, at least
--    once.
--
--  - If you modify `Basics.lean`, VS Code will automatically recompile it
--    when you save. You may need to reopen this file or wait for
--    recompilation to finish.
--
--  - If you get errors that seem inconsistent with the source, try running
--    `lake clean` followed by `lake build` to recompile everything from
--    scratch.
--
--    (If you are using the Lean 4 extension for VS Code, you can also
--    restart the extension on the current file via the `Restart File`
--    button in the InfoView. The extension should prompt you to do this if
--    you change things upstream in the dependency tree.)

--  ## Review

--  We reopen the namespace from the previous chapter to group this
--  chapter's definitions and theorems with the custom natural-number
--  development and keep their names distinct from the standard library.
--
--  Now let's review what we learned in Basics using some quiz questions
--  and an exercise.

namespace NatPlayground.Nat

--   ----------------------------------------

--  _Quiz:_

--  Recall the definition of `or`, which has notation `||` and is *not*
--  marked `@[irreducible]`:
--
--      def or (b1 : Bool) (b2 : Bool) : Bool :=
--        match b1 with
--        | true => true
--        | false => b2
--
--  To prove the following theorem, which tactics will we need besides
--  `rfl`?
--
--      theorem review₁ : (true || false) = true
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

--  _Quiz:_

--  What about the next one?
--
--      theorem review₂ (b : Bool) : (true || b) = true
--
--  Which tactics do we need besides `rfl`?
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

--  _Quiz:_

--  What if we change the order of the arguments of `||`?
--
--      theorem review₃ (b : Bool) : (b || true) = true
--
--  Which tactics do we need besides `rfl`?
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

sf_recall
  def add (n : Nat) (m : Nat) : Nat :=
    match m with
    | zero => n
    | succ m' => succ (add n m')

sf_recall statement add_zero : ∀ n : Nat, n + zero = n

sf_recall statement add_succ : ∀ n m : Nat, n + (succ m) = succ (n + m)

--   ----------------------------------------

--  _Quiz:_

--  What about this one? Recall that our `add` function has notation `+`
--  and *is* marked `@[irreducible]`.
--
--      theorem review₄ (n : Nat) : n + zero = n
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

--  _Quiz:_

--  What about this?
--
--      theorem review₅ (n : Nat) : zero + n = n
--
--  (A) none
--
--  (B) `rewrite`
--
--  (C) `cases`
--
--  (D) both `rewrite` and `cases`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

--  ### Exercise (1 star): succ_eq_add_one ⭐

--  One more warm-up exercise. Prove the following theorem, using theorems
--  from Basics:

theorem succ_eq_add_one (n : Nat) : succ n = n + one := by
  rewrite [one_eq_succ_zero, add_succ, add_zero]
  rfl

--  ## Proof by Induction

--  We will introduce proofs by induction on natural numbers, first
--  motivating why induction is needed, and then explaining what it is and
--  how you do it in Lean.

--  ### Motivation

--  We defined `add` to recurse on its *second* argument:

sf_recall
  def add (n : Nat) (m : Nat) : Nat :=
    match m with
    | zero => n
    | succ m' => succ (add n m')

--  For the `add_zero` simplification rule, we were able to prove that
--  `zero` is a neutral element for `+` on the *right* using just `rfl`.

--      theorem add_zero : ∀ (n : Nat), n + zero = n := by
--        intro n
--        rfl
--
--  This worked because `n + zero` reduces to `n` by definition. What if we
--  wanted to prove a rule that `zero` is also a neutral element on the
--  *left*? Just applying `rfl` doesn't work, since the `n` in `zero + n`
--  is an arbitrary unknown number, so the `match` in the definition of `+`
--  can't be reduced.

sf_expect_failure_in
  example (n : Nat) : zero + n = n := by
    rfl    -- doesn't work here!

--  Output:
--    Tactic `rfl` failed: The left-hand side
--      zero + n
--    is not definitionally equal to the right-hand side
--      n
--
--    n : Nat
--    ⊢ zero + n = n

--  And reasoning by cases using `cases` on `n` doesn't get us much
--  further: the branch of the case analysis where we assume `n = zero`
--  goes through just fine, but in the branch where `n = n' + 1` for some
--  `n'` we get stuck in exactly the same way.

sf_expect_failure_in
  example (n : Nat) : zero + n = n := by
    cases n with
    | zero => /- n = zero -/
      rewrite [add_zero]
      rfl
      -- so far so good...
    | succ n' =>   /- n = succ n' -/
      _     -- ...but we're stuck on zero + n'

--  Output:
--    unsolved goals
--    case succ
--    n' : Nat
--    ⊢ zero + succ n' = succ n'

--  We could use `cases` on `n'` to get a bit further, but, since `n` can
--  be arbitrarily large, we'll never get all the way there if we just go
--  on like this.

--  ### Induction: In Principle and in Lean

--  To prove interesting facts about numbers, lists, and other inductively
--  defined sets, we often need a more powerful reasoning principle:
--  *induction*.
--
--  Recall (from a discrete math course, probably) the *principle of
--  induction over natural numbers*: If `P(n)` is some proposition
--  involving a natural number `n` and we want to show that `P` holds for
--  all numbers `n`, we can reason like this:
--
--  - show that `P(zero)` holds;
--  - show that, for any `n'`, if `P(n')` holds, then so does `P(succ n')`;
--  - conclude that `P(n)` holds for all `n`.
--
--  In Lean, the steps are the same: we begin with the goal of proving
--  `P(n)` for all `n` and use the `induction` tactic to break it down into
--  two separate subgoals: one where we must show `P(zero)` and another
--  where we must show `P(n') → P(succ n')`. Here's how this works for the
--  theorem at hand...

theorem zero_add (n : Nat) : zero + n = n := by
  induction n with
  | zero => /- n = zero -/
    rewrite [add_zero]
    rfl
  | succ n' ih => /- n = succ n' -/
    /-
      Goal: zero + (succ n') = succ n'
      We can rewrite `zero + (succ n')` to `succ (zero + n')`.
      Then we can rewrite with the induction hypothesis.
    -/
    rewrite [add_succ, ih]
    rfl

--  Like `cases`, the `induction` tactic takes a `with` clause that
--  specifies the names of the variables to be introduced in the subgoals.
--  Since there are two subgoals (for `zero` and `succ`), the `with` clause
--  has two branches.
--
--  In the first subgoal, `n` is replaced by `zero`. The goal becomes
--  `zero + zero = zero`, which follows by `rewrite [add_zero]` and `rfl`.
--
--  In the second subgoal, `n` is replaced by `succ n'`, and the induction
--  hypothesis `ih : zero + n' = n'` is added to the context. The goal
--  becomes `zero + (succ n') = succ n'`. `add_succ` tells us that
--  `a + (succ b) = succ (a + b)`, so `rewrite [add_succ]` transforms the
--  goal to `succ (zero + n') = succ n'`. Then `rewrite [ih]` rewrites
--  `zero + n'` to `n'`, and the goal becomes `succ n' = succ n'`, which
--  closes with reflexivity.

--  Here's another theorem to try, this time involving equality on natural
--  numbers.

theorem beq_self (n : Nat) : (n == n) = true := by
  induction n with
  | zero =>
    rewrite [zero_beq_zero]
    rfl
  | succ n' ih =>
    rewrite [succ_beq_succ]
    exact ih

--  ### Exercise (2 stars): basic_induction ⭐⭐

--  Prove the following using induction. You might need previously proven
--  results.

theorem zero_mul (n : Nat) :
    zero * n = zero := by
  induction n with
  | zero =>
    rewrite [mul_zero]
    rfl
  | succ n' ih =>
    rewrite [mul_succ, ih, add_zero]
    rfl

theorem succ_add (n m : Nat) :
    (succ n) + m = succ (n + m) := by
  induction m
  case zero =>
    rewrite [add_zero, add_zero]
    rfl
  case succ m' ih =>
    rewrite [add_succ, add_succ, ih]
    rfl

theorem add_comm (n m : Nat) :
    n + m = m + n := by
  induction m with
  | zero =>
    rewrite [add_zero, zero_add]
    rfl
  | succ m' ih =>
    rewrite [add_succ, ih, succ_add]
    rfl

theorem add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  induction p with
  | zero =>
    rewrite [add_zero, add_zero]
    rfl
  | succ p' ih =>
    rewrite [add_succ, add_succ, add_succ, ih]
    rfl

--  ### Tip: The `rw` Tactic

--  As you've probably noticed, a common pattern in Lean proofs is
--  `rewrite [...]` followed by `rfl`. Lean also provides a tactic that
--  combines these two steps: `rw [...]` will automatically close the goal
--  if the rewrite makes the goal true by definition. For example, instead
--  of
--
--      rewrite [double_zero]; rfl
--
--  we could write this:
--
--      rw [double_zero]

--  One small caveat: `rw [...]` only performs a quick reflexivity check
--  after rewriting; it does not unfold every definition. So, in some
--  cases, `rw` may leave a goal that can actually be solved immediately by
--  `rfl`. For example, `rw` does not unfold the definition of `aliasOfTwo`
--  in the following example, and thus needs an explicit `rfl`.

def aliasOfTwo := two

example (n : Nat) (h : n = aliasOfTwo) : n = two := by
  rw [h]
  /- The remaining goal is `aliasOfTwo = two`. -/
  rfl

--  Let's get some practice with using `rw`.

--  THE FOLLOWING DETAILS CAN BE SKIPPED
set_option pp.fieldNotation false
--  END DETAILS

--  ### Exercise (2 stars): double_add ⭐⭐

--  Consider the following function, which doubles its argument:

def double (n : Nat) : Nat :=
  match n with
  | zero    => zero
  | succ n' => succ (succ (double n'))

theorem double_zero : double zero = zero := by rfl
theorem double_succ n : double (succ n) = succ (succ (double n)) := by rfl
attribute [irreducible] double

--  Use induction to prove this simple fact about `double`. Try using `rw`
--  instead of `rewrite`.

theorem double_add (n : Nat) : double n = n + n := by
  induction n with
  | zero       => rw [add_zero, double_zero]
  | succ n' ih => rw [double_succ, ih, add_succ, succ_add]

--  ## Proofs Within Proofs

--  In Lean, as in informal mathematics, large proofs are often broken into
--  sequences of theorems, with later proofs referring to earlier theorems.
--  But sometimes a proof will involve some miscellaneous fact that is too
--  trivial and of too little general interest to bother giving it its own
--  top-level name. In such cases, it is convenient to simply state and
--  prove the required fact "in place." The `have` tactic allows us to do
--  this.

theorem mul_zero_add' (n m : Nat) :
    ((zero + n) + zero) * m = n * m := by
  have h : (zero + n) + zero = n := by
    rw [zero_add, add_zero]
  rw [h]

--  The `have` tactic introduces a local lemma into the proof. We prove it
--  immediately, and it's available as a hypothesis for the rest of the
--  proof.

--  As another example, suppose we want to prove that
--  `(n + m) + (p + q) = (m + n) + (p + q)`. The only difference between
--  the two sides of the `=` is that the arguments `m` and `n` to the first
--  inner `+` are swapped, so it seems we should be able to use the
--  commutativity of addition (`add_comm`) to rewrite one into the other.
--  However, the `rw` tactic is not very smart about *where* it applies the
--  rewrite. There are three uses of `+` here, and `rw [add_comm]` may
--  choose the wrong one...

sf_expect_failure_in
  example (n m p q : Nat) :
     (n + m) + (p + q) = (m + n) + (p + q) := by
    /-
      We just need to swap (n + m) for (m + n)... seems
      like add_comm should do the trick!
      But `rw [add_comm]` might rewrite the wrong `+`!
    -/
    rw [add_comm]

--  Output:
--    unsolved goals
--    n m p q : Nat
--    ⊢ p + q + (n + m) = m + n + (p + q)

--  To use `add_comm` at the point where we need it, we can supply explicit
--  arguments: `rw [add_comm n m]` tells Lean exactly which `+` to rewrite.
--  (We can also use `have` to establish the specific equation we want,
--  then rewrite with it.)

theorem add_rearrange (n m p q : Nat) :
    (n + m) + (p + q) = (m + n) + (p + q) := by
  rw [add_comm n m]

--  ## Formal vs. Informal Proof

--  "Informal proofs are algorithms; formal proofs are code."

--  What constitutes a successful proof of a mathematical claim?
--
--  The question has challenged philosophers for millennia, but a rough and
--  ready answer could be this: A proof of a mathematical proposition `P`
--  is a text that instills in the reader the certainty that `P` is true.
--  That is, a proof is an act of *communication*.
--
--  Acts of communication may involve different sorts of readers. On one
--  hand, the reader can be a program like Lean, in which case the "belief"
--  that is instilled is that `P` can be mechanically derived from a
--  certain set of formal logical rules, and the proof is a recipe that
--  guides the program in checking this fact. Such recipes are *formal*
--  proofs.
--
--  Alternatively, the reader can be a human being, in which case the proof
--  will probably be written in English or some other natural language and
--  will thus necessarily be *informal*. Here, the criteria for success are
--  less clearly specified. A "valid" proof is one that makes the reader
--  believe `P`. But the same proof may be read by many different readers,
--  some of whom may be convinced by a particular way of phrasing the
--  argument, while others may not be. Some readers may be unfamiliar with
--  the area and need the argument spelled out in detail. Other readers,
--  more familiar with the area, may find that extra detail makes it
--  *harder* to follow the argument; all they want is to be told the main
--  ideas, since it is easier for them to fill in the details for
--  themselves than to wade through a written presentation of them.
--  Ultimately, there is no universal standard, because there is no single
--  way of writing an informal proof that will convince every conceivable
--  reader.
--
--  In practice, mathematicians have developed a rich set of conventions
--  and idioms for writing about complex mathematical objects that — at
--  least within a certain community — make communication pretty reliable.
--  The conventions of this stylized form of communication give a
--  reasonably clear standard for judging proofs good or bad.
--
--  Because we are using Lean in this course, we will be working heavily
--  with formal proofs. But this doesn't mean we can completely forget
--  about informal ones! Formal proofs are useful in many ways, but they
--  are typically *not* the most efficient ways of communicating ideas
--  between human beings.
--
--  For example, here is a proof that addition is associative (you might
--  have written something like it yourself, recently...):

theorem add_assoc' (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  induction p with
  | zero       => rw [add_zero, add_zero]
  | succ p' ih => rw [add_succ, add_succ, add_succ, ih]

--  Lean is perfectly happy with this. For a human, however, it is
--  difficult to make much sense of it. We can pass arguments to the
--  `add_succ` theorem to show the structure more clearly...

theorem add_assoc'' (n m p : Nat) :
    add n (add m p) = add (add n m) p := by
  induction p with
  | zero => /- p = zero -/
    rw [add_zero, add_zero]
  | succ p' ih => /- p = succ p', in other words p = p' + 1 -/
    rw [add_succ m p', add_succ n (m + p'), add_succ (n + m) p', ih]

--  ... and if you're used to Lean you might be able to step through the
--  tactics one after the other in your mind and imagine the state of the
--  context and goal stack at each point, but, if the proof were even a
--  little bit more complicated, this would be next to impossible.
--
--  On paper, a (somewhat pedantic) mathematician might write the proof
--  like this:
--
--  - *Theorem*: For any `n`, `m`, and `p`,
--
--        n + (m + p) = (n + m) + p.
--
--  *Proof*: By induction on `p`.
--
--  - First, suppose `p = zero`. We must show that
--
--        n + (m + zero) = (n + m) + zero.
--
--  This follows directly from the definition of `+` (since `x + zero = x`
--  for any `x`).
--
--  - Next, suppose `p = p' + 1` (i.e., `p = succ p'`), where
--
--        n + (m + p') = (n + m) + p'.
--
--  We must now show that
--
--        n + (m + (p' + 1)) = (n + m) + (p' + 1).
--
--  By definition of `+`, both sides rewrite (via `add_succ`) to
--
--        (n + (m + p')) + 1   and   ((n + m) + p') + 1
--
--  respectively, which are equal by the induction hypothesis. *QED*.

--  The overall form of the formal and informal proofs is basically
--  similar, and of course this is no accident: Lean has been designed so
--  that its `induction` tactic generates the same sub-goals, in the same
--  order, as the bullet points that a mathematician would usually write.
--  But there are significant differences of detail: the formal proof is
--  much more explicit in some ways (e.g., the sequence of rewrites) and
--  less explicit in others. In particular, the "proof state" at any given
--  point in the Lean proof is completely implicit, whereas the informal
--  proof reminds the reader several times where things stand.

--  ### Exercise (2 stars): add_comm_informal (Advanced, Optional, Manually graded) ⭐⭐

--  Translate your solution for `add_comm` into an informal proof:
--
--  Theorem: Addition is commutative.
--
--  Proof: ...

--  Let natural numbers `n` and `m` be given. We show `n + m = m + n` by
--  induction on `m`.
--
--  - First, suppose `m = zero`. We must show
--
--      n + zero = zero + n.
--
--  By the definition of `+`, `n + zero = n`, so we now must show
--
--      n = zero + n.
--
--  We have already shown (lemma `zero_add`) that `zero + n = n`. Thus both
--  sides equal `n`.
--
--  - Next, suppose `m = m' + 1` for some `m'`, where `n + m' = m' + n`. We
--    must show that
--
--      n + (m' + 1) = (m' + 1) + n.
--
--  By the definition of `+`, `n + (m' + 1) = (n + m') + 1`, so our new
--  goal is to show
--
--      (n + m') + 1 = (m' + 1) + n.
--
--  By `succ_add`, `(m' + 1) + n = (m' + n) + 1`, so it remains to show
--  `(n + m') + 1 = (m' + n) + 1`. This follows from the induction
--  hypothesis `n + m' = m' + n`.
--
--  *QED*.

--  ### Exercise (2 stars): beq_refl_informal (Optional) ⭐⭐

--  Write an informal proof of the following theorem, using the informal
--  proof of `add_assoc` as a model. Don't just paraphrase the Lean tactics
--  into English!
--
--  Theorem: `(n == n) = true` for any `n`.
--
--  Proof:

--  By induction on `n`.
--
--  - First, suppose `n = zero`. We must show `(zero == zero) = true`. This
--    follows directly from the definition of `beq`.
--
--  - Next, suppose `n = n' + 1`, where `(n' == n') = true`. We must show
--    `(n' + 1 == n' + 1) = true`. This follows directly from the induction
--    hypothesis and the definition of `beq`.
--
--  *QED*.

--  ## Aside: Using Code Actions to Generate Match Skeletons

--  Lean's language server can suggest *code actions*, which are small
--  editor commands that modify the source code.
--
--  In VS Code, a lightbulb icon appears on the left when a code action is
--  available at your cursor.

--  You can click the icon or open the code action menu with `Ctrl + .` on
--  Windows/Linux or `Command + .` on macOS. For more information, see the
--  [Lean 4 VSCode extension
--  manual](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md#code-actions).
--
--  For example, code actions can generate the explicit branches needed for
--  pattern matching. This can be especially useful when working with
--  `match` expressions or with tactics such as `cases` and `induction`,
--  which we saw earlier in the book.

--  Let's look at a code action for `induction`. Suppose we start with the
--  following incomplete proof:

sf_expect_failure_in
  example (n : Nat) : Nat.beq n n = true := by
    induction n

--  Put your cursor on `induction n` and open the code action menu.

--  You should see "Generate an explicit pattern match for 'induction'." in
--  the list. If you choose this action, Lean adds an explicit branch for
--  each constructor:

example (n : Nat) : Nat.beq n n= true := by
  induction n with
  | zero => sorry
  | succ n ih => sorry

--  This gives us the basic structure of the proof without requiring us to
--  write each branch by hand. We can then focus on proving each case.

--  One possible proof is the following.

example (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => exact (beq_self zero)
  | succ n ih => rw [Nat.beq, ih]

--  The same trick also works for `match` expressions. For example, suppose
--  we start with

sf_expect_failure_in
  def isZero (n : Nat) : Bool :=
    match n

--  Lean can generate the missing branches:

sf_expect_failure_in
  def isZero (n : Nat) : Bool :=
    match n with
    | .zero => _
    | .succ n => _

--  Now you just have to replace the holes `_` with your definition. You
--  can use code actions freely to fill out `induction`, `case`, and
--  `match` branches while working with this book.

--  One note: Sometimes the variables the code action chooses are not
--  ideal, so you might want to change them.

--  For example, here is what we get from the code action for `add_comm`

theorem add_comm' (n m : Nat) : n + m = m + n := by
  induction m with
  | zero => sorry
  | succ n ih => sorry -- bad choice of variable `n`, want `m` or `m'` !

--  Notice that the action chose `n` for the `succ` case, even though we
--  are inducting on `m`. Manually updating this variable to either `m` or
--  `m'` will make your proof easier to read.

--  ## More Exercises

--  ### Exercise (1 star): mul_one ⭐

theorem mul_one (p : Nat) :
    one * p = p := by
  induction p with
  | zero       => rw [mul_zero]
  | succ p' ih => rw [mul_succ, ih, succ_eq_add_one]

--  By default, `rewrite` and `rw` rewrite left to right, i.e., they
--  transform the goal (or a hypothesis) from the form on the left side of
--  the equality to the right side. To rewrite from right to left, use
--  `rewrite [← h]` or `rw [← h]`, where `←` is entered as `\l` or `\<-`.

--  ### Exercise (2 stars): mul_two ⭐⭐

theorem mul_two (p : Nat) :
    two * p = p + p := by
  induction p with
  | zero => rw [mul_zero, add_zero]
  | succ p' ih =>
    rw [mul_succ, ih, two_eq_succ_one, succ_eq_add_one, succ_eq_add_one]
    rw [add_assoc, add_assoc, ←add_assoc p' p' one]
    rw [add_comm p' one, add_comm p']

--  ### Exercise (3 stars): mul_comm ⭐⭐⭐

--  Use `have` (or `rw` with explicit arguments) to help prove
--  `add_shuffle3`. You don't need to use induction.

theorem add_shuffle3 (n m p : Nat) : n + m + p = n + p + m := by
  rw [← add_assoc, add_comm m p, add_assoc]

theorem succ_mul (m n : Nat) :
    (succ n) * m = (n * m) + m := by
  induction m with
  | zero => rw [mul_zero, mul_zero, add_zero]
  | succ m ih =>
    rw [mul_succ, ih, add_succ, add_comm _ n,
        add_assoc n _ m, add_comm n, mul_succ, add_succ]

--  Now prove commutativity of multiplication.

theorem mul_comm (m n : Nat) :
    m * n = n * m := by
  induction n with
  | zero =>
    rw [mul_zero, zero_mul]
  | succ n' ih =>
    rw [mul_succ, ih, succ_mul]

--  ### Exercise (3 stars): more_exercises (Optional) ⭐⭐⭐

--  Take a piece of paper. For each of the following theorems, first
--  *think* about whether (a) it can be proved using only simplification
--  and rewriting, (b) it also requires case analysis (`cases`), or (c) it
--  also requires induction. Write down your prediction. Then fill in the
--  proof. (There is no need to turn in your piece of paper; this is just
--  to encourage you to reflect before you hack!)

theorem ble_refl (n : Nat) :
    Nat.ble n n = true := by
  induction n with
  | zero       => rw [zero_ble]
  | succ n' ih => rw [succ_ble_succ]; exact ih

theorem andb_false (b : Bool) :
    (b && false) = false := by
  cases b with
  | false => rw [Bool.false_and]
  | true  => rw [Bool.true_and]

theorem all3_spec (b c : Bool) :
    ((b && c) || ((!b) || (!c))) = true := by
  cases b with
  | true => cases c with
    | false => rfl
    | true => rfl
  | false => rfl

theorem right_distrib (n m p : Nat) :
    (n + m) * p = (n * p) + (m * p) := by
  induction p with
  | zero => rw [mul_zero, mul_zero, mul_zero, add_zero]
  | succ p' ih =>
    rw [mul_succ, mul_succ, mul_succ, ih]
    rw [add_assoc ((n * p') + (m * p')),
        add_shuffle3 (n * p') (m * p'),
        add_assoc ((n * p') + n)]

theorem left_distrib (n m p : Nat) :
    p * (n + m) = (p * n) + (p * m) := by
  rw [mul_comm p, mul_comm p, mul_comm p]
  rw [right_distrib]

theorem mul_assoc (n m p : Nat) :
    n * (m * p) = (n * m) * p := by
  induction p with
  | zero       => rw [mul_zero, mul_zero, mul_zero]
  | succ p' ih => rw [mul_succ, mul_succ, ← ih, left_distrib]

--  ## A New Tactic Combinator: `<;>`

--  Before moving on to the next batch of exercises, let's introduce a
--  simple *tactic combinator*. A tactic combinator combines tactics to
--  form a larger tactic.
--
--  If `t₁` and `t₂` are tactics, then `t₁ <;> t₂` means: first run `t₁`,
--  then run `t₂` on every subgoal produced by `t₁`.
--
--  This is useful when the first tactic splits the goal into several
--  subgoals and all of them can be finished by the second.

example (b : Bool) : (b || true) = true := by
  cases b <;> rfl

--  This is short for:

example (b : Bool) : (b || true) = true := by
  cases b with
  | false => rfl
  | true  => rfl

--  We can also chain `<;>`s. In the next example, `cases` on `b` creates
--  two goals; in each of them, `cases` on `c` splits the goal again; then
--  `rfl` solves all four remaining goals.

example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl

--  For the moment, you should use `<;>` only when the generated subgoals
--  really do have the same proof. If different branches need different
--  arguments, it is usually clearer to write the cases explicitly. We'll
--  discuss some other tactic combinators in the Automation chapter.

--  ## Nat to Bin and Back

namespace NatToBin

--  Recall the `Bin` type we defined in Basics:

inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

--  Before you start working on the next exercise, replace the stub
--  definitions of `incr` and `binToNat`, below, with your solution from
--  Basics, so that this file can be graded on its own.

def incr (m : Bin) : Bin
  := (match m with
  | .z     => .b1 .z
  | .b0 m' => .b1 m'
  | .b1 m' => .b0 (incr m'))

theorem incr_z : incr .z = .b1 .z := (by rfl)
theorem incr_b0 m : incr (.b0 m) = .b1 m := (by rfl)
theorem incr_b1 m : incr (.b1 m) = .b0 (incr m) := (by rfl)

def binToNat (m : Bin) : Nat
  := (match m with
  | .z     => zero
  | .b0 m' => (binToNat m') * two
  | .b1 m' => ((binToNat m') * two) + one)

theorem binToNat_z : binToNat .z = zero := (by rfl)
theorem binToNat_b0 m : binToNat (.b0 m) = mul (binToNat m) two := (by rfl)
theorem binToNat_b1 m : binToNat (.b1 m) = add (mul (binToNat m) two) one := (by rfl)

--  THE FOLLOWING DETAILS CAN BE SKIPPED
attribute [pp_nodot] Bin.b0 Bin.b1
--  END DETAILS

--  In Basics, we did some unit testing of `binToNat`, but we didn't prove
--  its correctness. Now we'll do so.

--  ### Exercise (3 stars): binary_commute ⭐⭐⭐

--  Prove that the following diagram commutes — that is, incrementing a
--  binary number and then converting it to a (standard, unary) natural
--  number yields the same result as first converting it to a natural
--  number and then incrementing:
--
--                            incr
--                Bin ------------------------> Bin
--                 |                             |
--      binToNat   |                             |  binToNat
--                 |                             |
--                 v                             v
--                Nat ------------------------> Nat
--                            succ
--
--  If you want to change your previous definitions of `incr` or `binToNat`
--  to make the property easier to prove, feel free!

theorem bin_to_nat_pres_incr (b : Bin) :
    binToNat (incr b) = (binToNat b) + one := by
  induction b with
  | z =>
    rw [incr_z, binToNat_b1, binToNat_z]
    rw [zero_mul]
  | b0 b' ih =>
    rw [incr_b0, binToNat_b0, binToNat_b1]
  | b1 b' ih =>
    rw [incr_b1, binToNat_b1, binToNat_b0, ih]
    rw [mul_comm, mul_two, mul_comm, mul_two, add_assoc]
    rw [add_shuffle3 _ one]

--  ### Exercise (3 stars): nat_bin_nat ⭐⭐⭐

--  Write a function to convert natural numbers to binary numbers. Also
--  write some simplification lemmas for it.

def natToBin (n : Nat) : Bin := (
  match n with
  | zero    => .z
  | succ n' => incr (natToBin n'))

theorem natToBin_zero : natToBin zero = .z := by rfl
theorem natToBin_succ (m : Nat) : natToBin (succ m) = incr (natToBin m) := by rfl

--  Prove that, if we start with any `Nat`, convert it to `Bin`, and
--  convert it back, we get the `Nat` that we started with.
--
--  Hint: This proof should go through smoothly using the previous exercise
--  about `incr` as a lemma. If not, revisit your definitions of the
--  functions involved and consider whether they are more complicated than
--  necessary: the shape of a proof by induction will match the recursive
--  structure of the program being verified, so make the recursion as
--  simple as possible.

theorem nat_bin_nat (n : Nat) :
    binToNat (natToBin n) = n := by
  induction n with
  | zero =>
    rw [natToBin_zero, binToNat_z]
  | succ n' ih =>
    rw [natToBin_succ, bin_to_nat_pres_incr, ih, ← succ_eq_add_one]

--  ## Bin to Nat and Back (Advanced)

--  The opposite direction — starting with a `Bin`, converting to `Nat`,
--  then converting back to `Bin` — turns out to be problematic: the
--  expected "theorem" does not hold.

sf_expect_failure_in
  example (b : Bin) : natToBin (binToNat b) = b := by

--  Let's explore why it fails and how to prove a modified version of it.
--  We'll start with some lemmas that might seem unrelated but will turn
--  out to be relevant.

--  ### Exercise (2 stars): double_bin (Advanced) ⭐⭐

--  Prove this lemma about `double`, which we defined earlier in the
--  chapter.

theorem double_incr (n : Nat) :
    double (succ n) = (double n) + two := by
  rw [double_succ]
  rw [two_eq_succ_one, one_eq_succ_zero, add_succ, add_succ, add_zero]

--  Now define a similar doubling function for `Bin`.

def doubleBin (b : Bin) : Bin := (
  match b with
  | .z => .z
  | _  => .b0 b)

--  Fill in the characterizing lemmas for this definition below:

theorem doubleBin_z : doubleBin .z = .z := by rfl
theorem doubleBin_b0 (m : Bin) : doubleBin (.b0 m) = .b0 (.b0 m) := by rfl
theorem doubleBin_b1 (m : Bin) : doubleBin (.b1 m) = .b0 (.b1 m) := by rfl

--  Check that your function correctly doubles zero.

theorem double_bin_zero : doubleBin .z = .z := (by rfl)

--  Prove this lemma, which corresponds to `double_incr`.

theorem double_incr_bin (b : Bin) :
    doubleBin (incr b) = incr (incr (doubleBin b)) := by
  cases b with
  | z =>    rw [incr_z, doubleBin_b1, doubleBin_z, incr_z, incr_b1, incr_z]
  | b0 n => rw [incr_b0, doubleBin_b1, doubleBin_b0, incr_b0, incr_b1, incr_b0]
  | b1 n => rw [incr_b1, doubleBin_b0, doubleBin_b1, incr_b0, incr_b1, incr_b1]

--  Let's return to our desired theorem:

sf_expect_failure_in
  example (b : Bin) : natToBin (binToNat b) = b := by

--  The theorem fails because there are some `Bin`s for which we won't
--  necessarily get back to the *original* `Bin`, but instead to an
--  "equivalent" `Bin`. (We deliberately leave this notion informal here so
--  that you can think about it.)
--
--  Explain in a comment, below, why this failure occurs. Your explanation
--  will not be graded, but it's important that you get it clear in your
--  mind before going on to the next part. If you're stuck on this, think
--  about alternative implementations of `doubleBin` that might have failed
--  to satisfy `double_bin_zero` yet otherwise seem correct.

--  The problem is that `zero` has many representations: it can be written
--  `.z`, `.b0 .z`, `.b0 (.b0 .z)`, and so on. For these alternate
--  representations, if you do `binToNat` then `natToBin`, you don't get
--  back what you started with.
--
--  Any other number also has many representations, after applying
--  constructors to the multiple representations of zero.

--  To solve this problem, we can introduce a *normalization* function that
--  selects the simplest `Bin` out of all the equivalent `Bin`s. Then we
--  can prove that the conversion from `Bin` to `Nat` and back again
--  produces that normalized, simplest `Bin`.

--  ### Exercise (4 stars): bin_nat_bin (Advanced) ⭐⭐⭐⭐

--  Define `normalize`. Keep its definition as simple as possible so that
--  later proofs go through smoothly. Do not use `binToNat` or `natToBin`,
--  but do use `doubleBin`.
--
--  Hint: Structure the recursion such that it *always* reaches the end of
--  the `Bin` and *only* processes each bit once. Do not try to "look
--  ahead" at future bits, as this will complicate the proof.

def normalize (b : Bin) : Bin := (
  match b with
  | .z     => .z
  | .b0 b' => doubleBin (normalize b')
  | .b1 b' => incr (doubleBin (normalize b')))

--  Also specify the characterizing lemmas for this definition:

theorem normalize_z : normalize .z = .z := by rfl
theorem normalize_b0 (m : Bin) : normalize (.b0 m) = doubleBin (normalize m) := by rfl
theorem normalize_b1 (m : Bin) : normalize (.b1 m) = incr (doubleBin (normalize m)) := by rfl

--  Next, it would be a good idea to do some `example` proofs to check that
--  your definition of `normalize` works the way you intend before you
--  proceed. They won't be graded, but do fill in a few below.

/- normalize_test_zero -/
example : normalize .z = .z := by rfl
/- normalize_test_1 -/
example : normalize (.b1 .z) = .b1 .z := by rfl
/- normalize_test_2 -/
example : normalize (.b0 .z) = .z := by rfl
/- normalize_test_3 -/
example : normalize (.b0 (.b0 .z)) = .z := by rfl
/- normalize_test_4 -/
example : normalize (.b1 (.b0 .z)) = .b1 .z := by rfl

--  Now that we have defined all of our functions and their characterizing
--  lemmas, we mark the definitions irreducible as usual. From here on,
--  proofs about these definitions should use `rewrite` or `rw`, not `rfl`.

attribute [irreducible] normalize doubleBin natToBin incr binToNat

--  Finally, prove the main theorem. The inductive cases could be a bit
--  tricky.
--
--  Hint: Start by trying to prove the main statement, see where you get
--  stuck, and see if you can find a lemma — perhaps requiring its own
--  inductive proof — that will allow the main proof to make progress. We
--  have one lemma for the `b0` case (which also makes use of
--  `double_incr_bin`) and another for the `b1` case.

theorem incr_doubleBin (b : Bin) :
    incr (doubleBin b) = .b1 b := by
  cases b with
  | z    => rw [doubleBin_z, incr_z]
  | b0 n => rw [doubleBin_b0, incr_b0]
  | b1 n => rw [doubleBin_b1, incr_b0]

theorem natToBin_two_mul n :
    natToBin (mul n two) = doubleBin (natToBin n) := by
  induction n with
  | zero => rw [zero_mul, natToBin_zero, doubleBin_z]
  | succ n' ih =>
    /-
      2 * (n' + 1) = 2 * n' + 2 by Nat.mul_succ.
      natToBin (2 * n' + 2): since +2 is +(1+1), this unfolds to
      incr (incr (natToBin (2 * n'))).
      By ih: = incr (incr (doubleBin (natToBin n'))).
      RHS: doubleBin (natToBin (n' + 1)) = doubleBin (incr (natToBin n')).
      By double_incr_bin: = incr (incr (doubleBin (natToBin n'))). ✓
    -/
    rw [mul_comm, mul_two] at *
    rw [add_succ, succ_add]
    rw [natToBin_succ, natToBin_succ, natToBin_succ]
    rw [ih, ← double_incr_bin]

theorem bin_nat_bin (b : Bin) :
    natToBin (binToNat b) = normalize b := by
  induction b with
  | z =>
    rw [binToNat_z, normalize_z, natToBin_zero]
  | b0 b' ih =>
    rw [binToNat_b0, normalize_b0]
    rw [natToBin_two_mul, ih]
  | b1 b' ih =>
    rw [binToNat_b1, normalize_b1]
    /- Goal: natToBin (binToNat b' * 2 + 1) = incr (doubleBin (normalize b')) -/
    rw [← succ_eq_add_one]
    rw [natToBin_succ]
    rw [natToBin_two_mul, ih]

end NatToBin
end NatPlayground.Nat

-- Built on 2026-09-02 15:30 UTC

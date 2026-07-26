import LF.Basics

import LF.SFLCompat

-- # Induction: Proof by Induction

-- Note to developers (Jonathan Chan  @ionathanch):
--     [BCP: Old comment -- might be out of date?] A lot of the proofs on the
--     naturals rely on how operations on naturals were defined in
--     `Basics.lean`, but in the stdlib they're slightly different (e.g. `sub`
--     is defined via `pred` rather than directly by recursion), and the
--     notations all go through typeclasses, which makes the proofs a lot less
--     direct (e.g. the existing `0 + n` proof refers to `Nat.add_succ`). We
--     should do one of the following:
--
--     1. Not use `+`, `-`, `*` notation and instead use `add`, `sub`, `mul`
--        directly; or
--
--     2. Override stdlib notation with ones pointing to the definitions in
--        `Basics.lean`.

-- Note to developers (Harrison Goldstein  @hgoldstein95):
--     Option 1 is a very reasonable way to go about this if we're attached to
--     arithmetic being the way we teach induction. My primary concern is that
--     operators and type classes are already so confusing that adding another
--     meaning of `+` is liable to throw someone way off. Is there another
--     context we can teach induction in that also doesn't require a ton of
--     background?

-- Note to developers (Jonathan Chan  @ionathanch):
--     `Basics.lean` now overrides the typeclasses for `-`, `*`, and `^`, but
--     not `+`, since that one is pervasive throughout the stdlib and causes
--     problems; I think this works okay and isn't too confusing.
--
--     If we continue doing arithmetic proofs, this is a good place to
--     introduce equational reasoning via `calc`.

-- Note to developers (before next release):
--     `Readers might expect us to add eqn:H annotations to uses of
--     induction, but this changes the shape of the IH in a nasty way! :-(
--     We should at least comment.  (BCP: Is this still relevant in Lean?)
--
--     SOONER: We should also consider adding more examples to clarify
--     the concepts introduced in this chapter. This could help in
--     reinforcing the understanding of induction principles.
--
--     LATER: In 3/22, MRC and BCP discussed "inlining" IndPrinciples
--     into earlier chapters, thus eliminating it as a chapter. This
--     chapter, Induction, is the first place a change would occur.  We
--     would present [nat_ind] here. Then in Lists/Poly we'd present
--     [list_ind], and the rest would go in IndProp and ProofObjects. The
--     main wrinkle is that we'd need to introduce [apply] here instead of
--     in Tactics if we want to preserve the presentation. The discussion
--     is preserved here: https://github.com/DeepSpec/sfdev/pull/471.
--
--     LATER: Now that we've added Steve's nice late-policy exercise in
--     Basics.v, the assignment for that chapter is probably hard enough.  Now
--     what about this chapter?  Can/should we make it a notch or two
--     harder?`

-- ## Separate Compilation

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `This section will need some tidying and rewriting...`

-- Before getting started on this chapter, we need to import all of our
-- definitions from the previous chapter:

-- For this `import` to work, Lean needs to be able to find a compiled version
-- of the previous chapter (`Basics.lean`). This compiled version, called
-- `Basics.olean`, is analogous to the `.class` files compiled from `.java`
-- source files and the `.o` files compiled from `.c` files.

-- When using Lake (Lean's build system), the `lakefile.lean` file specifies
-- dependencies and build configuration. Running `lake build` will compile all
-- necessary files in the correct order.

-- If you are using VS Code with the Lean 4 extension, compilation happens
-- automatically in the background. When you open a file, the extension will
-- compile its dependencies as needed.

-- Troubleshooting:

-- - If you get complaints about missing imports, make sure you have run
--   `lake build` from the project root directory at least once.

-- - If you modify `Basics.lean`, VS Code will automatically recompile it when
--   you save. You may need to reopen this file or wait for recompilation to
--   finish.

-- - If you get errors that seem inconsistent with the source, try running
--   `lake clean` followed by `lake build` to recompile everything from scratch.

-- - If you are using the Lean 4 extension for VS Code, you can also restart the
--   extension on the current file via the `Restart File` button in the
--   InfoView. The extension will often prompt you do this if you change things
--   upstream in the dependency tree.

namespace NatPlayground.Nat

-- ## Review

-- _Quiz:_

-- To prove the following theorem, which tactics will we need besides `intro`
-- and `rfl`? (A) none, (B) `rewrite`, (C) `cases`, (D) both `rewrite` and
-- `cases`, or (E) can't be done with the tactics we've seen.

--       theorem review1 : (true || false) = true

-- _Quiz:_

-- What about the next one?

--       theorem review2 : ∀ b, (true || b) = true

-- Which tactics do we need besides `intro` and `rfl`? (A) none (B) `rewrite`,
-- (C) `cases`, (D) both `rewrite` and `cases`, or (E) can't be done with the
-- tactics we've seen.

-- _Quiz:_

-- What if we change the order of the arguments of `||`?

--       theorem review3 : ∀ b, (b || true) = true

-- Which tactics do we need besides `intro` and `rfl`? (A) none (B) `rewrite`,
-- (C) `cases`, (D) both `rewrite` and `cases`, or (E) can't be done with the
-- tactics we've seen.

-- _Quiz:_

-- What about this one? (Recall that in Lean, `Nat.add` recurses on the
-- *second* argument: `n + zero = n` by definition, and
-- `n + (m + 1) = (n + m) + 1` by definition.)

--       theorem review4 : ∀ n : Nat, n + zero = n

-- (A) none, (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`, or
-- (E) can't be done with the tactics we've seen.

-- _Quiz:_

-- What about this?

--       theorem review5 : ∀ n : Nat, zero + n = n

-- (A) none, (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`, or
-- (E) can't be done with the tactics we've seen.

-- ### Exercise (1 star): succ_eq_add_one ⭐

-- Prove the following theorem, using theorems from Basics.

theorem succ_eq_add_one : ∀ n : Nat, succ n = n + one := by
  all_goals
    intro n
    rewrite [one_eq_succ_zero, add_succ, add_zero]
    rfl

-- ### Proof by Induction

-- We defined `add` to recurse on its *second* argument:

-- def add (n : Nat) (m : Nat) : Nat :=
--     match m with
--     | zero => n
--     | succ m' => succ (add n m')

-- This means `n + zero` reduces to `n` by definition, but `zero + n` does
-- *not*.

-- In `add_zero`, we were able to prove that `zero` is a neutral element for
-- `+` on the *right* using just `rfl`:

-- theorem add_zero : forall (n : Nat), n + zero = n := by
--     intro n
--     rfl

-- But the proof that it is also a neutral element on the *left* can't be done
-- in the same simple way. Just applying `rfl` doesn't work, since the `n` in
-- `zero + n` is an arbitrary unknown number, so the `match` in the definition
-- of `+` can't be simplified.

example : ∀ n : Nat, zero + n = n := by
  intro n
  -- `rfl` doesn't work here!
  sorry

-- And reasoning by cases using `cases n` doesn't get us much further: the
-- branch of the case analysis where we assume `n = zero` goes through just
-- fine, but in the branch where `n = n' + 1` for some `n'` we get stuck in
-- exactly the same way.

example : ∀ n : Nat, zero + n = n := by
  intro n
  cases n with
  | zero => /- n = zero -/
    rewrite [add_zero]
    rfl
    -- so far so good...
  | succ n' =>   /- n = succ n' -/
    -- ...but we're stuck on zero + n'
    sorry

-- We could use `cases n'` to get a bit further, but, since `n` can be
-- arbitrarily large, we'll never get all the way there if we just go on like
-- this.

-- To prove interesting facts about numbers, lists, and other inductively
-- defined sets, we often need a more powerful reasoning principle:
-- *induction*.

-- Recall (from a discrete math course, probably) the *principle of induction
-- over natural numbers*: If `P(n)` is some proposition involving a natural
-- number `n` and we want to show that `P` holds for all numbers `n`, we can
-- reason like this:

-- - show that `P(zero)` holds;
-- - show that, for any `n'`, if `P(n')` holds, then so does `P(succ n')`;
-- - conclude that `P(n)` holds for all `n`.

-- In Lean, the steps are the same: we begin with the goal of proving `P(n)`
-- for all `n` and use the `induction` tactic to break it down into two
-- separate subgoals: one where we must show `P(zero)` and another where we
-- must show `P(n') → P(succ n')`. Here's how this works for the theorem at
-- hand...

theorem zero_add : ∀ n : Nat, zero + n = n := by
  intro n
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

-- Like `cases`, the `induction` tactic takes a `with` clause that specifies
-- the names of the variables to be introduced in the subgoals. Since there
-- are two subgoals (for `zero` and `succ`), the `with` clause has two
-- branches.

-- In the first subgoal, `n` is replaced by `zero`. The goal becomes
-- `zero + zero = zero`, which follows by `rfl`.

-- In the second subgoal, `n` is replaced by `succ n'`, and the induction
-- hypothesis `ih : zero + n' = n'` is added to the context. The goal becomes
-- `zero + (succ n') = succ n'`. `add_succ` tells us that
-- `a + (succ b) = succ (a + b)`, so `rewrite [add_succ]` transforms the goal
-- to `succ (zero + n') = succ n'`. Then `rewrite [ih]` rewrites `zero + n'`
-- to `n'`, and the goal becomes `succ n' = succ n'`, which closes with
-- reflexivity.

theorem beq_self : ∀ n : Nat,
    (n == n) = true := by
  all_goals
    intro n
    induction n with
    | zero =>
      rewrite [zero_zero_beq_true]
      rfl
    | succ n' ih =>
      rewrite [succ_succ_beq]
      exact ih

-- Note to developers (Roger Burtonpatel  @rogerburtonpatel):
--     `We need to make sure this section below is true! It won't be once we switch
--          to the indexed style.`

-- Up until this point, we have been explicitly writing out all the parameters
-- to theorems with ∀s, which makes us introduce them explicitly with `intro`
-- before we can use them. A more Lean-idiomatic way is to write them on the
-- left side of the `:` in the theorem statement, which introduces them
-- automatically. So, the statement of `beq_self` that we just wrote could
-- also be:

-- `theorem beq_self (n : Nat) : (n == n) = true := by ...`

-- When written this way, we don't need to `intro n` at the start of the
-- proof, as `n` will already be in the context when we begin. We will prefer
-- this style going forward.

-- ### Exercise (2 stars): basic_induction ⭐⭐

-- Prove the following using induction. You might need previously proven
-- results.

theorem zero_mul (n : Nat) :
    zero * n = zero := by
  all_goals
    induction n with
    | zero =>
      rewrite [mul_zero]
      rfl
    | succ n' ih =>
      rewrite [mul_succ, ih, add_zero]
      rfl

theorem succ_add (n m : Nat) :
    (succ n) + m = succ (n + m) := by
  all_goals
    induction m
    case zero =>
      rewrite [add_zero, add_zero]
      rfl
    case succ m' ih =>
      rewrite [add_succ, add_succ, ih]
      rfl

theorem add_comm (n m : Nat) :
    n + m = m + n := by
  all_goals
    induction m with
    | zero =>
      rewrite [add_zero, zero_add]
      rfl
    | succ m' ih =>
      rewrite [add_succ, ih, succ_add]
      rfl

theorem add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  all_goals
    induction p with
    | zero =>
      rewrite [add_zero, add_zero]
      rfl
    | succ p' ih =>
      rewrite [add_succ, add_succ, add_succ, ih]
      rfl

-- ### Exercise (2 stars): double_plus ⭐⭐

-- Consider the following function, which doubles its argument:

-- Note to developers (NOW):
--     `Rule rewrite
--
--     BCP: What is "ASSUME HIDDEN"??
--     ASSUME HIDDEN`

def double (n : Nat) : Nat :=
  match n with
  | zero    => zero
  | succ n' => succ (succ (double n'))

theorem double_zero : double zero = zero := by rfl
theorem double_succ : ∀ n, double (succ n) = succ (succ (double n)) := by
  intro n; rfl

attribute [irreducible] double

-- Note to developers (Claude, NOW):
--     The `ASSUME HIDDEN` / `END ASSUME` region markers around this exercise
--     are unhandled: `ASSUME HIDDEN` got swept into the developer note above,
--     and this bare `END ASSUME` line renders as stray book prose in **all
--     three** build products. (See BCP's "What is ASSUME HIDDEN??" note
--     above.) Either implement the marker or delete both lines.

-- END ASSUME

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `We need better typesetting for displays like the following ones:`

-- ### Tip: the `rw` tactic

-- As you've probably noticed, a common pattern in Lean proofs is
-- `rewrite [...]` followed by `rfl`. There is a tactic that combines these
-- two steps: `rw [...]` will automatically close the goal if the rewrite
-- makes the goal true by definition. For example, instead of writing

--   rewrite [double_zero]; rfl

-- We could write this:

--   rw [double_zero]

-- Using `rw` in your proofs is optional, but it will save you time (and is
-- better style).

-- (One small caveat: `rw [...]` only performs a quick reflexivity check after
-- rewriting; it does not unfold every definition. So, in rare cases, `rw` may
-- leave a goal that is still solved immediately by `rfl`.)

def aliasOfTwo := two

example (n : Nat) (h : n = aliasOfTwo) : n = two := by
  rw [h]
  /- The remaining goal is `aliasOfTwo = two`. -/
  rfl

-- Use induction to prove this simple fact about `double`. Experiment with
-- using `rw` instead of `rewrite` as well.

theorem double_add (n : Nat) : double n = n + n := by
  all_goals
    induction n with
    | zero       => rw [add_zero, double_zero]
    | succ n' ih => rw [double_succ, ih, add_succ, succ_add]

-- ### Exercise (2 stars): beq_refl ⭐⭐

-- The following theorem relates the computational equality `beq` on `Nat`
-- with the definitional equality `=` on `Bool`.

theorem beq_refl (n : Nat) :
    (n == n) = true := by
  all_goals
    induction n with
    | zero       => rw [zero_zero_beq_true]
    | succ n' ih => rw [succ_succ_beq, ih]

-- ### Exercise (2 stars): even_succ ⭐⭐

-- Here's a useful theorem that proves `even (n + 1)` flips the parity. This
-- will facilitate proofs by induction on `n`:

-- One inconvenient aspect of our definition of `even n` is the recursive call
-- on `n - two`. This makes proofs about `even n` harder when done by
-- induction on `n`, since we may need an induction hypothesis about
-- `n - two`. The following lemma gives an alternative characterization of
-- `even (succ n)` that works better with induction:

-- (Tip: To expand the body of `even` in a proof, use `rewrite [even]` or
-- `rw [even]`.)

theorem even_succ (n : Nat) :
    even (succ n) = !even n := by
  all_goals
    induction n with
    | zero =>
      rw [even_zero, even_one]
      rfl
    | succ n' ih =>
      rw [even, ih, not_involutive]

-- ## Proofs Within Proofs

-- In Lean, as in informal mathematics, large proofs are often broken into a
-- sequence of theorems, with later proofs referring to earlier theorems. But
-- sometimes a proof will involve some miscellaneous fact that is too trivial
-- and of too little general interest to bother giving it its own top-level
-- name. In such cases, it is convenient to be able to simply state and prove
-- the required fact "in place". The `have` tactic allows us to do this.

theorem mult_zero_plus' (n m : Nat) :
    ((zero + n) + zero) * m = n * m := by
  have h : (zero + n) + zero = n := by
    rw [zero_add, add_zero]
  rw [h]

-- The `have` tactic introduces a local lemma into the proof. We prove it
-- immediately, and then it's available as a hypothesis for the rest of the
-- proof.

-- As another example, suppose we want to prove that
-- `(n + m)
-- + (p + q) = (m + n) + (p + q)`. The only difference between the
-- two sides of the `=` is that the arguments `m` and `n` to the first inner
-- `+` are swapped, so it seems we should be able to use the commutativity of
-- addition (`add_comm`) to rewrite one into the other. However, the `rw`
-- tactic is not very smart about *where* it applies the rewrite. There are
-- three uses of `+` here, and `rw [add_comm]` may affect the wrong one...

example (n m p q : Nat) :
   (n + m) + (p + q) = (m + n) + (p + q) := by
  /-
    We just need to swap (n + m) for (m + n)... seems
    like add_comm should do the trick!
    But `rw [add_comm]` might rewrite the wrong `+`!
  -/
  rw [add_comm]
  sorry

theorem plus_rearrange (n m p q : Nat) :
    (n + m) + (p + q) = (m + n) + (p + q) := by
  rw [add_comm n m]

-- ## Formal vs. Informal Proof

-- "Informal proofs are algorithms; formal proofs are code."

-- What constitutes a successful proof of a mathematical claim?

-- The question has challenged philosophers for millennia, but a rough and
-- ready answer could be this: A proof of a mathematical proposition `P` is a
-- written (or spoken) text that instills in the reader or hearer the
-- certainty that `P` is true -- an unassailable argument for the truth of
-- `P`. That is, a proof is an act of communication.

-- Acts of communication may involve different sorts of readers. On one hand,
-- the "reader" can be a program like Lean, in which case the "belief" that is
-- instilled is that `P` can be mechanically derived from a certain set of
-- formal logical rules, and the proof is a recipe that guides the program in
-- checking this fact. Such recipes are *formal* proofs.

-- Alternatively, the reader can be a human being, in which case the proof
-- will probably be written in English or some other natural language and will
-- thus necessarily be *informal*. Here, the criteria for success are less
-- clearly specified. A "valid" proof is one that makes the reader believe
-- `P`. But the same proof may be read by many different readers, some of whom
-- may be convinced by a particular way of phrasing the argument, while others
-- may not be. Some readers may be particularly pedantic, inexperienced, or
-- just plain thick-headed; the only way to convince them will be to make the
-- argument in painstaking detail. Other readers, more familiar in the area,
-- may find all this detail so overwhelming that they lose the overall thread;
-- all they want is to be told the main ideas, since it is easier for them to
-- fill in the details for themselves than to wade through a written
-- presentation of them. Ultimately, there is no universal standard, because
-- there is no single way of writing an informal proof that will convince
-- every conceivable reader.

-- In practice, however, mathematicians have developed a rich set of
-- conventions and idioms for writing about complex mathematical objects that
-- -- at least within a certain community -- make communication fairly
-- reliable. The conventions of this stylized form of communication give a
-- reasonably clear standard for judging proofs good or bad.

-- Because we are using Lean in this course, we will be working heavily with
-- formal proofs. But this doesn't mean we can completely forget about
-- informal ones! Formal proofs are useful in many ways, but they are *not*
-- very efficient ways of communicating ideas between human beings.

-- For example, here is a proof that addition is associative (you might have
-- written it yourself, earlier in this chapter!):

theorem add_assoc' (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  induction p with
  | zero       => rw [add_zero, add_zero]
  | succ p' ih => rw [add_succ, add_succ, add_succ, ih]

-- Lean is perfectly happy with this. For a human, however, it is difficult to
-- make much sense of it. We can pass arguments to the `add_succ` theorems to
-- show the structure more clearly...

-- Note to developers (Jonathan Chan  @ionathanch):
--     `This would be a great location to introduce `calc`!`

theorem add_assoc'' (n m p : Nat) :
    add n (add m p) = add (add n m) p := by
  induction p with
  | zero => /- p = zero -/
    rw [add_zero, add_zero]
  | succ p' ih => /- p = p' + 1 -/
    rw [add_succ m p', add_succ n (m + p'), add_succ (n + m) p', ih]

-- ... and if you're used to Lean you might be able to step through the
-- tactics one after the other in your mind and imagine the state of the
-- context and goal stack at each point, but if the proof were even a little
-- bit more complicated this would be next to impossible.

-- A (pedantic) mathematician might write the proof something like this:

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `Again, the math displays need to be displayed!`

-- - *Theorem*: For any `n`, `m` and `p`,

--         n + (m + p) = (n + m) + p.

-- *Proof*: By induction on `p`.

-- - First, suppose `p = zero`. We must show that

--           n + (m + zero) = (n + m) + zero.

-- This follows directly from the definition of `+` (since `x + zero = x` for
-- any `x`).

-- - Next, suppose `p = p' + 1`, where

--           n + (m + p') = (n + m) + p'.

-- We must now show that

--           n + (m + (p' + 1)) = (n + m) + (p' + 1).

-- By the definition of `+`, both sides reduce to

--           (n + (m + p')) + 1   and   ((n + m) + p') + 1

-- respectively, which are equal by the induction hypothesis. *Qed*.

-- The overall form of the proof is basically similar, and of course this is
-- no accident: Lean has been designed so that its `induction` tactic
-- generates the same sub-goals, in the same order, as the bullet points that
-- a mathematician would usually write. But there are significant differences
-- of detail: the formal proof is much more explicit in some ways (e.g., the
-- use of `rfl`) but much less explicit in others (in particular, the "proof
-- state" at any given point in the Lean proof is completely implicit, whereas
-- the informal proof reminds the reader several times where things stand).

-- ### Exercise (2 stars): add_comm_informal (Advanced, manually graded) ⭐⭐

-- Translate your solution for `add_comm` into an informal proof:

-- Theorem: Addition is commutative.

-- Proof:

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `Somebody please check that this typesets nicely!  (I doubt it does...) Ditto below.
--     SOLUTION`

-- Let natural numbers `n` and `m` be given. We show `n + m = m +
-- n` by
-- induction on `m`.

-- - First, suppose `m = zero`. We must show `n + zero = zero + n`. By the
--   definition of `+`, `n + zero = n`. We have already shown (lemma `zero_add`)
--   that `zero + n = n`. Thus both sides equal `n`.

-- - Next, suppose `m = m' + 1` for some `m'`, where `n + m' = m'
--   + n`. We must
--   show that `n + (m' + 1) = (m' + 1) + n`. By the definition of `+`,
--   `n + (m' + 1) = (n + m') + 1`. By `succ_add`,
--   `(m' + 1) + n = (m' + n) + 1`. By the induction hypothesis,
--   `n + m' = m' + n`, so both sides equal `(m' + n) + 1`.

-- ### Exercise (2 stars): beq_refl_informal ⭐⭐

-- Write an informal proof of the following theorem, using the informal proof
-- of `add_assoc` as a model. Don't just paraphrase the Lean tactics into
-- English!

-- Theorem: `(n == n) = true` for any `n`.

-- Proof:

-- By induction on `n`.

-- - First, suppose `n = zero`.  We must show `(zero == zero) = true`.  This
-- follows directly from the definition of `beq`.

-- - Next, suppose `n = n' + 1`, where `(n' == n') = true`.  We
-- must show `(n' + 1 == n' + 1) = true`. This
-- follows directly from the induction hypothesis and the
-- definition of `beq`.

-- ## More Exercises

-- Tip: By default, `rewrite` and `rw` rewrite left to right, i.e., they
-- transform the hypothesis or goal being rewritten from the form on the left
-- side of the equality to the right side. To rewrite from right to left, use
-- `rewrite [← h]` or `rw [← h]`, where `←` is entered as `\l` or `\<-`.

-- ### Exercise (1 star): mul_one ⭐

theorem mul_one (p : Nat) :
    one * p = p := by
  all_goals
    induction p with
    | zero       => rw [mul_zero]
    | succ p' ih => rw [mul_succ, ih, succ_eq_add_one]

-- ### Exercise (2 stars): mul_two ⭐⭐

theorem mul_two (p : Nat) :
    two * p = p + p := by
  all_goals
    induction p with
    | zero => rw [mul_zero, add_zero]
    | succ p' ih =>
      rw [mul_succ, ih, two_eq_succ_one, succ_eq_add_one, succ_eq_add_one]
      rw [add_assoc, add_assoc, ←add_assoc p' p' one]
      rw [add_comm p' one, add_comm p']

-- ### Exercise (3 stars): mul_comm ⭐⭐⭐

-- Use `have` (or `rw` with explicit arguments) to help prove `add_shuffle3`.
-- You don't need to use induction yet.

-- Note: By default, `rewrite` and `rw` rewrite left-to-right. To rewrite from
-- right to left, use `rw [← h]`, where `←` is typed as `\l` or `\<-`.

theorem add_shuffle3 : ∀ n m p : Nat,
    add (add n m) p = add (add n p) m := by
  all_goals
    intro n m p
    rw [← add_assoc, add_comm m p, add_assoc]

-- Note to developers (Claude, NOW):
--     Rendering bug (all three build products look wrong). This helper-lemma
--     block wraps its **entire** contents in the
--     `-- SOLUTION`/`-- END SOLUTION` comment-marker idiom, which the Verso
--     HTML build does not process (only the `solution!` tactic is handled).
--     Result: in **student** and **terse** the block renders empty with a
--     spurious `unexpected end of input` error and a doubled
--     `-- FILL IN HERE`; in **solutions** the lemma is shown but the literal
--     `-- SOLUTION` / `-- END SOLUTION` comment lines leak into the displayed
--     code. (The generated `.lean` files are correct.) Fix by expressing
--     `succ_mul` with the `solution!` tactic instead of the comment markers.

theorem succ_mul (m n : Nat) :
    (succ n) * m = (n * m) + m := by
  induction m with
  | zero => rw [mul_zero, mul_zero, add_zero]
  | succ m ih =>
    rw [mul_succ, ih, add_succ, add_comm _ n,
        add_assoc n _ m, add_comm n, mul_succ, add_succ]

-- Now prove commutativity of multiplication.

theorem mul_comm (m n : Nat) :
    m * n = n * m := by
  all_goals
    induction n with
    | zero =>
      rw [mul_zero, zero_mul]
    | succ n' ih =>
      rw [mul_succ, ih, succ_mul]

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `This comment is placed a bit awkwardly: In the terse version, we
--     usually skim past these exercises, but now we'll need to pause and look
--     at how <;> works...
--     TERSE`

-- New tactic combinator: `t₁ <;> t₂` runs `t₁`, then runs `t₂` on every
-- subgoal produced by `t₁`.

-- Before moving on to the next batch of exercises, let's introduce one small
-- *tactic combinator*. A tactic combinator combines tactics to form a larger
-- tactic.

-- If `t₁` and `t₂` are tactics, then `t₁ <;> t₂` means: run `t₁`, then run
-- `t₂` on every subgoal produced by `t₁`.

-- This is useful when one tactic splits the goal into several subgoals and
-- all of them can be finished in the same way.

example (b : Bool) : (b || true) = true := by
  cases b <;> rfl

-- This is short for:

example (b : Bool) : (b || true) = true := by
  cases b with
  | false => rfl
  | true  => rfl

-- We can also chain `<;>`s. In the next example, `cases b` creates two goals;
-- in each of them, `cases c` splits the goal again; then `rfl` solves all
-- four remaining goals.

example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl

-- Use `<;>` when the generated subgoals really do have the same proof. If
-- different branches need different arguments, it is usually clearer to write
-- the cases explicitly.

-- ### Exercise (3 stars): more_exercises ⭐⭐⭐

-- Take a piece of paper. For each of the following theorems, first *think*
-- about whether (a) it can be proved using only simplification and rewriting,
-- (b) it also requires case analysis (`cases`), or (c) it also requires
-- induction. Write down your prediction. Then fill in the proof. (There is no
-- need to turn in your piece of paper; this is just to encourage you to
-- reflect before you hack!) Some of these proofs can be shortened with `<;>`
-- when several generated subgoals have the same proof.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `Is that the main reason for introducing <;> here?  Seems weak if so.
--     Could we consider moving it later?`

theorem ble_refl (n : Nat) :
    ble n n = true := by
  all_goals
    induction n with
    | zero       => rw [zero_ble]
    | succ n' ih => rw [succ_ble_succ]; exact ih

theorem andb_false (b : Bool) :
    (b && false) = false := by
  all_goals
    cases b with
    | false => rw [Bool.false_and]
    | true  => rw [Bool.true_and]

theorem all3_spec (b c : Bool) :
    (b && c) || ((!b) || (!c)) = true := by
  all_goals
    cases b with
    | true  => cases c <;> rfl
    | false => rfl

theorem right_distrib (n m p : Nat) :
    (n + m) * p = (n * p) + (m * p) := by
  all_goals
    induction p with
    | zero => rw [mul_zero, mul_zero, mul_zero, add_zero]
    | succ p' ih =>
      rw [mul_succ, mul_succ, mul_succ, ih]
      rw [add_assoc ((n * p') + (m * p')),
          add_shuffle3 (n * p') (m * p'),
          add_assoc ((n * p') + n)]

theorem left_distrib (n m p : Nat) :
    p * (n + m) = (p * n) + (p * m) := by
  all_goals
    rw [mul_comm p, mul_comm p, mul_comm p]
    rw [right_distrib]

theorem mul_assoc (n m p : Nat) :
    n * (m * p) = (n * m) * p := by
  all_goals
    induction p with
    | zero       => rw [mul_zero, mul_zero, mul_zero]
    | succ p' ih => rw [mul_succ, mul_succ, ← ih, left_distrib]

-- ### Nat to Bin and Back to Nat

namespace NatToBin

-- Recall the `Bin` type we defined in Basics:

inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

-- Before you start working on the next exercise, replace the stub definitions
-- of `incr` and `binToNat`, below, with your solution from Basics. That will
-- make it possible for this file to be graded on its own.

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

attribute [pp_nodot] Bin.b0 Bin.b1

-- In Basics, we did some unit testing of `binToNat`, but we didn't prove its
-- correctness. Now we'll do so.

-- ### Exercise (3 stars): binary_commute ⭐⭐⭐

-- Note to developers (Daniel Sainati  @dsainati1, before next release):
--     `This is a very category theoretic way to present
--        this idea. Is this the most useful way to convey this to
--        an audience who is presumably unfamiliar with commutative diagrams?
--
--     BCP: I think it's fine, though the english version could precede the diagram
--     instead of following it...`

-- Prove that the following diagram commutes:

--          incr Bin ----------------------> Bin
--              |                             |
--   binToNat   |                             |  binToNat
--              |                             |
--              v                             v
--             Nat ------------------------> Nat
--                         succ

-- That is, incrementing a binary number and then converting it to a (unary)
-- natural number yields the same result as first converting it to a natural
-- number and then incrementing.

-- If you want to change your previous definitions of `incr` or `binToNat` to
-- make the property easier to prove, feel free!

theorem bin_to_nat_pres_incr (b : Bin) :
    binToNat (incr b) = (binToNat b) + one := by
  all_goals
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

-- ### Exercise (3 stars): nat_bin_nat ⭐⭐⭐

-- Write a function to convert natural numbers to binary numbers. Also write
-- some simplification lemmas for it.

def natToBin (n : Nat) : Bin := (
  match n with
  | zero    => .z
  | succ n' => incr (natToBin n'))

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     `How to hide these theorem statements so that students can get practice writing them?`

-- Note to developers (Claude, NOW):
--     The developer discussion below is not wrapped in a note, so it renders
--     as ordinary book prose in **all three** build products (a stray "From
--     GitHub: CH: David set it up so that if you put: `-- SOLUTION`
--     `-- END SOLUTION` …" block). It should be a `:::dev` note or deleted.
--     NB it also documents the intended behaviour of the
--     `-- SOLUTION`/`-- END SOLUTION` idiom that is currently mis-rendering
--     elsewhere in this chapter.

-- From GitHub: CH: David set it up so that if you put: -- SOLUTION -- END
-- SOLUTION

-- in an exercise that it will turn into -- FILL IN HERE in both student
-- version of the Lean files and the generated HTML.

theorem natToBin_zero : natToBin zero = .z := (by rfl)
theorem natToBin_succ m : natToBin (succ m) = incr (natToBin m) := (by rfl)

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     `Could these be moved later so that at least the reader has the chance to do the exercise
--     before encountering them?`

-- Prove that, if we start with any `Nat`, convert it to `Bin`, and convert it
-- back, we get the same `Nat` which we started with.

-- Hint: This proof should go through smoothly using the previous exercise
-- about `incr` as a lemma. If not, revisit your definitions of the functions
-- involved and consider whether they are more complicated than necessary: the
-- shape of a proof by induction will match the recursive structure of the
-- program being verified, so make the recursions as simple as possible.

theorem nat_bin_nat (n : Nat) :
    binToNat (natToBin n) = n := by
  all_goals
    induction n with
    | zero =>
      rw [natToBin_zero, binToNat_z]
    | succ n' ih =>
      rw [natToBin_succ, bin_to_nat_pres_incr, ih, ← succ_eq_add_one]

-- ### Bin to Nat and Back to Bin (Advanced)

-- The opposite direction -- starting with a `Bin`, converting to `Nat`, then
-- converting back to `Bin` -- turns out to be problematic. That is, the
-- following theorem does not hold.

example : ∀ b, natToBin (binToNat b) = b := by sorry

-- Let's explore why this theorem fails and how to prove a modified version of
-- it. We'll start with some lemmas that might seem unrelated but will turn
-- out to be relevant.

-- ### Exercise (2 stars): double_bin (Advanced) ⭐⭐

-- Prove this lemma about `double`, which we defined earlier in the chapter.

theorem double_incr (n : Nat) :
    double (succ n) = (double n) + two := by
  all_goals
    rw [double_succ]
    rw [two_eq_succ_one, one_eq_succ_zero, add_succ, add_succ, add_zero]

-- Now define a similar doubling function for `Bin`.

def doubleBin (b : Bin) : Bin := (
  match b with
  | .z => .z
  | _  => .b0 b)

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     `How to hide these theorem statements so that students can get practice writing them?`

theorem doubleBin_z : doubleBin .z = .z := (by rfl)
theorem doubleBin_b0 m : doubleBin (.b0 m) = .b0 (.b0 m) := (by rfl)
theorem doubleBin_b1 m : doubleBin (.b1 m) = .b0 (.b1 m) := (by rfl)

-- Check that your function correctly doubles zero.

example : doubleBin .z = .z := (by rfl)

-- Prove this lemma, which corresponds to `double_incr`.

theorem double_incr_bin (b : Bin) :
    doubleBin (incr b) = incr (incr (doubleBin b)) := by
  all_goals
    cases b with
    | z =>    rw [incr_z, doubleBin_b1, doubleBin_z, incr_z, incr_b1, incr_z]
    | b0 n => rw [incr_b0, doubleBin_b1, doubleBin_b0, incr_b0, incr_b1, incr_b0]
    | b1 n => rw [incr_b1, doubleBin_b0, doubleBin_b1, incr_b0, incr_b1, incr_b1]

-- Let's return to our desired theorem:

example b : natToBin (binToNat b) = b := by sorry

-- The theorem fails because there are some `Bin` such that we won't
-- necessarily get back to the *original* `Bin`, but instead to an
-- "equivalent" `Bin`. (We deliberately leave that notion undefined here for
-- you to think about.)

-- Explain in a comment, below, why this failure occurs. Your explanation will
-- not be graded, but it's important that you get it clear in your mind before
-- going on to the next part. If you're stuck on this, think about alternative
-- implementations of `doubleBin` that might have failed to satisfy
-- `double_bin_zero` yet otherwise seem correct.

-- The problem is that `zero` has many representations: it can be written
-- `.z`, `.b0 .z`, `.b0 (.b0 .z)`, and so on.  For these alternate
-- representations, if you do `binToNat` then `natToBin`, you
-- don't get back what you started with.

-- Any other number also has many representations, after applying
-- constructors to the multiple representations of zero.

-- To solve that problem, we can introduce a *normalization* function that
-- selects the simplest `Bin` out of all the equivalent `Bin`. Then we can
-- prove that the conversion from `Bin` to `Nat` and back again produces that
-- normalized, simplest `Bin`.

-- ### Exercise (4 stars): bin_nat_bin (Advanced) ⭐⭐⭐⭐

-- Define `normalize`. You will need to keep its definition as simple as
-- possible for later proofs to go smoothly. Do not use `binToNat` or
-- `natToBin`, but do use `doubleBin`.

-- Hint: Structure the recursion such that it *always* reaches the end of the
-- `Bin` and *only* processes each bit once. Do not try to "look ahead" at
-- future bits.

def normalize (b : Bin) : Bin := (
  match b with
  | .z     => .z
  | .b0 b' => doubleBin (normalize b')
  | .b1 b' => incr (doubleBin (normalize b')))

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     `How to hide these theorem statements so that students can get practice writing them?`

theorem normalize_z : normalize .z = .z := (by rfl)
theorem normalize_b0 m : normalize (.b0 m) = doubleBin (normalize m) := (by rfl)
theorem normalize_b1 m : normalize (.b1 m) = incr (doubleBin (normalize m)) := (by rfl)

-- It would be wise to do some `example` proofs to check that your definition
-- of `normalize` works the way you intend before you proceed. They won't be
-- graded, but fill them in below.

-- Note to developers (Claude, before next release):
--     Same `-- SOLUTION` mishandling as elsewhere in this chapter, milder
--     here: the block keeps surviving content (`attribute [irreducible] …`)
--     after `-- END SOLUTION`, so student/terse don't error, but the
--     **solutions** build leaks the literal `-- SOLUTION` / `-- END SOLUTION`
--     comment lines into the displayed code. Prefer `solution!` over the
--     comment markers.

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

attribute [irreducible] normalize doubleBin natToBin incr binToNat

-- Finally, prove the main theorem. The inductive cases could be a bit tricky.

-- Hint: Start by trying to prove the main statement, see where you get stuck,
-- and see if you can find a lemma -- perhaps requiring its own inductive
-- proof -- that will allow the main proof to make progress. We have one lemma
-- for the `b0` case (which also makes use of `double_incr_bin`) and another
-- for the `b1` case.

-- Note to developers (Claude, before next release):
--     Same `-- SOLUTION` mishandling, milder: `bin_nat_bin` survives after
--     `-- END SOLUTION` so student/terse don't error, but the **solutions**
--     build leaks the literal `-- SOLUTION` / `-- END SOLUTION` comment lines
--     around `incr_doubleBin`/`natToBin_two_mul` into the displayed code.
--     Prefer `solution!` over the comment markers.

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
  all_goals
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


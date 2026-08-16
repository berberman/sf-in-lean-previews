import LF.Typeclasses
import HL.Imp

import HL.SFLCompat

-- # Equiv: Program Equivalence

open scoped MyGetElem

-- Note to developers (Sati @satiscugcat):
--     At this point, the Rocq file provides instructions about using a new
--     directory, making sure the project is set up properly, and also
--     instructions about how to deal with the exercises. I am assuming these
--     things are being moved to Intro.lean? I am excluding them for now.

-- Note to developers (Sati @satiscugcat):
--     `namespace Equiv`

-- ## Behavioral Equivaleence

-- In an earlier chapter, we investigated the correctness of a very simple
-- program transformation: the `optimize_0plus` function. The programming
-- language we were considering was the first version of the language of
-- arithmetic expressions -- with no variables -- so in that setting it was
-- very easy to define what it means for a program transformation to be
-- correct: it should always yield a program that evaluates to the same number
-- as the original.

-- To talk about the correctness of program transformations for the full Imp
-- language -- in particular, assignment -- we need to consider the role of
-- mutable state and develop a more sophisticated notion of correctness, which
-- we'll call *behavioral equivalence*.

-- For example:

-- - `X + 2` is behaviorally equivalent to `1 + X + 1`
-- - `X - X` is behaviorally equivalent to `0`
-- - `(X - 1) + 1` is *not* behaviorally equivalent to `X`

-- ### Definitions

-- For `aexp`s and `bexp`s with variables, the definition we want is clear:
-- Two `aexp`s or `bexp`s are "behaviorally equivalent" if they evaluate to
-- the same result in every state.

def Aexp.equiv (a₁ a₂ : Aexp) : Prop :=
  ∀ (st: State),
    a₁.eval st = a₂.eval st

def Bexp.equiv (b₁ b₂ : Bexp) : Prop :=
  ∀ (st: State),
    b₁.eval st = b₂.eval st

-- -- ::::full -- Here are some simple examples of equivalences of arithmetic
-- -- and boolean expressions. -- ::::

example : Aexp.equiv
          (aexp { X - X })
          (aexp { 0 }) :=
  by
    intros st
    simp

example : Bexp.equiv
          (bexp { X - X = 0 })
          (bexp { true }) :=
  by
    intros st
    simp

-- For commands, the situation is a little more subtle. We can't simply say
-- "two commands are behaviorally equivalent if they evaluate to the same
-- ending state whenever they are started in the same initial state," because
-- some commands, when run in some starting states, don't terminate in any
-- final state at all!

-- What we need instead is this: two commands are behaviorally equivalent if,
-- for any given starting state, they either (1) both diverge or else (2) both
-- terminate in the same final state. A compact way to express this is "if the
-- first one terminates in a particular state then so does the second, and
-- vice versa."

def Com.equiv (c₁ c₂: Com) : Prop :=
    ∀ (st st': State),
      (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st')

-- ### Simple Examples

-- For examples of command equivalence, let's start by looking at a trivial
-- equivalence involving `skip`.

theorem skip_left: ∀ c,
  Com.equiv
    (imp { skip; ~c })
    c := by
  all_goals
    intros c st st'
    constructor <;> intro h
    case mp =>
      cases h with
      | seq _ _ _ _ _ h1 h2 =>
        cases h1 with
        | skip => assumption
    case mpr =>
      apply Com.EvalR.seq _ _ _ st
      · apply Com.EvalR.skip
      · assumption

-- Note to developers (Sati @satiscugcat):
--     Is the syntax of Imp settled? I find this really unintuitive.

-- ### Exercise (2 stars): skip_right ⭐⭐

-- Prove that adding a `skip` *after* a command also results in an equivalent
-- program.

theorem skip_right : ∀ c,
  Com.equiv
    (imp { ~c  skip; })
    c := by
  all_goals(
    intros c st st'
    constructor <;> intro h
    case mp =>
      cases h with
      | seq _ _ _ _ _ h1 h2 =>
        cases h2 with
        | skip => assumption
    case mpr =>
      apply Com.EvalR.seq _ _ _ st'
      · assumption
      · apply Com.EvalR.skip
  )

-- Similarly, here is a simple equivalence that optimises `if` commands.

theorem if_true_simple: ∀ c₁ c₂,
  Com.equiv
    (imp {if (true) {~c₁} else {~c₂}})
    c₁ := by
  intro c₁ c₂ st st'
  constructor <;> intro h
  case mp =>
    cases h with
    | ifTrue => assumption
    | ifFalse => contradiction
  case mpr =>
    apply Com.EvalR.ifTrue
    · rfl
    · assumption

-- Of course, no programmer would write a conditional whose condition is
-- literally `true`. (At least, no human programmer -- compilers and macro
-- preprocessors do this sort of thing internally all the time!) But they
-- might write one whose condition is *equivalent* to true:

-- Note to developers (Sati @satiscugcat):
--     The to_verso script seems to use `\[\]` blocks, but these seem to cause
--     problems with the tilde. Currently skipping them and just using
--     backticks.

-- *Theorem*: If `b` is equivalent to `true`, then `if (~b) {~c₁}
-- else {~c₂}`
-- is equivalent to `c₁`. *Proof*:

-- - (`->`) We must show, for all `st` and `st'`, that if
--   `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'` then `st =[ c₁ ]=> st'`.

--   Proceed by cases on the rules that could possibly have been used to show
--   `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'`, namely `Com.EvalR.ifTrue`
--   and `Com.EvalR.ifFalse`.

--   - Suppose the final rule in the derivation of
--     `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'` was `Com.EvalR.ifTrue`. We
--     then have, by the premises of `Com.EvalR.ifTrue`, that `st =[ c₁ ]=> st'`.
--     This is exactly what we set out to prove.

--   - On the other hand, suppose the final rule in the derivation of
--     `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'` was `Com.EvalR.ifFalse`. We
--     then know that `b.eval st = false` and `st =[ c₂ ]=> st'`.

--     Recall that `b` is equivalent to `true`, i.e., forall `st`,
--     `b.eval st = (bexp {true}).eval st`. In particular, this means that
--     `b.eval st = true`, since `(bexp {true}).eval st = true`. But this is a
--     contradiction, since `Com.EvalR.ifFalse` requires that `b.eval st = false`.
--     Thus, the final rule could not have been `Com.EvalR.ifFalse`.

-- - (`<-`) We must show, for all `st` and `st'`, that if `st =[ c₁ ]=> st'`
--   then `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'`.

--   Since `b` is equivalent to `true`, we know that `b.eval st` =
--   `(bexp {true}).eval st = true` = `true`. Together with the assumption that
--   `st =[ c₁ ]=> st'`, we can apply `Com.EvalR.ifTrue` to derive
--   `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'`.

-- Here is the formal version of this proof:

-- Note to developers (Sati @satiscugcat):
--     `if_true` causes a naming conflict, I don't know with what.

theorem if_true_equiv: ∀ b c₁ c₂,
  Bexp.equiv b (bexp {true}) ->
  Com.equiv
    (imp {if (~b) {~c₁} else {~c₂}})
    c₁ := by
  intro b c₁ c₂ hb st st'
  constructor <;> intro h
  case mp =>
    cases h with
    | ifTrue => assumption
    | ifFalse _ _ _ _ _ hb' hc =>
      unfold Bexp.equiv at hb; simp at hb
      rw [hb] at hb'
      contradiction
  case mpr =>
    apply Com.EvalR.ifTrue <;> try assumption
    unfold Bexp.equiv at hb; dsimp at hb
    apply hb

-- ### Exercise (2 stars): if_false_equiv ⭐⭐

theorem if_false_equiv: ∀ b c₁ c₂,
  Bexp.equiv b (bexp {false}) ->
  Com.equiv
    (imp {if (~b) {~c₁} else {~c₂}})
    c₂ := by
  all_goals(
    intro b c₁ c₂ hb st st'
    constructor <;> intro h
    case mp =>
      cases h with
      | ifTrue _ _ _ _ _ hb' hc =>
        unfold Bexp.equiv at hb; dsimp at hb
        rw [hb] at hb'
        contradiction
      | ifFalse => assumption
    case mpr =>
      apply Com.EvalR.ifFalse <;> try assumption
      unfold Bexp.equiv at hb; dsimp at hb
      apply hb
  )

-- ### Exercise (3 stars): swap_if_branches ⭐⭐⭐

-- Show that we can swap the branches of an `if` if we also negate its
-- condition.

theorem swap_if_branches : ∀ b c₁ c₂,
  Com.equiv
    (imp {if (~b) {~c₁} else {~c₂}})
    (imp {if (¬ ~b) {~c₂} else {~c₁}}) := by
  all_goals(
    intro b c₁ c₂ st st'
    constructor <;> intro h
    case mp =>
      cases h with
      | ifTrue _ _ _ _ _ hb hc =>
        apply Com.EvalR.ifFalse <;> try assumption
        simp_all
      | ifFalse _ _ _ _ _ hb hc =>
        apply Com.EvalR.ifTrue <;> try assumption
        simp_all
    case mpr =>
      cases h with
      | ifTrue _ _ _ _ _ hb hc =>
        apply Com.EvalR.ifFalse <;> try assumption
        simp_all
      | ifFalse _ _ _ _ _ hb hc =>
        apply Com.EvalR.ifTrue <;> try assumption
        simp_all
  )

-- For `while` loops, we can give a similar pair of theorems. A loop whose
-- guard is equivalent to `false` is equivalent to `skip`, while a loop whose
-- guard is equivalent to `true` is equivalent to `while (true) {skip;} end`
-- (or any other non-terminating program).

-- The first of these facts is easy.

theorem while_false_equiv : ∀ b c,
  Bexp.equiv b (bexp {false}) ->
  Com.equiv
    (imp {while (~b) {~c}})
    (imp {skip;}) := by
  intro b c hb st st'
  constructor <;> intro h
  case mp =>
    cases h with
    | whileFalse => apply Com.EvalR.skip
    | whileTrue _ _ _ _ _ hb' hc hloop =>
      rw [hb] at hb'
      simp at hb'
  case mpr =>
    cases h with
    | skip =>
      apply Com.EvalR.whileFalse
      apply hb

-- ### Exercise (2 stars): while_false_informal (Advanced, manually graded) ⭐⭐

-- Write an informal proof of `while_false_equiv`.

-- To prove the second fact, we need an auxiliary lemma stating that `while`
-- loops whose guards are equivalent to `true` never terminate.

-- *Lemma*: If `b` is equivalent to `true`, then it cannot be the case that
-- `st =[ while (~b) {~c} ]=> st'`.

-- *Proof*: Suppose that `st =[ while (~b) {~c} ]=> st'`. We show, by
-- induction on a derivation of `st =[ while (~b) {~c} ]=> st'`, that this
-- assumption leads to a contradiction. The only two cases to consider are
-- `Com.EvalR.whileFalse` and `Com.EvalR.whileTrue`; the others are
-- contradictory.

-- - Suppose `st =[ while (~b) {~c} ]=> st'` is proved using rule
--   `Com.EvalR.whileFalse`. Then by assumption `b.eval st = false`. But this
--   contradicts the assumption that `b` is equivalent to `true`.

-- - Suppose `st =[ while (~b) {~c} ]=> st'` is proved using rule
--   `Com.EvalR.whileTrue`. We must have:

--   1. `b.eval st = true`, and

--   2. there is some `st₀` such that `st =[ c ] => st₀` and
--      `st₀ =[ while (~b) {~c} ]=> st'`.

--   3. Also, we are given an induction hypothesis saying that
--      `st₀ =[ while (~b) {~c} ]=> st'` leads to a contradiction,

--   We obtain a contradiction by 2 and 3.

theorem while_true_nonterm : ∀ b c st st',
  Bexp.equiv b (bexp {true}) ->
  ¬ (st =[ while (~b) {~c} ]=> st') := by
  all_goals
    intro b c st st' hb contra
    have key : ∀ (c': Com) (s s': State), (s =[ c' ]=> s') -> c' = (imp {while (~b) {~c}}) -> False :=
      by
        intro c' s s' hce
        induction hce with
        | whileFalse b' s0 c0 hb' =>
          intro heq; injection heq with beq ceq
          subst beq; rw [hb] at hb'
          simp at hb'
        | whileTrue s0 s0' s0'' b' c0 hb hc' hwhile ih1 ih2 => exact ih2
        | skip => simp
        | asgn => simp
        | seq => simp
        | ifTrue => simp
        | ifFalse => simp
    exact key (imp {while (~b) {~c}}) st st' contra (by rfl)

-- ### Exercise (2 stars): while_true_nonterm_informal (manually graded) ⭐⭐

-- Explain what the lemma `while_true_nonterm` means in English.

-- ### Exercise (2 stars): while_true ⭐⭐

-- Prove the following theorem. *Hint*: You'll want to use
-- `while_true_nonterm` here.

theorem while_true : ∀ b c,
  Bexp.equiv b (bexp {true}) ->
  Com.equiv
    (imp {while (~b) {~c}})
    (imp {while (true) {skip;}}) := by
  all_goals(
    intro b c beq st st'
    constructor
    case mp =>
      intro h
      apply False.elim
      exact while_true_nonterm b c st st' beq h
    case mpr =>
      intro h
      apply False.elim
      have bexp_equiv_refl : ∀ (b: Bexp), b.equiv b :=
        by
          intro b st
          rfl
      exact while_true_nonterm (bexp {true}) (imp {skip;}) st st' (bexp_equiv_refl (bexp {true})) h
  )

-- A more interesting fact about `while` commands is that any number of copies
-- of the body can be "unrolled" without changing meaning.

-- Loop unrolling is an important transformation in any real compiler, so its
-- correctness is of more than just academic interest!

theorem loop_unrolling : ∀ b c,
  Com.equiv
    (imp {while (~b) {~c}})
    (imp {
      if (~b) {~c} else {skip;}
      while (~b) {~c}
    }) := by
  all_goals
    intro b c st st'
    constructor <;> intro hce
    case mp =>
      cases hce with
      | whileFalse _ _ _ hb =>
        apply Com.EvalR.seq _ _ _ st
        · apply Com.EvalR.ifFalse <;> try assumption
          apply Com.EvalR.skip
        · apply Com.EvalR.whileFalse <;> try assumption
      | whileTrue _ st'' _ _ _ hb hc hloop =>
        apply Com.EvalR.seq _ _ _ st''
        · apply Com.EvalR.ifTrue <;> try assumption
        · assumption
    case mpr =>
      cases hce with
      | seq _ _ _ st'' _ h1 h2 =>
        cases h1 with
        | ifTrue _ _ _ _ _ hb hc =>
          apply Com.EvalR.whileTrue _ st'' <;> try assumption
        | ifFalse _ _ _ _ _ hb hc =>
          cases hc with
          | skip => assumption

-- Note to developers (Sati @satiscugcat):
--     Leaving out optional exercise `seq_assoc` for now.

-- Proving program properties involving assignments is one place where the
-- fact that we are treating equality on program states extensionally (e.g.,
-- `x →ₜ m[x] ; m` and `m` are equal maps) comes in handy.

-- Note to developers (Sati @satiscugcat):
--     I am not able to use `m[x]` syntax here for some reason? I have to use
--     function application and then do some weird manipulation. syntax.

theorem identity_assignment : ∀ X,
  Com.equiv
    (imp {X := X;})
    (imp {skip;}) := by
  intro X st st'
  constructor <;> intro hce
  case mp =>
    cases hce with
    | asgn _ _ n _ h =>
      dsimp at h
      rw [← h, TotalMap.update_same]
      apply Com.EvalR.skip

  case mpr =>
    cases hce with
    | skip =>
      suffices st =[ X := X; ]=> X →ₜ st[X] ; st by
        simp only [TotalMap.update_same] at this
        exact this
      apply Com.EvalR.asgn
      simp

-- ### Exercise (2 stars): assign_equiv ⭐⭐

theorem assign_equiv : ∀ (X : Ident) (a : Aexp),
  Aexp.equiv (aexp {X}) a ->
  Com.equiv
    (imp {skip;})
    (imp {X := ~a;}) := by
  all_goals(
    intro X a aeq st st'
    constructor <;> intro hce
    case mp =>
      cases hce with
      | skip =>
        unfold Aexp.equiv at aeq
        dsimp at aeq
        suffices st =[ X:= ~a; ]=> X →ₜ st[X]; st by
          simp only [TotalMap.update_same] at this
          exact this
        apply Com.EvalR.asgn
        simp [aeq]
    case mpr =>
      cases hce with
      | asgn _ _ n _ h =>
        unfold Aexp.equiv at aeq
        dsimp at aeq
        rw [← h, ← aeq, TotalMap.update_same]
        apply Com.EvalR.skip
  )

-- Note to developers (Sati @satiscugcat):
--     Leaving out optional exercise `equiv_classes` for now.

-- ## Properties of Behavior Equivalence

-- We next consider some fundamental properties of program equivalence.

-- ### Behavioral Equivalence is an Equivalence

-- First, let's verify that the equivalences on `Aexp`s, `Bexp`s, and `Com`s
-- really are *equivalences* -- ie, that they are reflexive, symmetric, and
-- transitive. These proofs are all easy.

theorem Aexp.equiv.refl : ∀ (a : Aexp),
  a.equiv a := by
  intros a st
  rfl

theorem Aexp.equiv.sym : ∀ (a₁ a₂ : Aexp),
  a₁.equiv a₂ → a₂.equiv a₁ := by
  intro a₁ a₂ h st
  rw [h]

theorem Aexp.equiv.trans : ∀ (a₁ a₂ a₂ : Aexp),
  a₁.equiv a₂ → a₂.equiv a₃ → a₁.equiv a₃ := by
  intro a₁ a₂ a₃ h₁ h₂ st
  rw [h₁, h₂]

theorem Bexp.equiv.refl : ∀ (b : Bexp),
  b.equiv b := by
  intros b st
  rfl

theorem Bexp.equiv.sym : ∀ (b₁ b₂ : Bexp),
  b₁.equiv b₂ → b₂.equiv b₁ := by
  intro b₁ b₂ h st
  rw [h]

theorem Bexp.equiv.trans : ∀ (b₁ b₂ b₂ : Bexp),
  b₁.equiv b₂ → b₂.equiv b₃ → b₁.equiv b₃ := by
  intro b₁ b₂ b₃ h₁ h₂ st
  rw [h₁, h₂]

theorem Com.equiv.refl : ∀ (c : Com),
  c.equiv c := by
  intros c st st'
  rfl

theorem Com.equiv.sym : ∀ (c₁ c₂ : Com),
  c₁.equiv c₂ → c₂.equiv c₁ := by
  intro c₁ c₂ h st st'
  rw [h]

theorem Com.equiv.trans : ∀ (c₁ c₂ c₂ : Com),
  c₁.equiv c₂ → c₂.equiv c₃ → c₁.equiv c₃ := by
  intro c₁ c₂ c₃ h₁ h₂ st st'
  rw [h₁, h₂]

-- ### Behavioral Equivalence is a Congruence

-- Less obviously, behavioral equivalence is also a *congruence*. That is, the
-- equivalence of two subprograms implies the equivalence of the larger
-- programs in which they are embedded:

-- aequiv a a' ------------------------- cequiv (x := a) (x := a')

-- cequiv c1 c1' cequiv c2 c2' -------------------------- cequiv (c1;c2)
-- (c1';c2')

-- ... and so on for the other forms of commands.

-- (Note that we are using the inference rule notation here not as part of an
-- inductive definition, but simply to write down some valid implications in a
-- readable format. We prove these implications below.)

-- We will see a concrete example of why these congruence properties are
-- important in the following section (in the proof of
-- `fold_constants_com_sound`), but the main idea is that they allow us to
-- replace a small part of a large program with an equivalent small part and
-- know that the whole large programs are equivalent *without* doing an
-- explicit proof about the parts that didn't change -- i.e., the "proof
-- burden" of a small change to a large program is proportional to the size of
-- the change, not the program!


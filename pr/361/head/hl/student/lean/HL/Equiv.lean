import LF.CustomTactics
import LF.Typeclasses
import HL.Imp

import SFLCompat

--  # Equiv: Program Equivalence

open scoped HasEval MyGetElem Com

open scoped HasEval MyGetElem

--  ## Behavioral Equivaleence

--  In an earlier chapter, we investigated the correctness of a very simple
--  program transformation: the `optimize0plus` function. The programming
--  language we were considering was the first version of the language of
--  arithmetic expressions -- with no variables -- so in that setting it
--  was very easy to define what it means for a program transformation to
--  be correct: it should always yield a program that evaluates to the same
--  number as the original.
--
--  To talk about the correctness of program transformations for the full
--  Imp language -- in particular, assignment -- we need to consider the
--  role of mutable state and develop a more sophisticated notion of
--  correctness, which we'll call *behavioral equivalence*.

--  For example:
--
--  - `X + 2` is behaviorally equivalent to `1 + X + 1`
--  - `X - X` is behaviorally equivalent to `0`
--  - `(X - 1) + 1` is *not* behaviorally equivalent to `X`

--  ### Definitions

--  For `aexp`s and `bexp`s with variables, the definition we want is
--  clear: Two `aexp`s or `bexp`s are "behaviorally equivalent" if they
--  evaluate to the same result in every state.

def Aexp.Equiv (a₁ a₂ : Aexp) : Prop :=
  ∀ (st : State),
    a₁.eval st = a₂.eval st

theorem Aexp.equiv_def {a₁ a₂ : Aexp} :
    a₁.Equiv a₂ ↔ ∀ (st : State), a₁.eval st = a₂.eval st := by rfl

def Bexp.Equiv (b₁ b₂ : Bexp) : Prop :=
  ∀ (st : State),
    b₁.eval st = b₂.eval st

theorem Bexp.equiv_def {b₁ b₂ : Bexp} :
    b₁.Equiv b₂ ↔ ∀ (st : State), b₁.eval st = b₂.eval st := by rfl

--  Here are some simple examples of equivalences of arithmetic and boolean
--  expressions.

example : Aexp.Equiv
    (aexp { X - X })
    (aexp { 0 }) := by
  rw [Aexp.equiv_def]
  intro st
  simp

example : Bexp.Equiv
    (bexp { X - X = 0 })
    (bexp { true }) := by
  rw [Bexp.equiv_def]
  intro st
  simp

--  For commands, the situation is a little more subtle. We can't simply
--  say "two commands are behaviorally equivalent if they evaluate to the
--  same ending state whenever they are started in the same initial state,"
--  because some commands, when run in some starting states, don't
--  terminate in any final state at all!
--
--  What we need instead is this: two commands are behaviorally equivalent
--  if, for any given starting state, they either (1) both diverge or else
--  (2) both terminate in the same final state. A compact way to express
--  this is "if the first one terminates in a particular state then so does
--  the second, and vice versa."

def Com.Equiv (c₁ c₂ : Com) : Prop :=
    ∀ {st st' : State},
      (st =[ ~c₁ ]=> st') ↔ (st =[ ~c₂ ]=> st')

theorem Com.equiv_def {c₁ c₂ : Com} : c₁.Equiv c₂ ↔
    ∀ {st st' : State}, (st =[ ~c₁ ]=> st') ↔ (st =[ ~c₂ ]=> st') := by rfl

--  ### Simple Examples

namespace Com

--  For examples of command equivalence, let's start by looking at a
--  trivial equivalence involving `skip`.

theorem skip_left {c : Com} : (imp { skip; ~c }).Equiv c := by
  rw [equiv_def]
  intro st st''
  constructor
  · intro h
    inversion h with
    | seq st' h1 h2 =>
      inversion h1
      exact h2
  · intro h
    exact EvalR.seq EvalR.skip h

--  ### Exercise (2 stars): skip_right ⭐⭐

--  Prove that adding a `skip` *after* a command also results in an
--  equivalent program.

theorem skip_right {c : Com} : (imp { ~c; skip }).Equiv c := by
  sorry

--  Similarly, here is a simple equivalence that optimises `if` commands.

theorem if_true_simple {c₁ c₂ : Com} : (imp {if (true) {~c₁} else {~c₂}}).Equiv c₁ := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    inversion h with
    | ifTrue hb hc => exact hc
    | ifFalse hb hc => simp at hb
  · intro h
    apply EvalR.ifTrue _ h
    simp

--  Of course, no programmer would write a conditional whose condition is
--  literally `true`. (At least, no human programmer -- compilers and macro
--  preprocessors do this sort of thing internally all the time!) But they
--  might write one whose condition is *equivalent* to true:

--  *Theorem*: If `b` is equivalent to `true`, then
--  `if (~b) {~c₁}
--  else {~c₂}` is equivalent to `c₁`. *Proof*:
--
--  - (`->`) We must show, for all `st` and `st'`, that if
--    `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'` then
--    `st =[ c₁ ]=> st'`.
--
--    Proceed by cases on the rules that could possibly have been used to
--    show `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'`, namely
--    `Com.EvalR.ifTrue` and `Com.EvalR.ifFalse`.
--
--    - Suppose the final rule in the derivation of
--      `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'` was
--      `Com.EvalR.ifTrue`. We then have, by the premises of
--      `Com.EvalR.ifTrue`, that `st =[ c₁ ]=> st'`. This is exactly what
--      we set out to prove.
--
--    - On the other hand, suppose the final rule in the derivation of
--      `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'` was
--      `Com.EvalR.ifFalse`. We then know that `b.eval st = false` and
--      `st =[ c₂ ]=> st'`.
--
--      Recall that `b` is equivalent to `true`, i.e., forall `st`,
--      `b.eval st = (bexp {true}).eval st`. In particular, this means that
--      `b.eval st = true`, since `(bexp {true}).eval st = true`. But this
--      is a contradiction, since `Com.EvalR.ifFalse` requires that
--      `b.eval st = false`. Thus, the final rule could not have been
--      `Com.EvalR.ifFalse`.
--
--  - (`<-`) We must show, for all `st` and `st'`, that if
--    `st =[ c₁ ]=> st'` then
--    `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'`.
--
--    Since `b` is equivalent to `true`, we know that `b.eval st` =
--    `(bexp {true}).eval st = true` = `true`. Together with the assumption
--    that `st =[ c₁ ]=> st'`, we can apply `Com.EvalR.ifTrue` to derive
--    `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'`.

--  Here is the formal version of this proof:

theorem if_true {b : Bexp} {c₁ c₂ : Com} (hb : b.Equiv (bexp {true})) :
    (imp {if (~b) {~c₁} else {~c₂}}).Equiv c₁ := by
  rw [equiv_def]
  rw [Bexp.equiv_def] at hb
  intro st st'
  constructor
  · intro h
    inversion h with
    | ifTrue hb' hc =>
      exact hc
    | ifFalse hb' hc =>
      rw [hb] at hb'
      simp at hb'
  · intro h
    apply EvalR.ifTrue _ h
    rw [hb]
    simp

--  ### Exercise (2 stars): if_false_equiv ⭐⭐

theorem if_false {b : Bexp} {c₁ c₂ : Com} (hb : b.Equiv (bexp {false})) :
    (imp {if (~b) {~c₁} else {~c₂}}).Equiv c₂ := by
  sorry

--  ### Exercise (3 stars): swap_if_branches ⭐⭐⭐

--  Show that we can swap the branches of an `if` if we also negate its
--  condition.

theorem swap_if_branches {b : Bexp} {c₁ c₂ : Com} :
    (imp {if (~b) {~c₁} else {~c₂}}).Equiv
    (imp {if (¬ ~b) {~c₂} else {~c₁}}) := by
  sorry

--  For `while` loops, we can give a similar pair of theorems. A loop whose
--  guard is equivalent to `false` is equivalent to `skip`, while a loop
--  whose guard is equivalent to `true` is equivalent to
--  `while (true) {skip;} end` (or any other non-terminating program).

--  The first of these facts is easy.

theorem while_false_equiv {b : Bexp} {c : Com} (hb : b.Equiv (bexp {false})) :
    (imp {while (~b) {~c}}).Equiv
    (imp {skip}) := by
  rw [equiv_def]
  rw [Bexp.equiv_def] at hb
  intro st st''
  constructor
  · intro h
    inversion h with
    | whileFalse => exact EvalR.skip
    | whileTrue st' hb' hc hloop =>
      simp [hb] at hb'
  · intro h
    inversion h
    apply EvalR.whileFalse
    simp [hb]

--  ### Exercise (2 stars): while_false_informal (Advanced, Manually graded) ⭐⭐

--  Write an informal proof of `while_false_equiv`.

--  To prove the second fact, we need an auxiliary lemma stating that
--  `while` loops whose guards are equivalent to `true` never terminate.

--  *Lemma*: If `b` is equivalent to `true`, then it cannot be the case
--  that `st =[ while (~b) {~c} ]=> st'`.
--
--  *Proof*: Suppose that `st =[ while (~b) {~c} ]=> st'`. We show, by
--  induction on a derivation of `st =[ while (~b) {~c} ]=> st'`, that this
--  assumption leads to a contradiction. The only two cases to consider are
--  `Com.EvalR.whileFalse` and `Com.EvalR.whileTrue`; the others are
--  contradictory.
--
--  - Suppose `st =[ while (~b) {~c} ]=> st'` is proved using rule
--    `Com.EvalR.whileFalse`. Then by assumption `b.eval st = false`. But
--    this contradicts the assumption that `b` is equivalent to `true`.
--
--  - Suppose `st =[ while (~b) {~c} ]=> st'` is proved using rule
--    `Com.EvalR.whileTrue`. We must have:
--
--    1. `b.eval st = true`, and
--
--    2. there is some `st₀` such that `st =[ c ] => st₀` and
--       `st₀ =[ while (~b) {~c} ]=> st'`.
--
--    3. Also, we are given an induction hypothesis saying that
--       `st₀ =[ while (~b) {~c} ]=> st'` leads to a contradiction,
--
--    We obtain a contradiction by 2 and 3.

theorem while_true_nonterm {b : Bexp} {c : Com} {st st' : State} (hb : b.Equiv (bexp {true})) :
    ¬ st =[ while (~b) {~c} ]=> st' := by
  intro contra
  generalize heq : (imp {while (~b) {~c}}) = com at contra
  induction contra with
  | @whileFalse b' s0 c0 hb' =>
    injection heq with hbeq hceq
    subst hbeq
    rw [Bexp.equiv_def] at hb
    simp [hb] at hb'
  | @whileTrue s0 s0' s0'' b' c0 hb' hc' hwhile ih1 ih2 =>
    exact ih2 heq
  | skip | asgn | seq | ifTrue | ifFalse =>
    contradiction -- heq says that different commands are equal

--  ### Exercise (2 stars): while_true_nonterm_informal (Manually graded) ⭐⭐

--  Explain what the lemma `while_true_nonterm` means in English.

--  ### Exercise (2 stars): while_true ⭐⭐

--  Prove the following theorem. *Hint*: You'll want to use
--  `while_true_nonterm` here.

theorem while_true {b : Bexp} {c : Com} (hb : b.Equiv (bexp {true})) :
    (imp {while (~b) {~c}}).Equiv
    (imp {while (true) {skip}}) := by
  sorry

--  A more interesting fact about `while` commands is that any number of
--  copies of the body can be "unrolled" without changing meaning.
--
--  Loop unrolling is an important transformation in any real compiler, so
--  its correctness is of more than just academic interest!

theorem loop_unrolling {b : Bexp} {c : Com} :
    (imp {while (~b) {~c}}).Equiv
    (imp {
      if (~b) {~c} else {skip};
      while (~b) {~c}
    }) := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    inversion h with
    | whileFalse hb =>
      apply EvalR.seq (st' := st)
      · exact EvalR.ifFalse hb EvalR.skip
      · exact EvalR.whileFalse hb
    | whileTrue stmid hb hc hloop =>
      apply EvalR.seq _ hloop
      exact EvalR.ifTrue hb hc
  · intro h
    inversion h with
    | seq stmid h1 h2 =>
      inversion h1 with
      | ifTrue hb hc =>
        exact EvalR.whileTrue hb hc h2
      | ifFalse hb hc =>
        inversion hc
        exact h2

--  Proving program properties involving assignments is one place where the
--  fact that we are treating equality on program states extensionally
--  (e.g., `x →ₜ m[x] ; m` and `m` are equal maps) comes in handy.

theorem identity_assignment {X : Ident} :
    (imp {X := X}).Equiv
    (imp {skip}) := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    inversion h with
    | asgn n h =>
      subst h
      simp only [Aexp.eval_id, TotalMap.update_same]
      exact Com.EvalR.skip
  · intro h
    inversion h
    suffices st =[ X := X ]=> X →ₜ st[X] ; st by
      simp only [TotalMap.update_same] at this
      exact this
    apply Com.EvalR.asgn
    simp

--  ### Exercise (2 stars): assign_equiv ⭐⭐

theorem assign_equiv {X : Ident} {a : Aexp} (ha : Aexp.Equiv (aexp {X}) a) :
    (imp {skip}).Equiv
    (imp {X := ~a}) := by
  sorry

--  ## Properties of Behavior Equivalence

--  We next consider some fundamental properties of program equivalence.

--  ### Behavioral Equivalence is an Equivalence

--  First, let's verify that the equivalences on `Aexp`s, `Bexp`s, and
--  `Com`s really are *equivalences* -- ie, that they are reflexive,
--  symmetric, and transitive. These proofs are all easy.

end Com

theorem Aexp.equiv_refl (a : Aexp) : a.Equiv a := by
  rw [equiv_def]
  intro st
  rfl

theorem Aexp.equiv_symm {a₁ a₂ : Aexp} (h : a₁.Equiv a₂) : a₂.Equiv a₁ := by
  rw [equiv_def] at h ⊢
  intro st
  rw [h]

theorem Aexp.equiv_trans {a₁ a₂ a₃ : Aexp} (h₁ : a₁.Equiv a₂) (h₂ : a₂.Equiv a₃) :
    a₁.Equiv a₃ := by
  rw [equiv_def] at h₁ h₂ ⊢
  intro st
  rw [h₁, h₂]

theorem Bexp.equiv_refl {b : Bexp} : b.Equiv b := by
  rw [equiv_def]
  intro st
  rfl

theorem Bexp.equiv_symm {b₁ b₂ : Bexp} (h : b₁.Equiv b₂) : b₂.Equiv b₁ := by
  rw [equiv_def]
  intro st
  rw [h]

theorem Bexp.equiv_trans {b₁ b₂ b₃ : Bexp} (h₁ : b₁.Equiv b₂) (h₂ : b₂.Equiv b₃) :
    b₁.Equiv b₃ := by
  rw [equiv_def]
  intro st
  rw [h₁, h₂]

theorem Com.equiv_refl {c : Com} : c.Equiv c := by
  rewrite [equiv_def]
  intro st st'
  rfl

theorem Com.equiv_symm {c₁ c₂ : Com} (h : c₁.Equiv c₂) : c₂.Equiv c₁ := by
  rw [equiv_def] at h ⊢
  intro st st'
  rw [h]

theorem Com.equiv_trans {c₁ c₂ c₃ : Com} (h₁ : c₁.Equiv c₂) (h₂ : c₂.Equiv c₃) :
    c₁.Equiv c₃ := by
  rw [equiv_def] at h₁ h₂ ⊢
  intro st st'
  rw [h₁, h₂]

--  ### Behavioral Equivalence is a Congruence

--  Less obviously, behavioral equivalence is also a *congruence*. That is,
--  the equivalence of two subprograms implies the equivalence of the
--  larger programs in which they are embedded:
--
--  aequiv a a' ------------------------- cequiv (x := a) (x := a')
--
--  cequiv c1 c1' cequiv c2 c2' -------------------------- cequiv (c1;c2)
--  (c1';c2')
--
--  ... and so on for the other forms of commands.
--
--  (Note that we are using the inference rule notation here not as part of
--  an inductive definition, but simply to write down some valid
--  implications in a readable format. We prove these implications below.)

--  We will see a concrete example of why these congruence properties are
--  important in the following section (in the proof of
--  `fold_constants_com_sound`), but the main idea is that they allow us to
--  replace a small part of a large program with an equivalent small part
--  and know that the whole large programs are equivalent *without* doing
--  an explicit proof about the parts that didn't change -- i.e., the
--  "proof burden" of a small change to a large program is proportional to
--  the size of the change, not the program!

theorem Com.congruence.asgn {x : Ident} {a a' : Aexp} (ha : a.Equiv a') :
    (imp {x := ~a}).Equiv
    (imp {x := ~a'}) := by
  rw [equiv_def]
  intro st st'
  constructor <;>
  · intro h
    inversion h with
    | asgn n h =>
      subst h
      apply Com.EvalR.asgn
      rw [Aexp.equiv_def] at ha
      rw [ha]

--  The congruence property for loops is a little more interesting, since
--  it requires induction.
--
--  *Theorem*: Equivalence is a congruence for `while` -- that is, if `b`
--  is equivalent to `b'` and `c` is equivalent to `c'`, then
--  `while (~b) {~c}` is equivalent to `while (~b') {~c'}`.
--
--  *Proof*: Suppose `b` is equivalent to `b'` and `c` is equivalent to
--  `c'`. We must show, for every `st` and `st'`, that
--  `st =[ while (~b) {~c} ]=> st'` iff `st = while (~b') {~c'}
--  ]=> st'`.
--  We consider the two directions separately.
--
--  - (`->`) We show that `st =[ while (~b) {~c} ]=> st'` implies
--    `st =[ while (~b') {~c'} ]=> st'`, by induction on a derivation of
--    `st =[ while (~b) {~c} ]=> st'`. The only nontrivial cases are when
--    the final rule in the derivation is `Com.EvalR.whileFalse` or
--    `Com.EvalR.whileTrue`.
--
--    - `Com.EvalR.whileFalse`: In this case, the form of the rule gives us
--      `beval st b = false` and `st = st'`. But then, since `b` and `b'`
--      are equivalent, we have `beval st b' =false`, and
--      `Com.EvalR.whileFalse` applies, giving us
--      `st =[ while (~b') {~c'} ]=> st'`, as required.
--
--    - `Com.EvalR.whileTrue`: The form of the rule now gives us
--      `beval st b = true`, with `st =[ c ]=> st'0` and
--      `st'0 =[ while {~b} {~c} ]=> st'` for some state `st'0`, with the
--      induction hypothesis `st'0 =[ while (~b') {~c'} ]=> st'`.
--
--      Since `c` and `c'` are equivalent, we know that `st =[ c']=> st'0`.
--      And since `b` and `b'` are equivalent, we have
--      `beval st b' = true`. Now `Com.EvalR.whileTrue` applies, giving us
--      `st =[ while (~b') {~c'} ]=> st'`, as required.
--
--  - (`<-`) Similar.

-- Built on 2026-09-03 13:56 UTC

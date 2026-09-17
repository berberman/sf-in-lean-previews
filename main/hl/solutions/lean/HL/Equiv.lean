import LF.CustomTactics
import LF.Typeclasses
import HL.Imp

import SFLCompat

--  # Equiv: Program Equivalence

open scoped HasEval MyGetElem Com

--  ## Behavioral Equivalence

--  In an earlier chapter, we investigated the correctness of a very simple
--  program transformation: the `optimize0plus` function. The programming
--  language we were considering was the first version of the language of
--  arithmetic expressions - with no variables - so in that setting it was
--  very easy to define what it means for a program transformation to be
--  correct: it should always yield a program that evaluates to the same
--  number as the original.
--
--  To talk about the correctness of program transformations for the full
--  Imp language - in particular, assignment - we need to consider the role
--  of mutable state and develop a more sophisticated notion of
--  correctness, which we'll call *behavioral equivalence*.
--
--  For example:
--  - `X + 2` is behaviorally equivalent to `1 + X + 1`
--  - `X - X` is behaviorally equivalent to `0`
--  - `(X - 1) + 1` is *not* behaviorally equivalent to `X`

--  ### Definitions

--  For `Aexp`s and `Bexp`s with variables, the definition we want is
--  clear: Two `Aexp`s or `Bexp`s are "behaviorally equivalent" if they
--  evaluate to the same result in every state.

def Aexp.Equiv (a₁ a₂ : Aexp) : Prop :=
  ∀ (st : State),
    a₁.eval st = a₂.eval st

def Bexp.Equiv (b₁ b₂ : Bexp) : Prop :=
  ∀ (st : State),
    b₁.eval st = b₂.eval st

--  We'll also define a notation for `Equiv`:

class Equiv (α : Type) where
  equiv : α → α → Prop

infix:70 " ≃ " => Equiv.equiv -- you can type `≃` as \equiv

instance : Equiv Aexp where
  equiv := Aexp.Equiv

instance : Equiv Bexp where
  equiv := Bexp.Equiv

@[simp]
theorem Aexp.equiv_notation {a₁ a₂ : Aexp} : a₁.Equiv a₂ ↔ a₁ ≃ a₂ := by rfl
@[simp]
theorem Aexp.equiv_def {a₁ a₂ : Aexp} :
    a₁ ≃ a₂ ↔ ∀ (st : State), a₁.eval st = a₂.eval st := by rfl

@[simp]
theorem Bexp.equiv_notation {b₁ b₂ : Bexp} : b₁.Equiv b₂ ↔ b₁ ≃ b₂ := by rfl
@[simp]
theorem Bexp.equiv_def {b₁ b₂ : Bexp} :
    b₁ ≃ b₂ ↔ ∀ (st : State), b₁.eval st = b₂.eval st := by rfl

--  Here are some simple examples of equivalences of arithmetic and boolean
--  expressions.

example : aexp { X - X } ≃ aexp { 0 } := by simp

example : bexp { X - X = 0 } ≃ bexp { true } := by simp

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
      (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st')

instance : Equiv Com where
  equiv := Com.Equiv

@[simp]
theorem Com.equiv_notation {c₁ c₂ : Com} : c₁.Equiv c₂ ↔ c₁ ≃ c₂ := by rfl
@[simp]
theorem Com.equiv_def {c₁ c₂ : Com} : c₁ ≃ c₂ ↔
    ∀ {st st' : State}, (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st') := by rfl

--  ### Simple Examples

namespace Com

--  For examples of command equivalence, let's start by looking at a
--  trivial equivalence involving `skip`.

theorem skip_left {c : Com} : imp { skip; c } ≃ c := by
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

theorem skip_right {c : Com} : imp { c; skip } ≃ c := by
  rw [equiv_def]
  intro st st''
  constructor
  · intro h
    inversion h with
    | seq st' h1 h2 =>
      inversion h2
      exact h1
  · intro h
    exact EvalR.seq h EvalR.skip

--  (End of exercise)

--  Similarly, here is a simple equivalence that optimises `if` commands.

theorem if_true_simple {c₁ c₂ : Com} : imp {if (true) {c₁} else {c₂}} ≃ c₁ := by
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
--  literally `true`. (At least, no human programmer - compilers and macro
--  preprocessors do this sort of thing internally all the time!) But they
--  might write one whose condition is *equivalent* to true:
--
--  *Theorem*: If `b` is equivalent to `true`, then `if (b) {c₁} else {c₂}`
--  is equivalent to `c₁`. *Proof*:
--  - (`→`) We must show, for all `st` and `st'`, that if
--    `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'` then `st =[ c₁ ]=> st'`.
--
--    Proceed by cases on the rules that could possibly have been used to
--    show `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'`, namely
--    `Com.EvalR.ifTrue` and `Com.EvalR.ifFalse`.
--    - Suppose the final rule in the derivation of
--      `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'` was `Com.EvalR.ifTrue`.
--      We then have, by the premises of `Com.EvalR.ifTrue`, that
--      `st =[ c₁ ]=> st'`. This is exactly what we set out to prove.
--
--    - On the other hand, suppose the final rule in the derivation of
--      `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'` was
--      `Com.EvalR.ifFalse`. We then know that `b.eval st = false` and
--      `st =[ c₂ ]=> st'`.
--
--      Recall that `b` is equivalent to `true`, i.e., forall `st`,
--      `b.eval st = (Bexp {true}).eval st`. In particular, this means that
--      `b.eval st = true`, since `(Bexp {true}).eval st = true`. But this
--      is a contradiction, since `Com.EvalR.ifFalse` requires that
--      `b.eval st = false`. Thus, the final rule could not have been
--      `Com.EvalR.ifFalse`.
--
--  - (`<-`) We must show, for all `st` and `st'`, that if
--    `st =[ c₁ ]=> st'` then `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'`.
--
--    Since `b` is equivalent to `true`, we know that `b.eval st` =
--    `(Bexp {true}).eval st = true` = `true`. Together with the assumption
--    that `st =[ c₁ ]=> st'`, we can apply `Com.EvalR.ifTrue` to derive
--    `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'`.
--
--  Here is the formal version of this proof:

theorem if_true {b : Bexp} {c₁ c₂ : Com} (hb : b ≃ bexp {true}) :
    imp {if (b) {c₁} else {c₂}} ≃ c₁ := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    inversion h <;> simp_all
  · intro h
    apply EvalR.ifTrue _ h
    simp_all

--  ### Exercise (2 stars): if_false_equiv ⭐⭐

theorem if_false {b : Bexp} {c₁ c₂ : Com} (hb : b ≃ bexp {false}) :
    imp {if (b) {c₁} else {c₂}} ≃ c₂ := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    inversion h <;> simp_all
  · intro h
    apply EvalR.ifFalse _ h
    simp_all

--  ### Exercise (3 stars): swap_if_branches ⭐⭐⭐

--  Show that we can swap the branches of an `if` if we also negate its
--  condition.

theorem swap_if_branches {b : Bexp} {c₁ c₂ : Com} :
    imp {if (b) {c₁} else {c₂}} ≃
    imp {if (¬ b) {c₂} else {c₁}} := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    inversion h with
    | ifTrue hb hc =>
      apply EvalR.ifFalse _ hc
      simp [hb]
    | ifFalse hb hc =>
      apply EvalR.ifTrue _ hc
      simp [hb]
  · intro h
    inversion h with
    | ifTrue hb hc =>
      apply EvalR.ifFalse _ hc
      simp_all
    | ifFalse hb hc =>
      apply EvalR.ifTrue _ hc
      simp_all

--  (End of exercise)

--  For `while` loops, we can give a similar pair of theorems. A loop whose
--  guard is equivalent to `false` is equivalent to `skip`, while a loop
--  whose guard is equivalent to `true` is equivalent to
--  `while (true) {skip} end` (or any other non-terminating program).
--
--  The first of these facts is easy.

theorem while_false {b : Bexp} {c : Com} (hb : b ≃ bexp {false}) :
    imp {while (b) {c}} ≃ imp {skip} := by
  rw [equiv_def]
  intro st st''
  constructor
  · intro h
    inversion h with
    | whileFalse => exact EvalR.skip
    | whileTrue st' hb' hc hloop =>
      simp_all
  · intro h
    inversion h
    apply EvalR.whileFalse
    simp_all

--  ### Exercise (2 stars): while_false_informal (Advanced, Manually graded) ⭐⭐

--  Write an informal proof of `while_false`.

--  (End of exercise)

--  To prove the second fact, we need an auxiliary lemma stating that
--  `while` loops whose guards are equivalent to `true` never terminate.
--
--  *Lemma*: If `b` is equivalent to `true`, then it cannot be the case
--  that `st =[ while (b) {c} ]=> st'`.
--
--  *Proof*: Suppose that `st =[ while (b) {c} ]=> st'`. We show, by
--  induction on a derivation of `st =[ while (b) {c} ]=> st'`, that this
--  assumption leads to a contradiction. The only two cases to consider are
--  `Com.EvalR.whileFalse` and `Com.EvalR.whileTrue`; the others are
--  contradictory.
--  - Suppose `st =[ while (b) {c} ]=> st'` is proved using rule
--    `Com.EvalR.whileFalse`. Then by assumption `b.eval st = false`. But
--    this contradicts the assumption that `b` is equivalent to `true`.
--
--  - Suppose `st =[ while (b) {c} ]=> st'` is proved using rule
--    `Com.EvalR.whileTrue`. We must have:
--    1. `b.eval st = true`, and
--    2. there is some `st₀` such that `st =[ c ] => st₀` and
--       `st₀ =[ while (b) {c} ]=> st'`.
--    3. Also, we are given an induction hypothesis saying that
--       `st₀ =[ while (b) {c} ]=> st'` leads to a contradiction,
--
--    We obtain a contradiction by 2 and 3.

theorem while_true_nonterm {b : Bexp} {c : Com} {st st' : State} (hb : b ≃ bexp {true}) :
    ¬ st =[ while (b) {c} ]=> st' := by
  intro contra
  generalize heq : (imp {while (b) {c}}) = com at contra
  induction contra with
  | whileFalse hb' =>
    injection heq with hbeq hceq
    subst hbeq
    simp_all -- hb and hb' are contradictory
  | whileTrue hb' hc' hwhile ih1 ih2 =>
    exact ih2 heq
  | skip | asgn | seq | ifTrue | ifFalse =>
    contradiction -- `heq` says that different commands are equal

--  ### Exercise (2 stars): while_true_nonterm_informal (Manually graded) ⭐⭐

--  Explain what the lemma `while_true_nonterm` means in English.

--  ### Exercise (2 stars): while_true ⭐⭐

--  Prove the following theorem. *Hint*: You'll want to use
--  `while_true_nonterm` here.

theorem while_true {b : Bexp} {c : Com} (hb : b ≃ bexp {true}) :
    imp {while (b) {c}} ≃ imp {while (true) {skip}} := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    exfalso
    exact while_true_nonterm hb h
  · intro h
    exfalso
    apply while_true_nonterm _ h
    rw [Bexp.equiv_def]
    intro
    rfl

--  (End of exercise)

--  A more interesting fact about `while` commands is that any number of
--  copies of the body can be "unrolled" without changing meaning.
--
--  Loop unrolling is an important transformation in any real compiler, so
--  its correctness is of more than just academic interest!

theorem loop_unrolling {b : Bexp} {c : Com} :
    imp { while (b) {c} } ≃
    imp {
      if (b) {c} else {skip};
      while (b) {c}
    } := by
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

--  ### Exercise (2 stars): seq_assoc (Optional) ⭐⭐

theorem seq_assoc {c₁ c₂ c₃ : Com} :
  imp {~(imp {c₁; c₂}); c₃} ≃ imp {c₁; c₂; c₃} := by
    intro st₁ st₂
    constructor <;> intro h
    · inversion h with
      | seq h₁ h₂ =>
          inversion h₁
          apply EvalR.seq; assumption
          apply EvalR.seq <;> assumption
    · inversion h with
      | seq h₁ h₂ =>
          inversion h₂
          apply EvalR.seq <;> try assumption
          apply EvalR.seq <;> assumption

--  (End of exercise)

--  Proving program properties involving assignments is one place where the
--  fact that we are treating equality on program states extensionally
--  (e.g., `x →ₜ m[x] ; m` and `m` are equal maps) comes in handy.

theorem identity_assignment {X : Ident} :
    imp { X := X } ≃ imp { skip } := by
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
    have h' : st =[ X := X ]=> X →ₜ st[X] ; st := by
      apply Com.EvalR.asgn
      simp
    simp_all [TotalMap.update_same]

--  ### Exercise (2 stars): assign_equiv ⭐⭐

theorem assign_equiv {X : Ident} {a : Aexp} (ha : aexp { X } ≃ a) :
    imp { skip } ≃ imp { X := a } := by
  rw [equiv_def]
  rw [Aexp.equiv_def] at ha
  intro st st'
  constructor
  · intro h
    inversion h
    have h' : st =[ X := ~a ]=> X →ₜ st[X]; st := by
      apply Com.EvalR.asgn
      simp [← ha]
    simp_all [← ha]
  · intro h
    inversion h with
    | asgn n h =>
      subst h
      simp only [← ha, Aexp.eval_id, TotalMap.update_same]
      exact Com.EvalR.skip

--  ### Exercise (2 stars): equiv_classes (Optional, Manually graded) ⭐⭐

--  Given the following programs, group together those that are equivalent
--  in Imp. Your answer should be given as a list of lists, where each
--  sub-list represents a group of equivalent programs. For example, if you
--  think programs (a) through (h) are all equivalent to each other, but
--  not to (i), your answer should look like this:

--  [ [progA, progB, progC, progD, progE, progF, progG, progH], [progI] ]

--  Write down your answer below in the definition of `equiv_classes`

def progA : Com :=
  imp {
    while (X > 0) {
       X := X + 1
    }
  }

def progB : Com :=
  imp {
    if (X = 0) {
       X := X + 1;
       Y := 1
     } else {
       Y := 0
     };
     X := X - Y;
     Y := 0
  }

def progC : Com :=
  imp { skip }

def progD : Com :=
  imp {
    while (X ≠ 0) {
       X := (X * Y) + 1
    }
  }

def progE : Com :=
  imp { Y := 0 }

def progF : Com :=
  imp {
    Y := X + 1;
    while (X ≠ Y) {
      Y := X + 1
    }
  }

def progG : Com :=
  imp {
    while (true) {
      skip
    }
  }

def progH : Com :=
  imp {
    while (X ≠ X) {
      X := X + 1
    }
  }

def progI : Com :=
  imp {
    while (X ≠ Y) {
      X := Y + 1
    }
  }

def equiv_classes : List (List Com) := (
  [ [progA, progD] ,
    [progB, progE] ,
    [progC, progH] ,
    [progF, progG] ,
    [progI] ]
)

--  ## Properties of Behavior Equivalence

--  We next consider some fundamental properties of program equivalence.

--  ### Behavioral Equivalence is an Equivalence

--  First, let's verify that the equivalences on `Aexp`s, `Bexp`s, and
--  `Com`s really are *equivalences* - ie, that they are reflexive,
--  symmetric, and transitive. These proofs are all easy.

end Com

theorem Aexp.equiv_refl (a : Aexp) : a ≃ a := by simp_all
theorem Aexp.equiv_symm {a₁ a₂ : Aexp} (h : a₁ ≃ a₂) : a₂ ≃ a₁ := by simp_all
theorem Aexp.equiv_trans {a₁ a₂ a₃ : Aexp} (h₁ : a₁ ≃ a₂) (h₂ : a₂ ≃ a₃) : a₁ ≃ a₃ := by simp_all

theorem Bexp.equiv_refl {b : Bexp} : b ≃ b := by simp_all
theorem Bexp.equiv_symm {b₁ b₂ : Bexp} (h : b₁ ≃ b₂) : b₂ ≃ b₁ := by simp_all
theorem Bexp.equiv_trans {b₁ b₂ b₃ : Bexp} (h₁ : b₁ ≃ b₂) (h₂ : b₂ ≃ b₃) : b₁ ≃ b₃ := by simp_all

theorem Com.equiv_refl {c : Com} : c ≃ c := by simp_all
theorem Com.equiv_symm {c₁ c₂ : Com} (h : c₁ ≃ c₂) : c₂ ≃ c₁ := by simp_all
theorem Com.equiv_trans {c₁ c₂ c₃ : Com} (h₁ : c₁ ≃ c₂) (h₂ : c₂ ≃ c₃) : c₁ ≃ c₃ := by simp_all

--  Lean has a standard library definition for relations that are
--  equivalences, unsurprisingly called `Equivalence`. To show that a
--  relation is an `Equivalence`, one needs only supply proofs of the three
--  properties above:

theorem Com.equiv_equivalence : Equivalence Com.Equiv where
  refl := @Com.equiv_refl
  symm := Com.equiv_symm
  trans := Com.equiv_trans

--  ### Behavioral Equivalence is a Congruence

--  Less obviously, behavioral equivalence is also a *congruence*. That is,
--  the equivalence of two subprograms implies the equivalence of the
--  larger programs in which they are embedded:
--
--  a ≃ a' ------------------------- (x := a) ≃ (x := a')
--
--  c₁ ≃ c₁' c₂ ≃ c₂' -------------------------- (c₁ ; c₂) ≃ (c₁' ; c₂')
--
--  ... and so on for the other forms of commands.
--
--  (Note that we are using the inference rule notation here not as part of
--  an inductive definition, but simply to write down some valid
--  implications in a readable format. We prove these implications below.)
--
--  We will see a concrete example of why these congruence properties are
--  important in the following section (in the proof of
--  `fold_constants_com_sound`), but the main idea is that they allow us to
--  replace a small part of a large program with an equivalent small part
--  and know that the whole large programs are equivalent *without* doing
--  an explicit proof about the parts that didn't change - i.e., the "proof
--  burden" of a small change to a large program is proportional to the
--  size of the change, not the program!

theorem Com.congruence_asgn {x : Ident} {a a' : Aexp} (ha : a ≃ a') :
    imp {x := a} ≃ imp {x := a'} := by
  rw [equiv_def]
  intro st st'
  constructor <;>
  · intro h
    inversion h with
    | asgn n h =>
      subst h
      apply Com.EvalR.asgn
      simp_all

--  The congruence property for loops is a little more interesting, since
--  it requires induction.
--
--  *Theorem*: Equivalence is a congruence for `while` -- that is, if `b`
--  is equivalent to `b'` and `c` is equivalent to `c'`, then
--  `while (b) {c}` is equivalent to `while (b') {c'}`.
--
--  *Proof*: Suppose `b` is equivalent to `b'` and `c` is equivalent to
--  `c'`. We must show, for every `st` and `st'`, that
--  `st =[ while (b) {c} ]=> st'` iff `st = while (b') {c'}]=> st'`. We
--  consider the two directions separately.
--  - (`→`) We show that `st =[ while (b) {c} ]=> st'` implies
--    `st =[ while (b') {c'} ]=> st'`, by induction on a derivation of
--    `st =[ while (b) {c} ]=> st'`. The only nontrivial cases are when the
--    final rule in the derivation is `Com.EvalR.whileFalse` or
--    `Com.EvalR.whileTrue`.
--    - `Com.EvalR.whileFalse`: In this case, the form of the rule gives us
--      `b.eval st = false` and `st = st'`. But then, since `b` and `b'`
--      are equivalent, we have `b'.eval st = false`, and
--      `Com.EvalR.whileFalse` applies, giving us
--      `st =[ while (b') {c'} ]=> st'`, as required.
--
--    - `Com.EvalR.whileTrue`: The form of the rule now gives us
--      `b.eval st = true`, with `st =[ c ]=> st'₀` and
--      `st'₀ =[ while {b} {c} ]=> st'` for some state `st'₀`, with the
--      induction hypothesis `st'₀ =[ while (b') {c'} ]=> st'`.
--
--      Since `c` and `c'` are equivalent, we know that `st =[ c']=> st'0`.
--      And since `b` and `b'` are equivalent, we have `b'.eval st = true`.
--      Now `Com.EvalR.whileTrue` applies, giving us
--      `st =[ while (b') {c'} ]=> st'`, as required.
--
--  - (`←`) Similar.

theorem Com.congruence_while {b b' : Bexp} {c c' : Com} (hb : b ≃ b') (hc : c ≃ c') :
    imp {while (b) {c}} ≃ imp {while (b') {c'}} := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    generalize heq : (imp {while (b) {c}}) = com at h
    induction h with
    | whileFalse hb' =>
      injection heq with hbeq hceq
      subst hbeq
      apply Com.EvalR.whileFalse
      rw [← hb]
      exact hb'
    | whileTrue hb' hc' hwhile _ ih2 =>
      injection heq with beq ceq
      subst beq ceq
      rw [hb] at hb'
      specialize ih2 rfl
      apply Com.EvalR.whileTrue hb' _ ih2
      · rw [equiv_def] at hc
        exact hc.mp hc'
    | skip | asgn | seq | ifTrue | ifFalse =>
      contradiction
  · intro h
    generalize heq : (imp {while (~b') {~c'}}) = com at h
    induction h with
    | whileFalse hb' =>
      injection heq with hbeq hceq
      subst hbeq
      apply Com.EvalR.whileFalse
      rw [hb]
      exact hb'
    | whileTrue hb' hc' hwhile _ ih2 =>
      injection heq with beq ceq
      subst beq ceq
      rw [← hb] at hb'
      specialize ih2 rfl
      apply Com.EvalR.whileTrue hb' _ ih2
      · rw [equiv_def] at hc
        exact hc.mpr hc'
    | skip | asgn | seq | ifTrue | ifFalse =>
      contradiction

--  ### Exercise (3 stars): Com.congruence_seq (Optional) ⭐⭐⭐

theorem Com.congruence_seq {c₁ c₁' c₂ c₂' : Com} (hc₁ : c₁ ≃ c₁') (hc₂ : c₂ ≃ c₂') :
    imp {c₁ ; ~c₂} ≃ imp {c₁' ; c₂'} := by
  (
    intro st st'
    constructor
    · intro h
      inversion h with
      | seq hc₁' hc₂' =>
        rw [equiv_def] at hc₁
        rw [equiv_def] at hc₂
        exact Com.EvalR.seq (hc₁.mp hc₁') (hc₂.mp hc₂')
    · intro h
      inversion h with
      | seq hc₁' hc₂' =>
        rw [equiv_def] at hc₁
        rw [equiv_def] at hc₂
        exact Com.EvalR.seq (hc₁.mpr hc₁') (hc₂.mpr hc₂')
  )

--  ### Exercise (3 stars): Com.congruence_if ⭐⭐⭐

theorem Com.congruence_if {b b' : Bexp} {c₁ c₁' c₂ c₂' : Com}
   (hb : b ≃ b') (hc₁ : c₁ ≃ c₁') (hc₂ : c₂ ≃ c₂') :
    (imp {if (b) {c₁} else {c₂}}).Equiv
    (imp {if (b') {c₁'} else {c₂'}}) := by
  (
    intro st st'
    constructor
    · intro h
      inversion h with
      | ifTrue hb' hc₁' =>
        rw [hb] at hb'
        apply Com.EvalR.ifTrue <;> try assumption
        · rw [equiv_def] at hc₁
          exact (hc₁.mp hc₁')
      | ifFalse hb' hc₂' =>
        rw [hb] at hb'
        apply Com.EvalR.ifFalse <;> try assumption
        · rw [equiv_def] at hc₂
          exact (hc₂.mp hc₂')
    · intro h
      inversion h with
      | ifTrue hb' hc₁' =>
        rw [← hb] at hb'
        apply Com.EvalR.ifTrue <;> try assumption
        · rw [equiv_def] at hc₁
          exact (hc₁.mpr hc₁')
      | ifFalse hb' hc₂' =>
        rw [← hb] at hb'
        apply Com.EvalR.ifFalse <;> try assumption
        · rw [equiv_def] at hc₂
          exact (hc₂.mpr hc₂')
  )

--  (End of exercise)

--  For example, here are two programs and a proof of their equivalence
--  using their congruence theorems.

example :
    imp {X := 0; if (X = 0) {Y := 0} else {Y := 42}} ≃
    imp {X := 0; if (X = 0) {Y := X - X} else {Y := 42}} := by
  apply Com.congruence_seq
  · apply Com.equiv_refl
  · apply Com.congruence_if
    · apply Bexp.equiv_refl
    · apply Com.congruence_asgn
      simp
    · apply Com.equiv_refl

--  ### Exercise (3 stars): not_congr (Advanced, Manually graded) ⭐⭐⭐

--  We've shown that the `Com.Equiv` relation is both an equivalence and a
--  congruence on commands. Can you think of a relation on commands that is
--  an equivalence but *not* a congruence? Write down the relation
--  (formally), together with an informal sketch of a proof that it is an
--  equivalence and a counterexample showing it is not a congruence.

--  ## Program Transformation

--  A *program transformation* is a function that takes a program as input
--  and produces a modified program as output. Compiler optimizations such
--  as constant folding are canonical examples, but there are many others.

def Aexp.TransSound (trans : Aexp → Aexp) : Prop :=
  ∀ (a : Aexp), a ≃ (trans a)

@[simp]
theorem Aexp.transSound_def {trans : Aexp → Aexp} :
    TransSound trans ↔ ∀ (a : Aexp), a ≃ (trans a) := by rfl

def Bexp.TransSound (trans : Bexp → Bexp) : Prop :=
  ∀ (b : Bexp), b ≃ (trans b)

@[simp]
theorem Bexp.transSound_def {trans : Bexp → Bexp} :
    TransSound trans ↔ ∀ (b : Bexp), b ≃ (trans b) := by rfl

def Com.TransSound (trans : Com → Com) : Prop :=
  ∀ (c : Com), c ≃ (trans c)

@[simp]
theorem Com.transSound_def {trans : Com → Com} :
    TransSound trans ↔ ∀ (c : Com), c ≃ (trans c) := by rfl

--  ### The Constant-Folding Transformation

--  An expression is *constant* if it contains no variable references.
--
--  Constant folding is an optimization that finds constant expressions and
--  replaces them by their values.

def Aexp.foldConstants (a : Aexp) : Aexp :=
  match a with
  | .num n => .num n
  | .id x => .id x
  | aexp { ~a₁ + ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => .num (n₁ + n₂)
    | a₁', a₂' => aexp { ~a₁' + ~a₂' }
  | aexp { ~a₁ - ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => .num (n₁ - n₂)
    | a₁', a₂' => aexp { ~a₁' - ~a₂' }
  | aexp { ~a₁ * ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => .num (n₁ * n₂)
    | a₁', a₂' => aexp { ~a₁' * ~a₂' }

@[simp]
theorem Aexp.foldConstants_num (n : Nat) : (Aexp.num n).foldConstants = .num n := rfl
@[simp]
theorem Aexp.foldConstants_id (x : Ident) : (Aexp.id x).foldConstants = .id x := rfl

theorem Aexp.foldConstants_cases (a₁ a₂ : Aexp) :
    (∃ n₁ n₂, a₁.foldConstants = .num n₁ ∧ a₂.foldConstants = .num n₂) ∨
    (aexp {a₁ + a₂}).foldConstants = (aexp {~a₁.foldConstants + ~a₂.foldConstants}) ∧
    (aexp {a₁ - a₂}).foldConstants = (aexp {~a₁.foldConstants - ~a₂.foldConstants}) ∧
    (aexp {a₁ * a₂}).foldConstants = (aexp {~a₁.foldConstants * ~a₂.foldConstants}) := by
  cases ha₁ : a₁.foldConstants with
  | num n₁ =>
    cases ha₂ : a₂.foldConstants with
    | num n₂ =>
      left
      exists n₁, n₂
    | _ =>
      simp [foldConstants, ha₁, ha₂]
  | _ =>
    simp [foldConstants, ha₁]

--  Note to developers (Niklas Halonen @xhalo32):
--      Make sure we have explained what named cases hypotheses does
--      (`cases ha₁ : a₁.foldConstants` in the above proof).

example : (aexp { (1 + 2) * X }).foldConstants = (aexp { 3 * X }) := by rfl

--  Note that this version of constant folding doesn't do other "obvious"
--  things like eliminating trivial additions (e.g., rewriting `0 + X` to
--  just `X`).: we are focusing on a single optimization for the sake of
--  simplicity.
--
--  It is not hard to incorporate other ways of simplifying expressions --
--  the definitions and proofs just get longer. We'll consider some in the
--  exercises.

example : (aexp { X - ((0 * 6) + Y) }).foldConstants = (aexp { X - (0 + Y) }) := by rfl

--  Not only can we lift `Aexp.foldConstants` to `Bexp` in the `Bexp.eq`,
--  `Bexp.neq`, and `Bexp.le` cases, we can also look for constant
--  *boolean* expressions and evaluate them in place as well.

def Bexp.foldConstants (b : Bexp) : Bexp :=
  match b with
  | bexp { true } => bexp { true }
  | bexp { false } => bexp { false }
  | bexp { ~a₁ = ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ = n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { ~a₁' = ~a₂' }
  | bexp { ~a₁ ≠ ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ ≠ n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { ~a₁' ≠ ~a₂' }
  | bexp { ~a₁ ≤ ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ ≤ n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { ~a₁' ≤ ~a₂' }
  | bexp { ~a₁ > ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ > n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { ~a₁' > ~a₂' }
  | bexp { ¬ ~b₁ } =>
    match b₁.foldConstants with
    | bexp { true } => bexp { false }
    | bexp { false } => bexp { true }
    | b₁' => bexp { ¬ ~b₁' }
  | bexp { ~b₁ ∧ ~b₂ } =>
    match b₁.foldConstants, b₂.foldConstants with
    | bexp { true }, bexp { true } => bexp { true }
    | bexp { true }, bexp { false } => bexp { false }
    | bexp { false }, bexp { true } => bexp { false }
    | bexp { false }, bexp { false } => bexp { false }
    | b₁', b₂' => bexp { ~b₁' ∧ ~b₂' }

@[simp]
theorem Bexp.foldConstants_true : (bexp { true }).foldConstants = (bexp { true }) := rfl
@[simp]
theorem Bexp.foldConstants_false : (bexp { false }).foldConstants = (bexp { false }) := rfl

theorem Bexp.foldConstants_comp (a₁ a₂ : Aexp) :
    (∃ n₁ n₂, a₁.foldConstants = .num n₁ ∧ a₂.foldConstants = .num n₂) ∨
    (bexp {~a₁ = ~a₂}).foldConstants = (bexp {~a₁.foldConstants = ~a₂.foldConstants}) ∧
    (bexp {~a₁ ≠ ~a₂}).foldConstants = (bexp {~a₁.foldConstants ≠ ~a₂.foldConstants}) ∧
    (bexp {~a₁ ≤ ~a₂}).foldConstants = (bexp {~a₁.foldConstants ≤ ~a₂.foldConstants}) ∧
    (bexp {~a₁ > ~a₂}).foldConstants = (bexp {~a₁.foldConstants > ~a₂.foldConstants}) := by
  cases ha₁ : a₁.foldConstants with
  | num n₁ =>
    cases ha₂ : a₂.foldConstants with
    | num n₂ =>
      left
      exists n₁, n₂
    | _ =>
      simp [foldConstants, ha₁, ha₂]
  | _ => simp [foldConstants, ha₁]

theorem Bexp.foldConstants_unary (b : Bexp) :
    (b.foldConstants = (bexp { true }) ∨ b.foldConstants = (bexp { false })) ∨
    (bexp { ¬~b }).foldConstants = (bexp { ¬(~b.foldConstants)}) := by
  cases hb : b.foldConstants with
  | bool b' =>
    simp_all
  | _ =>
    simp [foldConstants, hb]

theorem Bexp.foldConstants_binary (b₁ : Bexp) (b₂ : Bexp) :
    ((b₁.foldConstants = (bexp { true }) ∨ b₁.foldConstants = (bexp { false })) ∧
     (b₂.foldConstants = (bexp { true }) ∨ b₂.foldConstants = (bexp { false }))) ∨
    (bexp {~b₁ ∧ ~b₂}).foldConstants = (bexp {~b₁.foldConstants ∧ ~b₂.foldConstants}) := by
  cases hb₁ : b₁.foldConstants with
  | bool b₁' =>
    cases hb₂ : b₂.foldConstants with
    | bool b₂' => simp_all
    | _ => simp [foldConstants, hb₁, hb₂]
  | _ => simp [foldConstants, hb₁]

example : (bexp { true ∧ ¬( false ∧ true) }).foldConstants = (bexp { true }) := by
  rfl
example : (bexp { (X = Y) ∧ ( 0 = (2 - (1 + 1))) }).foldConstants = (bexp { (X = Y) ∧ true }) := by
  rfl

--  To fold constants in a command, we simply apply the appropriate folding
--  functions on all embedded expressions.

def Com.foldConstants (c : Com) : Com :=
  match c with
  | imp { skip } => imp { skip }
  | imp { x := ~a } => imp { x := ~a.foldConstants }
  | imp { c₁ ; c₂ } =>  imp { c₁.foldConstants ; c₂.foldConstants }
  | imp { if (b) { c₁ } else { c₂ }} =>
    match b.foldConstants with
    | bexp { true } => c₁.foldConstants
    | bexp { false } => c₂.foldConstants
    | b' => imp { if (b') {c₁.foldConstants} else { c₂.foldConstants}}
  | imp { while (b) {c}} =>
    match b.foldConstants with
    | bexp { true } => imp { while (true) { skip }}
    | bexp { false } => imp { skip }
    | b' => imp { while (b') {c.foldConstants}}

example :
  (imp {
    X := 4 + 5;
    Y := X - 3;
    if ((X - Y) = (2 + 4)) {skip} else {Y := 0};
    if (0 ≤ (4 - (2 - 1))) {Y := 0} else {skip};
    while (Y = 0) {X := X+1}
  }).foldConstants =
  (imp {
    X := 9;
    Y := X - 3;
    if ((X - Y) = 6) {skip} else {Y := 0};
    Y := 0;
    while (Y = 0) {X := X+1}
  }) := by rfl

--  ### Soundness of Constant Folding

--  Now we need to show that what we've done is correct.
--
--  Here's the proof for arithmetic expressions.

theorem Aexp.foldConstants_sound : TransSound Aexp.foldConstants := by
  intro a st
  induction a with
  | num n | id x => rfl
  | _ a₁ a₂ _ _ =>
    cases Aexp.foldConstants_cases a₁ a₂ with
    | inl h =>
      obtain ⟨n₁, n₂, h₁, h₂⟩ := h
      simp_all [foldConstants]
    | inr h =>
      simp_all

--  An equivalent version using the `fun_induction` tactic would look
--  simpler:

theorem Aexp.foldConstants_sound' : TransSound Aexp.foldConstants := by
  intro a st
  fun_induction Aexp.foldConstants <;> simp_all

--  ### Exercise (3 stars): Bexp.fold_eq_informal (Optional, Manually graded) ⭐⭐⭐

--  Here is an informal proof of the `eq` case of the soundness argument
--  for boolean expression constant folding. Read it carefully and compare
--  it to the formal proof that follows. Then fill in the `le` case of the
--  formal proof (without looking at the `eq` case, if possible).
--
--  *Theorem*: The constant folding function for booleans,
--  `Bexp.fold_constants`, is sound.
--
--  *Proof*: We must show that `b` is equivalent to
--  `Bexp.fold_constants b`, for all boolean expressions `b`. Proceed by
--  induction on `b`. We show just the case where `b` has the form
--  `a₁ = a₂`.
--
--  In this case, we must show

--  (bexp { a₁ = a₂ }).eval st = (bexp { a₁ = a₂ }).foldConstants.eval st

--  There are two cases to consider:
--  - First, suppose `a₁.foldConstants = aexp { n₁ }` and
--    `a₂.foldConstants = aexp { n₂ }` for some `n₁` and `n₂`.
--
--    In this case, we have

--  Bexp.fold_constants (bexp { a₁ = a₂ }) = if (n₁ = n₂) then bexp { true } else bexp { false }

--  and

--  (bexp {a₁ = a₂}).eval st = a₁.eval st = a₂.eval st.

--  By the soundness of constant folding for arithmetic expressions
--  (`Aexp.foldConstants_sound`), we know

--  a₁.eval st
--           = (a₁.foldConstants).eval st
--           = (aexp { n₁ }).eval st
--           = n₁

--  and

--  a₂.eval st
--           = (a₂.foldConstants).eval st
--           = (aexp { n₂ }).eval st
--           = n₂

--  so

--  bexp { a₁ = a₂ }.eval st
--           = a₁.eval st = a₂.aeval st
--           = n₁ = n₂

--  Also, it is easy to see (by considering the cases `n₁ = n₂` and
--  `n₁ ≠ n₂` separately) that

--  (if n₁ = n₂ then (bexp { true }) else (bexp { false }) ).eval st
--           = if n₁ = n₂ then bexp { true }.eval st else bexp { false }.eval st
--           = if n₁ = n₂ then true else false
--           = n₁ = n₂

--  So

--  (bexp { a₁ = a₂ }).eval st
--           = n₁ = n₂.
--           = (if n₁ = n₂ then (bexp { true }) else (bexp { false }) ).eval st,

--  as required.
--  - Otherwise, one of `a₁.foldConstants` and `a₂.foldConstants` is not a
--    constant. In this case, we must show

--  bexp { a₁ = a₂ }.eval st
--           = (bexp { (a₁.foldConstants = a₂.foldConstants) }).eval st,

--  which, by the definition of `Bexp.eval`, is the same as showing

--  a₁.eval st = a₂.eval st
--          = (a₁.foldConstants).eval st = (a₂.foldConstants).eval st

--  But the soundness of constant folding for arithmetic expressions
--  (`Aexp.foldConstants_sound`) gives us

--  a₁ = (a₁.foldConstants).eval st
--           a₂ = (a₂.foldConstants).eval st

--  completing the case.

theorem Bexp.foldConstants_sound : Bexp.TransSound Bexp.foldConstants := by
    intro b st
    induction b with
    | bool b => cases b <;> simp
    | eq a₁ a₂ =>
        simp only [Bexp.eval_eq, Bexp.foldConstants]
        have h₁ : a₁.eval st = a₁.foldConstants.eval st := by
          rw [Aexp.foldConstants_sound]
        have h₂ : a₂.eval st = a₂.foldConstants.eval st := by
          rw [Aexp.foldConstants_sound]
        rw [h₁, h₂]
        cases a₁.foldConstants <;> cases a₂.foldConstants <;> (try simp_all; done)
        · case num.num n₁ n₂ =>
          -- The only interesting case is when both a₁ and a₂ become constants after folding
          by_cases n₁ = n₂ <;> simp_all
    | neq a₁ a₂ =>
        simp only [Bexp.eval_neq, Bexp.foldConstants]
        have h₁ : a₁.eval st = a₁.foldConstants.eval st := by
          rw [Aexp.foldConstants_sound]
        have h₂ : a₂.eval st = a₂.foldConstants.eval st := by
          rw [Aexp.foldConstants_sound]
        rw [h₁, h₂]
        cases a₁.foldConstants <;> cases a₂.foldConstants <;> (try simp_all; done)
        · case num.num n₁ n₂ =>
          by_cases n₁ = n₂ <;> simp_all
    | le a₁ a₂ =>
      simp only [Bexp.eval_le, Bexp.foldConstants]
      have h₁ : a₁.eval st = a₁.foldConstants.eval st := by
        rw [Aexp.foldConstants_sound]
      have h₂ : a₂.eval st = a₂.foldConstants.eval st := by
        rw [Aexp.foldConstants_sound]
      rw [h₁, h₂]
      cases a₁.foldConstants <;> cases a₂.foldConstants <;> (try simp_all; done)
      · case num.num n₁ n₂ =>
        simp only [Aexp.eval]
        by_cases (n₁ ≤ n₂) <;> simp_all [Nat.not_le_of_gt]
    | gt a₁ a₂ =>
      simp only [Bexp.eval_gt, Bexp.foldConstants]
      have h₁ : a₁.eval st = a₁.foldConstants.eval st := by
        rw [Aexp.foldConstants_sound]
      have h₂ : a₂.eval st = a₂.foldConstants.eval st := by
        rw [Aexp.foldConstants_sound]
      rw [h₁, h₂]
      cases a₁.foldConstants <;> cases a₂.foldConstants <;> (try simp_all; done)
      · case num.num n₁ n₂ =>
        by_cases n₂ < n₁ <;> simp_all [Nat.not_lt_of_le]
    | not b ih =>
        simp only [Bexp.eval_not, Bexp.foldConstants]
        rw [ih]
        cases b.foldConstants  <;> (try simp_all; done)
        · case not.bool b => cases b <;> simp_all
    | and b₁ b₂ ih₁ ih₂ =>
        simp only [Bexp.eval_and, Bexp.foldConstants]
        rw [ih₁, ih₂]
        cases b₁.foldConstants <;> cases b₂.foldConstants <;> (try simp_all; done)
        · case and.bool.bool b₁ b₂ =>
          cases b₁ <;> cases b₂ <;> simp_all

--  ### Exercise (3 stars): Com.foldConstants_sound (Optional, Manually graded) ⭐⭐⭐

--  Complete the `while` case of the following proof.

theorem Com.foldConstants_sound : Com.TransSound Com.foldConstants := by
  intro c
  induction c with
  | skip =>
      simp [Com.foldConstants]
  | asgn x a =>
      apply Com.congruence_asgn
      apply Aexp.foldConstants_sound
  | seq c₁ c₂ ih₁ ih₂ =>
      apply Com.congruence_seq <;> assumption
  | cond b c₁ c₂ ih₁ ih₂ =>
      simp only [Com.foldConstants]
      have hb : b ≃ b.foldConstants := by
        apply Bexp.foldConstants_sound
      -- If the optimization doesn't eliminate the `if`, then the
      -- result is easy to prove from the `ih` and
      -- `Bexp.foldConstants_sound`
      cases heq : b.foldConstants <;> try (apply Com.congruence_if <;> simp_all)
      · case cond.bool b =>
          cases b with
          | false =>
              apply Com.equiv_trans <;> try assumption
              apply Com.if_false; simp_all
          | true =>
              apply Com.equiv_trans <;> try assumption
              apply Com.if_true; simp_all
  | whileDo b c ih =>
      simp only [Com.foldConstants]
      have hb : b ≃ b.foldConstants := by
        apply Bexp.foldConstants_sound
      cases heq : b.foldConstants <;> try (apply Com.congruence_while <;> simp_all)
      · case whileDo.bool b =>
        cases b with
        | false =>
            apply Com.while_false; simp_all
        | true =>
            apply Com.while_true; simp_all

--  ## Soundness of (0 + n) Elimination, Redux

--  ### Exercise (4 stars): optimize0plus_var (Optional) ⭐⭐⭐⭐

--  Recall the definition `optimize0plus` from the Slang chapter:

--  def optimize0plus (a : Aexp) : Aexp :=
--    match a with
--    | num   n          => num n
--    | plus  (num 0) e₂ => optimize0plus e₂
--    | plus  e₁      e₂ => plus  (optimize0plus e₁) (optimize0plus e₂)
--    | minus e₁      e₂ => minus (optimize0plus e₁) (optimize0plus e₂)
--    | mult  e₁      e₂ => mult  (optimize0plus e₁) (optimize0plus e₂)

--  Note that this function is defined over the old version of `Aexp`s,
--  without states.
--
--  Write a new version of this function that deals with variables (by
--  leaving them alone), plus analogous ones for `Bexp`s and commands:

--  Aexp.optimize0plus
--  Bexp.optimize0plus
--  Com.optimize0plus

def Aexp.optimize0plus (a : Aexp) : Aexp := (
  match a with
  | Aexp.num n => Aexp.num n
  | Aexp.id x => Aexp.id x
  | (aexp { 0 + ~a₂ }) => Aexp.optimize0plus a₂
  | (aexp { ~a₁ + ~a₂ }) => (aexp { ~(Aexp.optimize0plus a₁) + ~(Aexp.optimize0plus a₂) })
  | (aexp { ~a₁ - ~a₂ }) => (aexp { ~(Aexp.optimize0plus a₁) - ~(Aexp.optimize0plus a₂) })
  | (aexp { ~a₁ * ~a₂ }) => (aexp { ~(Aexp.optimize0plus a₁) * ~(Aexp.optimize0plus a₂) })
)

def Bexp.optimize0plus (b : Bexp) : Bexp := (
  match b with
  | (bexp { true })        => (bexp { true })
  | (bexp { false })       => (bexp { false })
  | (bexp { ~a₁ = ~a₂ })  => (bexp { ~(Aexp.optimize0plus a₁) =  ~(Aexp.optimize0plus a₂) })
  | (bexp { ~a₁ ≠ ~a₂ })  => (bexp { ~(Aexp.optimize0plus a₁) ≠ ~(Aexp.optimize0plus a₂) })
  | (bexp { ~a₁ ≤ ~a₂ }) => (bexp { ~(Aexp.optimize0plus a₁) ≤ ~(Aexp.optimize0plus a₂) })
  | (bexp { ~a₁ > ~a₂ })  => (bexp { ~(Aexp.optimize0plus a₁) >  ~(Aexp.optimize0plus a₂) })
  | (bexp { ¬ ~b₁ })     => (bexp { ¬ ~(Bexp.optimize0plus b₁) })
  | (bexp { ~b₁ ∧ ~b₂ }) => (bexp { ~(Bexp.optimize0plus b₁) ∧ ~(Bexp.optimize0plus b₂) })
)

def Com.optimize0plus (c : Com) : Com := (
match c with
| (imp { skip })                     => (imp { skip })
| (imp { x := ~a })                   => (imp { x := ~(Aexp.optimize0plus a) })
| (imp { c₁ ; c₂ })                  => imp { ~(Com.optimize0plus c₁) ; ~(Com.optimize0plus c₂) }
| (imp { if (b) {c₁} else {c₂} }) =>
    imp { if (~(Bexp.optimize0plus b)) {~(Com.optimize0plus c₁)} else {~(Com.optimize0plus c₂)} }
| (imp { while (b) {c₁} })         => imp { while (~(Bexp.optimize0plus b))
                                        {~(Com.optimize0plus c₁)} }
)

example :
    Com.optimize0plus
       (imp { while (X ≠ 0) { X := 0 + X - 1 } }) =
    (imp { while (X ≠ 0) { X := X - 1 } }) := by
  rfl

--  Prove that these three functions are sound, as we did for
--  `foldConstants`. Make sure you use the congruence lemmas in the proof
--  for `Com.optimize0plus` - otherwise it will be *long*!

theorem Aexp.optimize0plus_sound: Aexp.TransSound Aexp.optimize0plus := by
  intro a st
  induction a with (simp only [Aexp.eval, Aexp.optimize0plus]; try rfl )
  | plus a₁ a₂ ih₁ ih₂ =>
    cases a₁ with (simp only [Aexp.eval, Aexp.optimize0plus] at *; try rw [←ih₁, ←ih₂])
    | num n =>
      cases n <;> simp only [Aexp.eval, Aexp.optimize0plus] <;> lia
    | id _ => rw [ih₂]
  | mult a₁ a₂ ih₁ ih₂
  | minus a₁ a₂ ih₁ ih₂ => rw [←ih₁, ←ih₂]

theorem Bexp.optimize0plus_sound: Bexp.TransSound Bexp.optimize0plus := by
  intro b st
  induction b with (
    simp only [Bexp.eval, Bexp.optimize0plus];
    try rw [←Aexp.optimize0plus_sound, ←Aexp.optimize0plus_sound]
  )
  | bool b => cases b <;> simp [Bexp.optimize0plus]
  | not b ih => rw [ih]
  | and b₁ b₂ ih₁ ih₂ => rw [ih₁, ih₂]

theorem Com.optimize0plus_sound: Com.TransSound Com.optimize0plus := by
  intro c
  induction c with
  | skip => apply Com.equiv_refl
  | asgn x a => apply Com.congruence_asgn; apply Aexp.optimize0plus_sound
  | seq c₁ c₂ ih₁ ih₂ => apply Com.congruence_seq <;> assumption
  | cond b c₁ c₂ ih₁ ih₂ =>
      apply Com.congruence_if <;> try assumption
      apply Bexp.optimize0plus_sound
  | whileDo b c ih =>
      apply Com.congruence_while <;> try assumption
      apply Bexp.optimize0plus_sound

--  Finally, let's define a compound optimizer on commands that first folds
--  constants (using `Com.foldConstants`) and then eliminates `0 + n` terms
--  (using`Com.optimize0plus`).

def optimizer (c : Com) := Com.optimize0plus (Com.foldConstants c)

--  Prove that this optimizer is sound.

theorem optimizer_sound : Com.TransSound optimizer := by
  intro c
  apply Com.equiv_trans
  · apply Com.foldConstants_sound
  · apply Com.optimize0plus_sound

--  ## Proving Inequivalence

--  Next, let's look at some programs that are *not* equivalent.
--
--  Suppose that `c₁` is a command of the form

--  X := a₁; Y := a₂

--  and `c₂` is the command

--  X := a₁; Y := a₂'

--  where `a₂'` is formed by substituting `a₁` for all occurrences of `X`
--  in `a₂`.
--
--  For example, `c₁` and `c₂` might be:

--  c₁  =  (X := 42 + 53;
--                 Y := Y + X)
--         c₂  =  (X := 42 + 53;
--                 Y := Y + (42 + 53))

--  Clearly, this *particular* `c₁` and `c₂` are equivalent. Is this true
--  in general?
--
--  We will see in a moment that it is not, but it is worthwhile to pause,
--  now, and see if you can find a counter-example on your own.
--
--  More formally, here is the function that substitutes an arithmetic
--  expression `u` for each occurrence of a given variable `x` in another
--  expression `a`:

def Aexp.subst (x : String) (u : Aexp) (a : Aexp) : Aexp :=
  match a with
  | Aexp.num n       =>
      Aexp.num n
  | Aexp.id x'       =>
      if x = x' then u else Aexp.id x'
  | (aexp { ~a₁ + ~a₂ })  =>
      (aexp { ~(Aexp.subst x u a₁) + ~(Aexp.subst x u a₂) })
  | (aexp { ~a₁ - ~a₂ }) =>
      (aexp { ~(Aexp.subst x u a₁) - ~(Aexp.subst x u a₂) })
  | (aexp { ~a₁ * ~a₂ })  =>
      (aexp { ~(Aexp.subst x u a₁) * ~(Aexp.subst x u a₂) })

example :
  Aexp.subst X (aexp { 42 + 53 })  (aexp { Y + X })
  = (aexp {  Y + (42 + 53) }) := by rfl

--  And here is the property we are interested in, expressing the claim
--  that commands `c₁` and `c₂` as described above are always equivalent.

def SubstEquivProperty : Prop := ∀ (x₁ x₂ : String) (a₁ a₂ : Aexp),
  (imp { x₁ := a₁; x₂ := a₂ }) ≃
  (imp { x₁ := a₁; x₂ := ~(Aexp.subst x₁ a₁ a₂) })

--  Sadly, the property does *not* always hold.
--
--  Here is a counterexample:

--  X := X + 1; Y := X

--  If we perform the substitution, we get

--  X := X + 1; Y := X + 1

--  which clearly isn't equivalent.

theorem subst_inequiv : ¬ SubstEquivProperty := by
  rw [SubstEquivProperty]
  intro contra

  /- Here is the counterexample: assuming that `SubstEquivProperty`
     holds allows us to prove that these two programs are
     equivalent... -/
  let c₁ := imp {X := X + 1; Y := X}
  let c₂ := imp {X := X + 1; Y := X + 1}
  have h : c₁ ≃ c₂ := by
    apply contra
  clear contra

  /- ... allows us to show that the command `c₂` can terminate
     in two different final states:
        st₁ = (Y →ₜ 1 ; X →ₜ 1)
        st₂ = (Y →ₜ 2 ; X →ₜ 1). -/
  let st₁ := Y →ₜ 1 ; X →ₜ 1
  let st₂ := Y →ₜ 2 ; X →ₜ 1
  have h₁ : ∅ =[ c₁ ]=> st₁ := by
    constructor <;> constructor <;> rfl
  have h₂ : ∅ =[ c₂ ]=> st₂ := by
    constructor <;> constructor <;> rfl

  -- Finally, we use the fact that evaluation is deterministic to obtain a contradiction.
  apply h.mp at h₁
  apply ceval_deterministic h₁ at h₂
  have contra : st₁[Y] = st₂[Y] := by rw [h₂]
  rw [TotalMap.update_eq, TotalMap.update_eq] at contra
  contradiction

--  ### Exercise (4 stars): better_subst_equiv (Optional) ⭐⭐⭐⭐

--  The equivalence we had in mind above was not complete nonsense -- in
--  fact, it was actually almost right. To make it correct, we just need to
--  exclude the case where the variable `X` occurs in the right-hand side
--  of the first assignment statement.

inductive VarNotUsedInAexp (x : String) : Aexp → Prop where
  | num {n : Nat} : VarNotUsedInAexp x (Aexp.num n)
  | id {y : String} (h : x ≠ y) : VarNotUsedInAexp x (Aexp.id y)
  | plus {a₁ a₂ : Aexp}
      (h₁ : VarNotUsedInAexp x a₁)
      (h₂ : VarNotUsedInAexp x a₂) :
      VarNotUsedInAexp x ((aexp { ~a₁ + ~a₂ }))
  | minus {a₁ a₂ : Aexp}
      (h₁ : VarNotUsedInAexp x a₁)
      (h₂ : VarNotUsedInAexp x a₂) :
      VarNotUsedInAexp x ((aexp { ~a₁ - ~a₂ }))
  | mult {a₁ a₂ : Aexp}
      (h₁ : VarNotUsedInAexp x a₁)
      (h₂ : VarNotUsedInAexp x a₂) :
      VarNotUsedInAexp x ((aexp { ~a₁ * ~a₂ }))

theorem Aexp.eval_weakening {x : String} {st : State} {a : Aexp} {ni : Nat}
  (h : VarNotUsedInAexp x a) :
  a.eval (x →ₜ ni ; st) = a.eval st := by

  induction a with
  | num n => rfl
  | id y =>
      inversion h; simp only [Aexp.eval]
      apply TotalMap.update_neq; assumption
  | plus a₁ a₂ ih₁ ih₂
  | minus a₁ a₂ ih₁ ih₂
  | mult a₁ a₂ ih₁ ih₂ =>
      simp only [Aexp.eval]; inversion h;
      rw [ih₁, ih₂] <;> assumption

--  Using `VarNotUsedInAexp`, formalize and prove a correct version of
--  `SubstEquivProperty`.

theorem aeval_subst {x : String} {st : State} {a₁ a₂ : Aexp}
  (h : VarNotUsedInAexp x a₁) :
  a₂.eval (x →ₜ a₁.eval st ; st) = (Aexp.subst x a₁ a₂).eval (x →ₜ a₁.eval st ; st) := by

  induction a₂ generalizing a₁ st with
  | num n => rfl
  | id y =>
      simp only [Aexp.subst]
      by_cases h : x = y
      · subst_vars; symm;
        simp only [Aexp.eval_id, TotalMap.update_eq]
        apply Aexp.eval_weakening; assumption
      · simp_all
  | plus a₁ a₂ ih₁ ih₂
  | minus a₁ a₂ ih₁ ih₂
  | mult a₁ a₂ ih₁ ih₂ =>
      simp only [Aexp.eval, Aexp.subst]
      rw [ih₁, ih₂] <;> assumption

theorem subst_equiv {x₁ x₂ : String} {a₁ a₂ : Aexp}
  (h : VarNotUsedInAexp x₁ a₁) :
  imp { x₁ := a₁; x₂ := a₂ } ≃
  imp { x₁ := a₁; x₂ := ~(Aexp.subst x₁ a₁ a₂)} := by

  intro st st'; constructor <;> intro heval
  · inversion heval with
    | seq h₁ h₂ =>
      constructor; assumption
      inversion h₂ <;> subst_vars; constructor
      inversion h₁ <;> subst_vars; symm
      apply aeval_subst h
  · inversion heval with
    | seq h₁ h₂ =>
      constructor; assumption
      inversion h₂ <;> subst_vars; constructor
      inversion h₁ <;> subst_vars
      apply aeval_subst h

--  ### Exercise (3 stars): inequiv_exercise (Optional) ⭐⭐⭐

--  Prove that an infinite loop is not equivalent to `skip`.

theorem inequiv_exercise:
  ¬ (imp { while (true) {skip} } ≃ imp { skip }) := by

  intro contra
  have h : ¬ (∅ =[ while (true) { skip } ]=> ∅) := by
    apply Com.while_true_nonterm; apply Bexp.equiv_refl
  apply h
  rw [@contra ∅ ∅]
  constructor

--  ## Extended Exercise: Nondeterministic Imp

--  As we have seen (in theorem `ceval_deterministic` in the `Imp`
--  chapter), Imp's evaluation relation is deterministic. However,
--  *non*-determinism is an important part of the definition of many real
--  programming languages. For example, in many imperative languages (such
--  as C and its relatives), the order in which function arguments are
--  evaluated is unspecified: the program fragment

--  x = 0;
--    f(++x, x)

--  might call `f` with arguments `(1, 0)` or `(1, 1)`, depending how the
--  compiler chooses to order things. This can be a little confusing for
--  programmers, but it gives compiler writers useful freedom.
--
--  In this exercise, we will extend Imp with a simple nondeterministic
--  command and study how this change affects program equivalence. The new
--  command has the syntax `havoc X`, where `X` is an identifier. The
--  effect of executing `havoc X` is to assign an *arbitrary* number to the
--  variable `X`, nondeterministically. For example, after executing the
--  program:

--  havoc Y;
--    Z := Y * 2

--  the value of `Y` can be any number, while the value of `Z` is twice
--  that of `Y` (so `Z` is always even). Note that we are not saying
--  anything about the *probabilities* of the outcomes -- just that there
--  are (infinitely) many different outcomes that can possibly happen after
--  executing this nondeterministic code.
--
--  In a sense, a variable on which we do `havoc` roughly corresponds to an
--  uninitialized variable in a low-level language like C. After the
--  `havoc`, the variable holds a fixed but arbitrary number. Most sources
--  of nondeterminism in language definitions are there precisely because
--  programmers don't care which choice is made (and so it is good to leave
--  it open to the compiler to choose whichever will run faster).
--
--  We call this new language *Himp* ("Imp extended with `havoc`").

namespace Himp

--  To formalize Himp, we first add a clause to the definition of commands.

inductive Com : Type where
  | skip : Com
  | asgn : String → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | havoc : String → Com  --  <--- NEW

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: commands, macro rules)
namespace Com

/-- Assignment -/
syntax:max "havoc" ppHardSpace ident : imp_com

open Lean

scoped macro_rules
  | `(imp { $s }) => do
    let stx ← match s with
      | `(imp_com| skip) => ``(Com.skip)
      | `(imp_com| havoc $x:ident) => ``(Com.havoc $x)
      | `(imp_com| $x:ident) => ``(($x : Com))
      | `(imp_com| $c₁ ; $c₂) =>
        ``(Com.seq (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| $x:ident := $a) =>
        ``(Com.asgn $x (aexp {$a}))
      | `(imp_com| if ($b) {$c₁} else {$c₂}) =>
        ``(Com.cond (bexp {$b}) (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| while ($b) {$c}) =>
        ``(Com.whileDo (bexp {$b}) (imp {$c}))
      | `(imp_com| ~$c) => `(($c : Com))
      | _ => Macro.throwUnsupported
    return Imp.Elab.withSourceInfoOf s stx

end Com

open scoped Com

namespace Delab
open Lean PrettyPrinter Imp.Delab

@[app_unexpander Com.havoc]
def unexpandComHavoc : Unexpander
  | `($_ $x:ident) => `(imp { havoc $x:ident })
  | _ => throw ()

attribute [app_unexpander Com.skip] unexpandComSkip
attribute [app_unexpander Com.asgn] unexpandComAsgn
attribute [app_unexpander Com.seq] unexpandComSeq
attribute [app_unexpander Com.cond] unexpandComCond
attribute [app_unexpander Com.whileDo] unexpandComWhileDo

end Delab

/-- info: imp {havoc X} : Com -/
#guard_msgs in
#check imp { havoc X }
--  END DETAILS

--  ### Exercise (2 stars): himp_eval (Optional, Manually graded) ⭐⭐

--  Now, we must extend the operational semantics. We have provided a
--  template for the `Com.EvalR` relation below, specifying the big-step
--  semantics. What rule(s) must be added to the definition of `Com.EvalR`
--  to formalize the behavior of the `havoc` command?

inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} : EvalR (imp {skip}) st st
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := a}) st (x →ₜ n ; st)
  | seq {c₁ c₂ : Com} {st st' st'' : State} (h₁ : EvalR c₁ st st') (h₂ : EvalR c₂ st' st'') :
      EvalR (imp {c₁; c₂}) st st''
  | ifTrue {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = true)
      (hc : EvalR c₁ st st') :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st'
  | ifFalse {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = false)
      (hc : EvalR c₂ st st') :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st'
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (b) {c}}) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st') (hloop : Com.EvalR (imp {while (b) {c}}) st' st'') :
      EvalR (imp {while (b) {c}}) st st''
  | havoc {st : State} {x : String} (n : Nat) :
      EvalR (imp {havoc x}) st (x →ₜ n ; st)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: commands)
open scoped HasEval

instance : HasEval Com State State where
  Eval := Com.EvalR

@[simp]
theorem Com.evalR_eq {c : Com} {st st' : State} :
    EvalR c st st' ↔ st =[ c ]=> st' := by rfl
--  END DETAILS

--  As a sanity check, the following claims should be provable for your
--  definition:

example : ∅ =[ havoc X ]=> (X →ₜ 0) := by
  constructor

example : ∅ =[ skip; havoc Z ]=> (Z →ₜ 42) := by
  apply Com.EvalR.seq; constructor; constructor

--  Finally, we repeat the definition of command equivalence from above:

def Com.Equiv (c₁ c₂ : Com) : Prop := ∀ (st st' : State),
  (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st')

instance : Equiv Com where
  equiv := Com.Equiv

@[simp]
theorem Com.equiv_notation {c₁ c₂ : Com} : c₁.Equiv c₂ ↔ c₁ ≃ c₂ := by rfl
@[simp]
theorem Com.equiv_def {c₁ c₂ : Com} : c₁ ≃ c₂ ↔
    ∀ {st st' : State}, (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st') := by rfl

--  Let's apply this definition to prove some nondeterministic programs
--  equivalent / inequivalent.

--  ### Exercise (3 stars): havoc_swap (Optional, Manually graded) ⭐⭐⭐

--  Are the following two programs equivalent?

def pXY := imp { havoc X ; havoc Y }

def pYX := imp { havoc Y; havoc X }

--  If you think they are equivalent, prove it. If you think they are not,
--  prove that.

--  Note that this is proving something general, considering arbitrary x
--  and y, not just the (distinct) string constants X and Y; this is why
--  the case distinction is needed.

theorem pXY_approx_pYX {x y : String} {st st' : State}
  (h : st =[ havoc x; havoc y ]=> st') :
  st =[ havoc y; havoc x ]=> st' := by

  by_cases hid : x = y
  · subst_vars; assumption
  · inversion h with
    | seq h₁ h₂ =>
      subst_vars
      inversion h₁; inversion h₂
      constructor; constructor; assumption
      rw [TotalMap.update_permute]; constructor; lia

theorem pXY_cequiv_pYX :
  (pXY ≃ pYX) ∨ ¬ (pXY ≃ pYX) := by
/- Hint: You may want to use `update_permute` at some point,
     in which case you'll probably be left with `X ≠ Y` as a
     hypothesis. You can use `contradiction to discharge this. -/
  left; intro st st'
  constructor <;> apply pXY_approx_pYX

--  ### Exercise (4 stars): havoc_copy (Optional) ⭐⭐⭐⭐

--  Are the following two programs equivalent?

def ptwice :=
  (imp { havoc X; havoc Y })

def pcopy :=
  (imp { havoc X; Y := X })

--  If you think they are equivalent, then prove it. If you think they are
--  not, then prove that. (Hint: You may find the `have` tactic useful.)

theorem ptwice_equiv_pcopy :
  (ptwice ≃ pcopy) ∨ ¬(ptwice ≃ pcopy) := by

  right; intro contra
  have h : ∅ =[ ptwice ]=> (Y →ₜ 1 ; X →ₜ 0) := by
    apply @Com.EvalR.seq (st' := X →ₜ 0) <;> constructor
  rw [contra] at h
  inversion h with
  | seq h₁ h₂ =>
    inversion h₁; inversion h₂ with
    | asgn n x h =>
        subst_vars; simp only [cond_eq_ite, beq_iff_eq, Aexp.eval_id, TotalMap.update_eq] at h
        have hy := congrFun h Y
        have hx := congrFun h X
        simp only [↓reduceIte] at hy
        simp only [TotalMap.update_eq, ite_self] at hx; rw [←hy] at hx
        contradiction

--  (End of exercise)

--  The definition of program equivalence we are using here has some subtle
--  consequences on programs that may loop forever. What `Equiv` says is
--  that the set of possible *terminating* outcomes of two equivalent
--  programs is the same. However, in a language with nondeterminism, like
--  Himp, some programs always terminate, some programs always diverge, and
--  some programs can nondeterministically terminate in some runs and
--  diverge in others. The final part of the following exercise illustrates
--  this phenomenon.

--  ### Exercise (4 stars): p₁_p₂_term (Advanced) ⭐⭐⭐⭐

--  Consider the following commands:

def p₁ : Com :=
  imp {
    while (¬ (X = 0)) {
       havoc Y;
       X := X + 1
    }
  }

def p₂ : Com :=
  imp{
    while (¬ (X = 0)) {
       skip
    }
  }

--  Intuitively, `p₁` and `p₂` have the same termination behavior: either
--  they loop forever, or they terminate in the same state they started in.
--  We can capture the termination behavior of `p₁` and `p₂` individually
--  with these lemmas:

theorem p₁_may_diverge (st st' : State) (h : st[X] ≠ 0) :
  ¬ (st =[ p₁ ]=> st') := by
  intro contra
  generalize h : p₁ = p₁' at contra
  induction contra with inversion h
  | whileFalse h' => simp_all [Bexp.eval]
  | whileTrue hb hc hloop ihc ihloop =>
      apply ihloop <;> try rfl
      inversion hc with
      | seq h₁ h₂ =>
        inversion h₁; inversion h₂
        rw [TotalMap.update_eq]; simp_all; lia

theorem p₂_may_diverge (st st' : State) (h : st[X] ≠ 0) :
  ¬ (st =[ p₂ ]=> st') := by
  intro contra
  generalize h : p₂ = p₂' at contra
  induction contra with inversion h
  | whileFalse h' => simp_all [Bexp.eval]
  | whileTrue hb hc hloop ihc ihloop =>
      inversion hc; apply ihloop <;> trivial

--  ### Exercise (4 stars): p₁_p₂_equiv (Advanced) ⭐⭐⭐⭐

--  Use these two lemmas to prove that `p₁` and `p₂` are actually
--  equivalent.

theorem p₁_p₂_equiv : p₁ ≃ p₂ := by
  intro st st'; constructor <;> intro h
  · cases h with
    | whileFalse h' => constructor; assumption
    | whileTrue hb hc hloop =>
        apply p₁_may_diverge at hloop; contradiction
        simp only [Bexp.eval, Aexp.eval,
          Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at hb
        inversion hc with
        | seq h₁ h₂ =>
          inversion h₁; inversion h₂
          rw [TotalMap.update_eq]; simp_all; lia
  · cases h with
        | whileFalse h' => constructor; assumption
        | whileTrue hb hc hloop =>
          apply p₂_may_diverge at hloop; contradiction
          simp only [Bexp.eval, Aexp.eval,
            Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at hb
          inversion hc; assumption

--  ### Exercise (4 stars): p₃_p₄_inequiv (Advanced) ⭐⭐⭐⭐

--  Prove that the following programs are *not* equivalent. (Hint: What
--  should the value of `Z` be when `p₃` terminates? What about `p₄`?)

def p₃ : Com :=
  imp {
    Z := 1;
    while (X ≠ 0) {
      havoc X;
      havoc Z
    }
  }

def p₄ : Com :=
  imp {
    X := 0;
    Z := 1
  }

--  First, note that the programs `p₃` and `p₄` are not equivalent: when
--  `p₃` terminates, even though `X` definitely has value `0`, `Z` might
--  have any natural number as the value.

theorem p₃_p₄_inequiv : ¬ (p₃ ≃ p₄) := by
  intro contra
  let st := X →ₜ 1
  have h : st =[ p₃ ]=> (Z →ₜ 0 ; X →ₜ 0 ; Z →ₜ 1 ; st) := by
    constructor
    · constructor; rfl
    · simp only [Aexp.eval_num, Com.evalR_eq]
      apply Com.EvalR.whileTrue
      · simp only [Bexp.eval_neq, Aexp.eval_id, Aexp.eval_num, bne_iff_ne, ne_eq]
        rw [TotalMap.update_neq, TotalMap.update_eq] <;> trivial
      · constructor
        apply Com.EvalR.havoc (n := 0)
        apply Com.EvalR.havoc (n := 0)
      · apply Com.EvalR.whileFalse
        · simp only [Bexp.eval_neq, Aexp.eval_id, Aexp.eval_num, bne_eq_false_iff_eq]
          rw [TotalMap.update_permute, TotalMap.update_eq]; trivial

  simp only [Com.equiv_def] at contra
  apply contra.mp at h
  inversion h with
  | seq h₁ h₂ =>
      inversion h₁; simp_all only [Aexp.eval_num, Com.evalR_eq]; subst_vars
      rw [TotalMap.update_shadow, TotalMap.update_permute,
          TotalMap.update_shadow, TotalMap.update_permute] at h₂ <;> try trivial
      inversion h₂ with
      | asgn _ h _ h' =>
        have hz := congrFun h' Z
        simp only [Aexp.eval] at h; subst_vars
        simp at hz

--  ### Exercise (5 stars): p₅_p₆_equiv (Advanced, Optional) ⭐⭐⭐⭐⭐

--  Prove that the following commands are equivalent. (Hint: As mentioned
--  above, our definition of `Equiv` for Himp only takes into account the
--  sets of possible terminating configurations: two programs are
--  equivalent if and only if the set of possible terminating states is the
--  same for both programs when given a same starting state `st`. If `p₅`
--  terminates, what should the final state be? Conversely, is it always
--  possible to make `p₅` terminate?)

def p₅ : Com :=
  imp {
    while (X ≠ 1) {
      havoc X
    }
  }

def p₆ : Com := imp { X := 1 }

--  Programs `p₅` and `p₆` are equivalent although `p₅` may diverge, while
--  `p₆` always terminates. The definition we took for `Equiv` cannot
--  distinguish between these two scenarios. It accepts the two programs as
--  equivalent on the basis that: if `p₅` terminates it produces the same
--  final state as `p₆`, and there exists an execution in which `p₅`
--  terminates and does exactly as `p₆`.
--
--  There are two directions to the proof:
--
--  `→`: Observe that whenever `p₅` terminates, it does so with `X` set to
--  `1`, and no other variable changed. But this is exactly the behavior of
--  `p₆`. Thus given a pair of states `st` and `st'` and that
--  `st =[ p₅ ]=> st'`, the answer to the question "Does
--  `st =[ p₆ ]=> st'`?" is "Yes".
--
--  `←` (and more controversially): Given that `st =[ p₆ ]=> st'` for some
--  `st` and `st'`, can we show that `st =[ p₅ ]=> st'`? Observe that we
--  can use the hypothesis to conclude that `st' = (X →ₜ 1 ; st)`. Is there
--  some execution of `p₅` starting from `st` which also ends up in `st'`?
--  Yes!
--
--  Hence their equivalence.

theorem p₅_summary (st st' : State) (h : st =[ p₅ ]=> st') : st' = (X →ₜ 1 ; st) := by

  generalize hp : p₅ = p₅' at h
  induction h with inversion hp
  | whileFalse h' =>
    simp only [Bexp.eval_neq, Aexp.eval_id, Aexp.eval_num, bne_eq_false_iff_eq] at h'
    rw [←h', TotalMap.update_same]
  | whileTrue hb hc hloop ihc ihloop =>
      specialize ihloop rfl; subst_vars
      inversion hc
      apply TotalMap.update_shadow

theorem p₅_p₆_equiv : p₅ ≃ p₆ := by
  intro st st'; constructor <;> intro h
  · apply p₅_summary at h; subst_vars
    constructor; rfl
  · inversion h with
    | asgn n h =>
      simp only [Aexp.eval_num] at h; rw [←h]
      by_cases hx : st[X] = 1
      · rw [←hx, TotalMap.update_same]
        apply Com.EvalR.whileFalse; simp_all
      · apply Com.EvalR.whileTrue (st' := X →ₜ 1 ; st)
        · simp_all
        · constructor
        · apply Com.EvalR.whileFalse; simp_all

--  (End of exercise)

end Himp

--  ## Additional Exercises

--  ### Exercise (3 stars): swap_noninterfering_assignments (Optional) ⭐⭐⭐

--  (Hint: You may or may not - depending how you approach it - need to use
--  `ext` explicitly for this one.)

theorem swap_noninterfering_assignments (l₁ l₂ : String) (a₁ a₂ : Aexp)
  (hl : l₁ ≠ l₂)
  (h₁ : VarNotUsedInAexp l₁ a₂)
  (h₂ : VarNotUsedInAexp l₂ a₁) :
  imp { l₁ := a₁; l₂ := a₂ } ≃ imp { l₂ := a₂; l₁ := a₁ } := by
    have hs : ∀ {l₁ l₂ : String} {a₁ a₂ : Aexp},
        l₁ ≠ l₂ →
        VarNotUsedInAexp l₁ a₂ →
        VarNotUsedInAexp l₂ a₁ →
        ∀ {st st' : State},
          (st =[ l₁ := a₁; l₂ := a₂ ]=> st') →
          st =[ l₂ := a₂; l₁ := a₁ ]=> st' := by
      intro l₁ l₂ a₁ a₂ hneq hne₁ hne₂ st st' h
      inversion h with
      | seq h₁ h₂ =>
        inversion h₂; inversion h₁; subst_vars
        constructor; constructor; rfl
        simp only [Com.evalR_eq]
        rw [TotalMap.update_permute]
        have heq : a₂.eval (l₁ →ₜ Aexp.eval st a₁ ; st) = a₂.eval st := by
          apply Aexp.eval_weakening; assumption
        rw [heq]; constructor; apply Aexp.eval_weakening; assumption; lia

    intro st st'; constructor <;> intro h
    · apply hs hl h₁ h₂ h
    · apply hs (by lia) h₂ h₁ h

--  ### Exercise (4 stars): for_while_equiv (Optional) ⭐⭐⭐⭐

--  This exercise extends the optional `add_for_loop` exercise from the Imp
--  chapter, where you were asked to extend the language of commands with
--  C-style `for` loops. Prove that the command:

--  for (c₁; b; c₂) {
--    c₃
--  }

--  is equivalent to:

--  c₁;
--  while (b) {
--    c₃;
--    c₂
--  }

--  ### Exercise (4 stars): cApprox (Advanced, Optional) ⭐⭐⭐⭐

--  In this exercise we define an asymmetric variant of program equivalence
--  we call *program approximation*. We say that a program `c₁`
--  *approximates* a program `c₂` when, for each of the initial states for
--  which `c₁` terminates, `c₂` also terminates and produces the same final
--  state. Formally, program approximation is defined as follows:

def Approx (c₁ c₂ : Com) : Prop := forall (st st' : State),
  (st =[ c₁ ]=> st') → (st =[ c₂ ]=> st')

--  For example, the program `c₁`

--  while (X ≠ 1) {
--    X := X - 1
--  }

--  approximates `c₂`: `X := 1`, but `c₂` does not approximate `c₁` since
--  `c₁` does not terminate when `X = 0` but `c₂` does. If two programs
--  approximate each other in both directions, then they are equivalent.
--
--  Find two programs `c₃` and `c₄` such that neither approximates the
--  other.

def c₃ : Com := (imp { X := 1 })
def c₄ : Com := (imp { X := 2 })

theorem c₃_c₄_different : ¬ (Approx c₃ c₄) ∧ ¬ (Approx c₄ c₃) := by
  constructor <;> intro contra
  · have h : ∅ =[ c₃ ]=> (X →ₜ 1) := by
      constructor; simp
    apply contra at h
    inversion h with
    | asgn n h _ h' =>
      have hx := congrFun h' X
      rw [←h] at hx
      simp at hx
  · have h : ∅ =[ c₄ ]=> (X →ₜ 2) := by
      constructor; simp
    apply contra at h
    inversion h with
    | asgn n h _ h' =>
      have hx := congrFun h' X
      rw [←h] at hx
      simp at hx

--  Find a program `cMin` that approximates every other program.

def cMin : Com := (imp { while (true) { skip } })

theorem cMin_minimal (c : Com) : Approx cMin c := by
  intro st st' h
  apply loop_never_stops at h
  contradiction

--  Finally, find a non-trivial property which is preserved by program
--  approximation (when going from left to right).

def zprop (c : Com) : Prop := (forall st, exists st', (st =[ c ]=> st'))

--  Intuitively, `zprop` holds of programs that terminate on all inputs.

theorem zprop_preserving (c c' : Com) (hc : zprop c) (ha : Approx c c') : zprop c' := by
  rw [zprop] at *
  intro st
  specialize hc st
  obtain ⟨st', h⟩ := hc
  apply ha at h; exists st'

-- Built on 2026-09-15 21:42 UTC

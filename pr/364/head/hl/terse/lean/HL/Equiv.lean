import LF.CustomTactics
import LF.Typeclasses
import HL.Imp

import SFLCompat

--  # Equiv: Program Equivalence

open scoped HasEval MyGetElem Com

open scoped HasEval MyGetElem

--  ## Behavioral Equivaleence

--  ### Definitions

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

def Com.Equiv (c₁ c₂ : Com) : Prop :=
    ∀ {st st' : State},
      (st =[ ~c₁ ]=> st') ↔ (st =[ ~c₂ ]=> st')

theorem Com.equiv_def {c₁ c₂ : Com} : c₁.Equiv c₂ ↔
    ∀ {st st' : State}, (st =[ ~c₁ ]=> st') ↔ (st =[ ~c₂ ]=> st') := by rfl

--  ### Simple Examples

namespace Com

theorem skip_left {c : Com} : (imp { skip; ~c }).Equiv c := by
  sorry

--  ### Exercise (2 stars): skip_right ⭐⭐

--  Prove that adding a `skip` *after* a command also
--  results in an equivalent program.

theorem skip_right {c : Com} : (imp { ~c; skip }).Equiv c := by
  sorry

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

--  Show that we can swap the branches of an `if` if we also
--  negate its condition.

theorem swap_if_branches {b : Bexp} {c₁ c₂ : Com} :
    (imp {if (~b) {~c₁} else {~c₂}}).Equiv
    (imp {if (¬ ~b) {~c₂} else {~c₁}}) := by
  sorry

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

theorem while_true_nonterm {b : Bexp} {c : Com} {st st' : State} (hb : b.Equiv (bexp {true})) :
    ¬ st =[ while (~b) {~c} ]=> st' := by
  sorry -- heq says that different commands are equal

--  ### Exercise (2 stars): while_true_nonterm_informal (Manually graded) ⭐⭐

--  Explain what the lemma `while_true_nonterm` means in
--  English.

--  ### Exercise (2 stars): while_true ⭐⭐

--  Prove the following theorem. *Hint*: You'll want to use
--  `while_true_nonterm` here.

theorem while_true {b : Bexp} {c : Com} (hb : b.Equiv (bexp {true})) :
    (imp {while (~b) {~c}}).Equiv
    (imp {while (true) {skip}}) := by
  sorry

theorem loop_unrolling {b : Bexp} {c : Com} :
    (imp {while (~b) {~c}}).Equiv
    (imp {
      if (~b) {~c} else {skip};
      while (~b) {~c}
    }) := by
  sorry

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

--  ### Behavioral Equivalence is an Equivalence

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

-- Built on 2026-09-03 15:03 UTC

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

--  ### Exercise (2 stars): while_false_informal (Advanced, manually graded) ⭐⭐

--  Write an informal proof of `while_false_equiv`.

theorem while_true_nonterm {b : Bexp} {c : Com} {st st' : State} (hb : b.Equiv (bexp {true})) :
    ¬ st =[ while (~b) {~c} ]=> st' := by
  sorry -- heq says that different commands are equal

--  ### Exercise (2 stars): while_true_nonterm_informal (manually graded) ⭐⭐

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

theorem Com.congruence_asgn {x : Ident} {a a' : Aexp} (ha : a.Equiv a') :
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

theorem Com.congruence_while {b b' : Bexp} {c c' : Com} (hb : b.Equiv b') (hc : c.Equiv c') :
    (imp {while (~b) {~c}}).Equiv
    (imp {while (~b') {~c'}}) := by
  sorry

--  ### Exercise (3 stars): Com.congruence_seq (Optional) ⭐⭐⭐

theorem Com.congruence_seq {c1 c1' c2 c2' : Com} (hc1 : c1.Equiv c1') (hc2 : c2.Equiv c2') :
    (imp {~c1 ; ~c2}).Equiv (imp {~c1' ; ~c2'}) := by
  sorry

--  ### Exercise (3 stars): Com.congruence_if ⭐⭐⭐

theorem Com.congruence_if {b b' : Bexp} {c1 c1' c2 c2' : Com} (hb : b.Equiv b') (hc1 : c1.Equiv c1') (hc2 : c2.Equiv c2') :
    (imp {if (~b) {~c1} else {~c2}}).Equiv
    (imp {if (~b') {~c1'} else {~c2'}}) := by
  sorry

example :
    (imp {X := 0; if (X = 0) {Y := 0} else {Y := 42}}).Equiv
    (imp {X := 0; if (X = 0) {Y := X - X} else {Y := 42}}) := by
  apply Com.congruence_seq
  · apply Com.equiv_refl
  · apply Com.congruence_if
    · apply Bexp.equiv_refl
    · apply Com.congruence_asgn
      rw [Aexp.equiv_def]
      simp
    · apply Com.equiv_refl

--  ### Exercise (3 stars): not_congr (Advanced, manually graded) ⭐⭐⭐

--  We've shown that the `Com.Equiv` relation is both an
--  equivalence and a congruence on commands. Can you think
--  of a relation on commands that is an equivalence but
--  *not* a congruence? Write down the relation (formally),
--  together with an informal sketch of a proof that it is
--  an equivalence and a counterexample showing it is not a
--  congruence.

--  ## Program Transformation

def Aexp.TransSound (trans : Aexp → Aexp) : Prop :=
  ∀ (a : Aexp), a.Equiv (trans a)

theorem Aexp.transSound_def {trans : Aexp → Aexp} :
    TransSound trans ↔ ∀ (a : Aexp), a.Equiv (trans a) := by rfl

def Bexp.TransSound (trans : Bexp → Bexp) : Prop :=
  ∀ (b : Bexp), b.Equiv (trans b)

theorem Bexp.transSound_def {trans : Bexp → Bexp} :
    TransSound trans ↔ ∀ (b : Bexp), b.Equiv (trans b) := by rfl

def Com.TransSound (trans : Com → Com) : Prop :=
  ∀ (c : Com), c.Equiv (trans c)

theorem Com.transSound_def {trans : Com → Com} :
    TransSound trans ↔ ∀ (c : Com), c.Equiv (trans c) := by rfl

--  ### The Constant-Folding Transformation

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
    (aexp {~a₁ + ~a₂}).foldConstants = (aexp {~a₁.foldConstants + ~a₂.foldConstants}) ∧
    (aexp {~a₁ - ~a₂}).foldConstants = (aexp {~a₁.foldConstants - ~a₂.foldConstants}) ∧
    (aexp {~a₁ * ~a₂}).foldConstants = (aexp {~a₁.foldConstants * ~a₂.foldConstants}) := by
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

example : (aexp { (1 + 2) * X }).foldConstants = (aexp { 3 * X }) := by rfl

example : (aexp { X - ((0 * 6) + Y) }).foldConstants = (aexp { X - (0 + Y) }) := by rfl

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

example : (bexp { true ∧ ¬( false ∧ true) }).foldConstants = (bexp { true }) := by rfl
example : (bexp { (X = Y) ∧ ( 0 = (2 - (1 + 1))) }).foldConstants = (bexp { (X = Y) ∧ true }) := by rfl

def Com.foldConstants (c : Com) : Com :=
  match c with
  | imp { skip } => imp { skip }
  | imp { x := ~a } => imp { x := ~a.foldConstants }
  | imp { ~c₁ ; ~c₂ } =>  imp { ~c₁.foldConstants ; ~c₂.foldConstants }
  | imp { if (~b) {~c₁} else {~c₂}} =>
    match b.foldConstants with
    | bexp { true } => c₁.foldConstants
    | bexp { false } => c₂.foldConstants
    | b' => imp { if (~b') {~c₁.foldConstants} else {~c₂.foldConstants}}
  | imp { while (~b) {~c}} =>
    match b.foldConstants with
    | bexp { true } => imp { while (true) { skip }}
    | bexp { false } => imp { skip }
    | b' => imp { while (~b') {~c.foldConstants}}

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

theorem Aexp.foldConstants_sound : TransSound foldConstants := by
  rw [transSound_def]
  intro a
  rw [equiv_def]
  intro st
  induction a with
  | num n | id x => rfl
  | _ a₁ a₂ _ _ =>
    cases foldConstants_cases a₁ a₂ with
    | inl h =>
      obtain ⟨n₁, n₂, h₁, h₂⟩ := h
      rw [foldConstants]
      simp_all
    | inr h =>
      simp_all

-- Golfed version with `fun_induction`
theorem Aexp.foldConstants_sound' : TransSound foldConstants := by
  rw [transSound_def]
  intro a
  rw [equiv_def]
  intro st
  fun_induction foldConstants a <;> simp_all


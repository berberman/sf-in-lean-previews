import LF.CustomTactics
import LF.Typeclasses
import HL.Imp

import SFLCompat

--  # Equiv: Program Equivalence

open scoped HasEval MyGetElem Com

--  ## Behavioral Equivalence

--  ### Definitions

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

example : aexp { X - X } ≃ aexp { 0 } := by simp

example : bexp { X - X = 0 } ≃ bexp { true } := by simp

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

theorem skip_left {c : Com} : imp { skip; c } ≃ c := by
  sorry

--  ### Exercise (2 stars): skip_right ⭐⭐

--  Prove that adding a `skip` *after* a command also
--  results in an equivalent program.

theorem skip_right {c : Com} : imp { c; skip } ≃ c := by
  sorry

--  (End of exercise)

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

theorem while_true_nonterm {b : Bexp} {c : Com} {st st' : State} (hb : b ≃ bexp {true}) :
    ¬ st =[ while (b) {c} ]=> st' := by
  sorry -- `heq` says that different commands are equal

theorem loop_unrolling {b : Bexp} {c : Com} :
    imp { while (b) {c} } ≃
    imp {
      if (b) {c} else {skip};
      while (b) {c}
    } := by
  sorry

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

--  ## Properties of Behavior Equivalence

--  ### Behavioral Equivalence is an Equivalence

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

--  ### Behavioral Equivalence is a Congruence

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

theorem Com.congruence_while {b b' : Bexp} {c c' : Com} (hb : b ≃ b') (hc : c ≃ c') :
    imp {while (b) {c}} ≃ imp {while (b') {c'}} := by
  sorry

--  ## Program Transformation

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

example : (aexp { (1 + 2) * X }).foldConstants = (aexp { 3 * X }) := by rfl

example : (aexp { X - ((0 * 6) + Y) }).foldConstants = (aexp { X - (0 + Y) }) := by rfl

def Bexp.foldConstants (b : Bexp) : Bexp :=
  match b with
  | bexp { true } => bexp { true }
  | bexp { false } => bexp { false }
  | bexp { ~a₁ = ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ = n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { a₁' = a₂' }
  | bexp { ~a₁ ≠ ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ ≠ n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { a₁' ≠ a₂' }
  | bexp { ~a₁ ≤ ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ ≤ n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { a₁' ≤ a₂' }
  | bexp { ~a₁ > ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ > n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { a₁' > a₂' }
  | bexp { ¬ ~b₁ } =>
    match b₁.foldConstants with
    | bexp { true } => bexp { false }
    | bexp { false } => bexp { true }
    | b₁' => bexp { ¬ b₁' }
  | bexp { ~b₁ ∧ ~b₂ } =>
    match b₁.foldConstants, b₂.foldConstants with
    | bexp { true }, bexp { true } => bexp { true }
    | bexp { true }, bexp { false } => bexp { false }
    | bexp { false }, bexp { true } => bexp { false }
    | bexp { false }, bexp { false } => bexp { false }
    | b₁', b₂' => bexp { b₁' ∧ b₂' }

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
    (bexp { ¬b }).foldConstants = (bexp { ¬(b.foldConstants)}) := by
  cases hb : b.foldConstants with
  | bool b' =>
    simp_all
  | _ =>
    simp [foldConstants, hb]

theorem Bexp.foldConstants_binary (b₁ : Bexp) (b₂ : Bexp) :
    ((b₁.foldConstants = (bexp { true }) ∨ b₁.foldConstants = (bexp { false })) ∧
     (b₂.foldConstants = (bexp { true }) ∨ b₂.foldConstants = (bexp { false }))) ∨
    (bexp {b₁ ∧ b₂}).foldConstants = (bexp {b₁.foldConstants ∧ b₂.foldConstants}) := by
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

--  An equivalent version using the `fun_induction` tactic
--  would look simpler:

theorem Aexp.foldConstants_sound' : TransSound Aexp.foldConstants := by
  intro a st
  fun_induction Aexp.foldConstants <;> simp_all

--  ## Proving Inequivalence

--  Next, let's look at some programs that are *not*
--  equivalent.
--
--  Suppose that `c₁` is a command of the form

--  X := a₁; Y := a₂

--  and `c₂` is the command

--  X := a₁; Y := a₂'

--  where `a₂'` is formed by substituting `a₁` for all
--  occurrences of `X` in `a₂`.
--
--  For example, `c₁` and `c₂` might be:

--  c₁  =  (X := 42 + 53;
--                 Y := Y + X)
--         c₂  =  (X := 42 + 53;
--                 Y := Y + (42 + 53))

--  Clearly, this *particular* `c₁` and `c₂` are equivalent.
--  Is this true in general?
--
--  More formally, here is the function that substitutes an
--  arithmetic expression `u` for each occurrence of a given
--  variable `x` in another expression `a`:

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

--  And here is the property we are interested in,
--  expressing the claim that commands `c₁` and `c₂` as
--  described above are always equivalent.

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

-- Source revision: 28c1d13, committed 2026-09-22 17:33 UTC

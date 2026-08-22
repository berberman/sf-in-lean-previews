import LF.Typeclasses
import HL.Imp

import HL.SFLCompat

-- # Equiv: Program Equivalence

open scoped HasEval MyGetElem Com

-- Note to developers (Sati @satiscugcat):
--     At this point, the Rocq file provides instructions about
--     using a new directory, making sure the project is set up
--     properly, and also instructions about how to deal with
--     the exercises. I am assuming these things are being
--     moved to Intro.lean? I am excluding them for now.

-- Note to developers (Sati @satiscugcat):
--     `namespace Equiv`

-- ## Behavioral Equivaleence

-- ### Definitions

def Aexp.equiv (a₁ a₂ : Aexp) : Prop :=
  ∀ (st: State),
    a₁.eval st = a₂.eval st

def Bexp.equiv (b₁ b₂ : Bexp) : Prop :=
  ∀ (st: State),
    b₁.eval st = b₂.eval st

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

def Com.equiv (c₁ c₂: Com) : Prop :=
    ∀ (st st': State),
      (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st')

-- ### Simple Examples

theorem skip_left: ∀ c,
  Com.equiv
    (imp { skip; ~c })
    c := by
  sorry

-- Note to developers (Sati @satiscugcat):
--     Is the syntax of Imp settled? I find this really
--     unintuitive.

-- ### Exercise (2 stars): skip_right ⭐⭐

-- Prove that adding a `skip` *after* a command also results in
-- an equivalent program.

theorem skip_right : ∀ c,
  Com.equiv
    (imp { ~c; skip })
    c := by
  sorry

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

-- Note to developers (Sati @satiscugcat):
--     The to_verso script seems to use `\[\]` blocks, but
--     these seem to cause problems with the tilde. Currently
--     skipping them and just using backticks.

-- Note to developers (Sati @satiscugcat):
--     `if_true` causes a naming conflict, I don't know with
--     what.

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
    | ifFalse hb' hc =>
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
  sorry

-- ### Exercise (3 stars): swap_if_branches ⭐⭐⭐

-- Show that we can swap the branches of an `if` if we also
-- negate its condition.

theorem swap_if_branches : ∀ b c₁ c₂,
  Com.equiv
    (imp {if (~b) {~c₁} else {~c₂}})
    (imp {if (¬ ~b) {~c₂} else {~c₁}}) := by
  sorry

theorem while_false_equiv : ∀ b c,
  Bexp.equiv b (bexp {false}) ->
  Com.equiv
    (imp {while (~b) {~c}})
    (imp {skip}) := by
  intro b c hb st st'
  constructor <;> intro h
  case mp =>
    cases h with
    | whileFalse => apply Com.EvalR.skip
    | whileTrue hb' hc hloop =>
      rw [hb] at hb'
      simp at hb'
  case mpr =>
    cases h with
    | skip =>
      apply Com.EvalR.whileFalse
      apply hb

-- ### Exercise (2 stars): while_false_informal (Advanced, manually graded) ⭐⭐

-- Write an informal proof of `while_false_equiv`.

theorem while_true_nonterm : ∀ b c st st',
  Bexp.equiv b (bexp {true}) ->
  ¬ (st =[ while (~b) {~c} ]=> st') := by
  sorry

-- ### Exercise (2 stars): while_true_nonterm_informal (manually graded) ⭐⭐

-- Explain what the lemma `while_true_nonterm` means in
-- English.

-- ### Exercise (2 stars): while_true ⭐⭐

-- Prove the following theorem. *Hint*: You'll want to use
-- `while_true_nonterm` here.

theorem while_true : ∀ b c,
  Bexp.equiv b (bexp {true}) ->
  Com.equiv
    (imp {while (~b) {~c}})
    (imp {while (true) {skip}}) := by
  sorry

theorem loop_unrolling : ∀ b c,
  Com.equiv
    (imp {while (~b) {~c}})
    (imp {
      if (~b) {~c} else {skip};
      while (~b) {~c}
    }) := by
  sorry

-- Note to developers (Sati @satiscugcat):
--     Leaving out optional exercise `seq_assoc` for now.

-- Note to developers (Sati @satiscugcat):
--     I am not able to use `m[x]` syntax here for some reason?
--     I have to use function application and then do some
--     weird manipulation. syntax.

theorem identity_assignment : ∀ X,
  Com.equiv
    (imp {X := X})
    (imp {skip}) := by
  intro X st st'
  constructor <;> intro hce
  case mp =>
    cases hce with
    | asgn  h =>
      dsimp at h
      rw [← h, TotalMap.update_same]
      apply Com.EvalR.skip

  case mpr =>
    cases hce with
    | skip =>
      suffices st =[ X := X ]=> X →ₜ st[X] ; st by
        simp only [TotalMap.update_same] at this
        exact this
      apply Com.EvalR.asgn
      simp

-- ### Exercise (2 stars): assign_equiv ⭐⭐

theorem assign_equiv : ∀ (X : Ident) (a : Aexp),
  Aexp.equiv (aexp {X}) a ->
  Com.equiv
    (imp {skip})
    (imp {X := ~a}) := by
  sorry

-- Note to developers (Sati @satiscugcat):
--     Leaving out optional exercise `equiv_classes` for now.

-- ## Properties of Behavior Equivalence

-- ### Behavioral Equivalence is an Equivalence

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

theorem Com.congruence.asgn : ∀ x a a',
  Aexp.equiv a a' ->
  Com.equiv (imp {x := ~a}) (imp {x := ~a'}) := by
  intro x a a' heqv st st'
  constructor <;> intro hce
  case mp =>
    cases hce with
    | asgn  h =>
      subst h; apply Com.EvalR.asgn
      rw [heqv]
  case mpr =>
    cases hce with
    | asgn  h =>
      subst h; apply Com.EvalR.asgn
      rw [heqv]

-- Note to developers (Sati @satiscugcat):
--     `NOT PORTED YET - remaining portions of Equiv.v left (apart from the portions explicitly stated so far).
--       - The rest of "Behavioural Equivalence is a Congruence"
--       - The section on "Program Transformation"
--       - Soundness of (0 + n) Elimination
--       - Extended Exercise: Nondeterministic Imp
--       - Additional Exercises`


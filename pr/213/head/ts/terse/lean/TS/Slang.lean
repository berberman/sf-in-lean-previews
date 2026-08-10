import TS.SFLCompat

-- # Slang: Arithmetic and Boolean Expressions

-- Note to developers (Benjamin Pierce @bcpierce00):
--     We need to figure out our approach to text width,
--     especially for proofs. Quite a few proofs here don't
--     render into the chosen page width, and for terse mode it
--     will be worse.

-- ## Arithmetic and Boolean Expressions

-- ### Syntax

namespace Slang

-- Abstract syntax trees for arithmetic and boolean
-- expressions:

inductive Aexp where
  | num (n : Nat)
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)

inductive Bexp where
  | bool (b : Bool)
  | eq (a1 a2 : Aexp)
  | neq (a1 a2 : Aexp)
  | le (a1 a2 : Aexp)
  | gt (a1 a2 : Aexp)
  | not (b : Bexp)
  | and (b1 b2 : Bexp)

-- ### Evaluation

-- *Evaluating* an arithmetic expression produces a number.

def Aexp.eval (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | plus  a1 a2 =>  a1.eval + a2.eval
  | minus a1 a2 =>  a1.eval - a2.eval
  | mult  a1 a2 =>  a1.eval * a2.eval

@[simp] theorem Aexp.eval_num (n : Nat) : (num n).eval = n := rfl
@[simp] theorem Aexp.eval_plus (a1 a2 : Aexp) : (plus a1 a2).eval = a1.eval + a2.eval := rfl
@[simp] theorem Aexp.eval_minus (a1 a2 : Aexp) : (minus a1 a2).eval = a1.eval - a2.eval := rfl
@[simp] theorem Aexp.eval_mult (a1 a2 : Aexp) : (mult a1 a2).eval = a1.eval * a2.eval := rfl

example : Aexp.eval (.plus (.num 2) (.num 2)) = 4 := by simp

-- Similarly, evaluating a boolean expression yields a boolean,
-- and we give it the same treatment.

def Bexp.eval (b : Bexp) : Bool :=
  match b with
  | bool b     =>  b
  | eq   a1 a2 =>  a1.eval == a2.eval
  | neq  a1 a2 =>  a1.eval != a2.eval
  | le   a1 a2 =>  a1.eval ≤ a2.eval
  | gt   a1 a2 =>  a1.eval > a2.eval
  | not  b1    =>  !eval b1
  | and  b1 b2 =>  eval b1 && eval b2

@[simp] theorem Bexp.eval_bool (b : Bool) : (bool b).eval = b := rfl
@[simp] theorem Bexp.eval_eq (a1 a2 : Aexp) : (eq a1 a2).eval = (a1.eval == a2.eval) := rfl
@[simp] theorem Bexp.eval_neq (a1 a2 : Aexp) : (neq a1 a2).eval = (a1.eval != a2.eval) := rfl
@[simp] theorem Bexp.eval_le (a1 a2 : Aexp) : (le a1 a2).eval = (a1.eval ≤ a2.eval : Bool) := rfl
@[simp] theorem Bexp.eval_gt (a1 a2 : Aexp) : (gt a1 a2).eval = (a1.eval > a2.eval : Bool) := rfl
@[simp] theorem Bexp.eval_not (b : Bexp) : (not b).eval = !b.eval := rfl
@[simp] theorem Bexp.eval_and (b1 b2 : Bexp) : (and b1 b2).eval = (b1.eval && b2.eval) := rfl

-- It's worth noting that `≤` and `>` are `Prop`-valued, i.e.
-- `a1.eval st ≤ a2.eval st` is a proposition, but `Bexp.eval`
-- returns a `Bool` so Lean implicitly inserts a `decide`
-- coercion. You can observe the call to `decide` by hovering
-- over `Bexp.eval_le` and `Bexp.eval_gt`.

-- _Quiz:_

-- What does the following expression evaluate to?

-- Aexp.eval (.plus (.num 3) (.minus (.num 4) (.num 1)))

-- (A) true (B) false (C) 0 (D) 3 (E) 6

-- ### Optimization

def Aexp.optimize0plus (a : Aexp) : Aexp :=
  match a with
  | num   n          => num n
  | plus  (num 0) e2 => optimize0plus e2
  | plus  e1      e2 => plus  (optimize0plus e1) (optimize0plus e2)
  | minus e1      e2 => minus (optimize0plus e1) (optimize0plus e2)
  | mult  e1      e2 => mult  (optimize0plus e1) (optimize0plus e2)

example :
    Aexp.optimize0plus (.plus (.num 2)
                               (.plus (.num 0)
                                      (.plus (.num 0) (.num 1))))
      = .plus (.num 2) (.num 1) := by rfl

theorem optimize0plus_sound (a : Aexp) :
    a.optimize0plus.eval = a.eval := by
  induction a with
  | num n => rfl
  | plus a1 a2 ih1 ih2 =>
    cases a1 with
    | num n =>
      cases n with
      | zero =>
        simp only [Aexp.optimize0plus, Aexp.eval_plus, Aexp.eval_num, Nat.zero_add]
        exact ih2
      | succ n =>
        simp only [Aexp.optimize0plus, Aexp.eval_plus, Aexp.eval_num]
        rw [ih2]
    | plus b1 b2 =>
      simp only [Aexp.optimize0plus, Aexp.eval_plus] at ih1 ⊢
      rw [ih1, ih2]
    | minus b1 b2 =>
      simp only [Aexp.optimize0plus, Aexp.eval_plus] at ih1 ⊢
      rw [ih1, ih2]
    | mult b1 b2 =>
      simp only [Aexp.optimize0plus, Aexp.eval_plus] at ih1 ⊢
      rw [ih1, ih2]
  | minus a1 a2 ih1 ih2 =>
    simp only [Aexp.optimize0plus, Aexp.eval_minus]
    rw [ih1, ih2]
  | mult a1 a2 ih1 ih2 =>
    simp only [Aexp.optimize0plus, Aexp.eval_mult]
    rw [ih1, ih2]

theorem optimize0plus_sound' (a : Aexp) :
    a.optimize0plus.eval = a.eval := by
  fun_induction Aexp.optimize0plus a <;> simp_all

-- ### Exercise (3 stars): optimize0plusB_sound ⭐⭐⭐

-- Since the `Aexp.optimize0plus` transformation doesn't change
-- the value of an `Aexp`, we should be able to apply it to all
-- the `Aexp`s that appear in a `Bexp` without changing the
-- `Bexp`'s value. Write a function that performs this
-- transformation on `Bexp`s and prove it sound. Use the
-- combinators we've just seen to make the proof as short and
-- elegant as possible.

def Bexp.optimize0plusB (b : Bexp) : Bexp := sorry

theorem optimize0plusB_test1 :
    Bexp.optimize0plusB
        (.not (.gt (.plus (.num 0) (.num 4)) (.num 8)))
      = (.not (.gt (.num 4) (.num 8))) := sorry

theorem optimize0plusB_test2 :
    Bexp.optimize0plusB
        (.and (.le (.plus (.num 0) (.num 4)) (.num 5)) (.bool true))
      = (.and (.le (.num 4) (.num 5)) (.bool true)) := sorry

theorem optimize0plusB_sound (b : Bexp) :
    b.optimize0plusB.eval = b.eval := by
  sorry

-- ### Exercise (4 stars): optimize ⭐⭐⭐⭐

-- The optimization implemented by our `Aexp.optimize0plus` is
-- only one of many possible optimizations on arithmetic and
-- boolean expressions. Write a more sophisticated optimizer
-- and prove it correct. (You will probably find it easiest to
-- start small -- add just a single, simple optimization and
-- its correctness proof -- and build up incrementally to
-- something more interesting.)

-- ## Evaluation as a Relation

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.plus a1 a2) (n1 + n2)
  | minus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.minus a1 a2) (n1 - n2)
  | mult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.mult a1 a2) (n1 * n2)

-- One comment on the style of this definition. We could
-- instead have presented this relation with **positional**
-- hypotheses -- no names for the premises.

namespace ArithUnnamed

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus (e1 e2 : Aexp) (n1 n2 : Nat) : EvalR e1 n1 → EvalR e2 n2 → EvalR (.plus e1 e2) (n1 + n2)
  | minus (e1 e2 : Aexp) (n1 n2 : Nat) : EvalR e1 n1 → EvalR e2 n2 → EvalR (.minus e1 e2) (n1 - n2)
  | mult (e1 e2 : Aexp) (n1 n2 : Nat) : EvalR e1 n1 → EvalR e2 n2 → EvalR (.mult e1 e2) (n1 * n2)

end ArithUnnamed

-- It will be convenient to have an infix notation for
-- `Aexp.EvalR`. We'll write `e ⇓ n` to mean that arithmetic
-- expression `e` evaluates to value `n`.

scoped notation:55 e:56 " ⇓ " n:56 => Aexp.EvalR e n

-- Note to developers (Michael Hicks @mwhicks1, before next release):
--     The Rocq version here says "As we saw in our case study
--     of regular expressions in chapter IndProp, Rocq provides
--     a way to use this notation in the definition of aevalR
--     itself." It then re-shows the definition with Downarrow.
--     We need to resolve how we want to do this.

-- ### Inference Rule Notation

-- Note to developers (Benjamin Pierce @bcpierce00):
--     The first two quizzes here seem kind of boring.

-- _Quiz:_

-- Which rules are needed to prove the following?

-- .mult (.plus (.num 3) (.num 1)) (.num 0) ⇓ 0

-- (A) `num` and `plus` (B) `num` only (C) `num` and `mult` (D)
-- `mult` and `plus` (E) `num`, `mult`, and `plus`

-- Note to developers (Michael Hicks @mwhicks1, before next release):
--     Not sure if we need ⇓b, or whether we can define ⇓
--     overloaded. Don't understand Lean notation yet!

-- Note to developers (Chris Henson @chenson2018, before next release):
--     About `Bexp.eval` below: We should discuss a way to
--     recall definitions without having to write them out
--     manually like this. I think a simple `#print` may work
--     as an alternative, assuming there are no namespace
--     issues..

-- ### Exercise (1 star): beval_rules ⭐

-- Here, again, is the definition of the `Bexp.eval` function:

-- def Bexp.eval (b : Bexp) : Bool :=
--   match b with
--   | bool b     => b
--   | eq   a1 a2 => a1.eval == a2.eval
--   | neq  a1 a2 => a1.eval != a2.eval
--   | le   a1 a2 => a1.eval ≤ a2.eval
--   | gt   a1 a2 => a1.eval > a2.eval
--   | not  b1    => !eval b1
--   | and  b1 b2 => eval b1 && eval b2

-- Write out a corresponding definition of boolean evaluation
-- as a relation (in inference rule notation).

-- ### Equivalence of the Definitions

-- It is straightforward to prove that the relational and
-- functional definitions of evaluation agree.

theorem Aexp.evalR_iff_eval (a : Aexp) (n : Nat) :
    a ⇓ n ↔ a.eval = n := by
  constructor
  · intro h
    induction h with
    | num n => rfl
    | plus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval_plus]; rw [ih1, ih2]
    | minus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval_minus]; rw [ih1, ih2]
    | mult a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval_mult]; rw [ih1, ih2]
  · intro h
    subst h
    induction a with
    | num n => exact .num n
    | plus a1 a2 ih1 ih2 => exact .plus a1 a2 _ _ ih1 ih2
    | minus a1 a2 ih1 ih2 => exact .minus a1 a2 _ _ ih1 ih2
    | mult a1 a2 ih1 ih2 => exact .mult a1 a2 _ _ ih1 ih2

-- We can make the proof quite a bit shorter using more
-- automation like we did in the previous section.

-- Note to developers (Michael Hicks @mwhicks1, before next release):
--     the `workinclass!` marker should signal this live
--     in-class exercise. But it is not rendering properly on
--     the HTML. In fact it replaces `workinclass!` with the
--     `all_goals` tactic, which we don't need.

theorem Aexp.evalR_iff_eval' (a : Aexp) (n : Nat) :
    a ⇓ n ↔ a.eval = n := by
  sorry

-- ### Exercise (3 stars): bevalR ⭐⭐⭐

-- Write a relation `Bexp.EvalR` in the same style as
-- `Aexp.EvalR`, and prove that it is equivalent to
-- `Bexp.eval`.

inductive Bexp.EvalR : Bexp → Bool → Prop where
  -- FILL IN HERE

scoped notation:55 e:56 " ⇓b " b:56 => Bexp.EvalR e b

-- Note to developers (Michael Hicks @mwhicks1):
--     There is no keyboard shortcut for a subscript b, nor is
--     there one for c (to use used with cevalR below). There
--     are numbers, x, y, z, l, m, n, etc.

theorem Bexp.evalR_iff_eval (b : Bexp) (bv : Bool) :
    b ⇓b bv ↔ b.eval = bv := by
  sorry

end Slang

-- ### Computational vs. Relational Definitions

-- Sometimes relational definitions are the only reasonable
-- option...

namespace Slang.AevalRDivision

-- For example, suppose that we wanted to extend the arithmetic
-- operations with division:

inductive Aexp where
  | num (n : Nat)
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)
  | div (a1 a2 : Aexp)             -- NEW

-- Extending the definition of `Aexp.eval` to handle this new
-- operation would not be straightforward due to division being
-- a *partial* operation; i.e., what should we return as the
-- result of `.div (.num 5) (.num 0)`? By contrast, partiality
-- is no problem for the relational version of the definition.

-- What should `Aexp.eval` return for
-- `.div (.num 1) (.num 0)`??

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.plus a1 a2) (n1 + n2)
  | minus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.minus a1 a2) (n1 - n2)
  | mult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.mult a1 a2) (n1 * n2)
  | div (a1 a2 : Aexp) (n1 n2 n3 : Nat)             -- NEW
      (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) (hpos : n2 > 0) (hdiv : n2 * n3 = n1) :
      EvalR (.div a1 a2) n3

-- Notice that there are some inputs (those with a divisor of
-- 0) for which this relation does not specify an output.

end Slang.AevalRDivision

namespace Slang.AevalRExtended

-- Another example: a *nondeterministic* number generator:

-- As another example, suppose that we want to extend the
-- arithmetic operations by a nondeterministic number generator
-- `any` that, when evaluated, may yield any number. (This is
-- not the same as making a *probabilistic* choice among all
-- numbers -- we only say which results are *possible*.)

inductive Aexp where
  | any                            -- NEW
  | num (n : Nat)
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)

-- Again, extending `Aexp.eval` would be tricky, since
-- evaluation is now *not* a deterministic function from
-- expressions to numbers; but extending the relation is no
-- problem.

-- What should `Aexp.eval` do with nondeterminism??

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | any (n : Nat) : EvalR .any n                   -- NEW
  | num (n : Nat) : EvalR (.num n) n
  | plus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.plus a1 a2) (n1 + n2)
  | minus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.minus a1 a2) (n1 - n2)
  | mult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.mult a1 a2) (n1 * n2)

end Slang.AevalRExtended

-- Note to developers (Michael Hicks @mwhicks1, before next release):
--     The following text seems not quite right to me. First,
--     you can use options for partial functions, and that's
--     very natural to do in Lean as a monad. Second, and
--     related, monadic functions need not even be terminating
--     if the implement the `CCPO` typeclass and are labeled as
--     a `partial_fixpoint`. Maybe we don't want to get into
--     the second thing here, but failing to mention options
--     (which I think were introduced in LF) seems a bit
--     surprising.

-- Note to developers (Benjamin Pierce @bcpierce00):
--     Agreed.

-- Functional: computation. Relational: expressive. Best: both,
-- proved equivalent.


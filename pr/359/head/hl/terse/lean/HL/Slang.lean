import SFLCompat

--  # Slang: Arithmetic and Boolean Expressions

--  ## Arithmetic and Boolean Expressions

--  ### Syntax

namespace Slang

--  Abstract syntax trees for arithmetic and boolean
--  expressions:

inductive Aexp where
  | num (n : Nat)
  | plus (a₁ a₂ : Aexp)
  | minus (a₁ a₂ : Aexp)
  | mult (a₁ a₂ : Aexp)

inductive Bexp where
  | bool (b : Bool)
  | eq (a₁ a₂ : Aexp)
  | neq (a₁ a₂ : Aexp)
  | le (a₁ a₂ : Aexp)
  | gt (a₁ a₂ : Aexp)
  | not (b : Bexp)
  | and (b₁ b₂ : Bexp)

--  ### Evaluation

--  *Evaluating* an arithmetic expression produces a number.

namespace Aexp
def eval (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | plus  a₁ a₂ =>  a₁.eval + a₂.eval
  | minus a₁ a₂ =>  a₁.eval - a₂.eval
  | mult  a₁ a₂ =>  a₁.eval * a₂.eval

@[simp] theorem eval_num (n : Nat) : (num n).eval = n := rfl
@[simp] theorem eval_plus (a₁ a₂ : Aexp) : (plus a₁ a₂).eval = a₁.eval + a₂.eval := rfl
@[simp] theorem eval_minus (a₁ a₂ : Aexp) : (minus a₁ a₂).eval = a₁.eval - a₂.eval := rfl
@[simp] theorem eval_mult (a₁ a₂ : Aexp) : (mult a₁ a₂).eval = a₁.eval * a₂.eval := rfl

example : eval (.plus (.num 2) (.num 2)) = 4 := by simp
end Aexp

--  Similarly, evaluating a boolean expression yields a
--  boolean.

namespace Bexp
def eval (b : Bexp) : Bool :=
  match b with
  | bool b     =>  b
  | eq   a₁ a₂ =>  a₁.eval == a₂.eval
  | neq  a₁ a₂ =>  a₁.eval != a₂.eval
  | le   a₁ a₂ =>  a₁.eval ≤ a₂.eval
  | gt   a₁ a₂ =>  a₁.eval > a₂.eval
  | not  b₁    =>  !eval b₁
  | and  b₁ b₂ =>  eval b₁ && eval b₂

@[simp] theorem eval_bool (b : Bool) : (bool b).eval = b := rfl
@[simp] theorem eval_eq (a₁ a₂ : Aexp) : (eq a₁ a₂).eval = (a₁.eval == a₂.eval) := rfl
@[simp] theorem eval_neq (a₁ a₂ : Aexp) : (neq a₁ a₂).eval = (a₁.eval != a₂.eval) := rfl
@[simp] theorem eval_le (a₁ a₂ : Aexp) : (le a₁ a₂).eval = (a₁.eval ≤ a₂.eval : Bool) := rfl
@[simp] theorem eval_gt (a₁ a₂ : Aexp) : (gt a₁ a₂).eval = (a₁.eval > a₂.eval : Bool) := rfl
@[simp] theorem eval_not (b : Bexp) : (not b).eval = !b.eval := rfl
@[simp] theorem eval_and (b₁ b₂ : Bexp) : (and b₁ b₂).eval = (b₁.eval && b₂.eval) := rfl
end Bexp

--  It's worth noting that `≤` and `>` are `Prop`-valued,
--  i.e. `a₁.eval st ≤ a₂.eval st` is a proposition, but
--  `Bexp.eval` returns a `Bool`, so Lean implicitly inserts
--  a `decide` coercion. You can observe the call to
--  `decide` by hovering over `Bexp.eval_le` and
--  `Bexp.eval_gt`.

--   ----------------------------------------

--  _Quiz:_

--  What does the following expression evaluate to?

--  Aexp.eval (.plus (.num 3) (.minus (.num 4) (.num 1)))

--  (A) true (B) false (C) 0 (D) 3 (E) 6

--   ----------------------------------------

--  ### Optimization

namespace Aexp

def optimize0plus (a : Aexp) : Aexp :=
  match a with
  | num   n          => num n
  | plus  (num 0) e₂ => optimize0plus e₂
  | plus  e₁      e₂ => plus  (optimize0plus e₁) (optimize0plus e₂)
  | minus e₁      e₂ => minus (optimize0plus e₁) (optimize0plus e₂)
  | mult  e₁      e₂ => mult  (optimize0plus e₁) (optimize0plus e₂)

example :
    Aexp.optimize0plus (.plus (.num 2)
                               (.plus (.num 0)
                                      (.plus (.num 0) (.num 1))))
      = .plus (.num 2) (.num 1) := by rfl

theorem optimize0plus_sound (a : Aexp) :
    a.optimize0plus.eval = a.eval := by
  induction a with
  | num n => rfl
  | plus a₁ a₂ ih₁ ih₂ =>
    cases a₁ with
    | num n =>
      cases n with
      | zero =>
        simp only [optimize0plus, eval_plus, eval_num, Nat.zero_add]
        exact ih₂
      | succ n =>
        simp only [optimize0plus, eval_plus, eval_num]
        rw [ih₂]
    | plus b₁ b₂ =>
      simp only [optimize0plus, eval_plus] at ih₁ ⊢
      rw [ih₁, ih₂]
    | minus b₁ b₂ =>
      simp only [optimize0plus, eval_plus] at ih₁ ⊢
      rw [ih₁, ih₂]
    | mult b₁ b₂ =>
      simp only [optimize0plus, eval_plus] at ih₁ ⊢
      rw [ih₁, ih₂]
  | minus a₁ a₂ ih₁ ih₂ =>
    simp only [optimize0plus, eval_minus]
    rw [ih₁, ih₂]
  | mult a₁ a₂ ih₁ ih₂ =>
    simp only [optimize0plus, eval_mult]
    rw [ih₁, ih₂]

--  We can use `fun_induction` to achieve a much shorter
--  proof.

theorem optimize0plus_sound' (a : Aexp) :
    a.optimize0plus.eval = a.eval := by
  fun_induction Aexp.optimize0plus a <;> simp_all

end Aexp

--  ### Exercise (3 stars): optimize0plus_sound ⭐⭐⭐

--  Since the `Aexp.optimize0plus` transformation doesn't
--  change the value of an `Aexp`, we should be able to
--  apply it to all the `Aexp`s that appear in a `Bexp`
--  without changing the `Bexp`'s value. Write a function
--  that performs this transformation on `Bexp`s and prove
--  it sound. Use the combinators we've just seen to make
--  the proof as short and elegant as possible.

def Bexp.optimize0plus (b : Bexp) : Bexp := sorry

theorem Bexp.optimize0plus_test1 :
    Bexp.optimize0plus
        (.not (.gt (.plus (.num 0) (.num 4)) (.num 8)))
      = (.not (.gt (.num 4) (.num 8))) := sorry

theorem Bexp.optimize0plus_test2 :
    Bexp.optimize0plus
        (.and (.le (.plus (.num 0) (.num 4)) (.num 5)) (.bool true))
      = (.and (.le (.num 4) (.num 5)) (.bool true)) := sorry

theorem Bexp.optimize0plus_sound (b : Bexp) :
    b.optimize0plus.eval = b.eval := by
  sorry

--  ### Exercise (4 stars): optimize (Optional) ⭐⭐⭐⭐

--  The optimization implemented by our `Aexp.optimize0plus`
--  is only one of many possible optimizations on arithmetic
--  and boolean expressions. Write a more sophisticated
--  optimizer and prove it correct. (You will probably find
--  it easiest to start small -- add just a single, simple
--  optimization and its correctness proof -- and build up
--  incrementally to something more interesting.)

--  ## Evaluation as a Relation

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.plus a₁ a₂) (n₁ + n₂)
  | minus {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.minus a₁ a₂) (n₁ - n₂)
  | mult {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.mult a₁ a₂) (n₁ * n₂)

--  One comment on the style of this definition. We could
--  instead have presented this relation with **positional**
--  hypotheses -- no names for the premises.

namespace ArithUnnamed

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus {a₁ a₂ : Aexp} {n₁ n₂ : Nat} : EvalR a₁ n₁ → EvalR a₂ n₂ → EvalR (.plus a₁ a₂) (n₁ + n₂)
  | minus {a₁ a₂ : Aexp} {n₁ n₂ : Nat} : EvalR a₁ n₁ → EvalR a₂ n₂ → EvalR (.minus a₁ a₂) (n₁ - n₂)
  | mult {a₁ a₂ : Aexp} {n₁ n₂ : Nat} : EvalR a₁ n₁ → EvalR a₂ n₂ → EvalR (.mult a₁ a₂) (n₁ * n₂)

end ArithUnnamed

--  It will be convenient to have an infix notation for
--  `Aexp.EvalR`. We'll write `e ⇓ n` to mean that
--  arithmetic expression `e` evaluates to value `n`. The
--  `⇓` symbol is typed `\Downarrow`.

namespace Aexp
scoped notation:55 e:56 " ⇓ " n:56 => EvalR e n

--  ### Inference Rule Notation

--   ----------------------------------------

--  _Quiz:_

--  Which rules are needed to prove the following?

--  .mult (.plus (.num 3) (.num 1)) (.num 0) ⇓ 0

--  (A) `num` and `plus` (B) `num` only (C) `num` and `mult`
--  (D) `mult` and `plus` (E) `num`, `mult`, and `plus`

--   ----------------------------------------

--  ### Exercise (1 star): beval_rules (Optional, Manually graded) ⭐

--  Here, again, is the definition of the `Bexp.eval`
--  function:
--
--      def Bexp.eval (b : Bexp) : Bool :=
--        match b with
--        | bool b     => b
--        | eq   a₁ a₂ => a₁.eval == a₂.eval
--        | neq  a₁ a₂ => a₁.eval != a₂.eval
--        | le   a₁ a₂ => a₁.eval ≤ a₂.eval
--        | gt   a₁ a₂ => a₁.eval > a₂.eval
--        | not  b₁    => !eval b₁
--        | and  b₁ b₂ => eval b₁ && eval b₂
--
--  Write out a corresponding definition of boolean
--  evaluation as a relation in inference rule notation.

--  ### Equivalence of the Definitions

--  It is straightforward to prove that the relational and
--  functional definitions of evaluation agree.

theorem evalR_iff_eval (a : Aexp) (n : Nat) :
    a ⇓ n ↔ a.eval = n := by
  constructor
  · intro h
    induction h with
    | num n => rfl
    | plus h₁ h₂ ih₁ ih₂ => simp only [eval_plus]; rw [ih₁, ih₂]
    | minus h₁ h₂ ih₁ ih₂ => simp only [eval_minus]; rw [ih₁, ih₂]
    | mult h₁ h₂ ih₁ ih₂ => simp only [eval_mult]; rw [ih₁, ih₂]
  · intro h
    subst h
    induction a with
    | num n => exact .num n
    | plus a₁ a₂ ih₁ ih₂ => exact .plus ih₁ ih₂
    | minus a₁ a₂ ih₁ ih₂ => exact .minus ih₁ ih₂
    | mult a₁ a₂ ih₁ ih₂ => exact .mult ih₁ ih₂

--  We can make the proof quite a bit shorter using more
--  automation like we did in the previous section.

theorem evalR_iff_eval' (a : Aexp) (n : Nat) :
    a ⇓ n ↔ a.eval = n := by
  sorry

end Aexp

--  ### Exercise (3 stars): bevalR ⭐⭐⭐

--  Write a relation `Bexp.EvalR` in the same style as
--  `Aexp.EvalR`, and prove that it is equivalent to
--  `Bexp.eval`.

namespace Bexp
open scoped Aexp -- opens the ⇓ notation for Aexp.EvalR

inductive EvalR : Bexp → Bool → Prop where
  --  FILL IN HERE

scoped notation:55 e:56 " ⇓ " b:56 => EvalR e b

theorem evalR_iff_eval (b : Bexp) (bv : Bool) :
    b ⇓ bv ↔ b.eval = bv := by
  sorry

end Bexp
end Slang

--  ### Computational vs. Relational Definitions

--  Sometimes relational definitions are the only reasonable
--  option...

namespace Slang.AevalRDivision

--  For example, suppose that we wanted to extend the
--  arithmetic operations with division:

inductive Aexp where
  | num (n : Nat)
  | plus (a₁ a₂ : Aexp)
  | minus (a₁ a₂ : Aexp)
  | mult (a₁ a₂ : Aexp)
  | div (a₁ a₂ : Aexp)             -- NEW

--  Extending the definition of `Aexp.eval` to handle this
--  new operation would not be straightforward due to
--  division being a *partial* operation; i.e., what should
--  we return as the result of `.div (.num 5) (.num 0)`? One
--  option would be to lift the definition of `Aexp.eval` to
--  return an option:

namespace Aexp

def eval (a : Aexp) : Option Nat :=
  match a with
  | num   n     =>  some n
  | plus  a₁ a₂ =>  match a₁.eval, a₂.eval with
                    | some n₁, some n₂ => some (n₁ + n₂)
                    | _, _ => none
  | minus a₁ a₂ =>  match a₁.eval, a₂.eval with
                    | some n₁, some n₂ => some (n₁ - n₂)
                    | _, _ => none
  | mult  a₁ a₂ =>  match a₁.eval, a₂.eval with
                    | some n₁, some n₂ => some (n₁ * n₂)
                    | _, _ => none
  | div   a₁ a₂ =>  match a₁.eval, a₂.eval with
                    | _, some 0 => none
                    | some n₁, some n₂ => if n₂ ∣ n₁ then some (n₁ / n₂) else none
                    | _, _ => none
end Aexp

--  This definition is a lot wordier than the earlier
--  version. There are tools to reduce this overhead, namely
--  monads, but we will not discuss these in Software
--  Foundations in Lean. Curious readers can learn more
--  about them from [Functional Programming in
--  Lean](https://lean-lang.org/functional_programming_in_lean/Monads/).
--
--  By contrast, partiality is no problem for the relational
--  version of the definition.

--  What should `Aexp.eval` return for
--  `.div (.num 1) (.num 0)`??

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.plus a₁ a₂) (n₁ + n₂)
  | minus (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.minus a₁ a₂) (n₁ - n₂)
  | mult (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.mult a₁ a₂) (n₁ * n₂)
  | div (a₁ a₂ : Aexp) (n₁ n₂ n₃ : Nat)             -- NEW
      (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) (hpos : n₂ > 0) (hdiv : n₂ * n₃ = n₁) :
      EvalR (.div a₁ a₂) n₃

--  Notice that there are some inputs (those with a divisor
--  of 0) for which this relation does not specify an
--  output.

end Slang.AevalRDivision

namespace Slang.AevalRExtended

--  Another example: a *nondeterministic* number generator:

--  As another example, suppose that we want to extend the
--  arithmetic operations by a nondeterministic number
--  generator `any` that, when evaluated, may yield any
--  number. (This is not the same as making a
--  *probabilistic* choice among all numbers -- we only say
--  which results are *possible*.)

inductive Aexp where
  | any                            -- NEW
  | num (n : Nat)
  | plus (a₁ a₂ : Aexp)
  | minus (a₁ a₂ : Aexp)
  | mult (a₁ a₂ : Aexp)

--  Again, extending `Aexp.eval` would be tricky, since
--  evaluation is now *not* a deterministic function from
--  expressions to numbers; but extending the relation is no
--  problem.

--  What should `Aexp.eval` do with nondeterminism??

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | any (n : Nat) : EvalR .any n                   -- NEW
  | num (n : Nat) : EvalR (.num n) n
  | plus (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.plus a₁ a₂) (n₁ + n₂)
  | minus (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.minus a₁ a₂) (n₁ - n₂)
  | mult (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.mult a₁ a₂) (n₁ * n₂)

end Slang.AevalRExtended

--  Functional: computation. Relational: expressive. Best:
--  both, proved equivalent.

-- Built on 2026-09-02 17:11 UTC

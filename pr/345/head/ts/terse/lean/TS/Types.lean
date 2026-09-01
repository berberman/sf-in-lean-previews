import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer
import TS.Smallstep

import SFLCompat

--  # Types: Type Systems

--  New topic: *type systems*
--
--  - This chapter: a toy type system for a toy language
--
--    - typing relation
--    - *progress* and *preservation* theorems
--
--  - Next chapter: *simply typed lambda-calculus*

--  ## Typed Arithmetic Expressions

--  - A simple toy language where expressions may fail with
--    dynamic type errors
--
--    - numbers (and arithmetic)
--    - booleans (and conditionals)
--
--  - This means we can write *stuck* terms like `5 + true`
--    and `if 42 then 0 else 1`.

--  ### Syntax

--  Here is the syntax of program terms, informally:

--  t ::= true
--      | false
--      | if t then t else t
--      | 0
--      | succ t
--      | pred t
--      | iszero t

--  And here it is formally:

namespace TM

inductive Tm where
  | tru
  | fls
  | ite (c t e : Tm)
  | zero
  | succ (t : Tm)
  | pred (t : Tm)
  | isZero (t : Tm)

--  #### Notation

declare_syntax_cat tm
-- The keyword atoms (`true`/`false`/`succ`/`pred`/`iszero`) are parsed as bare
-- identifiers and dispatched in the macro below, rather than declared as
-- reserved symbols.  Reserving them would break ordinary Lean uses of
-- `true`/`false` and clash with the constructor/case names `succ`, `pred`.
syntax:max num : tm
syntax:max ident : tm
syntax:75 ident ppHardSpace tm:76 : tm
syntax:max "(" tm ")" : tm
syntax:max "~" term:max : tm
syntax:50 "if " tm:51 " then " tm:51 " else " tm:51 : tm
syntax:max "<{ " tm " }>" : term

open Lean in
macro_rules
  | `(<{ $n:num }>) =>
      if n.getNat == 0 then `(Tm.zero)
      else Macro.throwErrorAt n "the only numeric literal in this language is 0"
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "true"  => `(Tm.tru)
      | "false" => `(Tm.fls)
      | _ => `($x)   -- a bare identifier is a spliced Lean term (usually a variable)
  | `(<{ $f:ident $e:tm }>) =>
      match f.getId.toString with
      | "succ"   => `(Tm.succ <{ $e }>)
      | "pred"   => `(Tm.pred <{ $e }>)
      | "iszero" => `(Tm.isZero <{ $e }>)
      | _ => Macro.throwErrorAt f s!"unknown operator `{f.getId}`"
  | `(<{ ($e) }>) => `(<{ $e }>)
  | `(<{ ~$e }>)  => pure e
  | `(<{ if $c then $t else $e }>) => `(Tm.ite <{ $c }> <{ $t }> <{ $e }>)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing terms back)
open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
/-- Re-inserts parentheses in `tm` output according to the grammar's precedences. -/
@[category_parenthesizer tm]
def tm.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `tm true wrapParens prec <|
    parenthesizeCategoryCore `tm prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(tm| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `tm` concrete syntax from a `Tm` term. -/
partial def delabTmInner : DelabM (TSyntax `tm) := do
  let stx ←
    match_expr ← getExpr with
    | Tm.tru => `(tm| $(mkIdent `true):ident)
    | Tm.fls => `(tm| $(mkIdent `false):ident)
    | Tm.zero => `(tm| 0)
    | Tm.succ _ => do `(tm| $(mkIdent `succ):ident $(← withAppArg delabTmInner))
    | Tm.pred _ => do `(tm| $(mkIdent `pred):ident $(← withAppArg delabTmInner))
    | Tm.isZero _ => do `(tm| $(mkIdent `iszero):ident $(← withAppArg delabTmInner))
    | Tm.ite _ _ _ => do
        let c ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let t ← withAppFn <| withAppArg delabTmInner
        let e ← withAppArg delabTmInner
        `(tm| if $c then $t else $e)
    | _ => do
        -- A bare variable prints without the `~` escape; anything else keeps it.
        match ← delab with
        | `($i:ident) => `(tm| $i:ident)
        | e => `(tm| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
-- The keys are the constants' full names: `Tm` lives in namespace `TM`, and the
-- `delab` attribute does not resolve its argument against the current namespace.
@[delab app.TM.Tm.tru, delab app.TM.Tm.fls, delab app.TM.Tm.zero, delab app.TM.Tm.succ,
  delab app.TM.Tm.pred, delab app.TM.Tm.isZero, delab app.TM.Tm.ite]
partial def delabTm : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Tm.tru => true | Tm.fls => true | Tm.zero => true
    | Tm.succ _ => true | Tm.pred _ => true | Tm.isZero _ => true
    | Tm.ite _ _ _ => true | _ => false
  match ← delabTmInner with
  | `(tm| ~$e) => pure e
  | e => `(<{ $e }>)
--  END DETAILS

--  #### Values

--  *Values* are `true`, `false`, and numeric values (`0`,
--  and `succ` of a numeric value).

inductive Tm.IsBValue : Tm → Prop where
  | tru : Tm.IsBValue <{ true }>
  | fls : Tm.IsBValue <{ false }>

inductive Tm.IsNValue : Tm → Prop where
  | zero : Tm.IsNValue <{ 0 }>
  | succ (t : Tm) (h : Tm.IsNValue t) : Tm.IsNValue <{ succ t }>

def Tm.IsValue (t : Tm) : Prop := Tm.IsBValue t ∨ Tm.IsNValue t

--  ### Operational Semantics

--  -----------------------------                 (ifTrue)
--                     if true then t₁ else t₂ ⟶ t₁
--
--                     ------------------------------                (ifFalse)
--                     if false then t₁ else t₂ ⟶ t₂
--
--                                t₁ ⟶ t₁'
--              -----------------------------------------------      (ifStep)
--              if t₁ then t₂ else t₃ ⟶ if t₁' then t₂ else t₃
--
--                                t₁ ⟶ t₁'
--                           -------------------                     (succStep)
--                           succ t₁ ⟶ succ t₁'
--
--                             -----------                           (predZero)
--                             pred 0 ⟶ 0
--
--                              IsNValue v
--                          ------------------                       (predSucc)
--                          pred (succ v) ⟶ v
--
--                                t₁ ⟶ t₁'
--                           -------------------                     (predStep)
--                           pred t₁ ⟶ pred t₁'
--
--                            ----------------                       (isZeroZero)
--                            iszero 0 ⟶ true
--
--                               IsNValue v
--                        ------------------------                   (isZeroSucc)
--                        iszero (succ v) ⟶ false
--
--                                t₁ ⟶ t₁'
--                         -----------------------                   (isZeroStep)
--                         iszero t₁ ⟶ iszero t₁'

section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Tm.Step t t'
inductive Tm.Step : Tm → Tm → Prop where
  | ifTrue (t₁ t₂ : Tm) : <{ if true then t₁ else t₂ }> ⟶ t₁
  | ifFalse (t₁ t₂ : Tm) : <{ if false then t₁ else t₂ }> ⟶ t₂
  | ifStep (c c' t₂ t₃ : Tm) (h : c ⟶ c') :
      <{ if c then t₂ else t₃ }> ⟶ <{ if c' then t₂ else t₃ }>
  | succStep (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') : <{ succ t₁ }> ⟶ <{ succ t₁' }>
  | predZero : <{ pred 0 }> ⟶ <{ 0 }>
  | predSucc (v : Tm) (hv : Tm.IsNValue v) : <{ pred (succ v) }> ⟶ v
  | predStep (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') : <{ pred t₁ }> ⟶ <{ pred t₁' }>
  | isZeroZero : <{ iszero 0 }> ⟶ <{ true }>
  | isZeroSucc (v : Tm) (hv : Tm.IsNValue v) : <{ iszero (succ v) }> ⟶ <{ false }>
  | isZeroStep (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') : <{ iszero t₁ }> ⟶ <{ iszero t₁' }>
end

scoped notation:40 t:41 " ⟶ " t':41 => Tm.Step t t'

--  ### Normal Forms and Values

--  The first interesting thing to notice about this
--  `Tm.Step` relation is that the strong progress theorem
--  from the Smallstep chapter fails here. That is, there
--  are terms that are normal forms (they can't take a step)
--  but not values (they are not included in our definition
--  of possible "results of reduction").
--
--  Such terms are *stuck*.

def Tm.IsNormalForm (t : Tm) : Prop := _root_.IsNormalForm Tm.Step t

def Tm.IsStuck (t : Tm) : Prop := Tm.IsNormalForm t ∧ ¬ Tm.IsValue t

--  ### Exercise (2 stars): some_term_is_stuck ⭐⭐

theorem some_term_is_stuck : ∃ t, Tm.IsStuck t := by
  sorry

--  However, although values and normal forms are *not* the
--  same in this language, the set of values is a subset of
--  the set of normal forms.
--
--  This is important because it shows we did not
--  accidentally define things so that some value could
--  still take a step.

theorem nvalue_is_nf (t : Tm) (h : Tm.IsNValue t) : Tm.IsNormalForm t := by
  induction h with
  | zero => intro hc; obtain ⟨t', hstp⟩ := hc; cases hstp
  | succ t₀ hn₀ ih =>
      intro hc; obtain ⟨t', hstp⟩ := hc
      cases hstp with
      | succStep _ t₁' h => exact ih ⟨t₁', h⟩

--  ### Exercise (3 stars): value_is_nf ⭐⭐⭐

--  (Hint: You will reach a point in this proof where you
--  need to use an induction to reason about a term that is
--  known to be a numeric value. This induction can be
--  performed either over the term itself or over the
--  evidence that it is a numeric value. The proof goes
--  through in either case, but you will find that one way
--  is quite a bit shorter than the other. For the sake of
--  the exercise, try to complete the proof both ways.)

theorem value_is_nf (t : Tm) (h : Tm.IsValue t) : Tm.IsNormalForm t := by
  sorry

--  The "other way" mentioned in the hint proves the same
--  fact by induction on the term itself rather than on the
--  evidence that it is a numeric value. It goes through,
--  but is a bit longer than the `nvalue_is_nf` route above.

theorem value_is_nf' (t : Tm) (h : Tm.IsValue t) : Tm.IsNormalForm t := by
  sorry

--  ### Exercise (3 stars): step_deterministic (Optional) ⭐⭐⭐

--  Use `value_is_nf` (here, `nvalue_is_nf`) to show that
--  the `Tm.Step` relation is also deterministic.

theorem step_deterministic : Deterministic Tm.Step := by
  sorry

--   ----------------------------------------

--  _Quiz:_

--  Is the following term stuck?

--  iszero (if true then (succ 0) else 0)

--  (A) Yes (B) No

--   ----------------------------------------

--  _Quiz:_

--  What about this one? Is it stuck?

--  if (succ 0) then true else false

--  (A) Yes (B) No

--   ----------------------------------------

--  _Quiz:_

--  What about this one? Is it stuck?

--  succ (succ 0)

--  (A) Yes (B) No

--   ----------------------------------------

--  _Quiz:_

--  What about this one? Is it stuck?

--  succ (if true then true else true)

--  (A) Yes (B) No
--
--  (Hint: Notice that the `Tm.Step` relation doesn't care
--  about whether the expression being stepped makes global
--  sense — it just checks that the operation in the *next*
--  reduction step is being applied to the right kinds of
--  operands.)

--   ----------------------------------------

--  Suppose we define an alternate single-step relation,
--  written `t ⇢ t'`, that *drops* the `Tm.IsNValue` premise
--  from the `predSucc` and `isZeroSucc` rules — so
--  `pred (succ t)` and `iszero (succ t)` may step even when
--  `t` is not a numeric value. (It is built with exactly
--  the same notation setup as `Tm.Step`; note
--  `predSucc`/`isZeroSucc` no longer take a premise.)

section
set_option hygiene false in
local notation:40 t:41 " ⇢ " t':41 => Tm.AltStep t t'
inductive Tm.AltStep : Tm → Tm → Prop where
  | ifTrue (t₁ t₂ : Tm) : <{ if true then t₁ else t₂ }> ⇢ t₁
  | ifFalse (t₁ t₂ : Tm) : <{ if false then t₁ else t₂ }> ⇢ t₂
  | ifStep (t₁ t₁' t₂ t₃ : Tm) : t₁ ⇢ t₁' →
      <{ if t₁ then t₂ else t₃ }> ⇢ <{ if t₁' then t₂ else t₃ }>
  | succStep (t₁ t₁' : Tm) : t₁ ⇢ t₁' → <{ succ t₁ }> ⇢ <{ succ t₁' }>
  | predZero : <{ pred 0 }> ⇢ <{ 0 }>
  | predSucc (t₁ : Tm) : <{ pred (succ t₁) }> ⇢ t₁
  | predStep (t₁ t₁' : Tm) : t₁ ⇢ t₁' → <{ pred t₁ }> ⇢ <{ pred t₁' }>
  | isZeroZero : <{ iszero 0 }> ⇢ <{ true }>
  | isZeroSucc (t₁ : Tm) : <{ iszero (succ t₁) }> ⇢ <{ false }>
  | isZeroStep (t₁ t₁' : Tm) : t₁ ⇢ t₁' → <{ iszero t₁ }> ⇢ <{ iszero t₁' }>
end

scoped notation:40 t:41 " ⇢ " t':41 => Tm.AltStep t t'

--  Some questions about this relation (answers inline):
--
--  - Is `⇢` deterministic
--    (`∀ t t' t'', t ⇢ t' → t ⇢ t'' → t' = t''`)? No:
--    `pred (succ (pred 0))` steps to both `pred 0` (by
--    `predSucc`) and `pred (succ 0)` (by `predStep`, since
--    `pred 0 ⇢ 0`).
--
--  - Is every `Tm.Step` normal form also a `⇢` normal form?
--    No: `pred (succ true)` is stuck for `Tm.Step` but
--    steps under `⇢` (to `true`, by `predSucc`, now that
--    the `Tm.IsNValue` premise is gone).
--
--  - Is every `⇢` normal form also a `Tm.Step` normal form?
--    Yes — `Tm.Step` is a subrelation of `⇢`, so anything
--    stuck for `⇢` is stuck for `Tm.Step`.
--
--  - Is every value reachable by `Tm.Step` (in many steps)
--    also reachable by `⇢` (in many steps)? Yes, for the
--    same subrelation reason.
--
--  - Conversely? No: `iszero (succ true)` reaches the value
--    `false` under `⇢` but is stuck under `Tm.Step`.
--
--  A *functional* version computes a single `⇢` step of a
--  term, returning `none` when the term is a `⇢` normal
--  form. This is a nice chance to see a step *function*,
--  which the chapter otherwise gives only as a relation:

def alt_simplify_step (t : Tm) : Option Tm :=
  match t with
  | <{ if t₁ then t₂ else t₃ }> =>
      match alt_simplify_step t₁ with
      | some t₁' => some <{ if t₁' then t₂ else t₃ }>
      | none =>
        match t₁ with
        | <{ true }>  => some t₂
        | <{ false }> => some t₃
        | _           => none
  | <{ succ t₁ }> =>
      match alt_simplify_step t₁ with
      | some t₁' => some <{ succ t₁' }>
      | none     => none
  | <{ pred t₁ }> =>
      match alt_simplify_step t₁ with
      | some t₁' => some <{ pred t₁' }>
      | none =>
        match t₁ with
        | <{ 0 }>       => some <{ 0 }>
        | <{ succ t₂ }> => some t₂
        | _             => none
  | <{ iszero t₁ }> =>
      match alt_simplify_step t₁ with
      | some t₁' => some <{ iszero t₁' }>
      | none =>
        match t₁ with
        | <{ 0 }>       => some <{ true }>
        | <{ succ t₂ }> => some <{ false }>
        | _             => none
  | _ => none

-- `pred (succ true)` steps under `⇢` (the dropped `IsNValue` premise) even
-- though it is stuck under `Tm.Step`:
example : alt_simplify_step <{ pred (succ true) }> = some <{ true }> := rfl
example : alt_simplify_step <{ if true then 0 else succ 0 }> = some <{ 0 }> := rfl
example : alt_simplify_step <{ 0 }> = none := rfl

--  ### Typing

--  *Types* describe the possible shapes of values.

--  Here are the formal rules.

inductive Ty where
  | bool
  | nat

syntax:max "<{ " "⊢ " tm " ⦂ " ident " }>" : term
syntax:max "<{ " "⊢ " tm " ⦂ " "~" term:max " }>" : term

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: typing relation)
--  The notation is defined inside a `section` with
--  `set_option hygiene false` so the bare name `Tm.HasType`
--  in the expansion resolves to the relation being defined;
--  after the `section` we re-declare the same rules
--  hygienically for real use. Unlike `⟶`, the judgment
--  builds on the custom `tm` syntactic category, so it must
--  use `syntax`/`macro_rules` rather than `notation` —
--  which is why it still needs the `app_unexpander` to
--  print the judgment back.

section
set_option hygiene false in
local macro_rules
  | `(<{ ⊢ $t ⦂ $T:ident }>) =>
      match T.getId.toString with
      | "Bool" => `(Tm.HasType <{ $t }> Ty.bool)
      | "Nat"  => `(Tm.HasType <{ $t }> Ty.nat)
      | _      => `(Tm.HasType <{ $t }> $T)
  | `(<{ ⊢ $t ⦂ ~$T }>) => `(Tm.HasType <{ $t }> $T)
--  END DETAILS

-- The actual definition, written in the notation above.
inductive Tm.HasType : Tm → Ty → Prop where
  | tru : <{ ⊢ true ⦂ Bool }>
  | fls : <{ ⊢ false ⦂ Bool }>
  | ite (t₁ t₂ t₃ : Tm) (τ : Ty)
      (h₁ : <{ ⊢ t₁ ⦂ Bool }>) (h₂ : <{ ⊢ t₂ ⦂ τ }>) (h₃ : <{ ⊢ t₃ ⦂ τ }>) :
      <{ ⊢ if t₁ then t₂ else t₃ ⦂ τ }>
  | zero : <{ ⊢ 0 ⦂ Nat }>
  | succ (t₁ : Tm) (h : <{ ⊢ t₁ ⦂ Nat }>) : <{ ⊢ succ t₁ ⦂ Nat }>
  | pred (t₁ : Tm) (h : <{ ⊢ t₁ ⦂ Nat }>) : <{ ⊢ pred t₁ ⦂ Nat }>
  | isZero (t₁ : Tm) (h : <{ ⊢ t₁ ⦂ Nat }>) : <{ ⊢ iszero t₁ ⦂ Bool }>
end

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: typing relation)
-- The same rules repeated with hygiene enabled, for use after the section.
macro_rules
  | `(<{ ⊢ $t ⦂ $T:ident }>) =>
      match T.getId.toString with
      | "Bool" => `(Tm.HasType <{ $t }> Ty.bool)
      | "Nat"  => `(Tm.HasType <{ $t }> Ty.nat)
      | _      => `(Tm.HasType <{ $t }> $T)
  | `(<{ ⊢ $t ⦂ ~$T }>) => `(Tm.HasType <{ $t }> $T)

-- Print `Tm.HasType`/`Ty` values back as `<{ ⊢ … ⦂ … }>` notation: `delabTy`
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.TM.Ty.bool, delab app.TM.Ty.nat]
def delabTy : Delab := whenPPOption getPPNotation do
  match_expr ← getExpr with
  | Ty.bool => `($(mkIdent `Bool):ident)
  | Ty.nat  => `($(mkIdent `Nat):ident)
  | _ => failure

@[app_unexpander Tm.HasType]
def Tm.HasType.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ <{ $t }> $T:ident) => `(<{ ⊢ $t ⦂ $T }>)
  | `($_ $t:ident $T:ident)  => `(<{ ⊢ $(⟨t.raw⟩) ⦂ $T }>)
  | `($_ $t $T)              => `(<{ ⊢ ~$t ⦂ ~$T }>)
  | _ => throw ()
--  END DETAILS

example : <{ ⊢ if false then 0 else succ 0 ⦂ Nat }> :=
  .ite _ _ _ _ .fls .zero (.succ _ .zero)

--  Typing is a *conservative* (or *static*) approximation
--  to behavior.
--
--  In particular, a term can be ill typed even though it
--  steps to something well typed.

example : ¬ <{ ⊢ if false then 0 else true ⦂ Bool }> := by
  intro hc; cases hc with | ite _ _ _ _ h₁ h₂ h₃ => cases h₂

example :
    ¬ <{ ⊢ if iszero (succ 0) then succ false else true ⦂ Bool }> := by
  intro hc; cases hc with | ite _ _ _ _ h₁ h₂ h₃ => cases h₂

--  ### Exercise (1 star): succ_hastype_nat__hastype_nat (Optional) ⭐

example (t : Tm) (h : <{ ⊢ succ t ⦂ Nat }>) : <{ ⊢ t ⦂ Nat }> := by
  sorry

--  ### Canonical forms

--  The following two lemmas capture the fundamental fact
--  that the definitions of boolean and numeric values agree
--  with the typing relation: a well-typed value of type
--  `Bool` is a boolean value, and of type `Nat` a numeric
--  value.

theorem bool_canonical (t : Tm) (hT : <{ ⊢ t ⦂ Bool }>) (hv : Tm.IsValue t) : Tm.IsBValue t := by
  cases hv with
  | inl hb => exact hb
  | inr hn => cases hn with
    | zero => cases hT
    | succ t₀ h => cases hT

theorem nat_canonical (t : Tm) (hT : <{ ⊢ t ⦂ Nat }>) (hv : Tm.IsValue t) : Tm.IsNValue t := by
  cases hv with
  | inl hb => cases hb <;> cases hT
  | inr hn => exact hn

--  ### Progress

--  The typing relation enjoys two critical properties.
--
--  The first is that well-typed normal forms are not stuck
--  — or conversely, if a term is well typed, then either it
--  is a value or it can take at least one step. We call
--  this *progress*.

--  ### Exercise (3 stars): finish_progress ⭐⭐⭐

--  Complete the formal proof of the `progress` property.
--  (Make sure you understand the parts we've given of the
--  informal proof in the following exercise before starting
--  — this will save you a lot of time.)

theorem progress (t : Tm) (τ : Ty) (hT : <{ ⊢ t ⦂ T }>) : Tm.IsValue t ∨ ∃ t', t ⟶ t' := by
  sorry

--   ----------------------------------------

--  _Quiz:_

--  What is the relation between the *progress* property
--  defined here and the *strong progress* from the
--  Smallstep chapter?
--
--  (A) No difference — they mean the same thing
--
--  (B) Progress implies strong progress
--
--  (C) Strong progress implies progress
--
--  (D) No relationship
--
--  (E) Dunno

--   ----------------------------------------

--  ### Exercise (3 stars): finish_progress_informal (Optional) ⭐⭐⭐

--  Complete the corresponding informal proof.

--  *Theorem*: If `⊢ t ⦂ T`, then either `t` is a value or
--  else `t ⟶ t'` for some `t'`.
--
--  *Proof*: By induction on a derivation of `⊢ t ⦂ T`.
--
--  - If the last rule in the derivation is `ite`, then
--    `t = if t₁ then t₂
--        else t₃`, with `⊢ t₁ ⦂ Bool`,
--    `⊢ t₂ ⦂ T` and `⊢ t₃ ⦂ T`. By the IH, either `t₁` is a
--    value or else `t₁` can step to some `t₁'`.
--
--    - If `t₁` is a value, then by the canonical forms
--      lemmas and the fact that `⊢ t₁ ⦂ Bool` we have that
--      `t₁` is a boolean value (`Tm.IsBValue`) — i.e., it
--      is either `true` or `false`. If `t₁ = true`, then
--      `t` steps to `t₂` by `ifTrue`, while if
--      `t₁ = false`, then `t` steps to `t₃` by `ifFalse`.
--      Either way, `t` can step, which is what we wanted to
--      show.
--
--    - If `t₁` itself can take a step, then, by `ifStep`,
--      so can `t`.

--   ----------------------------------------

--  _Quiz:_

--  Quick review: in the language defined at the start of
--  this chapter...
--
--  - Every well-typed normal form is a value.
--
--  (A) True (B) False

--   ----------------------------------------

--  _Quiz:_

--  In this language...
--
--  - Every value is a normal form.
--
--  (A) True (B) False

--   ----------------------------------------

--  _Quiz:_

--  In this language...
--
--  - The single-step reduction relation is a partial
--    function (i.e., it is deterministic).
--
--  (A) True (B) False

--   ----------------------------------------

--  _Quiz:_

--  In this language...
--
--  - The single-step reduction relation is a *total*
--    function.
--
--  (A) True (B) False

--   ----------------------------------------

--  ### Type Preservation

--  The second critical property of typing is that, when a
--  well-typed term takes a step, the result is a well-typed
--  term (of the same type).

--  ### Exercise (2 stars): finish_preservation ⭐⭐

--  Complete the formal proof of the `preservation`
--  property. (Again, make sure you understand the informal
--  proof fragment in the following exercise first.)

theorem preservation (t t' : Tm) (τ : Ty) (hT : <{ ⊢ t ⦂ T }>) (he : t ⟶ t') : <{ ⊢ t' ⦂ T }> := by
  sorry

--  ### Exercise (3 stars): finish_preservation_informal (Optional) ⭐⭐⭐

--  Complete the following informal proof.
--
--  *Theorem*: If `⊢ t ⦂ T` and `t ⟶ t'`, then `⊢ t' ⦂ T`.
--
--  *Proof*: By induction on a derivation of `⊢ t ⦂ T`.
--
--  - If the last rule in the derivation is `ite`, then
--    `t = if t₁ then t₂
--        else t₃`, with `⊢ t₁ ⦂ Bool`,
--    `⊢ t₂ ⦂ T` and `⊢ t₃ ⦂ T`.
--
--    Inspecting the rules for the small-step reduction
--    relation and remembering that `t` has the form
--    `if ...`, we see that the only ones that could have
--    been used to prove `t ⟶ t'` are `ifTrue`, `ifFalse`,
--    or `ifStep`.
--
--    - If the last rule was `ifTrue`, then `t' = t₂`. But
--      we know that `⊢ t₂ ⦂ T`, so we are done.
--
--    - If the last rule was `ifFalse`, then `t' = t₃`. But
--      we know that `⊢ t₃ ⦂ T`, so we are done.
--
--    - If the last rule was `ifStep`, then
--      `t' = if t₁' then t₂ else t₃`, where `t₁ ⟶ t₁'`. We
--      know `⊢ t₁ ⦂ Bool` so, by the IH,
--      `⊢ t₁' ⦂
--            Bool`. The `ite` rule then gives us
--      `⊢ if t₁' then t₂ else t₃ ⦂ T`, as required.

--  ### Exercise (3 stars): preservation_alternate_proof ⭐⭐⭐

--  Now prove the same property again by induction on the
--  *evaluation* derivation instead of on the typing
--  derivation. Begin by carefully reading and thinking
--  about the first few lines of the above proofs to make
--  sure you understand what each one is doing. The set-up
--  for this proof is similar, but not exactly the same.

theorem preservation' (t t' : Tm) (τ : Ty) (hT : <{ ⊢ t ⦂ τ }>) (he : t ⟶ t') : <{ ⊢ t' ⦂ τ }> := by
  sorry

--  ### Type Soundness

--  Putting progress and preservation together, we see that
--  a well-typed term can never reach a stuck state.

def Tm.MultiStep (t₁ t₂ : Tm) : Prop := Multi Tm.Step t₁ t₂

scoped notation:40 t₁:41 " ⟶* " t₂:41 => Tm.MultiStep t₁ t₂

theorem soundness (t t' : Tm) (τ : Ty) (hT : <{ ⊢ t ⦂ τ }>) (hm : t ⟶* t') : ¬ Tm.IsStuck t' := by
  induction hm generalizing τ with
  | refl a =>
      intro hst; obtain ⟨hnf, hnv⟩ := hst
      cases progress a τ hT with
      | inl hv => exact hnv hv
      | inr hs => exact hnf hs
  | step a b c h₁ h₂ ih => exact ih τ (preservation a b τ hT h₁)

--   ----------------------------------------

--  _Quiz:_

--  Suppose we add the following two new rules to the
--  reduction relation:

--  | predTrue  : pred true  ⟶ pred false
--  | predFalse : pred false ⟶ pred true

--  Which of the following properties remain true in the
--  presence of these rules? (Choose 1 for yes, 2 for no.)
--
--  - Determinism of `Tm.Step`
--  - Progress
--  - Preservation

--   ----------------------------------------

--  _Quiz:_

--  Suppose, instead, that we add this new rule to the
--  typing relation:

--  | ifFunny : ⊢ t₂ ⦂ Nat → ⊢ if true then t₂ else t₃ ⦂ Nat

--  Which of the following properties remain true in the
--  presence of this rule?
--
--  - Determinism of `Tm.Step`
--  - Progress
--  - Preservation

--   ----------------------------------------

--  ## Additional Exercises

--  ### Exercise (3 stars): subject_expansion ⭐⭐⭐

--  Having seen the subject reduction property, one might
--  wonder whether the opposite property — subject
--  *expansion* — also holds. That is, is it always the case
--  that, if `t ⟶ t'` and `⊢ t' ⦂ T`, then `⊢ t ⦂ T`? If so,
--  prove it. If not, give a counter-example.

theorem subject_expansion :
    (∀ (t t' : Tm) (τ : Ty), t ⟶ t' ∧ <{ ⊢ t' ⦂ τ }> → <{ ⊢ t ⦂ τ }>)
    ∨ ¬ (∀ (t t' : Tm) (τ : Ty), t ⟶ t' ∧ <{ ⊢ t' ⦂ τ }> → <{ ⊢ t ⦂ τ }>) := by
  sorry

end TM

--  The following are *thought exercises*: for each
--  modification, say which of determinism / progress /
--  preservation still hold, with a counterexample if one
--  breaks. (These are graded manually; there is no Lean
--  code to complete.)

--  ### Exercise (2 stars): variation1 (Manually graded) ⭐⭐

--  Suppose that we add this new rule to the typing
--  relation:

--  succBool : ⊢ t ⦂ Bool → ⊢ succ t ⦂ Bool

--  Which of the following properties remain true in the
--  presence of this rule? For each one, write either
--  "remains true" or else "becomes false." If a property
--  becomes false, give a counterexample.
--
--  - Determinism of `Tm.Step`
--  - Progress
--  - Preservation

--  ### Exercise (2 stars): variation2 (Manually graded) ⭐⭐

--  Suppose, instead, that we add this new rule to the
--  `Tm.Step` relation:

--  funny1 : if true then t₂ else t₃ ⟶ t₃

--  Which of the above properties become false in the
--  presence of this rule? For each one that does, give a
--  counter-example.

--  ### Exercise (2 stars): variation3 (Optional) ⭐⭐

--  Suppose instead that we add this rule:

--  funny2 : t₂ ⟶ t₂' → if t₁ then t₂ else t₃ ⟶ if t₁ then t₂' else t₃

--  Which of the above properties become false in the
--  presence of this rule? For each one that does, give a
--  counter-example.

--  ### Exercise (2 stars): variation4 (Optional) ⭐⭐

--  Suppose instead that we add this rule:

--  funny3 : pred false ⟶ pred (pred false)

--  Which of the above properties become false in the
--  presence of this rule? For each one that does, give a
--  counter-example.

--  ### Exercise (2 stars): variation5 (Optional) ⭐⭐

--  Suppose instead that we add this rule:

--  funny4 : ⊢ 0 ⦂ Bool

--  Which of the above properties become false in the
--  presence of this rule? For each one that does, give a
--  counter-example.

--  ### Exercise (2 stars): variation6 (Optional) ⭐⭐

--  Suppose instead that we add this rule:

--  funny5 : ⊢ pred 0 ⦂ Bool

--  Which of the above properties become false in the
--  presence of this rule? For each one that does, give a
--  counter-example.

--  ### Exercise (3 stars): more_variations (Optional) ⭐⭐⭐

--  Make up some exercises of your own along the same lines
--  as the ones above. Try to find ways of selectively
--  breaking properties — i.e., ways of changing the
--  definitions that break just one of the properties and
--  leave the others alone.

--  ### Exercise (1 star): remove_pred0 (Manually graded) ⭐

--  The reduction rule `predZero` is a bit
--  counter-intuitive: we might feel that it makes more
--  sense for the predecessor of `0` to be undefined, rather
--  than being defined to be `0`. Can we achieve this simply
--  by removing the rule from the definition of `Tm.Step`?
--  Would doing so create any problems elsewhere?

--  ### Exercise (4 stars): prog_pres_bigstep (Advanced, Manually graded) ⭐⭐⭐⭐

--  Suppose our evaluation relation is defined in the
--  big-step style. State appropriate analogs of the
--  progress and preservation properties. (You do not need
--  to prove them.)
--
--  Can you see any limitations of either of your
--  properties? Do they allow for nonterminating programs?
--  Why might we prefer the small-step semantics for stating
--  preservation and progress?

-- Built on 2026-09-01 12:46 UTC

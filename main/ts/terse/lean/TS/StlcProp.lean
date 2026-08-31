import TS.Stlc
import LF.CustomTactics

import SFLCompat

--  # StlcProp: Properties of STLC

--  THE SIMPLY TYPED LAMBDA CALCULUS
--
--  Syntax:

--  t ::= x                     (variable)
--      | λ x : T . t           (abstraction)
--      | t t                   (application)
--      | true                  (constant true)
--      | false                 (constant false)
--      | if t then t else t    (conditional)

--  Values:

--  v ::= λ x : T . t
--      | true
--      | false

--  Substitution:
--
--      [x:=s]x               = s
--      [x:=s]y               = y                     if x ≠ y
--      [x:=s](λx:T. t)       = λx:T. t
--      [x:=s](λy:T. t)       = λy:T. [x:=s]t         if x ≠ y
--      [x:=s](t₁ t₂)         = ([x:=s]t₁) ([x:=s]t₂)
--      [x:=s]true            = true
--      [x:=s]false           = false
--      [x:=s](if t₁ then t₂ else t₃) =
--                      if [x:=s]t₁ then [x:=s]t₂ else [x:=s]t₃
--
--  Small-step operational semantics:

--  v.IsValue
--                         -----------------------                    (appAbs)
--                          (λx:T. t) v ⟶ [x:=v]t
--
--                                t₁ ⟶ t₁'
--                            ----------------                        (app1)
--                             t₁ t₂ ⟶ t₁' t₂
--
--                               v₁.IsValue
--                                t₂ ⟶ t₂'
--                            ----------------                        (app2)
--                             v₁ t₂ ⟶ v₁ t₂'
--
--                    --------------------------------                (ifTrue)
--                     (if true then t₁ else t₂) ⟶ t₁
--
--                    ---------------------------------               (ifFalse)
--                     (if false then t₁ else t₂) ⟶ t₂
--
--                                t₁ ⟶ t₁'
--          ----------------------------------------------------      (ifStep)
--           (if t₁ then t₂ else t₃) ⟶ (if t₁' then t₂ else t₃)

--  Typing:

--  Γ x = T₁
--                              ------------                       (var)
--                               Γ ⊢ x ⦂ T₁
--
--                          x ↦ T₂ ; Γ ⊢ t₁ ⦂ T₁
--                        -------------------------                (abs)
--                         Γ ⊢ λx:T₂. t₁ ⦂ T₂ → T₁
--
--                            Γ ⊢ t₁ ⦂ T₂ → T₁
--                              Γ ⊢ t₂ ⦂ T₂
--                           ------------------                    (app)
--                             Γ ⊢ t₁ t₂ ⦂ T₁
--
--                            -----------------                    (tru)
--                             Γ ⊢ true ⦂ Bool
--
--                           ------------------                    (fls)
--                            Γ ⊢ false ⦂ Bool
--
--               Γ ⊢ t₁ ⦂ Bool    Γ ⊢ t₂ ⦂ T₁    Γ ⊢ t₃ ⦂ T₁
--              ---------------------------------------------      (ite)
--                     Γ ⊢ if t₁ then t₂ else t₃ ⦂ T₁

--  In this chapter, we develop the fundamental theory of
--  the Simply Typed Lambda Calculus — in particular, the
--  type safety theorem.
--
--  We pick up where the Stlc chapter left off, so
--  everything below lives in the same namespace as the
--  definitions it is about.

namespace Stlc

open scoped MyGetElem

--  ## Canonical Forms

--  Formally, we will need these lemmas only for terms that
--  are not only well typed but *closed* — i.e., well typed
--  in the empty context.

theorem canonical_forms_bool (t : Tm) (hT : <{ ∅ ⊢ ~t ⦂ Bool }>) (hv : t.IsValue) :
    t = <{ true }> ∨ t = <{ false }> := by
  cases hv with
  | abs x T t₁ => cases hT
  | tru => left; rfl
  | fls => right; rfl

theorem canonical_forms_fun (t : Tm) (T₁ T₂ : Ty)
    (hT : <{ ∅ ⊢ ~t ⦂ ~T₁ → ~T₂ }>) (hv : t.IsValue) :
    ∃ x u, t = <{ λ ~x : ~T₁ . ~u }> := by
  cases hv with
  | abs x T t₁ => cases hT with | abs _ _ _ _ _ _ =>
    exists x, t₁
  | tru => cases hT
  | fls => cases hT

--  ## Progress

--  The *progress* theorem tells us that closed, well-typed
--  terms are not stuck.

theorem progress (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  generalize hΓ : (∅ : Context) = Γ at hT
  induction hT with
  | var Γ x T₁ h =>
    subst hΓ
    -- Contradictory: variables cannot be typed in an empty context.
    rw [PartialMap.getElem_empty] at h
    cases h
  | abs => left; constructor
  | tru => left; constructor
  | fls => left; constructor
  | app Γ T₁ T₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    -- `t = t₁ t₂`.  Proceed by cases on whether `t₁` is a value or steps.
    right
    cases ih₁ hΓ with
    | inl hv₁ =>
      cases ih₂ hΓ with
      | inl hv₂ =>
        obtain ⟨x, u, rfl⟩ := canonical_forms_fun t₁ _ _ (hΓ ▸ h₁) hv₁
        exists <{ [~x := ~t₂] ~u }>
        constructor
        assumption
      | inr hs₂ =>
        obtain ⟨t₂', h⟩ := hs₂
        exists <{ ~t₁ ~t₂' }>
        constructor <;> assumption
    | inr hs₁ =>
      obtain ⟨t₁', h⟩ := hs₁
      exists <{ ~t₁' ~t₂ }>
      constructor <;> assumption
  | ite Γ t₁ t₂ t₃ T₁ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    right
    cases ih₁ hΓ with
    | inl hv₁ =>
      cases canonical_forms_bool t₁ (hΓ ▸ h₁) hv₁ with
      | inl he =>
        subst he
        exists t₂
        constructor
      | inr he =>
        subst he
        exists t₃
        constructor
    | inr hs₁ =>
      obtain ⟨t₁', h⟩ := hs₁
      exists <{ if ~t₁' then ~t₂ else ~t₃ }>
      constructor
      assumption

--  ## Preservation

--  For preservation, we need some technical machinery for
--  reasoning about variables and substitution.
--
--  - The *preservation theorem* is proved by induction on a
--    typing derivation and case analysis on the step
--    relation, pretty much as we did in the Types chapter.
--
--    Main novelty: `Step.appAbs` uses the substitution
--    operation.
--
--    To see that this step preserves typing, we need to
--    know that the substitution itself does. So we prove
--    a...

--  - *substitution lemma*, stating that substituting a
--    (closed, well-typed) term `s` for a variable `x` in a
--    term `t` preserves the type of `t`.
--
--  The proof goes by induction on the form of `t` and
--  requires looking at all the different cases in the
--  definition of substitution.
--
--  Tricky case: variables.
--
--  In this case, we need to deduce from the fact that a
--  term `s` has type S in the empty context the fact that
--  `s` has type S in every context.
--
--  For this we prove a...

--  - *weakening* lemma, showing that typing is preserved
--    under "extensions" to the context `Γ`.

--  To make Lean happy, we need to formalize all this in the
--  opposite order...

--  ### The Weakening Lemma

--  First, we show that typing is preserved under
--  "extensions" to the context `Γ`. (Recall map inclusion,
--  `Γ ⊆ Γ'`, from the `Typeclasses` chapter.)

-- IN PROGRESS
theorem weakening (Γ Γ' : Context) (t : Tm) (T : Ty)
    (hi : Γ ⊆ Γ') (hT : <{ ~Γ ⊢ ~t ⦂ ~T }>) : <{ ~Γ' ⊢ ~t ⦂ ~T }> := by
  induction hT generalizing Γ' with
  | var _ x _ h => exact .var _ x _ (hi h)
  | abs _ x _ _ _ _ ih => exact .abs _ x _ _ _ (ih _ (PartialMap.update_subset _ _ _ _ hi))
  | app _ _ _ _ _ _ _ ih₁ ih₂ => exact .app _ _ _ _ _ (ih₁ _ hi) (ih₂ _ hi)
  | tru => exact .tru _
  | fls => exact .fls _
  | ite _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ => exact .ite _ _ _ _ _ (ih₁ _ hi) (ih₂ _ hi) (ih₃ _ hi)

--  The following simple corollary is what we actually need
--  below.

theorem weakening_empty (Γ : Context) (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    <{ ~Γ ⊢ ~t ⦂ ~T }> :=
  weakening _ _ _ _
    (fun h => by
      rw [PartialMap.getElem_empty] at h
      cases h) hT

--  ### The Substitution Lemma

--  Now we come to the conceptual heart of the proof that
--  reduction preserves types — namely, the observation that
--  *substitution* preserves types.

--  The *substitution lemma* says:
--
--  - Suppose we have a term `t` with a free variable `x`,
--    and suppose we've been able to assign a type `T` to
--    `t` under the assumption that `x` has some type `U`.
--
--  - Also, suppose that we have some other term `v` and
--    that we've shown that `v` has type `U`.
--
--  - Then we can substitute `v` for each of the occurrences
--    of `x` in `t` and obtain a new term that still has
--    type `T`.

-- IN PROGRESS
theorem substitution_preserves_typing (Γ : Context) (x : String) (U : Ty)
    (t v : Tm) (T : Ty)
    (hT : <{ ~x ↦ ~U ; ~Γ ⊢ ~t ⦂ ~T }>) (hv : <{ ∅ ⊢ ~v ⦂ ~U }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~T }> := by
  -- By induction on `t`; in each case we get at the derivation of `hT`.
  induction t generalizing Γ T with
  | var y =>
    cases hT with
    | var _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [PartialMap.update_eq] at h
        rw [subst_var_eq]
        have hUT : U = T := Option.some.inj h
        subst hUT
        exact weakening_empty _ _ _ hv
      · rw [PartialMap.update_neq hxy] at h
        rw [subst_var_ne _ _ _ hxy]
        exact .var _ y _ h
  | app t₁ t₂ ih₁ ih₂ =>
    cases hT with
    | app _ _ _ _ _ h₁ h₂ => rw [subst_app]; exact .app _ _ _ _ _ (ih₁ _ _ h₁) (ih₂ _ _ h₂)
  | abs y S t₁ ih =>
    cases hT with
    | abs _ _ _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [subst_abs_eq]
        rw [PartialMap.update_shadow] at h
        exact .abs _ _ _ _ _ h
      · rw [subst_abs_ne _ _ _ _ _ hxy]
        rw [PartialMap.update_permute (Ne.symm hxy)] at h
        exact .abs _ _ _ _ _ (ih _ _ h)
  | tru => cases hT with | tru => rw [subst_tru]; exact .tru _
  | fls => cases hT with | fls => rw [subst_fls]; exact .fls _
  | ite c t e ihc iht ihe =>
    cases hT with
    | ite _ _ _ _ _ h₁ h₂ h₃ =>
      rw [subst_ite]
      exact .ite _ _ _ _ _ (ihc _ _ h₁) (iht _ _ h₂) (ihe _ _ h₃)

--  ### Main Theorem

--  We now have the ingredients we need to prove
--  preservation: if a closed, well-typed term `t` has type
--  `T` and takes a step to `t'`, then `t'` is also a closed
--  term with type `T`. In other words, the small-step
--  reduction relation preserves types.

-- IN PROGRESS
theorem preservation (t t' : Tm) (T : Ty)
    (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) (hs : t ⟶ t') : <{ ∅ ⊢ ~t' ⦂ ~T }> := by
  generalize hΓ : (∅ : Context) = Γ at hT
  induction hT generalizing t' with
  | var => cases hs
  | abs => cases hs
  | tru => cases hs
  | fls => cases hs
  | app Γ T₁ T₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    subst hΓ
    cases hs with
    | appAbs _ _ _ _ _ =>
      -- The one interesting case: the desired result is the substitution lemma.
      cases h₁ with
      | abs _ _ _ _ _ hb => exact substitution_preserves_typing _ _ _ _ _ _ hb h₂
    | app1 _ t₁' _ h => exact .app _ _ _ _ _ (ih₁ t₁' h rfl) h₂
    | app2 _ _ t₂' _ h => exact .app _ _ _ _ _ h₁ (ih₂ t₂' h rfl)
  | ite Γ t₁ t₂ t₃ T₁ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    subst hΓ
    cases hs with
    | ifTrue => exact h₂
    | ifFalse => exact h₃
    | ifStep _ t₁' _ _ h => exact .ite _ _ _ _ _ (ih₁ t₁' h rfl) h₂ h₃

end Stlc

--  Let's extend the STLC with a base type of numbers, some
--  constants, and some primitive operators.

namespace StlcArith

open scoped MyGetElem

--  To types, we add a base type of natural numbers (and
--  remove booleans, for brevity).

inductive Ty where
  | arrow (T₁ T₂ : Ty)
  | nat

--  To terms, we add natural number constants, along with
--  successor, predecessor, multiplication, and
--  zero-testing.

inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (T : Ty) (t : Tm)
  | const (n : Nat)
  | succ (t : Tm)
  | pred (t : Tm)
  | mult (t₁ t₂ : Tm)
  | ite0 (c t e : Tm)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: types)
--  The type grammar needs no new productions: `Nat` is a
--  bare identifier, which the template already accepts, and
--  arrows and parentheses are unchanged. Only the
--  `macro_rules` are new, and they differ from the STLC's
--  in just two places — the identifier `Nat` names this
--  language's base type, and the arrow builds this
--  language's `StlcArith.Ty.arrow`.

scoped macro_rules (kind := Stlc.tyBracket)
  | `(<{ ~$T:term }>)    => pure T
  | `(<{ ($T:stlcTy) }>) => `(<{ $T:stlcTy }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat" => `(Ty.nat)
      | _ => `(($x : Ty))
  | `(<{ $T₁:stlcTy → $T₂:stlcTy }>)  => `(Ty.arrow <{ $T₁:stlcTy }> <{ $T₂:stlcTy }>)
  | `(<{ $T₁:stlcTy -> $T₂:stlcTy }>) => `(Ty.arrow <{ $T₁:stlcTy }> <{ $T₂:stlcTy }>)
--  END DETAILS

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: terms)
--  Terms do need new productions: a numeral, an infix `*`,
--  and the zero test. Multiplication binds looser than
--  application and tighter than `λ`, so `x * y z`
--  multiplies `x` by the application `y z`; it associates
--  to the right, so `x * y * z` is `x * (y * z)`.
--
--  `succ` and `pred` get no production of their own. Making
--  them keywords would reserve those words globally — and
--  we would then be unable to write `succ` as a case name
--  in a proof, including for Lean's own `Nat`. Instead they
--  are written as though they were functions applied to an
--  argument, `succ t`, and the application rule below
--  recognizes them. `if0` **is** a keyword, since `then`
--  and `else` leave no other option; that is why the
--  constructor above is called `StlcArith.Tm.ite0` rather
--  than `if0`, just as the STLC's conditional is
--  `Stlc.Tm.ite`.

scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:61 " * " stlcTm:60 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

open Lean in
scoped macro_rules (kind := Stlc.tmBracket)
  | `(<{ ~$e:term }>)    => pure e
  | `(<{ ($t:stlcTm) }>) => `(<{ $t:stlcTm }>)
  | `(<{ $n:num }>)      => `(Tm.const $n)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat"  => Macro.throwErrorAt x "`Nat` is a type, not a term"
      | "succ" => Macro.throwErrorAt x "`succ` must be applied to an argument"
      | "pred" => Macro.throwErrorAt x "`pred` must be applied to an argument"
      | _      => `(Tm.var $(quote x.getId.toString))
  | `(<{ $t₁:stlcTm $t₂:stlcTm }>) =>
      match t₁ with
      | `(stlcTm| $f:ident) =>
          match f.getId.toString with
          | "succ" => `(Tm.succ <{ $t₂:stlcTm }>)
          | "pred" => `(Tm.pred <{ $t₂:stlcTm }>)
          | _      => `(Tm.app <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
      | _ => `(Tm.app <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ λ $x : $T . $t }>) => do
      `(Tm.abs $(← Stlc.varStr x) <{ $T:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ $t₁:stlcTm * $t₂:stlcTm }>) => `(Tm.mult <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ if0 $c then $t else $e }>) =>
      `(Tm.ite0 <{ $c:stlcTm }> <{ $t:stlcTm }> <{ $e:stlcTm }>)
--  END DETAILS

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing it back)
--  As in the Stlc chapter, a delaborator runs the grammar
--  backwards, so that goals mentioning these terms and
--  types read in the concrete syntax. The parenthesizers
--  registered there are for the whole syntax category, so
--  they serve this language too and are not repeated.

open Lean in
/-- Is `s` usable as a bare variable in `stlcTm` rather than as reserved syntax? -/
def isPlainTmVarName (s : String) : Bool :=
  Stlc.isPlainName s && s != "Nat" && s != "succ" && s != "pred"

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTy` concrete syntax from a `Ty` value. -/
partial def delabTyInner : DelabM (TSyntax `stlcTy) := do
  let stx ←
    match_expr ← getExpr with
    | Ty.nat => `(stlcTy| $(mkIdent `Nat):ident)
    | Ty.arrow _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a → $b)
    | _ => do
        match ← delab with
        | `($i:ident) => `(stlcTy| $i:ident)
        | e => `(stlcTy| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTm` concrete syntax from a `Tm` value. -/
partial def delabTmInner : DelabM (TSyntax `stlcTm) := do
  let stx ←
    match_expr ← getExpr with
    | Tm.var _ => do
        let x ← withAppArg delab
        match x with
        | `($s:str) =>
            if isPlainTmVarName s.getString then
              `(stlcTm| $(mkIdent (Name.mkSimple s.getString)):ident)
            else
              let var : Term := mkIdent ``StlcArith.Tm.var
              `(stlcTm| ~($var $x))
        | _ =>
            let var : Term := mkIdent ``StlcArith.Tm.var
            `(stlcTm| ~($var $x))
    | Tm.const _ => do
        let n ← withAppArg delab
        match n with
        | `($n:num) => `(stlcTm| $n:num)
        | _ =>
            let const : Term := mkIdent ``StlcArith.Tm.const
            `(stlcTm| ~($const $n))
    | Tm.app _ _ => do
        let f ← withAppFn <| withAppArg delabTmInner
        let a ← withAppArg delabTmInner
        `(stlcTm| $f $a)
    | Tm.abs _ _ _ => do
        let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let T ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| λ $x : $T . $t)
    | Tm.succ _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `succ):ident $t)
    | Tm.pred _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `pred):ident $t)
    | Tm.mult _ _ => do
        let a ← withAppFn <| withAppArg delabTmInner
        let b ← withAppArg delabTmInner
        `(stlcTm| $a * $b)
    | Tm.ite0 _ _ _ => do
        let c ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let t ← withAppFn <| withAppArg delabTmInner
        let e ← withAppArg delabTmInner
        `(stlcTm| if0 $c then $t else $e)
    | _ => do
        -- `subst` is defined below, so it is matched by name rather than with
        -- `match_expr`; a substitution prints in its own bracket notation.
        let e ← getExpr
        if e.getAppFn.constName? == some `StlcArith.subst && e.getAppNumArgs == 3 then
          let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
          let s ← withAppFn <| withAppArg delabTmInner
          let t ← withAppArg delabTmInner
          `(stlcTm| [$x := $s] $t)
        else
          match ← delab with
          | `($i:ident) => `(stlcTm| $i:ident)
          | e => `(stlcTm| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcArith.Ty.nat, delab app.StlcArith.Ty.arrow]
def delabTy : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Ty.nat => true | Ty.arrow _ _ => true | _ => false
  match ← delabTyInner with
  | `(stlcTy| ~$e) => pure e
  | e => `(<{ $e:stlcTy }>)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcArith.Tm.var, delab app.StlcArith.Tm.app, delab app.StlcArith.Tm.abs,
  delab app.StlcArith.Tm.const, delab app.StlcArith.Tm.succ, delab app.StlcArith.Tm.pred,
  delab app.StlcArith.Tm.mult, delab app.StlcArith.Tm.ite0]
def delabTm : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Tm.var _ => true | Tm.app _ _ => true | Tm.abs _ _ _ => true
    | Tm.const _ => true | Tm.succ _ => true | Tm.pred _ => true
    | Tm.mult _ _ => true | Tm.ite0 _ _ _ => true
    | _ => false
  match ← delabTmInner with
  | `(stlcTm| ~($e)) => pure e
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
--  END DETAILS

end StlcArith

-- Built on 2026-08-31 21:29 UTC

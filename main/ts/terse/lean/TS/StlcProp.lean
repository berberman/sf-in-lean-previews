import TS.Stlc
import LF.CustomTactics

import SFLCompat

--  # StlcProp: Properties of STLC

--  THE SIMPLY TYPED LAMBDA CALCULUS
--
--  Syntax:

--  t ::= x                     (variable)
--      | λ x : τ . t           (abstraction)
--      | t t                   (application)
--      | true                  (constant true)
--      | false                 (constant false)
--      | if t then t else t    (conditional)

--  Values:

--  v ::= λ x : τ . t
--      | true
--      | false

--  Substitution:
--
--      [x:=s]x               = s
--      [x:=s]y               = y                     if x ≠ y
--      [x:=s](λx:τ. t)       = λx:τ. t
--      [x:=s](λy:τ. t)       = λy:τ. [x:=s]t         if x ≠ y
--      [x:=s](t₁ t₂)         = ([x:=s]t₁) ([x:=s]t₂)
--      [x:=s]true            = true
--      [x:=s]false           = false
--      [x:=s](if t₁ then t₂ else t₃) =
--                      if [x:=s]t₁ then [x:=s]t₂ else [x:=s]t₃
--
--  Small-step operational semantics:

--  v.IsValue
--                         -----------------------                    (appAbs)
--                          (λx:τ. t) v ⟶ [x:=v]t
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

--  Γ x = τ₁
--                              ------------                       (var)
--                               Γ ⊢ x ⦂ τ₁
--
--                          x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁
--                        -------------------------                (abs)
--                         Γ ⊢ λx:τ₂. t₁ ⦂ τ₂ → τ₁
--
--                            Γ ⊢ t₁ ⦂ τ₂ → τ₁
--                              Γ ⊢ t₂ ⦂ τ₂
--                           ------------------                    (app)
--                             Γ ⊢ t₁ t₂ ⦂ τ₁
--
--                            -----------------                    (tru)
--                             Γ ⊢ true ⦂ Bool
--
--                           ------------------                    (fls)
--                            Γ ⊢ false ⦂ Bool
--
--               Γ ⊢ t₁ ⦂ Bool    Γ ⊢ t₂ ⦂ τ₁    Γ ⊢ t₃ ⦂ τ₁
--              ---------------------------------------------      (ite)
--                     Γ ⊢ if t₁ then t₂ else t₃ ⦂ τ₁

--  In this chapter, we develop the fundamental theory of
--  the Simply Typed Lambda Calculus — in particular, the
--  type safety theorem.
--
--  We pick up where the Stlc chapter left off, so
--  everything below lives in the same namespace as the
--  definitions it is about.

namespace Stlc

open scoped MyGetElem
open scoped Elab

--  ## Canonical Forms

--  Formally, we will need these lemmas only for terms that
--  are not only well typed but *closed* — i.e., well typed
--  in the empty context.

theorem canonical_forms_bool (t : Tm) (hτ : <{ ∅ ⊢ t ⦂ Bool }>) (hv : t.IsValue) :
    t = <{ true }> ∨ t = <{ false }> := by
  cases hv with
  | abs x τ t₁ => cases hτ
  | tru => left; rfl
  | fls => right; rfl

theorem canonical_forms_fun (t : Tm) (τ₁ τ₂ : Ty)
    (hτ : <{ ∅ ⊢ t ⦂ τ₁ → τ₂ }>) (hv : t.IsValue) :
    ∃ x u, t = <{ λ x : τ₁ . u }> := by
  cases hv with
  | abs x τ t₁ => cases hτ with | abs _ _ _ _ _ _ =>
    exists x, t₁
  | tru => cases hτ
  | fls => cases hτ

--  ## Progress

--  The *progress* theorem tells us that closed, well-typed
--  terms are not stuck.

theorem progress (t : Tm) (τ : Ty) (hτ : <{ ∅ ⊢ t ⦂ τ }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  generalize hΓ : (∅ : Context) = Γ at hτ
  induction hτ with
  | var Γ x τ₁ h =>
    subst hΓ
    -- Contradictory: variables cannot be typed in an empty context.
    rw [PartialMap.getElem_empty] at h
    cases h
  | abs => left; constructor
  | tru => left; constructor
  | fls => left; constructor
  | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    -- `t = t₁ t₂`.  Proceed by cases on whether `t₁` is a value or steps.
    subst hΓ
    right
    cases ih₁ rfl with
    | inl hv₁ =>
      cases ih₂ rfl with
      | inl hv₂ =>
        obtain ⟨x, u, rfl⟩ := canonical_forms_fun t₁ _ _ h₁ hv₁
        exists <{ [x := t₂] u }>
        constructor
        assumption
      | inr hs₂ =>
        obtain ⟨t₂', h⟩ := hs₂
        exists <{ t₁ t₂' }>
        constructor <;> assumption
    | inr hs₁ =>
      obtain ⟨t₁', h⟩ := hs₁
      exists <{ t₁' t₂ }>
      constructor <;> assumption
  | ite Γ t₁ t₂ t₃ τ₁ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    subst hΓ
    right
    cases ih₁ rfl with
    | inl hv₁ =>
      cases canonical_forms_bool t₁ h₁ hv₁ with
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
      exists <{ if t₁' then t₂ else t₃ }>
      constructor
      assumption

--  ## Preservation

--  For preservation, we need some technical machinery for
--  reasoning about variables and substitution.
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
--  term `s` has type `σ` in the empty context the fact that
--  `s` has type `σ` in every context.
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

theorem weakening {Γ Γ' : Context} {t : Tm} {τ : Ty}
    (hi : Γ ⊆ Γ') (ht : <{ Γ ⊢ t ⦂ τ }>) : <{ Γ' ⊢ t ⦂ τ }> := by
  induction ht generalizing Γ' with
  | var _ x _ h =>
    constructor
    exact hi h
  | abs _ x _ _ _ _ ih =>
    constructor
    apply ih
    apply PartialMap.update_subset
    assumption
  | app _ _ _ _ _ _ _ ih₁ ih₂ =>
    constructor
    · apply ih₁
      exact hi
    · apply ih₂
      exact hi
  | tru => constructor
  | fls => constructor
  | ite _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
    constructor
    · apply ih₁
      exact hi
    · apply ih₂
      exact hi
    · apply ih₃
      exact hi

--  Through judicious use of `apply_rules`, we can heavily
--  automate this proof. The tactic after `with` is applied
--  to every case of the `induction` and handles all the
--  cases using `apply_rules`'s automation. We must give the
--  tactic access to all the `HasType` constructors and the
--  `PartialMap.update_subset` lemma for this to work:

theorem weakening' {Γ Γ' : Context} {t : Tm} {τ : Ty}
    (hi : Γ ⊆ Γ') (ht : <{ Γ ⊢ t ⦂ τ }>) : <{ Γ' ⊢ t ⦂ τ }> := by
  induction ht generalizing Γ' with (apply_rules [PartialMap.update_subset] using StlcTyping)

--  The following simple corollary is what we actually need
--  below.

theorem weakening_empty {Γ : Context} {t : Tm} {τ : Ty} (ht : <{ ∅ ⊢ t ⦂ τ }>) :
    <{ Γ ⊢ t ⦂ τ }> := by
  apply weakening (Γ := ∅)
  -- this is the "manual" way to show that the empty context is a subset of any context:
  -- show that a 'lookup' in it is impossible.
  · intros x b contra
    contradiction
  · assumption

--  ### The Substitution Lemma

--  Now we come to the conceptual heart of the proof that
--  reduction preserves types — namely, the observation that
--  *substitution* preserves types.
--
--  The *substitution lemma* says:
--  - Suppose we have a term `t` with a free variable `x`,
--    and suppose we've been able to assign a type `τ` to
--    `t` under the assumption that `x` has some type `τ'`.
--  - Also, suppose that we have some other term `v` and
--    that we've shown that `v` has type `τ'`.
--  - Then we can substitute `v` for each of the occurrences
--    of `x` in `t` and obtain a new term that still has
--    type `τ`.

theorem substitution_preserves_typing (Γ : Context) (x : String) (τ' : Ty)
    (t v : Tm) (τ : Ty)
    (hτ : <{ x ↦ τ' ; Γ ⊢ t ⦂ τ }>) (hv : <{ ∅ ⊢ v ⦂ τ' }>) :
    <{ Γ ⊢ [x := v] t ⦂ τ }> := by
  -- By induction on `t`; in each case we get at the derivation of `hτ`.
  induction t generalizing Γ τ with
  | var y =>
    cases hτ with
    | var _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [PartialMap.update_eq] at h
        rw [subst_var_eq]
        have hτ'τ : τ' = τ := by
          apply Option.some.inj
          exact h
        subst hτ'τ
        apply weakening_empty
        exact hv
      · rw [PartialMap.update_neq hxy] at h
        rw [subst_var_ne _ _ _ hxy]
        constructor
        exact h
  | app t₁ t₂ ih₁ ih₂ =>
    cases hτ with
    | app _ _ _ _ _ h₁ h₂ =>
      rw [subst_app]
      constructor
      · apply ih₁
        exact h₁
      · apply ih₂
        exact h₂
  | abs y σ t₁ ih =>
    cases hτ with
    | abs _ _ _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [subst_abs_eq]
        rw [PartialMap.update_shadow] at h
        constructor
        exact h
      · rw [subst_abs_ne _ _ _ _ _ hxy]
        rw [PartialMap.update_permute (Ne.symm hxy)] at h
        constructor
        apply ih
        exact h
  | tru =>
    cases hτ with
    | tru =>
      rw [subst_tru]
      constructor
  | fls =>
    cases hτ with
    | fls =>
      rw [subst_fls]
      constructor
  | ite c t e ihc iht ihe =>
    cases hτ with
    | ite _ _ _ _ _ h₁ h₂ h₃ =>
      rw [subst_ite]
      constructor
      · apply ihc
        exact h₁
      · apply iht
        exact h₂
      · apply ihe
        exact h₃

--  ### Main Theorem

--  We now have the ingredients we need to prove
--  preservation: if a closed, well-typed term `t` has type
--  `τ` and takes a step to `t'`, then `t'` is also a closed
--  term with type `τ`. In other words, the small-step
--  reduction relation preserves types.

theorem preservation (t t' : Tm) (τ : Ty)
    (hτ : <{ ∅ ⊢ t ⦂ τ }>) (hs : t ⟶ t') : <{ ∅ ⊢ t' ⦂ τ }> := by
  generalize hΓ : (∅ : Context) = Γ at hτ
  induction hτ generalizing t' with
  | var => cases hs
  | abs => cases hs
  | tru => cases hs
  | fls => cases hs
  | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    subst hΓ
    cases hs with
    | appAbs _ _ _ _ _ =>
      -- The one interesting case: the desired result is the substitution lemma.
      cases h₁ with
      | abs _ _ _ _ _ hb =>
        apply substitution_preserves_typing
        · exact hb
        · exact h₂
    | app1 _ t₁' _ h =>
      constructor
      · apply ih₁
        · exact h
        · rfl
      · exact h₂
    | app2 _ _ t₂' _ h =>
      constructor
      · exact h₁
      · apply ih₂
        · exact h
        · rfl
  | ite Γ t₁ t₂ t₃ τ₁ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    subst hΓ
    cases hs with
    | ifTrue => exact h₂
    | ifFalse => exact h₃
    | ifStep _ t₁' _ _ h =>
      constructor
      · apply ih₁
        · exact h
        · rfl
      · exact h₂
      · exact h₃

end Stlc

--  Let's extend the STLC with a base type of numbers, some
--  constants, and some primitive operators.

namespace StlcArith

open scoped MyGetElem

--  To types, we add a base type of natural numbers (and
--  remove booleans, for brevity).

inductive Ty where
  | arrow (τ₁ τ₂ : Ty)
  | nat

--  To terms, we add natural number constants, along with
--  successor, predecessor, multiplication, and
--  zero-testing.

inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (τ : Ty) (t : Tm)
  | const (n : Nat)
  | succ (t : Tm)
  | pred (t : Tm)
  | mult (t₁ t₂ : Tm)
  | ite0 (c t e : Tm)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding)
scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:60 " * " stlcTm:61 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

namespace Elab

open StlcCommon
open Lean Meta Elab Term

def language : Language where
  tyType := ``Ty
  tmType := ``Tm
  arrowCtor := ``Ty.arrow
  varCtor := ``Tm.var
  appCtor := ``Tm.app
  absCtor := ``Tm.abs

  -- defined later
  subst := `StlcArith.subst
  hasType := `StlcArith.HasType

def natTyHandler : TyElabHandler :=
  fun _recur k T => do
    match T with
    | `(stlcTy| Nat) =>
        return mkConst ``Ty.nat
    | _ => k T

def tyHandlers : TyElabHandler :=
  natTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy <| unsupportedTy language

def arithTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| $n:num) => do
        return (mkApp (mkConst ``Tm.const) (mkNatLit n.getNat), free)
    | `(stlcTm| Nat) => do
        throwError "`Nat` is not a valid term."
    | `(stlcTm| succ $e:stlcTm) => do
        let (e, free) ←  recur Γ free e
        return (mkApp (mkConst ``Tm.succ) e, free)
    | `(stlcTm| pred $e:stlcTm) => do
        let (e, free) ←  recur Γ free e
        return (mkApp (mkConst ``Tm.pred) e, free)
    | `(stlcTm| $t₁:stlcTm * $t₂:stlcTm) => do
        let (e₁, free) ←  recur Γ free t₁
        let (e₂, free) ←  recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.mult) e₁ e₂, free)
    | `(stlcTm| if0 $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite0) c t e, free)
    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  arithTmHandler.orElse (commonTmHandler language elabTy)

partial def elabTm : TmElab :=
  tmHandlers elabTm unsupportedTm

def elabCtx : CtxElab := elabCtxCommon language elabTy

@[scoped term_elab StlcCommon.bracket]
def elabBracket : TermElab :=
  fun stx expectedType? => do
    let `(<{ $q:stlcQuoted }>) := stx
      | throwUnsupportedSyntax
    elabQuoted language elabTy elabTm elabCtx q expectedType?

end Elab

open scoped Elab


namespace Delab

open StlcCommon Elab Delab
open Lean PrettyPrinter Delaborator

@[app_unexpander Ty.nat]
private def Ty.unexpandNat : Unexpander
  | stx => do
    let T ← `(stlcTy| $(mkIdentFrom stx `Nat):ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

private def reservedNames : String → Bool
  | "Nat" | "succ" | "pred" | "if0" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.ite0]
private def Tm.unexpandIte : Unexpander
  | `($_ $c $t $e) =>
      `(<{ if0 $(getTm c) then $(getTm t) else $(getTm e) }>)
  | _ => throw ()

@[app_unexpander Tm.const]
def Tm.unexpandConst : Unexpander
  | `($_ $n:num) => `(<{ $n:num }>)
  | _ => throw ()

@[app_unexpander Tm.succ]
def Tm.unexpandSucc : Unexpander
  | stx@`($_ $t) => do
    let succ := mkObjectIdentFrom stx "succ"
    `(<{ $succ:ident $(getTm t) }>)
  | _ => throw ()

@[app_unexpander Tm.pred]
def Tm.unexpandPred : Unexpander
  | stx@`($_ $t) => do
    let pred := mkObjectIdentFrom stx "pred"
    `(<{ $pred:ident $(getTm t) }>)
  | _ => throw ()

@[app_unexpander Tm.mult]
def Tm.unexpandMult : Unexpander
  | `($_ $t₁ $t₂) => do
    let t ← `(stlcTm| $(getTm t₁) * $(getTm t₂))
    let q ← `(stlcQuoted| $t:stlcTm)
    `(<{ $q:stlcQuoted }>)
  | _ => throw ()

end Delab
--  END DETAILS

end StlcArith

-- Source revision: 00e1228, committed 2026-10-05 22:06 UTC

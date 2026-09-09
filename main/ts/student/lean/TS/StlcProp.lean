import TS.Stlc
import LF.CustomTactics

import SFLCompat

--  # StlcProp: Properties of STLC

--  In this chapter, we develop the fundamental theory of the Simply Typed
--  Lambda Calculus — in particular, the type safety theorem.
--
--  We pick up where the Stlc chapter left off, so everything below lives
--  in the same namespace as the definitions it is about.

namespace Stlc

open scoped MyGetElem

--  ## Canonical Forms

--  As we saw for the very simple language in the Types chapter, the first
--  step in establishing basic properties of reduction and types is to
--  identify the possible *canonical forms* (i.e., well-typed values)
--  belonging to each type. For `Bool`, these are again the boolean values
--  `true` and `false`; for arrow types, they are lambda-abstractions.

--  Formally, we will need these lemmas only for terms that are not only
--  well typed but *closed* — i.e., well typed in the empty context.

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

--  The *progress* theorem tells us that closed, well-typed terms are not
--  stuck: either a well-typed term is a value, or it can take a reduction
--  step. The proof is a relatively straightforward extension of the
--  progress proof we saw in the Types chapter. We give the proof in
--  English first, then the formal version.

--  *Proof*: By induction on the derivation of `⊢ t ⦂ T`.
--
--  - The last rule of the derivation cannot be `HasType.var`, since a
--    variable is never well typed in an empty context.
--
--  - The `HasType.tru`, `HasType.fls`, and `HasType.abs` cases are
--    trivial, since in each of these cases we can see by inspecting the
--    rule that `t` is a value.
--
--  - If the last rule of the derivation is `HasType.app`, then `t` has the
--    form `t₁ t₂` for some `t₁` and `t₂`, where `⊢ t₁ ⦂ T₂ → T` and
--    `⊢ t₂ ⦂ T₂` for some type `T₂`. The induction hypothesis for the
--    first subderivation says that either `t₁` is a value or else it can
--    take a reduction step.
--
--    - If `t₁` is a value, then consider `t₂`, which by the induction
--      hypothesis for the second subderivation must also either be a value
--      or take a step.
--
--      - Suppose `t₂` is a value. Since `t₁` is a value with an arrow
--        type, it must be a lambda abstraction; hence `t₁ t₂` can take a
--        step by `Step.appAbs`.
--
--      - Otherwise, `t₂` can take a step, and hence so can `t₁ t₂` by
--        `Step.app2`.
--
--    - If `t₁` can take a step, then so can `t₁ t₂` by `Step.app1`.
--
--  - If the last rule of the derivation is `HasType.ite`, then
--    `t = if t₁ then t₂ else t₃`, where `t₁` has type `Bool`. The first IH
--    says that `t₁` either is a value or takes a step.
--
--    - If `t₁` is a value, then since it has type `Bool` it must be either
--      `true` or `false`. If it is `true`, then `t` steps to `t₂`;
--      otherwise it steps to `t₃`.
--
--    - Otherwise, `t₁` takes a step, and therefore so does `t` (by
--      `Step.ifStep`).

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

--  ### Exercise (3 stars): progress_from_term_ind (Advanced) ⭐⭐⭐

--  Show that progress can also be proved by induction on terms instead of
--  induction on typing derivations.

-- IN PROGRESS
theorem progress' (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  sorry

--  ## Preservation

--  The other half of the type soundness property is the preservation of
--  types during reduction. For this part, we'll need to develop some
--  technical machinery for reasoning about variables and substitution.
--  Working from top to bottom (from the high-level property we are
--  actually interested in to the lowest-level technical lemmas that are
--  needed by various cases of the more interesting proofs), the story goes
--  like this:
--
--  - The *preservation theorem* is proved by induction on a typing
--    derivation and case analysis on the step relation, pretty much as we
--    did in the Types chapter. The one case that is significantly
--    different is the one for the `Step.appAbs` rule, whose definition
--    uses the substitution operation. To see that this step preserves
--    typing, we need to know that the substitution itself does. So we
--    prove a...
--
--  - *substitution lemma*, stating that substituting a (closed,
--    well-typed) term `s` for a variable `x` in a term `t` preserves the
--    type of `t`. The proof goes by induction on the form of `t` and
--    requires looking at all the different cases in the definition of
--    substitution. This time, for the variables case, we discover that we
--    need to deduce from the fact that a term `s` has type S in the empty
--    context the fact that `s` has type S in every context. For this we
--    prove a...
--
--  - *weakening* lemma, showing that typing is preserved under
--    "extensions" to the context `Γ`.
--
--  To make Lean happy, though, we need to formalize the story in the
--  opposite order, starting with weakening...

--  ### The Weakening Lemma

--  First, we show that typing is preserved under "extensions" to the
--  context `Γ`. (Recall map inclusion, `Γ ⊆ Γ'`, from the `Typeclasses`
--  chapter.)

theorem weakening {Γ Γ' : Context} {t : Tm} {τ : Ty}
    (hi : Γ ⊆ Γ') (ht : <{ ~Γ ⊢ ~t ⦂ ~τ }>) : <{ ~Γ' ⊢ ~t ⦂ ~τ }> := by
  induction ht generalizing Γ' with
  | var =>
      constructor; apply hi; assumption
  | abs _ _ _ _ _ _ ih =>
      constructor; apply ih; apply PartialMap.update_subset; assumption
  | app _ _ _ _ _ _ _ ih₁ ih₂ =>
      constructor
      . exact ih₁ hi
      . exact ih₂ hi
  | tru => constructor
  | fls => constructor
  | ite _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
      constructor
      . exact ih₁ hi
      . exact ih₂ hi
      . exact ih₃ hi

--  Through judicious use of `apply_rules`, we can heavily automate this
--  proof. The tactic after `with` is applied to every case of the
--  `induction` and handles all the cases using `apply_rules`'s automation.
--  We must give the tactic access to all the `HasType` constructors and
--  the `PartialMap.update_subset` lemma for this to work:

theorem weakening' {Γ Γ' : Context} {t : Tm} {τ : Ty}
    (hi : Γ ⊆ Γ') (ht : <{ ~Γ ⊢ ~t ⦂ ~τ }>) : <{ ~Γ' ⊢ ~t ⦂ ~τ }> := by
  induction ht generalizing Γ' with (apply_rules [PartialMap.update_subset] using StlcTyping)

--  The following simple corollary is what we actually need below.

theorem weakening_empty {Γ : Context} {t : Tm} {τ : Ty} (ht : <{ ∅ ⊢ ~t ⦂ ~τ }>) :
    <{ ~Γ ⊢ ~t ⦂ ~τ }> := by
  apply weakening _ ht
  intro _ _ h
  rw [PartialMap.getElem_empty] at h
  contradiction

--  ### The Substitution Lemma

--  Now we come to the conceptual heart of the proof that reduction
--  preserves types — namely, the observation that *substitution* preserves
--  types.

--  Formally, the so-called *substitution lemma* says this: Suppose we have
--  a term `t` with a free variable `x`, and suppose we've assigned a type
--  `T` to `t` under the assumption that `x` has some type `U`. Also,
--  suppose that we have some other term `v` and that we've shown that `v`
--  has type `U`. Then, since `v` satisfies the assumption we made about
--  `x` when typing `t`, we can substitute `v` for each of the occurrences
--  of `x` in `t` and obtain a new term that still has type `T`.

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
        exact weakening_empty hv
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

--  The substitution lemma can be viewed as a kind of "commutation
--  property." Intuitively, it says that substitution and typing can be
--  done in either order: we can either assign types to the terms `t` and
--  `v` separately (under suitable contexts) and then combine them using
--  substitution, or we can substitute first and then assign a type to
--  `[x:=v] t`; the result is the same either way.
--
--  *Proof*: We show, by induction on `t`, that for all `T` and `Γ`, if
--  `x ↦ U; Γ ⊢ t ⦂ T` and `⊢ v ⦂ U`, then `Γ ⊢ [x:=v]t ⦂ T`.
--
--  - If `t` is a variable there are two cases to consider, depending on
--    whether `t` is `x` or some other variable.
--
--    - If `t = x`, then from the fact that `x ↦ U; Γ ⊢ x ⦂ T` we conclude
--      that `U = T`. We must show that `[x:=v]x = v` has type `T` under
--      `Γ`, given the assumption that `v` has type `U = T` under the empty
--      context. This follows from the weakening lemma.
--
--    - If `t` is some variable `y` that is not equal to `x`, then we need
--      only note that `y` has the same type under `x ↦ U; Γ` as under `Γ`.
--
--  - If `t` is an abstraction `λy:S. t₀`, then `T = S→T₁` and the IH tells
--    us, for all `Γ'` and `T₀`, that if `x ↦ U; Γ' ⊢ t₀ ⦂ T₀`, then
--    `Γ' ⊢ [x:=v]t₀ ⦂ T₀`. Moreover, by inspecting the typing rules we see
--    it must be the case that `y ↦ S; x ↦ U; Γ ⊢ t₀ ⦂ T₁`.
--
--    The substitution in the conclusion behaves differently depending on
--    whether `x` and `y` are the same variable.
--
--    First, suppose `x = y`. Then, by the definition of substitution,
--    `[x:=v]t = t`, so we just need to show `Γ ⊢ t ⦂ T`. Using
--    `HasType.abs`, we need to show that `y ↦ S; Γ ⊢ t₀ ⦂ T₁`. But we know
--    `y ↦ S; x ↦ U; Γ ⊢ t₀ ⦂ T₁`, and the claim follows since `x = y`.
--
--    Second, suppose `x <> y`. Again, using `HasType.abs`, we need to show
--    that `y ↦ S; Γ ⊢ [x:=v]t₀ ⦂ T₁`. Since `x <> y`, we have
--    `y ↦ S; x ↦ U; Γ = x ↦ U; y ↦ S; Γ`. So we have
--    `x ↦ U; y ↦ S; Γ ⊢ t₀ ⦂ T₁`. Then, the the IH applies (taking
--    `Γ' = y ↦ S; Γ`), giving us `y ↦ S; Γ ⊢ [x:=v]t₀ ⦂ T₁`, as required.
--
--  - If `t` is an application `t₁ t₂`, the result follows
--    straightforwardly from the definition of substitution and the
--    induction hypotheses.
--
--  - The remaining cases are similar to the application case.

--  One technical subtlety in the statement of the above lemma is that we
--  assume `v` has type `U` in the *empty* context — in other words, we
--  assume `v` is closed. (Since we are using a simple definition of
--  substitution that is not capture-avoiding, it doesn't make sense to
--  substitute non-closed terms into other terms. Fortunately, closed terms
--  are all we need!)

--  ### Exercise (3 stars): substitution_preserves_typing_from_typing_ind (Advanced) ⭐⭐⭐

--  Show that substitution*preserves*typing can also be proved by induction
--  on typing derivations instead of induction on terms.

-- IN PROGRESS
theorem substitution_preserves_typing_from_typing_ind (Γ : Context) (x : String) (U : Ty)
    (t v : Tm) (T : Ty)
    (hT : <{ ~x ↦ ~U ; ~Γ ⊢ ~t ⦂ ~T }>) (hv : <{ ∅ ⊢ ~v ⦂ ~U }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~T }> := by
  sorry

--  ### Main Theorem

--  We now have the ingredients we need to prove preservation: if a closed,
--  well-typed term `t` has type `T` and takes a step to `t'`, then `t'` is
--  also a closed term with type `T`. In other words, the small-step
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

--  *Proof*: By induction on the derivation of `⊢ t ⦂ T`.
--
--  - We can immediately rule out `HasType.var`, `HasType.abs`,
--    `HasType.tru`, and `HasType.fls` as final rules in the derivation,
--    since in each of these cases `t` cannot take a step.
--
--  - If the last rule in the derivation is `HasType.app`, then
--    `t = t₁ t₂`, and there are subderivations showing that `⊢ t₁ ⦂ T₂→T`
--    and `⊢ t₂ ⦂ T₂` plus two induction hypotheses: (1) `t₁ ⟶ t₁'` implies
--    `⊢ t₁' ⦂ T₂→T` and (2) `t₂ ⟶ t₂'` implies `⊢ t₂' ⦂ T₂`. There are now
--    three subcases to consider, one for each rule that could be used to
--    show that `t₁ t₂` takes a step to `t'`.
--
--    - If `t₁ t₂` takes a step by `Step.app1`, with `t₁` stepping to
--      `t₁'`, then, by the first IH, `t₁'` has the same type as `t₁`
--      (`⊢ t₁' ⦂ T₂→T`), and hence by `HasType.app` `t₁' t₂` has type `T`.
--
--    - The `Step.app2` case is similar, using the second IH.
--
--    - If `t₁ t₂` takes a step by `Step.appAbs`, then `t₁ = λx:T₀. t₀` and
--      `t₁ t₂` steps to `[x0:=t₂]t₀`; the desired result now follows from
--      the substitution lemma.
--
--  - If the last rule in the derivation is `HasType.ite`, then
--    `t = if t₁ then t₂ else t₃`, with `⊢ t₁ ⦂ Bool`, `⊢ t₂ ⦂ T₁`, and
--    `⊢ t₃ ⦂ T₁`, and with three induction hypotheses: (1) `t₁ ⟶ t₁'`
--    implies `⊢ t₁' ⦂ Bool`, (2) `t₂ ⟶ t₂'` implies `⊢ t₂' ⦂ T₁`, and (3)
--    `t₃ ⟶ t₃'` implies `⊢ t₃' ⦂ T₁`.
--
--    There are again three subcases to consider, depending on how `t`
--    steps.
--
--    - If `t` steps to `t₂` or `t₃` by `Step.ifTrue` or `Step.ifFalse`,
--      the result is immediate, since `t₂` and `t₃` have the same type as
--      `t`.
--
--    - Otherwise, `t` steps by `Step.ifStep`, and the desired conclusion
--      follows directly from the first induction hypothesis.

--  ### Exercise (2 stars): subject_expansion_stlc (Manually graded) ⭐⭐

--  An exercise in the Types chapter asked about the *subject expansion*
--  property for the simple language of arithmetic and boolean expressions.
--  This property did not hold for that language, and it also fails for
--  STLC. That is, it is not always the case that, if `t ⟶ t'` and
--  `empty ⊢ t' ⦂ T`, then `empty ⊢ t ⦂ T`. Show this by giving a
--  counter-example that does *not involve conditionals*.

theorem not_subject_expansion :
    ∃ (t t' : Tm) (T : Ty), t ⟶ t' ∧ <{ ∅ ⊢ ~t' ⦂ ~T }> ∧ ¬ <{ ∅ ⊢ ~t ⦂ ~T }> := by
    sorry

--  ## Type Soundness

--  ### Exercise (2 stars): type_soundness ⭐⭐

--  Put progress and preservation together and show that a well-typed term
--  can *never* reach a stuck state.

def Tm.IsStuck (t : Tm) : Prop := IsNormalForm Step t ∧ ¬ t.IsValue

theorem type_soundness (t t' : Tm) (T : Ty)
    (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) (hm : t ⟶* t') : ¬ t'.IsStuck := by
  intro hst
  obtain ⟨hnf, hnv⟩ := hst
  sorry

--  ## Uniqueness of Types

--  ### Exercise (3 stars): unique_types ⭐⭐⭐

--  Another nice property of the STLC is that types are unique: a given
--  term (in a given context) has at most one type.

-- AI
theorem unique_types (Γ : Context) (e : Tm) (T T' : Ty)
    (h : <{ ~Γ ⊢ ~e ⦂ ~T }>) (h' : <{ ~Γ ⊢ ~e ⦂ ~T' }>) : T = T' := by
  sorry

--  ## Context Invariance (Optional)

--  Another standard technical lemma associated with typed languages is
--  *context invariance*. It states that typing is preserved under
--  "inessential changes" to the context `Γ` — in particular, changes that
--  do not affect any of the free variables of the term. In this section,
--  we establish this property for our system, introducing some other
--  standard terminology on the way.
--
--  First, we need to define the *free variables* in a term — i.e.,
--  variables that are used in the term in positions that are *not* in the
--  scope of an enclosing function abstraction binding a variable of the
--  same name.
--
--  More technically, a variable `x` *appears free in* a term *t* if `t`
--  contains some occurrence of `x` that is not under an abstraction
--  labeled `x`. For example:
--
--  - `y` appears free, but `x` does not, in `λx:T→U. x y`
--  - both `x` and `y` appear free in `(λx:T→U. x y) x`
--  - no variables appear free in `λx:T→U. λy:T. x y`
--
--  We write this `x ∈ᶠ t`, reading the relation as "`x` is one of the free
--  variables of `t`". Formally:

section
set_option hygiene false in
local infix:50 " ∈ᶠ " => AppearsFreeIn

inductive AppearsFreeIn (x : String) : Tm → Prop where
  | var : x ∈ᶠ (Tm.var x)
  | app1 (t₁ t₂ : Tm) (h : x ∈ᶠ t₁) : x ∈ᶠ <{ ~t₁ ~t₂ }>
  | app2 (t₁ t₂ : Tm) (h : x ∈ᶠ t₂) : x ∈ᶠ <{ ~t₁ ~t₂ }>
  | abs (y : String) (T₁ : Ty) (t₁ : Tm) (hne : y ≠ x) (h : x ∈ᶠ t₁) :
      x ∈ᶠ <{ λ ~y : ~T₁ . ~t₁ }>
  | ite1 (t₁ t₂ t₃ : Tm) (h : x ∈ᶠ t₁) : x ∈ᶠ <{ if ~t₁ then ~t₂ else ~t₃ }>
  | ite2 (t₁ t₂ t₃ : Tm) (h : x ∈ᶠ t₂) : x ∈ᶠ <{ if ~t₁ then ~t₂ else ~t₃ }>
  | ite3 (t₁ t₂ t₃ : Tm) (h : x ∈ᶠ t₃) : x ∈ᶠ <{ if ~t₁ then ~t₂ else ~t₃ }>
end

scoped infix:50 " ∈ᶠ " => AppearsFreeIn

--  The *free variables* of a term are just the variables that appear free
--  in it. This gives us another way to define *closed* terms — arguably a
--  better one, since it applies even to ill-typed terms. Indeed, this is
--  the standard definition of the term "closed."

def Tm.Closed (t : Tm) : Prop := ∀ x, ¬ x ∈ᶠ t

--  Conversely, an *open* term is one that may contain free variables.
--  (I.e., every term is an open term; the closed terms are a subset of the
--  open ones. "Open" precisely means "possibly containing free
--  variables.")

--  ### Exercise (1 star): afi ⭐

--  (Officially optional, but strongly recommended!) In the space below,
--  write out the rules of the `∈ᶠ` relation in informal inference-rule
--  notation. (Use whatever notational conventions you like — the point of
--  the exercise is just for you to think a bit about the meaning of each
--  rule.) Although this is a rather low-level, technical definition,
--  understanding it is crucial to understanding substitution and its
--  properties, which are really the crux of the lambda-calculus.

--  Next, we show that if a variable `x` appears free in a term `t`, and if
--  we know `t` is well typed in context `Γ`, then it must be the case that
--  `Γ` assigns a type to `x`.

-- IN PROGRESS
theorem free_in_context (x : String) (t : Tm) (T : Ty) (Γ : Context)
    (ha : x ∈ᶠ t) (hT : <{ ~Γ ⊢ ~t ⦂ ~T }>) : ∃ T', Γ[x] = some T' := by
  sorry

--  *Proof*: We show, by induction on the proof that `x` appears free in
--  `t`, that, for all contexts `Γ`, if `t` is well typed under `Γ`, then
--  `Γ` assigns some type to `x`.
--
--  - If the last rule used is `AppearsFreeIn.var`, then `t = x`, and from
--    the assumption that `t` is well typed under `Γ` we have immediately
--    that `Γ` assigns a type to `x`.
--
--  - If the last rule used is `AppearsFreeIn.app1`, then `t = t₁ t₂` and
--    `x` appears free in `t₁`. Since `t` is well typed under `Γ`, we can
--    see from the typing rules that `t₁` must also be, and the IH then
--    tells us that `Γ` assigns `x` a type.
--
--  - Almost all the other cases are similar: `x` appears free in a subterm
--    of `t`, and since `t` is well typed under `Γ`, we know the subterm of
--    `t` in which `x` appears is well typed under `Γ` as well, and the IH
--    gives us exactly the conclusion we want.
--
--  - The only remaining case is `AppearsFreeIn.abs`. In this case
--    `t = λy:T₁. t₁` and `x` appears free in `t₁`, and we also know that
--    `x` is different from `y`. The difference from the previous cases is
--    that, whereas `t` is well typed under `Γ`, its body `t₁` is well
--    typed under `y ↦ T₁; Γ`, so the IH allows us to conclude that `x` is
--    assigned some type by the extended context `y ↦ T₁; Γ`. To conclude
--    that `Γ` assigns a type to `x`, we appeal to lemma
--    `PartialMap.update_neq`, noting that `x` and `y` are different
--    variables.

--  ### Exercise (2 stars): free_in_context ⭐⭐

--  Complete the following proof.

--  From the `free_in_context` lemma, it immediately follows that any term
--  `t` that is well typed in the empty context is closed (it has no free
--  variables).

--  ### Exercise (2 stars): typable_empty__closed ⭐⭐

theorem typable_empty_closed (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) : t.Closed := by
  sorry

--  Finally, we establish *context invariance*. It is useful in cases when
--  we have a proof of some typing relation `Γ ⊢ t ⦂ T`, and we need to
--  replace `Γ` by a different context `Γ'`. When is it safe to do this?
--  Intuitively, it must at least be the case that `Γ'` assigns the same
--  types as `Γ` to all the variables that appear free in `t`. In fact,
--  this is the only condition that is needed.

-- IN PROGRESS
theorem context_invariance (Γ Γ' : Context) (t : Tm) (T : Ty)
    (hT : <{ ~Γ ⊢ ~t ⦂ ~T }>) (hf : ∀ x, x ∈ᶠ t → Γ[x] = Γ'[x]) :
    <{ ~Γ' ⊢ ~t ⦂ ~T }> := by
  sorry

--  *Proof*: By induction on the derivation of `Γ ⊢ t ⦂ T`.
--
--  - If the last rule in the derivation was `HasType.var`, then `t = x`
--    and `Γ x = T`. By assumption, `Γ' x = T` as well, and hence
--    `Γ' ⊢ t ⦂ T` by `HasType.var`.
--
--  - If the last rule was `HasType.abs`, then `t = λy:T₂. t₁`, with
--    `T = T₂ → T₁` and `y ↦ T₂; Γ ⊢ t₁ ⦂ T₁`. The induction hypothesis
--    states that for any context `Γ''`, if `y ↦ T₂; Γ` and `Γ''` assign
--    the same types to all the free variables in `t₁`, then `t₁` has type
--    `T₁` under `Γ''`. Let `Γ'` be a context which agrees with `Γ` on the
--    free variables in `t`; we must show `Γ' ⊢ λy:T₂. t₁ ⦂ T₂ → T₁`.
--
--    By `HasType.abs`, it suffices to show that `y ↦ T₂; Γ' ⊢ t₁ ⦂ T₁`. By
--    the IH (setting `Γ'' = y ↦ T₂;Γ'`), it suffices to show that
--    `y ↦ T₂;Γ` and `y ↦ T₂;Γ'` agree on all the variables that appear
--    free in `t₁`.
--
--    Any variable occurring free in `t₁` must be either `y` or some other
--    variable. `y ↦ T₂; Γ` and `y ↦ T₂; Γ'` clearly agree on `y`.
--    Otherwise, note that any variable other than `y` that occurs free in
--    `t₁` also occurs free in `t = λy:T₂. t₁`, and by assumption `Γ` and
--    `Γ'` agree on all such variables; hence so do `y ↦ T₂; Γ` and
--    `y ↦ T₂; Γ'`.
--
--  - If the last rule was `HasType.app`, then `t = t₁ t₂`, with
--    `Γ ⊢ t₁ ⦂ T₂ → T` and `Γ ⊢ t₂ ⦂ T₂`. One induction hypothesis states
--    that for all contexts `Γ'`, if `Γ'` agrees with `Γ` on the free
--    variables in `t₁`, then `t₁` has type `T₂ → T` under `Γ'`; there is a
--    similar IH for `t₂`. We must show that `t₁ t₂` also has type `T`
--    under `Γ'`, given the assumption that `Γ'` agrees with `Γ` on all the
--    free variables in `t₁ t₂`. By `HasType.app`, it suffices to show that
--    `t₁` and `t₂` each have the same type under `Γ'` as under `Γ`. But
--    all free variables in `t₁` are also free in `t₁ t₂`, and similarly
--    for `t₂`; hence the desired result follows from the induction
--    hypotheses.

--  ### Exercise (3 stars): context_invariance ⭐⭐⭐

--  Complete the following proof.

--  The context invariance lemma can actually be used in place of the
--  weakening lemma to prove the crucial substitution lemma stated earlier.

--  ## Additional Exercises

--  ### Exercise (1 star): progress_preservation_statement ⭐

--  (Officially optional, but strongly recommended!) Without peeking at
--  their statements above, write down the progress and preservation
--  theorems for the simply typed lambda-calculus (as Lean theorems). You
--  can write `sorry` for the proofs.

--  ### Exercise (2 stars): stlc_variation1 (Manually graded) ⭐⭐

--  Suppose we add a new term `zap` with the following reduction rule
--
--      ---------                  (ST_Zap)
--      t --> zap
--
--  and the following typing rule:
--
--      -------------------           (T_Zap)
--      Γ ⊢ zap ⦂ T
--
--  Which of the following properties of the STLC remain true in the
--  presence of these rules? For each property, write either "remains true"
--  or "becomes false." If a property becomes false, give a counterexample.
--
--  - Determinism of `step`
--
--  - Progress
--
--  - Preservation

--  ### Exercise (2 stars): stlc_variation2 (Manually graded) ⭐⭐

--  Suppose instead that we add a new term `foo` with the following
--  reduction rules:
--
--      -----------------                (ST_Foo1)
--      (\x:A, x) --> foo
--
--        ------------                   (ST_Foo2)
--        foo --> true
--
--  Which of the following properties of the STLC remain true in the
--  presence of this rule? For each one, write either "remains true" or
--  else "becomes false." If a property becomes false, give a
--  counterexample.
--
--  - Determinism of `step`
--
--  - Progress
--
--  - Preservation

--  ### Exercise (2 stars): stlc_variation3 (Manually graded) ⭐⭐

--  Suppose instead that we remove the rule `Step.app1` from the `step`
--  relation. Which of the following properties of the STLC remain true in
--  the presence of this rule? For each one, write either "remains true" or
--  else "becomes false." If a property becomes false, give a
--  counterexample.
--
--  - Determinism of `step`
--
--  - Progress
--
--  - Preservation

--  ### Exercise (2 stars): stlc_variation4 ⭐⭐

--  Suppose instead that we add the following new rule to the reduction
--  relation:
--
--      ----------------------------------        (ST_FunnyIfTrue)
--      (if true then t₁ else t₂) --> true
--
--  Which of the following properties of the STLC remain true in the
--  presence of this rule? For each one, write either "remains true" or
--  else "becomes false." If a property becomes false, give a
--  counterexample.
--
--  - Determinism of `step`
--
--  - Progress
--
--  - Preservation

--  ### Exercise (2 stars): stlc_variation5 ⭐⭐

--  Suppose instead that we add the following new rule to the typing
--  relation:
--
--      Γ ⊢ t₁ ⦂ Bool->Bool->Bool
--          Γ ⊢ t₂ ⦂ Bool
--      ---------------------------------       (T_FunnyApp)
--         Γ ⊢ t₁ t₂ ⦂ Bool
--
--  Which of the following properties of the STLC remain true in the
--  presence of this rule? For each one, write either "remains true" or
--  else "becomes false." If a property becomes false, give a
--  counterexample.
--
--  - Determinism of `step`
--
--  - Progress
--
--  - Preservation

--  ### Exercise (2 stars): stlc_variation6 ⭐⭐

--  Suppose instead that we add the following new rule to the typing
--  relation:
--
--      Γ ⊢ t₁ ⦂ Bool
--      Γ ⊢ t₂ ⦂ Bool
--      ------------------------            (T_FunnyApp')
--      Γ ⊢ t₁ t₂ ⦂ Bool
--
--  Which of the following properties of the STLC remain true in the
--  presence of this rule? For each one, write either "remains true" or
--  else "becomes false." If a property becomes false, give a
--  counterexample.
--
--  - Determinism of `step`
--
--  - Progress
--
--  - Preservation

--  ### Exercise (2 stars): stlc_variation7 ⭐⭐

--  Suppose we add the following new rule to the typing relation of the
--  STLC:
--
--      ---------------------- (T_FunnyAbs)
--      ⊢ \x:Bool,t ⦂ Bool
--
--  Which of the following properties of the STLC remain true in the
--  presence of this rule? For each one, write either "remains true" or
--  else "becomes false." If a property becomes false, give a
--  counterexample.
--
--  - Determinism of `step`
--
--  - Progress
--
--  - Preservation

end Stlc

--  ### Exercise: STLC with Arithmetic

--  To see how the STLC might function as the core of a real programming
--  language, let's extend it with a concrete base type of numbers and some
--  constants and primitive operators.
--
--  The arithmetic we are adding is the arithmetic of the Slang chapter —
--  numeric constants and multiplication — together with the successor,
--  predecessor, and zero-test operations of the Types chapter. What is new
--  is the setting: those operations now live in a language that also has
--  variables, abstraction, and application, so an arithmetic computation
--  can be packaged up as a function and passed around as a value.

namespace StlcArith

open scoped MyGetElem

--  To types, we add a base type of natural numbers (and remove booleans,
--  for brevity).

inductive Ty where
  | arrow (T₁ T₂ : Ty)
  | nat

--  To terms, we add natural number constants, along with successor,
--  predecessor, multiplication, and zero-testing.

inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (T : Ty) (t : Tm)
  | const (n : Nat)
  | succ (t : Tm)
  | pred (t : Tm)
  | mult (t₁ t₂ : Tm)
  | ite0 (c t e : Tm)

--  `StlcArith` is a **different** language from the STLC of this chapter,
--  not an extension of it, so it needs its own concrete syntax. Rather
--  than invent a new one, we reuse the grammars set up in the Stlc chapter
--  — the syntax categories `stlcTy`, `stlcTm`, and `stlcVar` — and give
--  them a new meaning here. Terms and types of this language are therefore
--  written inside the same `<{ … }>` brackets, with the same `~e` escape
--  back to Lean.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: types)
--  The type grammar needs no new productions: `Nat` is a bare identifier,
--  which the template already accepts, and arrows and parentheses are
--  unchanged. Only the `macro_rules` are new, and they differ from the
--  STLC's in just two places — the identifier `Nat` names this language's
--  base type, and the arrow builds this language's `StlcArith.Ty.arrow`.

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
--  Terms do need new productions: a numeral, an infix `*`, and the zero
--  test. Multiplication binds looser than application and tighter than
--  `λ`, so `x * y z` multiplies `x` by the application `y z`; it
--  associates to the right, so `x * y * z` is `x * (y * z)`.
--
--  `succ` and `pred` get no production of their own. Making them keywords
--  would reserve those words globally — and we would then be unable to
--  write `succ` as a case name in a proof, including for Lean's own `Nat`.
--  Instead they are written as though they were functions applied to an
--  argument, `succ t`, and the application rule below recognizes them.
--  `if0` **is** a keyword, since `then` and `else` leave no other option;
--  that is why the constructor above is called `StlcArith.Tm.ite0` rather
--  than `if0`, just as the STLC's conditional is `Stlc.Tm.ite`.

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
--  As in the Stlc chapter, a delaborator runs the grammar backwards, so
--  that goals mentioning these terms and types read in the concrete
--  syntax. The parenthesizers registered there are for the whole syntax
--  category, so they serve this language too and are not repeated.

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

--  In this extended exercise, your job is to finish formalizing the
--  definition and properties of the STLC extended with arithmetic.
--  Specifically:
--
--  Fill in the core definitions for `StlcArith`, by starting with the
--  rules and terms which are the same as the STLC. Then prove the key
--  lemmas and theorems we provide. You will need to define and prove
--  helper lemmas, as before.
--
--  Make sure Lean accepts the whole file before submitting.

--  ### Exercise (5 stars): StlcArith.subst ⭐⭐⭐⭐⭐

--  Substitution is defined exactly as it was for the STLC, with one clause
--  per new constructor.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Why the definition is wrapped in a section)
--  Substitution is written using its own `[x := s] t` notation, which is
--  being defined at the same time, so — as in the Stlc chapter — the rule
--  is first declared `local`, with hygiene off so that the `subst` in its
--  expansion refers to the function being defined, and then declared again
--  for real once the section closes.
--  END DETAILS

section
set_option hygiene false in
local macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

def subst (x : String) (s : Tm) (t : Tm) : Tm := sorry
end

macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: substitution)
--  One more line registers substitutions with the printer, so that a goal
--  mentioning one reads as `[x := s] t` rather than as a `subst`
--  application.

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcArith.subst]
def delabSubst : Delab := whenPPOption getPPNotation do
  match ← delabTmInner with
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
--  END DETAILS

--  You will also want one `@[simp]` simplification lemma per constructor,
--  saying how your `subst` behaves on that constructor, in the style of
--  the Stlc chapter — the substitution lemma below is proved by rewriting
--  with them rather than by unfolding the definition. Two of the
--  constructors need two lemmas apiece, since substitution treats a bound
--  name differently depending on whether it is the name being substituted
--  for.

section
variable (x y : String) (s t t₁ t₂ t₃ : Tm) (T : Ty) (n : Nat)
--  FILL IN HERE
end

--  Next, the values. In the pure STLC, function abstractions were the only
--  values; now the numbers are values too.

inductive Tm.IsValue : Tm → Prop where
--  FILL IN HERE

--  Now the reduction relation. The three rules for application are the
--  STLC's; the rest say how the arithmetic operators evaluate their
--  arguments and what they compute once those arguments are numbers.

section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
--  FILL IN HERE
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

--  An example:

-- AI
theorem Nat_step_example : ∃ t, <{ (λ x : Nat . λ y : Nat . x * y) 3 2 }> ⟶* t := by
  sorry

--  A typing context is a partial map from variables to types, exactly as
--  before.

abbrev Context := PartialMap String Ty

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: contexts and judgments)
--  The context grammar `stlcCtx` is reused as well; only the map it
--  denotes is new, since the types it stores are this language's. As with
--  `subst`, the judgment rule is introduced twice: `local` and
--  hygiene-free while the relation is being declared, then again for real.

open Lean in
/-- The `Context` denoted by a context expression. -/
partial def ctxTerm (G : TSyntax `stlcCtx) : MacroM Term :=
  match G with
  | `(stlcCtx| ∅)   => `((∅ : Context))
  | `(stlcCtx| ~$e) => pure e
  | `(stlcCtx| $x:stlcVar ↦ $T:stlcTy ; $G:stlcCtx) => do
      `(PartialMap.update $(← ctxTerm G) $(← Stlc.varStr x) <{ $T:stlcTy }>)
  | _ => Macro.throwUnsupported

section StlcArith
set_option hygiene false in
local macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $T:stlcTy }>)
--  END DETAILS

--  The typing rules for variables, abstraction, and application are the
--  STLC's. The remaining four are the typing rules for arithmetic
--  expressions.

inductive HasType : Context → Tm → Ty → Prop where
--  FILL IN HERE

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: the judgment, for real)
--  Closing the section retires the hygiene-free rule; the same rule is
--  then declared again, hygienically, for every later use, and a pair of
--  unexpanders prints judgments back in their own notation.

end StlcArith

scoped macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $T:stlcTy }>)

open Lean PrettyPrinter in
/-- Rebuild `stlcCtx` syntax from the term syntax of a `Context`, so that a
context prints as `x ↦ Nat ; Γ` rather than as a chain of map updates. -/
partial def unexpandCtx : Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₚ $T) => do
      unexpandCtx (← `($x →ₚ $T ; ∅))
  | `($x:str →ₚ $T ; $G) => do
      let G' ← unexpandCtx G
      let x' : TSyntax `stlcVar ←
        if Stlc.isPlainName x.getString then
          `(stlcVar| $(mkIdent (Name.mkSimple x.getString)):ident)
        else `(stlcVar| ~$x)
      match T with
      | `(<{ $T':stlcTy }>) => `(stlcCtx| $x':stlcVar ↦ $T' ; $G')
      | _                   => `(stlcCtx| $x':stlcVar ↦ ~($T) ; $G')
  | G => `(stlcCtx| ~($G))

open Lean PrettyPrinter in
@[app_unexpander StlcArith.HasType]
def HasType.unexpand : Unexpander
  | `($_ $G <{ $t:stlcTm }> <{ $T:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ $T }>)
  | `($_ $G <{ $t:stlcTm }> $T) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ ~($T) }>)
  | `($_ $G $t <{ $T:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ $T }>)
  | `($_ $G $t $T) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ ~($T) }>)
  | _ => throw ()
--  END DETAILS

--  An example:

-- AI
theorem Nat_typing_example : <{ ∅ ⊢ (λ x : Nat . λ y : Nat . x * y) 3 2 ⦂ Nat }> :=
  sorry

--  #### The Technical Theorems

--  The next lemmas are proved *exactly* as before.

--  ### Exercise (4 stars): StlcArith.weakening ⭐⭐⭐⭐

-- AI
theorem weakening (Γ Γ' : Context) (t : Tm) (T : Ty)
    (hi : Γ ⊆ Γ') (hT : <{ ~Γ ⊢ ~t ⦂ ~T }>) : <{ ~Γ' ⊢ ~t ⦂ ~T }> := by
  sorry

--  The two helper lemmas that weakening is for are also proved just as
--  they were for the STLC.

-- AI
theorem weakening_empty (Γ : Context) (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    <{ ~Γ ⊢ ~t ⦂ ~T }> :=
  sorry
-- AI
theorem substitution_preserves_typing (Γ : Context) (x : String) (U : Ty)
    (t v : Tm) (T : Ty)
    (hT : <{ ~x ↦ ~U ; ~Γ ⊢ ~t ⦂ ~T }>) (hv : <{ ∅ ⊢ ~v ⦂ ~U }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~T }> := by
  sorry

--  #### Preservation

--  ### Exercise (4 stars): StlcArith.preservation ⭐⭐⭐⭐

--  *Hint*: you will need to define and prove the same helper lemmas we
--  used before.

theorem preservation (t t' : Tm) (T : Ty)
-- AI
    (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) (hs : t ⟶ t') : <{ ∅ ⊢ ~t' ⦂ ~T }> := by
  sorry

--  #### Progress

--  ### Exercise (4 stars): StlcArith.progress ⭐⭐⭐⭐

-- AI
theorem progress (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  sorry

end StlcArith

-- Built on 2026-09-02 16:12 UTC

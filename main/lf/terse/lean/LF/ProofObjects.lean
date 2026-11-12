import LF.IndProp

import SFLCompat

--  # ProofObjects: The Curry-Howard Correspondence

--  This setting is enabled to make some tricky mistakes
--  harder to make.

set_option autoImplicit false

--  "Algorithms are the computational content of proofs."
--  (Robert Harper)

--  Programming and proving in Lean are two sides of the
--  same coin. Proofs manipulate evidence much as programs
--  manipulate data.
--
--  Question: If evidence is data, what are propositions
--  themselves?
--
--  Answer: They are types!

--  Look again at the formal definition of the `Even`
--  property. For illustrative purposes, we've made the
--  implicit argument `{n : Nat}` to `Even.succ_succ`
--  explicit.

namespace EvenProp
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ (n : Nat) (h : Even n) : Even (n + 2)

--  We can pronounce the ":" here as either "has type" or
--  "is a proof of." For example, the second line in the
--  definition of `Even` declares that
--  `(Even.zero : Even 0)`. Instead of "`Even.zero` has type
--  `Even 0`," we can say that "`Even.zero` is a proof of
--  `Even 0`."

--  This pun between types and propositions — between `:` as
--  "has type" and `:` as "is a proof of" or "is evidence
--  for" — is called the *Curry-Howard correspondence*. It
--  proposes a deep connection between the world of logic
--  and the world of computation:
--
--      propositions  ~  types
--      proofs        ~  programs
--
--  See Wadler (2015) for a brief history and modern
--  exposition.

--  Many useful insights follow from this connection. To
--  begin with, it gives us a natural interpretation of the
--  type of the `Even.succ_succ` constructor.
--
--  The type of `Even.succ_succ` says that it is a
--  *function* (better: a data *constructor*) taking two
--  arguments (one number `n` plus evidence for `Even n`)
--  and returning evidence that `n + 2` is even.

#check @Even.succ_succ

--  Output:
--    Even.succ_succ : ∀ (n : Nat), Even n → Even (n + 2)

--  This can be read "`Even.succ_succ` is a constructor that
--  takes two arguments — a number `n` and evidence for the
--  proposition `Even n` — and yields evidence for the
--  proposition `Even (n + 2)`."

--  Now let's look again at an earlier proof involving
--  `Even`.

theorem even_4 : Even 4 := by
  apply Even.succ_succ
  apply Even.succ_succ
  apply Even.zero

--  Just as with ordinary data values and functions, we can
--  use the `#print` command to see the *proof object* that
--  results from this proof script.

#print even_4

--  Output:
--    theorem EvenProp.even_4 : Even 4 :=
--    Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  Indeed, we can also write down this proof object
--  directly, with no need for a proof script at all:

#check (Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
  : Even (2 + 2))

--  Output:
--    Even.succ_succ 2 (Even.succ_succ 0 Even.zero) : Even (2 + 2)

--  Similarly, as we've seen, we can directly apply theorems
--  to arguments in proof scripts:

theorem even_4' : Even 4 := by
  apply Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  ## Proof Scripts

--  When we write a proof using tactics, what we are doing
--  is instructing Lean to build a proof object under the
--  hood. We can see this using the custom command
--  `show_proof`:

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Tactic: show_proof)
section ShowProof
open Lean Elab Tactic Meta

/-- Like `instantiateMVars`, but also substitutes holes
whose assignment Lean delays until they are complete
(e.g., the body under an `intro`). -/
partial def instantiatePartial (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  transform e (pre := fun e => do
    let .mvar m := e.getAppFn | return .continue
    let some d ← getDelayedMVarAssignment? m
      | return .continue
    let v ← instantiatePartial (mkMVar d.mvarIdPending)
    let args := e.getAppArgs
    let n := d.fvars.size
    let v :=
      (v.abstract d.fvars).instantiateRevRange 0 n args
    return .done (mkAppN v args[n:]))

/-- `show_proof tac₁ … tacₙ` runs the tactics in order,
printing the partial proof term (with `?_` for unfilled
holes) before the first tactic and after each one. -/
elab "show_proof" seq:tacticSeq : tactic => do
  let root ← getMainGoal
  let s := seq.raw[0]
  let tacs :=
    if s.getKind == ``Parser.Tactic.tacticSeqBracketed then
      s[1].getSepArgs
    else s[0].getSepArgs
  let render : TacticM Format := do
    let e ← instantiatePartial (mkMVar root)
    withOptions
      (fun o => (o.setBool `pp.mvars false).setBool
        `pp.fieldNotation false)
      (ppExpr e)
  let mut out ← render
  for t in tacs do
    evalTactic t
    let tac ← PrettyPrinter.ppTactic ⟨t⟩
    out := out ++ .line ++ .line ++ f!"after {tac}:" ++
      .nest 2 (.line ++ (← render))
  logInfo m!"{out}"

end ShowProof
--  END DETAILS

theorem even_4'' : Even 4 := by
  show_proof
    apply Even.succ_succ
    apply Even.succ_succ
    apply Even.zero

--  Output:
--    ?_
--
--    after apply Even.succ_succ:
--      Even.succ_succ 2 ?_
--
--    after apply Even.succ_succ:
--      Even.succ_succ 2 (Even.succ_succ 0 ?_)
--
--    after apply Even.zero:
--      Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  Tactic proofs are convenient, but they are not essential
--  in Lean: in principle, we can always just construct the
--  required evidence by hand. Then we can write a proof
--  term directly following a `:=` (instead of writing `by`
--  and then tactics) to introduce a global name for this
--  evidence.

theorem even_4''' : Even 4 :=
  Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  ## Quantifiers, Implications, Functions

--  In Lean's computational universe (where data structures
--  and programs live), there are two sorts of values that
--  have arrows in their types: *constructors* introduced by
--  `inductive`ly defined data types, and *functions*.
--
--  Similarly, in Lean's logical universe (where we carry
--  out proofs), there are two ways of giving evidence for
--  an implication: constructors introduced by `inductive`ly
--  defined propositions, and... functions!

--  For example, consider this statement:

theorem even_plus4 (n : Nat) (h : Even n) :
    Even (n + 4) := by
  apply Even.succ_succ
  apply Even.succ_succ
  apply h

--  What is the proof object corresponding to `even_plus4`?

--  We're looking for an expression whose *type* is
--  `∀ (n : Nat), Even n → Even (n + 4)` — that is, a
--  *function* that takes two arguments (one number and a
--  piece of evidence) and returns a piece of evidence!
--
--  Here it is:

theorem even_plus4' : ∀ (n : Nat), Even n → Even (n + 4) :=
  fun (n : Nat) => fun (h : Even n) =>
    Even.succ_succ (n + 2) (Even.succ_succ n h)

--  Or equivalently:

theorem even_plus4'' (n : Nat) (h : Even n) :
    Even (n + 4) :=
  Even.succ_succ (n + 2) (Even.succ_succ n h)

#check (even_plus4'' : ∀ (n : Nat), Even n → Even (n + 4))

--  ### Dependency, Equivalence, and Proof Irrelevance

--  When we view the proposition being proved by
--  `even_plus4` as a function type, one interesting point
--  becomes apparent: The second argument's type, `Even n`,
--  mentions the *value* of the first argument, `n`.
--
--  While such *dependent types* are not found in most
--  mainstream programming languages, they can be quite
--  useful in programming too, as the flurry of activity in
--  the functional programming community over the past
--  couple of decades (and recently, most notably Lean!)
--  demonstrates. Dependent types sit at the "highest
--  corner" of the Lambda Cube (see the `Stlc` chapter of
--  *Type Systems*): types can depend on *values* in
--  addition to other types.

--  Notice that both implication (`→`) and quantification
--  (`∀`) correspond to functions on evidence. In fact, they
--  are really the same thing: `→` is just a shorthand for a
--  degenerate use of `∀` where there is no dependency,
--  i.e., no need to give a name to the type on the
--  left-hand side of the arrow:
--
--         ∀ (x : Nat), Nat
--      =  ∀ (_ : Nat), Nat
--      =  Nat        → Nat

--   ----------------------------------------

--  _Quiz:_

--  Recall the definition of `Even`:
--
--      inductive Even : Nat → Prop where
--        | zero : Even 0
--        | succ_succ (n : Nat) (h : Even n) : Even (n + 2)
--
--  What is the type of this expression?
--
--      fun (n : Nat) =>
--        fun (h : Even n) =>
--           Even.succ_succ (n + 2) (Even.succ_succ n h)
--
--  (A) `∀ (n : Nat), Even n`
--
--  (B) `∀ (n : Nat), Even (n + 2)`
--
--  (C) `∀ (n : Nat), Even n → Even n`
--
--  (D) `∀ (n : Nat), Even n → Even (n + 2)`
--
--  (E) `∀ (n : Nat), Even n → Even (n + 4)`
--
--  (F) Not typeable

--   ----------------------------------------

section IncrementalProofObjects
set_option warn.sorry false

end IncrementalProofObjects

--  ## Practical Uses of Terms in Proofs

--  In the `Even` examples, we show how to build proofs
--  using terms to illustrate that they are one and they
--  same. But in this particular example, doing so is
--  impractical: the proof terms above are verbose and
--  arguably harder to write and follow than a tactic proof,
--  which is more aligned with most people's style of
--  reasoning. So the question naturally arises- would we
--  ever use terms in *real* Lean proofs? The answer is yes,
--  and we show some examples where such use is both helpful
--  and actively encouraged in real Lean developments.
--
--  Here are some of the places where terms most often
--  appear in Lean proofs:
--  1. `rfl`: The *term* `rfl` is used very often as a full
--     proof instead of `by rfl` (which references the
--     *tactic* `rfl` of the same name) and is even
--     preferred in Lean's Mathlib, which writes its
--     `@[simp]` definitional lemmas this way.

theorem two_add_two : 2 + 2 = 4 := rfl

@[simp]
theorem length_cons {α : Type} (x : α) (xs : List α) :
    (x :: xs).length = xs.length + 1 := rfl

--  2. To succinctly apply an existing lemma, possibly via
--     dot notation on proofs

theorem add_comm_flip (a b : Nat) : b + a = a + b := Nat.add_comm b a
theorem le_chain {a b c : Nat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Nat.le_trans h₁ h₂

--  3. Within anonymous constructors and projections for
--     `And` (`∧`), `Iff` (`↔`), and `Exists` (`∃`)

theorem and_swap {P Q : Prop} (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩
theorem iff_swap {P Q : Prop} (h : P ↔ Q) : Q ↔ P := ⟨h.2, h.1⟩
theorem exists_double : ∃ n, n + n = 4 := ⟨2, rfl⟩

--  4. `fun` for implications (as in `even_plus4'`)

theorem imp_trans {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) :
    P → R :=
  fun hp => hqr (hpq hp)

--  5. Proof fields of structures/instances (as in
--     Typeclasses' Monoid laws)

structure PosNat where
  val : Nat
  pos : 0 < val
def three : PosNat where
  val := 3
  pos := Nat.succ_pos 2

--  Using terms in proofs can be more succinct and more
--  useful than writing out tactics. Try out using terms
--  like `rfl` directly in your proofs in this book and see
--  what you discover.

namespace Props

--   ----------------------------------------

--  _Quiz:_

--   ----------------------------------------

--  _Quiz:_

--   ----------------------------------------

--  _Quiz:_

--   ----------------------------------------

--  To destruct existentials in a proof term we simply use
--  match:

theorem dist_exists_or_term (α : Type) (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) :=
  fun h => match h with
           | Exists.intro x hx =>
               match hx with
               | Or.inl hpx => Or.inl (Exists.intro x hpx)
               | Or.inr hqx => Or.inr (Exists.intro x hqx)

end Props

namespace EqualityPlayground

--   ----------------------------------------

--  _Quiz:_

--   ----------------------------------------

end EqualityPlayground

end EvenProp

-- Source revision: f784fe9, committed 2026-11-12 01:26 UTC

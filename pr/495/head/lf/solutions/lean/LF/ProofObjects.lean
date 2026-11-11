import LF.IndProp

import SFLCompat

--  # ProofObjects: The Curry-Howard Correspondence

--  This setting is enabled to make some tricky mistakes harder to make.

set_option autoImplicit false

--  "Algorithms are the computational content of proofs." (Robert Harper)

--  We have seen that Lean has mechanisms both for *programming*, using
--  inductive data types like `Nat` or `List` and functions over these
--  types, and for *proving* properties of these programs, using inductive
--  propositions (like `Even`), implication, universal quantification, and
--  the like. So far, we have mostly treated these mechanisms as if they
--  were quite separate, and for many purposes this is a good way to think.
--  But we have also seen hints that Lean's programming and proving
--  facilities are closely related. For example, the keyword `inductive` is
--  used to declare both data types and propositions, and `→` is used both
--  to describe the type of functions on data and logical implication. This
--  is not just a syntactic accident! In fact, programs and proofs in Lean
--  are almost the same thing. In this chapter we will study this
--  connection in more detail.
--
--  We have already seen the fundamental idea: provability in Lean is
--  always witnessed by *evidence*. When we construct the proof of a basic
--  proposition, we are actually building a tree of evidence, which can be
--  thought of as a concrete data structure.
--
--  If the proposition is an implication like `A → B`, then its proof is an
--  evidence *transformer*: a recipe for converting evidence for A into
--  evidence for B. So at a fundamental level, proofs are simply programs
--  that manipulate evidence.
--
--  Question: If evidence is data, what are propositions themselves?
--
--  Answer: They are types!
--
--  Look again at the formal definition of the `Even` property. For
--  illustrative purposes, we've made the implicit argument `{n : Nat}` to
--  `Even.succ_succ` explicit.

namespace EvenProp
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ (n : Nat) (h : Even n) : Even (n + 2)

--  We can pronounce the ":" here as either "has type" or "is a proof of."
--  For example, the second line in the definition of `Even` declares that
--  `(Even.zero : Even 0)`. Instead of "`Even.zero` has type `Even 0`," we
--  can say that "`Even.zero` is a proof of `Even 0`."
--
--  This pun between types and propositions — between `:` as "has type" and
--  `:` as "is a proof of" or "is evidence for" — is called the
--  *Curry-Howard correspondence*. It proposes a deep connection between
--  the world of logic and the world of computation:
--
--      propositions  ~  types
--      proofs        ~  programs
--
--  See Wadler (2015) for a brief history and modern exposition.
--
--  Many useful insights follow from this connection. To begin with, it
--  gives us a natural interpretation of the type of the `Even.succ_succ`
--  constructor.
--
--  The type of `Even.succ_succ` says that it is a *function* (better: a
--  data *constructor*) taking two arguments (one number `n` plus evidence
--  for `Even n`) and returning evidence that `n + 2` is even.

#check @Even.succ_succ

--  Output:
--    Even.succ_succ : ∀ (n : Nat), Even n → Even (n + 2)

--  This can be read "`Even.succ_succ` is a constructor that takes two
--  arguments — a number `n` and evidence for the proposition `Even n` —
--  and yields evidence for the proposition `Even (n + 2)`."
--
--  Now let's look again at an earlier proof involving `Even`.

theorem even_4 : Even 4 := by
  apply Even.succ_succ
  apply Even.succ_succ
  apply Even.zero

--  Just as with ordinary data values and functions, we can use the
--  `#print` command to see the *proof object* that results from this proof
--  script.

#print even_4

--  Output:
--    theorem EvenProp.even_4 : Even 4 :=
--    Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  Indeed, we can also write down this proof object directly, with no need
--  for a proof script at all:

#check (Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
  : Even (2 + 2))

--  Output:
--    Even.succ_succ 2 (Even.succ_succ 0 Even.zero) : Even (2 + 2)

--  The expression `Even.succ_succ 2 (Even.succ_succ 0 Even.zero)`
--  instantiates the parameterized constructor `Even.succ_succ` with the
--  specific arguments `2` and `0` plus the corresponding proof objects for
--  its premises `Even 2` and `Even 0`. Alternatively, we can think of
--  `Even.succ_succ` as a primitive "evidence constructor" that, when
--  applied to a particular number, wants to be further applied to evidence
--  that this number is even; its type,
--
--      ∀ (n : Nat), Even n → Even (n + 2)
--
--  expresses this functionality, in the same way that the polymorphic type
--  `{α : Type} → List α` expresses the fact that the constructor
--  `List.nil` can be thought of as a function from types to empty lists
--  with elements of that type.
--
--  The fact that the some arguments are implicit, like `{α}` of `List` and
--  `{n}` of the real `Even.succ_succ`, actually doesn't make a difference
--  at all: `List` is still taking one argument, and `Even.succ_succ` is
--  still taking two. Implicit arguments are just a usability feature that
--  tells Lean to figure some arguments out when we apply a definition
--  (like `Even.succ_succ`) to an explicit argument (like a proof of
--  `Even n`). In this case, since `Even n` contains `n`, we don't need to
--  pass `n` in to begin with, and can mark it as implicit with the curly
--  braces as `{n}`.
--
--  We saw in the Logic chapter that we can use function application syntax
--  to instantiate universally quantified variables in lemmas, as well as
--  to supply evidence for assumptions that these lemmas impose. For
--  instance:

theorem even_4' : Even 4 := by
  apply Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  ## Proof Scripts

--  The *proof objects* we've been discussing lie at the core of how Lean
--  operates. When Lean is following a proof script, what is happening
--  internally is that it is gradually constructing a proof object — a term
--  whose type is the proposition being proved. All the tactics following
--  `by` tell it how to build up a term of the required type. To see this
--  process in action, we provide a `show_proof` command to display the
--  current state of the proof tree at various points in the following
--  tactic proof.
--
--  `show_proof` wraps a tactic script and prints the partial proof term —
--  a term with *holes* where the remaining proof obligations are — before
--  and after each step. A term's holes are shown as `?_`.

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

--  At any given moment, Lean has constructed a term with a "hole"
--  (indicated by `?_` here, and so on), and it knows what type of evidence
--  is needed to fill this hole.
--
--  Each hole corresponds to a subgoal, and the proof is finished when
--  there are no more subgoals. At this point, the evidence we've built is
--  stored in the global context (i.e. Lean's environment that it uses for
--  type-checking) under the name given in the `theorem` command.
--
--  Tactic proofs are convenient, but they are not essential in Lean: in
--  principle, we can always just construct the required evidence by hand.
--  Then we can write a proof term directly following a `:=` (instead of
--  writing `by` and then tactics) to introduce a global name for this
--  evidence.

theorem even_4''' : Even 4 :=
  Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  All these different ways of building the proof lead to exactly the same
--  evidence being saved in the global environment.

#print even_4
#print even_4'
#print even_4''
#print even_4'''

--  Output:
--    theorem EvenProp.even_4 : Even 4 :=
--    Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  Output:
--    theorem EvenProp.even_4' : Even 4 :=
--    Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  Output:
--    theorem EvenProp.even_4'' : Even 4 :=
--    Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  Output:
--    theorem EvenProp.even_4''' : Even 4 :=
--    Even.succ_succ 2 (Even.succ_succ 0 Even.zero)

--  ### Exercise (2 stars): eight_is_even ⭐⭐

--  Give a tactic proof and a proof object showing that `Even 8`.

theorem even_8_tactics : Even 8 := by
  apply Even.succ_succ
  apply Even.succ_succ
  apply even_4

theorem even_8_term : Even 8 :=
  (Even.succ_succ 6 (Even.succ_succ 4 even_4))

--  ## Quantifiers, Implications, Functions

--  In Lean's computational universe (where data structures and programs
--  live), there are two sorts of values that have arrows in their types:
--  *constructors* introduced by `inductive`ly defined data types, and
--  *functions*.
--
--  Similarly, in Lean's logical universe (where we carry out proofs),
--  there are two ways of giving evidence for an implication: constructors
--  introduced by `inductive`ly defined propositions, and... functions!
--
--  For example, consider this statement:

theorem even_plus4 (n : Nat) (h : Even n) :
    Even (n + 4) := by
  apply Even.succ_succ
  apply Even.succ_succ
  apply h

--  What is the proof object corresponding to `even_plus4`?
--
--  We're looking for an expression whose *type* is
--  `∀ (n : Nat), Even n → Even (n + 4)` — that is, a *function* that takes
--  two arguments (one number and a piece of evidence) and returns a piece
--  of evidence!
--
--  Here it is:

theorem even_plus4' : ∀ (n : Nat), Even n → Even (n + 4) :=
  fun (n : Nat) => fun (h : Even n) =>
    Even.succ_succ (n + 2) (Even.succ_succ n h)

--  Recall that `fun n => blah` means "the function that, given `n`, yields
--  `blah`," and that Lean treats `n + 4` and `n + 2 + 2` as synonyms.
--  Another equivalent way to write this definition is:

theorem even_plus4'' (n : Nat) (h : Even n) :
    Even (n + 4) :=
  Even.succ_succ (n + 2) (Even.succ_succ n h)

#check (even_plus4'' : ∀ (n : Nat), Even n → Even (n + 4))

--  ### Dependency, Equivalence, and Proof Irrelevance

--  When we view the proposition being proved by `even_plus4` as a function
--  type, one interesting point becomes apparent: The second argument's
--  type, `Even n`, mentions the *value* of the first argument, `n`.
--
--  While such *dependent types* are not found in most mainstream
--  programming languages, they can be quite useful in programming too, as
--  the flurry of activity in the functional programming community over the
--  past couple of decades (and recently, most notably Lean!) demonstrates.
--  Dependent types sit at the "highest corner" of the Lambda Cube (see the
--  `Stlc` chapter of *Type Systems*): types can depend on *values* in
--  addition to other types.
--
--  Notice that both implication (`→`) and quantification (`∀`) correspond
--  to functions on evidence. In fact, they are really the same thing: `→`
--  is just a shorthand for a degenerate use of `∀` where there is no
--  dependency, i.e., no need to give a name to the type on the left-hand
--  side of the arrow:
--
--         ∀ (x : Nat), Nat
--      =  ∀ (_ : Nat), Nat
--      =  Nat        → Nat
--
--  For example, consider this proposition:

def even_plus2 : Prop :=
  ∀ (n : Nat), ∀ (E : Even n), Even (n + 2)

--  A proof term inhabiting this proposition would be a function with two
--  arguments: a number `n` and some evidence `E` that `n` is even. But the
--  name `E` for this evidence is not used in the rest of the statement of
--  `even_plus2`, so it's a bit silly to bother making up a name for it. We
--  could write it like this instead, using the dummy identifier `_` in
--  place of a real name:

def even_plus2' : Prop :=
  ∀ (n : Nat), ∀ (_ : Even n), Even (n + 2)

--  Or, equivalently, we can write it in a different, familiar way:

def even_plus2'' : Prop :=
  ∀ (n : Nat), Even n → Even (n + 2)

--  In general, "`P → Q`" is just syntactic sugar for "`∀ (_ : P), Q`".
--
--  When we write theorem statements in Lean, we often *will* name the
--  quantified evidence with a name often beginning with `h`:

theorem even_plus2_thm :
  ∀ (n : Nat) (heven : Even n), Even (n + 2) := by
    intro n h; constructor; assumption

--  And we will also put the names before the `:`, which saves needing to
--  use `intro`:

theorem even_plus2_thm' (n : Nat) (heven : Even n) :
    Even (n + 2) := by
    constructor; assumption

--  *All* of these theorem statements are equivalent! When we write `def`,
--  we are just writing down the statement — the type. When we write
--  `theorem`, we are stating the type and then providing a witness after
--  the `:=` (either with `by` and tactics or directly with a term). We can
--  even show the two definitions are equivalent in Lean itself:

theorem even_plus2_defs_same :
    even_plus2 = even_plus2'' := by rfl

--  Remember that theorem statements are just types, so `rfl` here is just
--  comparing two types.
--
--  What about the two theorems? Here, we are asking if two *proofs* —
--  which we now know are both *functions* — are equal. Then, do we need to
--  use `funext`?

theorem even_plus2_theorems_same :
    even_plus2_thm = even_plus2_thm' := by rfl

--  Surprisingly, we don't. This is because Lean has a special feature
--  called *definitional proof irrelevance*. It says that any two proofs of
--  the same proposition are definitionally equal. So we could write the
--  same proof again however we wanted— with different tactics, using terms
--  instead of tactics, etc.— and we would still have "the same theorem."

theorem even_plus2_thm'' (n : Nat) (heven : Even n) :
    Even (n + 2) := by
    exact Even.succ_succ n heven

theorem even_plus2_theorems_still_same :
  even_plus2_thm = even_plus2_thm'' := by rfl

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

--  ## Programming with Tactics

--  If we can build proofs by giving explicit terms rather than executing
--  tactic scripts, you may wonder whether we can build *programs* using
--  tactics rather than by writing down explicit terms.
--
--  Naturally, the answer is yes!

def add2 : Nat → Nat := by
  show_proof
    intro n
    apply Nat.succ
    apply Nat.succ
    exact n

--  Output:
--    ?_
--
--    after intro n:
--      fun n => ?_
--
--    after apply Nat.succ:
--      fun n => Nat.succ ?_
--
--    after apply Nat.succ:
--      fun n => Nat.succ (Nat.succ ?_)
--
--    after exact n:
--      fun n => Nat.succ (Nat.succ n)

#print add2

--  Output:
--    def EvenProp.add2 : Nat → Nat :=
--    fun n => n.succ.succ

#eval add2 2

--  Output:
--    4

--  Notice that we followed `def … :=` with `by` rather than with a term.
--  This tells Lean to enter *proof scripting mode* to build an object of
--  type `Nat → Nat`.
--
--  This feature is mainly useful for writing functions with dependent
--  types, which we won't explore much further in this book. But it does
--  illustrate the uniformity and orthogonality of the basic ideas in Lean.

--  Note to developers (Michael Hicks @mwhicks1):
--      This statement is a bit mysterious. Why are dependent types
--      special? I think the answer is that they allow for more explicit
--      specifications -- normal types are just not strong enough to say
--      much about a function you might ask tactics to synthesize. There
--      are lots of Nat -> Nat functions, but far fewer that ... insert
--      dependent type here.

--  Since `def` and `theorem` can both use terms or `by`, is there any
--  difference between the two? There is one: a `theorem` must have a
--  `Prop` type.

sf_expect_failure_in
  theorem add2_with_theorem_wrong : Nat → Nat := by
      apply Nat.succ

--  Output:
--    type of theorem `EvenProp.add2_with_theorem_wrong` is not a proposition
--      Nat → Nat

--  ## Building Proof Objects Incrementally (Optional)

section IncrementalProofObjects
set_option warn.sorry false

--  As you probably noticed while solving the exercises earlier in the
--  chapter, constructing proof objects is more involved than constructing
--  the corresponding tactic proofs. Fortunately, there's a simple trick to
--  help in the construction: we can use the *term* `sorry` as placeholder
--  of any type we like.
--
--  As an example, let's walk through the process of constructing a proof
--  object demonstrating the evenness of `8`.

theorem even_8_atmpt_1 : Even 8 := sorry

--  Maybe we can use `Even.succ_succ` to construct a term of type `Even 8`?
--  Recall that `Even.succ_succ` is of type
--
--      ∀ (n : Nat), Even n → Even (n + 2)
--
--  If we can demonstrate that `6` is even, we should be done.

theorem even_8_atmpt_2 : Even 8 := Even.succ_succ 6 sorry

--  In the attempt above, we've omitted the proofs that `6` is even, but it
--  can easily be constructed following the same procedure:

theorem even_8_atmpt_3 : Even 8 :=
  Even.succ_succ 6 (Even.succ_succ 4 sorry)

theorem even_8_atmpt_4 : Even 8 :=
  Even.succ_succ 6 (Even.succ_succ 4
    (Even.succ_succ 2 sorry))

theorem even_8_atmpt_5 : Even 8 :=
  Even.succ_succ 6 (Even.succ_succ 4
    (Even.succ_succ 2 (Even.succ_succ 0 Even.zero)))

--  To recap, we've been guided by an informal proof that we have in our
--  minds, and we check the high level details before completing the
--  intricacies of the proof. The `sorry` term allows us to do this.

end IncrementalProofObjects

--  ## Practical Uses of Terms in Proofs

--  In the `Even` examples, we show how to build proofs using terms to
--  illustrate that they are one and they same. But in this particular
--  example, doing so is impractical: the proof terms above are verbose and
--  arguably harder to write and follow than a tactic proof, which is more
--  aligned with most people's style of reasoning. So the question
--  naturally arises- would we ever use terms in *real* Lean proofs? The
--  answer is yes, and we show some examples where such use is both helpful
--  and actively encouraged in real Lean developments.
--
--  Here are some of the places where terms most often appear in Lean
--  proofs:
--  1. `rfl`: The *term* `rfl` is used very often as a full proof instead
--     of `by rfl` (which references the *tactic* `rfl` of the same name)
--     and is even preferred in Lean's Mathlib, which writes its `@[simp]`
--     definitional lemmas this way.

theorem two_add_two : 2 + 2 = 4 := rfl

@[simp]
theorem length_cons {α : Type} (x : α) (xs : List α) :
    (x :: xs).length = xs.length + 1 := rfl

--  2. To succinctly apply an existing lemma, possibly via dot notation on
--     proofs

theorem add_comm_flip (a b : Nat) : b + a = a + b := Nat.add_comm b a
theorem le_chain {a b c : Nat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Nat.le_trans h₁ h₂

--  3. Within anonymous constructors and projections for `And` (`∧`), `Iff`
--     (`↔`), and `Exists` (`∃`)

theorem and_swap {P Q : Prop} (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩
theorem iff_swap {P Q : Prop} (h : P ↔ Q) : Q ↔ P := ⟨h.2, h.1⟩
theorem exists_double : ∃ n, n + n = 4 := ⟨2, rfl⟩

--  4. `fun` for implications (as in `even_plus4'`)

theorem imp_trans {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) :
    P → R :=
  fun hp => hqr (hpq hp)

--  5. Proof fields of structures/instances (as in Typeclasses' Monoid
--     laws)

structure PosNat where
  val : Nat
  pos : 0 < val
def three : PosNat where
  val := 3
  pos := Nat.succ_pos 2

--  Using terms in proofs can be more succinct and more useful than writing
--  out tactics. Try out using terms like `rfl` directly in your proofs in
--  this book and see what you discover.

--  ## Logical Connectives as Inductive Types

--  We have already seen how tactics are not "special" in Lean: they are
--  just manipulators of terms. Recall that Lean's logical connectives are
--  also not "special:" only universal quantification (with implication as
--  a special case) is built into Lean; all the others are defined
--  inductively. Now that we know more about the relationship between terms
--  and tactics, we can delve further into more advanced ways to work with
--  logical connectives. Let's see how.

namespace Props

--  ### Conjunction

--  To prove that `P ∧ Q` holds, we must present evidence for both `P` and
--  `Q`. Thus, it makes sense to define a proof object for `P ∧ Q` to
--  consist of a pair of two proofs: one for `P` and another one for `Q`.
--  This leads to the following definition.

namespace AndPlayground

structure And (P Q : Prop) : Prop where
  intro ::
  left : P
  right : Q

--  Now that we have pulled back the covers a bit further, we can reveal
--  another fact: a `structure` is just an inductive type with one
--  constructor and whose fields have names. By default, the constructor is
--  called `mk`, which we can rename to `<name>` using `<name> ::`, as in
--  the example.
--
--  We can also see that this definition of `And` matches core `And`
--  exactly: a `structure` with constructor `intro` and fields
--  `left`/`right` (except that core uses `a` and `b` instead of `P` `Q`).

#print _root_.And

--  Output:
--    structure _root_.And (a b : Prop) : Prop
--    number of parameters: 2
--    fields:
--      _root_.And.left : a
--      _root_.And.right : b
--    constructor:
--      _root_.And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

--  Notice the similarity with the definition of the `MyProd` type, given
--  in chapter Poly; the only difference is that `MyProd` takes `Type`
--  arguments, whereas `And` takes `Prop` arguments.

#print MyProd

--  Output:
--    structure MyProd (α β : Type) : Type
--    number of parameters: 2
--    fields:
--      MyProd.fst : α
--      MyProd.snd : β
--    constructor:
--      MyProd.mk {α β : Type} (fst : α) (snd : β) : MyProd α β

--  This similarity should clarify why `cases`, `obtain` `⟨hp, hq⟩`, and
--  `intro` `⟨hp, hq⟩` patterns can be used on a conjunctive hypothesis.
--  Case analysis allows us to consider all possible ways in which `P ∧ Q`
--  was proved — here just one (the `And.intro` constructor).

theorem proj1' (P Q : Prop) (hpq : And P Q) : P := by
    cases hpq with
    | intro hp _ => exact hp

theorem and_comm (P Q : Prop) : And P Q ↔ And Q P := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := h
    constructor
    · exact hq
    · exact hp
  · intro h
    obtain ⟨hq, hp⟩ := h
    constructor
    · exact hp
    · exact hq

end AndPlayground

--  This shows why the inductive (structure) definition of `And` can be
--  manipulated by tactics as we've been doing. We can also use it to build
--  proofs directly, using pattern-matching. For instance:

theorem proj1'' (P Q : Prop) (hpq : P ∧ Q) : P :=
  match hpq with
  | And.intro hp _ => hp

theorem and_comm'_aux (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  match h with
  | And.intro hp hq => And.intro hq hp

theorem and_comm' (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=
  Iff.intro (and_comm'_aux P Q) (and_comm'_aux Q P)

--  Here, `Iff.intro` is doing exactly the same thing as `And.intro`; it
--  builds the `Iff` `structure` with its two arguments.

--  ### Exercise (2 stars): conj_fact ⭐⭐

--  Construct a proof object for the following proposition.

theorem conj_fact : ∀ (P Q R : Prop),
    P ∧ Q → Q ∧ R → P ∧ R :=
  (fun _ _ _ hpq hqr =>
    match hpq, hqr with
    | And.intro hp _, And.intro _ hr => And.intro hp hr)

--  (End of exercise)

--   ----------------------------------------

--  _Quiz:_

--  What is the type of this expression?
--
--      fun P Q R (h1 : And P Q) (h2 : And Q R) =>
--        match h1, h2 with
--        | And.intro hp _, And.intro _ hr => And.intro hp hr
--
--  (A) `∀ (P Q R : Prop), P ∧ Q → Q ∧ R → P ∧ R`
--
--  (B) `∀ (P Q R : Prop), Q ∧ P → R ∧ Q → P ∧ R`
--
--  (C) `∀ (P Q R : Prop), P ∧ R`
--
--  (D) `∀ (P Q R : Prop), P ∨ Q → Q ∨ R → P ∨ R`
--
--  (E) Not typeable

--   ----------------------------------------

--  ### Disjunction

--  The inductive definition of disjunction uses two constructors, one for
--  each side of the disjunction:

namespace OrPlayground

inductive Or (P Q : Prop) : Prop where
  | inl : P → Or P Q
  | inr : Q → Or P Q

--  This declaration explains the behavior of the `cases` tactic on a
--  disjunctive hypothesis, since the generated subgoals match the shape of
--  the `Or.inl` and `Or.inr` constructors.
--
--  Once again, we can also directly write proof objects for theorems
--  involving `Or`, without resorting to tactics.

theorem inj_l : ∀ (P Q : Prop), P → Or P Q :=
  fun _ _ hp => Or.inl hp

theorem inj_l' (P Q : Prop) (hp : P) : Or P Q := by
  show_proof
    left
    exact hp

--  Output:
--    ?_
--
--    after left:
--      Or.inl ?_
--
--    after exact hp:
--      Or.inl hp

theorem or_elim : ∀ (P Q R : Prop),
    Or P Q → (P → R) → (Q → R) → R :=
  fun _ _ _ hpq hpr hqr =>
    match hpq with
    | Or.inl hp => hpr hp
    | Or.inr hq => hqr hq

theorem or_elim' (P Q R : Prop) (hpq : Or P Q)
    (hpr : P → R) (hqr : Q → R) : R := by
  cases hpq with
  | inl hp =>
    apply hpr
    exact hp
  | inr hq =>
    apply hqr
    exact hq

end OrPlayground

--  ### Exercise (2 stars): or_commut' ⭐⭐

--  Construct a proof object for the following proposition.

theorem or_commut' : ∀ (P Q : Prop), P ∨ Q → Q ∨ P :=
  (fun (P Q : Prop) (h : P ∨ Q) =>
    match h with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq)

--  (End of exercise)

--   ----------------------------------------

--  _Quiz:_

--  What is the type of this expression?
--
--      fun P Q h =>
--        match h with
--        | Or.inl hp => @Or.inr Q P hp
--        | Or.inr hq => @Or.inl Q P hq
--
--  (A) `∀ P Q H, Q ∨ P ∨ H`
--
--  (B) `∀ (P Q : Prop), P ∨ Q → P ∨ Q`
--
--  (C) `∀ P Q H, P ∨ Q → Q ∨ P → H`
--
--  (D) `∀ (P Q : Prop), P ∨ Q → Q ∨ P`
--
--  (E) Not typeable

--   ----------------------------------------

--  ### Existential Quantification

--  To give evidence for an existential quantifier, we package a witness
--  `x` together with a proof that `x` satisfies the property `P`:

namespace ExistsPlayground

inductive Exists {α : Type} (P : α → Prop) : Prop where
  | intro : ∀ (w : α), P w → Exists P

end ExistsPlayground

--  This probably needs a little unpacking. The core definition is for a
--  type former `Exists` that can be used to build propositions of the form
--  `Exists P`, where `P` itself is a *function* from witness values in the
--  type `α` to propositions. The `Exists.intro` constructor then offers a
--  way of constructing evidence for `Exists p`, given a witness `w` and a
--  proof of `P w`.
--
--  The notation in the standard library is a slight extension of the
--  above, enabling syntactic forms such as `∃ x y, P x y`. The standard
--  library's `Exists` also takes `P` implicitly.
--
--  The more familiar form `∃ x, Even x` desugars to an expression
--  involving `Exists`:

#check (Exists (fun n => Even n) : Prop)

--  Output:
--    ∃ n, Even n : Prop

--  Here's how to define an explicit proof object involving `Exists`:

theorem some_nat_is_even : ∃ n, Even n :=
  Exists.intro 4
    (Even.succ_succ 2 (Even.succ_succ 0 Even.zero))

--   ----------------------------------------

--  _Quiz:_

--  Which of the following propositions is proved by providing an explicit
--  witness `w` using `exists w`?
--
--  (A) `∀ (x : Nat), (∃ n, x = n + 1) → x ≠ 0`
--
--  (B) `∀ (x : Nat), x ≠ 0 → (∃ n, x = n + 1)`
--
--  (C) `∀ (x : Nat), x = 0 → ¬(∃ n, x = n + 1)`
--
--  (D) `∀ (x : Nat), x = 4 → x ≠ 0`
--
--  (E) none of the above

--   ----------------------------------------

--  ### Exercise (2 stars): ex_even_Sn ⭐⭐

--  Construct a proof object for the following proposition.

theorem ex_even_Sn : Exists (fun n => Even (n + 1)) :=
  (Exists.intro 1 (Even.succ_succ 0 Even.zero))

--  (End of exercise)

--  To destruct existentials in a proof term we simply use match:

theorem dist_exists_or_term (α : Type) (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) :=
  fun h => match h with
           | Exists.intro x hx =>
               match hx with
               | Or.inl hpx => Or.inl (Exists.intro x hpx)
               | Or.inr hqx => Or.inr (Exists.intro x hqx)

--  ### Exercise (2 stars): ex_match ⭐⭐

--  Construct a proof object for the following proposition:

theorem ex_match : ∀ (A : Type) (P Q : A → Prop),
    (∀ (x : A), P x → Q x) →
    (∃ x, P x) → (∃ x, Q x) :=
  (fun _ _ _ hpq hp =>
    match hp with
    | Exists.intro x hpx => Exists.intro x (hpq x hpx))

--  ### `True` and `False`

--  The inductive definition of the `True` proposition is simple:

inductive True : Prop where
  | intro : True

--  It has one constructor: there is one definitional way to build `True`.
--  (But there are lots of ways to state and prove true things!)

--  ### Exercise (1 star): p_implies_true ⭐

--  Construct a proof object for the following proposition.

theorem p_implies_true : ∀ (P : Prop), P → True :=
  (fun _ _ => True.intro)

--  (End of exercise)

--  `False` is equally simple — indeed, so simple it may look syntactically
--  wrong at first glance!

inductive False : Prop

--  That is, `False` is an inductive type with *no* constructors — i.e., no
--  way to build evidence for it. For example, there is no way to complete
--  the following definition such that it succeeds.

sf_expect_failure_in
  theorem contra : False :=
    True.intro

--  But it is possible to destruct `False` by pattern matching. There can
--  be no patterns that match it, since it has no constructors. To handle
--  this, Lean uses the `nomatch` construct.

theorem false_implies_zero_eq_one : False → 0 = 1 :=
  fun contra => nomatch contra

--  Since there are no branches to evaluate, the `nomatch` expression can
--  be given any type we want, including `0 = 1`. Fortunately, it's
--  impossible to ever cause the `nomatch` to be evaluated, because we can
--  never construct a value of type `False` to pass to the function.

--  ### Exercise (1 star): ex_falso_quodlibet' ⭐

--  Construct a proof object for the following proposition.

theorem ex_falso_quodlibet' : ∀ (P : Prop), False → P :=
  (fun _ contra => nomatch contra)

--  (End of exercise)

end Props

--  ## Equality

namespace EqualityPlayground

--  Even Lean's equality relation is not built in. We can define it
--  ourselves:

inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀ (x : α), Eq x x

scoped infix:50 " =' " => Eq

--  The way to think about this definition (which mirrors the standard
--  library's) is that, given a set `α`, it defines a *family* of
--  propositions "`x` is equal to `y`," parameterized by `x` and indexed by
--  `y` from `α`. There is just one way of constructing evidence for
--  members of this family: applying the constructor `Eq.refl` to a type
--  `α` and a single value `x : α`, which yields evidence that `x` is equal
--  to `x`.
--
--  Other types of the form `Eq x y` where `x` and `y` are not the same are
--  thus uninhabited.
--
--  We can use `Eq.refl` to construct evidence that, for example, `2 = 2`.
--  Can we also use it to construct evidence that `1 + 1 = 2`? Yes, we can.
--  Indeed, it is the very same piece of evidence!
--
--  The reason is that Lean treats as "the same" any two terms that are
--  *convertible* according to a simple set of computation rules.
--
--  These rules, which are similar to those used by `#eval`, include
--  evaluation of function application, inlining of definitions, and
--  simplification of `match`es.
--
--  Lean terms are "the same" if they are *convertible* according to a
--  simple set of computation rules: evaluation of function applications,
--  inlining of definitions, and simplification of `match`es.

theorem four : 2 + 2 =' 1 + 3 := by
  apply Eq.refl

--  The `rfl` tactic that we have used to prove equalities of the form
--  `x = y` up to now is essentially just shorthand for `apply Eq.refl`.
--
--  In tactic-based proofs of equality, the conversion rules are normally
--  hidden in uses of `simp` (either explicit or implicit in other tactics
--  such as `rfl`).
--
--  But you can see them directly at work in the following explicit proof
--  objects:

theorem four' : 2 + 2 =' 1 + 3 :=
  Eq.refl 4

theorem singleton : ∀ (α : Type) (x : α),
    [] ++ [x] =' x :: [] :=
  fun (α : Type) (x : α) => Eq.refl [x]

--  We can also pattern-match on an equality proof:

theorem eq_add : ∀ (n1 n2 : Nat),
    n1 =' n2 → (n1 + 1) =' (n2 + 1) :=
  fun n1 n2 heq =>
    match heq with
    | Eq.refl _ => Eq.refl (n1 + 1)

--  By pattern-matching against `n1 =' n2`, we replace `n2` with `n1` in
--  the type we have to produce, so instead of `(n1 + 1) =' (n2 + 1)`, we
--  now have to produce something of type `(n1 + 1) =' (n1 + 1)`, which we
--  establish by `Eq.refl (n1 + 1)`.
--
--  A tactic-based proof runs into some difficulties if we try to use our
--  usual repertoire of tactics, such as `rw` and `rfl`. Those work with
--  relations that Lean knows about, such as `=`, but not with our `='`. We
--  could teach Lean about `='` (by registering a reflexivity lemma for
--  `rfl`, or by working in a *quotient type* where `='` becomes `=`, for
--  `rw`), but a simpler way is to use `cases` and `apply` instead.

sf_expect_failure_in
  example (n1 n2 : Nat) (heq : n1 =' n2) :
      (n1 + 1) =' (n2 + 1) := by
    rw [heq] -- doesn't work for _our_ =' relation

sf_expect_failure_in
  example (n1 : Nat) : (n1 + 1) =' (n1 + 1) := by
    rfl -- doesn't work for _our_ =' relation

theorem eq_add' (n1 n2 : Nat) (heq : n1 =' n2) :
    (n1 + 1) =' (n2 + 1) := by
  cases heq -- n2 replaced by n1 in the goal!
  apply Eq.refl

--  ### Exercise (2 stars): eq_cons ⭐⭐

--  Construct the proof object for the following theorem. Use pattern
--  matching on the equality hypotheses.

theorem eq_cons : ∀ (α : Type) (h1 h2 : α) (t1 t2 : List α),
    h1 =' h2 → t1 =' t2 → h1 :: t1 =' h2 :: t2 :=
  (fun _ h1 _ t1 _ heq teq =>
    match heq, teq with
    | Eq.refl _, Eq.refl _ => Eq.refl (h1 :: t1))

--  ### Exercise (2 stars): equality__leibniz_equality ⭐⭐

--  The inductive definition of equality implies *Leibniz equality*: what
--  we mean when we say "`x` and `y` are equal" is that every property on
--  `P` that is true of `x` is also true of `y`. Prove that.

theorem equality__leibniz_equality : ∀ (α : Type) (x y : α),
    x =' y → ∀ (P : α → Prop), P x → P y := by
  intro α x y heq P hpx
  cases heq
  exact hpx

--  ### Exercise (2 stars): equality__leibniz_equality_term ⭐⭐

--  Construct the proof object for the previous exercise. All it requires
--  is anonymous functions and pattern-matching; the large proof term
--  constructed by tactics in the previous exercise is needessly
--  complicated. Hint: pattern-match as soon as possible.

theorem equality__leibniz_equality_term :
    ∀ (α : Type) (x y : α),
    x =' y → ∀ (P : α → Prop), P x → P y :=
  (fun _ _ _ heq =>
    match heq with
    | Eq.refl _ => fun _ hp => hp)

--  ### Exercise (2 stars): leibniz_equality__equality (Optional) ⭐⭐

--  Show that, in fact, the inductive definition of equality is
--  *equivalent* to Leibniz equality. Hint: the proof is quite short. You
--  can write it by inventing a clever property `P` to instantiate the
--  antecedent, or you can let Lean figure it out...

theorem leibniz_equality__equality : ∀ (α : Type) (x y : α),
    (∀ (P : α → Prop), P x → P y) → x =' y := by
  intro α x y h
  apply h (fun z => x =' z) -- `apply h` also works; Lean will provide `P`.
  apply Eq.refl

--  (End of exercise)

--   ----------------------------------------

--  _Quiz:_

--  Which of the following is a correct proof object for the proposition
--
--      ∃ x, x + 3 =' 4
--
--  ?
--
--  (A) `Eq.refl 4`
--
--  (B) `@Exists.intro Nat (z + 3 =' 4) 1 (Eq.refl 4)`
--
--  (C) `@Exists.intro Nat (fun z => z + 3 =' 4) 1 (Eq.refl 4)`
--
--  (D) `@Exists.intro Nat (fun z => z + 3 =' 4) 1 (Eq.refl 1)`
--
--  (E) none of the above

--   ----------------------------------------

end EqualityPlayground

--  ### Inversion, Again

--  Note to developers:
--      HIDE: PR: This section may be repetitive given the increased
--      attention paid to `inversion`, and it may be ineffective since this
--      chapter is no longer on the recommended path. We need to think
--      about whether this kind of reinforcement of the tactic is needed,
--      and if so, where to place it for best impact.
--
--      BCP 11/18: I agree — this material is a bit redundant. On the other
--      hand, the examples at the end may be helpful, so maybe it's fine to
--      leave it.

--  ## Lean's Trusted Computing Base

--  One question that arises with any automated proof assistant is "why
--  should we trust it?" — i.e., what if there is a bug in the
--  implementation that renders all its reasoning suspect?
--
--  While it is impossible to allay such concerns completely, the fact that
--  Lean is based on the Curry-Howard correspondence gives it a strong
--  foundation. Because propositions are just types and proofs are just
--  terms, checking that an alleged proof of a proposition is valid just
--  amounts to *type-checking* the term. Type checkers are relatively small
--  and straightforward programs, so the "trusted computing base" for Lean
--  — the part of the code that we have to believe is operating correctly —
--  is small too.
--
--  How, then, does Lean relegate its large set of complex behaviors to a
--  small codebase?
--
--  Lean is organized in two layers. The *elaborator* is large and
--  complicated: it handles notation, implicit arguments, `match`,
--  recursion, and tactics. Its output is a plain term in Lean's core type
--  theory, which it hands to the *kernel*. Only the kernel is trusted. It
--  is small, and its job is just to type-check that term, computing as
--  needed to decide whether two types are the same.
--
--  This division means that a bug in the elaborator, or in a tactic,
--  cannot lead Lean to accept a false theorem: at worst, it produces a
--  term that the kernel then rejects. Every declaration, whether written
--  as a term or built by tactics, is checked by the kernel when it is
--  added to the environment.
--
--  Two checks you might expect a typechecker to perform, exhaustiveness of
--  `match` and termination of recursive functions, happen in the
--  elaborator, because the kernel's language actually has no `match` and
--  no recursion at all. The kernel's language for destructuring values
--  only has the notion of a *recursor*: a primitive function that is
--  exhaustive and terminating by construction. If the elaborator cannot
--  express a definition in terms of the recursors generated by the kernel,
--  it rejects the definition.
--
--  There are some mild exceptions to this, like `partial def`, but those
--  exceptions have strict rules imposed upon them to prevent a proof of
--  `False`, and in general it is the translation to recursors that catches
--  such bugs.
--
--  We can see the elaborator refuse definitions that would otherwise let
--  us prove `False`:

sf_expect_failure_in
  theorem or_bogus : ∀ (P Q : Prop), P ∨ Q → P :=
    fun (P Q : Prop) (A : P ∨ Q) =>
      match A with
      | Or.inl h => h

--  All the types here match correctly, but the `match` only considers one
--  of the possible constructors for `Or`. Lean's exhaustiveness check will
--  reject this definition.

sf_expect_failure_in
  def infinite_loop {α : Type} (n : Nat) : α :=
    infinite_loop n
  termination_by structural n
  
  theorem falso : False := infinite_loop 0

--  Recursive function `infinite_loop` purports to return a value of any
--  type `α` that you would like. (The `termination_by structural n`
--  annotation tells Lean that it recurses on argument `n`, not `α`.) Were
--  Lean to allow `infinite_loop`, then `falso` would be definable, thus
--  giving evidence for `False`. So Lean rejects `infinite_loop`.
--
--  Besides the kernel, we also trust the handful of *axioms* Lean assumes,
--  such as `propext`. The command `#print axioms` shows which axioms a
--  theorem depends on. The tactic `native_decide` goes further, trusting
--  Lean's compiler too, which is why careful developments avoid it.

--  ## More Exercises

--  Most of the following theorems were already proved with tactics in
--  Logic. Now construct the proof objects for them directly.

--  ### Exercise (2 stars): and_assoc ⭐⭐

theorem and_assoc : ∀ (P Q R : Prop),
    P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  (fun _ _ _ h =>
    match h with
    | And.intro hp (And.intro hq hr) =>
      And.intro (And.intro hp hq) hr)

--  ### Exercise (3 stars): or_distributes_over_and ⭐⭐⭐

theorem or_distributes_over_and : ∀ (P Q R : Prop),
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
  (fun _ _ _ =>
    Iff.intro
      (fun h =>
        match h with
        | Or.inl hp => And.intro (Or.inl hp) (Or.inl hp)
        | Or.inr (And.intro hq hr) =>
          And.intro (Or.inr hq) (Or.inr hr))
      (fun h =>
        match h with
        | And.intro hpq hpr =>
          match hpq, hpr with
          | Or.inl hp, _ | _, Or.inl hp => Or.inl hp
          | Or.inr hq, Or.inr hr =>
            Or.inr (And.intro hq hr)))

--  ### Exercise (3 stars): negations ⭐⭐⭐

theorem double_neg : ∀ (P : Prop),
    P → ¬¬P :=
  (fun _ hp hnp => hnp hp)

theorem contradiction_implies_anything : ∀ (P Q : Prop),
    (P ∧ ¬P) → Q :=
  (fun _ _ h =>
    match h with
    | And.intro hp hnp => nomatch hnp hp)

theorem de_morgan_not_or : ∀ (P Q : Prop),
    ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  (fun _ _ h =>
    And.intro (fun hp => h (Or.inl hp))
      (fun hq => h (Or.inr hq)))

--  ### Exercise (2 stars): currying ⭐⭐

theorem curry : ∀ (P Q R : Prop),
    ((P ∧ Q) → R) → (P → (Q → R)) :=
  (fun _ _ _ h hp hq =>
    h (And.intro hp hq))

theorem uncurry : ∀ (P Q R : Prop),
    (P → (Q → R)) → ((P ∧ Q) → R) :=
  (fun _ _ _ h hpq =>
    match hpq with
    | And.intro hp hq => h hp hq)

--  ## Working with Proof Irrelevance

--  In Logic we saw that functional extensionality (`funext`) is a core
--  property of Lean. A similar notion about propositions also exists in a
--  Lean, this time as a core axiom:

-- Written out, propositional extensionality looks like this:
def propositional_extensionality : Prop :=
  ∀ (P Q : Prop), (P ↔ Q) → P = Q

-- Lean calls it `propext`:
#check propext

--  Output:
--    propext {a b : Prop} : (a ↔ b) → a = b

--  Propositional extensionality asserts that if two propositions are
--  equivalent — i.e., each implies the other — then they are in fact
--  equal. The *proof objects* for the propositions might be syntactically
--  different terms. But propositional extensionality overlooks that, just
--  as functional extensionality overlooks the syntactic differences
--  between functions.

--  ### Exercise (1 star): pe_implies_or_eq (Advanced) ⭐

--  Prove the following consequence of propositional extensionality.

theorem pe_implies_or_eq :
    propositional_extensionality →
    ∀ (P Q : Prop), (P ∨ Q) = (Q ∨ P) := by
  unfold propositional_extensionality
  intro PE P Q
  apply PE (P ∨ Q) (Q ∨ P)
  apply Or.comm

--  ### Exercise (1 star): pe_implies_true_eq (Advanced) ⭐

--  Prove that if a proposition `P` is provable, then it is equal to `True`
--  — as a consequence of propositional extensionality.

theorem pe_implies_true_eq :
    propositional_extensionality →
    ∀ (P : Prop), P → True = P := by
  unfold propositional_extensionality
  intro PE P p
  apply PE
  constructor
  · intro _
    exact p
  · intro _
    apply True.intro

--  (End of exercise)

end EvenProp

-- Source revision: ff31379, committed 2026-11-11 12:07 UTC

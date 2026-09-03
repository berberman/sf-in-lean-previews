import LF.CustomTactics
import HL.Imp

import SFLCompat

--  # Hoare: Hoare Logic, Part I

--  Our goal in this chapter is to develop the tools to work
--  through some simple examples of *program verification*
--  -- i.e., to use the precise definition of Imp to prove
--  formally that particular programs satisfy particular
--  specifications of their behavior.
--
--  We'll develop a reasoning system called *Floyd-Hoare
--  Logic* -- often shortened to just *Hoare Logic* -- in
--  which each of the syntactic constructs of Imp is
--  equipped with a generic "proof rule" that can be used to
--  reason compositionally about the correctness of programs
--  involving this construct.

--  Hoare Logic combines two beautiful ideas: a natural way
--  of writing down *specifications* of programs, and a
--  *structured proof technique* for proving that programs
--  are correct with respect to such specifications -- where
--  by "structured" we mean that the structure of proofs
--  directly mirrors the structure of the programs that they
--  are about.

--  ## Assertions

--  An *assertion* is a logical claim about the state of a
--  program's memory -- formally, a predicate of `State`s.

open scoped Com MyGetElem

abbrev Assertion := State → Prop

--  For example,
--
--  - `fun st => st[X] = 3` holds for states `st` in which
--    value of `X` is `3`,
--
--  - `fun st => True` hold for all states, and
--
--  - `fun st => False` holds for no states.

--   ----------------------------------------

--  _Quiz:_

--  Paraphrase the following assertions in English (i.e.,
--  say which states satisfy them)
--
--  (A) `fun st => st[X] ≤ st[Y]`
--
--  (B) `fun st => st[X] = 3 ∨ st[X] ≤ st[Y]`
--
--  (C)
--  `fun st => st[Z] * st[Z] ≤ st[X] ∧ ¬ ((st[Z] + 1) * (st[Z] + 1) ≤ st[X])`

--   ----------------------------------------

--  ### Notations for Assertions

--  We'll use Lean's notation features to make assertions
--  look as much like informal math as possible.
--
--  For example, instead of writing
--
--      fun st => st[X] = m
--
--  we'll usually write just
--
--      {{ X = m }}

--  Here, the `{{ A }}` brackets delimit the scope of the
--  assertion notation.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation: Assertions)
namespace Assertion

open Lean Elab Term Meta Imp.Elab

scoped syntax:max "assn(" ident "; " term ")" : term
scoped syntax:lead "{{" term "}}" : term

-- `: Assertion` guards that the resulting type is `State → Prop`.
macro_rules
  | `({{ $t }}) => `((fun st : _root_.State => assn(st; $t) : Assertion))

macro_rules
  | `(assn($st; $t)) => do
    let result ← match t with
      | `(($P)) => ``((assn($st; $P)))
      | `($l = $r) => ``(assn($st; $l) = assn($st; $r))
      | `($l + $r) => ``(assn($st; $l) + assn($st; $r))
      | `($l - $r) => ``(assn($st; $l) - assn($st; $r))
      | `($l * $r) => ``(assn($st; $l) * assn($st; $r))
      | `($l ≤ $r) => ``(assn($st; $l) ≤ assn($st; $r))
      | `($l < $r) => ``(assn($st; $l) < assn($st; $r))
      | `($l ≥ $r) => ``(assn($st; $l) ≥ assn($st; $r))
      | `($l > $r) => ``(assn($st; $l) > assn($st; $r))
      | `($l ∧ $r) => ``(assn($st; $l) ∧ assn($st; $r))
      | `($l ∨ $r) => ``(assn($st; $l) ∨ assn($st; $r))
      | `($l → $r) => ``(assn($st; $l) → assn($st; $r))
      | `($l ↔ $r) => ``(assn($st; $l) ↔ assn($st; $r))
      | `(¬ $p) => ``(¬ assn($st; $p))
      | `($f $args*) => do
        let mut result := f
        for arg in args do
          result ← `($result assn($st; $arg))
        pure result
      | _ => Macro.throwUnsupported
    return withSourceInfoOf t result

elab_rules : term
  | `(assn($st; $t:term)) => do
    let t ← elabTerm t none
    let ty ← whnf (← inferType t)
    tryPostponeIfMVar ty
    let st ← elabTerm st none
    match_expr ty with
    | String => mkAppM ``_root_.MyGetElem.getElem #[st, t]
    | Aexp => mkAppM ``Aexp.eval #[st, t]
    | Bexp => mkAppM ``Bexp.eval #[st, t]
    | _ =>
      match ty with
      | .forallE _ domain body _ =>
        if body.isProp && (← isDefEq domain (mkConst ``_root_.State)) then
          pure <| mkApp t st
        else
          pure t
      | _ => pure t

#check {{ 1 = 2 }}
#check {{ X = X }}
#check {{ X = 2 * X }} -- X is the constant "X" defined in Imp
#check_failure {{ X }} -- fails as expected
#check {{ True }}

#check {{ fun st => st[X] = st[Y] }}

variable (a : Aexp)
#check {{ X = a }}

variable (b : Bexp)
#check {{ b }}
#check {{ ¬ b }}
#check {{ b ∧ b }}

variable (P Q : Assertion)
#check {{ P ∧ Q }}

variable (f : Nat → Nat → Nat → Nat)
#check {{ f X Y X = 0 }}

end Assertion
open scoped Assertion
--  END DETAILS

--  Function applications inside assertions automatically
--  interpret their arguments in the current state:
--
--  `{{ f e1 ... en }}` stands for
--  `(fun st => f (e1 st) ... (en st))`.

--  We can place a raw Lean function directly inside
--  assertion notation:
--
--  For example: `{{ fun st => ∀ x, st[x] = 0 }}`

--  ### Example Assertions

namespace ExamplePrettyAssertions

def assertion1 : Assertion := {{ X = 3 }}
def assertion2 : Assertion := {{ True }}
def assertion3 : Assertion := {{ False }}
def assertion4 : Assertion := {{ True ∨ False }}
def assertion5 : Assertion := {{ X ≤ Y }}
def assertion6 : Assertion := {{ X = 3 ∨ X ≤ Y }}
def assertion7 : Assertion := {{ Z = max X Y }}
def assertion8 : Assertion := {{ Z * Z ≤ X
                                 ∧ ¬ (((Nat.succ Z) * (Nat.succ Z)) ≤ X) }}
def assertion9 : Assertion := {{ Nat.add X Y > max Y X }}
variable {xs : List Nat}
-- #check {{ xs = X }}
/--
info: def ExamplePrettyAssertions.assertion8 : Assertion :=
fun st => st[Z] * st[Z] ≤ st[X] ∧ ¬st[Z].succ * st[Z].succ ≤ st[X]
-/
#guard_msgs in
#print assertion8

end ExamplePrettyAssertions

--  ### Printing Assertions

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing assertions back)
namespace Assertion.Delab

open Lean PrettyPrinter Delaborator SubExpr Imp.Elab Imp.Delab

private def getAssn (stx : Term) : Term :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
  match stx with
  | `({{ $P }}) => return P
  | _ => return stx

/-- Rebuild the surface form of an assertion body, undoing the state
threading the `assn` elaborator performs: `st[X]` prints as `X`,
`Aexp.eval st a` as `a`, `Bexp.eval st b = true` as `b`, an applied
assertion `P st` as `P`, and a subterm that does not mention the state
prints as itself. -/
partial def delabBody (stId : FVarId) : DelabM Term := do
  let e ← getExpr
  if !e.containsFVar stId then
    delab
  else
    match_expr e with
    | MyGetElem.getElem _ _ _ _ st _ =>
      guard (st == .fvar stId)
      withAppArg delab
    | Aexp.eval st _ =>
      guard (st == .fvar stId)
      withAppArg delab
    | HAdd.hAdd _ _ _ _ _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) + $(← withAppArg (delabBody stId)))
    | HSub.hSub _ _ _ _ _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) - $(← withAppArg (delabBody stId)))
    | HMul.hMul _ _ _ _ _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) * $(← withAppArg (delabBody stId)))
    | Eq _ l r =>
      -- `Bexp.eval st b = true` is the threaded form of a bare boolean `b`
      if r.isConstOf ``Bool.true && l.isAppOfArity ``Bexp.eval 2
          && l.appFn!.appArg! == .fvar stId then
        withAppFn <| withAppArg <| withAppArg delab
      else
        `($(← withAppFn <| withAppArg (delabBody stId)) = $(← withAppArg (delabBody stId)))
    | Ne _ _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) ≠ $(← withAppArg (delabBody stId)))
    | LE.le _ _ _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) ≤ $(← withAppArg (delabBody stId)))
    | LT.lt _ _ _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) < $(← withAppArg (delabBody stId)))
    | GE.ge _ _ _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) ≥ $(← withAppArg (delabBody stId)))
    | GT.gt _ _ _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) > $(← withAppArg (delabBody stId)))
    | And _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) ∧ $(← withAppArg (delabBody stId)))
    | Or _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) ∨ $(← withAppArg (delabBody stId)))
    | Iff _ _ =>
      `($(← withAppFn <| withAppArg (delabBody stId)) ↔ $(← withAppArg (delabBody stId)))
    | Not _ =>
      `(¬ $(← withAppArg (delabBody stId)))
    | _ =>
      if e.isArrow then
        `($(← withBindingDomain (delabBody stId)) →
          $(← withBindingBody `h (delabBody stId)))
      else if let .app f v := e then
        if v == .fvar stId && !f.containsFVar stId then
          -- an applied assertion `P st` (or an applied escape lambda)
          if f.isLambda then
            withAppFn <| withOptions (pp.notation.set · false) delab
          else
            withAppFn delab
        else
          `($(← withAppFn (delabBody stId)) $(← withAppArg (delabBody stId)))
      else
        failure

/-- Print an `Assertion`-valued term as it appears inside `{{ … }}`: a
state lambda is un-threaded; a term the printer cannot rebuild falls back
to the raw lambda, which is exactly this notation's escape form. -/
partial def delabAssn : DelabM Term := do
  if (← getExpr).isLambda then
    (withBindingBody' `st (pure ·.fvarId!) fun stId => delabBody stId)
      <|> withOptions (pp.notation.set · false) Delaborator.delab
  else
    delab

/-- Print an assertion-position argument: a state lambda gets the
`{{ … }}` notation; any other term (a named assertion, a substitution)
already reads well bare. -/
def delabAssnArg (i : Nat) : DelabM Term := do
  if (← withNaryArg i getExpr).isLambda then
    `({{ $(← withNaryArg i delabAssn) }})
  else
    withNaryArg i Delaborator.delab

/-- Print a bare assertion lambda in `{{ … }}` notation.  Keyed on lambdas
at large, so the guards bail out cheaply unless the binder is a `State`
and the body is a proposition the printer can rebuild. -/
@[delab lam]
def delabAssertion : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isLambda && e.bindingDomain!.isConstOf ``_root_.State
  let P ← withBindingBody' `st (pure ·.fvarId!) fun stId => do
    guard (← Meta.inferType (← getExpr)).isProp
    delabBody stId
  `({{ $P }})

end Assertion.Delab
--  END DETAILS

--  ### Assertion Implication

--  Given two assertions `P` and `Q`, we say that `P`
--  *implies* `Q`, written `P ->> Q`, if, whenever `P` holds
--  in some state `st`, `Q` also holds.

def AssertImplies (P Q : Assertion) : Prop :=
  ∀ st, P st → Q st

--  Note that the notation for *assertion implication* is
--  analogous to the "usual" Lean implication `→`.

notation:26 P:27 " ->> " Q:27 => AssertImplies P Q

theorem assertImplies_def {P Q : Assertion} : P ->> Q ↔ ∀ st, P st → Q st := by rfl

--  We'll also want the "iff" variant of implication between
--  assertions:

notation:26 P:27 " <<->> " Q:27 => AssertImplies P Q ∧ AssertImplies Q P

theorem assertIff_def {P Q : Assertion} : P <<->> Q ↔ AssertImplies P Q ∧ AssertImplies Q P
    := by rfl

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing implications back)
namespace Assertion.Delab
open Lean PrettyPrinter Delaborator SubExpr

@[delab app.AssertImplies]
def delabAssertImplies : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``AssertImplies 2
  `($(← delabAssnArg 0) ->> $(← delabAssnArg 1))

/-- `<<->>` abbreviates a conjunction of two `AssertImplies`, so its
delaborator is keyed on `∧` and bails out unless the two conjuncts mirror
each other. -/
@[delab app.And]
def delabAssertIff : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isAppOfArity ``And 2
  let l := e.appFn!.appArg!
  let r := e.appArg!
  guard <| l.isAppOfArity ``AssertImplies 2 && r.isAppOfArity ``AssertImplies 2
  guard <| l.appFn!.appArg! == r.appArg! && l.appArg! == r.appFn!.appArg!
  `($(← withNaryArg 0 <| delabAssnArg 0) <<->> $(← withNaryArg 0 <| delabAssnArg 1))

end Assertion.Delab
--  END DETAILS

--  ## Hoare Triples, Informally

--  A *Hoare triple* is a claim about the state before and
--  after executing a command. A commond notation for Hoare
--  triples, and the one we use in this book, is
--
--      {{P}} c {{Q}}
--
--  meaning:
--
--  - If command `c` begins execution in a state satisfying
--    assertion `P`,
--
--  - and if `c` eventually terminates in some final state,
--
--  - then that final state will satisfy the assertion `Q`.
--
--  Assertion `P` is called the *precondition* of the
--  triple, and `Q` is the *postcondition*.

--  For example,
--
--  - The Hoare triple
--
--      {{X = 0}} X := X + 1 {{X = 1}}
--
--  states that command `X := X + 1` will transform a state
--  in which `X = 0` to a state in which `X = 1`.
--
--  - On the other hand,
--
--      ∀ m, {{X = m}} X := X + 1 {{X = m + 1}}
--
--  is a *proposition* stating that the Hoare triple
--  `{{X = m}} X :=
--  X + 1 {{X = m + 1}}` is valid for any
--  choice of `m`. Note that `m` in the two assertions is a
--  reference to the *Lean* variable `m`, which is bound
--  outside the Hoare triple.

--   ----------------------------------------

--  _Quiz:_

--  Paraphrase the following in English.
--
--      1) {{True}} c {{X = 5}}
--
--      2) ∀ m, {{X = m}} c {{X = m + 5}}
--
--      3) {{X ≤ Y}} c {{Y ≤ X}}
--
--      4) {{True}} c {{False}}
--
--      5) ∀ m,
--           {{X = m}}
--           c
--           {{Y = real_fact m}}
--
--      6) ∀ m,
--           {{X = m}}
--           c
--           {{(Z * Z) ≤ m ∧ ¬ ((Z + 1) * (Z + 1) ≤ m)}}

--   ----------------------------------------

--  _Quiz:_

--  Is the following Hoare triple *valid* -- i.e., is the
--  claimed relation between `P`, `c`, and `Q` true?
--
--      {{True}} X := 5 {{X = 5}}
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      {{X = 2}} X := X + 1 {{X = 3}}
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      {{True}} X := 5; Y := 0 {{X = 5}}
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      {{X = 2 ∧ X = 3}} X := 5 {{X = 0}}
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      {{True}} skip {{False}}
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      {{False}} skip {{True}}
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      {{True}} while true do skip end {{False}}
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  This one?
--
--      {{X = 0}}
--        while X = 0 do X := X + 1 end
--      {{X = 1}}
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  This one?
--
--      {{X = 1}}
--        while X ≠ 0 do X := X + 1 end
--      {{X = 100}}
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  ## Hoare Triples, Formally

--  We formalize valid Hoare triples in Lean as follows:

open scoped HasEval

def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st st' : State},
    (st =[ c ]=> st') →
    P st →
    Q st'

class HasTriple (Com : Type) where
  Triple : Assertion → Com → Assertion → Prop

namespace HasTriple

/-- Hoare triple: `{{ P }} c {{ Q }}` with `imp_com` command syntax -/
scoped syntax:lead "{{" term "}} " imp_com:min " {{" term "}}" : term
scoped macro_rules
  | `({{ $P }} $c:imp_com {{ $Q }}) =>
      ``(HasTriple.Triple ({{ $P }}) (imp { $c }) ({{ $Q }}))
end HasTriple

instance : HasTriple Com where
  Triple := ValidHoareTriple

--  We make `ValidHoareTriple` irreducible for "technical
--  reasons", and use it only via `validHoareTriple_def` in
--  proofs.

open scoped HasTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} c {{ Q }} ↔ ∀ {st st' : State},
      (st =[ c ]=> st') →
      P st →
      Q st' := by rfl

attribute [irreducible] ValidHoareTriple

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing triples back)
--  The delaborator is agnostic to the command type: it
--  prints the command with whatever printer is registered
--  for its constructors and splices the result into the
--  triple, so a language-extension chapter only has to
--  register a printer for its own `Com`.

namespace HasTriple.Delab

open Lean PrettyPrinter Delaborator SubExpr Assertion.Delab Imp.Delab
@[delab app.HasTriple.Triple]
def delabTriple : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``HasTriple.Triple 5
  let P ← withNaryArg 2 delabAssn
  let c ← withNaryArg 3 delab
  let Q ← withNaryArg 4 delabAssn
  match c with
  | `(imp { $c:imp_com }) => ``({{ $P }} $c:imp_com {{ $Q }})
  | c => ``({{ $P }} ~$c {{ $Q }})

end HasTriple.Delab
--  END DETAILS

--  ### Exercise (1 star): hoare_post_true ⭐

--  Prove that if `Q` holds in every state, then any triple
--  with `Q` as its postcondition is valid.

theorem hoare_post_true {P Q : Assertion} {c : Com} (h : ∀ st, Q st) :
    {{ P }} c {{ Q }} := by
  sorry

--  ### Exercise (1 star): hoare_pre_false (Optional) ⭐

--  Prove that if `P` holds in no state, then any triple
--  with `P` as its precondition is valid.

theorem hoare_pre_false {P Q : Assertion} {c : Com} (h : ∀ st, ¬ (P st)) :
    {{ P }} c {{ Q }} := by
  sorry

--  ## Proof Rules

--  We want to be able to *prove* Hoare triples formally.
--
--  Here's our plan:
--
--  - introduce one "proof rule" for each Imp syntactic form
--
--  - plus a couple of "structural rules" that help glue
--    proofs together
--
--  - prove these rules correct in terms of the definition
--    of `ValidHoareTriple`
--
--  - prove programs correct using these proof rules,
--    without ever unfolding the definition of
--    `ValidHoareTriple`

--  ### Skip

--  Since `skip` doesn't change the state, it preserves any
--  assertion `P`:
--
--      --------------------  (hoare_skip)
--      {{ P }} skip {{ P }}

theorem hoare_skip {P : Assertion} :
    {{ P }} skip {{ P }} := by
  rw [validHoareTriple_def]
  intro st st' h hpre
  inversion h
  exact hpre

--  ### Sequencing

--  If command `c1` takes any state where `P` holds to a
--  state where `Q` holds, and if `c2` takes any state where
--  `Q` holds to one where `R` holds, then doing `c1`
--  followed by `c2` will take any state where `P` holds to
--  one where `R` holds:
--
--       {{ P }} c1 {{ Q }}
--       {{ Q }} c2 {{ R }}
--      ----------------------  (hoare_seq)
--      {{ P }} c1; c2 {{ R }}

theorem hoare_seq {P Q R : Assertion} {c1 c2 : Com}
    (h1 : {{ Q }} c2 {{ R }}) (h2 : {{ P }} c1 {{ Q }}) :
    {{ P }} c1; c2 {{ R }} := by
  rw [validHoareTriple_def]
  intro st st' h hpre
  inversion h with
  | seq st'' hc1 hc2 =>
    rw [validHoareTriple_def] at h1 h2
    exact h1 hc2 (h2 hc1 hpre)

--  ### Assignment

--  How can we complete this triple?
--
--      {{ ??? }}  X := Y  {{ X = 1 }}
--
--  One natural possibility is:
--
--      {{ Y = 1 }}  X := Y  {{ X = 1 }}
--
--  The precondition is just the postcondition, but with `X`
--  replaced by `Y`.

--  How about this one?
--
--      {{ ??? }}  X := X + Y  {{ X = 1 }}
--
--  Replace `X` with `X + Y`:
--
--      {{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}
--
--  This works because "equals 1" holding of `X` is
--  guaranteed by the property "equals 1" holding of
--  whatever is being assigned to `X`.

--  In general, the postcondition could be some arbitrary
--  assertion `Q`, and the right-hand side of the assignment
--  could be some arbitrary arithmetic expression `a`:
--
--      {{ ??? }}  X := a  {{ Q }}
--
--  The precondition would then be `Q`, but with any
--  occurrences of `X` in it replaced by `a`.

--  Let's introduce a notation for this idea of replacing
--  occurrences: Define `Q \[X ↦ a`] to mean "`Q` where `a`
--  is substituted in place of `X`".
--
--  This yields the Hoare logic rule for assignment:
--
--      {{ Q [X ↦ a] }}  X := a  {{ Q }}
--
--  One way of reading this rule is: If you want statement
--  `X := a` to terminate in a state that satisfies
--  assertion `Q`, then it suffices to start in a state that
--  also satisfies `Q`, except where `a` is substituted for
--  every occurrence of `X`.

--  Here are some valid instances of the assignment rule:
--
--      {{ (X ≤ 5) [X ↦ X + 1] }}         (that is, X + 1 ≤ 5)
--        X := X + 1
--      {{ X ≤ 5 }}
--
--      {{ (X = 3) [X ↦ 3] }}              (that is, 3 = 3)
--        X := 3
--      {{ X = 3 }}
--
--      {{ (0 ≤ X ∧ X ≤ 5) [X ↦ 3] }}.  (that is, 0 ≤ 3 ∧ 3 ≤ 5)
--        X := 3
--      {{ 0 ≤ X ∧ X ≤ 5 }}

--  To formalize the rule, we must first formalize the idea
--  of "substituting an expression for an Imp variable in an
--  assertion", which we refer to as assertion substitution,
--  or `Assertion.subst`.
--
--  Intuitively, given a proposition `P`, a variable `X`,
--  and an arithmetic expression `a`, we want to derive
--  another proposition `P'` that is just the same as `P`
--  except that `P'` should mention `a` wherever `P`
--  mentions `X`.

--  This operation is related to the idea of substituting
--  Imp expressions for Imp variables that we saw in *Equiv*
--  (`subst_aexp` and friends). The difference is that,
--  here, `P` is an arbitrary Lean assertion, so we can't
--  directly "edit" its text.

--  However, we can achieve the same effect by evaluating
--  `P` in an updated state, defined as follows:

def Assertion.subst (x : Ident) (a : Aexp) (P : Assertion) : Assertion :=
  fun (st : State) => P (x →ₜ a.eval st ; st)

namespace Assertion

/-- Assertion substitution, written inside the braces: `{{ (P) [X ↦ a] }}`.
The substituted assertion is re-read with the same notation, so Imp
variables in it mean state lookups as usual; a named assertion is passed
through directly. -/
scoped syntax:max term:arg " [" ident " ↦ " imp_aexp "]" : term

macro_rules
  | `(assn($st; $P [$x ↦ $a:imp_aexp])) =>
    match P with
    | `($_:ident) => ``(Assertion.subst $x (aexp { $a }) $P $st)
    | _ => ``(Assertion.subst $x (aexp { $a }) ({{ $P }}) $st)

theorem subst_def {x : Ident} {a : Aexp} {P : Assertion} :
    Assertion.subst x a P = fun (st : State) => P (x →ₜ a.eval st ; st) := by rfl

@[simp]
theorem subst_apply {x : Ident} {a : Aexp} {P : Assertion} {st : State} :
    Assertion.subst x a P st ↔ P (x →ₜ a.eval st ; st) := by rfl

end Assertion

--  This notation allows us to write this operation as:
--
--      P [ X ↦ a ]

#check (fun st => Assertion.subst X (aexp { 2 * X }) ({{ X ≤ 10 }}) st)
#check {{ (X ≤ 10) [X ↦ 2 * X] }}
#check (∀ st, ({{ (X ≤ 10) [X ↦ 2 * X] }}) st)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: printing substitutions back)
namespace Assertion.Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab

/-- Print an `Assertion.subst` back in `P [x ↦ a]` notation.  Emits the
bare inside-the-braces form: the generic application case of `delabBody`
picks it up inside an assertion body, and the enclosing printer supplies
the single pair of braces. -/
@[app_unexpander Assertion.subst]
def unexpandSubst : Unexpander
  | `($_ $x:ident $a $P) =>
    match getAssn P with
    | `($P:ident) => `($P:ident [$x:ident ↦ $(getAexp a):imp_aexp])
    | P => `(($P) [$x:ident ↦ $(getAexp a):imp_aexp])
  | _ => throw ()

end Assertion.Delab
--  END DETAILS

--  That is, `P [X ↦ a]` stands for an assertion -- let's
--  call it `P'` -- that behaves just like `P` except that,
--  wherever `P` looks up the variable `X` in the current
--  state, `P'` instead uses the value of the expression
--  `a`.

--  We can demonstrate formally that we have captured
--  intuitive meaning of "assertion subsitution" by proving
--  some example logical equivalences:

namespace ExampleAssertionSub
example :
    {{ (X ≤ 5) [X ↦ 3] }} <<->> {{ 3 ≤ 5 }} := by
  rw [assertIff_def]
  rw [assertImplies_def]
  constructor
  · intro st _
    simp
  · intro st h
    simp

example :
    {{ (X ≤ 5) [X ↦ X + 1] }} <<->> {{ (X + 1) ≤ 5 }} := by
  rw [assertIff_def]
  constructor
  · rw [assertImplies_def]
    intro st
    simp
  · rw [assertImplies_def]
    intro st
    simp

end ExampleAssertionSub

--  Most of the `simp` calls rely on
--  `Assertion.subst_apply`, `TotalMap.update_eq` plus some
--  `Aexp` characterizing lemmas like `Aexp.eval_num`.

--  Now, using the substitution operation we've just
--  defined, we can give the precise proof rule for
--  assignment:
--
--      ---------------------------- (hoare_asgn)
--      {{Q [X ↦ a]}} X := a {{Q}}
--
--  We can prove formally that this rule is indeed valid.

theorem hoare_asgn {Q : Assertion} {x : Ident} {a : Aexp} :
    {{ Q [x ↦ a] }} x := a {{ Q }} := by
  rw [validHoareTriple_def]
  intro st st' hE hQ
  inversion hE with
  | asgn n h =>
    subst h
    rw [Assertion.subst_def] at hQ
    exact hQ

--  Here's a first formal proof of a Hoare triple using this
--  rule.

theorem assertion_sub_example :
    {{ (X < 5) [X ↦ X + 1] }}
      X := X + 1
    {{ X < 5 }} := by
  exact hoare_asgn

--  Of course, we'd probably prefer to work with this
--  simpler triple:
--
--      {{X < 4}} X := X + 1 {{X < 5}}
--
--  We will see how to do so in the next section.
--
--  Several proofs below use the facts about total-map
--  updates proved in the *Typeclasses* chapter --
--  `TotalMap.update_eq`, `TotalMap.update_neq`,
--  `TotalMap.update_shadow`, `TotalMap.update_same`, and
--  `TotalMap.update_permute`. Make sure you understand
--  their statements.

--  ### Consequence

--  Sometimes the preconditions and postconditions we get
--  from the Hoare rules won't quite be the ones we want in
--  the particular situation at hand -- they may be
--  logically equivalent but have a different syntactic form
--  that fails to unify with the goal we are trying to
--  prove, or they actually may be logically weaker (for
--  preconditions) or stronger (for postconditions) than
--  what we need.

--  For instance,
--
--      {{(X = 3) [X ↦ 3]}} X := 3 {{X = 3}},
--
--  follows directly from the assignment rule, but
--
--      {{True}} X := 3 {{X = 3}}
--
--  does not. This triple is valid, but it is not an
--  instance of `hoare_asgn` because `True` and
--  `(X = 3) \[X ↦ 3`] are not syntactically equal
--  assertions.
--
--  However, they are logically *equivalent*, so if one
--  triple is valid, then the other must certainly be as
--  well. We can capture this observation with the following
--  rule:
--
--         {{P'}} c {{Q}}
--           P <<->> P'
--      ---------------------
--         {{P}} c {{Q}}

--  Taking this line of thought a bit further, we can see
--  that strengthening the precondition or weakening the
--  postcondition of a valid triple always produces another
--  valid triple. This observation is captured by two *Rules
--  of Consequence*.
--
--             {{P'}} c {{Q}}
--                P ->> P'
--      -----------------------------   (hoare_consequence_pre)
--             {{P}} c {{Q}}
--
--             {{P}} c {{Q'}}
--               Q' ->> Q
--      -----------------------------    (hoare_consequence_post)
--             {{P}} c {{Q}}

--  Here are the formal versions:

theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} c {{ Q }}) (himp : P ->> P') :
    {{ P }} c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply hhoare heval
  rw [assertImplies_def] at himp
  exact himp _ hpre

theorem hoare_consequence_post {P Q Q' : Assertion} {c : Com}
    (hhoare : {{ P }} c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  rw [assertImplies_def] at himp
  apply himp
  exact hhoare heval hpre

--  For example, we can use the first consequence rule like
--  this:
--
--      {{ True }} ->>
--      {{ (X = 1) [X ↦ 1] }}
--        X := 1
--      {{ X = 1 }}
--
--  Or, formally...

theorem hoare_asgn_example1 :
    {{True}} X := 1 {{X = 1}} := by
  sorry

--  We can also use it to prove the example mentioned
--  earlier.
--
--      {{ X < 4 }} ->>
--      {{ (X < 5)[X ↦ X + 1] }}
--        X := X + 1
--      {{ X < 5 }}
--
--  Or, formally ...

theorem assertion_sub_example2 :
    {{X < 4}}
      X := X + 1
    {{X < 5}} := by
  sorry

--  Finally, here is a combined rule of consequence that
--  allows us to vary both the precondition and the
--  postcondition.
--
--             {{P'}} c {{Q'}}
--                P ->> P'
--                Q' ->> Q
--      -----------------------------   (hoare_consequence)
--             {{P}} c {{Q}}

theorem hoare_consequence {P P' Q Q' : Assertion} {c : Com}
    (htriple : {{ P' }} c {{ Q' }}) (hpre : P ->> P') (hpost : Q' ->> Q) :
    {{ P }} c {{ Q }} := by
  apply hoare_consequence_pre (P' := P')
  · exact hoare_consequence_post htriple hpost
  · exact hpre

--  ### Automation

--  Many of the proofs we have done so far with Hoare
--  triples can be streamlined using the automation
--  techniques that we introduced in the *Automation*
--  chapter of *Logical Foundations*.
--
--  Recall that `simp` rewrites with any lemmas we pass it.
--  The definitions whose meaning we keep needing to expose
--  in this chapter -- `ValidHoareTriple`, `AssertImplies`,
--  and `Assertion.subst` -- each come with a characterizing
--  lemma (`validHoareTriple_def`, `assertImplies_def`,
--  `Assertion.subst_def`) restating the definition as an
--  equation. Passing these lemmas to `simp` replaces the
--  defined notions by their meanings wherever they appear.
--  We'll do that explicitly below (and shortly package the
--  recipe up as a tactic of our own).

--  Here's a good candidate for automation:

--      theorem hoare_consequence_pre (P P' Q : Assertion) (c : Com)
--          (hhoare : {{ P' }} c {{ Q }}) (himp : P ->> P') :
--          {{ P }} c {{ Q }} := by
--        rw [validHoareTriple_def] at hhoare ⊢
--        intro st st' heval hpre
--        apply hhoare heval
--        rw [assertImplies_def] at himp
--        exact himp _ hpre

--  Since `AssertImplies` is not marked `irreducible`, and
--  `assertImplies_def` is a proof by definitional equality,
--  we can skip the `rw [assertImplies_def] at himp` and use
--  `P ->> P'` like an implication directly.

theorem hoare_consequence_pre' (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} c {{ Q }}) (himp : P ->> P') :
    {{ P }} c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply hhoare heval
  exact himp _ hpre

--  From now on, we will not usually rewrite
--  `assertImplies_def` explicitly.
--
--  Since, after the `rw` and `intro`, the remaining steps
--  just apply hypotheses to the goal (and each other), the
--  remaining proof can be compressed into a single tactic:
--  `apply_rules`.

theorem hoare_consequence_pre'' (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} c {{ Q }}) (himp : P ->> P') :
    {{ P }} c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply_rules

--  The same trick works for `hoare_consequence_post`.

theorem hoare_consequence_post' (P Q Q' : Assertion) (c : Com)
    (hhoare : {{ P }} c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply_rules

--  We can also leave a metavariable for `P'` in
--  `hoare_asgn_example1`, that we did earlier as an example
--  of using the consequence rule:

theorem hoare_asgn_example1' :
    {{True}} X := 1 {{X = 1}} := by
  apply hoare_consequence_pre -- not specifying `(P' := ...)` leaves a "hole" `?P'`
  · -- The goal is `{{?P'}} X := 1 {{X = 1}}`
    exact hoare_asgn -- Assigns `?P'` to `{{ (X = 1) [X ↦ 1] }}` (automatically closing `case P'`)
  · intro st _ -- Since `->>` is an implication, we can just use `intro` directly.
    simp

--  The final bullet of that proof also looks like a
--  candidate for automation.

theorem hoare_asgn_example1'' :
    {{True}} X := 1 {{X = 1}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · simp [assertImplies_def]

--  Now we have quite a nice proof script: it simply
--  identifies the Hoare rules that need to be used and
--  leaves the remaining low-level details up to Lean to
--  figure out.

--  The other example of using consequence that we did
--  earlier, `hoare_asgn_example2`, requires a little more
--  work to automate. `simp` simplifies the assertion
--  implication in the final bullet, but cannot finish it:
--  the leftover goal is arithmetic, so it needs `lia`.

theorem assertion_sub_example2' :
    {{X < 4}}
      X := X + 1
    {{X < 5}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · simp [assertImplies_def] -- an arithmetic goal remains
    lia

--  Let's introduce our own tactic to handle both that
--  bullet and the bullet from example 1. A `macro`
--  declaration gives a name to a canned sequence of
--  tactics:

macro "assertion_auto" : tactic =>
  `(tactic| focus (simp +decide [assertImplies_def, assertIff_def, validHoareTriple_def,
                                Assertion.subst_def] at *
                  <;> lia))

theorem assertion_sub_example2'' :
    {{X < 4}}
      X := X + 1
    {{X < 5}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · assertion_auto

theorem hoare_asgn_example1''' :
    {{True}} X := 1 {{X = 1}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · assertion_auto

--  Again, we have quite a nice proof script. All the
--  low-level details of proofs about assertions have been
--  taken care of automatically. Of course, `assertion_auto`
--  isn't able to prove everything we could possibly want to
--  know about assertions -- there's no magic here! But it's
--  pretty good.

--  ### Sequencing + Assignment

--  Here's an example of a program involving both sequencing
--  and assignment. Note the use of `hoare_seq` in
--  conjunction with `hoare_consequence_pre` and `apply`'s
--  metavariables.

theorem hoare_asgn_example3 (a : Aexp) (n : Nat) :
    {{a = n}}
      X := a;
      skip
    {{X = n}} := by
  apply hoare_seq
  · -- right part of seq
    exact hoare_skip
  · -- left part of seq
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto

--  Informally, a nice way of displaying a proof using the
--  sequencing rule is as a "decorated program" where the
--  intermediate assertion `Q` is written between `c1` and
--  `c2`:
--
--               {{ a = n }}
--      X := a
--               {{ X = n }};    <--- decoration for Q
--      skip
--               {{ X = n }}
--
--  We'll come back to the idea of decorated programs in
--  much more detail in the next chapter.

--  ### Conditionals

--  What sort of rule do we want for reasoning about
--  conditional commands?
--
--  Certainly, if the same assertion `Q` holds after
--  executing either of the branches, then it holds after
--  the whole conditional. So we might be tempted to write:
--
--              {{P}} c1 {{Q}}
--              {{P}} c2 {{Q}}
--      ---------------------------------
--      {{P}} if b then c1 else c2 {{Q}}

--  However, this is rather weak. For example, using this
--  rule, we cannot show
--
--      {{ True }}
--        if X = 0
--          then Y := 2
--          else Y := X + 1
--        end
--      {{ X ≤ Y }}
--
--  since the rule doesn't tell us enough about the state in
--  which the assignments take place in the "then" and
--  "else" branches.

--  Better:

--      {{P ∧   b}} c1 {{Q}}
--      {{P ∧ ¬ b}} c2 {{Q}}
--      ------------------------------------  (hoare_if)
--      {{P}} if b then c1 else c2 end {{Q}}

theorem bexp_eval_false (b : Bexp) (st : State) (h : b.eval st = false) :
    ¬ ({{ b }}) st := by
  dsimp
  simp [h]

--  Now we can formalize the Hoare proof rule for
--  conditionals and prove it correct.
--
--  The statement of the rule reads: given
--  `htrue : {{ P ∧ b }} c1 {{Q}}` and
--  `hfalse : {{ P ∧ ¬b }} c2 {{Q}}`, we can conclude
--  `{{P}} if (b) { c1 } else { c2 } {{Q}}`.

theorem hoare_if {P Q : Assertion} {b : Bexp} {c1 c2 : Com}
    (htrue : {{ P ∧ b }} c1 {{ Q }}) (hfalse : {{ P ∧ ¬ b }} c2 {{ Q }}) :
    {{ P }} if (b) { c1 } else { c2 } {{ Q }} := by
  rw [validHoareTriple_def] at htrue hfalse ⊢
  intro st st' hE hpre
  inversion hE with
  | ifTrue hb hc1 =>
    exact htrue hc1 ⟨hpre, hb⟩
  | ifFalse hb hc =>
    rw [← Bool.not_eq_true] at hb
    exact hfalse hc ⟨hpre, hb⟩

--  #### Example

theorem if_example :
    {{True}}
      if (X = 0) {
        Y := 2
      } else {
        Y := X + 1
      }
    {{X ≤ Y}} := by
  apply hoare_if
  · -- Then
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto
  · -- Else
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto

--  We can even shorten it a little bit more.

theorem if_example' :
    {{True}}
      if (X = 0) {
        Y := 2
      } else {
        Y := X + 1
      }
    {{X ≤ Y}} := by
  apply hoare_if <;> apply hoare_consequence_pre hoare_asgn (by assertion_auto)

--  ### While Loops

--  The Hoare rule for `while` loops is based on the idea of
--  a *command invariant* (or just *invariant*): an
--  assertion whose truth is guaranteed after executing a
--  command, assuming it is true before.
--
--  That is, an assertion `P` is a command invariant of `c`
--  if
--
--      {{P}} c {{P}}
--
--  holds. Note that the command invariant might temporarily
--  become false in the middle of executing `c`, but by the
--  end of `c` it must be restored.

--  The Hoare while rule combines the idea of a command
--  invariant with information about when guard `b` does or
--  does not hold.
--
--            {{P ∧ b}} c {{P}}
--      --------------------------------- (hoare_while)
--      {{P}} while b do c end {{P ∧ ¬b}}

theorem hoare_while {P : Assertion} {b : Bexp} {c : Com}
    (hhoare : {{P ∧ b}} c {{ P }}) :
    {{ P }} while (b) { c } {{P ∧ ¬ b}} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  /- We proceed by induction on `heval`, because, in the "keep
  looping" case, its hypotheses talk about the whole loop instead
  of just `c`. We begin by generalizing over an
  arbitrary command, together with an equation remembering that the
  command is the original loop. The cases for commands other than
  `while` are dismissed because their equations are contradictory. -/
  generalize heq : (imp { while (b) { c } }) = cmd at heval
  induction heval with
  | @whileFalse b0 s0 c0 hb =>
    injection heq with hbeq hceq
    simp_all
  | @whileTrue s0 s0' s0'' b0 c0 hb hc hloop ih1 ih2 =>
    injection heq with hbeq hceq
    subst hbeq hceq
    exact ih2 (hhoare hc ⟨hpre, hb⟩) rfl
  | skip | asgn | seq | ifTrue | ifFalse =>
    contradiction

--  We call `P` a *loop invariant* of `while b do c end` if
--
--      {{P ∧ b}} c {{P}}
--
--  is a valid Hoare triple.
--
--  This means that `P` will be true at the end of the loop
--  body whenever the loop body executes. If `P` contradicts
--  `b`, this holds trivially since the precondition is
--  false.
--
--  For instance, `X = 0` is a loop invariant of
--
--      while X = 2 do X := 1 end
--
--  since the program will never enter the loop.

--   ----------------------------------------

--  _Quiz:_

--  Is the assertion
--
--      Y = 0
--
--  a loop invariant of the following?
--
--      while X < 100 do X := X + 1 end
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  Is the assertion
--
--      X = 0
--
--  a loop invariant of the following?
--
--      while X < 100 do X := X + 1 end
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  Is the assertion
--
--      X < Y
--
--  a loop invariant of the following?
--
--      while true do X := X + 1; Y := Y + 1 end
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  Is the assertion
--
--      X = Y + Z
--
--  a loop invariant of the following?
--
--      while Y > 10 do Y := Y - 1; Z := Z + 1 end
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  Is the assertion
--
--      X > 0
--
--  a loop invariant of the following?
--
--      while X = 0 do X := X - 1 end
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  Is the assertion
--
--      X < 100
--
--  a loop invariant of the following?
--
--      while X < 100 do X := X + 1 end
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  _Quiz:_

--  Is the assertion
--
--      X > 10
--
--  a loop invariant of the following?
--
--      while X > 10 do X := X + 1 end
--
--  (A) Yes
--
--  (B) No

--   ----------------------------------------

--  ## Summary

--  The rules of Hoare Logic are:
--
--             --------------------------- (hoare_asgn)
--             {{Q [X ↦ a]}} X:=a {{Q}}
--
--             --------------------  (hoare_skip)
--             {{ P }} skip {{ P }}
--
--               {{ P }} c1 {{ Q }}
--               {{ Q }} c2 {{ R }}
--              ----------------------  (hoare_seq)
--              {{ P }} c1;c2 {{ R }}
--
--              {{P ∧   b}} c1 {{Q}}
--              {{P ∧ ¬ b}} c2 {{Q}}
--      ------------------------------------  (hoare_if)
--      {{P}} if b then c1 else c2 end {{Q}}
--
--               {{P ∧ b}} c {{P}}
--        -----------------------------------  (hoare_while)
--        {{P}} while b do c end {{P ∧ ¬ b}}
--
--                {{P'}} c {{Q'}}
--                   P ->> P'
--                   Q' ->> Q
--         -----------------------------   (hoare_consequence)
--                {{P}} c {{Q}}

--  Our main task in this chapter has been to *define* the
--  rules of Hoare logic, and prove that the definitions are
--  sound. Having done so, we can go on and work *within*
--  Hoare logic to prove that particular programs satisfy
--  particular Hoare triples. In the next chapter, we'll see
--  how Hoare logic is can be used to prove that more
--  interesting programs satisfy interesting specifications
--  of their behavior.
--
--  Crucially, we will do so without ever again `unfold`ing
--  the definition of Hoare triples -- i.e., we will take
--  the rules of Hoare logic as a closed world for reasoning
--  about programs.

-- Built on 2026-09-03 19:09 UTC

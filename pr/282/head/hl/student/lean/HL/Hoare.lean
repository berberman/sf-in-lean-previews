import LF.CustomTactics
import HL.Imp

import HL.SFLCompat

-- # Hoare: Hoare Logic, Part I

-- In an earlier chapter, we began applying the mathematical tools developed
-- in the first part of the course to studying the theory of a small
-- programming language, Imp.

-- - We defined a type of *abstract syntax trees* for Imp, together with an
--   *evaluation relation* (a partial function on states) that specifies the
--   *operational semantics* of programs.

--   The language we defined, though small, captures some of the key features of
--   full-blown languages like C, C++, and Java, including the fundamental
--   notion of mutable state and some common control structures.

-- - We proved a number of *metatheoretic properties* -- "meta" in the sense
--   that they are properties of the language as a whole, rather than of
--   particular programs in the language. These included:

--   - determinism of evaluation

--   - equivalence of some different ways of writing down the definitions (e.g.,
--     functional and relational definitions of arithmetic expression evaluation)

--   - guaranteed termination of certain classes of programs

--   - correctness (in the sense of preserving meaning) of a number of useful
--     program transformations

--   - behavioral equivalence of programs (in the Equiv chapter).

-- If we stopped here, we would already have something useful: a set of tools
-- for defining and discussing programming languages and language features
-- that are mathematically precise, flexible, and easy to work with, applied
-- to a set of key properties. All of these properties are things that
-- language designers, compiler writers, and users might care about knowing.
-- Indeed, many of them are so fundamental to our understanding of the
-- programming languages we deal with that we might not consciously recognize
-- them as "theorems." But properties that seem intuitively obvious can
-- sometimes be quite subtle (sometimes also subtly wrong!).

-- In another volume of this series (*Type Systems*), we expand upon the theme
-- of metatheoretic properties of whole languages when we discuss *types* and
-- *type soundness*. In this chapter, though, we turn to a different set of
-- issues.

-- Our goal in this chapter is to develop the tools to work through some
-- simple examples of *program verification* -- i.e., to use the precise
-- definition of Imp to prove formally that particular programs satisfy
-- particular specifications of their behavior.

-- We'll develop a reasoning system called *Floyd-Hoare Logic* -- often
-- shortened to just *Hoare Logic* -- in which each of the syntactic
-- constructs of Imp is equipped with a generic "proof rule" that can be used
-- to reason compositionally about the correctness of programs involving this
-- construct.

-- Hoare Logic originated in the 1960s, and it continues to be the subject of
-- intensive research right up to the present day. It lies at the core of a
-- multitude of tools that are being used in academia and industry to specify
-- and verify real software systems.

-- Hoare Logic combines two beautiful ideas: a natural way of writing down
-- *specifications* of programs, and a *structured proof technique* for
-- proving that programs are correct with respect to such specifications --
-- where by "structured" we mean that the structure of proofs directly mirrors
-- the structure of the programs that they are about.

-- ## Assertions

-- An *assertion* is a logical claim about the state of a program's memory --
-- formally, a predicate of `State`s.

open scoped Com MyGetElem

abbrev Assertion := State → Prop

-- For example,

-- - `fun st => st[X] = 3` holds for states `st` in which value of `X` is `3`,
-- - `fun st => True` hold for all states, and
-- - `fun st => False` holds for no states.

-- _Quiz:_

-- Paraphrase the following assertions in English (i.e., say which states
-- satisfy them)

-- (A) `fun st => st[X] ≤ st[Y]`

-- (B) `fun st => st[X] = 3 ∨ st[X] ≤ st[Y]`

-- (C)
-- `fun st => st[Z] * st[Z] ≤ st[X] ∧ ¬ ((st[Z] + 1) * (st[Z] + 1) ≤ st[X])`

-- ### Exercise (1 star): assertions ⭐

-- Paraphrase the following assertions in English (or your favorite natural
-- language).

namespace ExAssertions
def assertion1 : Assertion := fun st => st[X] ≤ st[Y]
def assertion2 : Assertion :=
  fun st => st[X] = 3 ∨ st[X] ≤ st[Y]
def assertion3 : Assertion :=
  fun st => st[Z] * st[Z] ≤ st[X] ∧
            ¬ ((st[Z] + 1) * (st[Z] + 1) ≤ st[X])
def assertion4 : Assertion :=
  fun st => st[Z] = max st[X] st[Y]

end ExAssertions

-- ### Notations for Assertions

-- This way of writing assertions can be a little bit heavy, for two reasons:
-- (1) every single assertion that we ever write is going to begin with
-- `fun st => `; and (2) this state `st` is the only one that we ever use to
-- look up variables in assertions (we will almost never need to talk about
-- two different memory states at the same time). For discussing examples
-- informally, we'll adopt some simplifying conventions: we'll drop the
-- initial `fun st =>`, and we'll write just `X` to mean `st[X]`. Thus,
-- instead of writing

--   fun st => st[X] = m

-- we'll write just

--   {{ X = m }}.

-- Here the "doubly curly" braces `{{` and `}}` delimit the scope of an
-- assertion. We'll see more examples below.

-- This example also illustrates a convention that we'll use throughout the
-- Hoare Logic chapters: in informal assertions, capital letters like `X`,
-- `Y`, and `Z` are Imp variables, while lowercase letters like `x`, `y`, `m`,
-- and `n` are ordinary Lean variables (of type `Nat`). This is why, when
-- translating from informal to formal, we replace `X` with `st[X]` but leave
-- `m` alone.

-- The convention described above can be implemented with a little syntax
-- magic, using coercions and a custom grammar, much as we did with the
-- `imp { … }` notation in Imp. This new notation automatically lifts `Aexp`s,
-- numbers, and `Prop`s into `Assertion`s when they appear between the
-- `{{ _ }}` brackets, or when Lean knows that the type of an expression is
-- `Assertion`.

-- There is no need to understand the details of how these notations work.

-- THESE DETAILS CAN BE SKIPPED: Notation: Assertions

namespace Assertion

section
open Lean Elab Term

scoped syntax:max (name := assn) "assn(" ident "; " term ")" : term
scoped syntax:lead "{{" term "}}" : term

@[term_elab assn]
def assnElab : TermElab := fun stx _type? => do
  match stx with
  | `(assn($st; $t:term)) =>
    let t ← elabTerm t none
    let ty ← Meta.inferType t
    -- if (← Meta.isDefEq ty (mkConst ``_root_.Ident)) then -- this incorrectly assigns metavariables
    if (ty.constName == ``_root_.Ident) then
      return mkApp6 (mkConst ``_root_.MyGetElem.getElem)
        (mkApp2 (mkConst ``TotalMap) (mkConst ``String) (mkConst ``Nat))
        (mkConst ``String)
        (mkConst ``Nat)
        (← Meta.synthInstance <| mkApp3 (mkConst ``_root_.MyGetElem)
          (mkApp2 (mkConst ``TotalMap) (mkConst ``String) (mkConst ``Nat))
          (mkConst ``String)
          (mkConst ``Nat))
        (← elabTerm st none) t
    if (ty.constName == ``_root_.Aexp) then -- Detect an embedded `Aexp` and turn it into `Aexp.eval st t`
      return (mkApp2 (mkConst ``Aexp.eval) (← elabTerm st none) t)
    else if (ty.constName == ``_root_.Bexp) then  -- Detect an embedded `Bexp` and turn it into `Bexp.eval st t`
      return (mkApp2 (mkConst ``Bexp.eval) (← elabTerm st none) t)
    else if ty.isMVar then -- This is a hack to guard against `Meta.isDefEq` assigning the type to be an `Assertion`
      return t
    else if (← Meta.isDefEq ty (mkConst ``_root_.Assertion)) then
      return mkApp t (← elabTerm st none)
    else
      return t
  | _ => throwUnsupportedSyntax

-- `: Assertion` guards that the resulting type is `State → Prop`.
macro_rules
  | `({{ $t }}) => `((fun st : _root_.State => assn(st; $t) : Assertion))

macro_rules
  | `(assn($st; ($P))) => ``((assn($st; $P)))
  | `(assn($st; $l = $r)) => ``(assn($st; $l) = assn($st; $r))
  | `(assn($st; $l + $r)) => ``(assn($st; $l) + assn($st; $r))
  | `(assn($st; $l - $r)) => ``(assn($st; $l) - assn($st; $r))
  | `(assn($st; $l * $r)) => ``(assn($st; $l) * assn($st; $r))
  | `(assn($st; $l ≤ $r)) => ``(assn($st; $l) ≤ assn($st; $r))
  | `(assn($st; $l < $r)) => ``(assn($st; $l) < assn($st; $r))
  | `(assn($st; $l ≥ $r)) => ``(assn($st; $l) ≥ assn($st; $r))
  | `(assn($st; $l > $r)) => ``(assn($st; $l) > assn($st; $r))
  | `(assn($st; $l ∧ $r)) => ``(assn($st; $l) ∧ assn($st; $r))
  | `(assn($st; $l ∨ $r)) => ``(assn($st; $l) ∨ assn($st; $r))
  | `(assn($st; $l → $r)) => ``(assn($st; $l) → assn($st; $r))
  | `(assn($st; $l ↔ $r)) => ``(assn($st; $l) ↔ assn($st; $r))
  | `(assn($st; ¬ $t)) => ``(¬ assn($st; $t))
  | `(assn($st; $f $args*)) => do
    let mut result := f
    for arg in args do
      result ← `($result assn($st; $arg))
    return result
end

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

-- END DETAILS

-- Function applications inside assertions automatically interpret their
-- arguments in the current state. Thus, `{{ f e1 ... en }}` stands for
-- `fun st => f (e1 st) ... (en st)`.

-- Occasionally it is simpler to write an assertion directly as a Lean
-- function. Such a function can be placed inside the assertion notation
-- without an escape marker.

-- For example, `{{ fun st => ∀ x, st[x] = 0 }}` indicates an assertion that
-- every variable maps to `0` in the given state.

-- ### Example Assertions

-- Here are some example assertions that take advantage of this new notation.

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

-- ### Printing Assertions

-- As in the Imp chapter, the assertion notation above is *input* only: Lean
-- reads `{{ X ≤ 5 }}` but still prints the underlying function, as
-- `#print assertion8` just showed. The delaborators below close the loop for
-- plain assertions: a state lambda whose body Lean can rebuild is printed
-- back in `{{ … }}` notation, and an assertion Lean cannot rebuild falls back
-- to the raw `fun st => …` form, which is exactly this notation's escape
-- syntax, so what you see is always valid input. Each time a new notation
-- involving assertions appears below (implication, Hoare triples,
-- substitution), a small delaborator defined next to it will extend this
-- printing to cover it. As before, there is no need to understand the
-- details.

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: printing assertions back

namespace Assertion.Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab

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
      withNaryArg 5 delab
    | Aexp.eval st _ =>
      guard (st == .fvar stId)
      withAppArg delab
    | HAdd.hAdd _ _ _ _ _ _ =>
      `($(← withNaryArg 4 (delabBody stId)) + $(← withNaryArg 5 (delabBody stId)))
    | HSub.hSub _ _ _ _ _ _ =>
      `($(← withNaryArg 4 (delabBody stId)) - $(← withNaryArg 5 (delabBody stId)))
    | HMul.hMul _ _ _ _ _ _ =>
      `($(← withNaryArg 4 (delabBody stId)) * $(← withNaryArg 5 (delabBody stId)))
    | Eq _ l r =>
      -- `Bexp.eval st b = true` is the threaded form of a bare boolean `b`
      if r.isConstOf ``Bool.true && l.isAppOfArity ``Bexp.eval 2
          && l.appFn!.appArg! == .fvar stId then
        withNaryArg 1 <| withAppArg delab
      else
        `($(← withNaryArg 1 (delabBody stId)) = $(← withNaryArg 2 (delabBody stId)))
    | Ne _ _ _ =>
      `($(← withNaryArg 1 (delabBody stId)) ≠ $(← withNaryArg 2 (delabBody stId)))
    | LE.le _ _ _ _ =>
      `($(← withNaryArg 2 (delabBody stId)) ≤ $(← withNaryArg 3 (delabBody stId)))
    | LT.lt _ _ _ _ =>
      `($(← withNaryArg 2 (delabBody stId)) < $(← withNaryArg 3 (delabBody stId)))
    | GE.ge _ _ _ _ =>
      `($(← withNaryArg 2 (delabBody stId)) ≥ $(← withNaryArg 3 (delabBody stId)))
    | GT.gt _ _ _ _ =>
      `($(← withNaryArg 2 (delabBody stId)) > $(← withNaryArg 3 (delabBody stId)))
    | And _ _ =>
      `($(← withNaryArg 0 (delabBody stId)) ∧ $(← withNaryArg 1 (delabBody stId)))
    | Or _ _ =>
      `($(← withNaryArg 0 (delabBody stId)) ∨ $(← withNaryArg 1 (delabBody stId)))
    | Iff _ _ =>
      `($(← withNaryArg 0 (delabBody stId)) ↔ $(← withNaryArg 1 (delabBody stId)))
    | Not _ =>
      `(¬ $(← withAppArg (delabBody stId)))
    | _ =>
      if e.isArrow then
        `($(← withBindingDomain (delabBody stId)) →
          $(← withBindingBody `h (delabBody stId)))
      else if let .app f v := e then
        -- an applied assertion `P st` (or an applied escape lambda)
        guard (v == .fvar stId)
        guard !(f.containsFVar stId)
        withAppFn delab
      else
        failure

/-- Print an `Assertion`-valued term as it appears inside `{{ … }}`: a
state lambda is un-threaded; a term the printer cannot rebuild falls back
to the raw lambda, which is exactly this notation's escape form. -/
partial def delabAssn : DelabM Term := do
  if (← getExpr).isLambda then
    (withBindingBody' `st (pure ·.fvarId!) fun stId => delabBody stId)
      <|> Delaborator.delab
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

-- END DETAILS

-- ### Assertion Implication

-- Given two assertions `P` and `Q`, we say that `P` *implies* `Q`, written
-- `P ->> Q`, if, whenever `P` holds in some state `st`, `Q` also holds.

def AssertImplies (P Q : Assertion) : Prop :=
  ∀ st, P st → Q st

-- Note that the notation for *assertion implication* is analogous to the
-- "usual" Lean implication `→`.

notation:26 P:27 " ->> " Q:27 => AssertImplies P Q

theorem assertImplies_def {P Q : Assertion} : P ->> Q ↔ ∀ st, P st → Q st := by rfl

-- We'll also want the "iff" variant of implication between assertions:

notation:26 P:27 " <<->> " Q:27 => AssertImplies P Q ∧ AssertImplies Q P

theorem assertIff_def {P Q : Assertion} : P <<->> Q ↔ AssertImplies P Q ∧ AssertImplies Q P
    := by rfl

-- The matching delaborators print implications and equivalences between
-- assertions back in `->>` and `<<->>` notation.

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: printing implications back

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

-- END DETAILS

-- ## Hoare Triples, Informally

-- A *Hoare triple* is a claim about the state before and after executing a
-- command. A commond notation for Hoare triples, and the one we use in this
-- book, is

--   {{P}} c {{Q}}

-- meaning:

-- - If command `c` begins execution in a state satisfying assertion `P`,
-- - and if `c` eventually terminates in some final state,
-- - then that final state will satisfy the assertion `Q`.

-- Assertion `P` is called the *precondition* of the triple, and `Q` is the
-- *postcondition*.

-- For example,

-- - The Hoare triple

--   {{X = 0}} X := X + 1 {{X = 1}}

-- states that command `X := X + 1` will transform a state in which `X = 0` to
-- a state in which `X = 1`.

-- - On the other hand,

--   ∀ m, {{X = m}} X := X + 1 {{X = m + 1}}

-- is a *proposition* stating that the Hoare triple
-- `{{X = m}} X :=
-- X + 1 {{X = m + 1}}` is valid for any choice of `m`. Note
-- that `m` in the two assertions is a reference to the *Lean* variable `m`,
-- which is bound outside the Hoare triple.

-- _Quiz:_

-- Paraphrase the following in English.

--   1) {{True}} c {{X = 5}}

--   2) ∀ m, {{X = m}} c {{X = m + 5}}

--   3) {{X ≤ Y}} c {{Y ≤ X}}

--   4) {{True}} c {{False}}

--   5) ∀ m,
--        {{X = m}}
--        c
--        {{Y = real_fact m}}

--   6) ∀ m,
--        {{X = m}}
--        c
--        {{(Z * Z) ≤ m ∧ ¬ ((Z + 1) * (Z + 1) ≤ m)}}

-- _Quiz:_

-- Is the following Hoare triple *valid* -- i.e., is the claimed relation
-- between `P`, `c`, and `Q` true?

--   {{True}} X := 5 {{X = 5}}

-- (A) Yes

-- (B) No

-- _Quiz:_

-- What about this one?

--   {{X = 2}} X := X + 1 {{X = 3}}

-- (A) Yes

-- (B) No

-- _Quiz:_

-- What about this one?

--   {{True}} X := 5; Y := 0 {{X = 5}}

-- (A) Yes

-- (B) No

-- _Quiz:_

-- What about this one?

--   {{X = 2 ∧ X = 3}} X := 5 {{X = 0}}

-- (A) Yes

-- (B) No

-- _Quiz:_

-- What about this one?

--   {{True}} skip {{False}}

-- (A) Yes

-- (B) No

-- _Quiz:_

-- What about this one?

--   {{False}} skip {{True}}

-- (A) Yes

-- (B) No

-- _Quiz:_

-- What about this one?

--   {{True}} while true do skip end {{False}}

-- (A) Yes

-- (B) No

-- _Quiz:_

-- This one?

--   {{X = 0}}
--     while X = 0 do X := X + 1 end
--   {{X = 1}}

-- (A) Yes

-- (B) No

-- _Quiz:_

-- This one?

--   {{X = 1}}
--     while X ≠ 0 do X := X + 1 end
--   {{X = 100}}

-- (A) Yes

-- (B) No

-- ### Exercise (1 star): valid_triples ⭐

-- Which of the following Hoare triples are *valid* -- i.e., the claimed
-- relation between `P`, `c`, and `Q` is true?

--   1) {{True}} X := 5 {{X = 5}}

--   2) {{X = 2}} X := X + 1 {{X = 3}}

--   3) {{True}} X := 5; Y := 0 {{X = 5}}

--   4) {{X = 2 ∧ X = 3}} X := 5 {{X = 0}}

--   5) {{True}} skip {{False}}

--   6) {{False}} skip {{True}}

--   7) {{True}} while true do skip end {{False}}

--   8) {{X = 0}}
--       while X = 0 do X := X + 1 end
--     {{X = 1}}

--   9) {{X = 1}}
--       while X ≠ 0 do X := X + 1 end
--     {{X = 100}}

-- ## Hoare Triples, Formally

-- We formalize valid Hoare triples in Lean as follows:

open scoped HasEval

def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st st' : State},
    (st =[ c ]=> st') →
    P st →
    Q st'

-- Notation for Hoare triples. The command between the two assertions is
-- parsed with the same grammar as the `imp { … }` notation, so a command that
-- is a Lean variable (rather than concrete syntax) is spliced in with `~c`,
-- just as in the `st =[ c ]=> st'` notation.

class HasTriple (Com : Type) where
  Triple : Assertion → Com → Assertion → Prop

namespace HasTriple

/-- Hoare triple: `{{ P }} c {{ Q }}` -/
scoped notation:lead "{{" P "}} " c:lead " {{" Q "}}" => Triple ({{ P }}) c ({{ Q }})

/-- Hoare triple with `imp_com` command syntax -/
scoped syntax:lead (priority := high) "{{" term "}} " imp_com:lead " {{" term "}}" : term
scoped macro_rules
  | `({{ $P }} $c:imp_com {{ $Q }}) =>
      ``(HasTriple.Triple ({{ $P }}) (imp { $c }) ({{ $Q }}))
end HasTriple

instance : HasTriple Com where
  Triple := ValidHoareTriple

open scoped HasTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st st' : State},
      (st =[ c ]=> st') →
      P st →
      Q st' := by rfl

attribute [irreducible] ValidHoareTriple

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: printing triples back

-- The delaborator is agnostic to the command type: it prints the command with
-- whatever printer is registered for its constructors and splices the result
-- into the triple, so a language-extension chapter only has to register a
-- printer for its own `Com`.

namespace Assertion.Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab
@[delab app.HasTriple.Triple]
def delabTriple : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``HasTriple.Triple 5
  let P ← withNaryArg 2 delabAssn
  let c ← withNaryArg 3 delab
  let Q ← withNaryArg 4 delabAssn
  match c with
  | `(imp { $c:imp_com }) => ``({{ $P }} $c:imp_com {{ $Q }})
  | c => ``({{ $P }} ~$c {{ $Q }})

end Assertion.Delab

-- END DETAILS

-- ### Exercise (1 star): hoare_post_true ⭐

-- Prove that if `Q` holds in every state, then any triple with `Q` as its
-- postcondition is valid.

theorem hoare_post_true {P Q : Assertion} {c : Com} (h : ∀ st, Q st) :
    {{ P }} ~c {{ Q }} := by
  sorry

-- ### Exercise (1 star): hoare_pre_false ⭐

-- Prove that if `P` holds in no state, then any triple with `P` as its
-- precondition is valid.

theorem hoare_pre_false {P Q : Assertion} {c : Com} (h : ∀ st, ¬ (P st)) :
    {{ P }} ~c {{ Q }} := by
  sorry

-- ## Proof Rules

-- The goal of Hoare logic is to provide a *compositional* method for proving
-- the validity of specific Hoare triples. That is, we want the structure of a
-- program's correctness proof to mirror the structure of the program itself.
-- To this end, in the sections below, we'll introduce a rule for reasoning
-- about each of the different syntactic forms of commands in Imp -- one for
-- assignment, one for sequencing, one for conditionals, etc. -- plus a couple
-- of "structural" rules for gluing things together. We will then be able to
-- prove programs correct using these proof rules, without ever unfolding the
-- definition of `ValidHoareTriple`.

-- ### Skip

-- Since `skip` doesn't change the state, it preserves any assertion `P`:

--   --------------------  (hoare_skip)
--   {{ P }} skip {{ P }}

theorem hoare_skip {P : Assertion} :
    {{ P }} skip {{ P }} := by
  rw [validHoareTriple_def]
  intro st st' h hpre
  inversion h
  exact hpre

-- ### Sequencing

-- If command `c1` takes any state where `P` holds to a state where `Q` holds,
-- and if `c2` takes any state where `Q` holds to one where `R` holds, then
-- doing `c1` followed by `c2` will take any state where `P` holds to one
-- where `R` holds:

--    {{ P }} c1 {{ Q }}
--    {{ Q }} c2 {{ R }}
--   ----------------------  (hoare_seq)
--   {{ P }} c1; c2 {{ R }}

theorem hoare_seq {P Q R : Assertion} {c1 c2 : Com}
    (h1 : {{ Q }} ~c2 {{ R }}) (h2 : {{ P }} ~c1 {{ Q }}) :
    {{ P }} ~c1; ~c2 {{ R }} := by
  rw [validHoareTriple_def]
  intro st st' h hpre
  inversion h with
  | seq st'' hc1 hc2 =>
    rw [validHoareTriple_def] at h1 h2
    exact h1 hc2 (h2 hc1 hpre)

-- Note that, in the formal rule `hoare_seq`, the premises are given in
-- backwards order (`c2` before `c1`). This matches the natural flow of
-- information in many of the situations where we'll use the rule, since the
-- natural way to construct a Hoare-logic proof is to begin at the end of the
-- program (with the final postcondition) and push postconditions backwards
-- through commands until we reach the beginning.

-- ### Assignment

-- The rule for assignment is the most fundamental of the Hoare logic proof
-- rules. Here's how it works.

-- Consider this incomplete Hoare triple:

--   {{ ??? }}  X := Y  {{ X = 1 }}

-- We want to assign `Y` to `X` and finish in a state where `X` is `1`. What
-- could the precondition be?

-- One possibility is `Y = 1`, because if `Y` is already `1` then assigning it
-- to `X` causes `X` to be `1`. That leads to a valid Hoare triple:

--   {{ Y = 1 }}  X := Y  {{ X = 1 }}

-- It may seem as though coming up with that precondition must have taken some
-- clever thought. But there is a mechanical way we could have done it: if we
-- take the postcondition `X = 1` and in it replace `X` with `Y`---that is,
-- replace the left-hand side of the assignment statement with the right-hand
-- side---we get the precondition, `Y = 1`.

-- That same idea works in more complicated cases. For example:

--   {{ ??? }}  X := X + Y  {{ X = 1 }}

-- If we replace the `X` in `X = 1` with `X + Y`, we get `X + Y = 1`. That
-- again leads to a valid Hoare triple:

--   {{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}

-- Why does this technique work? The postcondition identifies some property
-- `P` that we want to hold of the variable `X` being assigned. In this case,
-- `P` is "equals `1`". To complete the triple and make it valid, we need to
-- identify a precondition that guarantees that property will hold of `X`.
-- Such a precondition must ensure that the same property holds of *whatever
-- is being assigned to* `X`. So, in the example, we need "equals `1`" to hold
-- of `X + Y`. That's exactly what the technique guarantees.

-- In general, the postcondition could be some arbitrary assertion `Q`, and
-- the right-hand side of the assignment could be some arbitrary arithmetic
-- expression `a`:

--   {{ ??? }}  X := a  {{ Q }}

-- The precondition would then be `Q`, but with any occurrences of `X` in it
-- replaced by `a`.

-- Let's introduce a notation for this idea of replacing occurrences: Define
-- `Q \[X ↦ a`] to mean "`Q` where `a` is substituted in place of `X`".

-- This yields the Hoare logic rule for assignment:

--   {{ Q [X ↦ a] }}  X := a  {{ Q }}

-- One way of reading this rule is: If you want statement `X := a` to
-- terminate in a state that satisfies assertion `Q`, then it suffices to
-- start in a state that also satisfies `Q`, except where `a` is substituted
-- for every occurrence of `X`.

-- To many people, this rule seems "backwards" at first, because it proceeds
-- from the postcondition to the precondition. Actually it makes good sense to
-- go in this direction: the postcondition is often what is more important,
-- because it characterizes what will be true after running the code.

-- Nonetheless, it's also possible to formulate a "forward" assignment rule.
-- We'll do that later in some exercises.

-- Here are some valid instances of the assignment rule:

--   {{ (X ≤ 5) [X ↦ X + 1] }}         (that is, X + 1 ≤ 5)
--     X := X + 1
--   {{ X ≤ 5 }}

--   {{ (X = 3) [X ↦ 3] }}              (that is, 3 = 3)
--     X := 3
--   {{ X = 3 }}

--   {{ (0 ≤ X ∧ X ≤ 5) [X ↦ 3] }}.  (that is, 0 ≤ 3 ∧ 3 ≤ 5)
--     X := 3
--   {{ 0 ≤ X ∧ X ≤ 5 }}

-- To formalize the rule, we must first formalize the idea of "substituting an
-- expression for an Imp variable in an assertion", which we refer to as
-- assertion substitution, or `Assertion.subst`.

-- Intuitively, given a proposition `P`, a variable `X`, and an arithmetic
-- expression `a`, we want to derive another proposition `P'` that is just the
-- same as `P` except that `P'` should mention `a` wherever `P` mentions `X`.

-- This operation is related to the idea of substituting Imp expressions for
-- Imp variables that we saw in *Equiv* (`subst_aexp` and friends). The
-- difference is that, here, `P` is an arbitrary Lean assertion, so we can't
-- directly "edit" its text.

-- However, we can achieve the same effect by evaluating `P` in an updated
-- state, defined as follows:

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

-- This notation allows us to write this operation as:

--   P [ X ↦ a ]

#check (fun st => Assertion.subst X (aexp { 2 * X }) ({{ X ≤ 10 }}) st)
#check {{ (X ≤ 10) [X ↦ 2 * X] }}
#check (∀ st, ({{ (X ≤ 10) [X ↦ 2 * X] }}) st)

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: printing substitutions back

namespace Assertion.Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab

/-- Print an `Assertion.subst` back in `P [x ↦ a]` notation.  Emits the
bare inside-the-braces form: the generic application case of `delabBody`
picks it up inside an assertion body, and the enclosing printer supplies
the single pair of braces. -/
@[delab app.Assertion.subst]
def delabSub : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``Assertion.subst 3
  let `($x:ident) ← withNaryArg 0 delab | failure
  let a ← withNaryArg 1 delabAexpInner
  if (← withNaryArg 2 getExpr).isLambda then
    `(($(← withNaryArg 2 delabAssn)) [$x:ident ↦ $a:imp_aexp])
  else
    match ← withNaryArg 2 delab with
    | `($P:ident) => `($P:ident [$x:ident ↦ $a:imp_aexp])
    | P => `(($P) [$x:ident ↦ $a:imp_aexp])

end Assertion.Delab

-- END DETAILS

-- That is, `P [X ↦ a]` stands for an assertion -- let's call it `P'` -- that
-- behaves just like `P` except that, wherever `P` looks up the variable `X`
-- in the current state, `P'` instead uses the value of the expression `a`.

-- To see how this works in more detail, let's calculate what happens with a
-- couple of examples. First, suppose `P'` is `(X ≤ 5) [X ↦ 3]` -- that is,
-- more formally, `P'` is the Lean expression

--   fun st =>
--     (fun st' => st'[X] ≤ 5)
--     (X →ₜ Aexp.eval st 3 ; st),

-- which simplifies to

--   fun st =>
--     (fun st' => st'[X] ≤ 5)
--     (X →ₜ 3 ; st)

-- and further simplifies to

--   fun st =>
--     ((X →ₜ 3 ; st)[X]) ≤ 5

-- and finally to

--   fun st =>
--     3 ≤ 5.

-- That is, `P'` is the assertion that `3` is less than or equal to `5` (as
-- expected).

-- For a more interesting example, suppose `P'` is `(X ≤ 5) [X ↦
-- X + 1]`.
-- Formally, `P'` is the Lean expression

--   fun st =>
--     (fun st' => st'[X] ≤ 5)
--     (X →ₜ Aexp.eval st (aexp { X + 1 }) ; st),

-- which simplifies to

--   fun st =>
--     (X →ₜ Aexp.eval st (aexp { X + 1 }) ; st)[X] ≤ 5

-- and further simplifies to

--   fun st =>
--     (Aexp.eval st (aexp { X + 1 })) ≤ 5.

-- That is, `P'` is the assertion that `X + 1` is at most `5`.

-- We can demonstrate formally that we have captured intuitive meaning of
-- "assertion subsitution" by proving some example logical equivalences:

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

-- Most of the `simp` calls rely on `Assertion.subst_apply`,
-- `TotalMap.update_eq` plus some `Aexp` characterizing lemmas like
-- `Aexp.eval_num`.

-- Now, using the substitution operation we've just defined, we can give the
-- precise proof rule for assignment:

--   ---------------------------- (hoare_asgn)
--   {{Q [X ↦ a]}} X := a {{Q}}

-- We can prove formally that this rule is indeed valid.

theorem hoare_asgn {Q : Assertion} {x : Ident} {a : Aexp} :
    {{ Q [x ↦ ~a] }} x := ~a {{ Q }} := by
  rw [validHoareTriple_def]
  intro st st' hE hQ
  inversion hE with
  | asgn n h =>
    subst h
    rw [Assertion.subst_def] at hQ
    exact hQ

-- Here's a first formal proof of a Hoare triple using this rule.

theorem assertion_sub_example :
    {{ (X < 5) [X ↦ X + 1] }}
      X := X + 1
    {{ X < 5 }} := by
  exact hoare_asgn

-- Of course, we'd probably prefer to work with this simpler triple:

--   {{X < 4}} X := X + 1 {{X < 5}}

-- We will see how to do so in the next section.

-- Several proofs below use the facts about total-map updates proved in the
-- *Typeclasses* chapter -- `TotalMap.update_eq`, `TotalMap.update_neq`,
-- `TotalMap.update_shadow`, `TotalMap.update_same`, and
-- `TotalMap.update_permute`. Make sure you understand their statements.

-- Complete these Hoare triples by providing an appropriate precondition using
-- `exists`, then prove then with `apply
-- hoare_asgn`. If you find that tactic
-- doesn't suffice, double check that you have completed the triple properly.

-- ### Exercise (2 stars): hoare_asgn_examples1 ⭐⭐

theorem hoare_asgn_examples1 :
    ∃ P : Assertion,
      {{ P }}
        X := 2 * X
      {{ X ≤ 10 }} := by
  sorry

-- ### Exercise (2 stars): hoare_asgn_examples2 ⭐⭐

theorem hoare_asgn_examples2 :
    ∃ P : Assertion,
      {{ P }}
        X := 3
      {{ 0 ≤ X ∧ X ≤ 5 }} := by
  sorry

-- ### Exercise (2 stars): hoare_asgn_wrong ⭐⭐

-- The assignment rule looks backward to almost everyone the first time they
-- see it. If it still seems puzzling to you, it may help to think a little
-- about alternative "forward" rules. Here is a seemingly natural one:

--   ------------------------------ (hoare_asgn_wrong)
--   {{ True }} X := a {{ X = a }}

-- Give a counterexample showing that this rule is incorrect and use it to
-- complete the proof below, showing that it is really a counterexample.
-- (Hint: The rule universally quantifies over the arithmetic expression `a`,
-- so your counterexample needs to exhibit an `a` for which the rule doesn't
-- work.)

theorem hoare_asgn_wrong : ∃ a : Aexp,
    ¬ {{ True }} X := ~a {{ X = a }} := by
  sorry

-- ### Exercise (3 stars): hoare_asgn_fwd (Advanced) ⭐⭐⭐

-- By using a *parameter* `m` (a Lean number) to remember the original value
-- of `X` we can define a Hoare rule for assignment that does, intuitively,
-- "work forwards" rather than backwards.

--   ------------------------------------------ (hoare_asgn_fwd)
--   {{fun st => P st ∧ st[X] = m}}
--     X := a
--   {{fun st => P (X →ₜ m ; st) ∧ st[X] = Aexp.eval (X →ₜ m ; st) a }}

-- Note that we need to write out the postcondition in "desugared" form,
-- because it needs to talk about two different states: we use the original
-- value of `X` to reconstruct the state `st'` before the assignment took
-- place. (Also note that this rule is more complicated than `hoare_asgn`!)

-- Prove that this rule is correct.

theorem hoare_asgn_fwd {m : Nat} {a : Aexp} {P : Assertion} :
    {{ P ∧ X = m }}
      X := ~a
    {{ fun st => P (X →ₜ m ; st)
         ∧ st[X] = a.eval (X →ₜ m ; st) }} := by
  sorry

-- ### Exercise (2 stars): hoare_asgn_fwd_exists (Advanced) ⭐⭐

-- Another way to define a forward rule for assignment is to existentially
-- quantify over the previous value of the assigned variable. Prove that it is
-- correct.

--   ------------------------------------ (hoare_asgn_fwd_exists)
--   {{fun st => P st}}
--     X := a
--   {{fun st => ∃ m, P (X →ₜ m ; st) ∧
--                  st[X] = Aexp.eval (X →ₜ m ; st) a }}

theorem hoare_asgn_fwd_exists (a : Aexp) (P : Assertion) :
    {{ P }}
      X := ~a
    {{ fun st => ∃ m, P (X →ₜ m ; st) ∧
         st[X] = a.eval (X →ₜ m ; st) }} := by
  sorry

-- ### Consequence

-- Sometimes the preconditions and postconditions we get from the Hoare rules
-- won't quite be the ones we want in the particular situation at hand -- they
-- may be logically equivalent but have a different syntactic form that fails
-- to unify with the goal we are trying to prove, or they actually may be
-- logically weaker (for preconditions) or stronger (for postconditions) than
-- what we need.

-- For instance,

--   {{(X = 3) [X ↦ 3]}} X := 3 {{X = 3}},

-- follows directly from the assignment rule, but

--   {{True}} X := 3 {{X = 3}}

-- does not. This triple is valid, but it is not an instance of `hoare_asgn`
-- because `True` and `(X = 3) \[X ↦ 3`] are not syntactically equal
-- assertions.

-- However, they are logically *equivalent*, so if one triple is valid, then
-- the other must certainly be as well. We can capture this observation with
-- the following rule:

--      {{P'}} c {{Q}}
--        P <<->> P'
--   ---------------------
--      {{P}} c {{Q}}

-- Taking this line of thought a bit further, we can see that strengthening
-- the precondition or weakening the postcondition of a valid triple always
-- produces another valid triple. This observation is captured by two *Rules
-- of Consequence*.

--          {{P'}} c {{Q}}
--             P ->> P'
--   -----------------------------   (hoare_consequence_pre)
--          {{P}} c {{Q}}

--          {{P}} c {{Q'}}
--            Q' ->> Q
--   -----------------------------    (hoare_consequence_post)
--          {{P}} c {{Q}}

-- Here are the formal versions:

theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply hhoare heval
  rw [assertImplies_def] at himp
  exact himp _ hpre

theorem hoare_consequence_post {P Q Q' : Assertion} {c : Com}
    (hhoare : {{ P }} ~c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  rw [assertImplies_def] at himp
  apply himp
  exact hhoare heval hpre

-- For example, we can use the first consequence rule like this:

--   {{ True }} ->>
--   {{ (X = 1) [X ↦ 1] }}
--     X := 1
--   {{ X = 1 }}

-- Or, formally...

theorem hoare_asgn_example1 :
    {{True}} X := 1 {{X = 1}} := by
  all_goals
    apply hoare_consequence_pre (P' := {{ (X = 1) [X ↦ 1] }})
    · exact hoare_asgn
    · rw [assertImplies_def]
      intro st _
      simp

-- We can also use it to prove the example mentioned earlier.

--   {{ X < 4 }} ->>
--   {{ (X < 5)[X ↦ X + 1] }}
--     X := X + 1
--   {{ X < 5 }}

-- Or, formally ...

theorem assertion_sub_example2 :
    {{X < 4}}
      X := X + 1
    {{X < 5}} := by
  all_goals
    apply hoare_consequence_pre (P' := {{ (X < 5) [X ↦ X + 1] }})
    · exact hoare_asgn
    · rw [assertImplies_def]
      intro st h
      simp_all
      lia

-- Finally, here is a combined rule of consequence that allows us to vary both
-- the precondition and the postcondition.

--          {{P'}} c {{Q'}}
--             P ->> P'
--             Q' ->> Q
--   -----------------------------   (hoare_consequence)
--          {{P}} c {{Q}}

theorem hoare_consequence {P P' Q Q' : Assertion} {c : Com}
    (htriple : {{ P' }} ~c {{ Q' }}) (hpre : P ->> P') (hpost : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  apply hoare_consequence_pre (P' := P')
  · exact hoare_consequence_post htriple hpost
  · exact hpre

-- ### Automation

-- Many of the proofs we have done so far with Hoare triples can be
-- streamlined using the automation techniques that we introduced in the
-- *Automation* chapter of *Logical Foundations*.

-- Recall that `simp` rewrites with any lemmas we pass it. The definitions
-- whose meaning we keep needing to expose in this chapter --
-- `ValidHoareTriple`, `AssertImplies`, and `Assertion.subst` -- each come
-- with a characterizing lemma (`validHoareTriple_def`, `assertImplies_def`,
-- `Assertion.subst_def`) restating the definition as an equation. Passing
-- these lemmas to `simp` replaces the defined notions by their meanings
-- wherever they appear. We'll do that explicitly below (and shortly package
-- the recipe up as a tactic of our own).

-- Note to developers (Niklas Halonen @xhalo32, NOW):
--     The following paragraph is outdated.

-- The proof of `hoare_consequence_pre`, repeated below, looks like an
-- opportune place for automation, because all it does is `unfold`, `intro`,
-- and `apply`. (It uses `assumption`, too, but that's just application of a
-- hypothesis.)

--   theorem hoare_consequence_pre (P P' Q : Assertion) (c : Com)
--       (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
--       {{ P }} ~c {{ Q }} := by
--     rw [validHoareTriple_def] at hhoare ⊢
--     intro st st' heval hpre
--     apply hhoare heval
--     rw [assertImplies_def] at himp
--     exact himp _ hpre

-- Since `AssertImplies` is not marked `irreducible`, and `assertImplies_def`
-- is a proof by definitional equality, we can skip the
-- `rw [assertImplies_def] at himp` and use `P ->> P'` like an implication
-- directly.

theorem hoare_consequence_pre' (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply hhoare heval
  exact himp _ hpre

-- From now on, we will not usually rewrite `assertImplies_def` explicitly.

-- Since, after the `rw` and `intro`, the remaining steps just apply
-- hypotheses to the goal (and each other), the remaining proof can be
-- compressed into a single tactic: `apply_rules`.

theorem hoare_consequence_pre'' (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply_rules

-- The same trick works for `hoare_consequence_post`.

theorem hoare_consequence_post' (P Q Q' : Assertion) (c : Com)
    (hhoare : {{ P }} ~c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply_rules

-- We can also leave a metavariable for `P'` in `hoare_asgn_example1`, that we
-- did earlier as an example of using the consequence rule:

theorem hoare_asgn_example1' :
    {{True}} X := 1 {{X = 1}} := by
  apply hoare_consequence_pre -- not specifying `(P' := ...)` leaves a "hole" `?P'`
  · -- The goal is `{{?P'}} X := 1 {{X = 1}}`
    exact hoare_asgn -- Assigns `?P'` to `{{ (X = 1) [X ↦ 1] }}` (automatically closing `case P'`)
  · intro st _ -- Since `->>` is an implication, we can just use `intro` directly.
    simp

-- The final bullet of that proof also looks like a candidate for automation.

theorem hoare_asgn_example1'' :
    {{True}} X := 1 {{X = 1}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · simp [assertImplies_def]

-- Now we have quite a nice proof script: it simply identifies the Hoare rules
-- that need to be used and leaves the remaining low-level details up to Lean
-- to figure out.

-- By now it might be apparent that the *entire* proof could be automated by a
-- more ambitious tactic that also knew about the Hoare rules themselves. We
-- won't build one in this chapter, so that we can get a better understanding
-- of when and how the Hoare rules are used. In the next chapter, *Hoare2*,
-- we'll dive deeper into automating entire proofs of Hoare triples.

-- The other example of using consequence that we did earlier,
-- `hoare_asgn_example2`, requires a little more work to automate. `simp`
-- simplifies the assertion implication in the final bullet, but cannot finish
-- it: the leftover goal is arithmetic, so it needs `lia`.

theorem assertion_sub_example2' :
    {{X < 4}}
      X := X + 1
    {{X < 5}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · simp [assertImplies_def] -- an arithmetic goal remains
    lia

-- Let's introduce our own tactic to handle both that bullet and the bullet
-- from example 1. A `macro` declaration gives a name to a canned sequence of
-- tactics:

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

-- Again, we have quite a nice proof script. All the low-level details of
-- proofs about assertions have been taken care of automatically. Of course,
-- `assertion_auto` isn't able to prove everything we could possibly want to
-- know about assertions -- there's no magic here! But it's pretty good.

-- ### Exercise (2 stars): hoare_asgn_examples_2 ⭐⭐

-- Prove these triples. Try to make your proof scripts nicely automated by
-- following the examples above.

theorem assertion_sub_ex1' :
    {{ X ≤ 5 }}
      X := 2 * X
    {{ X ≤ 10 }} := by
  sorry

theorem assertion_sub_ex2' :
    {{ 0 ≤ 3 ∧ 3 ≤ 5 }}
      X := 3
    {{ 0 ≤ X ∧ X ≤ 5 }} := by
  sorry

-- ### Sequencing + Assignment

-- Here's an example of a program involving both sequencing and assignment.
-- Note the use of `hoare_seq` in conjunction with `hoare_consequence_pre` and
-- `apply`'s metavariables.

theorem hoare_asgn_example3 (a : Aexp) (n : Nat) :
    {{a = n}}
      X := ~a;
      skip
    {{X = n}} := by
  apply hoare_seq
  · -- right part of seq
    exact hoare_skip
  · -- left part of seq
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto

-- Informally, a nice way of displaying a proof using the sequencing rule is
-- as a "decorated program" where the intermediate assertion `Q` is written
-- between `c1` and `c2`:

--            {{ a = n }}
--   X := a
--            {{ X = n }};    <--- decoration for Q
--   skip
--            {{ X = n }}

-- We'll come back to the idea of decorated programs in much more detail in
-- the next chapter.

-- ### Exercise (2 stars): hoare_asgn_example4 ⭐⭐

-- Translate this "decorated program" into a formal proof:

--                  {{ True }} ->>
--                  {{ 1 = 1 }}
--   X := 1
--                  {{ X = 1 }} ->>
--                  {{ X = 1 ∧ 2 = 2 }};
--   Y := 2
--                  {{ X = 1 ∧ Y = 2 }}

-- Note the use of "`->>`" decorations, each marking a use of
-- `hoare_consequence_pre`.

-- We've started you off by providing a use of `hoare_seq` that explicitly
-- identifies `X = 1` as the intermediate assertion.

theorem hoare_asgn_example4 :
    {{ True }}
      X := 1;
      Y := 2
    {{ X = 1 ∧ Y = 2 }} := by
  apply hoare_seq (Q := {{ X = 1 }})
  · -- right part of seq
    sorry
  · -- left part of seq
    sorry

-- ### Exercise (3 stars): swap_exercise ⭐⭐⭐

-- Write an Imp program `c` that swaps the values of `X` and `Y` and show that
-- it satisfies the following specification:

--   {{X ≤ Y}} c {{Y ≤ X}}

-- Your proof should not need to use `rw [validHoareTriple_def]`.

-- Hints:

-- - Remember that Imp commands need to be enclosed in `imp { … }` brackets.

-- - Remember that the assignment rule works best when it's applied "back to
--   front," from the postcondition to the precondition. So your proof will want
--   to start at the end and work back to the beginning of your program.

-- - Remember that `apply` is your friend.)

def swap_program : Com := sorry

theorem swap_exercise :
    {{X ≤ Y}}
      ~swap_program
    {{Y ≤ X}} := by
  sorry

-- ### Exercise (4 stars): invalid_triple (Advanced) ⭐⭐⭐⭐

-- Show that

--   {{ a = n }} X := 3; Y := a {{ Y = n }}

-- is not a valid Hoare triple for some choices of `a` and `n`.

-- Conceptual hint: Invent a particular `a` and `n` for which the triple in
-- invalid, then use those to complete the proof.

-- Technical hint: Hypothesis `h` below begins `∀ a n, ...`. You'll want to
-- instantiate that with the particular `a` and `n` you've invented. You can
-- do that with `have` and `apply`, but you may remember (from the
-- *Automation* chapter of Logical Foundations) that Lean offers an even
-- easier tactic: `specialize`. If you write

--   specialize h your_a your_n

-- the hypothesis will be instantiated on `your_a` and `your_n`.

-- Having chosen your `a` and `n`, proceed as follows:

-- - Use the (assumed) validity of the given hoare triple to derive a state
--   `st'` in which `Y` has some value `y1`

-- - Use the evaluation rules (`Com.EvalR.seq` and `Com.EvalR.asgn`) to show
--   that `Y` has a *different* value `y2` in the same final state `st'`

-- - Since `y1` and `y2` are both equal to `st'[Y]`, they are equal to each
--   other. But we chose them to be different, so this is a contradiction, which
--   finishes the proof.

theorem invalid_triple : ¬ ∀ (a : Aexp) (n : Nat),
    {{ a = n }}
      X := 3; Y := ~a
    {{ Y = n }} := by
  intro h
  simp only [validHoareTriple_def] at h
  sorry

-- ### Conditionals

-- What sort of rule do we want for reasoning about conditional commands?

-- Certainly, if the same assertion `Q` holds after executing either of the
-- branches, then it holds after the whole conditional. So we might be tempted
-- to write:

--           {{P}} c1 {{Q}}
--           {{P}} c2 {{Q}}
--   ---------------------------------
--   {{P}} if b then c1 else c2 {{Q}}

-- However, this is rather weak. For example, using this rule, we cannot show

--   {{ True }}
--     if X = 0
--       then Y := 2
--       else Y := X + 1
--     end
--   {{ X ≤ Y }}

-- since the rule doesn't tell us enough about the state in which the
-- assignments take place in the "then" and "else" branches.

-- Fortunately, we can say something more precise. In the "then" branch, we
-- know that the boolean expression `b` evaluates to `true`, and in the "else"
-- branch, we know it evaluates to `false`. Making this information available
-- in the premises of the rule gives us more information to work with when
-- reasoning about the behavior of `c1` and `c2` (i.e., the reasons why they
-- establish the postcondition `Q`).

--   {{P ∧   b}} c1 {{Q}}
--   {{P ∧ ¬ b}} c2 {{Q}}
--   ------------------------------------  (hoare_if)
--   {{P}} if b then c1 else c2 end {{Q}}

theorem bexp_eval_false (b : Bexp) (st : State) (h : b.eval st = false) :
    ¬ ({{ b }}) st := by
  dsimp
  simp [h]

-- Here, we first reduce the expression to `¬Bexp.eval st b = true` with
-- `dsimp`, which is trivial after we instruct `simp` to rewrite `b.eval st`
-- to `false`.

-- Now we can formalize the Hoare proof rule for conditionals and prove it
-- correct.

-- The statement of the rule reads: given `htrue : {{ P ∧ b }} ~c1 {{Q}}` and
-- `hfalse : {{ P ∧ ¬b }} ~c2 {{Q}}`, we can conclude
-- `{{P}} if (~b) { ~c1 } else { ~c2 } {{Q}}`.

theorem hoare_if {P Q : Assertion} {b : Bexp} {c1 c2 : Com}
    (htrue : {{ P ∧ b }} ~c1 {{ Q }}) (hfalse : {{ P ∧ ¬ b }} ~c2 {{ Q }}) :
    {{ P }} if (~b) { ~c1 } else { ~c2 } {{ Q }} := by
  rw [validHoareTriple_def] at htrue hfalse ⊢
  intro st st' hE hpre
  inversion hE with
  | ifTrue hb hc1 =>
    exact htrue hc1 ⟨hpre, hb⟩
  | ifFalse hb hc =>
    rw [← Bool.not_eq_true] at hb
    exact hfalse hc ⟨hpre, hb⟩

-- #### Example

-- Here is a formal proof that the program we used to motivate the rule
-- satisfies the specification we wanted.

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

-- We can even shorten it a little bit more.

theorem if_example' :
    {{True}}
      if (X = 0) {
        Y := 2
      } else {
        Y := X + 1
      }
    {{X ≤ Y}} := by
  apply hoare_if <;> apply hoare_consequence_pre hoare_asgn (by assertion_auto)

-- ### Exercise (2 stars): if_minus_plus ⭐⭐

-- Prove the theorem below using `hoare_if`. Do not use unfold
-- `ValidHoareTriple`. The `assertion_auto` tactic we just defined may be
-- useful.

theorem if_minus_plus :
    {{True}}
      if (X ≤ Y) {
        Z := Y - X
      } else {
        Y := X + Z
      }
    {{Y = X + Z}} := by
  sorry

-- #### Exercise: One-sided conditionals

-- In this exercise we consider extending Imp with "one-sided conditionals" of
-- the form `if1 (b) { c }`. Here `b` is a boolean expression, and `c` is a
-- command. If `b` evaluates to `true`, then command `c` is evaluated. If `b`
-- evaluates to `false`, then `if1 (b) { c }` does nothing.

-- We recommend that you complete this exercise before attempting the ones
-- that follow, as it should help solidify your understanding of the material.

-- The first step is to extend the syntax of commands and introduce the usual
-- notations. (We've done this for you, in a separate namespace to prevent
-- polluting the global name space. The `scoped` notations below are active
-- only inside `namespace If1`.)

namespace If1

inductive Com : Type where
  | skip : Com
  | asgn : Ident → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | if1 : Bexp → Com → Com

/-- One-sided conditional -/
scoped syntax "if1 " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : imp_com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $c1; $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { if1 ($b) {$c} }) =>
    `(Com.if1 (bexp {$b}) (imp {$c}))
  | `(imp { ~$c }) =>
    pure c

-- The delaborators are re-instantiated the same way: the Imp printer is
-- parameterized over the namespace of the command constructors, so the
-- extended printer is that printer at `If1.Com` plus one case for `if1`.

-- THESE DETAILS CAN BE SKIPPED: Notation encoding: printing the extended commands back

namespace Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab

/-- Rebuild `imp_com` syntax from an `If1.Com` term. -/
partial def delabComInner : DelabM (TSyntax `imp_com) :=
  delabComInnerFor ``Com do
    let e ← getExpr
    guard <| e.isAppOfArity ``Com.if1 2
    let b ← withAppFn <| withAppArg delabBexpInner
    let c ← withAppArg If1.Delab.delabComInner
    `(imp_com| if1 ($b) {$c})

@[delab app.If1.Com.skip, delab app.If1.Com.asgn, delab app.If1.Com.seq,
  delab app.If1.Com.cond, delab app.If1.Com.whileDo, delab app.If1.Com.if1]
partial def delabCom : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Com.skip => true
    | Com.asgn _ _ => true
    | Com.seq _ _ => true
    | Com.cond _ _ _ => true
    | Com.whileDo _ _ => true
    | Com.if1 _ _ => true
    | _ => false
  match ← delabComInner with
  | `(imp_com| ~$e) => pure e
  | e => `(term| imp { $e })

end Delab

-- END DETAILS

-- ### Exercise (2 stars): if1_ceval ⭐⭐

-- Add two new evaluation rules to relation `Com.EvalR`, below, for `if1`. Let
-- the rules for `if` guide you.

inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} :
      EvalR (imp {skip}) st st
  | asgn {st : State} (a : Aexp) {n : Nat} (x : Ident) (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (x →ₜ n ; st)
  | seq {c1 c2 : Com} (st st' st'' : State)
      (h1 : EvalR c1 st st') (h2 : EvalR c2 st' st'') :
      EvalR (imp {~c1; ~c2}) st st''
  | ifTrue {st st' : State} (b : Bexp) {c1 c2 : Com} (hb : b.eval st = true)
      (hc : EvalR c1 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | ifFalse {st st' : State} (b : Bexp) {c1 c2 : Com} (hb : b.eval st = false)
      (hc : EvalR c2 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | whileFalse {b : Bexp} (st : State) (c : Com) (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c} }) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st st')
      (hloop : EvalR (imp {while (~b) {~c} }) st' st'') :
      EvalR (imp {while (~b) {~c} }) st st''
-- FILL IN HERE

instance : HasEval Com State State where
  Eval := Com.EvalR

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()

-- The following unit tests should be provable simply by applying your new
-- rules (plus `rfl` for the boolean side conditions) if you have defined them
-- correctly.

theorem if1true_test :
    ∅ =[ if1 (X = 0) { X := 1 } ]=> (X →ₜ 1) := by
  sorry

theorem if1false_test :
    (X →ₜ 2) =[ if1 (X = 0) { X := 1 } ]=> (X →ₜ 2) := by
  sorry

-- Now we have to repeat the definition and notation of Hoare triples, so that
-- they will use the updated `Com` type.

def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st st' : State},
    (st =[ c ]=> st') →
    P st →
    Q st'

instance : HasTriple Com where
  Triple := ValidHoareTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st st' : State},
      (st =[ c ]=> st') →
      P st →
      Q st' := by rfl

attribute [irreducible] ValidHoareTriple

-- ### Exercise (2 stars): hoare_if1 (manually graded) ⭐⭐

-- Invent a Hoare logic proof rule for `if1`. State and prove a theorem named
-- `hoare_if1` that shows the validity of your rule. Use `hoare_if` as a
-- guide. Try to invent a rule that is *complete*, meaning it can be used to
-- prove the correctness of as many one-sided conditionals as possible. Also
-- try to keep your rule *compositional*, meaning that any Imp command that
-- appears in a premise should syntactically be a part of the command in the
-- conclusion.

-- Hint: if you encounter difficulty getting Lean to parse part of your rule
-- as an assertion, try wrapping it in the `{{ … }}` brackets or adding a type
-- ascription. For example, if you want `e` to be parsed as an assertion,
-- write it as `(e : Assertion)`.

-- FILL IN HERE

-- For example (`hoare_if1_good`) your rule should be strong enough to show
-- the following Hoare triple is valid:

--   {{ X + Y = Z }}
--   if1 (Y ≠ 0) {
--     X := X + Y;
--   }
--   {{ X = Z }}

-- Before the next exercise, we need to restate the Hoare rules of consequence
-- (for preconditions) and assignment for the new `Com` type.

theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  exact hhoare heval (himp st hpre)

theorem hoare_asgn {Q : Assertion} {x : Ident} {a : Aexp} :
    {{Q [x ↦ ~a]}} x := ~a {{ Q }} := by
  rw [validHoareTriple_def]
  intro st st' heval hQ
  rw [Assertion.subst_apply] at hQ
  inversion heval with
  | asgn n h =>
    subst h
    exact hQ

-- ### Exercise (2 stars): hoare_if1_good ⭐⭐

-- Use your `if1` rule to prove the following (valid) Hoare triple.

-- Hint: `assertion_auto` will once again get you most but not all the way to
-- a completely automated proof. You can finish manually, or tweak the tactic
-- further.

-- Hint: If you see a message about failing to unify commands from the
-- top-level `Com` with commands from this namespace, it probably means you
-- are using a definition or theorem (e.g., `hoare_skip`) from above this
-- exercise without re-proving it for the new version of Imp with `if1`.

theorem hoare_if1_good :
    {{ X + Y = Z }}
      if1 (Y ≠ 0) {
        X := X + Y
      }
    {{ X = Z }} := by
  sorry

end If1

-- ### While Loops

-- The Hoare rule for `while` loops is based on the idea of a *command
-- invariant* (or just *invariant*): an assertion whose truth is guaranteed
-- after executing a command, assuming it is true before.

-- That is, an assertion `P` is a command invariant of `c` if

--   {{P}} c {{P}}

-- holds. Note that the command invariant might temporarily become false in
-- the middle of executing `c`, but by the end of `c` it must be restored.

-- As a first attempt at a `while` rule, we could try:

--          {{P}} c {{P}}
--   ---------------------------
--   {{P}} while b do c end {{P}}

-- This rule is valid: if `P` is a command invariant of `c`, as the premise
-- requires, then, no matter how many times the loop body executes, `P` is
-- going to be true when the loop finally finishes.

-- But the rule also omits two crucial pieces of information. First, the loop
-- terminates when `b` becomes false. So we can strengthen the postcondition
-- in the conclusion:

--           {{P}} c {{P}}
--   ---------------------------------
--   {{P}} while b do c end {{P ∧ ¬b}}

-- Second, the loop body will be executed only if `b` is true. So we can also
-- strengthen the precondition in the premise:

--         {{P ∧ b}} c {{P}}
--   --------------------------------- (hoare_while)
--   {{P}} while b do c end {{P ∧ ¬b}}

-- That is the Hoare `while` rule. Note how it combines aspects of `skip` and
-- conditionals:

-- - If the loop body executes zero times, the rule is like `skip` in that the
--   precondition survives to become (part of) the postcondition.

-- - Like a conditional, we can assume guard `b` holds on entry to the
--   subcommand.

theorem hoare_while {P : Assertion} {b : Bexp} {c : Com}
    (hhoare : {{P ∧ b}} ~c {{ P }}) :
    {{ P }} while (~b) { ~c } {{P ∧ ¬ b}} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  /- We proceed by induction on `heval`, because, in the "keep
  looping" case, its hypotheses talk about the whole loop instead
  of just `c`. We begin by generalizing over an
  arbitrary command, together with an equation remembering that the
  command is the original loop. The cases for commands other than
  `while` are dismissed because their equations are contradictory. -/
  generalize heq : (imp { while (~b) { ~c } }) = cmd at heval
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

-- We call `P` a *loop invariant* of `while b do c end` if

--   {{P ∧ b}} c {{P}}

-- is a valid Hoare triple.

-- This means that `P` will be true at the end of the loop body whenever the
-- loop body executes. If `P` contradicts `b`, this holds trivially since the
-- precondition is false.

-- For instance, `X = 0` is a loop invariant of

--   while X = 2 do X := 1 end

-- since the program will never enter the loop.

-- _Quiz:_

-- Is the assertion

--   Y = 0

-- a loop invariant of the following?

--   while X < 100 do X := X + 1 end

-- (A) Yes

-- (B) No

-- _Quiz:_

-- Is the assertion

--   X = 0

-- a loop invariant of the following?

--   while X < 100 do X := X + 1 end

-- (A) Yes

-- (B) No

-- _Quiz:_

-- Is the assertion

--   X < Y

-- a loop invariant of the following?

--   while true do X := X + 1; Y := Y + 1 end

-- (A) Yes

-- (B) No

-- _Quiz:_

-- Is the assertion

--   X = Y + Z

-- a loop invariant of the following?

--   while Y > 10 do Y := Y - 1; Z := Z + 1 end

-- (A) Yes

-- (B) No

-- The program

--   while Y > 10 do Y := Y - 1; Z := Z + 1 end

-- admits an interesting loop invariant:

--   X = Y + Z

-- Note that this doesn't contradict the loop guard but neither is it a
-- command invariant of

--   Y := Y - 1; Z := Z + 1

-- since, if X = 5, Y = 0 and Z = 5, running the command will set Y + Z to 6.
-- The loop guard `Y > 10` guarantees that this will not be the case. We will
-- see many such loop invariants in the following chapter.

theorem while_example :
    {{X ≤ 3}}
      while (X ≤ 2) {
        X := X + 1
      }
    {{X = 3}} := by
  apply hoare_consequence_post
  · apply hoare_while
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto
  · assertion_auto

-- _Quiz:_

-- Is the assertion

--   X > 0

-- a loop invariant of the following?

--   while X = 0 do X := X - 1 end

-- (A) Yes

-- (B) No

-- _Quiz:_

-- Is the assertion

--   X < 100

-- a loop invariant of the following?

--   while X < 100 do X := X + 1 end

-- (A) Yes

-- (B) No

-- _Quiz:_

-- Is the assertion

--   X > 10

-- a loop invariant of the following?

--   while X > 10 do X := X + 1 end

-- (A) Yes

-- (B) No

-- If the loop never terminates, any postcondition will work.

theorem always_loop_hoare (Q : Assertion) :
    {{True}} while (true) { skip } {{ Q }} := by
  apply hoare_consequence_post
  · apply hoare_while
    apply hoare_post_true
    intro st
    exact True.intro
  · intro st ⟨_, hguard⟩
    simp at hguard

-- Of course, this result is not surprising if we remember that the definition
-- of `ValidHoareTriple` asserts that the postcondition must hold *only* when
-- the command terminates. If the command doesn't terminate, we can prove
-- anything we like about the post-condition.

-- Hoare rules that specify what happens *if* commands terminate, without
-- proving that they do, are said to describe a logic of *partial*
-- correctness. It is also possible to give Hoare rules for *total*
-- correctness, which additionally specifies that commands must terminate.
-- Total correctness is out of the scope of this textbook.

-- #### Exercise: `repeat`

-- In this exercise, we'll add a new command to our language of commands:
-- `repeat { c } until (b)`. You will write the evaluation rule for `repeat`
-- and add a new Hoare rule to the language for programs involving it.

namespace RepeatExercise

inductive Com : Type where
  | skip : Com
  | asgn : Ident → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | repeatUntil : Com → Bexp → Com

-- `repeat` behaves like `while`, except that the loop guard is checked
-- *after* each execution of the body, with the loop repeating as long as the
-- guard stays *false*. Because of this, the body will always execute at least
-- once.

/-- Repeat loop -/
syntax "repeat" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") " until " "(" imp_bexp ")" : imp_com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $c1; $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { repeat {$c} until ($b) }) =>
    `(Com.repeatUntil (imp {$c}) (bexp {$b}))
  | `(imp { ~$c }) =>
    pure c

-- ### Exercise (4 stars): hoare_repeat (Advanced, manually graded) ⭐⭐⭐⭐

-- Add new rules for `repeat` to `Com.EvalR` below. You can use the rules for
-- `while` as a guide, but remember that the body of a `repeat` should always
-- execute at least once, and that the loop ends when the guard becomes true.

inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} :
      EvalR (imp {skip}) st st
  | asgn {st : State} (a : Aexp) {n : Nat} (x : Ident) (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (x →ₜ n ; st)
  | seq {c1 c2 : Com} (st st' st'' : State)
      (h1 : EvalR c1 st st') (h2 : EvalR c2 st' st'') :
      EvalR (imp {~c1; ~c2}) st st''
  | ifTrue {st st' : State} (b : Bexp) {c1 c2 : Com} (hb : b.eval st = true)
      (hc : EvalR c1 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | ifFalse {st st' : State} (b : Bexp) {c1 c2 : Com} (hb : b.eval st = false)
      (hc : EvalR c2 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | whileFalse {b : Bexp} (st : State) (c : Com) (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c} }) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st st')
      (hloop : EvalR (imp {while (~b) {~c} }) st' st'') :
      EvalR (imp {while (~b) {~c} }) st st''
-- FILL IN HERE

instance : HasEval Com State State where
  Eval := Com.EvalR

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()

-- A couple of definitions from above, copied here so they use the new
-- `Com.EvalR`.

def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st st' : State},
    (st =[ c ]=> st') →
    P st →
    Q st'

instance : HasTriple Com where
  Triple := ValidHoareTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st st' : State},
      (st =[ c ]=> st') →
      P st →
      Q st' := by rfl

attribute [irreducible] ValidHoareTriple

-- To make sure you've got the evaluation rules for `repeat` right, prove that
-- `ex1_repeat` evaluates correctly.

def ex1_repeat : Com :=
  imp {
    repeat {
      X := 1;
      Y := Y + 1
    } until (X = 1)
  }

theorem ex1_repeat_works :
    ∅ =[ ex1_repeat ]=> (Y →ₜ 1 ; X →ₜ 1) := by
  sorry

-- Now state and prove a theorem, `hoare_repeat`, that expresses an
-- appropriate proof rule for `repeat` commands. Use `hoare_while` as a model,
-- and try to make your rule as precise as possible.

-- FILL IN HERE

-- For full credit, make sure (informally) that your rule can be used to prove
-- the following valid Hoare triple:

--   {{ X > 0 }}
--   repeat {
--     Y := X;
--     X := X - 1;
--   } until (X = 0)
--   {{ X = 0 ∧ Y > 0 }}

-- FILL IN HERE

-- FILL IN HERE

-- FILL IN HERE
end RepeatExercise

-- ## Summary

-- So far, we've introduced Hoare Logic as a tool for reasoning about Imp
-- programs.

-- The rules of Hoare Logic are:

--          --------------------------- (hoare_asgn)
--          {{Q [X ↦ a]}} X:=a {{Q}}

--          --------------------  (hoare_skip)
--          {{ P }} skip {{ P }}

--            {{ P }} c1 {{ Q }}
--            {{ Q }} c2 {{ R }}
--           ----------------------  (hoare_seq)
--           {{ P }} c1;c2 {{ R }}

--           {{P ∧   b}} c1 {{Q}}
--           {{P ∧ ¬ b}} c2 {{Q}}
--   ------------------------------------  (hoare_if)
--   {{P}} if b then c1 else c2 end {{Q}}

--            {{P ∧ b}} c {{P}}
--     -----------------------------------  (hoare_while)
--     {{P}} while b do c end {{P ∧ ¬ b}}

--             {{P'}} c {{Q'}}
--                P ->> P'
--                Q' ->> Q
--      -----------------------------   (hoare_consequence)
--             {{P}} c {{Q}}

-- Our main task in this chapter has been to *define* the rules of Hoare
-- logic, and prove that the definitions are sound. Having done so, we can go
-- on and work *within* Hoare logic to prove that particular programs satisfy
-- particular Hoare triples. In the next chapter, we'll see how Hoare logic is
-- can be used to prove that more interesting programs satisfy interesting
-- specifications of their behavior.

-- Crucially, we will do so without ever again `unfold`ing the definition of
-- Hoare triples -- i.e., we will take the rules of Hoare logic as a closed
-- world for reasoning about programs.

-- ## Additional Exercises

-- ### Havoc

-- In this exercise, we will derive proof rules for a `havoc` command, which
-- is similar to the nondeterministic `any` expression from the the Imp
-- chapter.

-- First, we enclose this work in a separate namespace, and recall the syntax
-- and big-step semantics of Himp commands.

namespace Himp

inductive Com : Type where
  | skip : Com
  | asgn : Ident → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | havoc : Ident → Com

/-- Havoc: set a variable to a nondeterministically chosen number
(`havoc x;`).  As with `skip`, the word `havoc` is not reserved: the
production accepts any identifier and the macro below rejects
everything except `havoc`. -/
scoped syntax ident ident : imp_com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $c1; $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { $h:ident $x:ident }) =>
    if h.getId == `havoc then `(Com.havoc $x)
    else Macro.throwErrorAt h s!"expected 'havoc', got '{h.getId}'"
  | `(imp { ~$c }) =>
    pure c

inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} :
      EvalR (imp {skip}) st st
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (x →ₜ n ; st)
  | seq {c1 c2 : Com} {st st' st'' : State}
      (h1 : EvalR c1 st st') (h2 : EvalR c2 st' st'') :
      EvalR (imp {~c1; ~c2}) st st''
  | ifTrue {st st' : State} {b : Bexp} {c1 c2 : Com} (hb : b.eval st = true)
      (hc : EvalR c1 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | ifFalse {st st' : State} {b : Bexp} {c1 c2 : Com} (hb : b.eval st = false)
      (hc : EvalR c2 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c} }) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st st')
      (hloop : EvalR (imp {while (~b) {~c} }) st' st'') :
      EvalR (imp {while (~b) {~c} }) st st''
  | havoc {st : State} {x : Ident} {n : Nat} :
      EvalR (imp {havoc x}) st (x →ₜ n ; st)

instance : HasEval Com State State where
  Eval := Com.EvalR

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()

-- The definition of Hoare triples is exactly as before.

def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st st' : State},
    (st =[ c ]=> st') →
    P st →
    Q st'

instance : HasTriple Com where
  Triple := ValidHoareTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st st' : State},
      (st =[ c ]=> st') →
      P st →
      Q st' := by rfl

attribute [irreducible] ValidHoareTriple

-- And the precondition consequence rule is exactly as before.

theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply_rules

-- ### Exercise (3 stars): hoare_havoc (Advanced) ⭐⭐⭐

-- Complete the Hoare rule for `havoc` commands below by defining `havoc_pre`,
-- and prove that the resulting rule is correct.

def havoc_pre (x : Ident) (Q : Assertion) (st : State) : Prop :=
  sorry

theorem hoare_havoc {Q : Assertion} {x : Ident} :
    {{ fun st => havoc_pre x Q st }} havoc x {{ Q }} := by
  sorry

-- ### Exercise (3 stars): havoc_post (Advanced) ⭐⭐⭐

-- Complete the following proof without changing any of the provided commands.
-- If you find that it can't be completed, your definition of `havoc_pre` is
-- probably too strong. Find a way to relax it so that `havoc_post` can be
-- proved.

-- Hint: the `assertion_auto` tactics we've built won't help you here. You
-- need to proceed manually.

theorem havoc_post {P : Assertion} {x : Ident} :
    {{ P }}
    havoc x
    {{ fun st => ∃ (n : Nat), ({{ P [x ↦ ~(.num n)] }}) st }} := by
  apply hoare_consequence_pre
  · apply hoare_havoc
  · sorry

end Himp

-- ### Assert and Assume

-- In this exercise, we will extend IMP with two commands, `assert` and
-- `assume`. Both commands are ways to indicate that a certain assertion
-- should hold any time this part of the program is reached. However they
-- differ as follows:

-- - If an `assert` statement fails, it causes the program to go into an error
--   state and exit.

-- - If an `assume` statement fails, the program fails to evaluate at all. In
--   other words, the program gets stuck and has no final state.

-- The new set of commands is:

namespace HoareAssertAssume

inductive Com : Type where
  | skip : Com
  | asgn : Ident → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | assert : Bexp → Com
  | assume : Bexp → Com

/-- Assert / assume (`assert (b);`, `assume (b);`).  As with `skip`, the
words `assert` and `assume` are not reserved: the production accepts any
identifier and the macro below rejects everything else. -/
scoped syntax ident " (" imp_bexp ")" : imp_com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $h:ident ($b) }) =>
    if h.getId == `assert then `(Com.assert (bexp {$b}))
    else if h.getId == `assume then `(Com.assume (bexp {$b}))
    else Macro.throwErrorAt h s!"expected 'assert' or 'assume', got '{h.getId}'"
  | `(imp { $c1; $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { ~$c }) =>
    pure c

-- To define the behavior of `assert` and `assume`, we need to add notation
-- for an error, which indicates that an assertion has failed. We modify the
-- `Com.EvalR` relation, therefore, so that it relates a start state to either
-- an end state or to `error`. The `Result` type indicates the end value of a
-- program, either a state or an error:

inductive Result : Type where
  | normal (st : State) : Result
  | error : Result

-- Now we are ready to give you the evaluation relation for the new language.

inductive Com.EvalR : Com → State → Result → Prop where
  /- Old rules, several modified -/
  | skip {st : State} :
      EvalR (imp {skip}) st (.normal st)
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (.normal (x →ₜ n ; st))
  | seqNormal {c1 c2 : Com} {st st' : State} {r : Result}
      (h1 : EvalR c1 st (.normal st')) (h2 : EvalR c2 st' r) :
      EvalR (imp {~c1; ~c2}) st r
  | seqError {c1 c2 : Com} {st : State} (h : EvalR c1 st .error) :
      EvalR (imp {~c1; ~c2}) st .error
  | ifTrue {st : State} {r : Result} {b : Bexp} {c1 c2 : Com}
      (hb : b.eval st = true) (hc : EvalR c1 st r) :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st r
  | ifFalse {st : State} {r : Result} {b : Bexp} {c1 c2 : Com}
      (hb : b.eval st = false) (hc : EvalR c2 st r) :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st r
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c} }) st (.normal st)
  | whileTrueNormal {st st' : State} {r : Result} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st (.normal st'))
      (hloop : EvalR (imp {while (~b) {~c} }) st' r) :
      EvalR (imp {while (~b) {~c} }) st r
  | whileTrueError {st : State} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st .error) :
      EvalR (imp {while (~b) {~c} }) st .error
  /- Rules for Assert and Assume -/
  | assertTrue {st : State} {b : Bexp} (hb : b.eval st = true) :
      EvalR (imp {assert (~b)}) st (.normal st)
  | assertFalse {st : State} {b : Bexp} (hb : b.eval st = false) :
      EvalR (imp {assert (~b)}) st .error
  | assume {st : State} {b : Bexp} (hb : b.eval st = true) :
      EvalR (imp {assume (~b)}) st (.normal st)

instance : HasEval Com State Result where
  Eval := Com.EvalR

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()

-- We redefine hoare triples: Now, `{{ P }} c {{ Q }}` means that, whenever
-- `c` is started in a state satisfying `P`, and terminates with result `r`,
-- then `r` is not an error and the state of `r` satisfies `Q`.

def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st : State} {r : Result},
    (st =[ c ]=> r) → P st →
    ∃ st', r = Result.normal st' ∧ Q st'

instance : HasTriple Com where
  Triple := ValidHoareTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st : State} {r : Result},
      (st =[ c ]=> r) → P st →
      ∃ st', r = Result.normal st' ∧ Q st' := by rfl

attribute [irreducible] ValidHoareTriple

-- ### Exercise (4 stars): assert_vs_assume ⭐⭐⭐⭐

-- To test your understanding of this modification, give an example
-- precondition and postcondition that are satisfied by the `assume` statement
-- but not by the `assert` statement.

theorem assert_assume_differ : ∃ (P : Assertion) (b : Bexp) (Q : Assertion),
    ({{ P }} assume (~b) {{ Q }})
    ∧ ¬ ({{ P }} assert (~b) {{ Q }}) := by
  sorry

-- Then prove that any triple for an `assert` also works when `assert` is
-- replaced by `assume`.

theorem assert_implies_assume (P : Assertion) (b : Bexp) (Q : Assertion)
    (hhoare : {{ P }} assert (~b) {{ Q }}) :
    {{ P }} assume (~b) {{ Q }} := by
  sorry

-- Next, here are proofs for the old hoare rules adapted to the new semantics.
-- You don't need to do anything with these.

theorem hoare_asgn {Q : Assertion} {x : Ident} {a : Aexp} :
    {{Q [x ↦ ~a]}} x := ~a {{ Q }} := by
  rw [validHoareTriple_def]
  intro st r heval hQ
  rw [Assertion.subst_apply] at hQ
  inversion heval with
  | asgn n h =>
    exists (x →ₜ n ; st)
    subst h
    exact ⟨rfl, hQ⟩

theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st r hc hpre
  apply_rules

theorem hoare_consequence_post {P Q Q' : Assertion} {c : Com}
    (hhoare : {{ P }} ~c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} ~c {{   Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st r hc hpre
  obtain ⟨st', hr, hQ'⟩ := hhoare hc hpre
  exists st'
  exact ⟨hr, himp _ hQ'⟩

theorem hoare_seq {P Q R : Assertion} {c1 c2 : Com}
    (h1 : {{ Q }} ~c2 {{R}}) (h2 : {{ P }} ~c1 {{ Q }}) :
    {{ P }} ~c1; ~c2 {{R}} := by
  rw [validHoareTriple_def] at h1 h2 ⊢
  intro st r h12 hpre
  inversion h12 with
  | seqNormal st' hc1 hc2 =>
    apply h1 hc2
    specialize h2 hc1 hpre
    obtain ⟨st'', heq, hQ⟩ := h2
    injection heq with e
    subst e
    exact hQ
  | seqError hc1 =>
    -- Find contradictory assumption
    specialize h2 hc1 hpre
    obtain ⟨st', hC, _⟩ := h2
    contradiction

-- Here are the other proof rules (sanity check)

theorem hoare_skip {P : Assertion} :
    {{ P }} skip {{ P }} := by
  rw [validHoareTriple_def]
  intro st r h hpre
  inversion h
  exact ⟨st, rfl, hpre⟩

theorem hoare_if {P Q : Assertion} {b : Bexp} {c1 c2 : Com}
    (hTrue : {{ P ∧ b}} ~c1 {{ Q }}) (hFalse : {{ P ∧ ¬ b}} ~c2 {{ Q }}) :
    {{ P }} if (~b) { ~c1 } else { ~c2 } {{ Q }} := by
  rw [validHoareTriple_def] at hTrue hFalse ⊢
  intro st r hE hpre
  inversion hE with
  | ifTrue hb hc =>
    -- b is true
    apply_rules [And.intro]
  | ifFalse hb hc =>
    -- b is false
    apply hFalse hc
    exact ⟨hpre, by simp [hb]⟩

theorem hoare_while {P : Assertion} {b : Bexp} {c : Com}
    (hhoare : {{P ∧ b}} ~c {{ P }}) :
    {{ P }} while (~b) { ~c } {{ P ∧ ¬ b}} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st r heval hpre
  generalize heq : (imp { while (~b) { ~c } }) = cmd at heval
  induction heval generalizing P with
  | @whileFalse b0 s0 c0 hb =>
    injection heq with hbeq hceq
    subst hbeq hceq
    exact ⟨s0, rfl, hpre, by simp [hb]⟩
  | @whileTrueNormal s0 s0' r0 b0 c0 hb hc hloop ih1 ih2 =>
    injection heq with hbeq hceq
    subst hbeq hceq
    apply ih2 hhoare _ rfl
    obtain ⟨s1, heq1, hs1⟩ := hhoare hc ⟨hpre, hb⟩
    injection heq1 with he
    subst he
    exact hs1
  | @whileTrueError s0 b0 c0 hb hc =>
    injection heq with hbeq hceq
    subst hbeq hceq
    obtain ⟨s1, heq1, hs1⟩ := hhoare hc ⟨hpre, hb⟩
    simp at heq1
  | skip | asgn | seqNormal | seqError | ifTrue | ifFalse | assertTrue | assertFalse | assume =>
    contradiction

-- Finally, state Hoare rules for `assert` and `assume` and use them to prove
-- a simple program correct. Name your rules `hoare_assert` and
-- `hoare_assume`.

-- FILL IN HERE

-- Use your rules to prove the following triple.

theorem assert_assume_example :
    {{True}}
      assume (X = 1);
      X := X + 1;
      assert (X = 2)
    {{True}} := by
  sorry

end HoareAssertAssume


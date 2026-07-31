import LF.CustomTactics
import HL.Imp

import HL.SFLCompat

-- # Hoare: Hoare Logic, Part I

-- Note to developers (Benjamin Pierce  @bcpierce00, before next release, 2025):
--     There is an excellent and fairly polished problem on a
--     Hoare Logic for a little assembly language in the
--     materials for the 2025 CIS 5000 final exam at Penn. We
--     should turn it into an exercise in this chapter!

-- Note to developers (Benjamin Pierce  @bcpierce00, before next release, 2021):
--     Any chance we could move the (awkwardly placed) weakest
--     precondition discussion to this chapter instead?
--
--     The terse version of the chapter needs serious work --
--     it has gotten quite ragged after a bunch of
--     reorganization of the chapter over the past couple
--     years. BCP 23: Did some work on it. Bit better now. But
--     the notation issues make everything a bit heavy.

-- Note to developers:
--     `HIDE: What about typesetting multi-line triples as
--     {{ P }}
--        c
--     {{ Q }}
--     instead of
--       {{ P }}
--     c
--       {{ Q }}
--     when we print them?`
--
--     `HIDE: At some point we should try one more time to see if it's
--     possible to use single curly braces for Hoare triples.  The Rocq
--     manual says "For the sake of factorization with Rocq predefined
--     rules, simple rules have to be observed for notations starting with
--     a symbol: e.g., rules starting with { or ( should be put at level
--     0."  Maybe this suggests a way forward...?
--     BCP 10/18: Nope.  Writing
--        Notation "'{' P '}' c '{' Q '}'" :=
--          (ValidHoareTriple P c Q) (at level 0, c at next level)
--          : hoare_spec_scope.
--     yields
--         Error: A notation must include at least one symbol.`
--
--     HIDE: This file and all later ones should make a habit
--     of always presenting both syntax and semantics of new
--     language constructs in informal style as well as formal.
--     See MoreStlc.v for a template.

-- Our goal in this chapter is to develop the tools to work
-- through some simple examples of *program verification* --
-- i.e., to use the precise definition of Imp to prove formally
-- that particular programs satisfy particular specifications
-- of their behavior.

-- We'll develop a reasoning system called *Floyd-Hoare Logic*
-- -- often shortened to just *Hoare Logic* -- in which each of
-- the syntactic constructs of Imp is equipped with a generic
-- "proof rule" that can be used to reason compositionally
-- about the correctness of programs involving this construct.

-- Hoare Logic combines two beautiful ideas: a natural way of
-- writing down *specifications* of programs, and a *structured
-- proof technique* for proving that programs are correct with
-- respect to such specifications -- where by "structured" we
-- mean that the structure of proofs directly mirrors the
-- structure of the programs that they are about.

-- Note to developers:
--     `HIDE: MRC'20: The terse version used to start with just an outline of
--     what we've done and of this chapter, but it never mentioned Hoare logic!
--     The text above seems like a better intro.
--
--     MRC'20: this is the former terse intro.
--
--      What we've done so far:
--
--      - Formalized Imp
--           - identifiers and states
--           - abstract syntax trees
--           - evaluation functions (for [aexp]s and [bexp]s)
--           - evaluation relation (for commands)
--
--      - Proved some _metatheoretic_ properties
--          - determinism of evaluation
--          - equivalence of some different ways of writing down the
--            definitions (e.g., functional and relational definitions of
--            arithmetic expression evaluation)
--          - guaranteed termination of certain classes of programs
--          - meaning-preservation of some program transformations
--          - behavioral equivalence of programs ([Equiv])
--
--      We've dealt with a few sorts of properties of Imp programs:
--        - Termination
--        - Nontermination
--        - Equivalence
--
--      Topic:
--        - A systematic method for reasoning about the _functional
--          correctness_ of programs in Imp
--
--      Goals:
--        - a natural notation for _program specifications_ and
--        - a _compositional_ proof technique for program correctness
--
--      Plan:
--        - specifications (assertions / Hoare triples)
--        - proof rules
--        - loop invariants
--        - decorated programs
--        - examples`

-- ## Assertions

open scoped MyGetElem

-- An *assertion* is a logical claim about the state of a
-- program's memory -- formally, a predicate of `State`s.

abbrev Assertion := State → Prop

-- Note to developers:
--     HIDE: MRC'20: pulled up these examples from the
--     quiz/optional exercise so that there would be some
--     modeling of the kinds of answers we expect.

-- For example,

-- - `fun st => st[X] = 3` holds for states `st` in which value
--   of `X` is `3`,

-- - `fun st => True` hold for all states, and

-- - `fun st => False` holds for no states.

-- _Quiz:_

-- Paraphrase the following assertions in English (i.e., say
-- which states satisfy them)

-- (A) `fun st => st[X] ≤ st[Y]`

-- (B) `fun st => st[X] = 3 ∨ st[X] ≤ st[Y]`

-- (C)
-- `fun st => st[Z] * st[Z] ≤ st[X] ∧ ¬ ((st[Z] + 1) * (st[Z] + 1) ≤ st[X])`

-- ### Notations for Assertions

-- We'll use Lean's notation features to make assertions look
-- as much like informal math as possible.

-- For example, instead of writing

--   fun st => st[X] = m

-- we'll usually write just

--   {{ X = m }}

-- Note to developers (before next release):
--     RRand 2022: The coercion printing in recent updates is
--     making the Hoare logic statements we're aiming to prove
--     essentially unreadable. If the implicit coercions are
--     too hard to deal with (I don't see why they would be,
--     given the number of coercion happening here and in Imp)
--     I would roll back to a previous version. I cannot read
--     what's happening in my Rocq buffer.

-- Note to developers:
--     `HIDE: SAZ  2024: I'm confused by the above discussion.  Doesn't
--     [Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop]
--     request Rocq to _show_ those coercions?  I've removed it.`
--
--     `HIDE: SAZ 2024:
--     From what I can tell, the reason the notations expand during
--     the proofs is that they're writen in such a way that they
--     inlude type annotations [(a : Aexp)] and explicit lambdas
--     [(fun st => a st + b st)], neither of which is stable under
--     simplification.  For example:
--
--      [(fun st =>
--         (fun st => (X:Aexp) st + (Y:Aexp) st) st +
--         (fun st => (Z:Aexp) st) st)]
--
--     Will print as [X + Y + Z] until simplification, at which point
--     we have [(fun st => st X + st Y + st Z)] but there is no notation
--     that covers this case.`

-- Here, the `{{ A }}` brackets delimit the scope of the
-- assertion notation.

-- Note to developers:
--     HIDE: Make things easily unfoldable.
--
--     HIDE: MRC'20: Recording this here because it took a
--     merry chase through the Rocq manual to find it: this
--     version of the `Arguments` command is documented under
--     `simpl`.

-- Note to developers (One An  @meluge):
--     The Rocq source here issues
--     `Arguments assert_of_Prop /.` (and likewise for the
--     other two lifting functions) so that `simpl` always
--     unfolds them, with this instructors note: "These
--     `Arguments` commands tell Rocq that these functions
--     should always be unfolded during simplification (by
--     `simpl`)."
--
--     `SAZ 2024 - Why do we want these functions to simplify?
--     Ans: If [a : aexp] then in the assertion_scope [(X →ₜ a st; st)] and
--     [(X →ₜ aeval st a; st)] look different but are actually identical
--     thanks to the coercion [Aexp_of_aexp].`
--
--     Claude suggested `@[simp]`-tagged characterizing lemmas
--     next to the three lifting functions, a global simp
--     attribute means every `simp` unfolds applied
--     occurrences. Is there a better way?

-- Note to developers:
--     NOTATION: BCP 20: It probably makes sense now to put all
--     these in a custom grammar, so that we can really control
--     how it looks and get rid of things like ap.
--
--     `NOTATION: SAZ 2024: I have tried to implement the suggestion above.
--
--     There is now a custom entry [assn] for defining the syntax of
--     assertions.  Like the delimiters <{ }> used for Imp programs,
--     we now also have {{ }} delimiters for use with Assertions.
--
--     Inside that scope, the meaning of variables, nat literals,
--     propositions, etc. is "lifted" to take a state parameter.
--
--     The notation {{ #f x1 .. xn }} now "lifts" a normal function
--     that should be of type [nat -> .. -> nat -> T] so that each of
--     the inputs is treated as an [Aexp] and the state is threaded through.
--     (This replaces the need for [ap], [ap2], etc. throughout.)
--
--     The notation {{ $rocq_term }} now "quotes" a rocq term literally
--     without lifting.  Parentheses can be used as in {{ $(foo bar) }}.`

-- Note to developers (Claude):
--     Delaborators for this grammar are defined in the
--     *Printing Assertions* section below (after assertion
--     substitution, the last notation they need to recognize).
--     They cover the base chapter's forms -- triples, `->>`,
--     substitution, and lifted `Prop`s; not covered are the
--     extension modules' shadowed triples (each module defines
--     its own `Com` and `ValidHoareTriple`) and the
--     `bassertion` coercion, which fall back to raw display.
--     An assertion applied to a state (after `intro st`) also
--     prints raw -- the same thing that happens in the Rocq
--     development as soon as `simpl` unfolds the notation.

namespace Assertion

section
open Lean Elab Term

scoped syntax:max (name := assn) "assn(" ident "; " term ")" : term
scoped syntax:max "#" noWs term:arg : term
scoped syntax "{{" term "}}" : term

@[term_elab assn]
def assnElab : TermElab := fun stx type? => do
  match stx with
  | `(assn($st; #$t:term)) =>
    let t ← elabTerm t none
    let ty ← Meta.inferType t
    dbg_trace ty
    if (ty.constName == ``_root_.Aexp) then
      return (mkApp2 (mkConst ``Aexp.eval) (← elabTerm st none) t)
    else if (ty.constName == ``_root_.Bexp) then
      return (mkApp2 (mkConst ``Bexp.eval) (← elabTerm st none) t)
    else
      throwUnsupportedSyntax
  | `(assn($st; $t:term)) =>
    let t ← elabTerm t none
    let ty ← Meta.inferType t
    dbg_trace ty
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
    else if ty.isMVar then
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
  | `(assn($st; $f $a1)) => ``($f assn($st; $a1))
  | `(assn($st; $f $a1 $a2)) => ``($f assn($st; $a1) assn($st; $a2))
  -- | `(assn($st; $f $t*)) => ``($f ) -- TODO how to get arbitrary applications
end

#check {{ 1 = 2 }}
#check {{ X = X }}
#check {{ X = 2 * X }} -- X is the constant "X" defined in Imp
#check_failure {{ X }} -- fails as expected
#check {{ True }}

#check {{ fun st => st[X] = st[Y] }}

variable (a : Aexp)
#check {{ X = #a }}

variable (b : Bexp)
#check {{ #b }}
#check {{ ¬ #b }}
#check {{ #b ∧ #b }}

variable (P Q : Assertion)
#check {{ P ∧ Q }}

end Assertion

-- TODO OUTDATED We will sometimes need to lift functions to
-- operate on assertion expressions:

-- `{{ #f e1 .. en }}` stands for
-- `(fun st => f (e1 st) .. (en st))`

-- Note to developers:
--     NOTATION: This notation should come early so that later
--     notations for arithmetic expressions take precedence for
--     printing. Otherwise `{{ X + X }}` would print as
--     `{{ #add X Y }}`.

-- We can "escape" a raw Lean function using a `~` prefix:

-- For example: `{{ ~(fun st => ∀ x, st[x] = 0) }}`

-- Note to developers:
--     NOTATION: SAZ 2024: It is important that this custom
--     notation be at a level higher than 1 when added to the
--     `constr` grammar because it interacts with the
--     "application" case of `com` and the notation for Hoare
--     triples. That grammar parses embedded function arguments
--     at level 1. We never want `f {{P}}` to parse `{ P }` as
--     an assertion when used in a command. Instead we want
--     `{{P}}` to "close" the Hoare triple.
--
--     `NOTATION: Note for Rocq custom grammar hackers.  From what I can tell, the
--     Rocq LL(1) parser does left-factorize the grammar, *however* it uses a very
--     strict notion of what counts as "equal" for the purposes of the factorization.
--     In particular, a grammar entry might have a level,
--     as in [e custom assn at level 99] in the notation below.  Leaving out the
--     "at level 99" is *semantically equivalent*, because the [assn] grammar starts
--     at that level, but omitting it will not work because the grammar for
--     Hoare triples below includes "at level 99" -- the [LEVEL "99"] part of the
--     grammar counts for factorization.
--
--     The upshot is that means that this notation and the Hoare triple notation
--     (which overlaps with [{{ _ }}]) must be changed in tandem and use identical
--     level specifications.`

-- ### Example Assertions

namespace ExamplePrettyAssertions
open scoped Assertion

def assertion1 : Assertion := {{ X = 3 }}
def assertion2 : Assertion := {{ True }}
def assertion3 : Assertion := {{ False }}
def assertion4 : Assertion := {{ True ∨ False }}
def assertion5 : Assertion := {{ X ≤ Y }}
def assertion6 : Assertion := {{ X = 3 ∨ X ≤ Y }}
def assertion7 : Assertion := {{ Z = (max X Y) }}
def assertion8 : Assertion := {{ Z * Z ≤ X
                                 ∧ ¬ (((Nat.succ Z) * (Nat.succ Z)) ≤ X) }}
def assertion9 : Assertion := {{ Nat.add X Y > max Y X }}

/--
info: def ExamplePrettyAssertions.assertion8 : Assertion :=
fun st => st[Z] * st[Z] ≤ st[X] ∧ ¬st[Z].succ * st[Z].succ ≤ st[X]
-/
#guard_msgs in
#print assertion8

end ExamplePrettyAssertions

-- ### Assertion Implication

-- Given two assertions `P` and `Q`, we say that `P` *implies*
-- `Q`, written `P ->> Q`, if, whenever `P` holds in some state
-- `st`, `Q` also holds.

def AssertImplies (P Q : Assertion) : Prop :=
  ∀ st, P st → Q st

-- Note that the notation for *assertion implication* is
-- analogous to the "usual" Lean implication `→`.

notation:26 P:27 " ->> " Q:27 => AssertImplies P Q

theorem assertImplies_def {P Q : Assertion} : P ->> Q ↔ ∀ st, P st → Q st := by rfl

-- We'll also want the "iff" variant of implication between
-- assertions:

notation:26 P:27 " <<->> " Q:27 => AssertImplies P Q ∧ AssertImplies Q P

-- Note to developers (Claude):
--     The Rocq source puts these notations in a
--     `hoare_spec_scope`, with a book comment explaining that
--     "the `hoare_spec_scope` annotation tells Rocq that this
--     notation is not global but is intended to be used in
--     particular contexts." Lean has no notation scopes, so
--     the notations are simply global and that paragraph is
--     omitted.

-- ## Hoare Triples, Informally

-- A *Hoare triple* is a claim about the state before and after
-- executing a command:

--   {{P}} c {{Q}}

-- This means:

-- - If command `c` begins execution in a state satisfying
--   assertion `P`,

-- - and if `c` eventually terminates in some final state,

-- - then that final state will satisfy the assertion `Q`.

-- Assertion `P` is called the *precondition* of the triple,
-- and `Q` is the *postcondition*.

-- For example,

-- - The Hoare triple

--   {{X = 0}} X := X + 1 {{X = 1}}

-- states that command `X := X + 1` will transform a state in
-- which `X = 0` to a state in which `X = 1`.

-- - On the other hand,

--   ∀ m, {{X = m}} X := X + 1 {{X = m + 1}}

-- is a *proposition* stating that the Hoare triple
-- `{{X = m}} X :=
-- X + 1 {{X = m + 1}}` is valid for any choice
-- of `m`. Note that `m` in the two assertions is a reference
-- to the *Lean* variable `m`, which is bound outside the Hoare
-- triple.

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

-- Is the following Hoare triple *valid* -- i.e., is the
-- claimed relation between `P`, `c`, and `Q` true?

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

-- ## Hoare Triples, Formally

-- We formalize valid Hoare triples in Lean as follows:

def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ st st',
    (st =[ c ]=> st') →
    P st →
    Q st'

-- Note to developers:
--     `NOTATION: SAZ 2024 One trickiness of these notations is that we
--     want the [com] and [assn] grammars to be "open", so that they can
--     include expressions parsed by the full [constr] grammar of Rocq.
--     However, then there is a conflict of precedence of the
--     "application" cases:
--
--     The example " {{ True }} X := 0 {{ False }} " does not parse as
--     intended because the [com] grammar includes the capability of
--     parsing the (ill-typed) term "0 {{ False }}".
--
--     This means that the "application" for [com] should disallow
--     arguments at the level at which the [assn] grammar is included
--     in constr.  The upshot is that this notation should be included
--     in the grammar at the *same* level as the assertion notation
--     [{{ P }}], which is 2.`

-- Notation for Hoare triples. The command between the two
-- assertions is parsed with the same grammar as the
-- `imp { … }` notation, so a command that is a Lean variable
-- (rather than concrete syntax) is spliced in with `~c`, just
-- as in the `st =[ c ]=> st'` notation.

open scoped Assertion

namespace ValidHoareTriple

/-- Hoare triple: `{{ P }} c {{ Q }}` -/
scoped syntax:lead "{{" term "}} " imp_com:lead " {{" term "}}" : term

macro_rules
  | `({{ $P }} $c:imp_com {{ $Q }}) =>
      `(ValidHoareTriple ({{ $P }}) (imp { $c }) ({{ $Q }}))

end ValidHoareTriple

section
open scoped ValidHoareTriple

-- Note to developers:
--     `HIDE: AAA: If I try to set the notation as {P} c {Q}, I get the
--     following error:
--
--       Error: A notation must include at least one symbol.
--
--     Maybe we could use other braces? For instance, I tried it with [P]
--     c [Q] and it seems to work (although I don't know how that would
--     affect the rest of the book).
--
--     BCP: Let's try with the "squashed" double braces for a while and
--     see if we like it.
--
--     P.S.
--     This works:
--        Notation "{ x }" := (x) (at level 0, x at level 99).
--     But this doesn't:
--        Notation "{ P }  c  { Q }" :=
--          (ValidHoareTriple P c Q)
--          (at level 0, P at level 99, c at level 99, Q at level 99)
--        : hoare_spec_scope.
--     Why??`

-- ### Exercise (1 star): hoare_post_true ⭐

-- Prove that if `Q` holds in every state, then any triple with
-- `Q` as its postcondition is valid.

theorem hoare_post_true (P Q : Assertion) (c : Com) (h : ∀ st, Q st) :
    {{ P }} ~c {{ Q }} := by
  sorry

-- ### Exercise (1 star): hoare_pre_false ⭐

-- Prove that if `P` holds in no state, then any triple with
-- `P` as its precondition is valid.

theorem hoare_pre_false (P Q : Assertion) (c : Com) (h : ∀ st, ¬ (P st)) :
    {{ P }} ~c {{ Q }} := by
  sorry

-- ## Proof Rules

-- We want to be able to *prove* Hoare triples formally.

-- Here's our plan:

-- - introduce one "proof rule" for each Imp syntactic form

-- - plus a couple of "structural rules" that help glue proofs
--   together

-- - prove these rules correct in terms of the definition of
--   `ValidHoareTriple`

-- - prove programs correct using these proof rules, without ever
--   unfolding the definition of `ValidHoareTriple`

-- ### Skip

-- Since `skip` doesn't change the state, it preserves any
-- assertion `P`:

--   --------------------  (hoare_skip)
--   {{ P }} skip {{ P }}

theorem hoare_skip (P : Assertion) :
    {{ P }} skip; {{ P }} := by
  intro st st' h hp
  inversion h
  assumption

-- ### Sequencing

-- If command `c1` takes any state where `P` holds to a state
-- where `Q` holds, and if `c2` takes any state where `Q` holds
-- to one where `R` holds, then doing `c1` followed by `c2`
-- will take any state where `P` holds to one where `R` holds:

--    {{ P }} c1 {{ Q }}
--    {{ Q }} c2 {{ R }}
--   ----------------------  (hoare_seq)
--   {{ P }} c1;c2 {{ R }}

theorem hoare_seq (P Q R : Assertion) (c1 c2 : Com)
    (h1 : {{ Q }} ~c2 {{ R }}) (h2 : {{ P }} ~c1 {{ Q }}) :
    {{ P }} ~c1 ~c2 {{ R }} := by
  intro st st' h12 pre
  inversion h12 with
  | seq st'' hc1 hc2 =>
    exact h1 _ _ hc2 (h2 _ _ hc1 pre)

-- ### Assignment

-- How can we complete this triple?

--   {{ ??? }}  X := Y  {{ X = 1 }}

-- One natural possibility is:

--   {{ Y = 1 }}  X := Y  {{ X = 1 }}

-- The precondition is just the postcondition, but with `X`
-- replaced by `Y`.

-- How about this one?

--   {{ ??? }}  X := X + Y  {{ X = 1 }}

-- Replace `X` with `X + Y`:

--   {{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}

-- This works because "equals 1" holding of `X` is guaranteed
-- by the property "equals 1" holding of whatever is being
-- assigned to `X`.

-- In general, the postcondition could be some arbitrary
-- assertion `Q`, and the right-hand side of the assignment
-- could be some arbitrary arithmetic expression `a`:

--   {{ ??? }}  X := a  {{ Q }}

-- The precondition would then be `Q`, but with any occurrences
-- of `X` in it replaced by `a`.

-- Let's introduce a notation for this idea of replacing
-- occurrences: Define `Q \[X ↦ a`] to mean "`Q` where `a` is
-- substituted in place of `X`".

-- This yields the Hoare logic rule for assignment:

--   {{ Q [X ↦ a] }}  X := a  {{ Q }}

-- One way of reading this rule is: If you want statement
-- `X := a` to terminate in a state that satisfies assertion
-- `Q`, then it suffices to start in a state that also
-- satisfies `Q`, except where `a` is substituted for every
-- occurrence of `X`.

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

-- To formalize the rule, we must first formalize the idea of
-- "substituting an expression for an Imp variable in an
-- assertion", which we refer to as assertion substitution, or
-- `Assertion.sub`.

-- Intuitively, given a proposition `P`, a variable `X`, and an
-- arithmetic expression `a`, we want to derive another
-- proposition `P'` that is just the same as `P` except that
-- `P'` should mention `a` wherever `P` mentions `X`.

-- This operation is related to the idea of substituting Imp
-- expressions for Imp variables that we saw in *Equiv*
-- (`subst_aexp` and friends). The difference is that, here,
-- `P` is an arbitrary Lean assertion, so we can't directly
-- "edit" its text.

-- However, we can achieve the same effect by evaluating `P` in
-- an updated state, defined as follows:

def Assertion.sub (x : Ident) (a : Aexp) (P : Assertion) : Assertion :=
  fun (st : State) => P (x →ₜ a.eval st ; st)

-- Note to developers (before next release):
--     This concrete syntax is hard to read in comments because
--     of all the square brackets. Something like
--     `P with X ↦ a` would be much better. I guess the same
--     will apply to the lambda-calculus chapters... BCP 25: I
--     still think this is a good idea, and I had a quick go at
--     implementing it, but did not succeed yet.

-- TODO Introduce a notation typeclass for this (e.g. HasSubst)

/-- Assertion substitution: `P [X ↦ a]` -/
syntax:100 term:100 " [" ident " ↦ " imp_aexp "]" : term

macro_rules
  | `($P [$x ↦ $a]) => `(Assertion.sub $x (aexp { $a }) $P)
  -- | `(assn($st; $P [$x ↦ $a])) => ``(assn($st; $P) [$x ↦ $a]) -- maybe we could push substitutions inside

-- This notation allows us to write this operation as:

--   P [ X ↦ a ]

#check (fun st => Assertion.sub X (aexp { 2 * X }) ({{ X ≤ 10 }}) st)
#check {{ X ≤ 10 }} [X ↦ 2 * X]
#check (∀ st, ({{ X ≤ 10 }} [X ↦ 2 * X]) st)

-- That is, `P [X ↦ a]` stands for an assertion -- let's call
-- it `P'` -- that behaves just like `P` except that, wherever
-- `P` looks up the variable `X` in the current state, `P'`
-- instead uses the value of the expression `a`.

-- We can demonstrate formally that we have captured intuitive
-- meaning of "assertion subsitution" by proving some example
-- logical equivalences:

namespace ExampleAssertionSub
example :
    {{ (X ≤ 5) }} [X ↦ 3] <<->> {{ 3 ≤ 5 }} := by
  constructor <;> (unfold AssertImplies Assertion.sub; intro st h; exact h)

example :
    {{ (X ≤ 5) }} [X ↦ X + 1] <<->> {{ (X + 1) ≤ 5 }} := by
  constructor <;> (unfold AssertImplies Assertion.sub; intro st h; exact h)

end ExampleAssertionSub

-- ### Printing Assertions

-- -- ::::details (summary := "Notation encoding: printing
-- assertions back") --
-- `lean
-- -- namespace Assn.Delab
-- -- open Lean PrettyPrinter Delaborator SubExpr Parenthesizer Imp.Delab

-- -- /-- Re-inserts parentheses in `assn_aexp` output according to the grammar's
-- -- precedences. -/
-- -- @[category_parenthesizer assn_aexp]
-- -- def assn_aexp.parenthesizer : CategoryParenthesizer | prec => do
-- --   maybeParenthesize `assn_aexp
-- true wrapParens prec <| -- parenthesizeCategoryCore
-- `assn_aexp prec
-- -- where
-- --   wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
-- --     let pstx ← `(assn_aexp|
-- ($(⟨stx⟩))) -- return pstx.raw.setInfo (SourceInfo.fromRef
-- stx) -- /-- Re-inserts parentheses in `assn` output
-- according to the grammar's -- precedences. -/ --
-- @[category_parenthesizer assn] -- def assn.parenthesizer :
-- CategoryParenthesizer | prec => do -- maybeParenthesize
-- `assn true wrapParens prec <|
-- --     parenthesizeCategoryCore `assn
-- prec -- where -- wrapParens (stx : Syntax) : Syntax :=
-- Unhygienic.run do -- let pstx ←
-- `(assn| ($(⟨stx⟩)))
-- --     return pstx.raw.setInfo (SourceInfo.fromRef stx)

-- -- /-- Print the focused term as a bare identifier if it delaborates to one,
-- -- and with the `~` escape otherwise. -/
-- -- def identOrEscapeAexp : DelabM (TSyntax `assn_aexp)
-- := do -- match ← delab with -- | `($x:ident) => `(assn_aexp|
-- $x:ident) -- | t =>
-- `(assn_aexp| ~$t)

-- -- /-- Print the focused term as a bare identifier if it delaborates to one,
-- -- and with the `~` escape otherwise. -/
-- -- def identOrEscapeAssn : DelabM (TSyntax `assn)
-- := do -- match ← delab with -- | `($x:ident) => `(assn|
-- $x:ident) -- | t =>
-- `(assn| ~$t)

-- -- /-- Rebuild `assn_aexp` syntax from an `Aexp` (the argument of the
-- -- `Aexp'.ofAexp` coercion). -/
-- -- partial def delabAexpAsAssn : DelabM (TSyntax `assn_aexp)
-- := do -- let stx ← -- match_expr ← getExpr with -- |
-- Aexp.num _ => -- match (← withAppArg getExpr).nat? with -- |
-- some v => pure ⟨Syntax.mkNumLit (toString v) |>.raw⟩ -- |
-- none => identOrEscapeAexp -- | Aexp.id _ => -- match ←
-- withAppArg getExpr with -- | .const nm _ =>
-- `(assn_aexp| $(mkIdent nm):ident)
-- --       | _ => identOrEscapeAexp
-- --     | Aexp.plus _ _ =>
-- --       let s1 ← withAppFn <| withAppArg delabAexpAsAssn
-- --       let s2 ← withAppArg delabAexpAsAssn
-- --       `(assn_aexp|
-- $s1 + $s2) -- | Aexp.minus _ _ => -- let s1 ← withAppFn <|
-- withAppArg delabAexpAsAssn -- let s2 ← withAppArg
-- delabAexpAsAssn --
-- `(assn_aexp| $s1 - $s2)
-- --     | Aexp.mult _ _ =>
-- --       let s1 ← withAppFn <| withAppArg delabAexpAsAssn
-- --       let s2 ← withAppArg delabAexpAsAssn
-- --       `(assn_aexp|
-- $s1 * $s2) -- | _ => identOrEscapeAexp -- annAsTerm stx --
-- mutual -- /-- Rebuild `assn_aexp` syntax from an
-- assertion-level numeric value -- the -- body form the
-- `{{ … }}` macros produce, applied to the state variable. -/
-- -- partial def delabAssnAexpVal : DelabM (TSyntax
-- `assn_aexp) := do
-- --   let e ← getExpr
-- --   let stx ←
-- --     match_expr e with
-- --     | HAdd.hAdd _ _ _ _ _ _ =>
-- --       let s1 ← withNaryArg 4 delabAssnAexpVal
-- --       let s2 ← withNaryArg 5 delabAssnAexpVal
-- --       `(assn_aexp|
-- $s1 + $s2) -- | HSub.hSub _ _ _ _ _ _ => -- let s1 ←
-- withNaryArg 4 delabAssnAexpVal -- let s2 ← withNaryArg 5
-- delabAssnAexpVal --
-- `(assn_aexp| $s1 - $s2)
-- --     | HMul.hMul _ _ _ _ _ _ =>
-- --       let s1 ← withNaryArg 4 delabAssnAexpVal
-- --       let s2 ← withNaryArg 5 delabAssnAexpVal
-- --       `(assn_aexp|
-- $s1 * $s2) -- | _ => -- let .app f v := e | failure -- guard
-- v.isFVar -- match_expr f with -- | Aexp'.ofNat _ => -- match
-- (← withAppFn <| withAppArg getExpr).nat? with -- | some val
-- => pure ⟨Syntax.mkNumLit (toString val) |>.raw⟩ -- | none =>
-- withAppFn <| withAppArg identOrEscapeAexp -- | Aexp'.ofAexp
-- _ => withAppFn <| withAppArg delabAexpAsAssn -- | _ => -- if
-- f.isLambda then -- withAppFn do withBindingBody (←
-- getExpr).bindingName! delabAssnAexpVal -- else -- withAppFn
-- identOrEscapeAexp -- annAsTerm stx -- /-- Rebuild `assn`
-- syntax from an assertion body -- the proposition the --
-- `{{ … }}` macros produce, applied to the state variable. -/
-- -- partial def delabAssnVal : DelabM (TSyntax
-- `assn) := do
-- --   let e ← getExpr
-- --   let stx ←
-- --     match_expr e with
-- --     | Eq _ _ _ =>
-- --       let s1 ← withNaryArg 1 delabAssnAexpVal
-- --       let s2 ← withNaryArg 2 delabAssnAexpVal
-- --       `(assn|
-- $s1:assn_aexp = $s2:assn_aexp) -- | Ne _ _ _ => -- let s1 ←
-- withNaryArg 1 delabAssnAexpVal -- let s2 ← withNaryArg 2
-- delabAssnAexpVal --
-- `(assn| $s1:assn_aexp ≠ $s2:assn_aexp)
-- --     | LE.le _ _ _ _ =>
-- --       let s1 ← withNaryArg 2 delabAssnAexpVal
-- --       let s2 ← withNaryArg 3 delabAssnAexpVal
-- --       `(assn|
-- $s1:assn_aexp ≤ $s2:assn_aexp) -- | LT.lt _ _ _ _ => -- let
-- s1 ← withNaryArg 2 delabAssnAexpVal -- let s2 ← withNaryArg
-- 3 delabAssnAexpVal --
-- `(assn| $s1:assn_aexp < $s2:assn_aexp)
-- --     | GE.ge _ _ _ _ =>
-- --       let s1 ← withNaryArg 2 delabAssnAexpVal
-- --       let s2 ← withNaryArg 3 delabAssnAexpVal
-- --       `(assn|
-- $s1:assn_aexp ≥ $s2:assn_aexp) -- | GT.gt _ _ _ _ => -- let
-- s1 ← withNaryArg 2 delabAssnAexpVal -- let s2 ← withNaryArg
-- 3 delabAssnAexpVal --
-- `(assn| $s1:assn_aexp > $s2:assn_aexp)
-- --     | And _ _ =>
-- --       let s1 ← withNaryArg 0 delabAssnVal
-- --       let s2 ← withNaryArg 1 delabAssnVal
-- --       `(assn|
-- $s1 ∧ $s2) -- | Or _ _ => -- let s1 ← withNaryArg 0
-- delabAssnVal -- let s2 ← withNaryArg 1 delabAssnVal --
-- `(assn| $s1 ∨ $s2)
-- --     | Iff _ _ =>
-- --       let s1 ← withNaryArg 0 delabAssnVal
-- --       let s2 ← withNaryArg 1 delabAssnVal
-- --       `(assn|
-- $s1 ↔ $s2) -- | Not _ => --
-- `(assn| ¬$(← withAppArg delabAssnVal))
-- --     | _ =>
-- --       if e.isArrow then
-- --         let s1 ← withBindingDomain delabAssnVal
-- --         let s2 ← withBindingBody e.bindingName! delabAssnVal
-- --         `(assn|
-- $s1 → $s2) -- else -- let .app f v := e | failure -- guard
-- v.isFVar -- match_expr f with -- | Assertion.ofProp _ => --
-- match ← withAppFn <| withAppArg getExpr with -- | .const nm
-- _ =>
-- `(assn| $(mkIdent nm):ident)
-- --           | _ => withAppFn <| withAppArg identOrEscapeAssn
-- --         | Assertion.sub _ _ _ => withAppFn delabSubInner
-- --         | _ =>
-- --           if f.isLambda then
-- --             withAppFn do withBindingBody (← getExpr).bindingName! delabAssnVal
-- --           else
-- --             withAppFn identOrEscapeAssn
-- --   annAsTerm stx

-- -- /-- Rebuild the substitution notation from an `Assertion.sub` application. -/
-- -- partial def delabSubInner : DelabM (TSyntax `assn)
-- := do -- let .const nm _ ← withNaryArg 0 getExpr | failure
-- -- let a ← withNaryArg 1 delabAexpInner -- let P ←
-- withNaryArg 2 delabAssnFun --
-- `(assn| $P [$(mkIdent nm):ident ↦ $a:imp_aexp])

-- -- /-- Rebuild `assn` syntax from an `Assertion`-valued term. -/
-- -- partial def delabAssnFun : DelabM (TSyntax `assn)
-- := do -- let e ← getExpr -- let stx ← -- match_expr e with
-- -- | Assertion.ofProp _ => -- match ← withAppArg getExpr
-- with -- | .const nm _ =>
-- `(assn| $(mkIdent nm):ident)
-- --       | _ => withAppArg identOrEscapeAssn
-- --     | Assertion.sub _ _ _ => delabSubInner
-- --     | _ =>
-- --       if e.isLambda then
-- --         withBindingBody e.bindingName! delabAssnVal
-- --       else
-- --         identOrEscapeAssn
-- --   annAsTerm stx

-- -- end

-- -- /-- Rebuild `assn` syntax from an `Assertion`, falling back to the escaped
-- -- raw term. -/
-- -- def delabAssnTotal : DelabM (TSyntax `assn)
-- := -- delabAssnFun <|> identOrEscapeAssn -- `
-- -- ::::

-- -- ::::details (summary := "Notation encoding: registering
-- the delaborators") --
-- `lean
-- -- @[delab app.ValidHoareTriple]
-- -- def delabTriple : Delab := whenPPOption getPPNotation do
-- --   guard <| (← getExpr).isAppOfArity ``ValidHoareTriple 3
-- --   let P ← withNaryArg 0 delabAssnTotal
-- --   let c ← withNaryArg 1 delabComInner
-- --   let Q ← withNaryArg 2 delabAssnTotal
-- --   `({{
-- $P }} $c:imp_com {{ $Q }}) -- @[delab app.AssertImplies] --
-- def delabAssertImplies : Delab := whenPPOption getPPNotation
-- do -- guard <| (← getExpr).isAppOfArity ``AssertImplies 2 --
-- let P ← withNaryArg 0 delabAssnTotal -- let Q ← withNaryArg
-- 1 delabAssnTotal --
-- `({{ $P }} ->> {{ $Q }})

-- -- @[delab app.Assertion.sub]
-- -- def delabSub : Delab := whenPPOption getPPNotation do
-- --   guard <| (← getExpr).isAppOfArity ``Assertion.sub 3
-- --   `({{
-- $(← delabSubInner) }}) -- @[delab app.Assertion.ofProp] --
-- def delabOfProp : Delab := whenPPOption getPPNotation do --
-- guard <| (← getExpr).isAppOfArity ``Assertion.ofProp 1 --
-- `({{ $(← delabAssnFun) }})

-- -- end Assn.Delab
-- -- ` -- ::::

-- Now, using the substitution operation we've just defined, we
-- can give the precise proof rule for assignment:

--   ---------------------------- (hoare_asgn)
--   {{Q [X ↦ a]}} X := a {{Q}}

-- We can prove formally that this rule is indeed valid.

theorem hoare_asgn (Q : Assertion) (x : Ident) (a : Aexp) :
    {{ Q [x ↦ ~a] }}  x := ~a; {{ Q }} := by
  intro st st' hE hQ
  inversion hE with
  | asgn n h =>
    subst h
    exact hQ

-- Here's a first formal proof of a Hoare triple using this
-- rule.

theorem assertion_sub_example :
    {{ {{ X < 5 }} [X ↦ X + 1] }}
      X := X + 1;
    {{ X < 5 }} := by
  apply hoare_asgn

-- Of course, we'd probably prefer to work with this simpler
-- triple:

--   {{X < 4}} X := X + 1 {{X < 5}}

-- We will see how to do so in the next section.

-- Several proofs below use the facts about total-map updates
-- proved in the *Typeclasses* chapter -- `TotalMap.update_eq`,
-- `TotalMap.update_neq`, `TotalMap.update_shadow`,
-- `TotalMap.update_same`, and `TotalMap.update_permute`. Make
-- sure you understand their statements.

-- ### Consequence

-- Sometimes the preconditions and postconditions we get from
-- the Hoare rules won't quite be the ones we want in the
-- particular situation at hand -- they may be logically
-- equivalent but have a different syntactic form that fails to
-- unify with the goal we are trying to prove, or they actually
-- may be logically weaker (for preconditions) or stronger (for
-- postconditions) than what we need.

-- For instance,

--   {{(X = 3) [X ↦ 3]}} X := 3 {{X = 3}},

-- follows directly from the assignment rule, but

--   {{True}} X := 3 {{X = 3}}

-- does not. This triple is valid, but it is not an instance of
-- `hoare_asgn` because `True` and `(X = 3) \[X ↦ 3`] are not
-- syntactically equal assertions.

-- However, they are logically *equivalent*, so if one triple
-- is valid, then the other must certainly be as well. We can
-- capture this observation with the following rule:

--      {{P'}} c {{Q}}
--        P <<->> P'
--   ---------------------
--      {{P}} c {{Q}}

-- Taking this line of thought a bit further, we can see that
-- strengthening the precondition or weakening the
-- postcondition of a valid triple always produces another
-- valid triple. This observation is captured by two *Rules of
-- Consequence*.

--          {{P'}} c {{Q}}
--             P ->> P'
--   -----------------------------   (hoare_consequence_pre)
--          {{P}} c {{Q}}

--          {{P}} c {{Q'}}
--            Q' ->> Q
--   -----------------------------    (hoare_consequence_post)
--          {{P}} c {{Q}}

-- Here are the formal versions:

theorem hoare_consequence_pre (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  unfold ValidHoareTriple
  intro st st' heval hpre
  apply hhoare st st'
  · assumption
  · apply himp
    assumption

theorem hoare_consequence_post (P Q Q' : Assertion) (c : Com)
    (hhoare : {{ P }} ~c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  unfold ValidHoareTriple
  intro st st' heval hpre
  apply himp
  apply hhoare st st'
  · assumption
  · assumption

-- For example, we can use the first consequence rule like
-- this:

--   {{ True }} ->>
--   {{ (X = 1) [X ↦ 1] }}
--     X := 1
--   {{ X = 1 }}

-- Or, formally...

theorem hoare_asgn_example1 :
    {{True}} X := 1; {{X = 1}} := by
  sorry

-- We can also use it to prove the example mentioned earlier.

--   {{ X < 4 }} ->>
--   {{ (X < 5)[X ↦ X + 1] }}
--     X := X + 1
--   {{ X < 5 }}

-- Or, formally ...

theorem assertion_sub_example2 :
    {{X < 4}}
      X := X + 1;
    {{X < 5}} := by
  sorry

-- Finally, here is a combined rule of consequence that allows
-- us to vary both the precondition and the postcondition.

--          {{P'}} c {{Q'}}
--             P ->> P'
--             Q' ->> Q
--   -----------------------------   (hoare_consequence)
--          {{P}} c {{Q}}

theorem hoare_consequence (P P' Q Q' : Assertion) (c : Com)
    (htriple : {{ P' }} ~c {{ Q' }}) (hpre : P ->> P') (hpost : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  apply hoare_consequence_pre (P' := P')
  · apply hoare_consequence_post (Q' := Q')
    · assumption
    · assumption
  · assumption

-- ### Automation

-- Many of the proofs we have done so far with Hoare triples
-- can be streamlined using the automation techniques that we
-- introduced in the *Automation* chapter of *Logical
-- Foundations*.

-- Recall that the `simp` tactic can be told to unfold
-- definitions as part of its simplifications. The definitions
-- we keep needing to unfold in this chapter are
-- `ValidHoareTriple`, `AssertImplies`, `Assertion.sub`, the
-- lifting functions `Assertion.ofProp`, `Aexp'.ofNat`, and
-- `Aexp'.ofAexp`, and the total-map operations. We'll pass
-- these to `simp` explicitly below (and shortly package the
-- recipe up as a tactic of our own).

-- Note to developers (Claude):
--     The Rocq source here registers
--     `Hint Unfold assert_implies assertion_sub
--     t_update : core`
--     for `auto`. That only widens `auto`'s search (unlike the
--     `Arguments /.` commands, it does not affect `simpl`), so
--     its Lean counterpart is the `assertion_auto` tactic's
--     simp list below -- not global `@[simp]` lemmas as for
--     the notation wrappers, whose folded names carry no
--     meaning in goals the way `->>` and `Assertion.sub` do.

-- Here's a good candidate for automation:

theorem hoare_consequence_pre' (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  unfold ValidHoareTriple
  intro st st' heval hpre
  apply hhoare st st'
  · assumption
  · apply himp
    assumption

-- `apply` will find `st` for us, using a metavariable.

theorem hoare_consequence_pre''' (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  unfold ValidHoareTriple
  intro st st' heval hpre
  apply hhoare
  · assumption
  · apply himp
    assumption

-- Since the remaining steps just apply hypotheses to each
-- other, the entire proof can actually be compressed into a
-- single line, by writing the term that `exact`ly proves the
-- conclusion.

theorem hoare_consequence_pre'''' (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  intro st st' heval hpre
  exact hhoare st st' heval (himp st hpre)

-- ...as can the proof for the postcondition consequence rule.

theorem hoare_consequence_post' (P Q Q' : Assertion) (c : Com)
    (hhoare : {{ P }} ~c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  intro st st' heval hpre
  exact himp st' (hhoare st st' heval hpre)

-- We can also use a metavariable to streamline a proof
-- (`hoare_asgn_example1`), that we did earlier as an example
-- of using the consequence rule:

theorem hoare_asgn_example1' :
    {{True}} X := 1; {{X = 1}} := by
  apply hoare_consequence_pre  -- no need to state an assertion
  · apply hoare_asgn
  · unfold AssertImplies Assertion.sub
    intro st _
    rfl

-- The final bullet of that proof also looks like a candidate
-- for automation.

theorem hoare_asgn_example1'' :
    {{True}} X := 1; {{X = 1}} := by
  apply hoare_consequence_pre
  · apply hoare_asgn
  · simp [AssertImplies, Assertion.sub, TotalMap.update_eq]

-- Now we have quite a nice proof script: it simply identifies
-- the Hoare rules that need to be used and leaves the
-- remaining low-level details up to Lean to figure out.

-- The other example of using consequence that we did earlier,
-- `hoare_asgn_example2`, requires a little more work to
-- automate. `simp` simplifies the assertion implication in the
-- final bullet, but cannot finish it: the leftover goal is
-- arithmetic, so it needs `lia`.

theorem assertion_sub_example2' :
    {{X < 4}}
      X := X + 1;
    {{X < 5}} := by
  apply hoare_consequence_pre
  · apply hoare_asgn
  · simp [AssertImplies, Assertion.sub, TotalMap.update_eq]  -- an arithmetic goal remains
    lia

-- Let's introduce our own tactic to handle both that bullet
-- and the bullet from example 1. A `macro` declaration gives a
-- name to a canned sequence of tactics:

/-- Prove routine facts about assertions: unfold the Hoare-logic
definitions and lifting functions, simplify, and finish any leftover
arithmetic with `lia`. -/
macro "assertion_auto" : tactic =>
  `(tactic| (intros
             <;> try (simp [assertImplies_def, ValidHoareTriple, Assertion.sub,
                            TotalMap.update, TotalMap.getElem_def,
                            W, X, Y, Z] at *)
             <;> try lia))

theorem assertion_sub_example2'' :
    {{X < 4}}
      X := X + 1;
    {{X < 5}} := by
  apply hoare_consequence_pre
  · apply hoare_asgn
  · assertion_auto

theorem hoare_asgn_example1''' :
    {{True}} X := 1; {{X = 1}} := by
  apply hoare_consequence_pre
  · apply hoare_asgn
  · assertion_auto

-- Again, we have quite a nice proof script. All the low-level
-- details of proofs about assertions have been taken care of
-- automatically. Of course, `assertion_auto` isn't able to
-- prove everything we could possibly want to know about
-- assertions -- there's no magic here! But it's pretty good.

-- ### Sequencing + Assignment

-- Here's an example of a program involving both sequencing and
-- assignment. Note the use of `hoare_seq` in conjunction with
-- `hoare_consequence_pre` and `apply`'s metavariables.

theorem hoare_asgn_example3 (a : Aexp) (n : Nat) :
    {{#a = n}}
      X := ~a;
      skip;
    {{X = n}} := by
  apply hoare_seq
  · -- right part of seq
    apply hoare_skip
  · -- left part of seq
    apply hoare_consequence_pre
    · apply hoare_asgn
    · assertion_auto

-- Informally, a nice way of displaying a proof using the
-- sequencing rule is as a "decorated program" where the
-- intermediate assertion `Q` is written between `c1` and `c2`:

--            {{ a = n }}
--   X := a
--            {{ X = n }};    <--- decoration for Q
--   skip
--            {{ X = n }}

-- We'll come back to the idea of decorated programs in much
-- more detail in the next chapter.

-- ### Conditionals

-- What sort of rule do we want for reasoning about conditional
-- commands?

-- Certainly, if the same assertion `Q` holds after executing
-- either of the branches, then it holds after the whole
-- conditional. So we might be tempted to write:

--           {{P}} c1 {{Q}}
--           {{P}} c2 {{Q}}
--   ---------------------------------
--   {{P}} if b then c1 else c2 {{Q}}

-- However, this is rather weak. For example, using this rule,
-- we cannot show

--   {{ True }}
--     if X = 0
--       then Y := 2
--       else Y := X + 1
--     end
--   {{ X ≤ Y }}

-- since the rule doesn't tell us enough about the state in
-- which the assignments take place in the "then" and "else"
-- branches.

-- Better:

--   {{P ∧   b}} c1 {{Q}}
--   {{P ∧ ¬ b}} c2 {{Q}}
--   ------------------------------------  (hoare_if)
--   {{P}} if b then c1 else c2 end {{Q}}

-- To make this formal, we need a way of formally "lifting" any
-- bexp `b` to an assertion.

-- We'll write `bassertion b` for the assertion "the boolean
-- expression `b` evaluates to `true`."

def bassertion (b : Bexp) : Assertion := {{ #b }} -- NOTE xhalo32: we don't need this IMO

@[simp] theorem bassertion_apply (b : Bexp) (st : State) :
    bassertion b st = (b.eval st = true) := rfl

instance : Coe Bexp Assertion := ⟨bassertion⟩

-- A useful fact about `bassertion`:

-- Note to developers (before next release):
--     `Robert Rand: This isn't an identity but that's because
--     we're using [~(bassertion b st)] in our triples, instead of a more
--     direct/intuitive predicate.
--
--     Some alternatives: 1) P_True b and P_False b (defined directly as
--     desired) 1) bassertion b false (adds relevant argument to bassertion)
--     2) ((bassertion (!b)) st) (clearer, but less direct).`

theorem bexp_eval_false (b : Bexp) (st : State) (h : b.eval st = false) :
    ¬ ({{ #b }}) st := by
  simp [h]

-- Note to developers (One An  @meluge):
--     The Rocq proof is the single tactic `congruence`. Using
--     simp seems to work but should we build our own
--     `congruence` tactic?

-- Now we can formalize the Hoare proof rule for conditionals
-- and prove it correct.

-- The statement of the rule reads: given
-- `htrue : {{ P ∧ b }} ~c1 {{Q}}` and
-- `hfalse : {{ P ∧ ¬b }} ~c2 {{Q}}`, we can conclude
-- `{{P}} if (~b) { ~c1 } else { ~c2 } {{Q}}`.

-- That is (unwrapping the notations):

--   theorem hoare_if (P Q : Assertion) (b : Bexp) (c1 c2 : Com)
--       (htrue : ValidHoareTriple (fun st => P st ∧ bassertion b st) c1 Q)
--       (hfalse : ValidHoareTriple (fun st => P st ∧ ¬ (bassertion b st)) c2 Q) :
--       ValidHoareTriple P (Com.cond b c1 c2) Q

theorem hoare_if (P Q : Assertion) (b : Bexp) (c1 c2 : Com)
    (htrue : {{ P ∧ #b }} ~c1 {{ Q }}) (hfalse : {{ P ∧ ¬ #b }} ~c2 {{ Q }}) :
    {{ P }} if (~b) { ~c1 } else { ~c2 } {{ Q }} := by
  intro st st' hE hP
  inversion hE with
  | ifTrue hb hc => exact htrue _ _ hc ⟨hP, hb⟩
  | ifFalse hb hc => exact hfalse _ _ hc ⟨hP, bexp_eval_false b st hb⟩

-- #### Example

theorem if_example :
    {{True}}
      if (X = 0) {
        Y := 2;
      } else {
        Y := X + 1;
      }
    {{X ≤ Y}} := by
  apply hoare_if
  · -- Then
    apply hoare_consequence_pre
    · apply hoare_asgn
    · -- `assertion_auto` makes no progress here
      unfold AssertImplies Assertion.sub
      intro st ⟨_, h⟩
      simp only [Bexp.eval_eq, Aexp.eval_id, Aexp.eval_num, beq_iff_eq] at h
      rw [TotalMap.update_neq (by decide), TotalMap.update_eq, h]
      simp
  · -- Else
    apply hoare_consequence_pre
    · apply hoare_asgn
    · assertion_auto

-- As we did earlier, it would be nice to eliminate all the
-- low-level proof script that isn't about the Hoare rules.
-- Unfortunately, the `assertion_auto` tactic we wrote wasn't
-- quite up to the job. Looking at the proof of `if_example`,
-- we can see why: we had to unfold a definition (`bassertion`)
-- that we didn't need in earlier proofs. (The step from the
-- boolean equality test `st[X] == 0` to the equation
-- `st[X] = 0` is handled by lemmas `simp` already knows, such
-- as `beq_iff_eq`.) So, let's add the unfolding into our
-- tactic.

-- Note to developers:
--     HIDE: MRC'20: There's probably a better way to engineer
--     this. I don't know Ltac very well though.

/-- Like `assertion_auto`, but also unfolds `bassertion`, so that facts
about the boolean guards of conditionals and loops become available. -/
macro "assertion_auto'" : tactic =>
  `(tactic| (intros
             <;> try (simp [assertImplies_def, ValidHoareTriple, Assertion.sub,
                            TotalMap.update, TotalMap.getElem_def,
                            W, X, Y, Z] at *)
             <;> try lia))

-- Now the proof is quite streamlined.

theorem if_example'' :
    {{True}}
      if (X = 0) {
        Y := 2;
      } else {
        Y := X + 1;
      }
    {{X ≤ Y}} := by
  apply hoare_if
  · apply hoare_consequence_pre
    · apply hoare_asgn
    · assertion_auto'
  · apply hoare_consequence_pre
    · apply hoare_asgn
    · assertion_auto'

-- We can even shorten it a little bit more.

theorem if_example''' :
    {{True}}
      if (X = 0) {
        Y := 2;
      } else {
        Y := X + 1;
      }
    {{X ≤ Y}} := by
  apply hoare_if <;> apply hoare_consequence_pre <;>
    (try apply hoare_asgn) <;> try assertion_auto'

-- Note to developers (Claude):
--     At this point the Rocq source defines a further
--     refinement `assertion_auto''` that also rewrites with
--     `leb_le`, "for inequalities". In Lean the boolean
--     comparisons produced by `Bexp.eval` are already reduced
--     by `simp`'s standard `decide`/`==` lemmas, so
--     `assertion_auto'` handles inequalities as it stands and
--     no `assertion_auto''` is needed (nor the later
--     `assertion_auto'''`, whose extra `negb`/`not_false`
--     rewrites `simp` also covers); occurrences of both in the
--     Rocq text are rendered as `assertion_auto'`.

-- Note to developers:
--     HIDE: Question from 2012, Midterm 2. One-sided
--     conditionals.

-- ### While Loops

-- The Hoare rule for `while` loops is based on the idea of a
-- *command invariant* (or just *invariant*): an assertion
-- whose truth is guaranteed after executing a command,
-- assuming it is true before.

-- That is, an assertion `P` is a command invariant of `c` if

--   {{P}} c {{P}}

-- holds. Note that the command invariant might temporarily
-- become false in the middle of executing `c`, but by the end
-- of `c` it must be restored.

-- The Hoare while rule combines the idea of a command
-- invariant with information about when guard `b` does or does
-- not hold.

--         {{P ∧ b}} c {{P}}
--   --------------------------------- (hoare_while)
--   {{P}} while b do c end {{P ∧ ¬b}}

-- Note to developers:
--     HIDE: The big comment will not display nicely. But I
--     guess it's folded...

theorem hoare_while (P : Assertion) (b : Bexp) (c : Com)
    (hhoare : {{P ∧ #b}} ~c {{ P }}) :
    {{ P }} while (~b) { ~c } {{P ∧ ¬ #b}} := by
  intro st st' heval hP
  /- We proceed by induction on `heval`, because, in the "keep
  looping" case, its hypotheses talk about the whole loop instead
  of just `c`. The auxiliary statement `key` generalizes over an
  arbitrary command, together with an equation remembering that the
  command is the original loop; otherwise, that information would
  be lost in the induction. The cases for commands other than
  `while` are dismissed because their equations are contradictory. -/
  have key : ∀ (cmd : Com) (s s' : State), (s =[ cmd ]=> s') →
      cmd = (imp { while (~b) { ~c } }) → P s →
      P s' ∧ ¬ bassertion b s' := by
    intro cmd s s' hev
    induction hev with
    | whileFalse b0 s0 c0 hb =>
        intro heq hp
        injection heq with e1 _
        subst e1
        exact ⟨hp, bexp_eval_false _ _ hb⟩
    | whileTrue s0 s0' s0'' b0 c0 hb hc hloop ih1 ih2 =>
        intro heq hp
        injection heq with e1 e2
        subst e1 e2
        exact ih2 rfl (hhoare _ _ hc ⟨hp, hb⟩)
    | skip s0 => intro heq; simp at heq
    | asgn s0 a n x h => intro heq; simp at heq
    | seq c1 c2 s0 s0' s0'' h1 h2 ih1 ih2 => intro heq; simp at heq
    | ifTrue s0 s0' b0 c1 c2 hb hc ih => intro heq; simp at heq
    | ifFalse s0 s0' b0 c1 c2 hb hc ih => intro heq; simp at heq
  exact key _ st st' heval rfl hP

-- Note to developers (Benjamin Pierce  @bcpierce00, before next release, 2021):
--     This definition / discussion could be clearer.

-- Note to developers (Benjamin Pierce  @bcpierce00, before next release, 2023):
--     `Maja says: The wording of "we will never enter the
--     loop" could definitely be improved. As is, it suggests a situation
--     where the loop condition itself can never be satisfied. I suspect that
--     a previous draft included a discussion that explicitly placed {{ P }}
--     before the while, perhaps along the lines of "a loop invariant P of
--     [while b do c end] is also an invariant of [while b do c end]" (which
--     is, FWIW, a (somewhat obtuse) way of stating a weaker variant of
--     hoare_while, without the ~b in the postcondition). Combined with the
--     fact that it is supposed to justify a somewhat surprising and
--     unexpected fact — [X = 0] is not what I would intuitively consider an
--     invariant of this loop — this sentence ends up being quite confusing.
--     I only understood it when I came back to find this excerpt.`

-- We call `P` a *loop invariant* of `while b do c end` if

--   {{P ∧ b}} c {{P}}

-- is a valid Hoare triple.

-- This means that `P` will be true at the end of the loop body
-- whenever the loop body executes. If `P` contradicts `b`,
-- this holds trivially since the precondition is false.

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

-- Note to developers (before next release):
--     This last quiz should be turned into a discussion in the
--     text, at least in the full version -- indeed, maybe all
--     these should be turned into a long discussion of what it
--     means to be a loop invariant -- I think that would be
--     pretty helpful.

-- Note to developers (Benjamin Pierce  @bcpierce00, before next release, 2021):
--     What is this example doing here?? Needs some text.

-- Note to developers:
--     `HIDE: CJC: Maybe also a good place to talk about the structure of
--     our logic - that we've set up the hoare_* lemmas and they are all
--     the reasoning about Hoare triples that they should have to use (in
--     both formal or informal proofs)?  Probably should talk about this
--     somewhere or else we'll get back lots of proofs that unfold
--     ValidHoareTriple and reason at a low level everywhere.
--
--     BCP 21: I think we do this now?`

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

-- Note to developers:
--     HIDE: I (BCP) think I see a much simpler way to do the
--     'for' stuff. Instead of `for x from a to b do c` define
--     `for x downfrom a do c` that steps from a down to 0.
--     This will be much simpler to specify, though still an
--     interesting challenge. (CJC: This still seemed hard to
--     me, but I'm deleting it for now to get things looking
--     right)
--
--     HIDE: Coming up with the precise rule for REPEAT is
--     tricky, and so is proving formally that the precise rule
--     passes the litmus test (at this point we only ask them
--     to convince themselves informally there).

-- ## Summary

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

-- Our main task in this chapter has been to *define* the rules
-- of Hoare logic, and prove that the definitions are sound.
-- Having done so, we can go on and work *within* Hoare logic
-- to prove that particular programs satisfy particular Hoare
-- triples. In the next chapter, we'll see how Hoare logic is
-- can be used to prove that more interesting programs satisfy
-- interesting specifications of their behavior.

-- Crucially, we will do so without ever again `unfold`ing the
-- definition of Hoare triples -- i.e., we will take the rules
-- of Hoare logic as a closed world for reasoning about
-- programs.


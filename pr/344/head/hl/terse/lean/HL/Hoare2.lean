import HL.Hoare

import SFLCompat

--  # Hoare2: Hoare Logic, Part II

open scoped Com MyGetElem Assertion HasTriple

--   ----------------------------------------

--  _Quiz:_

--  On a piece of paper (or whatever), write down a
--  Hoare-triple specification for the following program:
--
--      X := 2;
--      Y := X + X

--   ----------------------------------------

--  _Quiz:_

--  Write down a (useful) specification for the following
--  program:
--
--      X := X + 1; Y := X + 1

--   ----------------------------------------

--  _Quiz:_

--  Write down a (useful) specification for the following
--  program:
--
--      if X <= Y then
--        skip
--      else
--        Z := X;
--        X := Y;
--        Y := Z
--      end

--   ----------------------------------------

--  _Quiz:_

--  Write down a (useful) specification for the following
--  program:
--
--      X := m;
--      Y := X + X

--   ----------------------------------------

--  _Quiz:_

--  Write down a (useful) specification for the following
--  program:
--
--      X := m;
--      Z := 0;
--      while X <> 0 do
--        X := X - 2;
--        Z := Z + 1
--      end

--   ----------------------------------------

--  ## Decorated Programs

--  The beauty of Hoare Logic is that it is *syntax
--  directed*: the structure of proofs exactly follows the
--  structure of programs.
--
--  We can record the essential ideas of a Hoare-logic proof
--  — omitting low-level calculational details — by
--  "decorating" a program with appropriate assertions on
--  each of its commands.
--
--  Such a *decorated program* carries within itself an
--  argument for its own correctness.

--  For example, consider the program:
--
--      X := m;
--      Z := p;
--      while X <> 0 do
--        Z := Z - 1;
--        X := X - 1
--      end

--  Here is one possible specification for this program, in
--  the form of a Hoare triple:
--
--      {{ True }}
--      X := m;
--      Z := p;
--      while X <> 0 do
--        Z := Z - 1;
--        X := X - 1
--      end
--      {{ Z = p - m }}

--  Here is a decorated version of this program, embodying a
--  proof of this specification:
--
--      {{ True }} ->>
--      {{ m = m }}
--        X := m
--                           {{ X = m }} ->>
--                           {{ X = m /\ p = p }};
--        Z := p;
--                           {{ X = m /\ Z = p }} ->>
--                           {{ Z - X = p - m }}
--        while X <> 0 do
--                           {{ Z - X = p - m /\ X <> 0 }} ->>
--                           {{ (Z - 1) - (X - 1) = p - m }}
--          Z := Z - 1
--                           {{ Z - (X - 1) = p - m }};
--          X := X - 1
--                           {{ Z - X = p - m }}
--        end
--      {{ Z - X = p - m /\ ~ (X <> 0) }} ->>
--      {{ Z = p - m }}

--  Concretely, a decorated program consists of the
--  program's text interleaved with assertions (sometimes
--  multiple assertions separated by ->>).

--  A decorated program can be viewed as a compact
--  representation of a proof in Hoare Logic: the assertions
--  surrounding each command specify the Hoare triple to be
--  proved for that part of the program using one of the
--  Hoare Logic rules, and the structure of the program
--  itself shows how to assemble all these individual steps
--  into a proof for the whole program.

--  ### Example: Swapping

--  Consider the following program, which swaps the values
--  of two variables using addition and subtraction, instead
--  of by assigning to a temporary variable.
--
--      X := X + Y;
--      Y := X - Y;
--      X := X - Y
--
--  We can give a proof, in the form of decorations, that
--  this program is correct — i.e., it really swaps `X` and
--  `Y` — as follows.

--  WORK IN CLASS

--  ### Example: Simple Conditionals

--  Here's a simple program using conditionals, along with a
--  possible specification:
--
--      {{ True }}
--        if X <= Y then
--          Z := Y - X
--        else
--          Z := X - Y
--        end
--      {{ Z + X = Y \/ Z + Y = X }}
--
--  Let's turn it into a decorated program...

--  WORK IN CLASS

--  ### Example: Reduce to Zero

--  Here is a very simple `while` loop with a simple
--  specification:
--
--      {{ True }}
--        while (X <> 0) do
--          X := X - 1
--        end
--      {{ X = 0 }}

--  WORK IN CLASS

--  ### Example: Division

--  Let's do one more example of simple reasoning about a
--  loop.
--
--  The following Imp program calculates the integer
--  quotient and remainder of parameters `m` and `n`.
--
--      X := m;
--      Y := 0;
--      while n <= X do
--        X := X - n;
--        Y := Y + 1
--      end;
--
--  If we replace `m` and `n` by concrete numbers and
--  execute the program, it will terminate with the variable
--  `X` set to the remainder when `m` is divided by `n` and
--  `Y` set to the quotient.

--  Here's a possible specification:
--
--      {{ True }}
--        X := m;
--        Y := 0;
--        while n <= X do
--          X := X - n;
--          Y := Y + 1
--        end
--      {{ n * Y + X = m /\ X < n }}

--  WORK IN CLASS

--  ### From Decorated Programs to Formal Proofs

--  From an informal proof in the form of a decorated
--  program, it is "easy in principle" to read off a formal
--  proof using the Lean theorems corresponding to the Hoare
--  Logic rules, but these proofs can be a bit long and
--  fiddly.

--  For example...

def reduceToZero : Com :=
  imp {
    while (X ≠ 0) {
      X := X - 1
    }
  }

theorem reduce_to_zero_correct' :
    {{ True }} ~reduceToZero {{ X = 0 }} := by
  -- First put the postcondition into the form expected by
  -- the while rule.
  sorry

--  A little more (OK, quite a bit more) tactic fanciness
--  for helping deal with the boring parts of the process of
--  proving assertions:

macro "verify_assertion" : tactic =>
  `(tactic| assertion_auto)

--  This makes it pretty easy to verify `reduce_to_zero`:

theorem reduce_to_zero_correct''' :
    {{ True }} ~reduceToZero {{ X = 0 }} := by
  sorry

--  This example shows that it is conceptually
--  straightforward to read off the main elements of a
--  formal proof from a decorated program. Indeed, the
--  process is so straightforward that it can be automated,
--  as we will see next.

--  ## Formal Decorated Programs

--  With a little more work, we can *formalize* the
--  definition of well-formed decorated programs and
--  *automate* the boring mechanical steps in proving that
--  the decorations are correct.

--  ### Syntax

--  The first thing we need to do is to formalize a variant
--  of the syntax of Imp commands that includes embedded
--  assertions, which we'll call "decorations." We call the
--  new commands *decorated commands*, or `dcom`s.
--
--  The choice of exactly where to put assertions in the
--  definition of `dcom` is a bit subtle. The simplest thing
--  to do would be to annotate every `dcom` with a
--  precondition and postcondition — something like this...

namespace DComFirstTry

inductive DCom where
  | skip (pre : Assertion)
  | seq (pre : Assertion) (first : DCom)
      (middle : Assertion)
      (second : DCom) (post : Assertion)
  | asgn (x : Ident) (a : Aexp) (post : Assertion)
  | cond (pre : Assertion) (b : Bexp)
      (thenPre : Assertion) (thenBranch : DCom)
      (elsePre : Assertion) (elseBranch : DCom)
      (post : Assertion)
  | whileDo (pre : Assertion) (b : Bexp)
      (bodyPre : Assertion) (body : DCom)
      (bodyPost : Assertion) (post : Assertion)
  | strengthenPre (pre : Assertion) (body : DCom)
  | weakenPost (body : DCom) (post : Assertion)

end DComFirstTry

--  But this would result in *very* verbose decorated
--  programs with a lot of repeated annotations: a simple
--  program like `skip;skip` would be decorated like this,
--
--      {{P}} ({{P}} skip {{P}}) ; ({{P}} skip {{P}}) {{P}}
--
--  with pre- and post-conditions around each `skip`, plus
--  identical pre- and post-conditions on the semicolon!

--  In other words, we don't want both preconditions and
--  postconditions on each command, because a sequence of
--  two commands would contain redundant decorations — the
--  postcondition of the first likely being the same as the
--  precondition of the second.
--
--  Instead, our formal syntax of decorated commands will
--  omit preconditions whenever possible and embed just
--  postconditions.

--  - The `skip` command, for example, is decorated only
--    with its postcondition
--
--      skip {{ Q }}
--
--  on the assumption that the precondition will be provided
--  by somebody else.
--
--  We carry the same assumption through the other syntactic
--  forms: each decorated command is assumed to carry its
--  own postcondition within itself but take its
--  precondition from its context in which it is used.

--  - Sequences `d1 ; d2` need no additional decorations.
--
--  Why?
--
--  Because inside `d2` there will be a postcondition, which
--  also serves as the postcondition of `d1;d2`.
--
--  Similarly, inside `d1` there will also be a
--  postcondition, which additionally serves as the
--  *precondition* for `d2`.

--  - An assignment `X := a` is decorated only with its
--    postcondition:
--
--      X := a {{ Q }}

--  - A conditional `if b then d1 else d2` is decorated with
--    a postcondition for the entire statement, as well as
--    preconditions for each branch:
--
--      if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }}

--  - A loop `while b do d end` is decorated with its final
--    postcondition plus a precondition for the body:
--
--      while b do {{ P }} d end {{ Q }}
--
--  The postcondition embedded in `d` serves as the loop
--  invariant.

--  - Implications `->>` can be added as decorations either
--    for a precondition...
--
--      ->> {{ P }} d
--
--  ...or for a postcondition:
--
--      d ->> {{ Q }}
--
--  The former is waiting for another precondition to be
--  supplied by the context; the latter relies on the
--  postcondition already embedded in `d`.

--  Putting this all together gives us the formal syntax of
--  decorated commands:

inductive DCom where
  | skip (post : Assertion)
  | seq (first second : DCom)
  | asgn (x : Ident) (a : Aexp) (post : Assertion)
  | cond (b : Bexp)
      (thenPre : Assertion) (thenBranch : DCom)
      (elsePre : Assertion) (elseBranch : DCom)
      (post : Assertion)
  | whileDo (b : Bexp) (bodyPre : Assertion) (body : DCom)
      (post : Assertion)
  | pre (pre : Assertion) (body : DCom)
  | post (body : DCom) (post : Assertion)

--  Lean keeps decorated-command notation in its own syntax
--  category, `dcom`, so it can coexist with the ordinary
--  Imp command syntax.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: decorated commands)
declare_syntax_cat dcom

syntax:max "(" dcom ")" : dcom
syntax:max "skip" " {{" term "}}" : dcom
syntax:max ident " := " imp_aexp " {{" term "}}" : dcom
syntax:20 dcom:21 ";" ppLine dcom:20 : dcom
syntax:max "if " "(" imp_bexp ")" ppHardSpace "then" ppLine
  "{{" term "}}" ppLine dcom ppLine
  "else" ppLine "{{" term "}}" ppLine dcom ppLine
  "end" ppLine "{{" term "}}" : dcom
syntax:max "while " "(" imp_bexp ")" ppHardSpace "do" ppLine
  "{{" term "}}" ppLine dcom ppLine
  "end" ppLine "{{" term "}}" : dcom
syntax:5 "->>" " {{" term "}}" ppLine dcom:0 : dcom
syntax:5 dcom:6 ppLine "->>" " {{" term "}}" : dcom

syntax:min "dcom" ppHardSpace "{" ppLine dcom
  ppDedent(ppLine "}") : term

macro_rules
  | `(dcom { ($body:dcom) }) =>
      `(dcom { $body })
  | `(dcom { skip {{ $q }} }) =>
      `(DCom.skip ({{ $q }}))
  | `(dcom { $x:ident := $a:imp_aexp {{ $q }} }) =>
      `(DCom.asgn $x (aexp { $a }) ({{ $q }}))
  | `(dcom { $d1:dcom; $d2:dcom }) =>
      `(DCom.seq (dcom { $d1 }) (dcom { $d2 }))
  | `(dcom {
        if ($b:imp_bexp) then
          {{ $p1 }}
          $d1:dcom
        else
          {{ $p2 }}
          $d2:dcom
        end
          {{ $q }}
      }) =>
      `(DCom.cond (bexp { $b })
        ({{ $p1 }}) (dcom { $d1 })
        ({{ $p2 }}) (dcom { $d2 })
        ({{ $q }}))
  | `(dcom {
        while ($b:imp_bexp) do
          {{ $p }}
          $body:dcom
        end
          {{ $q }}
      }) =>
      `(DCom.whileDo (bexp { $b }) ({{ $p }})
        (dcom { $body }) ({{ $q }}))
  | `(dcom { ->> {{ $p }} $body:dcom }) =>
      `(DCom.pre ({{ $p }}) (dcom { $body }))
  | `(dcom { $body:dcom ->> {{ $q }} }) =>
      `(DCom.post (dcom { $body }) ({{ $q }}))
--  END DETAILS

--  (We then need to redefine all our Notations to get nice
--  concrete syntax for `dcom`.)

--  To provide the initial precondition that goes at the
--  very top of a decorated program, we introduce a new type
--  `decorated`:

structure Decorated where
  pre : Assertion
  body : DCom

example : DCom :=
  .skip ({{ True }})

example : DCom :=
  .whileDo (bexp {true}) ({{ True }})
    (.skip ({{ True }})) ({{ True }})

--  To inspect the fully elaborated term behind this
--  notation, put `set_option pp.all true in` before a
--  `#check` or `#print` command.
--
--  The formal definitions can use either constructors
--  directly or the decorated-command notation introduced
--  above.

--  An example `decorated` program that decrements `X` to
--  `0`:

def decWhile : Decorated where
  pre := ({{ True }})
  body := dcom {
    while (X ≠ 0) do
      {{ True ∧ ¬ X = 0 }}
      X := X - 1 {{ True }}
    end
      {{ True ∧ X = 0 }}
    ->> {{ X = 0 }}
  }

--  It is easy to go from a `dcom` to a `com` by erasing all
--  annotations.

def DCom.erase (d : DCom) : Com :=
  match d with
  | .skip _ => .skip
  | .seq d1 d2 => .seq d1.erase d2.erase
  | .asgn x a _ => .asgn x a
  | .cond b _ d1 _ d2 _ => .cond b d1.erase d2.erase
  | .whileDo b _ body _ => .whileDo b body.erase
  | .pre _ body => body.erase
  | .post body _ => body.erase

def Decorated.erase (dec : Decorated) : Com :=
  dec.body.erase

--  It is also straightforward to extract the precondition
--  and postcondition from a decorated program.

def Decorated.precondition (dec : Decorated) : Assertion :=
  dec.pre

def DCom.postcondition (d : DCom) : Assertion :=
  match d with
  | .skip q => q
  | .seq _ d2 => d2.postcondition
  | .asgn _ _ q => q
  | .cond _ _ _ _ _ q => q
  | .whileDo _ _ _ q => q
  | .pre _ body => body.postcondition
  | .post _ q => q

def Decorated.postcondition (dec : Decorated) : Assertion :=
  dec.body.postcondition

--  We can then express what it means for a decorated
--  program to be correct as follows:

def Decorated.OuterTripleValid (dec : Decorated) : Prop :=
  ValidHoareTriple dec.precondition dec.erase
    dec.postcondition

--  For example:

example :
    decWhile.OuterTripleValid =
      {{ True }}
        while (X ≠ 0) {
          X := X - 1
        }
      {{ X = 0 }} := by
  rfl

--  The outer Hoare triple of a decorated program is just a
--  `Prop`; thus, to show that it is *valid*, we need to
--  produce a proof of this proposition.
--
--  We will do this by extracting "proof obligations" from
--  the decorations sprinkled throughout the program.
--
--  These obligations are often called *verification
--  conditions*, because they are the facts that must be
--  verified to see that the decorations are locally
--  consistent and thus constitute a proof of validity of
--  the outer triple.

--  ### Extracting Verification Conditions

--  The function `DCom.VerificationConditions` takes a
--  decorated command `d` together with a precondition `P`
--  and returns a *proposition* that, if it can be proved,
--  implies that the triple
--
--      {{P}} d.erase {{d.postcondition}}
--
--  is valid.
--
--  It does this by walking over `d` and generating a big
--  conjunction that includes
--
--  - local consistency checks for each form of command,
--    plus
--
--  - uses of `->>` to bridge the gap between the assertions
--    found inside a decorated command and the assertions
--    imposed by the external precondition; these uses
--    correspond to applications of the consequence rule.

--  *Local consistency* is defined as follows...
--
--  - The decorated command
--
--      skip {{Q}}
--
--  is locally consistent with respect to a precondition `P`
--  if `P ->> Q`.

--  - The sequential composition of `d1` and `d2` is locally
--    consistent with respect to `P` if `d1` is locally
--    consistent with respect to `P` and `d2` is locally
--    consistent with respect to the postcondition of `d1`.

--  - An assignment
--
--      X := a {{Q}}
--
--  is locally consistent with respect to a precondition `P`
--  if:
--
--      P ->> Q [X |-> a]

--  - A conditional
--
--      if b then {{P1}} d1 else {{P2}} d2 end {{Q}}
--
--  is locally consistent with respect to precondition `P`
--  if
--
--  (1) `P /\ b ->> P1`
--
--  (2) `P /\ ~b ->> P2`
--
--  (3) `d1` is locally consistent with respect to `P1`
--
--  (4) `d2` is locally consistent with respect to `P2`
--
--  (5) `d1.postcondition ->> Q`
--
--  (6) `d2.postcondition ->> Q`

--  - A loop
--
--      while b do {{Q}} d end {{R}}
--
--  is locally consistent with respect to precondition `P`
--  if:
--
--  (1) `P ->> d.postcondition`
--
--  (2) `d.postcondition /\ b ->> Q`
--
--  (3) `d.postcondition /\ ~b ->> R`
--
--  (4) `d` is locally consistent with respect to `Q`

--  - A command with an extra assertion at the beginning
--
--      ->> {{Q}} d
--
--  is locally consistent with respect to a precondition `P`
--  if:
--
--  (1) `P ->> Q`
--
--  (2) `d` is locally consistent with respect to `Q`

--  - A command with an extra assertion at the end
--
--      d ->> {{Q}}
--
--  is locally consistent with respect to a precondition `P`
--  if:
--
--  (1) `d` is locally consistent with respect to `P`
--
--  (2) `d.postcondition ->> Q`

--  With all this in mind, we can write a *verification
--  condition generator* that takes a decorated command and
--  reads off a proposition saying that all its decorations
--  are locally consistent.
--
--  Formally, since a decorated command is "waiting for its
--  precondition" the main VC generator takes a `dcom` plus
--  a given precondition as arguments.

def DCom.VerificationConditions
    (P : Assertion) (d : DCom) : Prop :=
  match d with
  | .skip Q =>
      P ->> Q
  | .seq d1 d2 =>
      d1.VerificationConditions P ∧
      d2.VerificationConditions d1.postcondition
  | .asgn x a Q =>
      P ->> {{ Q [x ↦ ~a] }}
  | .cond b P1 d1 P2 d2 Q =>
      ({{ P ∧ b }} ->> P1) ∧
      ({{ P ∧ ¬ b }} ->> P2) ∧
      (d1.postcondition ->> Q) ∧
      (d2.postcondition ->> Q) ∧
      d1.VerificationConditions P1 ∧
      d2.VerificationConditions P2
  | .whileDo b bodyPre body q =>
      -- The body's postcondition is both the loop invariant
      -- and the precondition for the first iteration.
      (P ->> body.postcondition) ∧
      ({{ body.postcondition ∧ b }} ->> bodyPre) ∧
      ({{ body.postcondition ∧ ¬ b }} ->> q) ∧
      body.VerificationConditions bodyPre
  | .pre P' body =>
      (P ->> P') ∧ body.VerificationConditions P'
  | .post body Q =>
      body.VerificationConditions P ∧
      (body.postcondition ->> Q)

--  The following key theorem states that
--  `DCom.VerificationConditions` does its job correctly.
--  Not surprisingly, each of the Hoare Logic rules plays a
--  critical role at some point in the proof.

theorem verification_correct (d : DCom) (P : Assertion)
    (hvc : d.VerificationConditions P) :
    ValidHoareTriple P d.erase d.postcondition := by
  sorry

--  Now that all the pieces are in place, we can define what
--  it means to verify an entire program.

def Decorated.VerificationConditions
    (dec : Decorated) : Prop :=
  dec.body.VerificationConditions dec.pre

--  And this brings us to the main theorem of this section:

theorem verification_conditions_correct (dec : Decorated)
    (hvc : dec.VerificationConditions) :
    dec.OuterTripleValid := by
  exact verification_correct dec.body dec.pre hvc

--  ### More Automation

--  The propositions generated by
--  `DCom.VerificationConditions` are fairly big and contain
--  many conjuncts that are essentially trivial.

example : decWhile.VerificationConditions := by
  unfold Decorated.VerificationConditions decWhile
  simp only [DCom.VerificationConditions,
    DCom.postcondition]
  sorry

--  Fortunately, our `verify_assertion` tactic can generally
--  take care of most (or sometimes all) of them.

example : decWhile.VerificationConditions := by
  sorry

--  To automate the overall process of verification, we can
--  use `verification_correct` to extract the verification
--  conditions, use `verify_assertion` to verify them as
--  much as it can, and finally tidy up any remaining bits
--  by hand.

macro "verify" : tactic =>
  `(tactic|
    (apply verification_conditions_correct;
     verify_assertion))

--  Here's the final, formal proof that `decWhile` is
--  correct.

theorem dec_while_correct :
    decWhile.OuterTripleValid := by
  sorry

--  ## Finding Loop Invariants

--  Once the outer pre- and postcondition are chosen, the
--  only creative part in verifying programs using Hoare
--  Logic is finding the right loop invariants...

--  ### Example: Slow Subtraction

--  The following program subtracts the value of `X` from
--  the value of `Y` by repeatedly decrementing both `X` and
--  `Y`. We want to verify its correctness with respect to
--  the pre- and postconditions shown:
--
--      {{ X = m /\ Y = n }}
--        while X <> 0 do
--          Y := Y - 1;
--          X := X - 1
--        end
--      {{ Y = n - m }}

--  To verify this program, we need to find an invariant
--  `Inv` for the loop. As a first step we can leave `Inv`
--  as an unknown and build a *skeleton* for the proof by
--  applying the rules for local consistency, working from
--  the end of the program to the beginning, as usual, and
--  without doing any thinking at all yet.

--  This leads to the following skeleton:
--
--      (1)    {{ X = m /\ Y = n }}  ->>                   (a)
--      (2)    {{ Inv }}
--               while X <> 0 do
--      (3)              {{ Inv /\ X <> 0 }}  ->>          (c)
--      (4)              {{ Inv [X |-> X-1] [Y |-> Y-1] }}
--                 Y := Y - 1;
--      (5)              {{ Inv [X |-> X-1] }}
--                 X := X - 1
--      (6)              {{ Inv }}
--               end
--      (7)    {{ Inv /\ ~ (X <> 0) }}  ->>                (b)
--      (8)    {{ Y = n - m }}

--  Examining this skeleton, we can see that any valid `Inv`
--  will have to respect three conditions:
--
--  - (a) it must be *weak* enough to be implied by the
--    loop's precondition, i.e., (1) must imply (2);
--
--  - (b) it must be *strong* enough to imply the program's
--    postcondition, i.e., (7) must imply (8);
--
--  - (c) it must be *preserved* by a single iteration of
--    the loop, assuming that the loop guard also evaluates
--    to true, i.e., (3) must imply (4).

--  WORK IN CLASS (by filling in the previous template)

--  ## Weakest Preconditions (Optional)

--  A useless (though valid) Hoare triple:
--
--      {{ False }}  X := Y + 1  {{ X <= 5 }}
--
--  A better precondition:
--
--      {{ Y <= 4 /\ Z = 0 }}  X := Y + 1 {{ X <= 5 }}
--
--  The *best* precondition:
--
--      {{ Y <= 4 }}  X := Y + 1  {{ X <= 5 }}

--  Assertion `Y <= 4` is a *weakest precondition* of
--  command `X := Y + 1` with respect to postcondition
--  `X <= 5`. Think of *weakest* here as meaning "easiest to
--  satisfy": a weakest precondition is one that as many
--  states as possible can satisfy.

--  `P` is a weakest precondition of command `c` for
--  postcondition `Q` if
--
--  - `P` is a precondition, that is, `{{P}} c {{Q}}`; and
--
--  - `P` is at least as weak as all other preconditions,
--    that is, if `{{P'}} c {{Q}}` then `P' ->> P`.
--
--  Note that weakest preconditions need not be unique. For
--  example, `Y <= 4` was a weakest precondition above, but
--  so are the logically equivalent assertions `Y < 5`,
--  `Y <= 2 * 2`, etc. It is easy to show that any two
--  weakest preconditions `P` and `P'` of a command `c` with
--  respect to postcondition `Q` are logically equivalent;
--  that is, `P <<->> P'`.

def IsWp (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ValidHoareTriple P c Q ∧
  ∀ P' : Assertion, {{ P' }} ~c {{ Q }} → P' ->> P

--  ### Exercise (1 star): wp (Optional) ⭐

--  What are weakest preconditions of the following commands
--  for the following postconditions?
--
--      1) {{ ? }}  skip  {{ X = 5 }}
--
--      2) {{ ? }}  X := Y + Z {{ X = 5 }}
--
--      3) {{ ? }}  X := Y  {{ X = Y }}
--
--      4) {{ ? }}
--       if X = 0 then Y := Z + 1 else Y := W + 2 end
--       {{ Y = 5 }}
--
--      5) {{ ? }}
--       X := 5
--       {{ X = 0 }}
--
--      6) {{ ? }}
--       while true do X := 0 end
--       {{ X = 0 }}

-- Built on 2026-08-31 12:08 UTC

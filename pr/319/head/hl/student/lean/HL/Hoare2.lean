import HL.Hoare

import SFLCompat

--  # Hoare2: Hoare Logic, Part II

open scoped Com MyGetElem Assertion HasTriple

--   ----------------------------------------

--  _Quiz:_

--  On a piece of paper (or whatever), write down a Hoare-triple
--  specification for the following program:
--
--      X := 2;
--      Y := X + X

--   ----------------------------------------

--  _Quiz:_

--  Write down a (useful) specification for the following program:
--
--      X := X + 1; Y := X + 1

--   ----------------------------------------

--  _Quiz:_

--  Write down a (useful) specification for the following program:
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

--  Write down a (useful) specification for the following program:
--
--      X := m;
--      Y := X + X

--   ----------------------------------------

--  _Quiz:_

--  Write down a (useful) specification for the following program:
--
--      X := m;
--      Z := 0;
--      while X <> 0 do
--        X := X - 2;
--        Z := Z + 1
--      end

--   ----------------------------------------

--  ## Decorated Programs

--  The beauty of Hoare Logic is that it is *syntax directed*: the
--  structure of proofs exactly follows the structure of programs.
--
--  We can record the essential ideas of a Hoare-logic proof — omitting
--  low-level calculational details — by "decorating" a program with
--  appropriate assertions on each of its commands.
--
--  Such a *decorated program* carries within itself an argument for its
--  own correctness.
--
--  For example, consider the program:
--
--      X := m;
--      Z := p;
--      while X <> 0 do
--        Z := Z - 1;
--        X := X - 1
--      end
--
--  Here is one possible specification for this program, in the form of a
--  Hoare triple:
--
--      {{ True }}
--      X := m;
--      Z := p;
--      while X <> 0 do
--        Z := Z - 1;
--        X := X - 1
--      end
--      {{ Z = p - m }}

--  (Note the *parameters* `m` and `p`, which stand for fixed-but-arbitrary
--  numbers. Formally, they are simply Lean variables of type `Nat`.)

--  Here is a decorated version of this program, embodying a proof of this
--  specification:
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
--
--  Concretely, a decorated program consists of the program's text
--  interleaved with assertions (sometimes multiple assertions separated by
--  ->>).
--
--  A decorated program can be viewed as a compact representation of a
--  proof in Hoare Logic: the assertions surrounding each command specify
--  the Hoare triple to be proved for that part of the program using one of
--  the Hoare Logic rules, and the structure of the program itself shows
--  how to assemble all these individual steps into a proof for the whole
--  program.

--  Our goal is to verify such decorated programs "mostly automatically."
--  But, before we can verify anything, we need to be able to *find* a
--  proof for a given specification, and for this we need to discover the
--  right assertions. This can be done in an almost mechanical way, with
--  the exception of finding loop invariants. In the remainder of this
--  section, we explain in detail how to construct decorations for several
--  short programs, all of which are loop free or have simple loop
--  invariants. We'll return to finding more interesting loop invariants
--  later in the chapter.

--  ### Example: Swapping

--  Consider the following program, which swaps the values of two variables
--  using addition and subtraction, instead of by assigning to a temporary
--  variable.
--
--      X := X + Y;
--      Y := X - Y;
--      X := X - Y
--
--  We can give a proof, in the form of decorations, that this program is
--  correct — i.e., it really swaps `X` and `Y` — as follows.

--      (1)    {{ X = m /\ Y = n }} ->>
--      (2)    {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
--               X := X + Y
--      (3)                     {{ X - (X - Y) = n /\ X - Y = m }};
--               Y := X - Y
--      (4)                     {{ X - Y = n /\ Y = m }};
--               X := X - Y
--      (5)    {{ X = n /\ Y = m }}
--
--  The decorations can be constructed as follows:
--
--  - We begin with the undecorated program (the unnumbered lines).
--
--  - We add the specification — i.e., the outer precondition (1) and
--    postcondition (5). In the precondition, we use parameters `m` and `n`
--    to remember the initial values of variables `X` and `Y` so that we
--    can refer to them in the postcondition (5).
--
--  - We work backwards, mechanically, starting from (5) and proceeding
--    until we get to (2). At each step, we obtain the precondition of the
--    assignment from its postcondition by substituting the assigned
--    variable with the right-hand-side of the assignment. For instance, we
--    obtain (4) by substituting `X` with `X - Y` in (5), and we obtain (3)
--    by substituting `Y` with `X - Y` in (4).
--
--  - Finally, we verify that (1) logically implies (2) — i.e., that the
--    step from (1) to (2) is a valid use of the law of consequence — by
--    doing a bit of high-school algebra.

--  ### Example: Simple Conditionals

--  Here is a simple decorated program using conditionals:
--
--      (1)   {{ True }}
--              if X <= Y then
--      (2)                    {{ True /\ X <= Y }} ->>
--      (3)                    {{ (Y - X) + X = Y \/ (Y - X) + Y = X }}
--                Z := Y - X
--      (4)                    {{ Z + X = Y \/ Z + Y = X }}
--              else
--      (5)                    {{ True /\ ~(X <= Y) }} ->>
--      (6)                    {{ (X - Y) + X = Y \/ (X - Y) + Y = X }}
--                Z := X - Y
--      (7)                    {{ Z + X = Y \/ Z + Y = X }}
--              end
--      (8)   {{ Z + X = Y \/ Z + Y = X }}
--
--  These decorations can be constructed as follows:
--
--  - We start with the outer precondition (1) and postcondition (8).
--
--  - Following the format dictated by the `hoare_if` rule, we copy the
--    postcondition (8) to (4) and (7). We conjoin the precondition (1)
--    with the guard of the conditional to obtain (2). We conjoin (1) with
--    the negated guard of the conditional to obtain (5).
--
--  - In order to use the assignment rule and obtain (3), we substitute `Z`
--    by `Y - X` in (4). To obtain (6) we substitute `Z` by `X - Y` in (7).
--
--  - Finally, we verify that (2) implies (3) and (5) implies (6). Both of
--    these implications crucially depend on the ordering of `X` and `Y`
--    obtained from the guard. For instance, knowing that `X <= Y` ensures
--    that subtracting `X` from `Y` and then adding back `X` produces `Y`,
--    as required by the first disjunct of (3). Similarly, knowing that
--    `~ (X <= Y)` ensures that subtracting `Y` from `X` and then adding
--    back `Y` produces `X`, as needed by the second disjunct of (6). Note
--    that `n - m + m = n` does *not* hold for arbitrary natural numbers
--    `n` and `m` (for example, [3 - 5 + 5 = 5]).

--  ### Exercise (2 stars): if_minus_plus_reloaded (Optional, Manually graded) ⭐⭐

--  N.b.: Although this exercise is marked optional, it is an excellent
--  warm-up for the (non-optional) `if_minus_plus_correct` exercise below!
--
--  Fill in valid decorations for the following program:
--
--      {{ True }}
--        if X <= Y then
--                  {{                         }} ->>
--                  {{                         }}
--          Z := Y - X
--                  {{                         }}
--        else
--                  {{                         }} ->>
--                  {{                         }}
--          Y := X + Z
--                  {{                         }}
--        end
--      {{ Y = X + Z }}
--
--  Briefly justify each use of `->>`.

--  ### Example: Reduce to Zero

--  Here is a `while` loop that is so simple that `True` suffices as a loop
--  invariant.
--
--      (1)    {{ True }}
--               while X <> 0 do
--      (2)                  {{ True /\ X <> 0 }} ->>
--      (3)                  {{ True }}
--                 X := X - 1
--      (4)                  {{ True }}
--               end
--      (5)    {{ True /\ ~(X <> 0) }} ->>
--      (6)    {{ X = 0 }}
--
--  The decorations can be constructed as follows:
--
--  - Start with the outer precondition (1) and postcondition (6).
--
--  - Following the format dictated by the `hoare_while` rule, we copy (1)
--    to (4). We conjoin (1) with the guard to obtain (2). We also conjoin
--    (1) with the negation of the guard to obtain (5).
--
--  - Because the final postcondition (6) does not syntactically match (5),
--    we add an implication between them.
--
--  - Using the assignment rule with assertion (4), we trivially substitute
--    and obtain assertion (3).
--
--  - We add the implication between (2) and (3).
--
--  Finally we check that the implications do hold; both are trivial.

--  ### Example: Division

--  Let's do one more example of simple reasoning about a loop.
--
--  The following Imp program calculates the integer quotient and remainder
--  of parameters `m` and `n`.
--
--      X := m;
--      Y := 0;
--      while n <= X do
--        X := X - n;
--        Y := Y + 1
--      end;
--
--  If we replace `m` and `n` by concrete numbers and execute the program,
--  it will terminate with the variable `X` set to the remainder when `m`
--  is divided by `n` and `Y` set to the quotient.

--  In order to give a specification to this program we need to remember
--  that dividing `m` by `n` produces a remainder `X` and a quotient `Y`
--  such that `n * Y + X = m /\ X < n`.
--
--  It turns out that we get lucky with this program and don't have to
--  think very hard about the loop invariant: the loop invariant is just
--  the first conjunct, `n * Y + X = m`, and we can use this to decorate
--  the program.
--
--       (1)  {{ True }} ->>
--       (2)  {{ n * 0 + m = m }}
--              X := m;
--       (3)                     {{ n * 0 + X = m }}
--              Y := 0;
--       (4)                     {{ n * Y + X = m }}
--              while n <= X do
--       (5)                     {{ n * Y + X = m /\ n <= X }} ->>
--       (6)                     {{ n * (Y + 1) + (X - n) = m }}
--                X := X - n;
--       (7)                     {{ n * (Y + 1) + X = m }}
--                Y := Y + 1
--       (8)                     {{ n * Y + X = m }}
--              end
--       (9)  {{ n * Y + X = m /\ ~ (n <= X) }} ->>
--      (10)  {{ n * Y + X = m /\ X < n }}
--
--  Assertions (4), (5), (8), and (9) are derived mechanically from the
--  loop invariant and the loop's guard. Assertions (8), (7), and (6) are
--  derived using the assignment rule going backwards from (8) to (6).
--  Assertions (4), (3), and (2) are again backwards applications of the
--  assignment rule.
--
--  Now that we've decorated the program it only remains to check that the
--  uses of the consequence rule are correct — i.e., that (1) implies (2),
--  that (5) implies (6), and that (9) implies (10). This is indeed the
--  case:
--
--  - (1) ->> (2): trivial, by algebra.
--
--  - (5) ->> (6): because `n <= X`, we are guaranteed that the subtraction
--    in (6) does not get zero-truncated. We can therefore rewrite (6) as
--    `n * Y + n + X - n` and cancel the `n`s, which results in the left
--    conjunct of (5).
--
--  - (9) ->> (10): if `~ (n <= X)` then `X < n`. That's straightforward
--    from high-school algebra. So, we have a valid decorated program.

--  ### From Decorated Programs to Formal Proofs

--  From an informal proof in the form of a decorated program, it is "easy
--  in principle" to read off a formal proof using the Lean theorems
--  corresponding to the Hoare Logic rules, but these proofs can be a bit
--  long and fiddly.

--  Note that we do *not* unfold the definition of `ValidHoareTriple`
--  anywhere in this proof: the point of the game we're playing now is to
--  use the Hoare rules as a self-contained logic for reasoning about
--  programs.

--  For example...

def reduceToZero : Com :=
  imp {
    while (X ≠ 0) {
      X := X - 1
    }
  }

theorem reduce_to_zero_correct' :
    {{ True }} reduceToZero {{ X = 0 }} := by
  -- First put the postcondition into the form expected by
  -- the while rule.
  sorry

--  In Hoare we introduced a series of tactics named `assertion_auto` to
--  automate proofs involving assertions.
--
--  The following declaration introduces a more sophisticated tactic that
--  will help with proving assertions throughout the rest of this chapter.
--  You don't need to understand the details, but briefly: it introduces
--  the available hypotheses, simplifies assertions, maps, and arithmetic
--  expressions, and then asks `lia` to solve linear arithmetic goals.
--  What's left after `verify_assertion` does its work should be just the
--  "interesting parts" of the proof (which, if we're lucky, might be
--  nothing at all!).

macro "verify_assertion" : tactic =>
  `(tactic| assertion_auto)

--  This makes it pretty easy to verify `reduce_to_zero`:

theorem reduce_to_zero_correct''' :
    {{ True }} reduceToZero {{ X = 0 }} := by
  sorry

--  This example shows that it is conceptually straightforward to read off
--  the main elements of a formal proof from a decorated program. Indeed,
--  the process is so straightforward that it can be automated, as we will
--  see next.

--  ## Formal Decorated Programs

--  Our informal conventions for decorated programs amount to a way of
--  "displaying" Hoare triples, in which commands are annotated with enough
--  embedded assertions that checking the validity of a triple is reduced
--  to simple logical and algebraic calculations showing that some
--  assertions imply others.
--
--  In this section, we show that this presentation style can be made
--  completely formal — and indeed that checking the validity of decorated
--  programs can be largely automated.

--  ### Syntax

--  The first thing we need to do is to formalize a variant of the syntax
--  of Imp commands that includes embedded assertions, which we'll call
--  "decorations." We call the new commands *decorated commands*, or
--  `dcom`s.
--
--  The choice of exactly where to put assertions in the definition of
--  `dcom` is a bit subtle. The simplest thing to do would be to annotate
--  every `dcom` with a precondition and postcondition — something like
--  this...

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

--  But this would result in *very* verbose decorated programs with a lot
--  of repeated annotations: a simple program like `skip;skip` would be
--  decorated like this,
--
--      {{P}} ({{P}} skip {{P}}) ; ({{P}} skip {{P}}) {{P}}
--
--  with pre- and post-conditions around each `skip`, plus identical pre-
--  and post-conditions on the semicolon!
--
--  In other words, we don't want both preconditions and postconditions on
--  each command, because a sequence of two commands would contain
--  redundant decorations — the postcondition of the first likely being the
--  same as the precondition of the second.
--
--  Instead, our formal syntax of decorated commands will omit
--  preconditions whenever possible and embed just postconditions.
--
--  - The `skip` command, for example, is decorated only with its
--    postcondition
--
--      skip {{ Q }}
--
--  on the assumption that the precondition will be provided by somebody
--  else.
--
--  We carry the same assumption through the other syntactic forms: each
--  decorated command is assumed to carry its own postcondition within
--  itself but take its precondition from its context in which it is used.
--
--  - Sequences `d1 ; d2` need no additional decorations.
--
--  Why?
--
--  Because inside `d2` there will be a postcondition, which also serves as
--  the postcondition of `d1;d2`.
--
--  Similarly, inside `d1` there will also be a postcondition, which
--  additionally serves as the *precondition* for `d2`.
--
--  - An assignment `X := a` is decorated only with its postcondition:
--
--      X := a {{ Q }}
--
--  - A conditional `if b then d1 else d2` is decorated with a
--    postcondition for the entire statement, as well as preconditions for
--    each branch:
--
--      if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }}
--
--  - A loop `while b do d end` is decorated with its final postcondition
--    plus a precondition for the body:
--
--      while b do {{ P }} d end {{ Q }}
--
--  The postcondition embedded in `d` serves as the loop invariant.
--
--  - Implications `->>` can be added as decorations either for a
--    precondition...
--
--      ->> {{ P }} d
--
--  ...or for a postcondition:
--
--      d ->> {{ Q }}
--
--  The former is waiting for another precondition to be supplied by the
--  context; the latter relies on the postcondition already embedded in
--  `d`.
--
--  Putting this all together gives us the formal syntax of decorated
--  commands:

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

--  Lean keeps decorated-command notation in its own syntax category,
--  `dcom`, so it can coexist with the ordinary Imp command syntax.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding: decorated commands)
declare_syntax_cat dcom

syntax:max "(" dcom ")" : dcom
syntax:max "skip" " {{" term "}}" : dcom
syntax:max ident " := " imp_aexp " {{" term "}}" : dcom
syntax:20 dcom:21 ";" ppDedent(ppLine dcom:20) : dcom
syntax:max "if " "(" imp_bexp ")" ppHardSpace "then" ppLine
  "{{" term "}}" ppLine dcom ppDedent(ppLine "else") ppLine
  "{{" term "}}" ppLine dcom ppDedent(ppLine "end") ppLine
  "{{" term "}}" : dcom
syntax:max "while " "(" imp_bexp ")" ppHardSpace "do" ppLine
  "{{" term "}}" ppLine dcom ppDedent(ppLine "end") ppLine
  "{{" term "}}" : dcom
syntax:5 "->>" " {{" term "}}" ppLine dcom:0 : dcom
syntax:5 dcom:6 ppLine "->>" " {{" term "}}" : dcom

syntax:min "dcom" ppHardSpace "{" ppLine dcom
  ppDedent(ppLine "}") : term

macro_rules
  | `(dcom { $s }) => do
    let stx ← match s with
      | `(dcom| ($body:dcom)) => `(dcom { $body })
      | `(dcom| skip {{ $q }}) => `(DCom.skip ({{ $q }}))
      | `(dcom| $x:ident := $a:imp_aexp {{ $q }}) =>
        `(DCom.asgn $x (aexp { $a }) ({{ $q }}))
      | `(dcom| $d1:dcom; $d2:dcom) =>
        `(DCom.seq (dcom { $d1 }) (dcom { $d2 }))
      | `(dcom|
          if ($b:imp_bexp) then
            {{ $p1 }}
            $d1:dcom
          else
            {{ $p2 }}
            $d2:dcom
          end
            {{ $q }}) =>
        `(DCom.cond (bexp { $b })
          ({{ $p1 }}) (dcom { $d1 })
          ({{ $p2 }}) (dcom { $d2 })
          ({{ $q }}))
      | `(dcom|
          while ($b:imp_bexp) do
            {{ $p }}
            $body:dcom
          end
            {{ $q }}) =>
        `(DCom.whileDo (bexp { $b }) ({{ $p }})
          (dcom { $body }) ({{ $q }}))
      | `(dcom| ->> {{ $p }} $body:dcom) =>
        `(DCom.pre ({{ $p }}) (dcom { $body }))
      | `(dcom| $body:dcom ->> {{ $q }}) =>
        `(DCom.post (dcom { $body }) ({{ $q }}))
      | _ => Lean.Macro.throwUnsupported
    return Imp.Elab.withSourceInfoOf s stx

namespace DCom.Delab

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer Imp.Elab Imp.Delab

@[category_parenthesizer «dcom»]
def dcom.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `dcom false wrapParens prec <|
    parenthesizeCategoryCore `dcom prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let stxInfo := SourceInfo.fromRef stx
    let stx := stx.setInfo .none
    let pstx ← `(dcom| ($(⟨stx⟩)))
    return pstx.raw.setInfo stxInfo

def getAssnBody (stx : Term) : Term :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `({{ $P }}) => return P
    | _ => return stx

private def getDCom? (stx : Term) : Option (TSyntax `dcom) :=
  match stx with
  | `(dcom { $d:dcom }) => some <| withSourceInfoOf (canonical := false) stx d
  | _ => none

@[app_unexpander DCom.skip]
def unexpandSkip : Unexpander
  | `($_ $q) => `(dcom { skip {{ $(getAssnBody q) }} })
  | _ => throw ()

@[app_unexpander DCom.asgn]
def unexpandAsgn : Unexpander
  | `($_ $x:ident $a $q) =>
      `(dcom { $x:ident := $(getAexp a) {{ $(getAssnBody q) }} })
  | _ => throw ()

@[app_unexpander DCom.seq]
def unexpandSeq : Unexpander
  | `($_ $first $second) => do
      let some first := getDCom? first | throw ()
      let some second := getDCom? second | throw ()
      `(dcom { $first; $second })
  | _ => throw ()

@[app_unexpander DCom.cond]
def unexpandCond : Unexpander
  | `($_ $b $thenPre $thenBranch $elsePre $elseBranch $post) => do
      let some thenBranch := getDCom? thenBranch | throw ()
      let some elseBranch := getDCom? elseBranch | throw ()
      `(dcom {
        if ($(getBexp b)) then
          {{ $(getAssnBody thenPre) }}
          $thenBranch
        else
          {{ $(getAssnBody elsePre) }}
          $elseBranch
        end
          {{ $(getAssnBody post) }}
      })
  | _ => throw ()

@[app_unexpander DCom.whileDo]
def unexpandWhileDo : Unexpander
  | `($_ $b $bodyPre $body $post) => do
      let some body := getDCom? body | throw ()
      `(dcom {
        while ($(getBexp b)) do
          {{ $(getAssnBody bodyPre) }}
          $body
        end
          {{ $(getAssnBody post) }}
      })
  | _ => throw ()

@[app_unexpander DCom.pre]
def unexpandPre : Unexpander
  | `($_ $pre $body) => do
      let some body := getDCom? body | throw ()
      `(dcom { ->> {{ $(getAssnBody pre) }} $body })
  | _ => throw ()

@[app_unexpander DCom.post]
def unexpandPost : Unexpander
  | `($_ $body $post) => do
      let some body := getDCom? body | throw ()
      `(dcom { $body ->> {{ $(getAssnBody post) }} })
  | _ => throw ()

end DCom.Delab
--  END DETAILS

--  To provide the initial precondition that goes at the very top of a
--  decorated program, we introduce a new type `decorated`:

structure Decorated where
  pre : Assertion
  body : DCom

example : DCom :=
  .skip ({{ True }})

example : DCom :=
  .whileDo (bexp {true}) ({{ True }})
    (.skip ({{ True }})) ({{ True }})

--  To inspect the fully elaborated term behind this notation, put
--  `set_option pp.all true in` before a `#check` or `#print` command.
--
--  The formal definitions can use either constructors directly or the
--  decorated-command notation introduced above.
--
--  An example `decorated` program that decrements `X` to `0`:

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

--  It is easy to go from a `dcom` to a `com` by erasing all annotations.

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

example :
    decWhile.erase =
      (imp {
        while (X ≠ 0) {
          X := X - 1
        }
      }) := by
  rfl

--  It is also straightforward to extract the precondition and
--  postcondition from a decorated program.

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

example : decWhile.precondition = {{ True }} := by
  funext st
  rfl

example : decWhile.postcondition = {{ X = 0 }} := by
  funext st
  rfl

--  We can then express what it means for a decorated program to be correct
--  as follows:

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

--  The outer Hoare triple of a decorated program is just a `Prop`; thus,
--  to show that it is *valid*, we need to produce a proof of this
--  proposition.
--
--  We will do this by extracting "proof obligations" from the decorations
--  sprinkled throughout the program.
--
--  These obligations are often called *verification conditions*, because
--  they are the facts that must be verified to see that the decorations
--  are locally consistent and thus constitute a proof of validity of the
--  outer triple.

--  ### Extracting Verification Conditions

--  The function `DCom.VerificationConditions` takes a decorated command
--  `d` together with a precondition `P` and returns a *proposition* that,
--  if it can be proved, implies that the triple
--
--      {{P}} d.erase {{d.postcondition}}
--
--  is valid.
--
--  It does this by walking over `d` and generating a big conjunction that
--  includes
--
--  - local consistency checks for each form of command, plus
--
--  - uses of `->>` to bridge the gap between the assertions found inside a
--    decorated command and the assertions imposed by the external
--    precondition; these uses correspond to applications of the
--    consequence rule.
--
--  *Local consistency* is defined as follows...
--
--  - The decorated command
--
--      skip {{Q}}
--
--  is locally consistent with respect to a precondition `P` if `P ->> Q`.
--
--  - The sequential composition of `d1` and `d2` is locally consistent
--    with respect to `P` if `d1` is locally consistent with respect to `P`
--    and `d2` is locally consistent with respect to the postcondition of
--    `d1`.
--
--  - An assignment
--
--      X := a {{Q}}
--
--  is locally consistent with respect to a precondition `P` if:
--
--      P ->> Q [X |-> a]
--
--  - A conditional
--
--      if b then {{P1}} d1 else {{P2}} d2 end {{Q}}
--
--  is locally consistent with respect to precondition `P` if
--
--  (1) `P /\ b ->> P1`
--
--  (2) `P /\ b ->> P2`
--
--  (3) `d1` is locally consistent with respect to `P1`
--
--  (4) `d2` is locally consistent with respect to `P2`
--
--  (5) `d1.postcondition ->> Q`
--
--  (6) `d2.postcondition ->> Q`
--
--  - A loop
--
--      while b do {{Q}} d end {{R}}
--
--  is locally consistent with respect to precondition `P` if:
--
--  (1) `P ->> d.postcondition`
--
--  (2) `d.postcondition /\ b ->> Q`
--
--  (3) `d.postcondition /\ b ->> R`
--
--  (4) `d` is locally consistent with respect to `Q`
--
--  - A command with an extra assertion at the beginning
--
--      ->> {{Q}} d
--
--  is locally consistent with respect to a precondition `P` if:
--
--  (1) `P ->> Q`
--
--  (2) `d` is locally consistent with respect to `Q`
--
--  - A command with an extra assertion at the end
--
--      d ->> {{Q}}
--
--  is locally consistent with respect to a precondition `P` if:
--
--  (1) `d` is locally consistent with respect to `P`
--
--  (2) `d.postcondition ->> Q`
--
--  With all this in mind, we can write a *verification condition
--  generator* that takes a decorated command and reads off a proposition
--  saying that all its decorations are locally consistent.
--
--  Formally, since a decorated command is "waiting for its precondition"
--  the main VC generator takes a `dcom` plus a given precondition as
--  arguments.

def DCom.VerificationConditions
    (P : Assertion) (d : DCom) : Prop :=
  match d with
  | .skip Q =>
      P ->> Q
  | .seq d1 d2 =>
      d1.VerificationConditions P ∧
      d2.VerificationConditions d1.postcondition
  | .asgn x a Q =>
      P ->> {{ Q [x ↦ a] }}
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

--  The following key theorem states that `DCom.VerificationConditions`
--  does its job correctly. Not surprisingly, each of the Hoare Logic rules
--  plays a critical role at some point in the proof.

theorem verification_correct (d : DCom) (P : Assertion)
    (hvc : d.VerificationConditions P) :
    ValidHoareTriple P d.erase d.postcondition := by
  sorry

--  Now that all the pieces are in place, we can define what it means to
--  verify an entire program.

def Decorated.VerificationConditions
    (dec : Decorated) : Prop :=
  dec.body.VerificationConditions dec.pre

--  And this brings us to the main theorem of this section:

theorem verification_conditions_correct (dec : Decorated)
    (hvc : dec.VerificationConditions) :
    dec.OuterTripleValid := by
  exact verification_correct dec.body dec.pre hvc

--  ### More Automation

--  The propositions generated by `DCom.VerificationConditions` are fairly
--  big and contain many conjuncts that are essentially trivial.

example : decWhile.VerificationConditions := by
  unfold Decorated.VerificationConditions decWhile
  simp only [DCom.VerificationConditions,
    DCom.postcondition]
  sorry

--  Fortunately, our `verify_assertion` tactic can generally take care of
--  most (or sometimes all) of them.

example : decWhile.VerificationConditions := by
  sorry

--  To automate the overall process of verification, we can use
--  `verification_correct` to extract the verification conditions, use
--  `verify_assertion` to verify them as much as it can, and finally tidy
--  up any remaining bits by hand.

macro "verify" : tactic =>
  `(tactic|
    (apply verification_conditions_correct;
     verify_assertion))

--  Here's the final, formal proof that `decWhile` is correct.

theorem dec_while_correct :
    decWhile.OuterTripleValid := by
  sorry

--  Similarly, here is the formal decorated program for the "swapping by
--  adding and subtracting" example that we saw earlier.

def swapDec (m n : Nat) : Decorated where
  pre := ({{ X = m ∧ Y = n }})
  body := dcom {
    ->> {{ (X + Y) - ((X + Y) - Y) = n ∧ (X + Y) - Y = m }}
    X := X + Y {{ X - (X - Y) = n ∧ X - Y = m }};
    Y := X - Y {{ X - Y = n ∧ Y = m }};
    X := X - Y {{ X = n ∧ Y = m }}
  }

theorem swap_correct (m n : Nat) :
    (swapDec m n).OuterTripleValid := by
  sorry

--  And here is the formal decorated version of the "positive difference"
--  program from earlier:

def positiveDifferenceDec : Decorated where
  pre := ({{ True }})
  body := dcom {
    if (X ≤ Y) then
      {{ True ∧ X ≤ Y }}
      ->> {{ (Y - X) + X = Y ∨ (Y - X) + Y = X }}
      Z := Y - X {{ Z + X = Y ∨ Z + Y = X }}
    else
      {{ True ∧ ¬ X ≤ Y }}
      ->> {{ (X - Y) + X = Y ∨ (X - Y) + Y = X }}
      Z := X - Y {{ Z + X = Y ∨ Z + Y = X }}
    end
      {{ Z + X = Y ∨ Z + Y = X }}
  }

theorem positive_difference_correct :
    positiveDifferenceDec.OuterTripleValid := by
  sorry

--  ### Exercise (2 stars): if_minus_plus_correct ⭐⭐

--  Here is a skeleton of the formal decorated version of the
--  `if_minus_plus` program that we saw earlier. Replace all occurrences of
--  `FILL_IN_HERE` with appropriate assertions and fill in the proof (which
--  should be just as straightforward as in the examples above).

def ifMinusPlusDec : Decorated where
  pre := ({{ True }})
  body := dcom {
    if (X ≤ Y) then
      {{ True ∧ X ≤ Y }}
      ->> {{ Y = X + (Y - X) }}
      Z := Y - X {{ Y = X + Z }}
    else
      {{ True ∧ ¬ X ≤ Y }}
      ->> {{ X + Z = X + Z }}
      Y := X + Z {{ Y = X + Z }}
    end
      {{ Y = X + Z }}
  }

theorem if_minus_plus_correct :
    ifMinusPlusDec.OuterTripleValid := by
  sorry

--  ### Exercise (2 stars): div_mod_outer_triple_valid (Optional) ⭐⭐

--  Fill in appropriate assertions for the division program from above.

def divModDec (a b : Nat) : Decorated where
  pre := ({{ True }})
  body := dcom {
    ->> {{ b * 0 + a = a }}
    X := ~(Aexp.num a) {{ b * 0 + X = a }};
    Y := 0 {{ b * Y + X = a }};
    while (~(Aexp.num b) ≤ X) do
      {{ b * Y + X = a ∧ b ≤ X }}
      ->> {{ b * (Y + 1) + (X - b) = a }}
      X := X - ~(Aexp.num b) {{ b * (Y + 1) + X = a }};
      Y := Y + 1 {{ b * Y + X = a }}
    end
      {{ b * Y + X = a ∧ ¬ b ≤ X }}
    ->> {{ b * Y + X = a ∧ X < b }}
  }

theorem div_mod_outer_triple_valid (a b : Nat) :
    (divModDec a b).OuterTripleValid := by
  sorry

--  ## Finding Loop Invariants

--  Once the outermost precondition and postcondition are chosen, the only
--  creative part of a verifying program using Hoare Logic is finding the
--  right loop invariants. The reason this is difficult is the same as the
--  reason that inductive mathematical proofs are:
--
--  - Strengthening a *loop invariant* means that you have a stronger
--    assumption to work with when trying to establish the postcondition of
--    the loop body, but it also means that the loop body's postcondition
--    is harder to prove.
--
--  - Similarly, strengthening an *induction hypothesis* means that you
--    have a stronger assumption to work with when trying to complete the
--    induction step of the proof, but it also means that the statement
--    being proved inductively is harder to prove.
--
--  This section explains how to approach the challenge of finding loop
--  invariants through a series of examples and exercises.

--  ### Example: Slow Subtraction

--  The following program subtracts the value of `X` from the value of `Y`
--  by repeatedly decrementing both `X` and `Y`. We want to verify its
--  correctness with respect to the pre- and postconditions shown:
--
--      {{ X = m /\ Y = n }}
--        while X <> 0 do
--          Y := Y - 1;
--          X := X - 1
--        end
--      {{ Y = n - m }}
--
--  To verify this program, we need to find an invariant `Inv` for the
--  loop. As a first step we can leave `Inv` as an unknown and build a
--  *skeleton* for the proof by applying the rules for local consistency,
--  working from the end of the program to the beginning, as usual, and
--  without doing any thinking at all yet.
--
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
--
--  Examining this skeleton, we can see that any valid `Inv` will have to
--  respect three conditions:
--
--  - (a) it must be *weak* enough to be implied by the loop's
--    precondition, i.e., (1) must imply (2);
--
--  - (b) it must be *strong* enough to imply the program's postcondition,
--    i.e., (7) must imply (8);
--
--  - (c) it must be *preserved* by a single iteration of the loop,
--    assuming that the loop guard also evaluates to true, i.e., (3) must
--    imply (4).

--  These conditions are actually independent of the particular program and
--  specification we are considering: every loop invariant has to satisfy
--  them.
--
--  One way to find a loop invariant that simultaneously satisfies these
--  three conditions is by using an iterative process: start with a
--  "candidate" invariant (e.g., a guess or a heuristic choice) and check
--  the three conditions above; if any of the checks fails, try to use the
--  information that we get from the failure to produce another — hopefully
--  better — candidate invariant, and repeat.
--
--  For instance, in the reduce-to-zero example above, we saw that, for a
--  very simple loop, choosing `True` as a loop invariant did the job.
--  Maybe it will work here too. To find out, let's try instantiating `Inv`
--  with `True` in the skeleton above and see what we get...
--
--      (1)    {{ X = m /\ Y = n }} ->>                    (a - OK)
--      (2)    {{ True }}
--               while X <> 0 do
--      (3)                   {{ True /\ X <> 0 }} ->>     (c - OK)
--      (4)                   {{ True }}
--                 Y := Y - 1;
--      (5)                   {{ True }}
--                 X := X - 1
--      (6)                   {{ True }}
--               end
--      (7)    {{ True /\ ~(X <> 0) }} ->>                 (b - WRONG!)
--      (8)    {{ Y = n - m }}
--
--  While conditions (a) and (c) are trivially satisfied, (b) is wrong: it
--  is not the case that `True /\ X = 0` (7) implies `Y = n - m` (8). In
--  fact, the two assertions are completely unrelated, so it is very easy
--  to find a counterexample to the implication (say, `Y = X = m = 0` and
--  `n = 1`).
--
--  If we want (b) to hold, we need to strengthen the loop invariant so
--  that it implies the postcondition (8). One simple way to do this is to
--  let the loop invariant *be* the postcondition. So let's return to our
--  skeleton, instantiate `Inv` with `Y = n - m`, and try checking
--  conditions (a) to (c) again.
--
--      (1)    {{ X = m /\ Y = n }} ->>                        (a - WRONG!)
--      (2)    {{ Y = n - m }}
--               while X <> 0 do
--      (3)                     {{ Y = n - m /\ X <> 0 }} ->>  (c - WRONG!)
--      (4)                     {{ Y - 1 = n - m }}
--                 Y := Y - 1;
--      (5)                     {{ Y = n - m }}
--                 X := X - 1
--      (6)                     {{ Y = n - m }}
--               end
--      (7)    {{ Y = n - m /\ ~(X <> 0) }} ->>                (b - OK)
--      (8)    {{ Y = n - m }}
--
--  This time, condition (b) holds trivially, but (a) and (c) are broken.
--  Condition (a) requires that (1) `X = m /\ Y = n` implies (2)
--  `Y = n - m`. If we substitute `Y` by `n` we have to show that
--  `n = n - m` for arbitrary `m` and `n`, which is not the case (for
--  instance, when `m = n = 1`). Condition (c) requires that
--  `n - m - 1 = n - m`, which fails, for instance, for `n = 1` and
--  `m = 0`. So, although `Y = n - m` holds at the end of the loop, it does
--  not hold from the start, and it doesn't hold on each iteration; it is
--  not a correct loop invariant.
--
--  This failure is not very surprising: the variable `Y` changes during
--  the loop, while `m` and `n` are constant, so the assertion we chose
--  didn't have much chance of being a loop invariant!
--
--  To do better, we need to generalize (7) to some statement that is
--  equivalent to (8) when `X` is `0`, since this will be the case when the
--  loop terminates, and that "fills the gap" in some appropriate way when
--  `X` is nonzero. Looking at how the loop works, we can observe that `X`
--  and `Y` are decremented together until `X` reaches `0`. So, if `X = 2`
--  and `Y = 5` initially, after one iteration of the loop we obtain
--  `X = 1` and `Y = 4`; after two iterations `X = 0` and `Y = 3`; and then
--  the loop stops. Notice that the difference between `Y` and `X` stays
--  constant between iterations: initially, `Y = n` and `X = m`, and the
--  difference is always `n - m`. So let's try instantiating `Inv` in the
--  skeleton above with `Y - X = n - m`.
--
--      (1)    {{ X = m /\ Y = n }} ->>                            (a - OK)
--      (2)    {{ Y - X = n - m }}
--               while X <> 0 do
--      (3)                    {{ Y - X = n - m /\ X <> 0 }} ->>   (c - OK)
--      (4)                    {{ (Y - 1) - (X - 1) = n - m }}
--                 Y := Y - 1;
--      (5)                    {{ Y - (X - 1) = n - m }}
--                 X := X - 1
--      (6)                    {{ Y - X = n - m }}
--               end
--      (7)    {{ Y - X = n - m /\ ~(X <> 0) }} ->>                (b - OK)
--      (8)    {{ Y = n - m }}
--
--  Success! Conditions (a), (b) and (c) all hold now. (To verify (c), we
--  need to check that, under the assumption that `X <> 0`, we have
--  `Y - X = (Y - 1) - (X - 1)`; this holds for all natural numbers `X` and
--  `Y`.)
--
--  Here is the final version of the decorated program:

def subtractSlowlyDec (m n : Nat) : Decorated where
  pre := ({{ X = m ∧ Y = n }})
  body := dcom {
    ->> {{ Y - X = n - m }}
    while (X ≠ 0) do
      {{ Y - X = n - m ∧ ¬ X = 0 }}
      ->> {{ (Y - 1) - (X - 1) = n - m }}
      Y := Y - 1 {{ Y - (X - 1) = n - m }};
      X := X - 1 {{ Y - X = n - m }}
    end
      {{ Y - X = n - m ∧ X = 0 }}
    ->> {{ Y = n - m }}
  }

theorem subtract_slowly_outer_triple_valid (m n : Nat) :
    (subtractSlowlyDec m n).OuterTripleValid := by
  sorry

--  ### Exercise: Slow Assignment

--  ### Exercise (2 stars): slow_assignment ⭐⭐

--  A roundabout way of assigning a number currently stored in `X` to the
--  variable `Y` is to start `Y` at `0`, then decrement `X` until it hits
--  `0`, incrementing `Y` at each step. Here is a program that implements
--  this idea. Fill in decorations and prove the decorated program correct.
--  (The proof should be very simple.)

def slowAssignmentDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body := dcom {
    Y := 0 {{ sorry }};
    (->> {{ sorry }}
      while (X ≠ 0) do
        {{ sorry }}
        ->> {{ sorry }}
        X := X - 1 {{ sorry }};
        (->> {{ sorry }}
          Y := Y + 1 {{ sorry }})
      end
        {{ sorry }}
      ->> {{ Y = m }})
  }

theorem slow_assignment (m : Nat) :
    (slowAssignmentDec m).OuterTripleValid := by
  sorry

--  ### Example: Parity

--  Here is a cute way of computing the parity of a value initially stored
--  in `X`, due to Daniel Cristofani.
--
--      {{ X = m }}
--        while 2 <= X do
--          X := X - 2
--        end
--      {{ X = parity m }}
--
--  The `parity` function used in the specification is defined in Lean as
--  follows:

def parity : Nat → Nat
  | 0 => 0
  | 1 => 1
  | Nat.succ (Nat.succ n) => parity n

--  The postcondition does not hold at the beginning of the loop, since
--  `m = parity m` does not hold for an arbitrary `m`, so we cannot hope to
--  use that as a loop invariant. To find a loop invariant that works,
--  let's think a bit about what this loop does. On each iteration it
--  decrements `X` by `2`, which preserves the parity of `X`. So the parity
--  of `X` does not change, i.e., it is invariant. The initial value of `X`
--  is `m`, so the parity of `X` is always equal to the parity of `m`.
--  Using `parity X = parity m` as an invariant we obtain the following
--  decorated program:
--
--      {{ X = m }} ->>                                         (a - OK)
--      {{ parity X = parity m }}
--        while 2 <= X do
--                     {{ parity X = parity m /\ 2 <= X }} ->>  (c - OK)
--                     {{ parity (X-2) = parity m }}
--          X := X - 2
--                     {{ parity X = parity m }}
--        end
--      {{ parity X = parity m /\ ~(2 <= X) }} ->>              (b - OK)
--      {{ X = parity m }}
--
--  With this loop invariant, conditions (a), (b), and (c) are all
--  satisfied. For verifying (b), we observe that, when `X < 2`, we have
--  `parity X = X` (we can easily see this in the definition of `parity`).
--  For verifying (c), we observe that, when `2 <= X`, we have
--  `parity X = parity (X-2)`.

--  ### Exercise (3 stars): parity (Optional) ⭐⭐⭐

--  Translate the above informal decorated program into a formal one and
--  prove it correct.
--
--  Hint: There are actually several possible loop invariants that all lead
--  to good proofs; one that leads to a particularly simple proof is
--  `parity X = parity m`. Ordinary Lean functions can be applied directly
--  to Imp variables inside assertions, so this can be written as
--  `{{ parity X = parity m }}`.

def parityDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body :=
    let inv : Assertion :=
      sorry
    let guardedInv : Assertion :=
      sorry
    let bodyPre : Assertion :=
      sorry
    let exit : Assertion :=
      sorry
    let post : Assertion :=
      fun st => st[X] = parity m
    dcom {
    ->> {{ inv }}
    while (2 ≤ X) do
      {{ guardedInv }}
      ->> {{ bodyPre }}
      X := X - 2 {{ inv }}
    end
      {{ exit }}
    ->> {{ post }}
  }

--  If you use the suggested loop invariant, you may find the following two
--  lemmas helpful.

theorem parity_ge_2 (x : Nat) (h : 2 ≤ x) :
    parity (x - 2) = parity x := by
  sorry

theorem parity_lt_2 (x : Nat) (h : ¬ 2 ≤ x) :
    parity x = x := by
  sorry

theorem parity_outer_triple_valid (m : Nat) :
    (parityDec m).OuterTripleValid := by
  sorry

--  FILL IN HERE

--  ### Example: Finding Square Roots

--  The following program computes the integer square root of `X` by naive
--  iteration:
--
--      {{ X=m }}
--        Z := 0;
--        while (Z+1)*(Z+1) <= X do
--          Z := Z+1
--        end
--      {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
--
--  WORK IN CLASS
--
--  As we did before, we can try to use the postcondition as a candidate
--  loop invariant, obtaining the following decorated program:
--
--      (1)  {{ X=m }} ->>                  (a - second conjunct of (2) WRONG!)
--      (2)  {{ 0*0 <= m /\ m<(0+1)*(0+1) }}
--              Z := 0
--      (3)            {{ Z*Z <= m /\ m<(Z+1)*(Z+1) }};
--              while (Z+1)*(Z+1) <= X do
--      (4)            {{ Z*Z<=m /\ m<(Z+1)*(Z+1)
--                               /\ (Z+1)*(Z+1)<=X }} ->>          (c - WRONG!)
--      (5)            {{ (Z+1)*(Z+1)<=m /\ m<((Z+1)+1)*((Z+1)+1) }}
--                Z := Z+1
--      (6)            {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
--              end
--      (7)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) /\ ~((Z+1)*(Z+1)<=X) }} ->>    (b - OK)
--      (8)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
--
--  This didn't work very well: conditions (a) and (c) both failed. Looking
--  at condition (c), we see that the second conjunct of (4) is almost the
--  same as the first conjunct of (5), except that (4) mentions `X` while
--  (5) mentions `m`. But note that `X` is never assigned in this program,
--  so we should always have `X=m`. We didn't propagate this information
--  from (1) into the loop invariant, but we could!
--
--  Also, we don't need the second conjunct of (8), since we can obtain it
--  from the negation of the guard — the third conjunct in (7) — again
--  under the assumption that `X=m`. This allows us to simplify a bit.
--
--  So we now try `X=m /\ Z*Z <= m` as the loop invariant:
--
--      {{ X=m }} ->>                                           (a - OK)
--      {{ X=m /\ 0*0 <= m }}
--        Z := 0
--                   {{ X=m /\ Z*Z <= m }};
--        while (Z+1)*(Z+1) <= X do
--                   {{ X=m /\ Z*Z<=m /\ (Z+1)*(Z+1)<=X }} ->>  (c - OK)
--                   {{ X=m /\ (Z+1)*(Z+1)<=m }}
--          Z := Z + 1
--                   {{ X=m /\ Z*Z<=m }}
--        end
--      {{ X=m /\ Z*Z<=m /\ ~((Z+1)*(Z+1)<=X) }} ->>            (b - OK)
--      {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
--
--  This works, since conditions (a), (b), and (c) are now all rather
--  trivially satisfied.
--
--  Very often, when a variable is used in a loop in a read-only fashion
--  (i.e., it is referred to by the program or by the specification, and it
--  is not changed by the loop), it is necessary to record the *fact* that
--  it doesn't change in the loop invariant.

--  ### Exercise (3 stars): sqrt (Optional) ⭐⭐⭐

--  Translate the above informal decorated program into a formal one and
--  prove it correct.
--
--  Hint: The loop invariant here must ensure that `Z*Z` is consistently
--  less than or equal to X.

def sqrtDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body := dcom {
    ->> {{ sorry }}
    Z := 0 {{ sorry }};
    while ((Z + 1) * (Z + 1) ≤ X) do
      {{ sorry }}
      ->> {{ sorry }}
      Z := Z + 1 {{ sorry }}
    end
      {{ sorry }}
    ->> {{ Z * Z ≤ m ∧ m < (Z + 1) * (Z + 1) }}
  }

theorem sqrt_correct (m : Nat) :
    (sqrtDec m).OuterTripleValid := by
  sorry

--  ### Example: Squaring

--  Here is a program that squares `X` by repeated addition:
--
--      {{ X = m }}
--        Y := 0;
--        Z := 0;
--        while Y <> X  do
--          Z := Z + X;
--          Y := Y + 1
--        end
--      {{ Z = m*m }}
--
--  WORK IN CLASS
--
--  The first thing to note is that the loop reads `X` but doesn't change
--  its value. As we saw in the previous example, it can be a good idea in
--  such cases to add `X = m` to the loop invariant. The other thing that
--  we know is often useful in the loop invariant is the postcondition, so
--  let's add that too, leading to the candidate loop invariant
--  `Z = m * m /\ X = m`.
--
--      {{ X = m }} ->>                                       (a - WRONG)
--      {{ 0 = m*m /\ X = m }}
--        Y := 0
--                     {{ 0 = m*m /\ X = m }};
--        Z := 0
--                     {{ Z = m*m /\ X = m }};
--        while Y <> X do
--                     {{ Z = m*m /\ X = m /\ Y <> X }} ->>   (c - WRONG)
--                     {{ Z+X = m*m /\ X = m }}
--          Z := Z + X
--                     {{ Z = m*m /\ X = m }};
--          Y := Y + 1
--                     {{ Z = m*m /\ X = m }}
--        end
--      {{ Z = m*m /\ X = m /\ ~(Y <> X) }} ->>               (b - OK)
--      {{ Z = m*m }}
--
--  Conditions (a) and (c) fail because of the `Z = m*m` part. While `Z`
--  starts at `0` and works itself up to `m*m`, we can't expect `Z` to be
--  `m*m` from the start. If we look at how `Z` progresses in the loop,
--  after the 1st iteration `Z = m`, after the 2nd iteration `Z = 2*m`, and
--  at the end `Z = m*m`. Since the variable `Y` tracks how many times we
--  go through the loop, this leads us to derive a new loop invariant
--  candidate: `Z = Y*m /\ X = m`.
--
--      {{ X = m }} ->>                                        (a - OK)
--      {{ 0 = 0*m /\ X = m }}
--        Y := 0
--                      {{ 0 = Y*m /\ X = m }};
--        Z := 0
--                      {{ Z = Y*m /\ X = m }};
--        while Y <> X do
--                      {{ Z = Y*m /\ X = m /\ Y <> X }} ->>   (c - OK)
--                      {{ Z+X = (Y+1)*m /\ X = m }}
--          Z := Z + X
--                      {{ Z = (Y+1)*m /\ X = m }};
--          Y := Y + 1
--                      {{ Z = Y*m /\ X = m }}
--        end
--      {{ Z = Y*m /\ X = m /\ ~(Y <> X) }} ->>                (b - OK)
--      {{ Z = m*m }}
--
--  This new loop invariant makes the proof go through: all three
--  conditions are easy to check.
--
--  It is worth comparing the postcondition `Z = m*m` and the `Z = Y*m`
--  conjunct of the loop invariant. It is often the case that one has to
--  replace parameters with variables — or with expressions involving both
--  variables and parameters, like `m - Y` — when going from postconditions
--  to loop invariants.

--  ### Exercise: Factorial

--  ### Exercise (4 stars): factorial_correct (Advanced) ⭐⭐⭐⭐

--  Recall that `n!` denotes the factorial of `n` (i.e., `n! =
--  1*2*...*n`).
--  We can define the factorial function recursively in Lean as follows:

def fact : Nat → Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * fact n

#eval fact 5

--  First, write the Imp program `factorial` that calculates the factorial
--  of the number initially stored in the variable `X` and puts it in the
--  variable `Y`.
--
--  Using your definition `factorial` and `slowAssignmentDec` as a guide,
--  write a formal decorated program `factorialDec` that implements the
--  factorial function. Ordinary Lean functions such as `fact` can be
--  applied directly to Imp variables inside assertions.
--
--  Fill in the blanks and finish the proof of correctness. Bear in mind
--  that we are working with natural numbers, for which both division and
--  subtraction can behave differently than with real numbers. Excluding
--  both operations from your loop invariant is advisable!
--
--  Then state a theorem named `factorial_correct` that says `factorialDec`
--  is correct, and prove the theorem. If all goes well, `verify` will
--  leave you with just two subgoals, each of which requires establishing
--  some mathematical property of `fact`, rather than proving anything
--  about your program.
--
--  Hint: if those two subgoals become tedious to prove, give some thought
--  to how you could restate your assertions such that the mathematical
--  operations are more amenable to manipulation in Lean. For example,
--  recall that `1 + ...` is easier to work with than `... + 1`.

def factorialDec (m : Nat) : Decorated := sorry

theorem fact_sub_one (m : Nat) (h : m ≠ 0) :
    m * fact (m - 1) = fact m := by
  sorry

theorem factorial_correct (m : Nat) :
    (factorialDec m).OuterTripleValid := by
  sorry

--  ### Exercise: Minimum

--  ### Exercise (3 stars): minimum_correct (Advanced) ⭐⭐⭐

--  Fill in decorations for the following program and prove them correct.
--  As with `factorial`, be careful about mathematical reasoning involving
--  natural numbers, especially subtraction.
--
--  Lean functions can be applied directly inside assertions. For example,
--  the minimum of `a` and `b` can be written `Nat.min a b`.

def minimumDec (a b : Nat) : Decorated where
  pre := ({{ True }})
  body := dcom {
    ->> {{ sorry }}
    X := ~(Aexp.num a) {{
      sorry
    }};
    Y := ~(Aexp.num b) {{
      sorry
    }};
    Z := 0 {{
      sorry
    }};
    while (X ≠ 0 ∧ Y ≠ 0) do
      {{ sorry }}
      ->> {{ sorry }}
      X := X - 1 {{
        sorry
      }};
      Y := Y - 1 {{
        sorry
      }};
      Z := Z + 1 {{
        sorry
      }}
    end
      {{ sorry }}
    ->> {{ Z = Nat.min a b }}
  }

theorem minimum_correct (a b : Nat) :
    (minimumDec a b).OuterTripleValid := by
  sorry

--  ### Exercise: Two Loops

--  ### Exercise (3 stars): two_loops ⭐⭐⭐

--  Here is a pretty inefficient way of adding 3 numbers:
--
--      X := 0;
--      Y := 0;
--      Z := c;
--      while X <> a do
--        X := X + 1;
--        Z := Z + 1
--      end;
--      while Y <> b do
--        Y := Y + 1;
--        Z := Z + 1
--      end
--
--  Show that it does what it should by completing the following decorated
--  program.

def twoLoopsDec (a b c : Nat) : Decorated where
  pre := ({{ True }})
  body := dcom {
    ->> {{ sorry }}
    X := 0 {{ sorry }};
    Y := 0 {{ sorry }};
    Z := ~(Aexp.num c) {{
      sorry
    }};
    (while (X ≠ ~(Aexp.num a)) do
      {{ sorry }}
      ->> {{ sorry }}
      X := X + 1 {{
        sorry
      }};
      Z := Z + 1 {{ sorry }}
    end
      {{ sorry }}
    ->> {{ sorry }});
    while (Y ≠ ~(Aexp.num b)) do
      {{ sorry }}
      ->> {{ sorry }}
      Y := Y + 1 {{ sorry }};
      Z := Z + 1 {{ sorry }}
    end
      {{ sorry }}
    ->> {{ Z = a + b + c }}
  }

theorem two_loops (a b c : Nat) :
    (twoLoopsDec a b c).OuterTripleValid := by
  sorry

--  ### Exercise: Power Series

--  ### Exercise (4 stars): dpow2 (Optional) ⭐⭐⭐⭐

--  Here is a program that computes the series:
--  `1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1`
--
--      X := 0;
--      Y := 1;
--      Z := 1;
--      while X <> m do
--        Z := 2 * Z;
--        Y := Y + Z;
--        X := X + 1
--      end
--
--  Turn this into a decorated program and prove it correct.

def pow2 : Nat → Nat
  | 0 => 1
  | Nat.succ n => 2 * pow2 n

def dpow2Dec (n : Nat) : Decorated where
  pre := ({{ True }})
  body := dcom {
    ->> {{ sorry }}
    X := 0 {{
      sorry
    }};
    Y := 1 {{
      sorry
    }};
    Z := 1 {{
      sorry
    }};
    while (X ≠ ~(Aexp.num n)) do
      {{ sorry }}
      ->> {{ sorry }}
      Z := 2 * Z {{
        sorry
      }};
      Y := Y + Z {{
        sorry
      }};
      X := X + 1 {{
        sorry
      }}
    end
      {{ sorry }}
    ->> {{ Y = pow2 (n + 1) - 1 }}
  }

--  Some lemmas that you may find useful...

theorem pow2_add_one (n : Nat) :
    pow2 (n + 1) = pow2 n + pow2 n := by
  sorry

theorem one_le_pow2 (n : Nat) : 1 ≤ pow2 n := by
  sorry

--  The main correctness theorem:

theorem dpow2_down_correct (n : Nat) :
    (dpow2Dec n).OuterTripleValid := by
  sorry

--  ### Exercise (2 stars): fib_eqn (Advanced, Optional) ⭐⭐

--  The Fibonacci function is characterized by the equations
--
--      fib 0 = 1
--      fib 1 = 1
--      fib (n + 2) = fib (n + 1) + fib n
--
--  This recurrence can be defined structurally in Lean as follows:

def fib : Nat → Nat
  | 0 => 1
  | Nat.succ 0 => 1
  | Nat.succ (Nat.succ n) => fib (Nat.succ n) + fib n

--  Prove that `fib` satisfies the following equation. You will need this
--  as a lemma in the next exercise.

theorem fib_eqn (n : Nat) (h : n > 0) :
    fib n + fib (Nat.pred n) = fib (1 + n) := by
  sorry

--  ### Exercise (4 stars): fib (Advanced, Optional) ⭐⭐⭐⭐

--  The following Imp program leaves the value of `fib n` in the variable
--  `Y` when it terminates:
--
--      X := 1;
--      Y := 1;
--      Z := 1;
--      while X <> 1 + n do
--        T := Z;
--        Z := Z + Y;
--        Y := T;
--        X := 1 + X
--      end
--
--  Fill in the following definition of `dfib` and prove that it satisfies
--  this specification:
--
--      {{ True }} dfib {{ Y = fib n }}
--
--  Ordinary Lean function application can be used in the assertions. If
--  all goes well, your proof will be very brief.

def T : Ident := "T"

def dfib (n : Nat) : Decorated where
  pre := ({{ True }})
  body :=
    let init : Assertion :=
      sorry
    let afterX : Assertion :=
      sorry
    let afterY : Assertion :=
      sorry
    let inv : Assertion :=
      sorry
    let guardedInv : Assertion :=
      sorry
    let bodyPre : Assertion :=
      sorry
    let afterT : Assertion :=
      sorry
    let afterZ : Assertion :=
      sorry
    let afterYBody : Assertion :=
      sorry
    let exit : Assertion :=
      sorry
    dcom {
      ->> {{ init }}
      X := 1 {{ afterX }};
      Y := 1 {{ afterY }};
      Z := 1 {{ inv }};
      while (X ≠ ~(Aexp.num (1 + n))) do
        {{ guardedInv }}
        ->> {{ bodyPre }}
        T := Z {{ afterT }};
        Z := Z + Y {{ afterZ }};
        Y := T {{ afterYBody }};
        X := 1 + X {{ inv }}
      end
        {{ exit }}
      ->> {{ Y = fib n }}
    }

theorem dfib_correct (n : Nat) :
    (dfib n).OuterTripleValid := by
  sorry

--  ### Exercise (5 stars): improve_dcom (Advanced, Optional) ⭐⭐⭐⭐⭐

--  The formal decorated programs defined above are intended to look as
--  similar as possible to the informal ones defined earlier. If we drop
--  this requirement, we can eliminate almost all annotations, just
--  requiring final postconditions and loop invariants to be provided
--  explicitly. Do this — i.e., define a new version of `DCom` with as few
--  annotations as possible and adapt the rest of the formal development
--  leading up to the `verification_correct` theorem.

namespace SparseAnnotations

--  FILL IN HERE

end SparseAnnotations

--  ## Weakest Preconditions (Optional)

--  Some preconditions are more interesting than others. For example, the
--  Hoare triple
--
--      {{ False }}  X := Y + 1  {{ X <= 5 }}
--
--  is *not* very interesting: although it is perfectly valid, it tells us
--  nothing useful. Since the precondition isn't satisfied by any state, it
--  doesn't describe any situations where we can use the command
--  `X := Y + 1` to achieve the postcondition `X <= 5`.
--
--  By contrast,
--
--      {{ Y <= 4 /\ Z = 0 }}  X := Y + 1 {{ X <= 5 }}
--
--  has a useful precondition: it tells us that, if we can somehow create a
--  situation in which we know that `Y <= 4 /\ Z = 0`, then running this
--  command will produce a state satisfying the postcondition. However,
--  this precondition is not as useful as it could be, because the `Z = 0`
--  clause in the precondition actually has nothing to do with the
--  postcondition `X <= 5`.
--
--  The *most* useful precondition for this command is this one:
--
--      {{ Y <= 4 }}  X := Y + 1  {{ X <= 5 }}
--
--  The assertion `Y <= 4` is called the *weakest precondition* of
--  `X := Y + 1` with respect to the postcondition `X <= 5`.

--  Assertion `Y <= 4` is a *weakest precondition* of command `X := Y + 1`
--  with respect to postcondition `X <= 5`. Think of *weakest* here as
--  meaning "easiest to satisfy": a weakest precondition is one that as
--  many states as possible can satisfy.
--
--  `P` is a weakest precondition of command `c` for postcondition `Q` if
--
--  - `P` is a precondition, that is, `{{P}} c {{Q}}`; and
--
--  - `P` is at least as weak as all other preconditions, that is, if
--    `{{P'}} c {{Q}}` then `P' ->> P`.
--
--  Note that weakest preconditions need not be unique. For example,
--  `Y <= 4` was a weakest precondition above, but so are the logically
--  equivalent assertions `Y < 5`, `Y <= 2 * 2`, etc. It is easy to show
--  that any two weakest preconditions `P` and `P'` of a command `c` with
--  respect to postcondition `Q` are logically equivalent; that is,
--  `P <<->> P'`.

def IsWp (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ValidHoareTriple P c Q ∧
  ∀ P' : Assertion, {{ P' }} c {{ Q }} → P' ->> P

--  ### Exercise (1 star): wp (Optional) ⭐

--  What are weakest preconditions of the following commands for the
--  following postconditions?
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

--  ### Exercise (3 stars): is_wp (Advanced, Optional) ⭐⭐⭐

--  Prove formally, using the definition of `ValidHoareTriple`, that
--  `Y <= 4` is indeed a weakest precondition of `X := Y + 1` with respect
--  to postcondition `X <= 5`.

theorem is_wp_example :
    IsWp ({{ Y ≤ 4 }}) (imp {X := Y + 1})
      ({{ X ≤ 5 }}) := by
  sorry

--  ### Exercise (2 stars): hoare_asgn_weakest (Advanced, Optional) ⭐⭐

--  Show that the precondition in the rule `hoare_asgn` is in fact the
--  weakest precondition.

theorem hoare_asgn_weakest
    (Q : Assertion) (x : Ident) (a : Aexp) :
    IsWp ({{ Q [x ↦ a] }}) (imp {x := a}) Q := by
  sorry

--  ### Exercise (2 stars): hoare_havoc_weakest (Advanced, Optional) ⭐⭐

--  Show that your `havoc_pre` function from the `himp_hoare` exercise in
--  the Hoare chapter returns a weakest precondition.

namespace Himp2

theorem hoare_havoc_weakest (P Q : Assertion) (x : Ident)
    (h : Himp.ValidHoareTriple P (Himp.Com.havoc x) Q) :
    P ->> Himp.havoc_pre x Q := by
  sorry

end Himp2

-- Built on 2026-09-03 17:08 UTC

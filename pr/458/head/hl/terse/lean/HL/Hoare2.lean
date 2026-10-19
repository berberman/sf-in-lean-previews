import HL.Hoare

import SFLCompat

--  # Hoare2: Hoare Logic, Part II

open scoped Com MyGetElem Assertion HasTriple HasEval

--  In this chapter, we put Hoare Logic's rules to work,
--  verifying Imp programs via formal *decorated programs*.

--   ----------------------------------------

--  _Quiz:_

--  Write down a Hoare-triple specification for the
--  following program:
--
--      X := 2;
--      Y := X + X

--   ----------------------------------------

--  _Quiz:_

--  Write down a (useful) specification for the following
--  program:
--
--      X := X + 1;
--      Y := X + 1

--   ----------------------------------------

--  _Quiz:_

--  Write down a (useful) specification for the following
--  program:
--
--      if X ≤ Y then
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
--      while X ≠ 0 do
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
--      while X ≠ 0 do
--        Z := Z - 1;
--        X := X - 1
--      end

--  Here is one possible specification for this program, in
--  the form of a Hoare triple:
--
--      {{ True }}
--      X := m;
--      Z := p;
--      while X ≠ 0 do
--        Z := Z - 1;
--        X := X - 1
--      end
--      {{ Z = p - m }}

--  Here is a decorated version of this program, embodying a
--  proof of this specification:
--
--      {{ True }} ↠
--      {{ m = m }}
--        X := m
--                           {{ X = m }} ↠
--                           {{ X = m ∧ p = p }};
--        Z := p;
--                           {{ X = m ∧ Z = p }} ↠
--                           {{ Z - X = p - m }}
--        while X ≠ 0 do
--                           {{ Z - X = p - m ∧ X ≠ 0 }} ↠
--                           {{ (Z - 1) - (X - 1) = p - m }}
--          Z := Z - 1
--                           {{ Z - (X - 1) = p - m }};
--          X := X - 1
--                           {{ Z - X = p - m }}
--        end
--      {{ Z - X = p - m ∧ ¬ (X ≠ 0) }} ↠
--      {{ Z = p - m }}

--  Concretely, a decorated program consists of the
--  program's text interleaved with assertions (sometimes
--  multiple assertions separated by ↠).

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
--
--  WORK IN CLASS

--  ### Example: Simple Conditionals

--  Here's a simple program using conditionals, along with a
--  possible specification:
--
--      {{ True }}
--        if X ≤ Y then
--          Z := Y - X
--        else
--          Z := X - Y
--        end
--      {{ Z + X = Y ∨ Z + Y = X }}
--
--  Let's turn it into a decorated program...
--
--  WORK IN CLASS

--  ### Example: Reduce to Zero

--  Here is a very simple `while` loop with a simple
--  specification:
--
--      {{ True }}
--        while (X ≠ 0) do
--          X := X - 1
--        end
--      {{ X = 0 }}
--
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
--      while n ≤ X do
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
--        while n ≤ X do
--          X := X - n;
--          Y := Y + 1
--        end
--      {{ n * Y + X = m ∧ X < n }}
--
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
    {{ True }} reduceToZero {{ X = 0 }} := by
  -- First put the postcondition into the form expected by
  -- the while rule.
  apply hoare_consequence_post
  -- We use the fact that after the `while` loop,
  -- the loops condition must not hold.
  · apply hoare_while
    -- Trivial postcondition: we just need to prove `True`
    · apply hoare_post_true; simp
    -- Our precondition that `X ≠ 0` cannot hold is
    -- exactly what we need to prove `X = 0`.
  · simp
    intros _ h; assumption

--  A little more tactic fanciness for helping deal with the
--  boring parts of the process of proving assertions:

macro "verify_assertion" : tactic =>
  `(tactic| assertion_auto)

--  This makes it pretty easy to verify `reduce_to_zero`:

theorem reduce_to_zero_correct''' :
    {{ True }} reduceToZero {{ X = 0 }} := by
  apply hoare_consequence_post
  apply hoare_while
  all_goals verify_assertion

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
--      {{p}} ({{p}} skip {{p}}) ; ({{p}} skip {{p}}) {{p}}
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
--      skip {{ q }}
--
--  on the assumption that the precondition will be provided
--  by somebody else.
--
--  We carry the same assumption through the other syntactic
--  forms: each decorated command is assumed to carry its
--  own postcondition within itself but take its
--  precondition from its context in which it is used.

--  - Sequences `d₁ ; d₂` need no additional decorations.
--
--  Why?
--
--  Because inside `d₂` there will be a postcondition, which
--  also serves as the postcondition of `d₁;d₂`.
--
--  Similarly, inside `d₁` there will also be a
--  postcondition, which additionally serves as the
--  *precondition* for `d₂`.

--  - An assignment `X := a` is decorated only with its
--    postcondition:
--
--      X := a {{ q }}

--  - A conditional `if b then d₁ else d₂` is decorated with
--    a postcondition for the entire statement, as well as
--    preconditions for each branch:
--
--      if b then {{ p₁ }} d₁ else {{ p₂ }} d₂ end {{ q }}

--  - A loop `while (b) {d}` is decorated with its final
--    postcondition plus a precondition for the body:
--
--      while (b) {{ p }} { d } {{ q }}
--
--  The postcondition embedded in `d` serves as the loop
--  invariant.

--  - Implications `↠` can be added as decorations either
--    for a precondition...
--
--      ↠ {{ p }} d
--
--  ...or for a postcondition:
--
--      d ↠ {{ q }}
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
syntax:20 dcom:21 ";" ppDedent(ppLine dcom:20) : dcom
syntax:max "if " "(" imp_bexp ")" ppHardSpace "then" ppLine
  "{{" term "}}" ppLine dcom ppDedent(ppLine "else") ppLine
  "{{" term "}}" ppLine dcom ppDedent(ppLine "end") ppLine
  "{{" term "}}" : dcom
syntax:max "while " "(" imp_bexp ")" ppHardSpace "do" ppLine
  "{{" term "}}" ppLine dcom ppDedent(ppLine "end") ppLine
  "{{" term "}}" : dcom
syntax:5 "↠" " {{" term "}}" ppLine dcom:0 : dcom
syntax:5 dcom:6 ppLine "↠" " {{" term "}}" : dcom

syntax:min "dcom" ppHardSpace "{" ppLine dcom
  ppDedent(ppLine "}") : term

macro_rules
  | `(dcom { $s }) => do
    let stx ← match s with
      | `(dcom| ($body:dcom)) => `(dcom { $body })
      | `(dcom| skip {{ $q }}) => `(DCom.skip ({{ $q }}))
      | `(dcom| $x:ident := $a:imp_aexp {{ $q }}) =>
        `(DCom.asgn $x (aexp { $a }) ({{ $q }}))
      | `(dcom| $d₁:dcom; $d₂:dcom) =>
        `(DCom.seq (dcom { $d₁ }) (dcom { $d₂ }))
      | `(dcom|
          if ($b:imp_bexp) then
            {{ $p₁ }}
            $d₁:dcom
          else
            {{ $p₂ }}
            $d₂:dcom
          end
            {{ $q }}) =>
        `(DCom.cond (bexp { $b })
          ({{ $p₁ }}) (dcom { $d₁ })
          ({{ $p₂ }}) (dcom { $d₂ })
          ({{ $q }}))
      | `(dcom|
          while ($b:imp_bexp) do
            {{ $p }}
            $body:dcom
          end
            {{ $q }}) =>
        `(DCom.whileDo (bexp { $b }) ({{ $p }})
          (dcom { $body }) ({{ $q }}))
      | `(dcom| ↠ {{ $p }} $body:dcom) =>
        `(DCom.pre ({{ $p }}) (dcom { $body }))
      | `(dcom| $body:dcom ↠ {{ $q }}) =>
        `(DCom.post (dcom { $body }) ({{ $q }}))
      | _ => Lean.Macro.throwUnsupported
    return Imp.Elab.withSourceInfoOf s stx

namespace DCom.Delab

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer
  Imp.Elab Imp.Delab

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
    | `({{ $p }}) => return p
    | _ => return stx

private def getDCom? (stx : Term) : Option (TSyntax `dcom) :=
  match stx with
  | `(dcom { $d:dcom }) =>
      some <| withSourceInfoOf (canonical := false) stx d
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
      `(dcom { ↠ {{ $(getAssnBody pre) }} $body })
  | _ => throw ()

@[app_unexpander DCom.post]
def unexpandPost : Unexpander
  | `($_ $body $post) => do
      let some body := getDCom? body | throw ()
      `(dcom { $body ↠ {{ $(getAssnBody post) }} })
  | _ => throw ()

end DCom.Delab
--  END DETAILS

example : DCom :=
  dcom { skip {{ True }} }

example : DCom :=
  dcom {
    while (true) do
      {{ True }}
      skip {{ True }}
    end
      {{ True }}
  }

--  To inspect the fully elaborated term behind this
--  notation, put `set_option pp.all true in` before a
--  `#check` or `#print` command.
--
--  To provide the initial precondition that goes at the
--  very top of a decorated program, we introduce a new type
--  `decorated`:

structure Decorated where
  pre : Assertion
  body : DCom

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
    ↠ {{ X = 0 }}
  }

--  It is easy to go from a `dcom` to a `com` by erasing all
--  annotations.

def DCom.erase (d : DCom) : Com :=
  match d with
  | .skip _ => .skip
  | .seq d₁ d₂ => .seq d₁.erase d₂.erase
  | .asgn x a _ => .asgn x a
  | .cond b _ d₁ _ d₂ _ => .cond b d₁.erase d₂.erase
  | .whileDo b _ body _ => .whileDo b body.erase
  | .pre _ body => body.erase
  | .post body _ => body.erase

def Decorated.erase (dec : Decorated) : Com :=
  dec.body.erase

--  We cannot use `dcom { ... }` syntax in pattern matches.

--  It is also straightforward to extract the precondition
--  and postcondition from a decorated program.

@[simp]
def Decorated.precondition (dec : Decorated) : Assertion :=
  dec.pre

--  Notice the `@[simp]` annotation we added here. This
--  directs Lean to generate an equational lemma of the same
--  form as the characterizing lemmas we've been writing by
--  hand, such as `validHoareTriple_def` and
--  `Assertion.subst_apply` in the Hoare chapter, and add it
--  to the `simp` set. We can see the added equation by
--  printing it.

#print equations Decorated.precondition

--  Output:
--    equations:
--    @[backward_defeq] theorem Decorated.precondition.eq_1 : ∀ (dec : Decorated), dec.precondition = dec.pre

--  We'll add `@[simp]` annotations on the following
--  definitions, too.

@[simp]
def DCom.postcondition (d : DCom) : Assertion :=
  match d with
  | .skip q => q
  | .seq _ d₂ => d₂.postcondition
  | .asgn _ _ q => q
  | .cond _ _ _ _ _ q => q
  | .whileDo _ _ _ q => q
  | .pre _ body => body.postcondition
  | .post _ q => q

@[simp]
def Decorated.postcondition (dec : Decorated) : Assertion :=
  dec.body.postcondition

--  We can then express what it means for a decorated
--  program to be correct as follows:

def Decorated.OuterTripleValid (dec : Decorated) : Prop :=
  ValidHoareTriple dec.precondition dec.erase
    dec.postcondition

--  For example, here is this definition unfolded for
--  `decWhile`:

example : decWhile.OuterTripleValid =
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
--  decorated command `d` together with a precondition `p`
--  and returns a *proposition* that, if it can be proved,
--  implies that the triple
--
--      {{p}} d.erase {{d.postcondition}}
--
--  is valid.
--
--  It does this by walking over `d` and generating a big
--  conjunction that includes
--  - local consistency checks for each form of command,
--    plus
--  - uses of `↠` to bridge the gap between the assertions
--    found inside a decorated command and the assertions
--    imposed by the external precondition; these uses
--    correspond to applications of the consequence rule.

--  *Local consistency* is defined as follows...
--  - The decorated command
--
--      skip {{q}}
--
--  is locally consistent with respect to a precondition `p`
--  if `p ↠ q`.

--  - The sequential composition of `d₁` and `d₂` is locally
--    consistent with respect to `p` if `d₁` is locally
--    consistent with respect to `p` and `d₂` is locally
--    consistent with respect to the postcondition of `d₁`.

--  - An assignment
--
--      X := a {{q}}
--
--  is locally consistent with respect to a precondition `p`
--  if:
--
--      p ↠ q [X ↦ a]

--  - A conditional
--
--      if b then {{p₁}} d₁ else {{p₂}} d₂ end {{q}}
--
--  is locally consistent with respect to precondition `p`
--  if
--
--  (1) `p ∧ b ↠ p₁`
--
--  (2) `p ∧ b ↠ p₂`
--
--  (3) `d₁` is locally consistent with respect to `p₁`
--
--  (4) `d₂` is locally consistent with respect to `p₂`
--
--  (5) `d₁.postcondition ↠ q`
--
--  (6) `d₂.postcondition ↠ q`

--  - A loop
--
--      while (b) {{{q}} d} {{r}}
--
--  is locally consistent with respect to precondition `p`
--  if:
--
--  (1) `p ↠ d.postcondition`
--
--  (2) `d.postcondition ∧ b ↠ q`
--
--  (3) `d.postcondition ∧ b ↠ r`
--
--  (4) `d` is locally consistent with respect to `q`

--  - A command with an extra assertion at the beginning
--
--      ↠ {{q}} d
--
--  is locally consistent with respect to a precondition `p`
--  if:
--
--  (1) `p ↠ q`
--
--  (2) `d` is locally consistent with respect to `q`

--  - A command with an extra assertion at the end
--
--      d ↠ {{q}}
--
--  is locally consistent with respect to a precondition `p`
--  if:
--
--  (1) `d` is locally consistent with respect to `p`
--
--  (2) `d.postcondition ↠ q`

--  With all this in mind, we can write a *verification
--  condition generator* that takes a decorated command and
--  reads off a proposition saying that all its decorations
--  are locally consistent.
--
--  Formally, since a decorated command is "waiting for its
--  precondition" the main VC generator takes a `dcom` plus
--  a given precondition as arguments.

@[simp]
def DCom.VerificationConditions
    (p : Assertion) (d : DCom) : Prop :=
  match d with
  | .skip q =>
      p ↠ q
  | .seq d₁ d₂ =>
      d₁.VerificationConditions p ∧
      d₂.VerificationConditions d₁.postcondition
  | .asgn x a q =>
      p ↠ {{ q [x ↦ a] }}
  | .cond b p₁ d₁ p₂ d₂ q =>
      ({{ p ∧ b }} ↠ p₁) ∧
      ({{ p ∧ ¬ b }} ↠ p₂) ∧
      (d₁.postcondition ↠ q) ∧
      (d₂.postcondition ↠ q) ∧
      d₁.VerificationConditions p₁ ∧
      d₂.VerificationConditions p₂
  | .whileDo b bodyPre body q =>
      -- The body's postcondition is both the loop invariant
      -- and the precondition for the first iteration.
      (p ↠ body.postcondition) ∧
      ({{ body.postcondition ∧ b }} ↠ bodyPre) ∧
      ({{ body.postcondition ∧ ¬ b }} ↠ q) ∧
      body.VerificationConditions bodyPre
  | .pre p' body =>
      (p ↠ p') ∧ body.VerificationConditions p'
  | .post body q =>
      body.VerificationConditions p ∧
      (body.postcondition ↠ q)

--  The following key theorem states that
--  `DCom.VerificationConditions` does its job correctly.
--  Not surprisingly, each of the Hoare Logic rules plays a
--  critical role at some point in the proof.

theorem verification_correct (d : DCom) (p : Assertion)
    (hvc : d.VerificationConditions p) :
    ValidHoareTriple p d.erase d.postcondition := by
  induction d generalizing p with
    simp only [DCom.VerificationConditions, DCom.erase,
      DCom.postcondition] at hvc ⊢
  -- Note that we need to escape `skip` as `«skip»`,
  -- as it is a reserved word under Hoare2's `dcom` syntax.
  | «skip» q =>
    apply hoare_consequence_pre
    · apply hoare_skip
    · exact hvc
  | seq d₁ d₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hvc
    apply hoare_seq
    · apply ih₂; exact h₂
    · apply ih₁; exact h₁
  | asgn x a q =>
    apply hoare_consequence_pre
    · apply hoare_asgn
    · exact hvc
  | cond b p₁ d₁ p₂ d₂ q ih₁ ih₂ =>
    obtain ⟨hpre₁, hpre₂, hd₁, hd₂, hthen, helse⟩ := hvc
    specialize ih₁ p₁ hthen
    specialize ih₂ p₂ helse
    apply hoare_if
    · apply hoare_consequence
      · exact ih₁
      · exact hpre₁
      · exact hd₁
    · apply hoare_consequence
      · exact ih₂
      · exact hpre₂
      · exact hd₂
  | whileDo b bodyPre body q ih =>
    obtain ⟨hpre, hbody, hpost, hd⟩ := hvc
    apply hoare_consequence
    · apply hoare_while
      apply hoare_consequence_pre
      · apply ih; exact hd
      · exact hbody
    · exact hpre
    · exact hpost
  | pre p' body ih =>
    obtain ⟨hp, hd⟩ := hvc
    apply hoare_consequence_pre
    · apply ih; exact hd
    · exact hp
  | post body q ih =>
    obtain ⟨hd, hq⟩ := hvc
    apply hoare_consequence_post
    · apply ih; exact hd
    · exact hq

--  Now that all the pieces are in place, we can define what
--  it means to verify an entire program.

@[simp]
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

sf_expect_failure_in
  example : decWhile.VerificationConditions := by
    rw [Decorated.VerificationConditions, decWhile]
    simp only [DCom.VerificationConditions,
      DCom.postcondition]

--  Fortunately, our `verify_assertion` tactic can generally
--  take care of most (or sometimes, all) of them.

example : decWhile.VerificationConditions := by
  simp only [decWhile]
  verify_assertion

--  We develop another tactic, `verify`, to automate the
--  overall process of verification. It uses
--  `verification_conditions_correct` to extract the
--  verification conditions, and the logic of
--  `verify_assertion` to verify them as much as it can. We
--  enhance this logic with some low-level simplification
--  lemmas, defined next, to make the process a little
--  smoother.

theorem Bexp.eval_le_true {st : State} {a₁ a₂ : Aexp} :
    (Bexp.le a₁ a₂).eval st = true ↔ a₁.eval st ≤ a₂.eval st := by
  simp

theorem Bexp.eval_le_false {st : State} {a₁ a₂ : Aexp} :
    (Bexp.le a₁ a₂).eval st = false ↔ ¬ a₁.eval st ≤ a₂.eval st := by
  simp

theorem Bexp.eval_gt_true {st : State} {a₁ a₂ : Aexp} :
    (Bexp.gt a₁ a₂).eval st = true ↔ a₁.eval st > a₂.eval st := by
  simp

theorem Bexp.eval_gt_false {st : State} {a₁ a₂ : Aexp} :
    (Bexp.gt a₁ a₂).eval st = false ↔ ¬ a₁.eval st > a₂.eval st := by
  simp

macro "verify" : tactic =>
  `(tactic|
    (apply verification_conditions_correct;
     simp +decide [-Bexp.eval_le, -Bexp.eval_gt,
       Bexp.eval_le_true, Bexp.eval_le_false,
       Bexp.eval_gt_true, Bexp.eval_gt_false,
       assertImplies_def, assertIff_def,
       validHoareTriple_def, Assertion.subst_def];
     all_goals and_intros;
     all_goals try lia))

--  Here's the final, formal proof that `decWhile` is
--  correct.

theorem dec_while_correct : decWhile.OuterTripleValid := by
  simp only [decWhile]
  verify

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
--      {{ X = m ∧ Y = n }}
--        while X ≠ 0 do
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
--      (1)    {{ X = m ∧ Y = n }}  ↠                   (a)
--      (2)    {{ Inv }}
--               while X ≠ 0 do
--      (3)              {{ Inv ∧ X ≠ 0 }}  ↠          (c)
--      (4)              {{ Inv [X ↦ X-1] [Y ↦ Y-1] }}
--                 Y := Y - 1;
--      (5)              {{ Inv [X ↦ X-1] }}
--                 X := X - 1
--      (6)              {{ Inv }}
--               end
--      (7)    {{ Inv ∧ ¬ (X ≠ 0) }}  ↠                (b)
--      (8)    {{ Y = n - m }}

--  Examining this skeleton, we can see that any valid `Inv`
--  will have to respect three conditions:
--  - (a) it must be *weak* enough to be implied by the
--    loop's precondition, i.e., (1) must imply (2);
--  - (b) it must be *strong* enough to imply the program's
--    postcondition, i.e., (7) must imply (8);
--  - (c) it must be *preserved* by a single iteration of
--    the loop, assuming that the loop guard also evaluates
--    to true, i.e., (3) must imply (4).

--  WORK IN CLASS (by filling in the previous template)

--  The following program computes the integer square root
--  of `X` by naive iteration:
--
--      {{ X=m }}
--        Z := 0;
--        while (Z+1)*(Z+1) ≤ X do
--          Z := Z+1
--        end
--      {{ Z*Z≤m ∧ m<(Z+1)*(Z+1) }}
--
--  WORK IN CLASS

--  Here is a program that squares `X` by repeated addition:
--
--      {{ X = m }}
--        Y := 0;
--        Z := 0;
--        while Y ≠ X  do
--          Z := Z + X;
--          Y := Y + 1
--        end
--      {{ Z = m*m }}
--
--  WORK IN CLASS

--  ## Weakest Preconditions (Optional)

--  A useless (though valid) Hoare triple:
--
--      {{ False }}  X := Y + 1  {{ X ≤ 5 }}
--
--  A better precondition:
--
--      {{ Y ≤ 4 ∧ Z = 0 }}  X := Y + 1 {{ X ≤ 5 }}
--
--  The *best* precondition:
--
--      {{ Y ≤ 4 }}  X := Y + 1  {{ X ≤ 5 }}
--
--  Assertion `Y ≤ 4` is a *weakest precondition* of command
--  `X := Y + 1` with respect to postcondition `X ≤ 5`.
--  Think of *weakest* here as meaning "easiest to satisfy":
--  a weakest precondition is one that as many states as
--  possible can satisfy.

--  `p` is a weakest precondition of command `c` for
--  postcondition `q` if
--  - `p` is a precondition, that is, `{{p}} c {{q}}`; and
--  - `p` is at least as weak as all other preconditions,
--    that is, if `{{p'}} c {{q}}` then `p' ↠ p`.
--
--  Note that weakest preconditions need not be unique. For
--  example, `Y ≤ 4` was a weakest precondition above, but
--  so are the logically equivalent assertions `Y < 5`,
--  `Y ≤ 2 * 2`, etc. It is easy to show that any two
--  weakest preconditions `p` and `p'` of a command `c` with
--  respect to postcondition `q` are logically equivalent;
--  that is, `p ↞↠ p'`.

def IsWp (p : Assertion) (c : Com) (q : Assertion) : Prop :=
  ValidHoareTriple p c q ∧
  ∀ p' : Assertion, {{ p' }} c {{ q }} → p' ↠ p

theorem isWp_def {p : Assertion} {c : Com} {q : Assertion} :
    IsWp p c q ↔
      ValidHoareTriple p c q ∧
      ∀ p' : Assertion, {{ p' }} c {{ q }} → p' ↠ p := by
  rfl

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
--       while (true) {X := 0}
--       {{ X = 0 }}

-- Source revision: 37dc7b2, committed 2026-10-19 15:47 UTC

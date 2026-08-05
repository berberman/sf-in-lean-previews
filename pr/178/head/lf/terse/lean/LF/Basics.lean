import LF.SFLCompat

-- # Basics: Functional Programming in Lean

-- Note to developers (Jonathan Chan  @ionathanch):
--     [BCP: Old comment -- might be out of date?] There should
--     be some instruction on interaction with the IDE, namely:
--
--     - how to read the proof state
--
--     - clicking immediately after a tactic will show you what
--       it changed
--
--     - clicking after each `h` in `rw [h₁, h₂, ...]` will show
--       you what was rewritten
--
--     - hovering over a tactic will provide documentation on how
--       to use it
--
--     - hovering over a definition will give its type
--
--     - hovering over a Unicode character will tell you how to
--       type it
--
--     - Ctrl-clicking on a definition will take you to the
--       definition location

-- ## Data and Functions

-- In Lean, we can build practically everything from first
-- principles...

-- ### Days of the Week (Enumerated Types)

-- A datatype definition:

inductive Day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

-- A function on days:

def nextWorkingDay (d : Day) : Day :=
  match d with
  | Day.monday    => Day.tuesday
  | Day.tuesday   => Day.wednesday
  | Day.wednesday => Day.thursday
  | Day.thursday  => Day.friday
  | Day.friday    => Day.monday
  | Day.saturday  => Day.monday
  | Day.sunday    => Day.monday

-- Evaluation:

#eval nextWorkingDay Day.friday

-- Day.monday

#eval nextWorkingDay (nextWorkingDay Day.saturday)

-- Day.tuesday

-- We can also record what we *expect* the result of calling a
-- function to be in the form of a Lean `example`:

example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
  rfl

-- The `rfl` tactic is used to observe that both sides of an
-- equal sign evaluate to the same value.

-- ### Booleans

-- Another familiar enumerated type; we'll switch to Lean's
-- built-in `Bool` later:

inductive MyBool : Type where
  | true
  | false

-- This command opens the namespace associated with the
-- `MyBool` type:

namespace MyBool

-- Functions over booleans can be defined in the same way as
-- functions over days of the week.

def not (b : MyBool) : MyBool :=
  match b with
  | MyBool.true => MyBool.false
  | MyBool.false => MyBool.true

def and (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | MyBool.true => b2
  | MyBool.false => MyBool.false

def or (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | MyBool.true => MyBool.true
  | MyBool.false => b2

-- Note the syntax for defining multi-argument functions (`and`
-- and `or`).

example : or MyBool.true  MyBool.false = MyBool.true  := by rfl
example : or MyBool.false MyBool.false = MyBool.false := by rfl
example : or MyBool.false MyBool.true  = MyBool.true  := by rfl
example : or MyBool.true  MyBool.true  = MyBool.true  := by rfl

-- We can define new symbolic notations for existing
-- definitions. Don't worry for now about how the notation is
-- defined.

local prefix:40 (priority := high) "!" => not
local infixl:35 (priority := high) " && " => and
local infixl:30 (priority := high) " || " => or

example : (MyBool.false || MyBool.false || MyBool.true) = MyBool.true := by rfl

example : (!MyBool.false) = MyBool.true := by rfl

-- ### Exercise (1 star): nand ⭐

-- The `sorry` keyword is a placeholder for an incomplete proof
-- or definition. We use it in exercises to indicate the parts
-- that we're leaving for you — i.e., your job is to replace
-- `sorry` with real definitions and proofs.

-- Remove `sorry` below and complete the definition of the
-- following function. The function should return `MyBool.true`
-- if either or both of its inputs are `MyBool.false`. Make
-- sure that the `example` assertions below can be verified by
-- Lean.

def nand (b1 : MyBool) (b2 : MyBool) : MyBool
  := sorry

example : nand MyBool.true  MyBool.false = MyBool.true  := sorry
example : nand MyBool.false MyBool.false = MyBool.true  := sorry
example : nand MyBool.false MyBool.true  = MyBool.true  := sorry
example : nand MyBool.true  MyBool.true  = MyBool.false := sorry

-- ### Exercise (1 star): and3 ⭐

-- Do the same for the `and3` function below. This function
-- should return `true` when all of its inputs are `true`, and
-- `false` otherwise.

def and3 (b1 : MyBool) (b2 : MyBool) (b3 : MyBool) : MyBool
  := sorry

example : and3 MyBool.true  MyBool.true  MyBool.true  = MyBool.true  := sorry
example : and3 MyBool.false MyBool.true  MyBool.true  = MyBool.false := sorry
example : and3 MyBool.true  MyBool.false MyBool.true  = MyBool.false := sorry
example : and3 MyBool.true  MyBool.true  MyBool.false = MyBool.false := sorry

-- ### Basic Proofs

-- Let's prove something simple about booleans:

theorem true_and : ∀ (b : MyBool), (MyBool.true && b) = b := by
  intro b
  rfl

-- And now let's see it in a bit more detail:

-- Note to developers (mwhicks1):
--     The theorem below has wonderful explaining what's going
--     on, but it is not typeset. Are we planning to fix that
--     problem? I re-flowed the text so it reads better on the
--     WWW in case not.

theorem true_and_explained : ∀ (b : MyBool), (MyBool.true && b) = b := by
  /- Move your cursor (click) here to see the initial proof state in
     the InfoView. If you are viewing the book online,
     instead click on the white button after `by`.
     The context (before the ⊢) is empty.
     The goal is `∀ (b : MyBool), (MyBool.true && b) = b`. -/
  intro b
  /- Now click here (or the white button after `intro b`)
     to see the new proof state that results from the
     tactic. Notice how `intro b` has changed the _context_: it now
     contains `b : MyBool`.

    The `intro` tactic is used to name variables quantified by a `∀`.
    Since we are trying to prove a property of all `MyBools`, we
    proceed by introducing an unknown `MyBool` `b` and prove
    the property holds for `b`, regardless of what it is.  Informally,
    this move can be read, "We want to prove <some property> for all
    `MyBool`s `b`. So suppose `b` is some arbitrary `MyBool`...
    <and then go on to prove the property for this particular `b`>..."
    Since `b` was chosen arbitrarily, we've now proved the property
    for all `b`.

    A proof of a theorem beginning with a ∀ will typically start with
    an `intro`.

    As in the `example`s above, we can use the `rfl` tactic,
    which closes goals about equality where both sides are equal to
    one another according to the principle of reflexivity. Now,
    inspecting our goal will show that it is `(MyBool.true && b) = b`,
    which may not appear to be equal to itself. However, the tactic
    _evaluates_ both sides of the equality before comparing them. In
    this case, if we look at the definition of `and`, we can see that,
    when its first argument is `MyBool.true`, the result is its second
    argument. So the two terms `MyBool.true && b` and `b` are in fact
    equal because one evaluates to the other.
  -/
  rfl
  /- The proof is now done! The Lean InfoView tells us there are "No goals". -/

-- ### Exercise (1 star): false_or_exercise ⭐

-- Here's a simple proof for you to try. Remove `sorry` and
-- fill in the proof.

theorem false_or : ∀ (b : MyBool), (MyBool.false || b) = b := by
  sorry

-- Now we'll switch to Lean's definition of booleans.

end MyBool

-- ### Types

-- We can use `#check` to check the type of an expression:

#check Bool.true

-- Bool.true : Bool

#check (Bool.true : Bool)
#check (Bool.not Bool.true : Bool)

-- true : Bool

-- !true : Bool

#check Bool.not

-- ### New Types from Old

-- Note to developers (Harrison Goldstein  @hgoldstein95):
--     I feel like this section has too much content in terse,
--     but I don't want to unilaterally make that call. TODO

-- A more interesting type definition:

inductive RGB : Type where
  | red
  | green
  | blue

inductive Color : Type where
  | black
  | white
  | primary (p : RGB)

-- We can define functions on colors using pattern matching,
-- just as we did for `Day` and `Bool`.

def monochrome (c : Color) : Bool :=
  match c with
  | Color.black => Bool.true
  | Color.white => Bool.true
  | Color.primary p => Bool.false

-- We can use a *wildcard* pattern `_` to match something we
-- don't care about:

def monochrome' (c : Color) : Bool :=
  match c with
  | Color.black => Bool.true
  | Color.white => Bool.true
  | Color.primary _ => Bool.false

-- We can use a constant argument to `Color.primary` to match a
-- specific primary color:

def isRed (c : Color) : Bool :=
  match c with
  | Color.black => Bool.false
  | Color.white => Bool.false
  | Color.primary RGB.red => Bool.true
  | Color.primary _ => Bool.false

-- An alternative way to write the same function would be to
-- explicitly nest match statements:

def isRed' (c : Color) : Bool :=
  match c with
  | Color.black => Bool.false
  | Color.white => Bool.false
  | Color.primary r =>
    match r with
    | RGB.red => Bool.true
    | _ => Bool.false

-- ### Exercise (1 star): is_weekend ⭐

-- Define a function that takes a `Day` and returns true if the
-- day is a weekend, and false otherwise.

-- Then, fill in right-hand sides of the `example` blocks
-- below. If you've done both correctly, the blocks will
-- produce no errors and contain no `sorry`.

-- Hint: You could write this function by pattern matching on
-- each possible day of the week, or you could try to come up
-- with a shorter solution...

def is_weekend (d : Day) : Bool
  := sorry

example : is_weekend Day.sunday = true := sorry
example : is_weekend Day.friday = false := sorry

-- ### Exercise (1 star): isInversion ⭐

-- Define a function that takes two colors and returns `true`
-- if the second color is an *inversion* of the first, and
-- false otherwise.

-- Inversion is defined by cases: Black is an inversion of
-- white, and vice versa. Red is an inversion of blue, and vice
-- versa. Green is not an inversion of anything.

-- As before, write the right-hand sides of the `example`
-- blocks to ensure they pass with no `sorry`.

def isInversion (c1 c2 : Color) : Bool
  := sorry

example : isInversion Color.black Color.white = true := sorry
example : isInversion Color.white Color.black = Bool.true := sorry
example : isInversion (Color.primary RGB.red) (Color.primary RGB.blue) = Bool.true :=
  sorry
example : isInversion (Color.primary RGB.green) (Color.primary RGB.red) = Bool.false :=
  sorry

-- ### Namespaces

-- `namespace` declarations create separate namespaces.

def myFoo : Bool := true
namespace Playground
def myFoo : RGB := RGB.blue
end Playground

#check myFoo
#check Playground.myFoo

-- myFoo : Bool

-- Playground.myFoo : RGB

namespace Playground
-- this refers to the `myFoo` we defined in the `Playground` namespace previously
def myBar : RGB := myFoo
end Playground

#check Playground.myBar

-- Playground.myBar : RGB

-- Type definitions implicitly create namespaces.

namespace RGB
def myBlue : RGB := blue
end RGB

-- Top-level definitions can also be prefixed by a namespace,
-- which opens the namespace temporarily for the body of the
-- definition.

-- Note to developers (Claude, NOW):
--     Rendering bug in **student** and **terse** (solutions is
--     fine): the leading `--- …` triple-dash comment lines in
--     this block and the next one each render **twice** in a
--     row (e.g. two consecutive `--- this works, because …`
--     lines). The solutions build shows each once, so this is
--     a Verso rendering quirk with `---`-style comments in the
--     elided builds, not a source duplication.

--- this works, because the definition is qualified by `RGB.`
def RGB.myOtherBlue : RGB := myBlue

#check RGB.myBlue
#check RGB.myOtherBlue

-- RGB.myBlue : RGB

-- RGB.myOtherBlue : RGB

sf_expect_failure
  -- this doesn't work; the identifier is unknown
  #check myBlue

-- Unknown identifier `myBlue`

def Day.nextWorkingDay' (d : Day) : Day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday

-- `open` brings definitions from a namespace into scope.

namespace MyNamespace
def myDef : Bool := Bool.true
end MyNamespace

open MyNamespace

#check myDef

-- MyNamespace.myDef : Bool

-- If we only want to bring *some*, rather than all, of the
-- definitions of a namespace into the current scope, we can
-- use the `open (...)` form:

namespace MyOtherNamespace
def myHiddenDef : Bool := Bool.true
def myVisibleDef : Bool := Bool.false
end MyOtherNamespace

open MyOtherNamespace (myVisibleDef)

-- `myVisibleDef` is now usable without qualification:
#check myVisibleDef

-- MyOtherNamespace.myVisibleDef : Bool

-- But `myHiddenDef`, which we did not `open`, still needs its
-- full name; using it unqualified is an error:

sf_expect_failure
  #check myHiddenDef

-- Unknown identifier `myHiddenDef`

-- Names from the `Bool` `namespace` are `open`ed and thus
-- available without qualification.

#check Bool.true
#check true

-- Bool.true : Bool

-- Bool.true : Bool

-- Lean can often guess which qualified name we mean if we
-- don't supply it explicitly:

def nextWorkingDay' (d : Day) : Day :=
  match d with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday

-- ### Exercise (0 stars): custom_namespace_checks

-- Predict the output of each of the statements below. Do you
-- think their results would change depending on which
-- namespace the statements appear in? How?

-- #check .black -- Write your prediction here.
-- #check Color.black -- Write your prediction here.
-- #check RGB -- Write your prediction here.
-- #check Playground.myFoo -- Write your prediction here.

-- Once you have written your predictions, copy the lines from
-- the comment into an active section of the book to evaluate
-- them.

-- Note to developers (mwhicks1):
--     This namespace section is great, but it interrupts the
--     pedagogical flow of the presentation of inductive types.
--     We were prevoiusly looking at constructors With one
--     argument, then there was this big digression, and now we
--     are back to two. Are we able to move the namespace stuff
--     to the end of this section (Data and Functions)? Then we
--     can start it by saying we are finishing with it but
--     readers can skip it if they prefer to "follow their
--     nose" regarding namespaces, and come back when they want
--     to know more.

-- ### Constructors with Multiple Parameters (Tuple Types)

namespace Playground

-- A Nibble is half a byte — four bits.

inductive Bit : Type where
  | b1
  | b0

inductive Nibble : Type where
  | bits (x0 x1 x2 x3 : Bit)

#check Nibble.bits .b1 .b0 .b1 .b0

-- Nibble.bits Bit.b1 Bit.b0 Bit.b1 Bit.b0 : Nibble

-- We can deconstruct a Nibble by pattern-matching.

def allZero (nb : Nibble) : Bool :=
  match nb with
  | .bits .b0 .b0 .b0 .b0 => true
  | .bits _   _   _   _   => false

example : allZero (.bits .b1 .b0 .b1 .b0) = false := by rfl
example : allZero (.bits .b0 .b0 .b0 .b0) = true  := by rfl

end Playground

-- ### Natural Numbers

namespace NatPlayground

-- For simplicity in proofs, we choose a *unary* representation
-- of natural numbers.

inductive Nat : Type where
  | zero
  | succ (n : Nat)

-- Eventually we'll swap to Lean's definition of natural
-- numbers, which is very similar to this.

namespace Nat

def one   : Nat := succ zero
def two   : Nat := succ one
def three : Nat := succ two
def four  : Nat := succ three

-- We can also write functions on `Nat`.

def pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n' => n'

def minusTwo (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ (zero) => zero
  | succ (succ n') => n'

#eval minusTwo four

-- Here are some recursive functions on natural numbers:

def even (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even n'

example : even one = false := by rfl
example : even four = true := by rfl

-- We could define `odd` by a similar recursive declaration,
-- but here is a simpler way:

def odd (n : Nat) : Bool :=
  not (even n)

example : odd one = true := by rfl
example : odd four = false := by rfl

-- This function takes multiple parameters, recursing on the
-- second:

def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

#eval add one two -- succ (succ (succ zero)) -- aka, three!

-- NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero)))

-- We can also define infix notation for our `add` functions.

scoped infixl:65 " + " => add

#eval one + two -- succ (succ (succ zero)) -- aka, three again.

-- NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero)))

-- ## Proof by Rewriting

-- ### Proving properties about functions in Lean

-- We can prove properties of recursive functions like `add`:

theorem add_zero : ∀ n : Nat, n + zero = n := by
  intro n
  rfl

#check add_zero

-- NatPlayground.Nat.add_zero (n : Nat) : n + zero = n

-- Using our simplification rule `add_zero`, we can carry out a
-- simple proof about natural numbers!

theorem add_zero_zero : ∀ n : Nat, n + zero + zero = n := by
  intro n
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

-- We'll walk through this proof in the next section.

-- ### Proof state and tactics

-- Here is the previous proof in more detail:

theorem add_zero_zero_explained : ∀  n : Nat, n + zero + zero = n := by
  intro n
  /- After introducing `n`, our goal is `n + zero + zero = n`.
     What can we do to simplify this expression? If you hover your cursor over the
     `add_zero` in the rewrite below, you can see its type: `n + zero = n`. So,
     we can use that rewrite rule to transform an appearnce of `n + zero` in the goal to `n`. -/
  rewrite [add_zero]
  /- Now click here to see the new proof state that results from the tactic.
     Notice how `n + zero + zero` changes to `n + zero` in the goal. -/
  rewrite [add_zero]
  /- Again the goal changes, from `n + zero` to `n`. Now the proof state
     is an equality with both sides equal, so it can be closed by the
     tactic `rfl`. -/
  rfl
  /- The proof is now done! The Lean InfoView tells us there are "No goals". -/

-- Give this proof a try (it's similar):

theorem add_zero_zero_zero : ∀ n : Nat, n + zero + zero + zero = n := by
  sorry

-- The `rfl` closes a goal that looks like `a = a`, reducing
-- both sides of the equality in the process.

-- ### A New `add` Rule

-- Here's another rule we can use for `add`:

theorem add_succ : ∀ n m : Nat, n + (succ m) = succ (n + m) := by
  intro n m
  rfl

-- Now, let's use `add_succ` in a proof:

theorem add_one (n : Nat) : n + (succ zero) = succ n + zero := by
  rewrite [add_succ]
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

-- ### Irreducibility, Rewriting, and Proof Engineering

-- After proving the theorems that characterize a definition,
-- we mark the definition `irreducible` to require rewriting by
-- them instead of using `rfl`.

attribute [irreducible] add

-- These characterizing theorems also follow a particular
-- pattern. Let's look again at the definition of `add`,
-- without the `+` notation for maximum clarity:

namespace AddPlayground

def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

theorem add_zero : ∀ (n : Nat), add n zero = n := by
  intro n
  rfl

theorem add_succ : ∀ (n m : Nat), add n (succ m) = succ (add n m) := by
  intro n m
  rfl

end AddPlayground

-- Each branch of a definition's control flow gets one
-- *simplification lemma*. Here are the two for `pred`:

theorem pred_zero : pred zero = zero := by rfl
theorem pred_succ n : pred (succ n) = n := by rfl

-- Now that we have defined and proved `pred`'s simplification
-- lemmas, we can mark it `irreducible`, to enforce rewriting
-- by these lemmas.

attribute [irreducible] pred

-- Similarly, for each of the three branches of the definition
-- of `even`, we need one simplification lemma:

theorem even_zero : even zero = true := rfl
theorem even_one : even (succ zero) = false := rfl
theorem even_succ_succ n : even (succ (succ n)) = even n := rfl

attribute [irreducible] even odd

-- From here on, we pair each definition with its
-- simplification lemmas and rewrite by those lemmas rather
-- than `rfl`-ing through the definition.

-- ### Working with Numerals

-- We know from our definitions above that `one` is just
-- `succ zero`, `two` is `succ one`, and so on. We can write
-- rules for these equalities too:

theorem one_eq_succ_zero : one = succ zero := by rfl
theorem two_eq_succ_one : two = succ one := by rfl
theorem three_eq_succ_two : three = succ two := by rfl
theorem four_eq_succ_three : four = succ three := by rfl

-- ### Exercise (1 star): mul_simpl_rules ⭐

-- Finish the proof using the `add` rules:

theorem one_plus_one_eq_two : one + one = two := by
  rewrite [one_eq_succ_zero]
  sorry

-- Try the same for `two + two = four`.

theorem two_plus_two_eq_four : two + two = four := by
  sorry

def mul (n m : Nat) : Nat :=
  match m with
  | zero => zero
  | succ m' => (mul n m') + n

scoped infixl:70 " * " => mul

-- ### Exercise (1 star): mul_simpl_rules ⭐

-- Multiplication, like any function we will prove properties
-- about, also has simplification rules.

-- Remove `sorry` and prove the simplification rules for `mul`
-- below. You will likely find the proofs of the simplification
-- rules for `add` to be helpful as a model.

-- Note to developers:
--     @rogerburtonpatel: it would be nice if we could get the
--     theorem *statements* inside a `solution!` block as well.

theorem mul_zero : ∀ n : Nat, n * zero = zero := by
  sorry

theorem mul_succ : ∀ n m : Nat, n * (succ m) = (n * m) + n := by
  sorry

attribute [irreducible] mul

-- Prove these thoerems using rewriting with the simplification
-- rules for addition and multiplication.

-- ### Exercise (2 stars): test_mul_add ⭐⭐

theorem zero_add_one : (zero + one : Nat) = one := by
  rewrite [one_eq_succ_zero]
  sorry

theorem one_add_one : (one + one : Nat) = two := by
  rewrite [one_eq_succ_zero]
  sorry


theorem zero_mul_two : (zero * two : Nat) = zero := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  sorry

theorem one_mul_two : (one * two : Nat) = two := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  sorry

theorem two_mul_two : (two * two : Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  sorry

-- Here is a function `beq` that tests natural numbers for
-- equality, yielding a boolean.

def beq (n m : Nat) : Bool :=
  match n with
  | zero => match m with
            | zero => true
            | succ _ => false
  | succ n' => match m with
               | zero => false
               | succ m' => beq n' m'

-- We could also write this by pattern matching on both `n` and
-- `m` at the same time:

def beq' (n m : Nat) : Bool :=
  match n, m with
  | zero, zero => true
  | zero, succ _ => false
  | succ _, zero => false
  | succ n', succ m' => beq n' m'

-- The definitions of `beq` and `beq'` are equivalent.

-- Similarly, the `ble` function tests whether its first
-- argument is less than or equal to its second argument,
-- yielding a boolean.

def ble (n m : Nat) : Bool :=
  match n with
  | zero => true
  | succ n' =>
      match m with
      | zero => false
      | succ m' => ble n' m'

theorem zero_ble (n : Nat) : ble zero n = true := by rfl
theorem succ_ble_zero (n : Nat) : ble (succ n) zero = false := by rfl
theorem succ_ble_succ (n m : Nat) : ble (succ n) (succ m) = ble n m := by rfl

example : ble two two = true  := by rfl
example : ble two four = true := by rfl
example : ble four two = false := by rfl

-- ### Exercise (1 star): blt ⭐

-- Define a less-than function in terms of `ble`.

def blt (n m : Nat) : Bool := sorry

example : blt two two = false := sorry
example : blt two four = true  := sorry
example : blt four two = false := sorry

attribute [irreducible] blt ble

-- We'll be using `beq` a lot, so let's give it an infix
-- notation.

scoped infixl:30 " == " => beq

-- Note that now `==` and `=` are different; the former means
-- `beq` whereas the latter is a logical claim.

theorem zero_zero_beq_true : (zero == zero) = true := by rfl
theorem zero_succ_beq_false (n : Nat) : (zero == (succ n)) = false := by rfl
theorem succ_zero_beq_false (n : Nat) : ((succ n) == zero) = false := by rfl
theorem succ_succ_beq (n m : Nat) : ((succ n) == (succ m)) = (n == m) := by rfl

attribute [irreducible] beq

-- ## General Proofs about Natural Numbers

-- A (slightly) more interesting theorem:

theorem add_id_example : ∀ n m : Nat,
    n = m → n + n = m + m := by
  intro n m
  intro h
  rewrite [h]
  rfl

-- ### Exercise (1 star): add_id_exercise ⭐

-- Remove `sorry` and fill in the proof.

theorem add_id_exercise : ∀ n m o : Nat,
    n = m → m = o → n + m = m + o := by
  sorry

-- ### Displaying Theorem Statements

-- The `#check` command can also be used to examine the
-- statements of previously declared lemmas and theorems.

#check mul_zero  -- ∀ (n : Nat), n * 0 = 0
#check mul_succ  -- ∀ (n m : Nat), n * Nat.succ m = n + n * m

-- NatPlayground.Nat.mul_zero (n : Nat) : n * zero = zero

-- NatPlayground.Nat.mul_succ (n m : Nat) : n * succ m = n * m + n

-- Lean may:

-- - print a fully qualified name, such as
--   `NatPlayground.Nat.mul_zero`;

-- - display universally quantified variables as binders before
--   the colon.

-- Thus,

--   mul_zero : ∀ (n : Nat), n * zero = zero

-- may be displayed as:

--   mul_zero (n : Nat) : n * zero = zero

-- The second form is the conventional *declaration-header
-- style* in Lean.

-- ## Proof by Case Analysis

-- Sometimes simple calculation and rewriting are not enough...

sf_expect_failure
  example (n : Nat) : (succ n == zero) = false := by
    intro n
    /-
      We can't rewrite by any lemmas here because `n` is unknown!
    -/

-- We can use `cases` to perform case analysis:

theorem add_one_neb_zero (n : Nat) : (succ n == zero) = false := by
  cases n with
  | zero =>
    rewrite [succ_zero_beq_false]
    rfl
  | succ n' =>
    rewrite [succ_zero_beq_false]
    rfl

-- Another example, using booleans:

theorem not_involutive (b : Bool) : (!!b) = b := by
  cases b with
  | false =>
    rewrite [Bool.not_false, Bool.not_true]
    rfl
  | true =>
    rewrite [Bool.not_true, Bool.not_false]
    rfl

-- Some of the above proofs use standard library lemmas; later
-- on we will discuss how to search for those yourself.

-- We can also have nested case analysis:

theorem and_commutative (b c : Bool) :
    (b && c) = (c && b) := by
  cases b with
  | true =>
    cases c with
    | true =>
      rewrite [Bool.and_self]
      rfl
    | false =>
      rewrite [Bool.and_false, Bool.and_true]
      rfl
  | false =>
    cases c with
    | true =>
      rewrite [Bool.and_true, Bool.and_false]
      rfl
    | false =>
      rewrite [Bool.and_self]
      rfl

theorem and3_exchange (b c d : Bool) :
    ((b && c) && d) = ((b && d) && c) := by
  cases b with
  | false =>
    cases c with
    | true =>
      cases d with
      | false =>
        rewrite [Bool.and_true, Bool.and_self]
        rfl
      | true =>
        rewrite [Bool.and_true]
        rfl
    | false =>
      cases d with
      | false =>
        rewrite [Bool.and_self]
        rfl
      | true =>
        rewrite [Bool.and_self, Bool.and_true]
        rfl
  | true =>
    cases c with
    | true =>
      cases d with
      | false =>
        rewrite [Bool.and_self, Bool.and_false, Bool.and_true]
        rfl
      | true =>
        rewrite [Bool.and_self]
        rfl
    | false =>
      cases d with
      | false =>
        rewrite [Bool.and_false]
        rfl
      | true =>
        rewrite [Bool.and_false, Bool.and_true, Bool.and_self]
        rfl

-- As you can see, proofs by cases can become very verbose. We
-- will introduce some tactics for writing shorter proofs by
-- case analysis in `Tactics.lean`.

-- ### New Tactics: `rewrite ... at` and `exact`

-- You will need the `rewrite ... at` and `exact` tactics to
-- complete the following exercises.

-- ### Exercise (2 stars): or_false_true ⭐⭐

-- Prove the following claim.

-- Tip: the rewrite rule to simplify `(b || false)` is called
-- `Bool.or_false`.

theorem or_false_true (b : Bool) :
    (b || false) = true → b = true := by
  sorry

-- ### Exercise (1 star): zero_nbeq_add_1 ⭐

theorem zero_neb_add_one (n : Nat) :
  (zero == succ n) = false := by
  sorry

-- Note to developers (Daniel Sainati  @dsainati1):
--     I move that we just cut this section entirely and come
--     back to it when we've presented enough of the requisite
--     material that we can actually explain

-- Note to developers (Michael Hicks  @mwhicks1, before next release):
--     I'm going to leave this here for now, but perhaps make a
--     note to fix later on---when you've fixed it, come back
--     and delete this, rather than delete it now.

-- Note to developers (Yipeng Liu  @berberman, before next release):
--     I feel we could split this section and push the
--     typeclass stuff to `Typeclasses` chapter and complex
--     notation syntax definitions to TS/HL.

-- ### More on Notation (Optional)

-- Lean has commands like `notation`, `infixl`, `infixr`,
-- `prefix`, and `postfix` for defining new notation.

-- ### Structural Recursion (Optional)

-- ### Exercise (2 stars): decreasing ⭐⭐

-- To get a concrete sense of how termination checking works in
-- Lean, find a way to write a sensible recursive definition
-- (of a simple function on numbers, say) that does actually
-- terminate on all inputs, but that Lean will reject because
-- it cannot automatically prove termination.

-- ### Binary Numerals

-- ### Exercise (3 stars): binary ⭐⭐⭐

-- We can generalize our unary representation of natural
-- numbers to the more efficient binary representation by
-- treating a binary number as a sequence of constructors `b0`
-- and `b1` (representing 0s and 1s), terminated by a `z`.

-- For example:

-- decimal                binary   unary
--       0                     z   zero
--       1                  b1 z   succ zero
--       2             b0 (b1 z)   succ (succ zero)
--       3             b1 (b1 z)   succ (succ (succ zero))
--       4        b0 (b0 (b1 z))   succ (succ (succ (succ zero)))
--       5        b1 (b0 (b1 z))   succ (succ (succ (succ (succ zero))))
--       6        b0 (b1 (b1 z))   succ (succ (succ (succ (succ (succ zero)))))
--       7        b1 (b1 (b1 z))   succ (succ (succ (succ (succ (succ (succ zero))))))
--       8   b0 (b0 (b0 (b1 z)))   succ (succ (succ (succ (succ (succ (succ (succ zero)))))))

-- Note that the low-order bit is on the left and the
-- high-order bit is on the right — the opposite of the way
-- binary numbers are usually written. This choice makes them
-- easier to manipulate.

-- (Comprehension check: What unary numeral does `b0 z`
-- represent?)

inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

attribute [pp_nodot] Bin.b1 Bin.b0

def incr (m : Bin) : Bin
  := sorry

def binToNat (m : Bin) : Nat
  := sorry

example : incr (.b1 .z) = .b0 (.b1 .z) := sorry
example : incr (.b0 (.b1 .z)) = .b1 (.b1 .z) := sorry
example : incr (.b1 (.b1 .z)) = .b0 (.b0 (.b1 .z)) := sorry

theorem incr_z : incr .z = .b1 .z := sorry
theorem incr_b0 (m : Bin) : incr (.b0 m) = .b1 m := sorry
theorem incr_b1 (m : Bin) : incr (.b1 m) = .b0 (incr m) := sorry

theorem binToNat_z : binToNat .z = zero := sorry
theorem binToNat_b0 (m : Bin) : binToNat (.b0 m) = binToNat m * two := sorry
theorem binToNat_b1 (m : Bin) : binToNat (.b1 m) = binToNat m * two + one := sorry

-- You may find your previous proofs of `zero_add_one`,
-- `one_add_one`, `zero_mul_two`, `one_mul_two`, and
-- `two_mul_two` useful here.

example : binToNat (.b0 (.b1 .z)) = two := sorry
example : binToNat (incr (.b1 .z)) = add one (binToNat (.b1 .z)) := sorry
example : binToNat (incr (incr (.b1 .z))) = add two (binToNat (.b1 .z)) := sorry
example : binToNat (.b0 (.b0 (.b1 .z))) = four := sorry

attribute [irreducible] incr binToNat

end Nat

-- ## More Exercises

-- ### Warmups

-- ### Exercise (1 star): identity_fn_applied_twice ⭐

-- You now have a small but rather powerful suite of tactics at
-- your disposal. As a warmup for the last section of the
-- chapter, use the tactics you have learned so far to prove
-- the following theorem about boolean functions.

-- Hint: You can use `rewrite` with *any* hypothesis that has
-- an `=` in it as long as the types line up.

theorem identity_fn_applied_twice (f : Bool → Bool) :
    (∀ x : Bool, f x = x) →
    ∀ b : Bool, f (f b) = b := by
  sorry

-- ### Exercise (1 star): negation_fn_applied_twice ⭐

-- Now state and prove a theorem `negation_fn_applied_twice`
-- similar to the previous one but where the hypothesis says
-- that the function `f` has the property that `f x = !x`.

-- FILL IN HERE

-- ### Exercise (3 stars): and_eq_or ⭐⭐⭐

-- Prove the following theorem.

theorem and_eq_or (b c : Bool) : (b && c) = (b || c) → b = c := by
  sorry

-- ### Course Late Policies, Formalized

-- Note to developers:
--     This exercise needs to be changed. Per GitHub
--     discussion: the way this exercise is currently
--     structured is at odds with our definition of Nats (use
--     of large digits that would be tedious to work with by
--     rewriting). The definitions of grades and letters also
--     do not lend themselves well to our discipline of
--     defining and using rewrite rules for all our functions,
--     as they would require a frustrating number of such
--     rules. We should come up with a new exercise here of
--     similar size and difficulty, but that works better with
--     the new presentation style of this material. HG: Also,
--     we should make sure that this reads OK in full/terse
--     TODO

namespace LateDays
open scoped NatPlayground.Nat

-- Numeric literals (`9`, `17`, `21`) for our unary `Nat`.
@[reducible] def ofNat : _root_.Nat → Nat
  | .zero => .zero
  | .succ n => .succ (ofNat n)

instance (n : _root_.Nat) : OfNat Nat n := ⟨ofNat n⟩

inductive Letter : Type where
  | A | B | C | D | F

inductive Modifier : Type where
  | plus | natural | minus

structure Grade where
  letter : Letter
  modifier : Modifier

inductive Comparison : Type where
  | eq   -- "equal"
  | lt   -- "less than"
  | gt   -- "greater than"

open Letter Modifier Comparison

def letterComparison (l1 l2 : Letter) : Comparison :=
  match l1, l2 with
  | A, A => eq
  | A, _ => gt
  | B, A => lt
  | B, B => eq
  | B, _ => gt
  | C, A => lt
  | C, B => lt
  | C, C => eq
  | C, _ => gt
  | D, F => gt
  | D, D => eq
  | D, _ => lt
  | F, F => eq
  | F, _ => lt

example : letterComparison B A = lt := by rfl
example : letterComparison D D = eq := by rfl
example : letterComparison B F = gt := by rfl

-- ### Exercise (1 star): letter_comparison ⭐

theorem letterComparison_Eq : ∀ l : Letter,
    letterComparison l l = eq := by
  sorry

def modifierComparison (m1 m2 : Modifier) : Comparison :=
  match m1, m2 with
  | plus, plus => eq
  | plus, _ => gt
  | natural, plus => lt
  | natural, natural => eq
  | natural, _ => gt
  | minus, minus => eq
  | minus, _ => lt

-- ### Exercise (2 stars): grade_comparison ⭐⭐

-- Here, we will need to access the fields of the `Grade`
-- structure. The field names are `letter` and `modifier`, so
-- for a grade `g`, we can write `g.letter` and `g.modifier` to
-- access these fields.

def gradeComparison (g1 g2 : Grade) : Comparison
  := sorry

example : gradeComparison ⟨A, minus⟩ ⟨B, plus⟩ = gt := sorry
example : gradeComparison ⟨A, minus⟩ ⟨A, plus⟩ = lt := sorry
example : gradeComparison ⟨F, plus⟩ ⟨F, plus⟩ = eq := sorry
example : gradeComparison ⟨B, minus⟩ ⟨C, plus⟩ = gt := sorry

def lowerLetter (l : Letter) : Letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F  -- Can't go lower than F!

theorem lowerLetter_F_is_F : lowerLetter F = F := by rfl

-- ### Exercise (2 stars): lower_letter_lowers ⭐⭐

theorem lowerLetter_lowers : ∀ l : Letter,
    letterComparison F l = lt →
    letterComparison (lowerLetter l) l = lt := by
  sorry

-- ### Exercise (2 stars): lower_grade ⭐⭐

-- In addition to the dot notation for accessing structure
-- fields, we can also use pattern matching to access these
-- fields. For example, if `g` is a grade, then we can write
-- `match g with ⟨l, m⟩ => ...` to access the letter and
-- modifier components of `g` as `l` and `m`, respectively.
-- Note: The angle brackets `⟨` and `⟩` are typed as `\<` and
-- `\>`.

def lowerGrade (g : Grade) : Grade
  := sorry

example : lowerGrade ⟨A, plus⟩ = ⟨A, natural⟩ := sorry
example : lowerGrade ⟨A, natural⟩ = ⟨A, minus⟩ := sorry
example : lowerGrade ⟨A, minus⟩ = ⟨B, plus⟩ := sorry
example : lowerGrade ⟨B, plus⟩ = ⟨B, natural⟩ := sorry
example : lowerGrade ⟨F, natural⟩ = ⟨F, minus⟩ := sorry
example : lowerGrade (lowerGrade ⟨B, minus⟩) = ⟨C, natural⟩ := sorry
example : lowerGrade (lowerGrade (lowerGrade ⟨B, minus⟩)) = ⟨C, minus⟩ := sorry

theorem lowerGrade_F_Minus : lowerGrade ⟨F, minus⟩ = ⟨F, minus⟩ := sorry

-- ### Exercise (3 stars): lower_grade_lowers ⭐⭐⭐

-- Note to developers:
--     For our solution we use:
--
--     - Working on multiple match cases with
--       `| _ ... | _ => ...`;
--
--     - Working on all remaining goals with `all_goals`.
--
--     - These are not expected of students at this point.

theorem lowerGrade_lowers : ∀ g : Grade,
    gradeComparison ⟨F, minus⟩ g = lt →
    gradeComparison (lowerGrade g) g = lt := by
  sorry

-- Note to developers (Roger Burtonpatel  @rogerburtonpatel):
--     in removing `dsimp` from these proofs, I found that you
--     might need the `contradiction` tactic here instead, or
--     some other reasoning that's not accomplishable with the
--     tactics we've introduced so far. Can you make this proof
--     work with only `rw`, `rfl`, `exact`, etc?

def applyLatePolicy (lateDays : NatPlayground.Nat) (g : Grade) : Grade :=
  if Nat.ble lateDays  9 then g
  else if Nat.ble lateDays 17 then lowerGrade g
  else if Nat.ble lateDays 21 then lowerGrade (lowerGrade g)
  else lowerGrade (lowerGrade (lowerGrade g))

theorem applyLatePolicy_unfold : ∀ (lateDays : NatPlayground.Nat) (g : Grade),
    applyLatePolicy lateDays g
    =
    (if Nat.ble lateDays 9 then g
     else if Nat.ble lateDays 17 then lowerGrade g
     else if Nat.ble lateDays 21 then lowerGrade (lowerGrade g)
     else lowerGrade (lowerGrade (lowerGrade g))) := by
  intro _ _; rfl

-- ### Exercise (2 stars): no_penalty_for_mostly_on_time ⭐⭐

theorem no_penalty_for_mostly_on_time : ∀ (lateDays : NatPlayground.Nat) (g : Grade),
    (Nat.ble lateDays 9 = true) →
    applyLatePolicy lateDays g = g := by
  sorry

-- ### Exercise (2 stars): grade_lowered_once ⭐⭐

theorem grade_lowered_once : ∀ (lateDays : NatPlayground.Nat) (g : Grade),
    (Nat.ble lateDays 9 = false) →
    (Nat.ble lateDays 17 = true) →
    applyLatePolicy lateDays g = lowerGrade g := by
  sorry

end LateDays

-- Note to developers (Roger Burtonpatel  @rogerburtonpatel):
--     If we are to have this exercise, we must either make the
--     functions irreducible or teach about `rw` of a reducible
--     definition. We also have to figure out how to make
--     lowerGrade_lowers go through without `dsimp` or
--     `contradiction`. To discuss.


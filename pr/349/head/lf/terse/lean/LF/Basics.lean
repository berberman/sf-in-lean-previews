import SFLCompat

--  # Basics: Functional Programming in Lean

--  This chapter introduces some of Lean's most essential
--  features for writing functional programs and proving
--  things about how they behave.

--  ## Introduction

--  ## Data and Functions

--  In Lean, we can build practically everything from first
--  principles using *inductive definitions*.

--  ### Days of the Week (Enumerated Types)

--  An inductive definition for an *enumerated type*:

inductive Day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

--  A function on days:

def nextWorkingDay (d : Day) : Day :=
  match d with
  | Day.monday    => Day.tuesday
  | Day.tuesday   => Day.wednesday
  | Day.wednesday => Day.thursday
  | Day.thursday  => Day.friday
  | Day.friday    => Day.monday
  | Day.saturday  => Day.monday
  | Day.sunday    => Day.monday

--  Evaluation:

#eval nextWorkingDay Day.friday

--  Output:
--    Day.monday

#eval nextWorkingDay (nextWorkingDay Day.saturday)

--  Output:
--    Day.tuesday

--  We can also record what we *expect* the result of
--  calling a function to be in the form of a Lean
--  `example`:

example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
  rfl

--  The `rfl` tactic is used to observe that both sides of
--  an equal sign evaluate to the same value.

--  ### Booleans

--  Another familiar enumerated type; we'll switch to Lean's
--  built-in `Bool` later:

inductive MyBool : Type where
  | true
  | false

--  THE FOLLOWING DETAILS CAN BE SKIPPED
variable (b : MyBool) (n m : Nat)
set_option pp.fieldNotation false
--  END DETAILS

--  This command opens the namespace associated with the
--  `MyBool` type:

namespace MyBool

--  Functions over booleans can be defined in the same way
--  as functions over days of the week.

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

--  Note the syntax for defining multi-argument functions
--  (`and` and `or`).

example : or MyBool.true  MyBool.false = MyBool.true  := by rfl
example : or MyBool.false MyBool.false = MyBool.false := by rfl
example : or MyBool.false MyBool.true  = MyBool.true  := by rfl
example : or MyBool.true  MyBool.true  = MyBool.true  := by rfl

--  Lean also allows us to define symbolic notations for
--  these functions.

local prefix:40 (priority := high) "!" => not
local infixl:35 (priority := high) " && " => and
local infixl:30 (priority := high) " || " => or

example :
    (MyBool.false || MyBool.false || MyBool.true) = MyBool.true := by rfl

example : (!MyBool.false) = MyBool.true := by rfl

--  ### Exercise (1 star): nand ⭐

--  The `sorry` keyword is a placeholder for an incomplete
--  proof or definition. We use it in exercises to indicate
--  the parts that we're leaving for you — i.e., your job is
--  to replace `sorry` with real definitions and proofs.
--
--  Remove `sorry` below and complete the definition of the
--  function. The function should return `MyBool.true` if
--  either or both of its inputs are `MyBool.false`. Make
--  sure that the `example` assertions below can be verified
--  by Lean.

def nand (b1 : MyBool) (b2 : MyBool) : MyBool
  := sorry

theorem nand_test1 : nand MyBool.true  MyBool.false = MyBool.true  := sorry
theorem nand_test2 : nand MyBool.false MyBool.false = MyBool.true  := sorry
theorem nand_test3 : nand MyBool.false MyBool.true  = MyBool.true  := sorry
theorem nand_test4 : nand MyBool.true  MyBool.true  = MyBool.false := sorry

--  Going forward, most exercises will be omitted from the
--  "terse" version of the notes used in lecture. The "full"
--  version (used online and for homeworks) contains both
--  longer explanations and all the exercises.

--  ## A First Taste of Proofs

--  Let's prove something simple about booleans:

theorem true_and : ∀ (b : MyBool), (MyBool.true && b) = b := by
  intro b
  rfl

--  And now let's see it in a bit more detail:

theorem true_and_explained : ∀ (b : MyBool), (MyBool.true && b) = b := by
  /- Move your cursor (click) here to see the initial proof state in
     the InfoView. If you are viewing the book online,
     click instead on the white button after `by`.
     The context (before the ⊢) is empty.
     The goal is `∀ (b : MyBool), (MyBool.true && b) = b`. -/
  intro b
  /- Now click here (or the white button after `intro b`)
     to see the new proof state that results from the
     tactic. Notice how `intro b` has changed the _context_: it now
     contains `b : MyBool`.

    The `intro` tactic is used to name variables quantified by a `∀`.
    Since we are trying to prove a property of all `MyBool`s, we
    proceed by introducing an unknown `MyBool` `b` and proving
    the property holds for this particular `b`.  Informally,
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
    which may not appear to be "true by reflexivity", since the two
    sides of the equality are not textually identical. However, the tactic
    _evaluates_ both sides of the equality before comparing them. In
    this case, if we look at the definition of `and`, we can see that,
    when its first argument is `MyBool.true`, the result is its second
    argument. So the two terms `MyBool.true && b` and `b` are in fact
    equal because one evaluates to the other.
  -/
  rfl
  /- The proof is now done! The Lean InfoView tells us there are "No goals". -/

--  Now we'll switch to Lean's definition of booleans.

end MyBool

--  ### Types

--  We can use `#check` to check the type of an expression:

#check Bool.true

--  Output:
--    Bool.true : Bool

#check (Bool.true : Bool)
#check (Bool.not Bool.true : Bool)

--  Output:
--    true : Bool

--  Output:
--    !true : Bool

#check Bool.not

--  ### New Types from Old

--  A more interesting type definition:

inductive RGB : Type where
  | red
  | green
  | blue

inductive Color : Type where
  | black
  | white
  | primary (p : RGB)

--  We can define functions on colors using pattern
--  matching, just as we did for `Day` and `MyBool`.

def monochrome (c : Color) : Bool :=
  match c with
  | Color.black => Bool.true
  | Color.white => Bool.true
  | Color.primary p => Bool.false

--  We can use a *wildcard* pattern `_` to match something
--  we don't care about:

def monochrome' (c : Color) : Bool :=
  match c with
  | Color.black => Bool.true
  | Color.white => Bool.true
  | Color.primary _ => Bool.false

--  We can use a constant argument to `Color.primary` to
--  match a specific primary color:

def isRed (c : Color) : Bool :=
  match c with
  | Color.black => Bool.false
  | Color.white => Bool.false
  | Color.primary RGB.red => Bool.true
  | Color.primary _ => Bool.false

--  An alternative way to write the same function would be
--  to explicitly nest match statements:

def isRed' (c : Color) : Bool :=
  match c with
  | Color.black => Bool.false
  | Color.white => Bool.false
  | Color.primary r =>
    match r with
    | RGB.red => Bool.true
    | _ => Bool.false

--  This `isRed'` function produces the same result as
--  `isRed`. It also illustrates the *use* of a pattern
--  variable in the corresponding branch.

--  ### Namespaces

--  `namespace` declarations create separate namespaces.

def myFoo : Bool := true
namespace Playground
def myFoo : RGB := RGB.blue
end Playground

#check myFoo
#check Playground.myFoo

--  Output:
--    myFoo : Bool

--  Output:
--    Playground.myFoo : RGB

namespace Playground
def myBar : RGB := myFoo
end Playground

#check Playground.myBar

--  Output:
--    Playground.myBar : RGB

--  The names of an inductive type's constructors are
--  prefixed by the type's name.

namespace RGB
def myBlue : RGB := blue
end RGB

--  Top-level definitions can also be prefixed by a
--  namespace, which opens the namespace temporarily for the
--  body of the definition.

-- The following works because the definition is qualified by `RGB.`
def RGB.myOtherBlue : RGB := myBlue

#check RGB.myBlue
#check RGB.myOtherBlue

--  Output:
--    RGB.myBlue : RGB

--  Output:
--    RGB.myOtherBlue : RGB

sf_expect_failure_in
  -- This doesn't work: the identifier is undefined
  #check myBlue

--  Output:
--    Unknown identifier `myBlue`

def Day.nextWorkingDay' (d : Day) : Day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday

--  `open` brings definitions from a namespace into scope.

namespace MyNamespace
def myDef : Bool := Bool.true
end MyNamespace

open MyNamespace

#check myDef

--  Output:
--    MyNamespace.myDef : Bool

--  If we only want to bring *some*, rather than all, of the
--  definitions of a namespace into the current scope, we
--  can use the `open (...)` form:

namespace MyOtherNamespace
def myHiddenDef : Bool := Bool.true
def myVisibleDef : Bool := Bool.false
end MyOtherNamespace

open MyOtherNamespace (myVisibleDef)

-- `myVisibleDef` is now usable without qualification:
#check myVisibleDef

--  Output:
--    MyOtherNamespace.myVisibleDef : Bool

--  But `myHiddenDef`, which we did not include in the
--  `open`, still needs to be qualified:

sf_expect_failure_in
  #check myHiddenDef

--  Output:
--    Unknown identifier `myHiddenDef`

--  Lean's prelude exports common names from the `Bool`
--  `namespace`.

#check Bool.true
#check true

--  Output:
--    Bool.true : Bool

--  Output:
--    Bool.true : Bool

--  Lean can often use the expected type to resolve a name
--  beginning with `.`:

def nextWorkingDay' (d : Day) : Day :=
  match d with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday

--  Here, Lean can't figure out which version of `.true` we
--  mean.

sf_expect_failure_in
  #check .true

--  Output:
--    Invalid dotted identifier notation: The expected type of `.true` could not be determined
--
--    Hint: Using one of these would be unambiguous:
--      [apply] `true`
--      [apply] `MyBool.true`
--      [apply] `Lake.Toml.true`
--      [apply] `Lean.LBool.true`
--      [apply] `Std.Do.ExceptConds.true`
--      [apply] `Lean.Meta.Grind.Filter.true`

--  But in the following example, because `Bool.not` takes a
--  `Bool` argument, Lean knows that `.true` must here be a
--  `Bool`:

#check (Bool.not .true)

--  Output:
--    !true : Bool

--  ### Constructors with Multiple Parameters (Tuple Types)

namespace Playground

--  A `Nibble` is half a byte — four bits.

inductive Bit : Type where
  | b1
  | b0

inductive Nibble : Type where
  | bits (x0 x1 x2 x3 : Bit)

#check Nibble.bits .b1 .b0 .b1 .b0

--  Output:
--    Nibble.bits Bit.b1 Bit.b0 Bit.b1 Bit.b0 : Nibble

--  We can deconstruct a Nibble by pattern matching.

def allZero (nb : Nibble) : Bool :=
  match nb with
  | .bits .b0 .b0 .b0 .b0 => true
  | .bits _   _   _   _   => false

example : allZero (.bits .b1 .b0 .b1 .b0) = false := by rfl
example : allZero (.bits .b0 .b0 .b0 .b0) = true  := by rfl

end Playground

--  An inductive type with just one constructor can
--  alternatively be defined as a `structure`, an analog of
--  a record type in other programming languages.

structure NibbleStruct : Type where
  x0 : Playground.Bit
  x1 : Playground.Bit
  x2 : Playground.Bit
  x3 : Playground.Bit

#check NibbleStruct.mk .b0 .b0 .b0 .b0

--  Output:
--    { x0 := Playground.Bit.b0, x1 := Playground.Bit.b0, x2 := Playground.Bit.b0, x3 := Playground.Bit.b0 } : NibbleStruct

--  The `.mk` constructor is created for us.

def zeroNibble : NibbleStruct := {
    x0 := .b0
    x1 := .b0
    x2 := .b0
    x3 := .b0
  }

--  We can "update" a structure like this:

def setFirstTwoBits (old : NibbleStruct)
    (newX0 : Playground.Bit)
    (newX1 : Playground.Bit) : NibbleStruct :=
  { old with x0 := newX0, x1 := newX1 }

--  When variables and field names match, construction is
--  easier.

def makeNibbleStruct (x0 x1 x2 x3 : Playground.Bit) : NibbleStruct :=
  { x0, x1, x2, x3 }

--  ### Natural Numbers

namespace NatPlayground

--  For simplicity in proofs, we choose a *unary*
--  representation of natural numbers.

inductive Nat : Type where
  | zero
  | succ (n : Nat)

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Library Nat to SFL Nat coercion)
def ofNat : _root_.Nat → Nat
  | .zero => .zero
  | .succ n => .succ (ofNat n)

instance (n : _root_.Nat) : OfNat Nat n := ⟨ofNat n⟩
attribute [pp_nodot] Nat.succ
--  END DETAILS

--  Eventually we'll swap to Lean's definition of natural
--  numbers, which is very similar to this.

namespace Nat

def one   : Nat := succ zero
def two   : Nat := succ one
def three : Nat := succ two
def four  : Nat := succ three

--  We can also write functions on `Nat`.

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

--  Look at the types of `succ`, `pred`, and `minusTwo`:

#check (succ)
#check (pred)
#check (minusTwo)

--  Output:
--    succ : Nat → Nat

--  Output:
--    pred : Nat → Nat

--  Output:
--    minusTwo : Nat → Nat

--  These are all things that can be applied to a number to
--  yield a number. But there is a difference between `succ`
--  and the other two.

--  Here are some recursive functions on natural numbers:

def even (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even n'

example : even one = false := by rfl
example : even four = true := by rfl

--  We could define `odd` by a similar recursive
--  declaration, but here is a simpler way:

def odd (n : Nat) : Bool :=
  not (even n)

example : odd one = true := by rfl
example : odd four = false := by rfl

--  This function takes multiple parameters, recursing on
--  the second:

def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

#eval add one two -- succ (succ (succ zero)) -- aka, three!

--  Output:
--    NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero)))

--  We can also define infix notation for our `add`
--  function.

scoped infixl:65 " + " => add

#eval one + two -- succ (succ (succ zero)) -- aka, three again.

--  Output:
--    NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero)))

--  ## Proof by Rewriting

--  ### Proving Properties about Functions in Lean

--  We can prove properties of recursive functions like
--  `add`:

theorem add_zero : ∀ n : Nat, n + zero = n := by
  intro n
  rfl

#check add_zero

--  Output:
--    NatPlayground.Nat.add_zero (n : Nat) : n + zero = n

--  Using our simplification rule `add_zero`, we can carry
--  out a simple proof about natural numbers.

theorem add_zero_zero : ∀ n : Nat, n + zero + zero = n := by
  intro n
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

--  Here is the previous proof in more detail:

theorem add_zero_zero_explained : ∀ n : Nat, n + zero + zero = n := by
  intro n
  /- After introducing `n`, our goal is `n + zero + zero = n`.
     What can we do to simplify this expression? If you hover
     your cursor over the `add_zero` in the rewrite below, you
     can see its type: `n + zero = n`. So, we can use that
     simplification rule to transform an appearance of `n + zero`
     in the goal to `n`. -/
  rewrite [add_zero]
  /- Now click here to see the new proof state that results
     from the tactic. Notice how `n + zero + zero` changes to
     `n + zero` in the goal. -/
  rewrite [add_zero]
  /- Again the goal changes, from `n + zero` to `n`. Now the
     proof state is an equality with both sides equal, so it
     can be closed by the tactic `rfl`. -/
  rfl
  /- The proof is now done! The Lean InfoView tells us there are
     "No goals". -/

--  Give this proof a try (it's similar):

theorem add_zero_zero_zero : ∀ n : Nat, n + zero + zero + zero = n := by
  sorry

--  The `rfl` closes a goal that looks like `a = a`,
--  reducing both sides of the equality in the process.

--  ### A New `add` Rule

--  Here's another rule we can use for `add`:

theorem add_succ : ∀ n m : Nat, n + (succ m) = succ (n + m) := by
  intro n m
  rfl

--  Now, let's use `add_succ` in a proof:

theorem add_one (n : Nat) : n + (succ zero) = succ n + zero := by
  rewrite [add_succ]
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

--  ### Irreducibility, Rewriting, and Proof Engineering

--  After proving the theorems that characterize a
--  definition, we mark the definition `irreducible` to
--  require rewriting by them instead of using `rfl`.

attribute [irreducible] add

--  These simplification rules also follow a particular
--  pattern. Let's look again at the definition of `add`,
--  without the `+` notation for maximum clarity:

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

--  Each branch of a definition's control flow gets one
--  simplification rule. Here are the two for `pred`:

theorem pred_zero : pred zero = zero := by rfl
theorem pred_succ (n : Nat) : pred (succ n) = n := by rfl

--  Now that we have defined and proved `pred`'s
--  simplification rules, we can mark it `irreducible` to
--  enforce rewriting by these lemmas.

attribute [irreducible] pred

--  Similarly, for each of the three branches of the
--  definition of `even`, we need one simplification rule:

theorem even_zero : even zero = true := rfl
theorem even_one : even (succ zero) = false := rfl
theorem even_succ_succ (n : Nat) : even (succ (succ n)) = even n := rfl

attribute [irreducible] even odd

--  From here on, we pair each definition with its
--  simplification rules and rewrite by those rules rather
--  than `rfl`-ing through the definition.

--  ### Working with Numerals

--  We know from our definitions above that `one` is just
--  `succ zero`, `two` is `succ one`, and so on. We can
--  write rules for these equalities too:

theorem one_eq_succ_zero : one = succ zero := by rfl
theorem two_eq_succ_one : two = succ one := by rfl
theorem three_eq_succ_two : three = succ two := by rfl
theorem four_eq_succ_three : four = succ three := by rfl

--  #### Multiplication

def mul (n m : Nat) : Nat :=
  match m with
  | zero => zero
  | succ m' => (mul n m') + n

scoped infixl:70 " * " => mul

--  ### Exercise (1 star): mul_simpl_rules ⭐

--  Multiplication, like any function we will prove
--  properties about, also has simplification rules.
--
--  Remove `sorry` and prove the simplification rules for
--  `mul` below. You will likely find the proofs of the
--  simplification rules for `add` to be helpful as a model.

theorem mul_zero : ∀ n : Nat, n * zero = zero := by
  sorry

theorem mul_succ : ∀ n m : Nat, n * (succ m) = (n * m) + n := by
  sorry

attribute [irreducible] mul

--  Prove this theorem using rewriting with the
--  simplification rules.

theorem zero_add_one : (zero + one : Nat) = one := by
  rewrite [one_eq_succ_zero]
  sorry

--  #### Equality and Ordering

--  Here is a function `beq` that tests natural numbers for
--  equality, yielding a boolean.

def beq (n m : Nat) : Bool :=
  match n with
  | zero => match m with
            | zero => true
            | succ _ => false
  | succ n' => match m with
               | zero => false
               | succ m' => beq n' m'

--  We could also write this by pattern matching on both `n`
--  and `m` at the same time:

def beq' (n m : Nat) : Bool :=
  match n, m with
  | zero, zero => true
  | zero, succ _ => false
  | succ _, zero => false
  | succ n', succ m' => beq n' m'

--  The definitions of `beq` and `beq'` are equivalent.

--  Similarly, the `ble` function tests whether its first
--  argument is less than or equal to its second argument,
--  yielding a boolean.

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

--  We'll be using `beq` a lot, so let's give it an infix
--  notation.

scoped infixl:30 " == " => beq

--  Note that `==` and `=` are different; the former means
--  `beq` whereas the latter is a logical claim. Here are
--  our simplification rules.

theorem zero_beq_zero : (zero == zero) = true := by rfl
theorem zero_beq_succ (n : Nat) : (zero == (succ n)) = false := by rfl
theorem succ_beq_zero (n : Nat) : ((succ n) == zero) = false := by rfl
theorem succ_beq_succ (n m : Nat) : ((succ n) == (succ m)) = (n == m) := by rfl

attribute [irreducible] beq

--  ### General Proofs about Natural Numbers

--  A (slightly) more interesting theorem:

theorem add_id_example : ∀ n m : Nat,
    n = m → n + n = m + m := by
  intro n m
  intro h
  rewrite [h]
  rfl

--  #### Displaying Theorem Statements

--  The `#check` command can also be used to examine the
--  statements of previously declared lemmas and theorems.

#check mul_zero
#check mul_succ

--  Output:
--    NatPlayground.Nat.mul_zero (n : Nat) : n * zero = zero

--  Output:
--    NatPlayground.Nat.mul_succ (n m : Nat) : n * succ m = n * m + n

--  Lean displays universally quantified variables as
--  binders before the colon, which is the preferred
--  *declaration-header style* in Lean.

--  ## Proof by Case Analysis

--  Sometimes simple calculation and rewriting are not
--  enough...

sf_expect_failure_in
  example (n : Nat) : (succ zero + n == zero) = false := by
    /-
      We can't rewrite by any lemmas here: `add`'s definition matches on its
      *second* argument, and here that argument is the unknown `n`!
    -/

--  We can use `cases` to perform case analysis:

theorem add_one_neb_zero (n : Nat) : (succ zero + n == zero) = false := by
  cases n with
  | zero =>
    rewrite [add_zero, succ_beq_zero]
    rfl
  | succ n' =>
    rewrite [add_succ, succ_beq_zero]
    rfl

--  Another example, using booleans:

theorem not_involutive (b : Bool) : (!!b) = b := by
  cases b with
  | false =>
    rewrite [Bool.not_false, Bool.not_true]
    rfl
  | true =>
    rewrite [Bool.not_true, Bool.not_false]
    rfl

--  Some of the above proofs use standard library lemmas;
--  later on we will discuss how to search for them
--  yourself.

--  We can also have nested case analysis:

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

--  As you can see, proofs by cases can become very verbose.
--  We will introduce some tactics for writing shorter
--  proofs by case analysis in the Tactics chapter.

--  You will need the `rewrite ... at` and `exact` tactics
--  to complete some exercises.

end Nat

-- Built on 2026-09-01 20:50 UTC

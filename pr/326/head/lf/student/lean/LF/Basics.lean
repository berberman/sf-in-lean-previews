import SFLCompat

--  # Basics: Functional Programming in Lean

--  This chapter introduces some of Lean's most essential features for
--  writing functional programs and proving things about how they behave.

--  ## Introduction

--  The *functional style* of programming is founded on simple mathematical
--  intuitions: a program is essentially a concrete means for computing a
--  mathematical function, which just maps inputs to outputs. (Even
--  programs with side effects like reading and writing files or network
--  packets can be presented in this way, using ideas like *monads*.) This
--  connection between programs and mathematical functions makes it
--  possible to reason both precisely and formally about a program's
--  behavior, i.e., to *prove properties* about programs.
--
--  This functional style is one sense of the word "functional" in
--  "functional programming." The other sense is that it emphasizes the use
--  of functions as *first-class* values — i.e., values that can be passed
--  as arguments to other functions, returned as results, included in data
--  structures, etc. The recognition that functions can be treated as data
--  gives rise to a host of useful and powerful programming idioms.
--
--  Other common features of functional languages include *algebraic data
--  types* and *pattern matching*, which make it easy to construct and
--  manipulate rich data structures, and *polymorphic types* supporting
--  abstraction and code reuse. Lean offers all of these features, and we
--  will see them often in this book.
--
--  The first part of this chapter introduces some key elements of Lean's
--  functional programming language. The second part shows how to use
--  *tactics* to prove properties about programs.

--  ## Data and Functions

--  Lean's set of primitives is extremely small. For example, instead of
--  providing the usual palette of *atomic datatypes* — booleans, integers,
--  strings, and so on — Lean's standard library *defines* them, along with
--  an extensive collection of other common data structures — lists, hash
--  tables, etc., etc. It does so with a single powerful and general
--  mechanism: *inductive definitions*. A type introduced with an inductive
--  definition is called an *inductive type*, and the word "inductive"
--  hints at the use of mathematical induction to reason about its values
--  (as we will see in the next chapter).
--
--  To demonstrate how inductive definitions work and illustrate their
--  expressive power, we will start by defining most of the datatypes we
--  use in this course from scratch, rather than importing the ones in the
--  standard library. (We will later switch over to the library versions to
--  take advantage of all the properties that have already been proved
--  about them.)

--  ### Days of the Week (Enumerated Types)

--  Let's start with a very simple example. The following declaration tells
--  Lean to give a name to a set of data values, i.e., to define a *type*.

inductive Day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

--  The new type is called `Day`, and its members are `monday`, `tuesday`,
--  etc. These are also called the *constructors* of the `Day` type. We
--  often call this sort of inductive type an *enumerated type* since the
--  values belonging to the type are explicitly enumerated in its
--  definition.
--
--  Having defined `Day`, we can write Lean functions that operate on days.

def nextWorkingDay (d : Day) : Day :=
  match d with
  | Day.monday    => Day.tuesday
  | Day.tuesday   => Day.wednesday
  | Day.wednesday => Day.thursday
  | Day.thursday  => Day.friday
  | Day.friday    => Day.monday
  | Day.saturday  => Day.monday
  | Day.sunday    => Day.monday

--  Note that the argument and result types of this function are explicitly
--  declared on its first line. As in most functional programming
--  languages, Lean can often figure out these types for itself when they
--  are not given explicitly — i.e., it can do *type inference* — but we'll
--  generally include them to make reading easier.
--
--  The `match` on the second line is Lean's keyword for *pattern
--  matching*, the functional programming way of examining and making
--  decisions on data. To evaluate `match d with...`, Lean will examine the
--  structure of `d` to see which case to execute; if `d` is `Day.monday`,
--  for example, it will evaluate the first case of the `match` statement;
--  if `d` is `Day.friday`, it will evaluate the fifth case. (There is much
--  more to say about pattern matching! We'll introduce more of its
--  features as the need arises.)
--
--  You may notice that we *qualified* `Day`'s constructors when using
--  them, writing `Day.monday` instead of just `monday`, for example. Lean
--  places all constructors into a *namespace* associated with their type,
--  and generally requires those constructors to be prefixed with their
--  namespace when they are used, though we will see later that this
--  requirement can sometimes be relaxed.
--
--  If you ever need to know the type of *any* pattern, object, or
--  function, you can hover over it with your mouse, either in VS Code or
--  in the HTML version of the chapter.

--  Having defined a function, we should check that it works on some
--  examples. There are a few different ways to do this in Lean. One is to
--  use the `#eval` command to evaluate a compound expression involving
--  `nextWorkingDay`.

#eval nextWorkingDay Day.friday

--  Output:
--    Day.monday

#eval nextWorkingDay (nextWorkingDay Day.saturday)

--  Output:
--    Day.tuesday

--  We can also record what we *expect* the result of calling a function to
--  be in the form of a Lean `example`:

example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
  rfl

--  This declaration asserts that the second working day after `saturday`
--  is `tuesday`. Having made the assertion, we can also ask Lean to
--  *verify* it. The `by rfl` can be read as "The assertion we've just made
--  can be proved by observing that both sides of the equality evaluate to
--  the same term."
--
--  Here, `rfl` is pronounced "reflexivity," the principle that any value
--  is equal to itself. After evaluation, both sides of the equality are
--  the same value, so the assertion is true by reflexivity. If we had made
--  a different assertion, such as

sf_expect_failure_in
  example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.monday := by rfl

--  then Lean would not be able to verify it and would instead signal an
--  error.
--
--  (The `sf_expect_failure_in` annotation tells Lean that there is
--  intended to be an error in the following expression and it should not
--  mark the whole file as broken.)

--  ### Aside: Using the VS Code Lean Extension

--  If you have not already done so, this would be an excellent moment to
--  fire up VS Code with the [Lean
--  Extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
--  and load this file, `Basics.lean`, from the book's Lean sources. Locate
--  the above example and observe its result in the Lean InfoView panel.
--
--  This panel displays the results of commands like `#eval` (click on a
--  particular `#eval` to see), as well as the current goal state when you
--  are working on proofs. The InfoView content always follows your cursor.
--
--  On Windows and Linux, Ctrl-click a type or variable name to navigate to
--  its definition. On macOS, Command-click instead. Try this with the
--  mention of `nextWorkingDay` in the above `#eval`.
--
--  You can also hover over expressions in the source code to see their
--  types. Try this with mentions of `nextWorkingDay` and `Day.saturday` in
--  the above `#eval`. If you hover over the `#eval` command itself, you
--  will see the popup that contains its output (at the top). Sometimes we
--  show Lean's responses to commands in the text below them; by hovering
--  over the command, you can check against that text.
--
--  Experiment with adding your own `#eval` commands to test other inputs.
--  Lean typechecks the file as you edit it, so you can see the results of
--  your changes immediately.

--  ### Booleans

--  Following the pattern of the days of the week above, we can define the
--  standard type `Bool` of booleans by enumerating its members `true` and
--  `false`. We define our own `MyBool` to teach the concept of building
--  booleans from scratch. Our definition of `MyBool` is equivalent to
--  Lean's built-in `Bool`, which we'll switch to later. We call it
--  `MyBool` to avoid clashing with the built-in name. Later in the
--  chapter, we will show a different way of avoiding such clashes: we will
--  place our custom natural numbers in a fresh `NatPlayground` namespace,
--  where they can be called `Nat` without clashing with Lean's built-in
--  `Nat`.

inductive MyBool : Type where
  | true
  | false

--  We next invoke a couple of Lean directives to help control formatting.
--  Exactly what these directives mean is not important for present
--  purposes — you can understand everything in the rest of the book
--  without knowing — so we will mark these commands — and similar bits
--  later on — with `THE FOLLOWING DETAILS CAN BE SKIPPED` comments in
--  `.lean` files, and with folded-up segments in the HTML presentation.
--  Feel free to have a peek if you want (click on the triangle in the HTML
--  to unfold it), or just jump down to the following material and keep
--  going.

--  THE FOLLOWING DETAILS CAN BE SKIPPED
variable (b : MyBool) (n m : Nat)
set_option pp.fieldNotation false
--  END DETAILS

--  The next command opens the namespace associated with the `MyBool` type,
--  so subsequent definitions will be part of the `MyBool` namespace. In
--  Lean, functions on a type are typically defined in that type's
--  namespace, which avoids name clashes with functions of the same name
--  elsewhere (e.g., functions on the built-in `Bool` type). We give a full
--  treatment of namespaces below.

namespace MyBool

--  Functions over booleans can be defined in the same way as functions
--  over days of the week.

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

--  The `and` and `or` definitions illustrate Lean's syntax for
--  multi-argument functions. The corresponding multi-argument
--  function-application syntax is illustrated by the following tests,
--  which effectively constitute a complete specification — a truth table —
--  for the `or` function:

example : or MyBool.true  MyBool.false = MyBool.true  := by rfl
example : or MyBool.false MyBool.false = MyBool.false := by rfl
example : or MyBool.false MyBool.true  = MyBool.true  := by rfl
example : or MyBool.true  MyBool.true  = MyBool.true  := by rfl

--  Lean also allows us to define symbolic notations for these functions.

local prefix:40 (priority := high) "!" => not
local infixl:35 (priority := high) " && " => and
local infixl:30 (priority := high) " || " => or

example :
    (MyBool.false || MyBool.false || MyBool.true) = MyBool.true := by rfl

example : (!MyBool.false) = MyBool.true := by rfl

--  The technical details of how these symbolic notations work are not
--  something you need to understand until quite a bit later in your Lean
--  journey.

--  THE FOLLOWING DETAILS CAN BE SKIPPED
--  Lean has a very flexible notation system. Operators like `||` and `&&`
--  are defined with specified precedence and associativity. For example,
--  the `infixl` directive above states that `&&` is an infix operator, has
--  precedence 35, and is left-associative, while `||` is also infix and
--  left-associative and has precedence 30. This means that
--  `MyBool.true || MyBool.false && MyBool.false` is parsed as
--  `MyBool.true || (MyBool.false && MyBool.false)`.
--
--  Custom notations are defined using the `notation`, `infixl`, `infixr`,
--  `prefix`, and `postfix` commands, some of which we will see (again, in
--  skippable sections) later on.
--  END DETAILS

--  ### Exercise (1 star): nand ⭐

--  The `sorry` keyword is a placeholder for an incomplete proof or
--  definition. We use it in exercises to indicate the parts that we're
--  leaving for you — i.e., your job is to replace `sorry` with real
--  definitions and proofs.
--
--  Remove `sorry` below and complete the definition of the function. The
--  function should return `MyBool.true` if either or both of its inputs
--  are `MyBool.false`. Make sure that the `example` assertions below can
--  be verified by Lean.

def nand (b1 : MyBool) (b2 : MyBool) : MyBool
  := sorry

theorem nand_test1 : nand MyBool.true  MyBool.false = MyBool.true  := sorry
theorem nand_test2 : nand MyBool.false MyBool.false = MyBool.true  := sorry
theorem nand_test3 : nand MyBool.false MyBool.true  = MyBool.true  := sorry
theorem nand_test4 : nand MyBool.true  MyBool.true  = MyBool.false := sorry

--  ### Exercise (1 star): and3 ⭐

--  Do the same for the `and3` function below. This function should return
--  `MyBool.true` when all of its inputs are `MyBool.true`, and
--  `MyBool.false` otherwise.

def and3 (b1 : MyBool) (b2 : MyBool) (b3 : MyBool) : MyBool
  := sorry

theorem and3_test1 : and3 MyBool.true  MyBool.true  MyBool.true  = MyBool.true  := sorry
theorem and3_test2 : and3 MyBool.false MyBool.true  MyBool.true  = MyBool.false := sorry
theorem and3_test3 : and3 MyBool.true  MyBool.false MyBool.true  = MyBool.false := sorry
theorem and3_test4 : and3 MyBool.true  MyBool.true  MyBool.false = MyBool.false := sorry

--  ## A First Taste of Proofs

--  Now that we've defined some basic functions on booleans, let's see how
--  to *prove* some simple properties of those functions. Here is a simple
--  rule about `&&`:
--
--      For any boolean value b, (MyBool.true && b) = b
--
--  This is an example of a *proposition*, a logical claim that we can try
--  to prove. It says that `MyBool.true && b` is equal to `b` for every
--  `MyBool` `b`.
--
--  How do we write this proposition in Lean? Like this:
--
--      theorem true_and : ∀ (b : MyBool), (MyBool.true && b) = b
--
--  The keyword `theorem` indicates that we are stating (and eventually
--  proving) a proposition; the text after the first `:` is the proposition
--  we want to prove.
--
--  You'll notice that this proposition looks a lot like the informal one
--  we began with, with some additional symbols in front. The `∀` symbol,
--  pronounced "forall," is a *universal quantifier*: it "quantifies" the
--  variable `b` that appears in the proposition. Quantifying a variable
--  with a `∀` means that the proposition applies to all possible values of
--  its type; we annotate `b` with the type `MyBool` to signify that the
--  proposition holds for all `b`s of type `MyBool`.
--
--  Now that we've stated the theorem we'd like to prove, let's see the
--  proof.

theorem true_and : ∀ (b : MyBool), (MyBool.true && b) = b := by
  intro b
  rfl

--  What does this mean?
--
--  First, the `by` keyword signals that what follows is a sequence of
--  *tactics*. The `intro b` and `rfl` after the `by` are examples of
--  tactics. If you hover over a tactic's name, Lean shows its
--  documentation.
--
--  Tactics manipulate the *proof state*, which you can see in the Lean
--  InfoView panel. The proof state is divided by the symbol ⊢, pronounced
--  *turnstile*. The part before the turnstile is the *context*; the part
--  after it is the *goal*. The context records what we know — the current
--  assumptions — at some given point in the proof; the goal is what we are
--  trying to prove at that point.
--
--  Each tactic manipulates the goal, the context, or both to move things
--  toward a configuration that is closer to being "solved." A tactic can
--  also *close* (solve) the current goal, finishing its proof.
--
--  Let's walk through the example above with this terminology in mind.

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

--  Like some other well-known languages (Python, Haskell, etc.), Lean is
--  *whitespace-sensitive*. That is, the indentation in proofs is
--  important, and changing it can change the meaning of the proof, usually
--  causing it to break.
--
--  If we had written the following, we'd see an error:

sf_expect_failure_in
  theorem true_and_wrong : ∀ (b : MyBool), (MyBool.true && b) = b := by
    intro b
      rfl

--  To see the error message in the Lean file, change
--  `sf_expect_failure_in` to `sf_expect_failure_in?` temporarily. You
--  should see the following message.

--  Output:
--    Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
--
--    b : MyBool
--    ⊢ (true && b) = b

--  Lean complains because the `rfl` is not at the same level of
--  indentation as the `intro b`, so it does not recognize these two
--  tactics as being sequential in the way they should be.
--
--  In general, sequential tactics applied to the same goal must either be
--  on subsequent lines at the same level of indentation or else be
--  separated on the same line by a `;` like so:

theorem true_and' : ∀ (b : MyBool), (MyBool.true && b) = b := by
  intro b; rfl

--  ### Exercise (1 star): false_or_exercise ⭐

--  Here's a simple proof for you to try. Remove `sorry` and fill in the
--  proof.

theorem false_or : ∀ (b : MyBool), (MyBool.false || b) = b := by
  sorry

--  In this book we often use `sorry` as a placeholder for you to replace
--  with an actual proof. This tells Lean that we want to skip trying to
--  prove the theorem and just accept it as a given. This can be useful for
--  developing longer proofs.
--
--  Be careful, though: every time you say `sorry` you are leaving a door
--  open for total nonsense to enter Lean's safe, formally checked world!

sf_experiment
  theorem really_bad : MyBool.true = MyBool.false := by sorry

--  The facts we've seen so far about booleans are quite simple, so the
--  tactics we need to prove them are also quite simple. Over the course of
--  this book, we are going to introduce new tactics and proof techniques
--  gradually, enriching the propositions we can prove along the way.
--
--  Now that we've seen how to define our own booleans and prove some basic
--  properties about them, let's switch over to Lean's built-in `Bool`
--  type, which has the same structure but comes with a lot of useful
--  functions and lemmas.

end MyBool

--  ### Aside: Unicode in Lean

--  Note that `∀` and `⊢` are Unicode symbols, not plain ASCII characters.
--  The Lean Extension for VS Code provides convenient shortcuts for
--  entering such symbols. Simply type `\` (backslash) followed by the name
--  of the symbol (its "shortcode"), and the extension will automatically
--  replace it with the actual symbol. For example, typing either `\all` or
--  `\forall` will produce `∀`, and `\->` or `\to` will produce `→`. To
--  find out what backslash sequence produces a Unicode symbol that you can
--  see on the screen, just hover over it. To see a list of all of the
--  Unicode shortcodes, open the Command Palette (Ctrl+Shift+P on
--  Windows/Linux or Cmd+Shift+P on macOS), type "Lean 4: Show Unicode
--  Input Abbreviations", and press Enter.

--  ### Types

--  Every expression in Lean has a type describing what sort of value it
--  computes. The `#check` command asks Lean to print the type of an
--  expression.

#check Bool.true

--  Output:
--    Bool.true : Bool

--  If the expression after `#check` is followed by a colon and a type,
--  Lean will verify that the type of the expression matches the given type
--  and signal an error if not.

#check (Bool.true : Bool)
#check (Bool.not Bool.true : Bool)

--  Output:
--    true : Bool

--  Output:
--    !true : Bool

--  Functions like `Bool.not` are themselves ordinary values, just like
--  `Bool.true` and `Bool.false`. Their types are called *function types*,
--  and they are written with arrows.

#check Bool.not

--  The type of `Bool.not`, written `Bool → Bool` and pronounced "`Bool`
--  arrow `Bool`," can be read, "Given an input of type `Bool`, this
--  function produces an output of type `Bool`." Similarly, the type of
--  `Bool.and`, written `Bool → Bool → Bool`, can be read, "Given two
--  inputs, each of type `Bool`, this function produces an output of type
--  `Bool`."

--  ### New Types from Old

--  The enumerated types we have seen so far are so named because their
--  definitions explicitly enumerate a finite set of elements: their
--  constructors. Here is a more interesting inductive type definition,
--  `Color`, where one of the constructors takes an argument:

inductive RGB : Type where
  | red
  | green
  | blue

inductive Color : Type where
  | black
  | white
  | primary (p : RGB)

--  *Constructor expressions* are formed by applying a constructor to zero
--  or more other constructors or constructor expressions, obeying the
--  declared number and types of the constructor arguments. E.g., these are
--  valid constructor expressions...
--
--  - `RGB.red`
--  - `Bool.true`
--  - `Color.primary` `RGB.red`
--
--  ...but these are not:
--
--  - `RGB.red Color.primary`
--  - `Bool.true RGB.red`
--  - `Color.primary (Color.primary RGB.red)`

--  We can define functions on colors using pattern matching, just as we
--  did for `Day` and `MyBool`.

def monochrome (c : Color) : Bool :=
  match c with
  | Color.black => Bool.true
  | Color.white => Bool.true
  | Color.primary p => Bool.false

--  Since the `primary` constructor takes an argument, a pattern that
--  matches `.primary` should include a variable, a constant of appropriate
--  type, or `_`. Lean's convention is to use a `_` (called a *wildcard*)
--  when the argument to a constructor doesn't matter. In the definition of
--  `monochrome`, we don't use the argument to `Color.primary`, so a more
--  idiomatic definition would be:

def monochrome' (c : Color) : Bool :=
  match c with
  | Color.black => Bool.true
  | Color.white => Bool.true
  | Color.primary _ => Bool.false

--  We can use a constant argument to `Color.primary` to match a specific
--  primary color:

def isRed (c : Color) : Bool :=
  match c with
  | Color.black => Bool.false
  | Color.white => Bool.false
  | Color.primary RGB.red => Bool.true
  | Color.primary _ => Bool.false

--  The pattern `Color.primary RGB.red` will match only when `c` is
--  `Color.primary` with the argument `RGB.red`. The pattern
--  `Color.primary _` matches every `Color.primary` color, but because
--  patterns are checked in order, the `Color.primary _` case will never be
--  reached if the color is `RGB.red`.

--  An alternative way to write the same function would be to explicitly
--  nest match statements:

def isRed' (c : Color) : Bool :=
  match c with
  | Color.black => Bool.false
  | Color.white => Bool.false
  | Color.primary r =>
    match r with
    | RGB.red => Bool.true
    | _ => Bool.false

--  This `isRed'` function produces the same result as `isRed`. It also
--  illustrates the *use* of a pattern variable in the corresponding
--  branch.

--  The `Color.primary r` pattern stores the `RGB` argument into variable
--  `r`, and then pattern matches on that argument to produce the final
--  result.

--  ### Exercise (1 star): is_weekend ⭐

--  Define a function that takes a `Day` and returns `true` iff the day is
--  a weekend.
--
--  Then fill in the right-hand sides of the `example` blocks below. If
--  you've done both correctly, the blocks will produce no errors and
--  contain no uses of `sorry`.
--
--  Hint: You could write this function by pattern matching on each
--  possible day of the week, or you could try to come up with a shorter
--  solution...

def is_weekend (d : Day) : Bool
  := sorry

theorem is_weekend_test1 : is_weekend Day.sunday = true := sorry
theorem is_weekend_test2 : is_weekend Day.friday = false := sorry

--  ### Exercise (1 star): isInversion ⭐

--  Define a function that takes two colors and returns `true` if the
--  second color is an *inversion* of the first, and `false` otherwise.
--
--  Inversion is defined by cases: Black is an inversion of white and vice
--  versa. Red is an inversion of blue and vice versa. Green is not an
--  inversion of anything.
--
--  As before, write the right-hand sides of the `example` blocks to ensure
--  they pass with no `sorry`.

def isInversion (c1 c2 : Color) : Bool
  := sorry

theorem isInversion_test1 : isInversion Color.black Color.white = true := sorry
theorem isInversion_test2 : isInversion Color.white Color.black = Bool.true := sorry
theorem isInversion_test3 : isInversion (Color.primary RGB.red) (Color.primary RGB.blue) = Bool.true :=
  sorry
theorem isInversion_test4 : isInversion (Color.primary RGB.green) (Color.primary RGB.red) = Bool.false :=
  sorry

--  ### Namespaces

--  This chapter has already used Lean's system of *namespaces* for
--  managing potentially conflicting names in a few places. Now we have
--  seen enough that we can look more closely at how it works.
--
--  When we enclose a collection of declarations in
--  `namespace X ... end X`, references from outside this collection to
--  names declared within it are referred to with prefix `X.`, like `X.foo`
--  instead of just `foo`. In large Lean developments, namespaces are used
--  to organize definitions and theorems similarly to how modules are used
--  in other programming languages.

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

--  Namespaces can be closed and later reopened, as often as you like, to
--  add new definitions and access old ones more conveniently. When inside
--  a `namespace`, definitions from that namespace can be referenced
--  without prefixes.

namespace Playground
def myBar : RGB := myFoo
end Playground

#check Playground.myBar

--  Output:
--    Playground.myBar : RGB

--  Lean gives each constructor of an inductive type a name prefixed by the
--  type's name, such as `RGB.blue`. When we enter the `RGB` `namespace`,
--  we can use its constructors without the `RGB` prefix. For example, we
--  can write just `blue` below.

namespace RGB
def myBlue : RGB := blue
end RGB

--  Top-level definitions can also be prefixed by a namespace, which opens
--  the namespace temporarily for the body of the definition.

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

--  Similarly, we could rewrite the definition of `nextWorkingDay` inside
--  the `Day` namespace like so:

def Day.nextWorkingDay' (d : Day) : Day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday

--  We can also use `open` to bring the definitions of a namespace into the
--  current scope; after that, we can refer to any of the namespace's
--  definitions without a prefix.

namespace MyNamespace
def myDef : Bool := Bool.true
end MyNamespace

open MyNamespace

#check myDef

--  Output:
--    MyNamespace.myDef : Bool

--  If we only want to bring *some*, rather than all, of the definitions of
--  a namespace into the current scope, we can use the `open (...)` form:

namespace MyOtherNamespace
def myHiddenDef : Bool := Bool.true
def myVisibleDef : Bool := Bool.false
end MyOtherNamespace

open MyOtherNamespace (myVisibleDef)

-- `myVisibleDef` is now usable without qualification:
#check myVisibleDef

--  Output:
--    MyOtherNamespace.myVisibleDef : Bool

--  But `myHiddenDef`, which we did not include in the `open`, still needs
--  to be qualified:

sf_expect_failure_in
  #check myHiddenDef

--  Output:
--    Unknown identifier `myHiddenDef`

--  You might be wondering why we can use constructors like `true` and
--  `false` and functions like `not` without qualifying them with `Bool`,
--  and without explicitly `open`ing the `Bool` `namespace`. Lean provides
--  a way to *export* unprefixed names from a `namespace`, with the same
--  effect as selectively `open`ing that `namespace` downstream, and the
--  Lean prelude does that for commonly used names from the standard
--  library. We don't explain this mechanism here because it's rarely used.

#check Bool.true
#check true

--  Output:
--    Bool.true : Bool

--  Output:
--    Bool.true : Bool

--  Finally, Lean can often use an expression's expected type to fill in
--  the missing prefix of a name that begins with `.`. So, instead of the
--  fully qualified style `Day.monday`, we can write just `.monday`.
--
--  For example, when the expected type is `Day`, Lean interprets `.monday`
--  as `Day.monday`. If the context does not determine an expected type,
--  Lean reports an error.
--
--  So, for example, we can also write `nextWorkingDay` like this, using
--  the shorter style for both the value being matched and the value being
--  returned:

def nextWorkingDay' (d : Day) : Day :=
  match d with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday

--  Here, both the type of `d` and the return type of the function are
--  declared to be `Day`s. When we use the `.monday` style in the function
--  body, Lean can figure out that we must mean `Day.monday`. However, in
--  the example below, there is no expected type, so Lean cannot determine
--  which declaration named `.true` is intended. In this case, it raises an
--  error:

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

--  But in the following example, because `Bool.not` takes a `Bool`
--  argument, Lean knows that `.true` must here be a `Bool`:

#check (Bool.not .true)

--  Output:
--    !true : Bool

--  ### Exercise (1 star): custom_namespace_checks (Manually graded) ⭐

--  Predict the output of each of the statements below. Would their results
--  change depending on which namespace the statements appear in? How?

--  #check .black           -- Write your prediction here.
--  #check Color.black      -- Write your prediction here.
--  #check RGB              -- Write your prediction here.
--  #check Playground.myFoo -- Write your prediction here.

--  Once you have written your predictions, copy the lines from the comment
--  into an active section of the book to evaluate them.

--  ### Constructors with Multiple Parameters (Tuple Types)

namespace Playground

--  A constructor of an inductive type can have multiple parameters, not
--  just zero or one. This feature lets us define *tuple types* in Lean.
--
--  As an example, consider representing the four bits in a nibble (half a
--  byte). We first define a datatype `Bit` that resembles `Bool` (using
--  the constructors `b1` and `b0` for the two possible bit values) and
--  then define the datatype `Nibble`, which is a tuple of four bits.

inductive Bit : Type where
  | b1
  | b0

inductive Nibble : Type where
  | bits (x0 x1 x2 x3 : Bit)

#check Nibble.bits .b1 .b0 .b1 .b0

--  Output:
--    Nibble.bits Bit.b1 Bit.b0 Bit.b1 Bit.b0 : Nibble

--  The `bits` constructor illustrates a convenience feature of
--  multi-parameter declarations, both for constructors and for functions:
--  instead of writing `(x0 : Bit) (x1 : Bit) ...`, we write
--  `(x0 x1 ... : Bit)` since all of the variables have the same type. We
--  could have done the same with the function definition `MyBool.or`
--  above, writing `or (b1 b2 : MyBool)` rather than
--  `or (b1 : MyBool) (b2 : MyBool)`.
--
--  The `bits` constructor acts as a wrapper for its contents. Unwrapping
--  happens during pattern matching, as in the `allZero` function below,
--  which tests a `Nibble` to see if all its bits are `b0`.

def allZero (nb : Nibble) : Bool :=
  match nb with
  | .bits .b0 .b0 .b0 .b0 => true
  | .bits _   _   _   _   => false

example : allZero (.bits .b1 .b0 .b1 .b0) = false := by rfl
example : allZero (.bits .b0 .b0 .b0 .b0) = true  := by rfl

end Playground

--  #### Structures

--  An inductive type with just one constructor can alternatively be
--  defined as a `structure`, an analog of a record type in other
--  programming languages.

structure NibbleStruct : Type where
  x0 : Playground.Bit
  x1 : Playground.Bit
  x2 : Playground.Bit
  x3 : Playground.Bit

--  Rather than construct an instance of this type as
--  `.bits .b0 .b0 .b0 .b0`, we write it like this:

#check NibbleStruct.mk .b0 .b0 .b0 .b0

--  Output:
--    { x0 := Playground.Bit.b0, x1 := Playground.Bit.b0, x2 := Playground.Bit.b0, x3 := Playground.Bit.b0 } : NibbleStruct

--  The `.mk` constructor is created for us.

--  A nicer way to build structure values is to assign values to their
--  fields by name.

def zeroNibble : NibbleStruct := {
    x0 := .b0
    x1 := .b0
    x2 := .b0
    x3 := .b0
  }

--  Since the result type is declared to be `NibbleStruct`, Lean knows
--  which structure and fields we mean. Unlike `NibbleStruct.mk`, this
--  construction syntax doesn't depend on the order of fields.
--
--  Besides constructing structures from scratch, we can also "update" an
--  existing structure — i.e., construct a new structure while reusing some
--  of the old fields.

def setFirstTwoBits (old : NibbleStruct)
    (newX0 : Playground.Bit)
    (newX1 : Playground.Bit) : NibbleStruct :=
  { old with x0 := newX0, x1 := newX1 }

--  The expression `{ old with ... }` constructs a new `NibbleStruct` whose
--  `x0` and `x1` have the given values and whose other fields are copied
--  from `old`. Keep in mind that `old` was not modified — we constructed a
--  new structure starting from the old one.

def makeNibbleStruct (x0 x1 x2 x3 : Playground.Bit) : NibbleStruct :=
  { x0, x1, x2, x3 }

--  When a field and the variable supplying its value have the same name,
--  Lean lets us write just the name. Thus `{ x0, x1, x2, x3 }` is a
--  shorthand for `{ x0 := x0, x1 := x1, x2 := x2, x3 := x3 }`. This is
--  called *field abbreviation*.

--  ### Natural Numbers

--  We put this portion of the chapter in a namespace so that our
--  definition of numbers does not interfere with the one from the standard
--  library. Our definition matches the standard one, which we will use in
--  the rest of the book.

namespace NatPlayground

--  All the types we have defined so far — both enumerated types such as
--  `Day`, `MyBool`, and `Playground.Bit`, and tuple types such as
--  `Playground.Nibble` built from them — are finite. The natural numbers,
--  on the other hand, are an infinite set, so we'll need to use a slightly
--  richer form of inductive type declaration to represent them:
--  *recursive* inductive types.
--
--  While the need for recursion is unequivocal, there are many recursively
--  defined representations of numbers to choose from. You are certainly
--  familiar with decimal notation (base 10), using the digits 0 through 9,
--  for example, to form the number 123. You have likely also encountered
--  hexadecimal notation (base 16), in which the same number is represented
--  as 7B, or octal (base 8), where it is 173, or binary (base 2), where it
--  is 1111011. Using an enumerated type to represent digits, we could use
--  any of these as our representation of natural numbers.
--
--  There are circumstances in which each of these choices is useful. The
--  binary representation is valuable in computer hardware because the
--  digits can be represented with just two distinct voltage levels,
--  resulting in simple circuitry.
--
--  Here we choose an even simpler *unary* (base 1) representation, for the
--  sake of streamlining proofs. As a Lean datatype, it uses two
--  constructors. The `zero` constructor represents the number zero. The
--  `succ` constructor can be applied to the representation of the natural
--  number `n`, yielding the representation of `n + 1`, where `succ` stands
--  for "successor." The number `n` is then represented by `n` applications
--  of `succ` to `zero`.
--
--  Here is the complete datatype definition:

inductive Nat : Type where
  | zero
  | succ (n : Nat)

--  With a little Lean magic, we can also arrange that ordinary numerals
--  such as 0, 1, and 2 will be interpreted as values of our new `Nat` type
--  whenever this is sensible in context. The technical details are not
--  important.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Library Nat to SFL Nat coercion)
def ofNat : _root_.Nat → Nat
  | .zero => .zero
  | .succ n => .succ (ofNat n)

instance (n : _root_.Nat) : OfNat Nat n := ⟨ofNat n⟩
attribute [pp_nodot] Nat.succ
--  END DETAILS

--  We'll define some shorthands for numbers, putting them in the `Nat`
--  namespace so we don't need to use `.` notation everywhere.

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

--  These are all things that can be applied to a number to yield a number.
--  But there is a difference between `succ` and the other two.

--  Functions like `pred` and `minusTwo` are defined by giving *computation
--  rules* — e.g., the definition of `pred` says that
--  `pred (succ (succ zero))` can be simplified to `succ zero` — while the
--  definition of `succ` has no such behavior attached. Although it is like
--  a function in the sense that it can be applied to an argument, it does
--  not *do* anything at all! It is just the way we write down numbers.

--  We can also define *recursive functions*: functions that call
--  themselves repeatedly down to a base case. Recursion is the essence of
--  repeated computation in functional programming; in this course, we will
--  make extensive use of recursive functions.
--
--  We first define a simple recursive function, `even`, then a slightly
--  more sophisticated recursive function, `add`.

def even (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even n'

example : even one = false := by rfl
example : even four = true := by rfl

--  We could define `odd` by a similar recursive declaration, but here is a
--  simpler way:

def odd (n : Nat) : Bool :=
  not (even n)

example : odd one = true := by rfl
example : odd four = false := by rfl

--  This function takes multiple parameters, recursing on the second:

def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

#eval add one two -- succ (succ (succ zero)) -- aka, three!

--  Output:
--    NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero)))

--  We can also define infix notation for our `add` function.

scoped infixl:65 " + " => add

#eval one + two -- succ (succ (succ zero)) -- aka, three again.

--  Output:
--    NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero)))

--  ## Proof by Rewriting

--  ### Proving Properties about Functions in Lean

--  Being recursive on a `Nat` and returning a `Nat` as well, `add` is the
--  first example of a more sophisticated class of functions. In this
--  chapter and beyond, we will *prove* properties about recursive
--  functions like `add` over inductive datatypes like `Nat`, using
--  *simplification rules*, also known as *characterizing lemmas*, about
--  their behavior.
--
--  Here is a simplification rule about `add`:
--
--  - `n + zero = n`
--
--  In Lean, this rule looks like this:

theorem add_zero : ∀ n : Nat, n + zero = n := by
  intro n
  rfl

#check add_zero

--  Output:
--    NatPlayground.Nat.add_zero (n : Nat) : n + zero = n

--  Using our simplification rule `add_zero`, we can carry out a simple
--  proof about natural numbers.

theorem add_zero_zero : ∀ n : Nat, n + zero + zero = n := by
  intro n
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

--  We'll walk through this proof in the next section.

--  ### Proof State and Tactics

--  The `rewrite` tactic in the proof of `add_zero_zero` is used to
--  transform the goal of the proof according to an equality. The
--  `add_zero` in brackets is an *argument* to the `rewrite` tactic.
--
--  Let's walk through the theorem again in detail.

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
  intro n
  rewrite [add_zero]
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

--  ### The `rewrite` tactic

--  The `rewrite` tactic tells Lean to rewrite (part of) a goal or
--  hypothesis based on a rule (or rules), given in square brackets. For
--  example, given the rule `add_zero`, which states that `n + zero` is
--  equal to `n` for any `n`, we can replace any `n + zero` in our proof
--  with `n` via `rewrite [add_zero]`.

--  ### The `rfl` tactic

--  The `rfl` tactic closes a goal of the shape `a = a`, for any `a`. It
--  checks that both sides of the equality are *definitionally equal* —
--  that is, that they reduce to the same term. (So, in particular, a term
--  is always definitionally equal to itself.)

--  ### A New `add` Rule

--  Here is another fundamental rule about addition:
--
--  `n + (succ m) = succ (n + m)`.
--
--  This is the rule we need to push `succ` around.
--
--  Here it is in Lean:

theorem add_succ : ∀ n m : Nat, n + (succ m) = succ (n + m) := by
  intro n m
  rfl

--  Now, let's use `add_succ` in a proof:

theorem add_one (n : Nat) : n + (succ zero) = succ n + zero := by
  rewrite [add_succ]
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

--  We recommend stepping through these proofs in VS Code — that is, moving
--  past each tactic with your cursor to see how it changes the proof state
--  and hovering over each argument to `rewrite` to see its type.

--  ### Irreducibility, Rewriting, and Proof Engineering

--  Lean, like any other programming language, has conventions and best
--  practices for writing good software. Lean takes inspiration from
--  object-oriented programming in favoring the use of *encapsulation*. In
--  OOP, it is considered poor style to expose the fields of an object in
--  its interface; instead, those fields should be accessible only by an
--  object's methods (like getters and setters). Doing so hides the
--  object's definition, so that, if its fields or implementation ever
--  change, the interface it exposes to the outside world remains the same.
--  In simple examples, such conventions may seem overly pedantic; in
--  complex codebases, they are the only way to maintain crucial invariants
--  that prevent a system from becoming unmaintainable.
--
--  The same principle applies to programs and proofs in Lean. In this
--  chapter, we will be proving facts about functions entirely through
--  their simplification rules, rather than using `rfl` to unfold their
--  implementations invisibly. This makes every computation step visible
--  and lets a proof rely on a function's interface rather than its
--  definition.
--
--  We can do this because the foundational theorems `add_zero` and
--  `add_succ` provide a characterization of the behavior of `add` that
--  makes using `rfl` to simplify expressions unnecessary; instead, we can
--  rewrite by these theorems anywhere we want to describe how `add`
--  evaluates. In real-world Lean developments, the style of writing proofs
--  using simplification rules is both standard and expected.
--
--  For the next few chapters, we mark definitions with
--  `attribute [irreducible]` to prevent this kind of unfolding. This means
--  that `rfl` cannot unfold these definitions behind the scenes: after
--  rewriting by their simplification rules, it closes only the remaining
--  straightforward equality. We use `attribute [irreducible]` for now to
--  enforce the style of using simplification rules, so that it is natural
--  to you moving forward. We will relax this discipline in later chapters.

attribute [irreducible] add

--  These simplification rules also follow a particular pattern. Let's look
--  again at the definition of `add`, without the `+` notation for maximum
--  clarity:

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

--  Each of `add_zero` and `add_succ` corresponds to one branch of the
--  `match` statement defining `add` and describes how the evaluation of
--  `add` proceeds in that case. The `add_zero` theorem describes how
--  `add n zero` evaluates, while `add_succ` describes (symbolically) how
--  `add n (succ m)` evaluates.
--
--  These are instances of a general pattern: for each definition that
--  pattern matches on an inductive type, we will provide one
--  simplification rule for each branch of control flow through the
--  function.
--
--  So, for example, we need two simplification rules for the definition of
--  `pred`:

theorem pred_zero : pred zero = zero := by rfl
theorem pred_succ (n : Nat) : pred (succ n) = n := by rfl

--  Now that we have defined and proved `pred`'s simplification rules, we
--  can mark it `irreducible` to enforce rewriting by these lemmas.

attribute [irreducible] pred

--  Similarly, for each of the three branches of the definition of `even`,
--  we need one simplification rule:

theorem even_zero : even zero = true := rfl
theorem even_one : even (succ zero) = false := rfl
theorem even_succ_succ (n : Nat) : even (succ (succ n)) = even n := rfl

attribute [irreducible] even odd

--  In the remainder of this textbook, we will pair definitions with
--  simplification rules. After proving these rules, instead of using `rfl`
--  to peek through the definitions, we will `rewrite` using the rules.
--
--  Eventually, we will introduce a way to *automatically* apply these
--  simplification rules. Real-world Lean developments use automation
--  extensively, and you will learn to do so gradually throughout this
--  book. For the moment, it is important that you work through these early
--  concepts by hand, without automation. By the time the more powerful
--  tools are introduced, you will have the foundational understanding to
--  use them with precision and skill.

--  ### Working with Numerals

--  We know from our definitions above that `one` is just `succ zero`,
--  `two` is `succ one`, and so on. We can write rules for these equalities
--  too:

theorem one_eq_succ_zero : one = succ zero := by rfl
theorem two_eq_succ_one : two = succ one := by rfl
theorem three_eq_succ_two : three = succ two := by rfl
theorem four_eq_succ_three : four = succ three := by rfl

--  We can rewrite with these rules to expand numerals into their
--  definitions, which allows us to use our `add` rules. Here's an example
--  of how to start a proof this way.

--  ### Exercise (1 star): nat_eq_rules ⭐

--  Finish the proof using the `add` rules:

theorem one_plus_one_eq_two : one + one = two := by
  rewrite [one_eq_succ_zero]
  sorry

--  Try the same for `two + two = four`.

theorem two_plus_two_eq_four : two + two = four := by
  sorry

--  #### Multiplication

--  Now that we know how addition is defined, we can use it to define
--  multiplication:

def mul (n m : Nat) : Nat :=
  match m with
  | zero => zero
  | succ m' => (mul n m') + n

scoped infixl:70 " * " => mul

--  ### Exercise (1 star): mul_simpl_rules ⭐

--  Multiplication, like any function we will prove properties about, also
--  has simplification rules.
--
--  Remove `sorry` and prove the simplification rules for `mul` below. You
--  will likely find the proofs of the simplification rules for `add` to be
--  helpful as a model.

theorem mul_zero : ∀ n : Nat, n * zero = zero := by
  sorry

theorem mul_succ : ∀ n m : Nat, n * (succ m) = (n * m) + n := by
  sorry

attribute [irreducible] mul

--  Prove this theorem using rewriting with the simplification rules.

theorem zero_add_one : (zero + one : Nat) = one := by
  rewrite [one_eq_succ_zero]
  rewrite [add_succ, add_zero]
  rfl

--  Notice how `rewrite` can take any number of arguments. You can rewrite
--  with all of the simplification rules at once, for example.
--
--  After each rewrite, check the proof state by placing the cursor
--  immediately after a rule to see how the goal is changing. This happens
--  naturally as you write the proof, which makes it convenient to use
--  `rewrite` blocks with multiple rules.

--  ### Exercise (2 stars): test_mul_add ⭐⭐

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

--  #### Equality and Ordering

--  When we say that Lean relies on almost nothing that's truly built-in,
--  we really mean it: even testing equality is not a primitive operation,
--  but an ordinary function that we could reimplement ourselves as users.

--  Here is a function `beq` that tests natural numbers for equality,
--  yielding a boolean.

def beq (n m : Nat) : Bool :=
  match n with
  | zero => match m with
            | zero => true
            | succ _ => false
  | succ n' => match m with
               | zero => false
               | succ m' => beq n' m'

--  We could also write this by pattern matching on both `n` and `m` at the
--  same time:

def beq' (n m : Nat) : Bool :=
  match n, m with
  | zero, zero => true
  | zero, succ _ => false
  | succ _, zero => false
  | succ n', succ m' => beq n' m'

--  The definitions of `beq` and `beq'` are equivalent.
--
--  Similarly, the `ble` function tests whether its first argument is less
--  than or equal to its second argument, yielding a boolean.

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

--  ### Exercise (1 star): blt ⭐

--  Define a less-than function in terms of `ble`.

def blt (n m : Nat) : Bool := sorry

example : blt two two = false := sorry
example : blt two four = true  := sorry
theorem blt_test3 : blt four two = false := sorry

attribute [irreducible] blt ble

--  We'll be using `beq` a lot, so let's give it an infix notation.

scoped infixl:30 " == " => beq

--  We now have seen two symbols that both look like equality: `=` and
--  `==`. We'll have much more to say about their differences and
--  similarities later. For now, notice that `x = y` is a logical *claim* —
--  a "proposition" — that we can try to prove, while `x == y` is a boolean
--  *expression* whose value (either `true` or `false`) Lean can compute.

--  We can also now define the simplification rules for `beq` with our new
--  notation, one for each of the four cases of control flow through the
--  function.

theorem zero_beq_zero : (zero == zero) = true := by rfl
theorem zero_beq_succ (n : Nat) : (zero == (succ n)) = false := by rfl
theorem succ_beq_zero (n : Nat) : ((succ n) == zero) = false := by rfl
theorem succ_beq_succ (n m : Nat) : ((succ n) == (succ m)) = (n == m) := by rfl

attribute [irreducible] beq

--  Aside: Our naming convention for simplification rules encodes their
--  meaning. For `add_zero` and `add_succ`, notice that the `zero` and
--  `succ` come after the `add`; this is because they depend on `add`'s
--  *second* argument and do not care about its first.
--
--  Also, in the `beq` rules above, we write `zero_beq_zero` and
--  `zero_beq_succ` because the rules apply to both the first and second
--  arguments of `beq`. We put `beq` between the arguments because it is
--  usually written in infix notation. There are no strict style
--  conventions for naming theorems like this in Lean, but many developers
--  follow this approach.

--  ### General Proofs about Natural Numbers

--  We now begin to make claims about *general* natural numbers.
--
--  We begin by making a universal claim about all numbers `n` and `m` that
--  are equal to each other (`n = m`). The arrow symbol is pronounced
--  "implies." Enter it with `\to` or `\->` or `\r`.
--
--  The `intro` tactic moves the universally quantified variables and the
--  hypothesis into the context, giving them names. The goal is now to
--  prove `n + n = m + m` under the assumption `h : n = m`.
--
--  The tactic that tells Lean to perform replacement is one we have seen
--  before: `rewrite`. It can take a hypothesis from the context as an
--  argument, just like it can take a previously proved theorem. In this
--  case, we want to rewrite with the hypothesis `h`, which says that `n`
--  and `m` are equal, so that we can replace `n` with `m` in the goal.
--
--  After the rewrite, the goal is `m + m = m + m`, which can be closed by
--  `rfl`.

theorem add_id_example : ∀ n m : Nat,
    n = m → n + n = m + m := by
  intro n m
  intro h
  rewrite [h]
  rfl

--  ### Exercise (1 star): add_id_exercise ⭐

--  Remove `sorry` and fill in the proof.

theorem add_id_exercise : ∀ n m o : Nat,
    n = m → m = o → n + m = m + o := by
  sorry

--  #### Displaying Theorem Statements

--  The `#check` command can also be used to examine the statements of
--  previously declared lemmas and theorems.

#check mul_zero
#check mul_succ

--  Output:
--    NatPlayground.Nat.mul_zero (n : Nat) : n * zero = zero

--  Output:
--    NatPlayground.Nat.mul_succ (n m : Nat) : n * succ m = n * m + n

--  Note that you may see a slight discrepancy in the output: `#check`
--  shows the theorem differently from the way it was introduced earlier.
--
--  First, Lean may print the theorem's fully qualified name
--  `NatPlayground.Nat.mul_zero`. The qualification identifies the
--  namespace containing the theorem, though the shorter name `mul_zero` is
--  usually sufficient when Lean can determine which declaration we mean.
--
--  Second, Lean displays the theorem's arguments before the colon, as in
--  `mul_zero (n : Nat) : n * zero = zero`. Writing arguments as binders
--  before the colon is called *declaration-header style*. The same
--  statement can be written using an explicit universal quantifier, as we
--  have seen before:
--
--      mul_zero : ∀ (n : Nat), n * zero = zero
--
--  Writing statements in declaration-header style shortens proofs because
--  Lean automatically adds declared variables to the context, rather than
--  requiring them to be added with `intro`. The declaration-header style
--  is conventional in Lean, and we will generally use it from now on.

--  ## Proof by Case Analysis

--  Of course, not everything can be proved by simple calculation and
--  rewriting: in general, the presence of unknown, hypothetical values
--  (arbitrary numbers, booleans, etc.) can block a proof.

sf_expect_failure_in
  example (n : Nat) : (succ zero + n == zero) = false := by
    /-
      We can't rewrite by any lemmas here: `add`'s definition matches on its
      *second* argument, and here that argument is the unknown `n`!
    -/

--  The tactic that tells Lean to consider separate cases is called
--  `cases`.

theorem add_one_neb_zero (n : Nat) : (succ zero + n == zero) = false := by
  cases n with
  | zero =>
    rewrite [add_zero, succ_beq_zero]
    rfl
  | succ n' =>
    rewrite [add_succ, succ_beq_zero]
    rfl

--  The `cases` tactic generates *two* subgoals, which we must prove
--  separately in order to get Lean to accept the theorem. The generated
--  subgoals are tagged by the names of the constructors. `| zero =>` and
--  `| succ n' =>` select which subgoal to work on next and introduce
--  variable names. Note also that when we enter a subcase, we increase the
--  level of indentation at which we are working by two spaces.
--
--  The `cases` tactic can be used with any inductively defined datatype.
--  For example, we use it next to prove that boolean negation is
--  involutive (that is, that negation is its own inverse).

theorem not_involutive (b : Bool) : (!!b) = b := by
  cases b with
  | false =>
    rewrite [Bool.not_false, Bool.not_true]
    rfl
  | true =>
    rewrite [Bool.not_true, Bool.not_false]
    rfl

--  The proof above uses some simplification rules that we didn't prove
--  previously. These come from Lean's standard library, in particular from
--  the section about booleans. In the UsingLean chapter we will discuss
--  how to search through the standard library for theorems like these. For
--  now, note that, if you hover over the names of these theorems in VS
--  Code, the Lean extension will show you what the theorem proves.

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

--  As you can see, proofs by cases can become very verbose. We will
--  introduce some tactics for writing shorter proofs by case analysis in
--  the Tactics chapter.

--  ### New Tactics: `rewrite ... at` and `exact`

--  Some new tactics will be useful for the exercises ahead.
--
--  The `rewrite ... at` tactic can be used to rewrite in a hypothesis
--  instead of the goal. For example, if `hp : p` is in the context and we
--  have a rule `r : p = q`, then `rewrite [r] at hp` changes the
--  hypothesis to `hp : q`.
--
--  The `exact` tactic closes a goal by providing the exact proof of the
--  goal. For example, if `hp : p` is in the context and the goal is `p`,
--  then `exact hp` closes the goal. You can also transform `hp` slightly
--  when using `exact`, and we will explain how when we get to an example
--  that needs it.

--  ### Exercise (2 stars): or_false_true ⭐⭐

--  Prove the following claim.
--
--  Tip: the simplification rule for `(b || false)` is called
--  `Bool.or_false`.

theorem or_false_true (b : Bool) (h : (b || false) = true) :
  b = true := by
  sorry

--  ### Exercise (1 star): zero_neb_add_one ⭐

theorem zero_neb_add_one (n : Nat) :
  (zero == (succ zero + n)) = false := by
  sorry

--  ### Structural Recursion (Optional)

--  Here is a copy of the definition of `even`:

def even' (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even' n'

--  When Lean checks this definition, it verifies that the recursion
--  terminates. Specifically, it checks that the recursive argument is
--  *structurally decreasing* — each recursive call made in the body of the
--  definition is made on an argument that is smaller than the original
--  input. In the `even'` example above, the argument to the recursive call
--  to `even'` is the variable `n'`. Because of our pattern match, we know
--  that `n` is equal to `succ (succ n')`, and therefore that `n'` is
--  smaller than `n`. This makes `n'` an acceptable argument to `even'` for
--  Lean's termination checker, and so this recursive definition is
--  accepted.
--
--  This requirement is a fundamental feature of Lean's design: it
--  guarantees that every ordinary recursive definition accepted into
--  Lean's logic terminates on all inputs. However, because Lean's
--  termination analysis is not always able to figure things out
--  automatically, it is sometimes necessary to provide hints or write
--  functions in slightly different ways.

--  ### Exercise (2 stars): decreasing (Optional, Manually graded) ⭐⭐

--  To get a concrete sense of how termination checking works in Lean, find
--  a way to write a sensible recursive definition (of a simple function on
--  numbers, say) that does actually terminate on all inputs, but that Lean
--  will reject because it cannot automatically prove termination.

--  ### Binary Numerals

--  ### Exercise (3 stars): binary ⭐⭐⭐

--  We can generalize our unary representation of natural numbers to the
--  more efficient binary representation by treating a binary number as a
--  sequence of constructors `b0` and `b1` (representing 0s and 1s),
--  terminated by a `z`.
--
--  For example:

--  decimal                binary   unary
--        0                     z   zero
--        1                  b1 z   succ zero
--        2             b0 (b1 z)   succ (succ zero)
--        3             b1 (b1 z)   succ (succ (succ zero))
--        4        b0 (b0 (b1 z))   succ (succ (succ (succ zero)))
--        5        b1 (b0 (b1 z))   succ (succ (succ (succ (succ zero))))
--        6        b0 (b1 (b1 z))   succ (succ (succ (succ (succ (succ zero)))))
--        7        b1 (b1 (b1 z))   succ (succ (succ (succ (succ (succ (succ zero))))))
--        8   b0 (b0 (b0 (b1 z)))   succ (succ (succ (succ (succ (succ (succ (succ zero)))))))

--  Note that the low-order bit is on the left and the high-order bit is on
--  the right — the opposite of the way binary numbers are usually written.
--  This choice makes them easier to manipulate.
--
--  (Comprehension check: What unary numeral does `b0 z` represent?)

inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

--  THE FOLLOWING DETAILS CAN BE SKIPPED
attribute [pp_nodot] Bin.b1 Bin.b0
--  END DETAILS

def incr (m : Bin) : Bin
  := sorry

def binToNat (m : Bin) : Nat
  := sorry

theorem incr_test1 : incr (.b1 .z) = .b0 (.b1 .z) := sorry
theorem incr_test2 : incr (.b0 (.b1 .z)) = .b1 (.b1 .z) := sorry
theorem incr_test3 : incr (.b1 (.b1 .z)) = .b0 (.b0 (.b1 .z)) := sorry

theorem incr_z : incr .z = .b1 .z := sorry
theorem incr_b0 (m : Bin) : incr (.b0 m) = .b1 m := sorry
theorem incr_b1 (m : Bin) : incr (.b1 m) = .b0 (incr m) := sorry

theorem binToNat_z : binToNat .z = zero := sorry
theorem binToNat_b0 (m : Bin) : binToNat (.b0 m) = binToNat m * two := sorry
theorem binToNat_b1 (m : Bin) : binToNat (.b1 m) = binToNat m * two + one := sorry

--  You may find your previous proofs of `zero_add_one`, `one_add_one`,
--  `zero_mul_two`, `one_mul_two`, and `two_mul_two` useful here.

example : binToNat (.b0 (.b1 .z)) = two := sorry
theorem binToNat_test1 : binToNat (incr (.b1 .z)) = add one (binToNat (.b1 .z)) := sorry
theorem binToNat_test2 : binToNat (incr (incr (.b1 .z))) = add two (binToNat (.b1 .z)) := sorry
theorem binToNat_test3 : binToNat (.b0 (.b0 (.b1 .z))) = four := sorry

attribute [irreducible] incr binToNat

end Nat

--  ## More Exercises

--  ### Warmups

--  ### Exercise (1 star): identity_fn_applied_twice ⭐

--  You now have a small but rather powerful suite of tactics at your
--  disposal. As a warmup for the last section of the chapter, use the
--  tactics you have learned so far to prove the following theorem about
--  boolean functions.
--
--  Hint: You can use `rewrite` with *any* hypothesis that has an `=` in it
--  as long as the types line up.

theorem identity_fn_applied_twice (f : Bool → Bool) :
    (∀ x : Bool, f x = x) →
    ∀ b : Bool, f (f b) = b := by
  sorry

--  ### Exercise (1 star): negation_fn_applied_twice (Manually graded) ⭐

--  Now state and prove a theorem `negation_fn_applied_twice` similar to
--  the previous one but where the hypothesis says that the function `f`
--  has the property that `f x = !x`.

--  FILL IN HERE

--  ### Exercise (3 stars): and_eq_or (Optional) ⭐⭐⭐

--  Prove the following theorem.

theorem and_eq_or (b c : Bool) : (b && c) = (b || c) → b = c := by
  sorry

--  ### Airport Exercise

--  Now that we have learned some basic features of Lean, let's close the
--  chapter with an exercise that brings them together.
--
--  In this exercise, we will model part of a database storing information
--  about travelers passing through an airport. The database contains one
--  entry per traveler, recording information about where the traveler is
--  in the airport process and the contents of their current carry-on bag.
--
--  We will implement several operations on these entries, state intended
--  properties of the database's behavior, and prove that the
--  implementation satisfies them.

namespace Airport

--  For simplicity, a carry-on bag either contains a prohibited item, such
--  as a liquid that exceeds the allowed limit, causing it to fail
--  inspection, or contains only ordinary items.

inductive BagContent : Type where
  | prohibited
  | ordinary

--  After a traveler checks in, the database also records the result of the
--  most recent security screening of their carry-on bag.

inductive ScreeningStatus : Type where
  | notScreened
  | cleared
  | blocked

--  Next, we define the possible stages of the airport process a traveler
--  can inhabit:
--
--  - they have not yet purchased a ticket;
--
--  - they have a ticket but have not yet checked in;
--
--  - they have checked in, in which case the database also stores the
--    screening status of their carry-on bag.
--
--  We can represent these possible database entries directly with an
--  inductive type.

inductive Traveler : Type where
  | noTicket  (bagContent : BagContent)
  | ticketed  (bagContent : BagContent)
  | checkedIn (bagContent : BagContent) (screeningStatus : ScreeningStatus)

--  Buying a ticket changes a traveler with no ticket into a ticketed
--  traveler. If the traveler already has a ticket or has already checked
--  in, nothing changes.

--  ### Exercise (1 star): buyTicket ⭐

def buyTicket (t : Traveler) : Traveler := sorry
theorem buyTicket_test1 : buyTicket (.noTicket .ordinary) = .ticketed .ordinary := sorry
theorem buyTicket_test2 : buyTicket (.checkedIn .prohibited .blocked) = .checkedIn .prohibited .blocked := sorry

--  Here are the simplification rules for `buyTicket`:

theorem buyTicket_noTicket (bagContent : BagContent) :
    buyTicket (.noTicket bagContent) = .ticketed bagContent := sorry

theorem buyTicket_ticketed (bagContent : BagContent) :
    buyTicket (.ticketed bagContent) = .ticketed bagContent := sorry

theorem buyTicket_checkedIn (bagContent : BagContent)
    (screeningStatus : ScreeningStatus) :
    buyTicket (.checkedIn bagContent screeningStatus) = .checkedIn bagContent screeningStatus := sorry

attribute [irreducible] buyTicket

--  The first property we will prove about our system is that purchasing a
--  ticket is an *idempotent* operation (i.e., performing it twice has the
--  same effect as performing it once).

--  ### Exercise (2 stars): buyTicket_idempotent ⭐⭐

theorem buyTicket_idempotent (t : Traveler) :
    buyTicket (buyTicket t) = buyTicket t := by
  sorry

--  A traveler can check in only after buying a ticket. Checking in records
--  that their carry-on bag still needs to be inspected. Calling `checkIn`
--  before buying a ticket or after already checking in does nothing.

--  ### Exercise (1 star): checkIn ⭐

def checkIn (t : Traveler) : Traveler := sorry

theorem checkIn_test1 : checkIn (.noTicket .ordinary) = .noTicket .ordinary := sorry
theorem checkIn_test2 : checkIn (.ticketed .prohibited) = .checkedIn .prohibited .notScreened := sorry
theorem checkIn_test3 : checkIn (.checkedIn .ordinary .cleared) = .checkedIn .ordinary .cleared := sorry

--  Again, we record one simplification rule for each case:

theorem checkIn_noTicket (bagContent : BagContent) :
    checkIn (.noTicket bagContent) = .noTicket bagContent := sorry

theorem checkIn_ticketed (bagContent : BagContent) :
    checkIn (.ticketed bagContent) = .checkedIn bagContent .notScreened := sorry

theorem checkIn_checkedIn (bagContent : BagContent)
    (screeningStatus : ScreeningStatus) :
    checkIn (.checkedIn bagContent screeningStatus) = .checkedIn bagContent screeningStatus := sorry

attribute [irreducible] checkIn

--  A traveler who does not yet have a ticket can buy one and then check
--  in. After this, the traveler is checked in and their carry-on bag needs
--  to be screened.

--  ### Exercise (1 star): buyTicket_then_checkIn ⭐

theorem buyTicket_then_checkIn (bagContent : BagContent) :
    checkIn (buyTicket (.noTicket bagContent)) = .checkedIn bagContent .notScreened := by
  sorry

--  Carry-on inspection happens only after check-in. A bag containing only
--  ordinary items is cleared, while a bag containing a prohibited item is
--  blocked. If the traveler has not checked in, `inspectBag` does nothing.

--  ### Exercise (1 star): inspectBag ⭐

--  Define `inspectBag`.

def inspectBag (t : Traveler) : Traveler := sorry

theorem inspectBag_test1 : inspectBag (.ticketed .prohibited) = .ticketed .prohibited := sorry
theorem inspectBag_test2 : inspectBag (.checkedIn .ordinary .notScreened) = .checkedIn .ordinary .cleared := sorry
theorem inspectBag_test3 : inspectBag (.checkedIn .prohibited .notScreened) = .checkedIn .prohibited .blocked := sorry

--  Again, we record one characterization lemma for each case.

theorem inspectBag_noTicket (bagContent : BagContent) :
    inspectBag (.noTicket bagContent) = .noTicket bagContent := sorry

theorem inspectBag_ticketed (bagContent : BagContent) :
    inspectBag (.ticketed bagContent) = .ticketed bagContent := sorry

theorem inspectBag_ordinary (screeningStatus : ScreeningStatus) :
    inspectBag (.checkedIn .ordinary screeningStatus) = .checkedIn .ordinary .cleared := sorry

theorem inspectBag_prohibited (screeningStatus : ScreeningStatus) :
    inspectBag (.checkedIn .prohibited screeningStatus) = .checkedIn .prohibited .blocked := sorry

attribute [irreducible] inspectBag

--  ### Exercise (2 stars): inspectBag_idempotent ⭐⭐

--  Show that inspecting the same unchanged carry-on bag twice has the same
--  effect as inspecting it once.

theorem inspectBag_idempotent (t : Traveler) : inspectBag (inspectBag t) = inspectBag t := by
  sorry

--  A traveler may leave the screened area and return with a different
--  carry-on bag. Since the previous screening result applied to the old
--  bag, a new carry-on must be screened again before the traveler can
--  re-enter.

--  ### Exercise (1 star): changeBag ⭐

--  Define `changeBag`.

def changeBag (newContent : BagContent) (t : Traveler) : Traveler := sorry

theorem changeBag_test1 : changeBag .prohibited (.ticketed .ordinary) = .ticketed .prohibited := sorry
theorem changeBag_test2 : changeBag .prohibited (.checkedIn .ordinary .cleared) = .checkedIn .prohibited .notScreened := sorry

--  As before, we record one simplification rule for each case.

theorem changeBag_noTicket (newContent oldContent : BagContent) :
    changeBag newContent (.noTicket oldContent) = .noTicket newContent := sorry

theorem changeBag_ticketed (newContent oldContent : BagContent) :
    changeBag newContent (.ticketed oldContent) = .ticketed newContent := sorry

theorem changeBag_checkedIn (newContent oldContent : BagContent)
    (screeningStatus : ScreeningStatus) :
    changeBag newContent (.checkedIn oldContent screeningStatus) =
    .checkedIn newContent .notScreened := sorry

attribute [irreducible] changeBag

--  It is easy to see that replacing a bag after it has been inspected
--  resets its screening status. In other words, `inspectBag` and
--  `changeBag` do not, in general, commute: the order in which the two
--  operations are performed can affect the result.
--
--  However, if the traveler has not checked in, `inspectBag` does nothing,
--  so changing and inspecting the carry-on can be performed in either
--  order. There are two such cases: the traveler may not yet have a
--  ticket, or may have a ticket but not yet be checked in.

--  ### Exercise (2 stars): inspectBag_changeBag_comm ⭐⭐

theorem inspectBag_changeBag_comm_noTicket
    (oldContent newContent : BagContent) :
    inspectBag (changeBag newContent (.noTicket oldContent)) =
    changeBag newContent (inspectBag (.noTicket oldContent)) := by
  sorry

theorem inspectBag_changeBag_comm_ticketed
    (oldContent newContent : BagContent) :
    inspectBag (changeBag newContent (.ticketed oldContent)) =
    changeBag newContent (inspectBag (.ticketed oldContent)) := by
  sorry

end Airport
end NatPlayground

-- Built on 2026-09-04 18:42 UTC

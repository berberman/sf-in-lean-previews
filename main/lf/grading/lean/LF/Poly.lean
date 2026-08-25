import LF.Induction
import LF.UsingLean

import ComparatorAutograderLib
import SFLCompat

-- # Poly: Polymorphism and Higher-Order Functions

-- ## Polymorphism

-- In this chapter we continue our development of basic concepts of functional
-- programming. The critical new ideas are *polymorphism* (abstracting
-- functions over the types of the data they manipulate) and *higher-order
-- functions* (treating functions as data). We begin with polymorphism.

-- ### Polymorphic Lists

-- In the last chapter, we worked with lists containing just numbers.
-- Obviously, interesting programs also need to be able to manipulate lists
-- with elements from other types — lists of booleans, lists of lists, etc. We
-- *could* just define a new inductive datatype for each of these, for
-- example...

inductive BoolList : Type where
  | nil
  | cons (b : Bool) (l : BoolList)

-- ... but this would quickly become tedious: not only would we have to make
-- up different constructor names for each datatype, but — even worse — we
-- would also need to define new versions of all the list manipulating
-- functions (`length`, `++`, `reverse`, etc.) and all their properties
-- (`length_reverse`, `append_assoc`, etc.) for each new definition.

-- To avoid this repetition, we can make the element type itself an *argument*
-- to the definition. Lean calls such definitions *polymorphic*. Here is a
-- polymorphic list type:

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons (x : α) (l : MyList α) : MyList α

-- This is exactly like the definition of `Natlist` from the previous chapter,
-- except that the `Nat` argument to the `cons` constructor has been replaced
-- by an arbitrary type `α`, a type parameter `α` has been added to the header
-- on the first line, and the occurrences of `Natlist` in the types of the
-- constructors have been replaced by `MyList α`. We can now write
-- `MyList Nat` instead of a dedicated nat-list type.

-- What sort of thing is `MyList` itself? A good way to think about it is as a
-- *type constructor* — that is, a function from `Type`s to `Type`s. For any
-- particular type `α`, the type `MyList α` is the inductively defined type of
-- lists whose elements are of type `α`.

-- Note to developers (Yipeng Liu @berberman):
--     A trick used below: parenthesizing the declaration makes it a term —
--     Lean elaborates it and prints its inferred function type, instead of
--     the declaration signature: `MyList (α : Type) : Type`.

#check (MyList)

-- MyList : Type → Type

-- The `α` in the definition of `MyList` automatically becomes a parameter to
-- the constructors `nil` and `cons` — that is, `nil` and `cons` are now
-- polymorphic constructors. In Lean, the type parameter is *implicit* by
-- default: Lean will infer it from context. For example, `MyList.nil` is the
-- empty list, and Lean figures out the element type from how it is used.

#check MyList.nil

-- MyList.nil {α : Type} : MyList α

-- Similarly, `MyList.cons` adds an element of type `Nat` to a list of type
-- `MyList Nat`. Here is an example of forming a list containing just the
-- natural number `3`.

#check MyList.cons 3 MyList.nil

-- MyList.cons 3 MyList.nil : MyList Nat

-- What is the full type of `MyList.nil`? We can read off the result type
-- `MyList α` from the definition, but to state the full type we must also
-- bind `α`. Since the type argument to the constructor is implicit, Lean
-- writes its type as (the equivalent of) `{α : Type} → MyList α`.

#check MyList.nil

-- MyList.nil {α : Type} : MyList α

-- Similarly, the type of `MyList.cons` includes the implicit type parameter:

#check MyList.cons

-- MyList.cons {α : Type} (x : α) (l : MyList α) : MyList α

-- Having to supply a type argument for every single use of a list constructor
-- would be rather burdensome. Fortunately, the type argument is implicit, so
-- Lean will normally infer it from context.

-- We can now go back and make polymorphic versions of all the list-processing
-- functions that we wrote before. Here is `myRepeat`, for example:

def myRepeat (α : Type) (x : α) (count : Nat) : MyList α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (myRepeat α x count')

-- Some simple facts about `myRepeat`:

theorem myRepeat_zero (α : Type) (v : α) :
    myRepeat α v 0 = MyList.nil := rfl

theorem myRepeat_succ (α : Type) (v : α) (count : Nat) :
    myRepeat α v (count + 1) = MyList.cons v (myRepeat α v count) := rfl

-- We can use `myRepeat` by applying it first to a type and then to an element
-- of this type (and a number):

example : myRepeat Nat 4 2 = .cons 4 (.cons 4 .nil) := by rfl

-- To use `myRepeat` to build other kinds of lists, we simply pass a different
-- type and an element of that type:

example : myRepeat Bool false 1 = .cons false .nil := by rfl

-- _Quiz:_

-- What is the type of `MyList.cons true (MyList.cons 3 MyList.nil)`?

-- (A) `MyList Nat`

-- (B) `{α : Type} → α → MyList α → MyList α`

-- (C) `MyList Bool`

-- (D) `MyList (Nat × Bool)`

-- (E) Ill-typed

-- _Quiz:_

-- What is the type of `myRepeat`?

-- (A) `Nat → Nat → MyList Nat`

-- (B) `(α : Type) → α → Nat → MyList α`

-- (C) `(α : Type) → {β : Type} → α → Nat → MyList β`

-- (D) Ill-typed

-- _Quiz:_

-- What is the type of `myRepeat 1 2`?

-- (A) `MyList Nat`

-- (B) `(α : Type) → α → Nat → MyList α`

-- (C) `MyList Bool`

-- (D) Ill-typed

-- From now on, we'll use Lean's built-in `List` type and its associated
-- notation. The built-in `List` is defined just like our `MyList` above, but
-- with notation `[]` for `List.nil`, `::` for `List.cons`, and `[1, 2, 3]`
-- for list literals. The `++` operator is list append. The type arguments to
-- the list constructors are implicit.

-- Using Lean's built-in list notations, we can now write lists in the natural
-- way:

example : List Nat := [1, 2, 3]

-- #### Type Annotation Inference

-- Let's write the definition of `myRepeat` again, but this time we won't
-- specify the type of the parameter `α`. Will Lean still accept it?

def myRepeat' α (x : α) (count : Nat) : List α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (myRepeat' α x count')

-- Indeed it will. Lean infers that `α` is a type.

#check myRepeat'

-- myRepeat'.{u_1} (α : Type u_1) (x : α) (count : Nat) : List α

-- The generated `u_1` is part of Lean's bookkeeping for treating types more
-- generally. We will not need to interpret names like this for now — you can
-- ignore them when they appear in Lean's output unless we explicitly call
-- attention to them.

-- Lean was able to use *type inference* to deduce what the type of `α` must
-- be, based on how it is used. Since `α` is an argument to `List`, it must be
-- a `Type`, since `List` expects a `Type` as its argument.

-- This facility means we don't always have to write explicit type annotations
-- everywhere, although explicit type annotations can still be quite useful as
-- documentation, so we will continue to use them much of the time.

-- #### Type Argument Synthesis

-- To use a polymorphic function, we need to pass it one or more types in
-- addition to its other arguments. For example, the recursive call in the
-- body of the `myRepeat` function above must pass along the type `α`. But
-- since the second argument to `myRepeat` is an element of `α`, it seems
-- entirely obvious that the first argument can only be `α` — why should we
-- have to write it explicitly?

-- Fortunately, Lean permits us to avoid this kind of redundancy. In place of
-- any type argument we can write a "hole" `_`, which can be read as "Please
-- try to figure out for yourself what belongs here." More precisely, when
-- Lean encounters a `_`, it will attempt to *unify* all locally available
-- information — the type of the function being applied, the types of the
-- other arguments, and the type expected by the context in which the
-- application appears — to determine what concrete type should replace the
-- `_`.

-- Using holes, the `myRepeat'` function can be rewritten like this:

def myRepeat'' (α : Type) (x : α) (count : Nat) : List α :=
  match count with
  | 0 => []
  | count' + 1 => x :: myRepeat'' _ x count'

-- Alternatively, we can declare an argument to be implicit when defining the
-- function itself, by surrounding it in curly braces instead of parentheses.
-- For example:

def myRepeat''' {α : Type} (x : α) (count : Nat) : List α :=
  match count with
  | 0 => []
  | count' + 1 => x :: myRepeat''' x count'

-- By making the type argument implicit, we no longer need to provide it to
-- the recursive call to `myRepeat'''`. Indeed, it would be invalid to provide
-- one, because Lean is not expecting it. For each implicit parameter, Lean
-- automatically inserts a hidden hole `_` argument for us, which is then
-- inferred as usual.

-- #### Supplying Type Arguments Explicitly

-- One small problem with implicit arguments is that, once in a while, Lean
-- does not have enough local information to determine a type argument; in
-- such cases, we need to tell Lean the type explicitly. For example:

-- This fails because Lean can't figure out the type of the empty list:
-- `def mynil := []` — error: type not known We can fix this with an explicit
-- type annotation:

-- We can use the `@` prefix to supply the type argument explicitly. The `@`
-- makes all implicit arguments of a function explicit:

#check @List.nil

def myNil' := @List.nil Nat

-- @List.nil : {α : Type u_1} → List α

-- _Quiz:_

-- Which type does Lean assign to the following expression? (The square
-- brackets in this quiz and the following ones are list brackets.)

--   [1, 2, 3]

-- (A) `List Nat`

-- (B) `List Bool`

-- (C) `Bool`

-- (D) No type can be assigned

-- _Quiz:_

-- What about this one?

--   [3 + 4] ++ []

-- (A) `List Nat`

-- (B) `List Bool`

-- (C) `Bool`

-- (D) No type can be assigned

-- _Quiz:_

-- What about this one?

--   (true && false) :: []

-- (A) `List Nat`

-- (B) `List Bool`

-- (C) `Bool`

-- (D) No type can be assigned

-- _Quiz:_

-- What about this one?

--   [1, []]

-- (A) `List Nat`

-- (B) `List (List Nat)`

-- (C) `List Bool`

-- (D) No type can be assigned

-- _Quiz:_

-- What about this one?

--   [[1], []]

-- (A) `List Nat`

-- (B) `List (List Nat)`

-- (C) `List Bool`

-- (D) No type can be assigned

-- _Quiz:_

-- And what about this one?

--   [1] :: [[]]

-- (A) `List Nat`

-- (B) `List (List Nat)`

-- (C) `List Bool`

-- (D) No type can be assigned

-- _Quiz:_

-- This one?

--   @List.nil Bool

-- (A) `List Nat`

-- (B) `List (List Nat)`

-- (C) `List Bool`

-- (D) No type can be assigned

-- ### Exercise (2 stars): mumble_grumble (Optional, manually graded) ⭐⭐

-- Consider the following two inductively defined types.

inductive Mumble : Type where
  | a : Mumble
  | b (x : Mumble) (y : Nat) : Mumble
  | c : Mumble

inductive Grumble (α : Type) : Type where
  | d (m : Mumble) : Grumble α
  | e (x : α) : Grumble α

-- Which of the following are well-typed elements of `Grumble α` for some type
-- `α`? (Add YES or NO to each line.)

-- - `Grumble.d (Mumble.b Mumble.a 5)`
-- - `@Grumble.d Mumble (Mumble.b Mumble.a 5)`
-- - `@Grumble.d Bool (Mumble.b Mumble.a 5)`
-- - `@Grumble.e Bool true`
-- - `@Grumble.e Mumble (Mumble.b Mumble.c 0)`
-- - `@Grumble.e Bool (Mumble.b Mumble.c 0)`
-- - `Mumble.c`

-- - YES — `Grumble.d (Mumble.b Mumble.a 5)`
-- - YES — `@Grumble.d Mumble (Mumble.b Mumble.a 5)`
-- - YES — `@Grumble.d Bool (Mumble.b Mumble.a 5)`
-- - YES — `@Grumble.e Bool true`
-- - YES — `@Grumble.e Mumble (Mumble.b Mumble.c 0)`
-- - NO — `@Grumble.e Bool (Mumble.b Mumble.c 0)`
-- - NO — `Mumble.c`

-- #### Exercises

def List.rev {α : Type} (l : List α) : List α :=
  match l with
  | .nil => .nil
  | .cons h t => rev t ++ (.cons h .nil)

theorem rev_nil {α : Type} : ([] : List α).rev = [] := by rfl

theorem rev_cons {α : Type} {x : α} {l : List α} :
    (x :: l).rev = l.rev ++ [x] := by rfl

-- ### Exercise (2 stars): poly_exercises ⭐⭐

-- Here are a few simple exercises, just like ones in the Lists chapter, for
-- practice with polymorphism. Complete the proofs below. You will likely find
-- useful the following characterizing lemmas for `List.append` in Lean
-- standard library:

#check List.nil_append
#check List.cons_append

-- List.cons_append.{u} {α : Type u} {a : α} {as bs : List α} : a :: as ++ bs = a :: (as ++ bs)

-- List.nil_append.{u} {α : Type u} (as : List α) : [] ++ as = as

theorem append_nil {α : Type} {l : List α} :
    l ++ [] = l := by
  sorry

theorem append_assoc {α : Type} {l₁ l₂ l₃ : List α} :
    l₁ ++ l₂ ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  sorry

theorem append_length {α : Type} {l₁ l₂ : List α} :
    (l₁ ++ l₂).length = l₁.length + l₂.length := by
  sorry

attribute [autogradedProof 0.5] append_nil

attribute [autogradedProof 1] append_assoc

attribute [autogradedProof 0.5] append_length

-- ### Exercise (2 stars): more_poly_exercises ⭐⭐

-- Here are some slightly more interesting ones...

theorem reverse_append {α : Type} {l₁ l₂ : List α} :
    (l₁ ++ l₂).rev = l₂.rev ++ l₁.rev := by
  sorry

theorem reverse_reverse {α : Type} (l : List α) :
    l.rev.rev = l := by
  sorry

attribute [autogradedProof 1] reverse_append

attribute [autogradedProof 1] reverse_reverse

-- ### Polymorphic Pairs

-- Like `inductive`s, `structure`s can also be made polymorphic. If we
-- generalize the definition `NatProd` of pairs of natural numbers from last
-- chapter, we get polymorphic pairs, often called *products*:

structure MyProd (α β : Type) where
  fst : α
  snd : β

-- Lean's built-in product type `Prod` provides a `Prod.mk` constructor, and
-- `Prod.fst` and `Prod.snd` functions for accessing the first and second
-- components of the pair. It also has special syntax for creating products:

#check (1, true)
#eval (1, true).fst
#eval (1, true).snd

-- (1, true) : Nat × Bool

-- 1

-- true

-- You can also use `.1` instead of `.fst` and `.2` instead of `.snd`:

example : (3, 5).1 = 3 := by rfl
example : (3, 5).2 = 5 := by rfl

-- Lean writes the product type `Prod α β` as `α × β`. In VS Code you can type
-- `\times` or `\x` to enter the `×` symbol.

-- It is easy at first to get `(x, y)` and `α × β` confused. Remember that
-- `(x, y)` is a *value* built from two other values, while `α × β` is a
-- *type* built from two other types. If `x` has type `α` and `y` has type
-- `β`, then `(x, y)` has type `α × β`.

-- The following function takes two lists and combines them into a list of
-- pairs.

def zip {α β : Type} (l₁ : List α) (l₂ : List β) : List (α × β) :=
  match l₁, l₂ with
  | [], _ => []
  | _, [] => []
  | x :: l₁', y :: l₂' => (x, y) :: zip l₁' l₂'

theorem zip_nil_right {α β : Type} (l₂ : List β) : zip [] l₂ = ([] : List (α × β)) := by rfl

theorem zip_nil_left {α β : Type} (l₁ : List α) : zip l₁ [] = ([] : List (α × β)) := by
   cases l₁ <;> rfl
theorem zip_cons_cons {α β : Type} {x : α} {y : β} {l₁ : List α} {l₂ : List β} :
   zip (x :: l₁) (y :: l₂) = (x, y) :: zip l₁ l₂ := by rfl

-- ### Exercise (1 star): zip_checks (Optional) ⭐

-- Try answering the following questions on paper and checking your answers in
-- Lean:

-- - What is the type of `zip` (i.e., what does `#check @zip` print?)

-- - What does

--   `#eval zip [1, 2] [false, false, true, true]`

--   print?

-- ### Exercise (2 stars): unzip ⭐⭐

-- The function `unzip` goes in the other direction from `zip`: it takes a
-- list of pairs and returns a pair of lists.

-- Fill in the definition of `unzip` below. Make sure it that passes the given
-- unit test, and that you can prove the simplification rules about it.

def unzip {α : Type} {β : Type} (l : List (α × β)) : List α × List β := sorry

theorem unzip_nil {α β : Type} : unzip [] = (([], []) : List α × List β) := sorry

theorem unzip_cons_fst {α β : Type} {x : α} {y : β} {l : List (α × β)} :
   (unzip ((x, y) :: l)).fst = x :: (unzip l).fst := sorry

theorem unzip_cons_snd {α β : Type} {x : α} {y : β} {l : List (α × β)} :
   (unzip ((x, y) :: l)).snd = y :: (unzip l).snd := sorry

theorem unzip_test1 : unzip [(1, false), (2, false)] = ([1, 2], [false, false]) := sorry

attribute [autogradedProof 0.25] unzip_nil unzip_cons_fst unzip_cons_snd unzip_test1

-- ### Polymorphic Options

-- Our last polymorphic type for now is *polymorphic options*. Lean's standard
-- library provides `Option α`, with constructors `none` and `some`. (We
-- already saw `NatOption` in the Lists chapter.) Let's briefly look at the
-- definition:

namespace OptionPlayground

inductive Option (α : Type) : Type where
  | none : Option α
  | some (x : α) : Option α

end OptionPlayground

-- We can now rewrite the `nth?` function so that it works with any type of
-- list.

def nth? {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | x :: l' => match n with
    | 0 => some x
    | n' + 1 => nth? l' n'

example : nth? [4, 5, 6, 7] 0 = some 4 := by rfl
example : nth? [[1], [2]] 1 = some [2] := by rfl
example : nth? [true] 2 = none := by rfl

-- ### Exercise (1 star): head?_poly (Optional) ⭐

-- Complete the definition of a polymorphic version of the `head?` function
-- from the last chapter. Be sure that it passes the unit tests below.

def head? {α : Type} (l : List α) : Option α := sorry

theorem head?_nil {α : Type} : head? ([] : List α) = none := sorry

theorem head?_cons {α : Type} {head : α} {tail : List α} : head? (head :: tail) = some head :=
  sorry

theorem test_head?1 : head? [1, 2] = some 1 := sorry

attribute [autogradedProof 0.5] test_head?1

theorem test_head?2 : head? [[1], [2]] = some [1] := sorry

attribute [autogradedProof 0.5] test_head?2

-- ## Functions as Data

-- Like most modern programming languages — especially other "functional"
-- languages, including OCaml, Haskell, Racket, Scala, Clojure, etc. — Lean
-- treats functions as first-class citizens, allowing them to be passed as
-- arguments to other functions, returned as results, stored in data
-- structures, etc.

-- ### Higher-Order Functions

-- Functions that manipulate other functions are often called *higher-order*
-- functions. Here's a simple one:

def doIt3Times {α : Type} (f : α → α) (x : α) : α :=
  f (f (f x))

-- The argument `f` here is itself a function (from `α` to `α`); the body of
-- `doIt3Times` applies `f` three times to some value `x`.

#check doIt3Times

example : doIt3Times Nat.minusTwo 9 = 3 := by rfl

example : doIt3Times not true = false := by rfl

-- doIt3Times {α : Type} (f : α → α) (x : α) : α

-- ### Filter

-- Here is a more useful higher-order function, taking a list of `α`s and a
-- *predicate* on `α` (a function from `α` to `Bool`) and "filtering" the list
-- to yield a new list containing just those elements for which the predicate
-- returns `true`.

def filter {α : Type} (test : α → Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | x :: l' =>
    bif test x then x :: filter test l'
    else filter test l'

-- For example, if we apply `filter` to the predicate `Nat.even` and a list of
-- numbers, it returns a list containing just the even members.

example : filter Nat.even [1, 2, 3, 4] = [2, 4] := by rfl

-- Here are some further examples and properties of `filter`.

def isLength1 {α : Type} (l : List α) : Bool :=
  l.length == 1

example : filter isLength1
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

theorem filter_nil {α : Type} {test : α → Bool} : filter test [] = [] := by rfl

theorem filter_cons_of_pos {α : Type} {test : α → Bool} {x : α}
    {l : List α} (h : test x = true) :
    filter test (x :: l) = x :: filter test l := by
  dsimp [filter]
  rw [h]
  dsimp

theorem filter_cons_of_neg {α : Type} {test : α → Bool} {x : α}
    {l : List α} (h : test x = false) :
    filter test (x :: l) = filter test l := by
   dsimp [filter]
   rw [h]
   dsimp

-- You might have noticed that `filter_cons_of_pos` and `filter_cons_of_neg`
-- have implicit parameters, such as `head` and `tail`, that do not have type
-- `Type` like `α` does. As it turns out, Lean allows *any* parameter to be
-- implicit, not just those of type `Type`. This is a standard Lean convention
-- for lemmas that are likely to be used by `rw` or `dsimp` when their values
-- can be inferred by unification.

-- For example, suppose you were using this theorem to rewrite
-- `filter Nat.even (3 :: rest)`. Matching that expression against the
-- theorem's left-hand side `filter test (head :: tail)` establishes that
-- `test = Nat.even`, `head = 3`, `tail = rest`, and `α = Nat`. By making
-- these arguments implicit, Lean automatically inserts a hole `_` for each of
-- them when you apply the theorem, just as with implicit parameters of type
-- `Type`, so they can be inferred from the context.

-- Note that `h : test head` is not implicit, it's explicit. That's because it
-- cannot be solved by unification, i.e., Lean can't prove that
-- `Nat.even 3 = true` that way. It's a general proof obligation.

-- We'll follow the Lean standard convention from now on.

-- We can use `filter` to give a concise version of the `countOddMembers`
-- function from the Lists chapter.

def countOddMembers (l : List Nat) : Nat := (filter Nat.odd l).length

example : countOddMembers [1, 0, 3, 1, 4, 5] = 4 := by rfl
example : countOddMembers [0, 2, 4] = 0 := by rfl
example : countOddMembers [] = 0 := by rfl

-- ### Anonymous Functions

-- It is arguably a little sad, in the example just above, to be forced to
-- define the function `isLength1` and give it a name just to be able to pass
-- it as an argument to `filter`, since we will probably never use it again.
-- Indeed, when using higher-order functions, we *often* want to pass as
-- arguments "one-off" functions that we will never use again; having to give
-- each of these functions a name would be tedious.

-- Fortunately, there is a better way. We can construct a function "on the
-- fly" without declaring it at the top level or giving it a name. Lean
-- provides two syntaxes for anonymous functions:

-- - `fun n => n * n` — traditional lambda syntax
-- - `(· * ·)` — "term with holes" syntax, where `·` marks arguments

example : doIt3Times (fun n => n * n) 2 = 256 := by rfl

-- The expression `fun n => n * n` can be read as "the function that, given a
-- number `n`, yields `n * n`."

-- Lean also supports a shorter notation using `·` as a placeholder for the
-- argument:

example : doIt3Times (· + 1) 0 = 3 := by rfl

-- Here is the `filter` example, rewritten to use an anonymous function.

example : filter (fun l => l.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

example : filter (·.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

-- ### Exercise (2 stars): filter_even_gt7 ⭐⭐

-- Use `filter` (instead of a recursive `def`) to write a Lean function
-- `filterEvenGt7` that takes a list of natural numbers as input and returns a
-- list of just those that are even and greater than `7`.

def filterEvenGt7 (l : List Nat) : List Nat := sorry

theorem test_filterEvenGt7_1 : filterEvenGt7 [1, 2, 6, 9, 10, 3, 12, 8] = [10, 12, 8] := sorry

theorem test_filterEvenGt7_2 : filterEvenGt7 [5, 2, 6, 19, 129] = [] := sorry

attribute [autogradedProof 1] test_filterEvenGt7_1 test_filterEvenGt7_2

-- ### Exercise (3 stars): partition ⭐⭐⭐

-- Use `filter` to write a Lean function `partition` that, given a type `α`, a
-- predicate of type `α → Bool` and a `List α`, should return a pair of lists.
-- The first member of the pair is the sublist of the original list containing
-- the elements that satisfy the test, and the second is the sublist
-- containing those that fail the test. The order of elements in the two
-- sublists should be the same as their order in the original list.

def partition {α : Type} (test : α → Bool) (l : List α) : List α × List α := sorry

theorem test_partition1 : partition (· % 2 != 0) [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) := sorry
theorem test_partition2 : partition (fun _ => false) [5, 9, 0] = ([], [5, 9, 0]) := sorry

attribute [autogradedProof 1.5] test_partition1 test_partition2

-- ### Map

-- Another handy higher-order function is called `map`.

def map {α β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | head :: tail => f head :: map f tail

-- It takes a function `f` and a list `l = [n1, n2, n3, ...]` and returns the
-- list `[f n1, f n2, f n3, ...]`, where `f` has been applied to each element
-- of `l` in turn. For example:

example : map (· + 3) [2, 0, 2] = [5, 3, 5] := by rfl

-- The element types of the input and output lists need not be the same, since
-- `map` takes *two* type arguments, `α` and `β`; it can thus be applied to a
-- list of numbers and a function from numbers to booleans to yield a list of
-- booleans:

example : map Nat.odd [2, 1, 2, 5] = [false, true, false, true] := by rfl

-- It can even be applied to a list of numbers and a function from numbers to
-- *lists* of booleans to yield a *list of lists* of booleans:

example : map (fun n => [n.even, n.odd]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]] := by rfl

-- _Quiz:_

-- Recall the definition of `map`:

sf_recall
  def map {α β : Type} (f : α → β) (l : List α) : List β :=
    match l with
    | [] => []
    | head :: tail => f head :: map f tail

-- What is the type of `@map`?

-- (A) `{α β : Type} → α → β → List α → List β`

-- (B) `α → β → List α → List β`

-- (C) `{α β : Type} → (α → β) → List α → List β`

-- (D) `{α : Type} → (α → α) → List α → List α`

-- As usual, we define the following simplification rules for `map`:

theorem map_nil {α : Type} {β : Type} {f : α → β} : map f [] = [] := by rfl

theorem map_cons {α : Type} {β : Type} {f : α → β} {x : α} {l : List α} :
    map f (x :: l) = f x :: map f l := by rfl

-- ### Exercise (3 stars): map_rev ⭐⭐⭐

-- Show that `map` and `List.rev` commute. (Hint: You may need to define an
-- auxiliary lemma.)

-- FILL IN HERE

theorem map_rev {α : Type} {β : Type} {f : α → β} {l : List α} :
    map f l.rev = (map f l).rev := by
  sorry

attribute [autogradedProof 3] map_rev

-- ### Exercise (2 stars): flat_map ⭐⭐

-- The function `map` maps a `List α` to a `List β` using a function of type
-- `α → β`. We can define a similar function, `flatMap`, which maps a `List α`
-- to a `List β` using a function `f` of type `α → List β`. Your definition
-- should work by 'flattening' the results of `f`, like so:

--   flatMap (fun n => [n, n + 1, n + 2]) [1, 5, 10]
--     = [1, 2, 3, 5, 6, 7, 10, 11, 12]

def flatMap {α β : Type} (f : α → List β) (l : List α) : List β := sorry

theorem test_flatMap : flatMap (fun n => [n, n, n]) [1, 5, 4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4] := sorry

attribute [autogradedProof 2] test_flatMap

theorem flatMap_nil {α : Type} {β : Type} (f : α → List β) : flatMap f [] = [] :=
   sorry

theorem flatMap_cons {α : Type} {β : Type} (f : α → List β) h t :
   flatMap f (h :: t) = f h ++ flatMap f t := sorry

-- Lists are not the only inductive type for which `map` makes sense. Here is
-- a `map` for the `Option` type:

def optionMap {α : Type} {β : Type} (f : α → β) (x? : Option α) : Option β :=
  match x? with
  | none => none
  | some x => some (f x)

-- ### Exercise (2 stars): implicit_args (Optional) ⭐⭐

-- The definitions and uses of `filter` and `map` use implicit arguments in
-- many places. Replace the curly braces around the implicit arguments with
-- explicit parentheses, and then fill in explicit type parameters where
-- necessary and use Lean to check that you've done so correctly. (This
-- exercise is not to be turned in; it is probably easiest to do it on a
-- *copy* of this file that you can throw away afterwards.)

-- ### Fold

-- An even more powerful higher-order function is `fold`. It is the
-- inspiration for the "reduce" operation that lies at the heart of Google's
-- map/reduce distributed programming framework.

def fold {α : Type} {β : Type} (f : α → β → β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | a :: l => f a (fold f l b)

-- Intuitively, the behavior of the `fold` operation is to insert a given
-- binary operator `f` between every pair of elements in a given list. For
-- example, `fold (· + ·) [1, 2, 3, 4]` intuitively means `1 + 2 + 3 + 4`. To
-- make this precise, we also need a "starting element" that serves as the
-- initial second input to `f`. So, for example,

--   fold (· + ·) [1, 2, 3, 4] 0

-- yields

--   1 + (2 + (3 + (4 + 0))).

example : fold (· && ·) [true, true, false, true] true = false := by rfl

example : fold (· * ·) [1, 2, 3, 4] 1 = 24 := by rfl

example : fold (· ++ ·) [[1], [], [2, 3], [4]] [] = [1, 2, 3, 4] := by rfl

example : fold (fun l n => l.length + n) [[1], [], [2, 3, 2], [4]] 0 = 5 := by rfl

theorem fold_nil {α : Type} {β : Type} {f : α → β → β} {b : β} : fold f [] b = b := by rfl

theorem fold_cons {α : Type} {β : Type} {f : α → β → β} {a : α} {l : List α} {b : β} :
    fold f (a :: l) b = f a (fold f l b) := by rfl

-- _Quiz:_

-- Here is the definition of `fold` again:

sf_recall
  def fold {α β : Type} (f : α → β → β) (l : List α) (b : β) : β :=
    match l with
    | [] => b
    | a :: l => f a (fold f l b)

-- What is the type of `@fold`?

-- (A) `{α β : Type} → (α → β → β) → List α → β → β`

-- (B) `α → β → (α → β → β) → List α → β → β`

-- (C) `{α β : Type} → α → β → β → List α → β → β`

-- (D) `α → β → α → β → β → List α → β → β`

-- _Quiz:_

-- What does `fold (· + ·) [1, 2, 3, 4] 0` simplify to?

-- (A) `[1, 2, 3, 4]`

-- (B) `0`

-- (C) `10`

-- (D) `[3, 7, 0]`

-- ### Exercise (1 star): fold_types_different (Optional, manually graded) ⭐

-- Observe that the type of `fold` is parameterized by *two* type variables,
-- `α` and `β`, and the parameter `f` is a binary operator that takes an `α`
-- and a `β` and returns a `β`. The examples above show one instance where it
-- is useful for `α` and `β` to be different. Can you think of any others?

-- ### Functions That Construct Functions

-- Most of the higher-order functions we have talked about so far take
-- functions as arguments. Let's look at some examples that involve
-- *returning* functions as the results of other functions. To begin, here is
-- a function that takes a value `x` (drawn from some type `α`) and returns a
-- function from `Nat` to `α` that yields `x` whenever it is called, ignoring
-- its `Nat` argument.

def constFun {α : Type} (x : α) : Nat → α :=
  fun _ => x

def fTrue := constFun true

example : fTrue 0 = true := by rfl

example : constFun 5 99 = 5 := by rfl

-- In fact, the multiple-argument functions we have already seen are also
-- examples of passing functions as data. To see why, recall the type of
-- addition:

#check Nat.add

-- Nat.add : Nat → Nat → Nat

def plus3 := Nat.add 3
#check plus3

example : plus3 4 = 7 := by rfl
example : doIt3Times plus3 0 = 9 := by rfl
example : doIt3Times (Nat.add 3) 0 = 9 := by rfl

-- plus3 : Nat → Nat

-- Similarly, we can write:

def fold_plus : List Nat → Nat → Nat :=
  fold (· + ·)

#check fold_plus

-- fold_plus : List Nat → Nat → Nat

-- What's happening here is called *partial application*. In Lean, the type
-- constructor `→` is right-associative, meaning a function type like
-- `α → β → γ` is parsed like `α → (β → γ)`, or "a function from `α` to a
-- function from `β` to `γ`."

-- We can think of `fold` not as a three-argument function, but as a
-- one-argument function that:

-- 1. Takes an argument `f` of type `α → β → β`
-- 2. Returns a function of type `List α → β → β` that "remembers" `f`

-- When we write `fold (· + ·)`, we're giving `fold` its first argument,
-- `(· + ·)`, and getting back a specialized function that can sum up the
-- elements of any list of numbers. This new function still expects two more
-- arguments: a list and a starting value.

-- ## Additional Exercises

-- ### Exercise (2 stars): fold_length ⭐⭐

-- Many common functions on lists can be implemented in terms of `fold`. For
-- example, here is an alternative definition of `List.length`:

def foldLength {α : Type} (l : List α) : Nat :=
  fold (fun _ n => n + 1) l 0

example : foldLength [4, 7, 0] = 3 := by rfl

-- Prove the correctness of `foldLength`.

-- Hint: It may help to use `dsimp [foldLength, fold]` to unfold the
-- definition.

theorem fold_length_correct {α : Type} {l : List α} :
    foldLength l = l.length := by
  sorry

attribute [autogradedProof 2] fold_length_correct

-- ### Exercise (3 stars): fold_map (manually graded) ⭐⭐⭐

-- We can also define `map` in terms of `fold`. Finish `foldMap` below.

def foldMap {α β : Type} (f : α → β) (l : List α) : List β := sorry

-- Write down a theorem `fold_map_correct` stating that `foldMap` is correct,
-- and prove it in Lean.

-- FILL IN HERE

-- ### Exercise (2 stars): currying (Advanced) ⭐⭐

-- The type `α → β → γ` can be read as describing functions that take two
-- arguments, one of type `α` and another of type `β`, and return an output of
-- type `γ`. Recall from our discussion of partial application that this type
-- is written `α → (β → γ)` when fully parenthesized. That is, if we have
-- `f : α → β → γ`, and we give `f` an input of type `α`, it will give us as
-- output a function of type `β → γ`. If we then give that function an input
-- of type `β`, it will return an output of type `γ`. That is, every function
-- in Lean takes only one input, but some functions return a function as
-- output. This is precisely what enables partial application, as we saw above
-- with `plus3`.

-- By contrast, functions of type `α × β → γ` — which when fully parenthesized
-- is written `(α × β) → γ` — require their single input to be a pair. Both
-- arguments must be given at once; there is no possibility of partial
-- application.

-- It is possible to convert a function between these two types. Converting
-- from `α × β → γ` to `α → β → γ` is called *currying*, in honor of the
-- logician Haskell Curry. Converting from `α → β → γ` to `α × β → γ` is
-- called *uncurrying*.

-- We can define currying as follows:

def prodCurry {α β γ : Type} (f : α × β → γ) (x : α) (y : β) : γ := f (x, y)

-- As an exercise, define its inverse, `prodUncurry`. Then prove the theorems
-- below to show that the two are really inverses.

def prodUncurry {α β γ : Type} (f : α → β → γ) (p : α × β) : γ := sorry

-- As a (trivial) example of the usefulness of currying, we can use it to
-- shorten one of the examples that we saw above:

example : map (Nat.add 3) [2, 0, 2] = [5, 3, 5] := by rfl

-- Thought exercise: before looking at the output of the following commands,
-- can you calculate the types of `prodCurry` and `prodUncurry`?

#check @prodCurry
#check @prodUncurry

-- @prodCurry : {α β γ : Type} → (α × β → γ) → α → β → γ

-- @prodUncurry : {α β γ : Type} → (α → β → γ) → α × β → γ

theorem uncurry_curry {α β γ : Type} {x : α} {y : β} {f : α → β → γ} :
    prodCurry (prodUncurry f) x y = f x y := by
  sorry

theorem curry_uncurry {α β γ : Type} {p : α × β} {f : α × β → γ} :
    prodUncurry (prodCurry f) p = f p := by
  sorry

attribute [autogradedProof 1] uncurry_curry curry_uncurry

-- ### Exercise (2 stars): nth_error_informal (Advanced, Optional, manually graded) ⭐⭐

-- Recall the definition of the `nth?` function:

sf_recall
  def nth? {α : Type} (l : List α) (n : Nat) : Option α :=
    match l with
    | [] => none
    | x :: l' => match n with
      | 0 => some x
      | n' + 1 => nth? l' n'

-- Write a careful informal proof of the following theorem:

--   ∀ (l : List α) (n : Nat), l.length = n → nth? l n = none

-- Make sure to state the induction hypothesis *explicitly*.

-- Theorem: For all types `α`, lists `l`, and natural numbers `n`, if
-- `l.length = n` then `nth? l n = none`.

-- Proof: By induction on `l`. There are two cases to consider:

-- - If `l = []`, we must show `nth? [] n = none`. This follows immediately from
--   the definition of `nth?`.

-- - Otherwise, `l = x :: l'` for some `x` and `l'`, and the induction
--   hypothesis tells us that `l'.length = n' → nth? l' n' = none`, for any
--   `n'`.

--   Let `n` be the length of `l`. We must show that `nth? (x :: l') n = none`.

--   But we know that `n = l.length = (x :: l').length = l'.length + 1`. So it's
--   enough to show `nth? l' l'.length = none`, which follows directly from the
--   induction hypothesis, picking `l'.length` for `n'`.

-- ### Church Numerals (Advanced)

-- The following exercises explore an alternative way of defining natural
-- numbers using the *Church numerals*, which are named after their inventor,
-- the mathematician Alonzo Church. We can represent a natural number `n` as a
-- function that takes a function `f` as a parameter and returns `f` iterated
-- `n` times.

namespace Church

def CNat := ∀ (α : Type), (α → α) → α → α

-- Let's see how to write some numbers with this notation. Iterating a
-- function once should be the same as just applying it. Thus:

def one : CNat :=
  fun (α : Type) (f : α → α) (x : α) => f x

-- Similarly, `two` should apply `f` twice to its argument:

def two : CNat :=
  fun (α : Type) (f : α → α) (x : α) => f (f x)

-- Defining `zero` is somewhat trickier: how can we "apply a function zero
-- times"? The answer is actually simple: just return the argument untouched.

def zero : CNat :=
  fun (α : Type) (_ : α → α) (x : α) => x

-- More generally, a number `n` can be written as
-- `fun α f x => f (f ... (f x) ...)`, with `n` occurrences of `f`. Let's
-- informally notate that as `fun α f x => f^n x`, with the convention that
-- `f^0 x` is just `x`. Note how the `doIt3Times` function we've defined
-- previously is actually just the Church representation of 3.

def three : CNat := @doIt3Times

-- So `n α f x` represents "do it `n` times", where `n` is a Church numeral
-- and "it" means applying `f` starting with `x`.

-- Another way to think about the Church representation is that function `f`
-- represents the successor operation on `α`, and value `x` represents the
-- zero element of `α`. We could even rewrite with those names to make it
-- clearer:

def zero' : CNat :=
  fun (α : Type) (_ : α → α) (zero : α) => zero
def one' : CNat :=
  fun (α : Type) (succ : α → α) (zero : α) => succ zero
def two' : CNat :=
  fun (α : Type) (succ : α → α) (zero : α) => succ (succ zero)

-- If we passed in `Nat.succ` as `succ` and `0` as `zero`, we'd even get the
-- Peano naturals as a result:

example : zero Nat Nat.succ 0 = 0 := by rfl
example : one  Nat Nat.succ 0 = 1 := by rfl
example : two  Nat Nat.succ 0 = 2 := by rfl

-- One very interesting implication of the Church numerals is that we don't
-- strictly need the natural numbers to be built-in to a functional
-- programming language, or even to be definable with an inductive data type.
-- It's possible to represent them purely (if not efficiently) with functions.

-- Of course, it's not enough just to "represent" numerals; we need to be able
-- to do arithmetic with the representation. Show that we can by completing
-- the definitions of the following functions. Make sure that the
-- corresponding unit tests pass by proving them with `rfl`.

-- ### Exercise (2 stars): church_scc (Advanced) ⭐⭐

-- Define a function that computes the successor of a Church numeral. Given a
-- Church numeral `n`, its successor `scc n` should iterate its function
-- argument once more than `n`. That is, given `fun X f x => f^n x` as input,
-- `scc` should produce `fun X f x => f^(n+1) x` as output. In other words, do
-- it `n` times, then do it once more.

def scc (n : CNat) : CNat := sorry

example : scc zero = one := sorry
theorem scc_2 : scc one = two := sorry
theorem scc_3 : scc two = three := sorry

attribute [autogradedProof 1] Church.scc_2 Church.scc_3

-- ### Exercise (3 stars): church_plus (Advanced) ⭐⭐⭐

-- Define a function that computes the addition of two Church numerals. Given
-- `fun X f x => f^n x` and `fun X f x => f^m x` as input, `plus` should
-- produce `fun X f x => f^(n + m) x` as output. In other words, do it `n`
-- times, then do it `m` more times.

-- Hint: the "zero" argument to a Church numeral need not be just `x`.

def plus (n m : CNat) : CNat := sorry

theorem plus_1 : plus zero one = one := sorry
theorem plus_2 : plus two three = plus three two := sorry
theorem plus_3 : plus (plus two two) three = plus one (plus three three) := sorry

attribute [autogradedProof 1] Church.plus_1 Church.plus_2 Church.plus_3

-- ### Exercise (3 stars): church_mult (Advanced) ⭐⭐⭐

-- Define a function that computes the multiplication of two Church numerals.

-- Hint: the "successor" argument to a Church numeral need not be just `f`.

-- Warning: Lean will not let you pass `CNat` itself as the type `α` argument
-- to a Church numeral; you will get a "sort mismatch" error between `Type 1`
-- and `Type 2`. Don't worry too much about what this means right now, but
-- know that this is Lean's way of preventing a paradox in which a type
-- contains itself. So leave the type argument unchanged.

def mult (n m : CNat) : CNat := sorry

theorem mult_1 : mult one one = one := sorry
theorem mult_2 : mult zero (plus three three) = zero := sorry
theorem mult_3 : mult two three = plus three three := sorry

attribute [autogradedProof 1] Church.mult_1 Church.mult_2 Church.mult_3

-- ### Exercise (3 stars): church_exp (Advanced) ⭐⭐⭐

-- Exponentiation:

-- Define a function that computes the exponentiation of two Church numerals.

-- Hint: the type argument to a Church numeral need not just be `α`. Finding
-- the right type can be tricky.

def exp (n m : CNat) : CNat := sorry

theorem exp_1 : exp two two = plus two two := sorry
theorem exp_2 : exp three zero = one := sorry
theorem exp_3 : exp three two = plus (mult two (mult two two)) one := sorry

attribute [autogradedProof 1] Church.exp_1 Church.exp_3 Church.exp_2

end Church


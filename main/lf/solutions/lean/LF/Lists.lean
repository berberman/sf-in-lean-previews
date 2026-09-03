import LF.Induction
import LF.UsingLean

import SFLCompat

--  # Lists: Working with Structured Data

--  This chapter introduces basic data structures and functions for working
--  with them. We place all these definitions in the `Lists` namespace to
--  avoid name clashes with Lean's standard library and with definitions
--  from other chapters.

namespace Lists

--  ## Pairs of Numbers

--  Note to developers (Mike Hicks @mwhicks1):
--      This content is a redundant with what's in Basics, which introduces
--      the idea of tuple types and structures as shorthand for them. I
--      suspect we can drop most of the Basics content and rely on what's
--      here instead. If we do that, we can introduce the term "Tuple"
--      here.

--  In an `inductive` type definition, each constructor can take any number
--  of arguments -- none (as with `true` and `0`), one (as with
--  `Nat.succ`), or more than one (as with `Playground.Nibble` and the
--  following):

inductive NatProd where
  | pair (n1 n2 : Nat)

--  This declaration can be read: "The one and only way to construct a pair
--  of numbers is by applying the constructor `NatProd.pair` to two
--  arguments of type `Nat`."

#check (NatProd.pair 3 5)

--  Note to developers (Mike Hicks @mwhicks1):
--      I would have expected us to have `namespace NatProd` here when
--      defining the following functions, so we don't need qualifiers.
--      We've already full explained namespaces back in Basics. Some of the
--      text below mentions using the `NatProd` prefix specifically, but I
--      think you can drop it and it will stick work.

--  Functions for extracting the first and second components of a pair can
--  then be defined by pattern matching.

def NatProd.fst (p : NatProd) : Nat :=
  match p with
  | .pair x _ => x

def NatProd.snd (p : NatProd) : Nat :=
  match p with
  | .pair _ y => y

--  Defining these functions with the `NatProd` type name qualifying their
--  name allows us to use them with `.` notation:

example : (NatProd.pair 3 5).fst = 3 := by rfl

--  Since pairs will be used heavily in what follows, it will be convenient
--  to write them with angle bracket notation `⟨n, m⟩` instead of
--  `NatProd.pair n m`. This notation is built into Lean and is called
--  "anonymous constructor syntax". It is available for any inductive type
--  with a single constructor, as long as the expected type is declared or
--  can be inferred from the context.

example : (⟨3, 5⟩ : NatProd).fst = 3 := by rfl

--  The anonymous constructor can be used in both expressions and in
--  pattern matches.

def NatProd.fst' (p : NatProd) : Nat :=
  match p with
  | ⟨x, _⟩ => x

def NatProd.snd' (p : NatProd) : Nat :=
  match p with
  | ⟨_, y⟩ => y

def NatProd.swap (p : NatProd) : NatProd :=
  ⟨snd p, fst p⟩

--  Note that pattern-matching on a pair (with angle brackets: `⟨x, y⟩`) is
--  not to be confused with the "multiple pattern" syntax (with no
--  brackets: `x, y`) that we have seen previously. The above examples
--  illustrate pattern matching on a pair with elements `x` and `y`,
--  whereas, for example, the definition of `sub` for subtracting two
--  `Nat`s performs pattern matching on the values `n` and `m`:

def sub (n m : Nat) : Nat :=
  match n, m with
  | 0,        _        => 0
  | .succ _,  0        => n
  | .succ n', .succ m' => sub n' m'

--  The distinction is minor, but it is worth understanding that they are
--  not the same. For instance, the following definitions are ill-formed:

sf_expect_failure_in
  def bad_fst (p : NatProd) : Nat :=
    match p with
    | x, y => x

--  Output:
--    Too many patterns in match alternative: Expected 1, but found 2:
--      x, y

sf_expect_failure_in
  def bad_sub (n m : Nat) : Nat :=
    match n, m with
    | ⟨0,        _⟩        => 0
    | ⟨.succ _,  0⟩        => n
    | ⟨.succ n', .succ m'⟩ => sub n' m'

--  Output:
--    Invalid `⟨...⟩` notation: The expected type `Nat` has more than one constructor
--
--    Note: This notation can only be used when the expected type is an inductive type with a single constructor

--  As with the multi-argument `match n, m with` style used above in `sub`,
--  matching jointly on several values can combine what would otherwise be
--  several separate cases into a single match arm. This means the
--  simplification rules we define for such a function may not always match
--  one-to-one with the cases of its match construct.

--  A property like `p = ⟨p.fst, p.snd⟩` can be proved by exposing the
--  structure of the pair, either with `cases` or by destructuring in
--  `intro`.

theorem surjective_pairing : ∀ p : NatProd,
    p = ⟨p.fst, p.snd⟩ := by
  intro ⟨n, m⟩; rfl

theorem surjective_pairing_cases (p : NatProd) :
    p = ⟨p.fst, p.snd⟩ := by
  cases p; rfl

--  Notice that, unlike the behavior of `cases` on `Nat`s, where it
--  generates two subgoals, `cases` generates just one subgoal here. That's
--  because `NatProd`s can only be constructed in one way.

--  ### Exercise (1 star): snd_fst_is_swap ⭐

theorem snd_fst_is_swap (p : NatProd) :
    (⟨p.snd, p.fst⟩ : NatProd) = p.swap := by
  cases p; rfl

--  ### Exercise (1 star): fst_swap_is_snd (Optional) ⭐

theorem fst_swap_is_snd (p : NatProd) :
    p.swap.fst = p.snd := by
  cases p; rfl

--  ### Structures

--  Lean also provides a convenient way to define `inductive` structures
--  like pairs that have a single constructor but multiple ways to access
--  their data, using the `structure` keyword. The definition of `NatProd'`
--  below is equivalent to the `NatProd` definition from earlier, except
--  that Lean automatically generates the `fst` and `snd` accessors.

structure NatProd' where
  fst : Nat
  snd : Nat

#check (NatProd'.mk 3 5)
example : (NatProd'.mk 3 5).fst = 3 := by rfl
example : (⟨3, 5⟩ : NatProd').fst = 3 := by rfl

--  ## Lists of Numbers

--  Generalizing the definition of pairs, we can describe the type of
--  *lists* of numbers like this: "A list is either the empty list or else
--  a pair of a number and another list."

inductive NatList : Type where
  | nil
  | cons (n : Nat) (l : NatList)

--  By convention, we place the operations (functions) of an inductive type
--  inside the namespace implicitly created by that type's definition.

namespace NatList

--  As with pairs, it is useful to give lists a symbolic notation. The
--  following declarations allow us to use `::` as an infix `cons` operator
--  and square brackets as an "outfix" notation for constructing lists.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (List syntax)
--  We first define `::` as right-associative notation for `cons`, and then
--  define list notation as a *macro*, allowing us to write `[1, 2]`
--  instead of `1 :: 2 :: []`. The *unexpander* reverses the macro,
--  translating list syntax back to cons syntax.

scoped infixr:65 (priority := high) " :: " => cons
scoped macro (priority := high) "[" elems:term,* "]" : term => do
  elems.getElems.foldrM (``(cons $(⟨·⟩) $(⟨·⟩))) (← ``(nil))

@[scoped app_unexpander nil]
def unexpandNil : Lean.PrettyPrinter.Unexpander
  | `($_) => `([])

@[scoped app_unexpander cons]
def unexpandCons : Lean.PrettyPrinter.Unexpander
  | `($_ $x []) => `([$x])
  | `($_ $x [$xs,*]) => `([$x, $xs,*])
  | _ => throw ()
--  END DETAILS

--  Now these all mean exactly the same thing:

def mylist1 : NatList := 1 :: (2 :: (3 :: []))
def mylist2 : NatList := 1 :: 2 :: 3 :: []
def mylist3 : NatList := [1, 2, 3]

--  Let's define some functions on lists.

--  ### Replicate

--  Our first is the `replicate` function, which takes a number `n` and a
--  `count` and returns a list of length `count` in which every element is
--  `n`.

def replicate (n count : Nat) : NatList :=
  match count with
  | 0 => []
  | count' + 1 => n :: replicate n count'

--  Some simple facts about replication:

theorem replicate_zero (n : Nat) : replicate n 0 = [] := by rfl

theorem replicate_succ (n count : Nat) :
  replicate n (count + 1) = n :: replicate n count := by rfl

--  ### Length

--  The `length` function calculates the length of a list.

def length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => (length t) + 1

--  Some simple facts about list lengths:

theorem length_nil : [].length = 0 := by rfl

theorem length_cons (n : Nat) (l : NatList) :
  (n :: l).length = l.length + 1 := by rfl

--  ### Append

--  The `append` function appends (concatenates) two lists.

def append (l₁ l₂ : NatList) : NatList :=
  match l₁ with
  | [] => l₂
  | h :: t => h :: append t l₂

--  ### Type Classes and Overloading Notation

--  Note to developers (Benjamin Pierce @bcpierce00):
--      One word, or two?

--  In Lean, notation like `++`, `==`, and `+` is not hardwired to
--  particular definitions, which is the way we have been defining notation
--  so far. Instead, Lean defines this notation using *type classes* — a
--  mechanism that lets us *overload* operations for different types.
--
--  We'll learn more about type classes in chapter Typeclasses. For now,
--  the key idea is just this: a type class is like a Java-style interface,
--  and an *instance* is an implementation of that interface for a
--  particular type. We associate notation with a particular type class
--  member, and then instances of that typeclass inherit the notation for
--  that member.
--
--  For example, `++` is defined via the `HAppend` type class's `hAppend`
--  member. Any type that provides an `HAppend` instance gets to use `++`
--  for its implementation of `hAppend`. Lean's built-in `List` already has
--  such an instance (using `List.append` for `hAppend`), but since we've
--  defined our own `append` function, we can register it as the `++`
--  operator within our namespace:

instance : HAppend NatList NatList NatList where
  hAppend := append

--  Now `l₁ ++ l₂` means `append l₁ l₂` within `NatList`.
--
--  Some simple facts about appending lists:

theorem nil_append (l : NatList) : [] ++ l = l := by rfl

theorem cons_append (n : Nat) (l₁ l₂ : NatList) :
  (n :: l₁) ++ l₂ = n :: (l₁ ++ l₂) := by rfl

example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := by rfl
example : [] ++ [4, 5] = [4, 5] := by rfl
example : [1, 2, 3] ++ [] = [1, 2, 3] := by rfl

--  The equality test `==` on `Nat`s is another example: it comes from the
--  `BEq` ("boolean equality") type class. One small but handy fact about
--  it, which several proofs below will need, is that `==` is reflexive:

#check (BEq.refl (α := Nat))

--  Output:
--    BEq.refl : ∀ (a : Nat), (a == a) = true

--  ### Head and Tail

--  The `head` function returns the first element (the "head") of the list,
--  while `tail` returns everything but the first element (the "tail").
--  Since the empty list has no first element, we pass a default value to
--  be returned in that case.

def head (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default
  | h :: _ => h

--  Basic theorems about how `head` behaves:

theorem head_cons (h x : Nat) (t : NatList) : (h :: t).head x = h := by rfl

theorem head_nil (x : Nat) : [].head x = x := by rfl

def tail (l : NatList) : NatList :=
  match l with
  | [] => []
  | _ :: t => t

--  Basic theorems about how `tail` behaves:

theorem tail_cons (h : Nat) (t : NatList) : (h :: t).tail = t := by rfl

theorem tail_nil : [].tail = [] := by rfl

--  And some examples:

example : head 0 [1, 2, 3] = 1 := by rw [head_cons]
example : head 0 [] = 0 := by rw [head_nil]
example : [1, 2, 3].tail = [2, 3] := by rw [tail_cons]

--   ----------------------------------------

--  _Quiz:_

--  What does the following function do?

def foo (n : Nat) : NatList :=
  match n with
  | 0 => []
  | n' + 1 => (n' + 1) :: foo n'

--   ----------------------------------------

--  ### Exercises

--  Note to developers (Michael Hicks @mwhicks1):
--      The exercises below are kind of massive, with many parts. Is that
--      really what we want, rather than separating out the graded parts
--      into separate exercises?

--  ### Exercise (2 stars): list_funs ⭐⭐

--  Complete the definitions of `nonZeros`, `oddMembers`, and
--  `countOddMembers` below. Have a look at the lemmas and examples to
--  understand what these functions should do.

def nonZeros (l : NatList) : NatList := (
  match l with
  | [] => []
  | 0 :: t => nonZeros t
  | h :: t => h :: nonZeros t
)

--  The following lemmas should hold about your definition

theorem nonZeros_cons_zero (t : NatList) :
    nonZeros (0 :: t) = nonZeros t := (by rfl)

theorem nonZeros_nil :
    nonZeros [] = [] := (by rfl)

theorem nonZeros_cons_nonZero (h : Nat) (t : NatList) :
    nonZeros ((h + 1) :: t) = (h + 1) :: nonZeros t := (by rfl)

theorem test_nonZeros : nonZeros [0, 1, 0] = [1] := by
  rw [nonZeros_cons_zero]
  rw [nonZeros_cons_nonZero]
  rw [nonZeros_cons_zero]
  rw [nonZeros_nil]

--  The next definition uses `bif`, Lean's conditional for Boolean tests.
--  The expression `bif b then x else y` evaluates to `x` when `b` is
--  `true` and to `y` when `b` is `false`. Its characterizing lemmas are
--  `cond_true` and `cond_false`.

sf_recall
  theorem Bool.cond_true {α} (x y : α) : (bif true then x else y) = x := by
    rfl

sf_recall
  theorem Bool.cond_false {α} (x y : α) : (bif false then x else y) = y := by
    rfl

def oddMembers (l : NatList) : NatList := (
  match l with
  | [] => []
  | h :: t => bif h.odd then h :: oddMembers t else oddMembers t)

theorem oddMembers_nil :
    oddMembers [] = [] := (by rfl)

theorem oddMembers_cons (h : Nat) (t : NatList) :
    oddMembers (h :: t) =
      bif h.odd then h :: oddMembers t else oddMembers t :=
  (by rfl)

theorem oddMembers_cons_odd (n : Nat) (l : NatList)
    (h : n.odd = true) :
    oddMembers (n :: l) = n :: oddMembers l := by
  rw [oddMembers_cons, h, Bool.cond_true]

theorem oddMembers_cons_not_odd (n : Nat) (l : NatList)
    (h : n.odd = false) :
    oddMembers (n :: l) = oddMembers l := by
  rw [oddMembers_cons, h, Bool.cond_false]

--  Now, we can prove that `oddMembers [1, 2]` returns `[1]` using the
--  lemmas:

example : oddMembers [1, 2] = [1] := by
  rw [oddMembers_cons_odd]
  · rw [oddMembers_cons_not_odd]
    · rw [oddMembers_nil]
    · rw [Nat.odd_def]
      rw [Nat.even_succ, Nat.even_succ, Nat.even_zero]
      rw [Bool.not_true, Bool.not_false, Bool.not_true]
  · rw [Nat.odd, Nat.even_succ, Nat.even_zero]
    rw [Bool.not_true, Bool.not_false]

--  This gets pretty verbose quite fast, however we can use `rfl` to deal
--  with subgoals such as `Nat.odd 2 = false`:

example : oddMembers [1, 2] = [1] := by
  rw [oddMembers_cons_odd]
  · rw [oddMembers_cons_not_odd]
    · rw [oddMembers_nil]
    · rfl
  · rfl

--  In fact, as the entire proof is just plain computation, it can be done
--  with a single `rfl`. This is possible because all of the elements and
--  lists are concrete -- there are no variables involved.

example : oddMembers [1, 2] = [1] := (by rfl)

theorem test_oddMembers : oddMembers [0, 1, 2, 3, 0] = [1, 3] := (by rfl)

--  For the next problem, `countOddMembers`, we encourage you to implement
--  it using already-defined functions, rather than recursion.

def countOddMembers (l : NatList) : Nat := (
  (oddMembers l).length)

example : countOddMembers [0, 1, 2, 3, 0] = 2 := (by rfl)

theorem test_countOddMembers1 : countOddMembers [0, 2, 4] = 0 := (by rfl)

theorem test_countOddMembers2 : countOddMembers [] = 0 := (by rfl)

--  ### Exercise (3 stars): alternate (Advanced) ⭐⭐⭐

--  Complete the following definition of `alternate`, which interleaves two
--  lists into one, alternating between elements taken from the first list
--  and elements from the second.
--
--  Hint: there are natural ways of writing `alternate` that fail to
--  satisfy Lean's requirement that all recursive definitions be
--  *structurally recursive*, as mentioned in Basics. If you encounter this
--  difficulty, consider pattern matching against both lists at the same
--  time.

def alternate (l₁ l₂ : NatList) : NatList := (
  match l₁, l₂ with
  | [], _ => l₂
  | _, [] => l₁
  | h₁ :: t₁, h₂ :: t₂ => h₁ :: h₂ :: alternate t₁ t₂)

theorem test_alternate1 :
    alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6] := (by rfl)

theorem test_alternate2 :
    alternate [1] [4, 5, 6] = [1, 4, 5, 6] := (by rfl)

theorem test_alternate3 :
    alternate [1, 2, 3] [4] = [1, 4, 2, 3] := (by rfl)

theorem test_alternate4 :
    alternate [] [20, 30] = [20, 30] := (by rfl)

--  ### Counting

--  ### Exercise (1 star): counting ⭐

--  Define a `count` function for `NatList`s that counts the number of
--  times an element `n` appears in the list.

def count (n : Nat) (l : NatList) : Nat := (
  match l with
  | [] => 0
  | h :: t => bif n == h then count n t + 1 else count n t)

--  Now, prove these lemmas which should hold about your definition.

theorem count_nil (n : Nat) : count n [] = 0 := (by rfl)

theorem count_cons_def (n h : Nat) (t : NatList) :
    count n (h :: t) =
      bif n == h then count n t + 1 else count n t := (by rfl)

theorem count_cons_same (n₁ n₂ : Nat) (t : NatList)
  (h : (n₁ == n₂) = true) :
    count n₁ (n₂ :: t) = count n₁ t + 1 := by
  rw [count_cons_def, h, cond_true]

theorem count_cons_diff (n₁ n₂ : Nat) (t : NatList)
  (h : (n₁ == n₂) = false) :
    count n₁ (n₂ :: t) = count n₁ t := by
  rw [count_cons_def, h, cond_false]

example : count 1 [1] = 1 := by
  rw [count_cons_same _ _ _ rfl]
  rw [count_nil]

example : count 2 [2, 2] = 2 := (by rfl)

theorem test_count1 : count 1 [1, 1, 4] = 2 := (by rfl)

theorem test_count2 : count 5 [1, 1, 4] = 0 := (by rfl)

--  Again, all these proofs could be completed with just `rfl`, because the
--  proof is computationally straight-forward -- compute both sides of the
--  equality and check if they are the same.

example : count 1 [1, 2, 3, 1, 4, 1] = 3 := (by rfl)
example : count 6 [1, 2, 3, 1, 4, 1] = 0 := (by rfl)

--  ### Membership

--  ### Exercise (1 star): membership ⭐

def member (n : Nat) (l : NatList) : Bool := (
  match l with
  | [] => false
  | h :: t => bif n == h then true else member n t)

theorem member_nil (n : Nat) : member n [] = false := (by rfl)

theorem member_cons_same (n₁ n₂ : Nat) (t : NatList)
  (h : (n₁ == n₂) = true) :
    member n₁ (n₂ :: t) = true := by
  rw [member, h, cond_true]

theorem member_cons_diff (n₁ n₂ : Nat) (t : NatList)
  (h : (n₁ == n₂) = false) :
    member n₁ (n₂ :: t) = member n₁ t := by
  rw [member, h, cond_false]

example : member 1 [1] = true := by
  rw [member_cons_same _ _ _ rfl]

example : member 2 [1] = false := (by rfl)

theorem test_member1 : member 1 [1, 4, 1] = true := (by rfl)

theorem test_member2 : member 2 [1, 4, 1] = false := (by rfl)

--  ### Removal

--  ### Exercise (3 stars): removing (Optional) ⭐⭐⭐

--  Here are some more `NatList` functions for you to practice with.
--
--  When `removeOne` is applied to a list without the number to remove, it
--  should return the same list unchanged.

def removeOne (n : Nat) (l : NatList) : NatList := (
  match l with
  | [] => nil
  | h :: t => bif n == h then t else h :: removeOne n t)

theorem removeOne_nil (n : Nat) : removeOne n nil = nil := (by rfl)

theorem removeOne_cons_same (n₁ n₂ : Nat) (t : NatList)
  (h : (n₁ == n₂) = true) :
    removeOne n₁ (n₂ :: t) = t := by
  rw [removeOne, h, cond_true]

theorem removeOne_cons_diff (n₁ n₂ : Nat) (t : NatList)
  (h : (n₁ == n₂) = false) :
    removeOne n₁ (n₂ :: t) = n₂ :: removeOne n₁ t := by
  rw [removeOne, h, cond_false]

example : removeOne 5 [1, 5, 4] = [1, 4] := by
  rw [removeOne_cons_diff _ _ _ rfl]
  rw [removeOne_cons_same _ _ _ rfl]

example : count 5 (removeOne 5 [1, 5, 4]) = 0 := (by rfl)

theorem test_removeOne1 : count 4 (removeOne 5 [4, 5, 1, 4]) = 2 := (by rfl)

theorem test_removeOne2 : count 5 (removeOne 5 [1, 5, 5, 4]) = 1 := (by rfl)

def removeAll (n : Nat) (l : NatList) : NatList := (
  match l with
  | [] => []
  | h :: t => bif n == h then removeAll n t else h :: removeAll n t)

theorem removeAll_nil (n : Nat) : removeAll n [] = [] := (by rfl)

theorem removeAll_cons_same (n₁ n₂ : Nat) (t : NatList)
  (h : (n₁ == n₂) = true) :
    removeAll n₁ (n₂ :: t) = removeAll n₁ t := by
  rw [removeAll, h, cond_true]

theorem removeAll_cons_diff (n₁ n₂ : Nat) (t : NatList)
  (h : (n₁ == n₂) = false) :
    removeAll n₁ (n₂ :: t) = n₂ :: removeAll n₁ t := by
  rw [removeAll, h, cond_false]

example : count 5 (removeAll 5 [5, 1]) = 0 := by
  rw [removeAll_cons_same _ _ _ rfl]
  rw [removeAll_cons_diff _ _ _ rfl]
  rw [removeAll_nil]
  rw [count_cons_diff _ _ _ rfl]
  rw [count_nil]

example : count 5 (removeAll 5 [5, 5]) = 0 := (by rfl)

theorem test_removeAll1 : count 4 (removeAll 5 [4, 5, 4]) = 2 := (by rfl)

theorem test_removeAll2 : count 5 (removeAll 5 [2, 5, 5, 5, 1]) = 0 := (by rfl)

--  ### Included

--  ### Exercise (3 stars): included (Optional) ⭐⭐⭐

def included (l₁ l₂ : NatList) : Bool := (
  match l₁ with
  | [] => true
  | h :: t => member h l₂ && included t (removeOne h l₂))

theorem included_nil (l₂ : NatList) : included nil l₂ = true := (by rfl)

theorem included_cons_member (n : Nat) (l₁ l₂ : NatList)
  (h : member n l₂ = true) :
    included (cons n l₁) l₂ = included l₁ (removeOne n l₂) := by
  rw [included, h, Bool.true_and]

theorem included_cons_nonmember (n : Nat) (l₁ l₂ : NatList)
  (h : member n l₂ = false) :
    included (cons n l₁) l₂ = false := by
  rw [included, h, Bool.false_and]

example : included [1] [2, 1] = true := by
  rw [included_cons_member]
  · exact included_nil _
  · rw [member_cons_diff _ _ _ rfl]
    rw [member_cons_same _ _ _ rfl]

example : included [1, 1] [2, 1, 4, 1] = true := (by rfl)

theorem test_included1 : included [1, 2] [2, 1, 4, 1] = true := (by rfl)

theorem test_included2 : included [1, 2, 2] [2, 1, 4, 1] = false := (by rfl)

--  ## Reasoning About Lists

--  As with numbers, simple facts about list-processing functions can
--  sometimes be proved entirely by rewriting. For example, just rewriting
--  the left-hand side of the following equality using the theorem
--  `nil_append` is enough for this theorem.

theorem tail_length_pred (l : NatList) :
    l.length.pred = l.tail.length := by
  cases l with
  | nil       => rw [tail_nil, length_nil]; rfl
  | cons n l' => rw [tail_cons, length_cons]; rfl

--  Here, the `nil` case works because we've chosen to define
--  `tail [] = []`. Notice that the `cons` case introduces two names, `n`
--  and `l'`, corresponding to the fact that the `cons` constructor for
--  lists takes two arguments (the head and tail of the list it is
--  constructing).

--  Usually, though, interesting theorems about lists require induction for
--  their proofs. We'll see how to do this next.

--  (Micro-Sermon: As we get deeper into this material, simply *reading*
--  proof scripts will not help you very much. Rather, it is important to
--  step through the details of each one using Lean and think about what
--  each step achieves. Otherwise it is more or less guaranteed that the
--  exercises will make no sense when you get to them. 'Nuff said.)

--  ### Induction on Lists

--  Proofs by induction over datatypes like `NatList` are a little less
--  familiar than standard natural number induction, but the idea is
--  equally simple. Each `inductive` declaration defines a set of data
--  values that can be built up using the declared constructors. For
--  example, a boolean can be either `true` or `false`; a number can be
--  either `0` or else `Nat.succ` applied to another number; and a list can
--  be either `[]` or else `::` applied to a number and a list. Moreover,
--  applications of the declared constructors to one another are the *only*
--  possible shapes that elements of an inductively defined set can have.
--
--  This last fact directly gives rise to a way of reasoning about
--  inductively defined sets: a number is either `0` or else it is
--  `Nat.succ` applied to some *smaller* number; a list is either `[]` or
--  else it is `::` applied to some number and some *smaller* list; etc.
--  Thus, if we have in mind some proposition `P` that mentions a list `l`
--  and we want to argue that `P` holds for *all* lists, we can reason as
--  follows:
--
--  - First, show that `P` is true of `l` when `l` is `[]`.
--
--  - Then show that `P` is true of `l` when `l` is `n :: l'` for some
--    number `n` and some smaller list `l'`, assuming that `P` is true for
--    `l'`.
--
--  Since larger lists can always be broken down into smaller ones,
--  eventually reaching `[]`, these two arguments together establish the
--  truth of `P` for all lists `l`.
--
--  Here's a concrete example:

theorem append_assoc (l₁ l₂ l₃ : NatList) :
    (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  induction l₁ with
  | nil =>
    rw [nil_append, nil_append]
  | cons n l₁' ih =>
    rw [cons_append, cons_append, cons_append, ih]

--  *Theorem*: For all lists `l₁`, `l₂`, and `l₃`,
--
--      (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃).
--
--  *Proof*: By induction on `l₁`.
--
--  - First, suppose `l₁ = []`. We must show
--
--      ([] ++ l₂) ++ l₃ = [] ++ (l₂ ++ l₃),
--
--  which follows directly from the definition of `append`.
--
--  - Next, suppose `l₁ = n :: l₁'`, which gives us the following inductive
--    hypothesis.
--
--      (l₁' ++ l₂) ++ l₃ = l₁' ++ (l₂ ++ l₃)
--
--  We must show
--
--      ((n :: l₁') ++ l₂) ++ l₃ = (n :: l₁') ++ (l₂ ++ l₃).
--
--  By the definition of `append`, this follows from
--
--      n :: ((l₁' ++ l₂) ++ l₃) = n :: (l₁' ++ (l₂ ++ l₃)),
--
--  which is immediate from the induction hypothesis. *Qed*.

--  #### Generalizing Statements

--  In some situations, it is necessary to generalize a statement in order
--  to prove it by induction. Intuitively, the reason is that a more
--  general statement also yields a more general (stronger) inductive
--  hypothesis. While the following statement is true, we cannot prove it
--  directly:

sf_expect_failure_in
  theorem replicate_append_fail (c n : Nat) :
      replicate n c ++ replicate n c = replicate n (c + c) := by
    induction c with
    | zero => rw [replicate_zero, nil_append]
    | succ c' ih =>
      rw [replicate_succ, cons_append]
      -- Now we seem to be stuck.
      -- The `ih` only works for `c' + c'`,
      -- but we need `c' + 1 + (c' + 1)`.

--  Output:
--    unsolved goals
--    case succ
--    n c' : Nat
--    ih : replicate n c' ++ replicate n c' = replicate n (c' + c')
--    ⊢ n :: replicate n c' ++ (n :: replicate n c') = replicate n (c' + 1 + (c' + 1))

--  To get a more general inductive hypothesis, we can generalize:

theorem replicate_append_general (c₁ c₂ n : Nat) :
    replicate n c₁ ++ replicate n c₂ = replicate n (c₁ + c₂) := by
  induction c₁ with
  | zero =>
    rw [replicate_zero, Nat.zero_add, nil_append]
  | succ c1' ih =>
    rw [Nat.succ_add, replicate_succ, replicate_succ, cons_append, ih]

--  Then, we can use this more general theorem to prove the original goal:

theorem replicate_append (c n : Nat) :
    replicate n c ++ replicate n c = replicate n (c + c) := by
  exact replicate_append_general c c n

--  #### Reversing a List

--  For a slightly more involved example of inductive proof over lists,
--  suppose we use `append` to define a list-reversing function `reverse`:

def reverse (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => t.reverse ++ [h]

theorem reverse_nil : [].reverse = [] := by rfl

theorem reverse_cons (h : Nat) (t : NatList) : (h :: t).reverse = t.reverse ++ [h] := by rfl

example : [1, 2, 3].reverse = [3, 2, 1] := by rfl

example : [].reverse = [] := by rfl

--  Let's prove that reversing a list does not change its length. Our first
--  attempt gets stuck in the successor case...

sf_expect_failure_in
  example (l : NatList) :
      l.reverse.length = l.length := by
    induction l with
    | nil => rw [reverse_nil]
    | cons n l' ih =>
      rw [reverse_cons]
      -- Now we seem to be stuck: the goal involves `++`,
      -- but we don't have any useful equations
      -- in either the immediate context or in the global
      -- environment!

--  Output:
--    unsolved goals
--    case cons
--    n : Nat
--    l' : NatList
--    ih : l'.reverse.length = l'.length
--    ⊢ (l'.reverse ++ [n]).length = (n :: l').length

--  A first attempt to make progress would be to prove exactly the
--  statement that we are missing at this point. But this attempt will fail
--  because the inductive hypothesis is not general enough.

sf_expect_failure_in
  theorem length_append_succ (l : NatList) (n : Nat) :
      (l.reverse ++ [n]).length = l.reverse.length + 1 := by
    induction l with
    | nil =>
      rw [reverse_nil, nil_append, length_cons, length_nil]
    | cons m l' ih =>
      rw [reverse_cons]
      -- `ih` not applicable

--  Output:
--    unsolved goals
--    case cons
--    n m : Nat
--    l' : NatList
--    ih : (l'.reverse ++ [n]).length = l'.reverse.length + 1
--    ⊢ (l'.reverse ++ [m] ++ [n]).length = (l'.reverse ++ [m]).length + 1

--  It turns out that the above lemma is more specific than it needs to be.
--  We can strengthen the lemma to work not only on reversed lists but on
--  general lists.

theorem append_length_succ (l : NatList) (n : Nat) :
    (l ++ [n]).length = l.length + 1 := by
  induction l with
  | nil => rw [nil_append, length_cons]
  | cons m l' ih =>
    rw [cons_append, length_cons, ih, length_cons]

--  Now we can prove the main theorem.

theorem length_reverse (l : NatList) :
    l.reverse.length = l.length := by
  induction l with
  | nil => rw [reverse_nil]
  | cons n l' ih =>
    rw [reverse_cons, append_length_succ, ih, length_cons]

--  We can also prove a more general form that gives the length of any two
--  appended lists.

theorem length_append (l₁ l₂ : NatList) :
    (l₁ ++ l₂).length = l₁.length + l₂.length := by
  induction l₁ with
  | nil => rw [nil_append, length_nil, Nat.zero_add]
  | cons n l₁' ih =>
    rw [cons_append, length_cons, ih, length_cons, Nat.succ_add]

--  For comparison, here are informal proofs of these two theorems:
--
--  *Theorem*: For all lists `l₁` and `l₂`,
--
--      (l₁ ++ l₂).length = l₁.length + l₂.length.
--
--  *Proof*: By induction on `l₁`.
--
--  - First, suppose `l₁ = []`. We must show
--
--      ([] ++ l₂).length = [].length + l₂.length,
--
--  which follows directly from the definitions of `length`, `++`, and `+`.
--
--  - Next, suppose `l₁ = n::l₁'`, with I.H.
--
--      (l₁' ++ l₂).length = l₁'.length + l₂.length
--
--  We must show
--
--      ((n::l₁') ++ l₂).length = (n::l₁').length + l₂.length.
--
--  This follows directly from the definitions of `length` and `++`
--  together with the induction hypothesis. *Qed*.
--
--  *Theorem*: For all lists `l`, `l.reverse.length = l.length`.
--
--  *Proof*: By induction on `l`.
--
--  - First, suppose `l = []`. We must show
--
--      [].reverse.length = [].length,
--
--  which follows directly from the definitions of `length` and `reverse`.
--
--  - Next, suppose `l = n::l'`, with
--
--      l'.reverse.length = l'.length
--
--  We must show
--
--      (n :: l').reverse.length = (n :: l').length.
--
--  By the definition of `reverse`, this follows from
--
--      (l'.reverse ++ [n]).length = l'.length + 1,
--
--  which, by the previous lemma, is the same as
--
--      l'.reverse.length + [n].length = l'.length + 1.
--
--  This follows directly from the induction hypothesis and the definition
--  of `length`. *Qed*.
--
--  The style of these proofs is rather longwinded and pedantic. After
--  reading a couple like this, we might find it easier to follow proofs
--  that give fewer details (which we can easily work out in our own minds
--  or on scratch paper if necessary) and just highlight the non-obvious
--  steps. In this more compressed style, the above proof might look like
--  this:
--
--  *Theorem*: For all lists `l`, `l.reverse.length = l.length`.
--
--  *Proof*: First observe, by a straightforward induction on `l`, that
--  `(l ++ [n]).length = l.length + 1` for any `l`. The main property then
--  follows by another induction on `l`, using this observation together
--  with the induction hypothesis in the case where `l = n'::l'`. *Qed*
--
--  Which style is preferable in a given situation depends on the
--  sophistication of the expected audience and how similar the proof at
--  hand is to ones that they will already be familiar with. The more
--  pedantic style is a good default for our present purposes because we're
--  trying to be very clear about the details.

--  ### List Exercises, Part 1

--  ### Exercise (3 stars): list_exercises ⭐⭐⭐

--  More practice with lists:

theorem append_nil (l : NatList) :
    l ++ [] = l := by
  induction l with
  | nil => rw [nil_append]
  | cons n l' ih =>
    rw [cons_append, ih]

theorem reverse_append (l₁ l₂ : NatList) :
   (l₁ ++ l₂).reverse = l₂.reverse ++ l₁.reverse := by
  induction l₁ with
  | nil => rw [nil_append, reverse_nil, append_nil]
  | cons x l₁' ih =>
    rw [cons_append, reverse_cons, ih, reverse_cons, append_assoc]

--  An *involution* is a function that is its own inverse. That is,
--  applying the function twice yields the original input.

theorem reverse_involutive (l : NatList) :
    l.reverse.reverse = l := by
  induction l with
  | nil => rw [reverse_nil, reverse_nil]
  | cons n l' ih =>
    rw [reverse_cons, reverse_append, ih]
    rw [reverse_cons, reverse, nil_append, cons_append, nil_append]

--  There is a short solution to the next one. If you find yourself getting
--  tangled up, step back and try to look for a simpler way.

theorem append_assoc4 (l₁ l₂ l₃ l4 : NatList) :
    l₁ ++ (l₂ ++ (l₃ ++ l4)) = ((l₁ ++ l₂) ++ l₃) ++ l4 := by
  rw [append_assoc, append_assoc]

--  An exercise about your implementation of `nonZeros`:

theorem nonZeros_append (l₁ l₂ : NatList) :
    nonZeros (l₁ ++ l₂) = (nonZeros l₁) ++ (nonZeros l₂) := by
  induction l₁ with
  | nil => rw [nonZeros_nil, nil_append, nil_append]
  | cons n l₁' ih =>
    cases n with
    | zero =>
      rw [nonZeros_cons_zero, ← ih, cons_append, nonZeros_cons_zero]
    | succ n' =>
      rw [cons_append, nonZeros_cons_nonZero, nonZeros_cons_nonZero, ih, cons_append]

--  ### Exercise (2 stars): beq ⭐⭐

--  Fill in the definition of `beq`, which compares lists of numbers for
--  equality. Prove that `beq l l` yields `true` for every list `l`.

def beq (l₁ l₂ : NatList) : Bool := (
  match l₁, l₂ with
  | [], [] => true
  | h₁ :: t₁, h₂ :: t₂ => (h₁ == h₂) && beq t₁ t₂
  | _, _ => false)

theorem beq_nil : beq [] [] = true := (by rfl)

theorem beq_cons_same (h₁ h₂ : Nat) (t₁ t₂ : NatList)
  (h : (h₁ == h₂) = true) :
    beq (h₁ :: t₁) (h₂ :: t₂) = beq t₁ t₂ := by
  rw [beq, h, Bool.true_and]

theorem beq_cons_diff (h₁ h₂ : Nat) (t₁ t₂ : NatList)
  (h : (h₁ == h₂) = false) :
    beq (h₁ :: t₁) (h₂ :: t₂) = false := by
  rw [beq, h, Bool.false_and]

example : beq [] [] = true := (by rfl)
example : beq [1, 2, 3] [1, 2, 3] = true := (by rfl)
example : beq [1, 2, 3] [1, 2, 4] = false := by
  rw [beq_cons_same _ _ _ _ rfl]
  rw [beq_cons_same _ _ _ _ rfl]
  rw [beq_cons_diff _ _ _ _ rfl]

theorem beq_refl (l : NatList) :
    beq l l = true := by
  induction l with
  | nil => rw [beq_nil]
  | cons n l' ih =>
    rw [beq_cons_same _ _ _ _ (BEq.refl n)]
    exact ih

--  ### List Exercises, Part 2

open NatList

--  Here are a couple of little theorems to prove about your definition
--  above.

--  ### Exercise (1 star): count_member_nonZero ⭐

theorem count_member_nonZero (l : NatList) :
    Nat.ble 1 (count 1 (1 :: l)) = true := by
  rw [count_cons_same] <;> rfl

--  The following lemma about `Nat.ble` might help you in the next exercise
--  (it will also be useful in later chapters).

theorem ble_self_succ (n : Nat) :
    Nat.ble n (n + 1) = true := by
  induction n with
  | zero       => rfl
  | succ n' ih => rw [Nat.ble]; exact ih

--  Before doing the next exercise, make sure you've filled in the
--  definition of `removeOne` above.

--  ### Exercise (3 stars): remove_does_not_increase_count (Advanced) ⭐⭐⭐

theorem remove_does_not_increase_count (l : NatList) :
    Nat.ble (count 0 (removeOne 0 l)) (count 0 l) = true := by
  induction l with
  | nil =>
    rw [removeOne_nil, count_nil]
    rfl
  | cons n s' ih =>
    cases n with
    | zero =>
      rw [removeOne_cons_same _ _ _ rfl, count_cons_same _ _ _ rfl, ble_self_succ]
    | succ n' =>
      rw [removeOne_cons_diff _ _ _ rfl, count_cons_diff _ _ _ rfl, count_cons_diff _ _ _ rfl]
      exact ih

--  ### Exercise (3 stars): count_append (Optional, Manually graded) ⭐⭐⭐

--  Write down an interesting theorem `count_append` about lists involving
--  the functions `count` and `append`, and prove it. (You may find that
--  the difficulty of the proof depends on how you defined `count`!)

theorem count_append (l₁ l₂ : NatList) (n : Nat) :
    count n (l₁ ++ l₂) = (count n l₁) + (count n l₂) := by
  induction l₁ with
  | nil =>
    rw [nil_append, count_nil, Nat.zero_add]
  | cons h s1' ih =>
    rw [cons_append]
    cases hv : (n == h) with
    | false =>
      rw [count_cons_diff _ _ _ hv, count_cons_diff _ _ _ hv]
      exact ih
    | true =>
      rw [count_cons_same _ _ _ hv, count_cons_same _ _ _ hv, Nat.succ_add, ← ih]

--  ### Exercise (3 stars): involutive_injective (Advanced) ⭐⭐⭐

--  Prove that every involution is injective.
--
--  Involutions were defined above in `reverse_involutive`. An *injective*
--  function is one-to-one: it maps distinct inputs to distinct outputs,
--  without any collisions.

theorem involutive_injective (f : Nat → Nat)
  (hInv : ∀ n : Nat, n = f (f n)) :
    (∀ n₁ n₂ : Nat, f n₁ = f n₂ → n₁ = n₂) := by
  intro n₁ n₂ h
  rw [hInv n₁, hInv n₂, h]

--  ### Exercise (2 stars): reverse_injective (Advanced) ⭐⭐

--  Prove that `reverse` is injective. Do not prove this by induction —
--  that would be hard. Instead, re-use the same proof technique that you
--  used for `involutive_injective`. (But: Don't try to use that exercise
--  directly as a lemma: the types are not the same!)

theorem reverse_injective (l₁ l₂ : NatList)
    (h : l₁.reverse = l₂.reverse) : l₁ = l₂ := by
  rw [← reverse_involutive l₁, ← reverse_involutive l₂, h]

--  ## Options

--  Suppose we want to write a function that returns the `n`th element of
--  some list. If we give it type `NatList → Nat → Nat`, then we'll have to
--  choose some number to return when the list is too short...

def nthBad (l : NatList) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' => match n with
    | 0 => a
    | n' + 1 => nthBad l' n'

--  This solution is not so good, since in some cases this default value of
--  `42` could appear in the input list, and thus will not clearly indicate
--  that `n` was greater than the length of the list. A better alternative
--  is to change the return type to include an error value as a possible
--  outcome. We call this new type `NatOption`.

end NatList

inductive NatOption : Type where
  | some (n : Nat)
  | none

namespace NatList

--  We can then change the above definition of `nthBad` to return
--  `NatOption.none` when the list is too short and `some a` when the list
--  has enough members and `a` appears at position `n`. We call this new
--  function `nth?` to indicate that it may result in an error.

def nth? (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => .none
  | a :: l' => match n with
    | 0 => .some a
    | n' + 1 => nth? l' n'

example : nth? [4, 5, 6, 7] 0 = .some 4 := by rfl
example : nth? [4, 5, 6, 7] 3 = .some 7 := by rfl
example : nth? [4, 5, 6, 7] 9 = .none := by rfl

--  The function below pulls the `Nat` out of a `NatOption`, returning a
--  supplied default in the `none` case.

def NatOption.elim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n => n
  | .none => d

theorem NatOption.elim_none (d : Nat) : elim d .none = d := by rfl

theorem NatOption.elim_some (d₁ d₂ : Nat) : elim d₁ (.some d₂) = d₂ := by rfl

--  ### Exercise (2 stars): head? ⭐⭐

--  Using the same idea, fix the `head` function from earlier so we don't
--  have to pass a default element for the `nil` case.

def head? (l : NatList) : NatOption := (
  match l with
  | [] => .none
  | h :: _ => .some h)

example : head? [] = .none := (by rfl)
theorem test_head?1 : head? [1] = .some 1 := (by rfl)
theorem test_head?2 : head? [5, 6] = .some 5 := (by rfl)

theorem head?_nil : head? [] = .none := (by rfl)

theorem head?_cons (h : Nat) (t : NatList) : head? (h :: t) = .some h := (by rfl)

--  ### Exercise (1 star): option_elim_head? (Optional) ⭐

--  This exercise relates your new `head?` to the old `head`.

theorem option_elim_head? (l : NatList) (default : Nat) :
    head default l = NatOption.elim default (head? l) := by
  cases l with
  | nil => rw [head?_nil, NatOption.elim_none, head_nil]
  | cons n l' =>
    rw [head_cons, head?_cons, NatOption.elim_some]

end NatList

--  ## Partial Maps

--  As a final illustration of how data structures can be defined in Lean,
--  here is a simple *partial map* data type, analogous to the map or
--  dictionary data structures found in most programming languages.
--
--  First, we define a new type `MyId` to serve as the "keys" of our
--  partial maps.

structure MyId where
  val : Nat

--  Internally, a `MyId` is just a number. Introducing a separate type by
--  wrapping each `Nat` makes definitions more readable and gives us
--  flexibility to change representations later if we want to.
--
--  We'll also need an equality test for `MyId`s:

def MyId.beq (x₁ x₂ : MyId) : Bool :=
  x₁.val == x₂.val

--  ### Exercise (1 star): MyId.beq_refl ⭐

theorem MyId.beq_refl (x : MyId) : MyId.beq x x = true := by
  rw [beq, BEq.refl]

--  Now we define the type of partial maps:

inductive PartialMap : Type where
  | empty : PartialMap
  | record (i : MyId) (n : Nat) (m : PartialMap) : PartialMap

--  This declaration can be read: "There are two ways to construct a
--  `PartialMap`: either using the constructor `empty` to represent an
--  empty partial map, or applying the constructor `record` to a key, a
--  value, and an existing `PartialMap` to construct a `PartialMap` with an
--  additional key-to-value mapping."

namespace PartialMap

--  The `update` function overrides the entry for a given key in a partial
--  map by shadowing it with a new one (or simply adds a new entry if the
--  given key is not already present).

def update (d : PartialMap) (x : MyId) (value : Nat) : PartialMap :=
  record x value d

--  Last, the `find` function searches a `PartialMap` for a given key. It
--  returns `none` if the key was not found and `some val` if the key was
--  associated with `val`. If the same key is mapped to multiple values,
--  `find` will return the first one it encounters.

def find (x : MyId) (d : PartialMap) : NatOption :=
  match d with
  | empty => .none
  | record y n d' =>
    bif MyId.beq x y then .some n
    else find x d'

--   ----------------------------------------

--  _Quiz:_

--  Is the following claim true or false?

theorem quiz1 (d : PartialMap) (x : MyId) (n : Nat) :
    find x (update d x n) = .some n := by
  rw [update, find, MyId.beq_refl, cond_true]

--  (A) True (B) False (C) Not sure

--   ----------------------------------------

--  _Quiz:_

--  Is the following claim true or false?

theorem quiz2  (d : PartialMap) (x y : MyId) (o : Nat) :
    MyId.beq x y = false →
    find x (update d y o) = find x d := by
  intro h
  rw [update, find, h, cond_false]

--  (A) True (B) False (C) Not sure

--   ----------------------------------------

--  ### Exercise (1 star): update_eq ⭐

theorem update_eq (d : PartialMap) (x : MyId) (n : Nat) :
    find x (update d x n) = .some n := by
  rw [update, find, MyId.beq_refl, cond_true]

--  ### Exercise (1 star): update_neq ⭐

theorem update_neq (d : PartialMap) (x y : MyId) (o : Nat) :
    MyId.beq x y = false → find x (update d y o) = find x d := by
  intro h
  rw [update, find, h, cond_false]

end PartialMap

end Lists

-- Built on 2026-09-03 11:55 UTC

import LF.Induction
import LF.UsingLean

import LF.SFLCompat

-- # Lists: Working with Structured Data

-- Note to developers (Daniel Sainati  @dsainati1):
--     [BCP: Old comment -- might be out of date?] Weird that this file
--     contains the first `inductive` definition students have seen up to this
--     point, but that definition is also actually a `structure`. Probably
--     need to restructure this.
--
--     Unsure if it's a good idea to actually use the built-in `List`
--     definition here, since it's polymorphic, and we aren't introducing this
--     idea until a later chapter. This also means we don't get the chance to
--     show students how to actually produce an inductive definition if we're
--     relying on the built-in ones.
--
--     We probably need to actually take time to explain what a `@[simp]`
--     annotation on a lemma means before we introduce it, and I don't think
--     this chapter is the right place to do it anyway. This is probably a
--     better fit for `Auto.lean`.
--
--     Claude picked a bad definition for `nonzeroes`:
--
--     `match l with
--       | [] => []
--       | 0 :: t => nonzeros t
--       | h :: t => h :: nonzeros t`
--
--     which makes many of the later proofs hard to do without the full
--     automation of `simp`. I changed it, but it's worth pointing this out.

-- Note to developers (Konstantinos Kallas  @angelhof):
--     The `Baz` "how many elements does this type have?" exercise (the last
--     exercise in the chapter) is a **manual** exercise, and that's a poor
--     fit: a student who doesn't realize an inductive definition needs a base
--     case will simply fail it and only see why in the grader comment — and
--     it's easy to wrongly think you have the right answer and move on
--     without thinking. Better to either add a short section that explains
--     this directly, or add a hint like the `one_true_baz` / `count_trues`
--     scaffold ("try to write a value of type `Baz` for which the lemma
--     holds"). Worth reworking for easier grading.

-- Note to developers (before next release):
--     `(BCP 9/18) Since the domain type of Maps has changed from
--     id to string, we should either do the same here (in the partial
--     maps section) or else comment there that we are making a different
--     choice.  For the moment, it feels cleaner to avoid importing the
--     string library, explaining or handwaving string_dec, etc., so I've
--     added a comment there. BCP 25: I wonder whether we can get away
--     with just using (... =? ...)%string instead of string_dec.  Would
--     make it a lot more palatable. I now think this is probably a good
--     idea. However: At the moment, the Stdlib has String.eqb to compare
--     strings, but it returns a standard bool, which is not the one we
--     are using. We'd have to put our booleans inside a module in
--     Basics.v. That's probably fine. After that, I think we just have to
--     alias Definition Id := string).`
--
--     This chapter could use another WORKINCLASS or three.

-- This chapter introduces basic data structures and functions for working
-- with them. We place all these definitions in the `Lists` namespace to avoid
-- name clashes with Lean's standard library and with definitions from other
-- chapters.

namespace Lists

-- Note to developers (before next release):
--     Note that rewrite laws should sometimes differ from pattern matching
--     now

-- ## Pairs of Numbers

-- In an `inductive` type definition, each constructor can take any number of
-- arguments -- none (as with `true` and `0`), one (as with `succ`), or more
-- than one (as with `Nibble` and the following):

inductive NatProd where
  | pair (n1 n2 : Nat)

-- This declaration can be read: "The one and only way to construct a pair of
-- numbers is by applying the constructor `pair` to two arguments of type
-- `Nat`."

#check (NatProd.pair 3 5)

-- Functions for extracting the first and second components of a pair can then
-- be defined by pattern matching.

def NatProd.fst (p : NatProd) : Nat :=
  match p with
  | .pair x _ => x

def NatProd.snd (p : NatProd) : Nat :=
  match p with
  | .pair _ y => y

-- Defining these functions with the `NatProd` type name qualifying their name
-- allows us to use them with `.` notation:

example : (NatProd.pair 3 5).fst = 3 := by rfl

-- Since pairs will be used heavily in what follows, it will be convenient to
-- write them with angle bracket notation `⟨x, y⟩` instead of
-- `NatProd.pair x y`. This notation is built into Lean and is called
-- "anonymous constructor syntax". It is available for any inductive type with
-- a single constructor, as long as the expected type is declared or can be
-- inferred from the context.

example : (⟨3, 5⟩ : NatProd).fst = 3 := by rfl

-- The anonymous constructor can be used in both expressions and in pattern
-- matches.

def fst' (p : NatProd) : Nat :=
  match p with
  | ⟨x, _⟩ => x

def snd' (p : NatProd) : Nat :=
  match p with
  | ⟨_, y⟩ => y

def NatProd.swap (p : NatProd) : NatProd :=
  ⟨snd p, fst p⟩

-- Note that pattern-matching on a pair (with angle brackets: `⟨x, y⟩`) is not
-- to be confused with the "multiple pattern" syntax (with no brackets:
-- `x, y`) that we have seen previously. The above examples illustrate pattern
-- matching on a pair with elements `x` and `y`, whereas, for example, the
-- definition of `sub` in Basics performs pattern matching on the values `n`
-- and `m`:

def sub (n m : Nat) : Nat :=
  match n, m with
  | 0,        _        => 0
  | .succ _,  0        => n
  | .succ n', .succ m' => sub n' m'

-- The distinction is minor, but it is worth understanding that they are not
-- the same. For instance, the following definitions are ill-formed:

sf_expect_failure
  -- Can't match on a pair with multiple patterns:
  def bad_fst (p : NatProd) : Nat :=
    match p with
    | x, y => x
  
  -- Can't match on multiple values with pair patterns:
  def bad_sub (n m : Nat) : Nat :=
    match n, m with
    | ⟨0,        _⟩       => 0
    | ⟨.succ _,  0⟩        => n
    | ⟨.succ n', .succ m'⟩ => sub n' m'

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     Wrote this, let me know how it reads.

-- Lean also provides a convenient way to define `inductive` structures like
-- pairs that have a single constructor but multiple ways to access their
-- data, using the `structure` keyword. The definition of `NatProd'` below is
-- equivalent to the `NatProd` definition from earlier, except that Lean
-- automatically generates the `fst` and `snd` accessors.

structure NatProd' where
  fst : Nat
  snd : Nat

#check (NatProd'.mk 3 5)
example : (NatProd'.mk 3 5).fst = 3 := by rfl
example : (⟨3, 5⟩ : NatProd').fst = 3 := by rfl

-- A property like `p = ⟨p.fst, p.snd⟩` can be proved by exposing the
-- structure of the pair, either with `cases` or by destructuring in `intro`.

theorem surjective_pairing : ∀ p : NatProd,
    p = ⟨p.fst, p.snd⟩ := by
  intro ⟨n, m⟩; rfl

theorem surjective_pairing_cases (p : NatProd) :
    p = ⟨p.fst, p.snd⟩ := by
  cases p; rfl

-- Notice that, by contrast with the behavior of `cases` on `Nat`s, where it
-- generates two subgoals, `cases` generates just one subgoal here. That's
-- because `NatProd`s can only be constructed in one way.

-- ### Exercise (1 star): snd_fst_is_swap ⭐

theorem snd_fst_is_swap (p : NatProd) :
    (⟨p.snd, p.fst⟩ : NatProd) = p.swap := by
  sorry

-- ### Exercise (1 star): fst_swap_is_snd ⭐

theorem fst_swap_is_snd (p : NatProd) :
    p.swap.fst = p.snd := by
  sorry

-- ## Lists of Numbers

-- Generalizing the definition of pairs, we can describe the type of *lists*
-- of numbers like this: "A list is either the empty list or else a pair of a
-- number and another list."

inductive NatList : Type where
  | nil
  | cons (n : Nat) (l : NatList)

-- By convention, we place the operations (functions) of an inductive type
-- inside the namespace implicitly created by that type's definition.

namespace NatList

-- As with pairs, it is convenient to write lists in familiar notation. The
-- following declarations allow us to use `::` as an infix `cons` operator and
-- square brackets as an "outfix" notation for constructing lists.

-- Don't worry too much about what this is doing:

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     Can we be a little more helpful, or tell them when we are going to tell
--     them, or tell them where to look?

scoped infixr:65 " :: " => cons
scoped macro (priority := high) "[ " elems:term,* "]" : term => do
  elems.getElems.foldrM (``(cons $(⟨·⟩) $(⟨·⟩))) (← ``(nil))

-- Now these all mean exactly the same thing:

def mylist1 : NatList := 1 :: (2 :: (3 :: []))
def mylist2 : NatList := 1 :: 2 :: 3 :: []
def mylist3 : NatList := [1, 2, 3]

-- ### Repeat

-- First is the `myRepeat` function, which takes a number `n` and a `count`
-- and returns a list of length `count` in which every element is `n`. (We use
-- `myRepeat` because `repeat` is a reserved keyword in Lean.)

def myRepeat (n count : Nat) : NatList :=
  match count with
  | 0 => []
  | count' + 1 => n :: myRepeat n count'

-- Some simple facts about repetition:

theorem repeat_zero v : myRepeat v 0 = [] := rfl

theorem repeat_succ v count : myRepeat v (count + 1) = v :: myRepeat v count := rfl

-- The `length` function calculates the length of a list.

def length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => (length t) + 1

-- Some simple facts about list lengths:

theorem nil_length : [].length = 0 := rfl

theorem cons_length (n : Nat) (l : NatList) : (n::l).length = l.length + 1 := rfl

-- ### Append

-- The `app` function appends (concatenates) two lists.

def app (l1 l2 : NatList) : NatList :=
  match l1 with
  | [] => l2
  | h :: t => h :: app t l2

-- ### Type Classes and Overloading

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     One word, or two?

-- In Lean, operators like `++`, `==`, and `+` are not hardwired to particular
-- types. Instead, they are defined using *type classes* — a mechanism that
-- lets us overload operations for different types.

-- For example, `++` is defined via the `HAppend` type class. Any type that
-- provides an `HAppend` instance gets to use `++`. Lean's built-in `List`
-- already has such an instance (using `List.append`), but since we've defined
-- our own `app` function, we can register it as the `++` operator within our
-- namespace:

instance : HAppend NatList NatList NatList where
  hAppend := app

-- Now `l1 ++ l2` means `app l1 l2` within `NatList`.

-- Some simple facts about appending lists:

theorem nil_append (l : NatList) : [] ++ l = l := rfl

theorem cons_append (n : Nat) (l1 l2 : NatList) : (n::l1) ++ l2 = n :: (l1 ++ l2) := rfl

example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := by rfl
example : ([] : NatList) ++ [4, 5] = [4, 5] := by rfl
example : [1, 2, 3] ++ ([] : NatList) = [1, 2, 3] := by rfl

-- Note to developers (One An  @meluge, NOW):
--     Experiment: introduce `BEq.refl` here, at the point where the `BEq`
--     class is named.

-- Note to developers (Chris Henson  @chenson2018):
--     The way that this is written might mislead the student to think it is
--     inherent to BEq, which is not true: this additionally requires the
--     ReflBEq typeclass. How crucial is it to have this early mention of
--     typeclasses? bcpierce00: Hopefully we can postpone it.

-- The equality test `==` on `Nat`s is another example: it comes from the
-- `BEq` ("boolean equality") type class. One small but handy fact about it,
-- which several proofs below will need, is that `==` is reflexive:

-- `BEq.refl : (a == a) = true`

-- This is the standard library's version of the `beq_refl` theorem you proved
-- in Induction.

-- We'll learn more about type classes as we go. For now, the key idea is: a
-- type class is an interface, and an instance is an implementation of that
-- interface for a particular type.

-- (For a thorough treatment of type classes, see Chapter 3 of *Functional
-- Programming in Lean*.)

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     Should we replace the above with a forward link to our typeclasses
--     chapter, once we have one?

-- #### Head and Tail

-- The `hd` function returns the first element (the "head") of the list, while
-- `tl` returns everything but the first element (the "tail"). Since the empty
-- list has no first element, we pass a default value to be returned in that
-- case.

def hd (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default
  | h :: _ => h

-- Basic theorems about how `hd` behaves:

theorem hd_cons h x (t : NatList) : (h :: t).hd x = h := by rfl

theorem hd_nil x : [].hd x = x := by rfl

def tl (l : NatList) : NatList :=
  match l with
  | [] => []
  | _ :: t => t

-- Basic theorems about how `tl` behaves:

theorem tl_cons h (t : NatList) : (h :: t).tl = t := by rfl

theorem tl_nil : [].tl = [] := by rfl

example : hd 0 [1, 2, 3] = 1 := by rw [hd_cons]
example : hd 0 [] = 0 := by rw [hd_nil]
example : [1, 2, 3].tl = [2, 3] := by rw [tl_cons]

-- _Quiz:_

-- What does the following function do?

def foo (n : Nat) : NatList :=
  match n with
  | 0 => []
  | n' + 1 => (n' + 1) :: foo n'

-- #### Exercises

-- ### Exercise (2 stars): list_funs ⭐⭐

-- Complete the definitions of `nonzeros`, `oddmembers`, and `countoddmembers`
-- below. Have a look at the tests to understand what these functions should
-- do.

def nonzeros (l : NatList) : NatList := sorry

example : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3] := sorry

-- The following lemmas should hold about your definition

theorem nonzeros_cons_zero (t : NatList) :
  nonzeros (0 :: t) = nonzeros t := sorry
theorem nonzeros_nil :
  nonzeros [] = [] := sorry
theorem nonzeros_cons_nonzero h (t : NatList) :
  nonzeros ((h + 1) :: t) = (h + 1) :: nonzeros t := sorry

def oddmembers (l : NatList) : NatList := sorry

example : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3] := sorry

-- For the next problem, `countoddmembers`, we encourage you to implement it
-- using already-defined functions, rather than recursion.

abbrev countoddmembers (l : NatList) : Nat := sorry

example : countoddmembers [1, 0, 3, 1, 4, 5] = 4 := sorry
example : countoddmembers [0, 2, 4] = 0 := sorry
example : countoddmembers [] = 0 := sorry

-- ### Exercise (3 stars): alternate (Advanced) ⭐⭐⭐

-- Complete the following definition of `alternate`, which interleaves two
-- lists into one, alternating between elements taken from the first list and
-- elements from the second.

-- Hint: there are natural ways of writing `alternate` that fail to satisfy
-- Lean's requirement that all recursive definitions be *structurally
-- recursive*, as mentioned in Basics. If you encounter this difficulty,
-- consider pattern matching against both lists at the same time.

def alternate (l1 l2 : NatList) : NatList := sorry

example : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6] := sorry

example : alternate [1] [4, 5, 6] = [1, 4, 5, 6] := sorry

example : alternate [1, 2, 3] [4] = [1, 4, 2, 3] := sorry
example : alternate ([] : NatList) [20, 30] = [20, 30] := sorry

-- ### Bags via Lists

-- A `bag` (or `multiset`) is like a set, except that each element can appear
-- multiple times rather than just once. One way of representing a bag of
-- numbers is as a list. The following definition introduces a new type,
-- `Bag`, as an abbreviation for `NatList`.

abbrev Bag := NatList
namespace Bag

-- ### Exercise (3 stars): bag_functions ⭐⭐⭐

-- Complete the following definitions for the functions `count`, `sum`, `add`,
-- and `member` for bags.

def count (v : Nat) (s : Bag) : Nat := sorry

-- These lemmas should hold about your definition

theorem count_nil x  : count x [] = 0 := sorry

theorem count_cons_same x y l : (y == x) = true → count x (y :: l) = count x l + 1 := by
  sorry

theorem count_cons_diff x y l : (y == x) = false → count x (y :: l) = count x l := by
  sorry

-- All these proofs can be completed with `rfl`.

example : count 1 [1, 2, 3, 1, 4, 1] = 3 := sorry
example : count 6 [1, 2, 3, 1, 4, 1] = 0 := sorry

-- Multiset `sum` is similar to set `union`: `sum a b` contains all the
-- elements of `a` and those of `b`. (Mathematicians usually define `union` on
-- multisets a little bit differently -- using max instead of sum -- which is
-- why we don't call this operation `union`.)

-- We've deliberately given you a header that does not give explicit names to
-- the arguments. Implement `sum` in terms of an already-defined function,
-- without changing the header.

abbrev sum : Bag → Bag → Bag := sorry

example : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3 := sorry

theorem nil_sum (l : NatList) : sum [] l = l := sorry

theorem cons_sum (n : Nat) (l1 l2 : Bag) : sum (n::l1) l2 = n :: (sum l1 l2) := sorry

abbrev add (v : Nat) (s : Bag) : Bag := sorry

example : count 1 (add 1 [1, 4, 1]) = 3 := by
  sorry
example : count 5 (add 1 [1, 4, 1]) = 0 := by
  sorry

def member (v : Nat) (s : Bag) : Bool := sorry

example : member 1 [1, 4, 1] = true := sorry

example : member 2 [1, 4, 1] = false := sorry

theorem member_nil v : member v [] = false := sorry

theorem member_add_same v t : member v (add v t) = true := by
  sorry

theorem member_add_diff v1 v2 t : (v1 == v2) = false → member v1 (add v2 t) = member v1 t := by
  sorry

-- ### Exercise (3 stars): bag_more_functions ⭐⭐⭐

-- Here are some more `bag` functions for you to practice with.

-- When `remove_one` is applied to a bag without the number to remove, it
-- should return the same bag unchanged. (This exercise is optional, but
-- students following the advanced track will need to fill in the definition
-- of `remove_one` for a later exercise.)

-- Note to developers (before next release):
--     BCP 25: At Penn this year, we removed the distinction between standard
--     and advanced tracks, which made the wording above confusing. Maybe just
--     make this an exercise for everybody?

def remove_one (v : Nat) (s : Bag) : Bag := sorry

example : count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0 := sorry
example : count 5 (remove_one 5 [2, 1, 4, 1]) = 0 := sorry
example : count 4 (remove_one 5 [2, 1, 4, 5, 1, 4]) = 2 := sorry

example : count 5 (remove_one 5 [2, 1, 5, 4, 5, 1, 4]) = 1 := sorry

theorem remove_one_nil v : remove_one v [] = [] := sorry

theorem remove_one_add_same v1 v2 t : (v2 == v1) = true → remove_one v1 (add v2 t) = t := by
  sorry

theorem remove_one_add_diff v1 v2 t : (v2 == v1) = false → remove_one v1 (add v2 t) = add v2 (remove_one v1 t) := by
  sorry

def remove_all (v : Nat) (s : Bag) : Bag := sorry

example : count 5 (remove_all 5 [2, 1, 5, 4, 1]) = 0 := sorry
example : count 5 (remove_all 5 [2, 1, 4, 1]) = 0 := sorry
example : count 4 (remove_all 5 [2, 1, 4, 5, 1, 4]) = 2 := sorry

example : count 5 (remove_all 5 [2, 1, 5, 4, 5, 1, 4, 5, 1, 4]) = 0 := sorry

theorem remove_all_nil v : remove_all v [] = [] := sorry

theorem remove_all_add_same v t : remove_all v (add v t) = remove_all v t := by
  sorry

theorem remove_all_add_diff v1 v2 t : (v2 == v1) = false → remove_all v1 (add v2 t) = add v2 (remove_all v1 t) := by
  sorry

def included (s1 s2 : Bag) : Bool := sorry

example : included [1, 2] [2, 1, 4, 1] = true := sorry

example : included [1, 2, 2] [2, 1, 4, 1] = false := sorry

theorem included_nil s : included [] s = true := sorry

theorem included_add_member v s1 s2 : member v s2 = true → included (add v s1) s2 = included s1 (remove_one v s2) := by
  sorry

theorem included_add_nonmember v s1 s2 : member v s2 = false → included (add v s1) s2 = false := by
  sorry

-- ### Exercise (2 stars): add_inc_count (manually graded) ⭐⭐

-- Adding a value to a bag should increase the value's count by one. State
-- this as a theorem and prove it.

-- FILL IN HERE

end Bag

-- ## Reasoning About Lists

-- As with numbers, simple facts about list-processing functions can sometimes
-- be proved entirely by rewriting. For example, just rewriting the left-hand
-- side of the following equality using the theorem `nil_append` is enough for
-- this theorem...

theorem nil_app (l : NatList) : ([] : NatList) ++ l = l := by rw [nil_append]

-- ...because the `[]` is substituted into the "scrutinee" (the expression
-- whose value is being "scrutinized" by the match) in the definition of
-- `app`, allowing the match itself to be simplified.

-- Also, as with numbers, it is sometimes helpful to perform case analysis on
-- the possible shapes -- empty or non-empty -- of an unknown list.

theorem tl_length_pred (l : NatList) :
    l.length.pred = l.tl.length := by
  cases l with
  | nil       => rw [tl_nil, nil_length]; dsimp
  | cons n l' => rw [tl_cons, cons_length]; dsimp

-- Here, the `nil` case works because we've chosen to define `tl [] = []`.
-- Notice that the `cons` case introduces two names, `n` and `l'`,
-- corresponding to the fact that the `cons` constructor for lists takes two
-- arguments (the head and tail of the list it is constructing).

-- Usually, though, interesting theorems about lists require induction for
-- their proofs. We'll see how to do this next.

-- (Micro-Sermon: As we get deeper into this material, simply *reading* proof
-- scripts will not help you very much. Rather, it is important to step
-- through the details of each one using Lean and think about what each step
-- achieves. Otherwise it is more or less guaranteed that the exercises will
-- make no sense when you get to them. 'Nuff said.)

-- ### Induction on Lists

-- Proofs by induction over datatypes like `NatList` are a little less
-- familiar than standard natural number induction, but the idea is equally
-- simple. Each `inductive` declaration defines a set of data values that can
-- be built up using the declared constructors. For example, a boolean can be
-- either `true` or `false`; a number can be either `0` or else `succ` applied
-- to another number; and a list can be either `[]` or else `::` applied to a
-- number and a list. Moreover, applications of the declared constructors to
-- one another are the *only* possible shapes that elements of an inductively
-- defined set can have.

-- This last fact directly gives rise to a way of reasoning about inductively
-- defined sets: a number is either `0` or else it is `succ` applied to some
-- *smaller* number; a list is either `[]` or else it is `::` applied to some
-- number and some *smaller* list; etc. Thus, if we have in mind some
-- proposition `P` that mentions a list `l` and we want to argue that `P`
-- holds for *all* lists, we can reason as follows:

-- - First, show that `P` is true of `l` when `l` is `[]`.

-- - Then show that `P` is true of `l` when `l` is `n :: l'` for some number `n`
--   and some smaller list `l'`, assuming that `P` is true for `l'`.

-- Since larger lists can always be broken down into smaller ones, eventually
-- reaching `[]`, these two arguments together establish the truth of `P` for
-- all lists `l`.

-- Here's a concrete example:

theorem app_assoc (l1 l2 l3 : NatList) :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  induction l1 with
  | nil =>
    rw [nil_append, nil_append]
  | cons n l1' ih =>
    rw [cons_append, cons_append, cons_append, ih]

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     What's the best Lean markup for a displayed equation? The markup below
--     is going to get squished into a paragraph with all the rest by default,
--     but IMO it would look better as a separate display. Also: Are we going
--     to consistently write Qed at the end of proofs? We should agree on a
--     convention.

-- *Theorem*: For all lists `l1`, `l2`, and `l3`,
-- `(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)`.

-- *Proof*: By induction on `l1`.

-- - First, suppose `l1 = []`. We must show

--   ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

-- which follows directly from the definition of `app`.

-- - Next, suppose `l1 = n :: l1'`, with

--   (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

-- (the induction hypothesis). We must show

--   ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

-- By the definition of `app`, this follows from

--   n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

-- which is immediate from the induction hypothesis. *Qed*.

-- #### Generalizing Statements

-- In some situations, it is necessary to generalize a statement in order to
-- prove it by induction. Intuitively, the reason is that a more general
-- statement also yields a more general (stronger) inductive hypothesis.

example (c n : Nat) :
    myRepeat n c ++ myRepeat n c = myRepeat n (c + c) := by
  induction c with
  | zero => rw [repeat_zero, nil_append]
  | succ c' ih =>
    rw [repeat_succ]
    -- Now we seem to be stuck.  The IH only works for c' + c',
    -- but we need c' + 1 + (c' + 1).
    sorry

-- To get a more general inductive hypothesis, we can generalize:

theorem myRepeat_plus (c1 c2 n : Nat) :
    myRepeat n c1 ++ myRepeat n c2 = myRepeat n (c1 + c2) := by
  induction c1 with
  | zero =>
    rw [repeat_zero, Nat.zero_add, nil_append]
  | succ c1' ih =>
    rw [Nat.succ_add, repeat_succ, repeat_succ, cons_append, ih]

-- #### Reversing a List

-- For a slightly more involved example of inductive proof over lists, suppose
-- we use `app` to define a list-reversing function `rev`:

def rev (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => t.rev ++ [h]

theorem rev_nil : [].rev = [] := by rfl

theorem rev_cons h (t : NatList) : (h :: t).rev = t.rev ++ [h] := by rfl

example : [1, 2, 3].rev = [3, 2, 1] := by rfl

example : ([] : NatList).rev = [] := by rfl

-- For something a bit more challenging, let's prove that reversing a list
-- does not change its length. Our first attempt gets stuck in the successor
-- case...

example (l : NatList) :
    l.rev.length = l.length := by
  induction l with
  | nil => rw [rev_nil]
  | cons n l' ih =>
    rw [rev_cons]
    -- Now we seem to be stuck: the goal involves `++`,
    -- but we don't have any useful equations
    -- in either the immediate context or in the global
    -- environment!
    sorry

-- A first attempt to make progress would be to prove exactly the statement
-- that we are missing at this point. But this attempt will fail because the
-- inductive hypothesis is not general enough.

example (l : NatList) n :
    (l.rev ++ [n]).length = .succ l.rev.length := by
  induction l with
  | nil =>
    rw [rev_nil, nil_append, cons_length, nil_length]
  | cons n l' ih =>
    rw [rev_cons]
    -- ih not applicable
    sorry

-- It turns out that the above lemma is more specific than it needs to be. We
-- can strengthen the lemma to work not only on reversed lists but on general
-- lists.

theorem app_length_succ (l : NatList) (n : Nat) :
    (l ++ [n]).length = l.length + 1 := by
  induction l with
  | nil => rw [nil_append, cons_length]
  | cons m l' ih =>
    rw [cons_append, cons_length, ih, cons_length]

-- Now we can prove the main theorem.

theorem rev_length (l : NatList) :
    l.rev.length = l.length := by
  induction l with
  | nil => rw [rev_nil]
  | cons n l' ih =>
    rw [rev_cons, app_length_succ, ih, cons_length]

-- We can also prove a more general form that gives the length of any two
-- appended lists.

theorem app_length (l1 l2 : NatList) :
    (l1 ++ l2).length = l1.length + l2.length := by
  all_goals
    induction l1 with
    | nil => rw [nil_append, nil_length, Nat.zero_add]
    | cons n l1' ih =>
      rw [cons_append, cons_length, ih, cons_length, Nat.succ_add]

-- For comparison, here are informal proofs of these two theorems:

-- *Theorem*: For all lists `l1` and `l2`,
-- `(l1 ++ l2).length = l1.length + l2.length`.

-- *Proof*: By induction on `l1`.

-- - First, suppose `l1 = []`. We must show

--   ([] ++ l2).length = [].length + l2.length,

-- which follows directly from the definitions of `length`, `++`, and `+`.

-- - Next, suppose `l1 = n::l1'`, with

--   (l1' ++ l2).length = l1'.length + l2.length

-- We must show

--   ((n::l1') ++ l2).length = (n::l1').length + l2.length.

-- This follows directly from the definitions of `length` and `++` together
-- with the induction hypothesis. *Qed*.

-- *Theorem*: For all lists `l`, `l.rev.length = l.length`.

-- *Proof*: By induction on `l`.

-- - First, suppose `l = []`. We must show

--   [].rev.length = [].length,

-- which follows directly from the definitions of `length` and `rev`.

-- - Next, suppose `l = n::l'`, with

--   l'.rev.length = l'.length

-- We must show

--   (n :: l').rev.length = (n :: l').length.

-- By the definition of `rev`, this follows from

--   (l'.rev ++ [n]).length = .succ (l'.length),

-- which, by the previous lemma, is the same as

--   l'.rev.length + [n].length = .succ (l'.length).

-- This follows directly from the induction hypothesis and the definition of
-- `length`. *Qed*.

-- The style of these proofs is rather longwinded and pedantic. After reading
-- a couple like this, we might find it easier to follow proofs that give
-- fewer details (which we can easily work out in our own minds or on scratch
-- paper if necessary) and just highlight the non-obvious steps. In this more
-- compressed style, the above proof might look like this:

-- *Theorem*: For all lists `l`, `l.rev.length = l.length`.

-- *Proof*: First observe, by a straightforward induction on `l`, that
-- `(l ++ [n]).length = .succ l.length` for any `l`. The main property then
-- follows by another induction on `l`, using the observation together with
-- the induction hypothesis in the case where `l = n'::l'`. *Qed*

-- Which style is preferable in a given situation depends on the
-- sophistication of the expected audience and how similar the proof at hand
-- is to ones that they will already be familiar with. The more pedantic style
-- is a good default for our present purposes because we're trying to be
-- ultra-clear about the details.

-- ### Search

-- We've seen that proofs can make use of other theorems we've already proved,
-- e.g., using `rw`. But in order to refer to a theorem, we need to know its
-- name!

-- In Lean, the `exact?` tactic will search for a lemma that closes the
-- current goal. The `#check` command shows the type of a named theorem. You
-- can also use `example` with `exact?` to search for lemmas matching a
-- particular pattern.

-- Your IDE likely has its own search functionality too. In VS Code with the
-- Lean 4 extension, you can use Ctrl+T to search for definitions by name.

-- ### List Exercises, Part 1

-- ### Exercise (3 stars): list_exercises ⭐⭐⭐

-- More practice with lists:

theorem app_nil_r (l : NatList) :
    l ++ ([] : NatList) = l := by
  sorry

theorem rev_app_distr (l1 l2 : NatList) :
   (l1 ++ l2).rev = l2.rev ++ l1.rev := by
  sorry

-- An *involution* is a function that is its own inverse. That is, applying
-- the function twice yields the original input.

theorem rev_involutive (l : NatList) :
    l.rev.rev = l := by
  sorry

-- There is a short solution to the next one. If you find yourself getting
-- tangled up, step back and try to look for a simpler way.

theorem app_assoc4 (l1 l2 l3 l4 : NatList) :
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4 := by
  sorry

-- An exercise about your implementation of `nonzeros`:

theorem nonzeros_app (l1 l2 : NatList) :
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2) := by
  sorry

-- ### Exercise (2 stars): eqblist ⭐⭐

-- Fill in the definition of `eqblist`, which compares lists of numbers for
-- equality. Prove that `eqblist l l` yields `true` for every list `l`.

def eqblist (l1 l2 : NatList) : Bool := sorry

theorem eqblist_nil : eqblist [] [] = true := sorry

theorem eqblist_cons_same h t1 t2 : eqblist (h :: t1) (h :: t2) = eqblist t1 t2 := by
  sorry

theorem eqblist_cons_diff h1 h2 t1 t2 : (h1 == h2) = false → eqblist (h1 :: t1) (h2 :: t2) = false := by
  sorry

example : eqblist [] [] = true := sorry
example : eqblist [1, 2, 3] [1, 2, 3] = true := sorry
example : eqblist [1, 2, 3] [1, 2, 4] = false := sorry

theorem eqblist_refl (l : NatList) :
    eqblist l l = true := by
  sorry

-- ### List Exercises, Part 2

open Bag

-- Here are a couple of little theorems to prove about your definitions about
-- bags above.

-- ### Exercise (1 star): count_member_nonzero ⭐

theorem count_member_nonzero (s : Bag) :
    Nat.ble 1 (count 1 (1 :: s)) = true := by
  sorry

-- The following lemma about `Nat.ble` might help you in the next exercise (it
-- will also be useful in later chapters).

theorem ble_n_Sn (n : Nat) :
    Nat.ble n (n + 1) = true := by
  induction n with
  | zero       => rfl
  | succ n' ih => dsimp [Nat.ble]; exact ih

-- Before doing the next exercise, make sure you've filled in the definition
-- of `remove_one` above.

-- ### Exercise (3 stars): remove_does_not_increase_count (Advanced) ⭐⭐⭐

theorem remove_does_not_increase_count (s : Bag) :
    Nat.ble (count 0 (remove_one 0 s)) (count 0 s) = true := by
  sorry

-- ### Exercise (3 stars): bag_count_sum (manually graded) ⭐⭐⭐

-- Write down an interesting theorem `bag_count_sum` about bags involving the
-- functions `count` and `sum`, and prove it. (You may find that the
-- difficulty of the proof depends on how you defined `count`!

-- FILL IN HERE

-- ### Exercise (3 stars): involution_injective (Advanced) ⭐⭐⭐

-- Prove that every involution is injective.

-- Involutions were defined above in `rev_involutive`. An *injective* function
-- is one-to-one: it maps distinct inputs to distinct outputs, without any
-- collisions.

theorem involution_injective (f : Nat → Nat) :
    (∀ n : Nat, n = f (f n)) →
    (∀ n1 n2 : Nat, f n1 = f n2 → n1 = n2) := by
  sorry

-- ### Exercise (2 stars): rev_injective (Advanced) ⭐⭐

-- Prove that `rev` is injective. Do not prove this by induction -- that would
-- be hard. Instead, re-use the same proof technique that you used for
-- `involution_injective`. (But: Don't try to use that exercise directly as a
-- lemma: the types are not the same!)

theorem rev_injective (l1 l2 : NatList) :
  l1.rev = l2.rev → l1 = l2 := by
  sorry

-- ## Options

-- Suppose we want to write a function that returns the `n`th element of some
-- list. If we give it type `NatList → Nat → Nat`, then we'll have to choose
-- some number to return when the list is too short...

def nth_bad (l : NatList) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' => match n with
    | 0 => a
    | n' + 1 => nth_bad l' n'

-- This solution is not so good: If `nth_bad` returns 42, we don't know
-- whether that value actually appears in the input or whether we gave bad
-- arguments. A better alternative is to change the return type to include an
-- error value as a possible outcome. We call this new type `NatOption`.

inductive NatOption : Type where
  | some (n : Nat)
  | none

-- We can then change the above definition of `nth_bad` to return `none` when
-- the list is too short and `some a` when the list has enough members and `a`
-- appears at position `n`. We call this new function `nth_error` to indicate
-- that it may result in an error.

def nth_error (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => .none
  | a :: l' => match n with
    | 0 => .some a
    | n' + 1 => nth_error l' n'

example : nth_error [4, 5, 6, 7] 0 = .some 4 := by rfl
example : nth_error [4, 5, 6, 7] 3 = .some 7 := by rfl
example : nth_error [4, 5, 6, 7] 9 = .none := by rfl

-- The function below pulls the `Nat` out of a `NatOption`, returning a
-- supplied default in the `none` case.

def option_elim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n => n
  | .none => d

theorem option_elim_none d : option_elim d .none = d := by rfl

theorem option_elim_some d1 d2 : option_elim d1 (.some d2) = d2 := by rfl

-- ### Exercise (2 stars): hd_error ⭐⭐

-- Using the same idea, fix the `hd` function from earlier so we don't have to
-- pass a default element for the `nil` case.

def hd_error (l : NatList) : NatOption := sorry

example : hd_error ([] : NatList) = .none := sorry
example : hd_error [1] = .some 1 := sorry
example : hd_error [5, 6] = .some 5 := sorry

theorem hd_error_nil : hd_error [] = .none := sorry

theorem hd_error_cons h t : hd_error (h :: t) = .some h := sorry

-- ### Exercise (1 star): option_elim_hd ⭐

-- This exercise relates your new `hd_error` to the old `hd`.

theorem option_elim_hd (l : NatList) (default : Nat) :
    hd default l = option_elim default (hd_error l) := by
  sorry

end NatList

-- ## Partial Maps

-- As a final illustration of how data structures can be defined in Lean, here
-- is a simple *partial map* data type, analogous to the map or dictionary
-- data structures found in most programming languages.

-- First, we define a new type `MyId` to serve as the "keys" of our partial
-- maps.

structure MyId where
  val : Nat

-- Internally, a `MyId` is just a number. Introducing a separate type by
-- wrapping each `Nat` makes definitions more readable and gives us
-- flexibility to change representations later if we want to.

-- We'll also need an equality test for `MyId`s:

def eqb_id (x1 x2 : MyId) : Bool :=
  x1.val == x2.val

-- ### Exercise (1 star): eqb_id_refl ⭐

theorem eqb_id_refl (x : MyId) : eqb_id x x = true := by
  sorry

-- Now we define the type of partial maps:

inductive PartialMap : Type where
  | empty : PartialMap
  | record (i : MyId) (v : Nat) (m : PartialMap) : PartialMap

-- This declaration can be read: "There are two ways to construct a
-- `PartialMap`: either using the constructor `empty` to represent an empty
-- partial map, or applying the constructor `record` to a key, a value, and an
-- existing `PartialMap` to construct a `PartialMap` with an additional
-- key-to-value mapping."

namespace PartialMap

-- The `update` function overrides the entry for a given key in a partial map
-- by shadowing it with a new one (or simply adds a new entry if the given key
-- is not already present).

def update (d : PartialMap) (x : MyId) (value : Nat) : PartialMap :=
  record x value d

-- Last, the `find` function searches a `PartialMap` for a given key. It
-- returns `none` if the key was not found and `some val` if the key was
-- associated with `val`. If the same key is mapped to multiple values, `find`
-- will return the first one it encounters.

def find (x : MyId) (d : PartialMap) : Option Nat :=
  match d with
  | empty => none
  | record y v d' =>
    bif eqb_id x y then some v
    else find x d'

-- _Quiz:_

-- Is the following claim true or false?

theorem quiz1 (d : PartialMap) (x : MyId) (v : Nat) :
    find x (update d x v) = some v := by
  dsimp [update, find]
  rw [eqb_id_refl]
  dsimp

-- (A) True (B) False (C) Not sure

-- _Quiz:_

-- Is the following claim true or false?

theorem quiz2  (d : PartialMap) (x y : MyId) (o : Nat) :
    eqb_id x y = false →
    find x (update d y o) = find x d := by
  intro h
  dsimp [update, find]
  rw [h]
  dsimp

-- (A) True (B) False (C) Not sure

-- ### Exercise (1 star): update_eq ⭐

theorem update_eq (d : PartialMap) (x : MyId) (v : Nat) :
    find x (update d x v) = some v := by
  sorry

-- ### Exercise (1 star): update_neq ⭐

theorem update_neq (d : PartialMap) (x y : MyId) (o : Nat) :
    eqb_id x y = false → find x (update d y o) = find x d := by
  sorry

end PartialMap

end Lists


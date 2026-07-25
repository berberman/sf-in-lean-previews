import LF.Induction
import LF.UsingLean

import LF.SFLCompat

-- # Lists: Working with Structured Data

-- Note to developers (Daniel Sainati  @dsainati1):
--     [BCP: Old comment -- might be out of date?] Weird that
--     this file contains the first `inductive` definition
--     students have seen up to this point, but that definition
--     is also actually a `structure`. Probably need to
--     restructure this.
--
--     Unsure if it's a good idea to actually use the built-in
--     `List` definition here, since it's polymorphic, and we
--     aren't introducing this idea until a later chapter. This
--     also means we don't get the chance to show students how
--     to actually produce an inductive definition if we're
--     relying on the built-in ones.
--
--     We probably need to actually take time to explain what a
--     `@[simp]` annotation on a lemma means before we
--     introduce it, and I don't think this chapter is the
--     right place to do it anyway. This is probably a better
--     fit for `Auto.lean`.
--
--     Claude picked a bad definition for `nonzeroes`:
--
--     `match l with
--       | [] => []
--       | 0 :: t => nonZeros t
--       | h :: t => h :: nonZeros t`
--
--     which makes many of the later proofs hard to do without
--     the full automation of `simp`. I changed it, but it's
--     worth pointing this out.

-- Note to developers (Konstantinos Kallas  @angelhof):
--     The `Baz` "how many elements does this type have?"
--     exercise (the last exercise in the chapter) is a
--     **manual** exercise, and that's a poor fit: a student
--     who doesn't realize an inductive definition needs a base
--     case will simply fail it and only see why in the grader
--     comment — and it's easy to wrongly think you have the
--     right answer and move on without thinking. Better to
--     either add a short section that explains this directly,
--     or add a hint like the `one_true_baz` / `count_trues`
--     scaffold ("try to write a value of type `Baz` for which
--     the lemma holds"). Worth reworking for easier grading.

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

namespace Lists

-- Note to developers (before next release):
--     Note that rewrite laws should sometimes differ from
--     pattern matching now

-- ## Pairs of Numbers

-- An inductive definition of pairs of numbers. It has just one
-- constructor, taking two arguments:

inductive NatProd where
  | pair (n1 n2 : Nat)

#check (NatProd.pair 3 5)

-- Functions for extracting the first and second components of
-- a pair can then be defined by pattern matching.

def NatProd.fst (p : NatProd) : Nat :=
  match p with
  | .pair x _ => x

def NatProd.snd (p : NatProd) : Nat :=
  match p with
  | .pair _ y => y

-- Defining these functions with the `NatProd` type name
-- qualifying their name allows us to use them with `.`
-- notation:

example : (NatProd.pair 3 5).fst = 3 := by rfl

-- A nicer notation for pairs:

example : (⟨3, 5⟩ : NatProd).fst = 3 := by rfl

-- The anonymous constructor can be used in both expressions
-- and in pattern matches.

def NatProd.fst' (p : NatProd) : Nat :=
  match p with
  | ⟨x, _⟩ => x

def NatProd.snd' (p : NatProd) : Nat :=
  match p with
  | ⟨_, y⟩ => y

def NatProd.swap (p : NatProd) : NatProd :=
  ⟨snd p, fst p⟩

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     Wrote this, let me know how it reads.

-- Lean also provides a convenient way to define `inductive`
-- structures like pairs that have a single constructor but
-- multiple ways to access their data, using the `structure`
-- keyword. The definition of `NatProd'` below is equivalent to
-- the `NatProd` definition from earlier, except that Lean
-- automatically generates the `fst` and `snd` accessors.

structure NatProd' where
  fst : Nat
  snd : Nat

#check (NatProd'.mk 3 5)
example : (NatProd'.mk 3 5).fst = 3 := by rfl
example : (⟨3, 5⟩ : NatProd').fst = 3 := by rfl

-- To expose the structure of a pair, use `cases` (or
-- destructuring).

theorem surjective_pairing : ∀ p : NatProd,
    p = ⟨p.fst, p.snd⟩ := by
  intro ⟨n, m⟩; rfl

theorem surjective_pairing_cases (p : NatProd) :
    p = ⟨p.fst, p.snd⟩ := by
  cases p; rfl

-- ## Lists of Numbers

-- An inductive definition of *lists* of numbers:

inductive NatList : Type where
  | nil
  | cons (n : Nat) (l : NatList)

-- By convention, we place the operations (functions) of an
-- inductive type inside the namespace implicitly created by
-- that type's definition.

namespace NatList

-- Some notation for lists to make our lives easier:

-- Don't worry too much about what this is doing:

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     Can we be a little more helpful, or tell them when we
--     are going to tell them, or tell them where to look?

scoped infixr:65 " :: " => cons
scoped macro (priority := high) "[ " elems:term,* "]" : term => do
  elems.getElems.foldrM (``(cons $(⟨·⟩) $(⟨·⟩))) (← ``(nil))

-- Now these all mean exactly the same thing:

def mylist1 : NatList := 1 :: (2 :: (3 :: []))
def mylist2 : NatList := 1 :: 2 :: 3 :: []
def mylist3 : NatList := [1, 2, 3]

-- Some useful list-manipulation functions...

-- ### Repeat

def myRepeat (n count : Nat) : NatList :=
  match count with
  | 0 => []
  | count' + 1 => n :: myRepeat n count'

-- Some simple facts about repetition:

theorem repeat_zero v : myRepeat v 0 = [] := rfl

theorem repeat_succ v count : myRepeat v (count + 1) = v :: myRepeat v count := rfl

def length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => (length t) + 1

-- Some simple facts about list lengths:

theorem length_nil : [].length = 0 := rfl

theorem length_cons (n : Nat) (l : NatList) : (n::l).length = l.length + 1 := rfl

-- ### Append

def app (l1 l2 : NatList) : NatList :=
  match l1 with
  | [] => l2
  | h :: t => h :: app t l2

-- ### Type Classes and Overloading

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     One word, or two?

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
--     Experiment: introduce `BEq.refl` here, at the point
--     where the `BEq` class is named.

-- Note to developers (Chris Henson  @chenson2018):
--     The way that this is written might mislead the student
--     to think it is inherent to BEq, which is not true: this
--     additionally requires the ReflBEq typeclass. How crucial
--     is it to have this early mention of typeclasses?
--     bcpierce00: Hopefully we can postpone it.

-- `==` comes from the `BEq` class;
-- `BEq.refl : (a == a) = true` is worth knowing by name.

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     Should we replace the above with a forward link to our
--     typeclasses chapter, once we have one?

-- #### Head and Tail

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

-- ### Bags via Lists

def Bag := NatList

namespace Bag

@[match_pattern]
def empty : Bag := []

theorem empty_def : empty = [] := rfl

def is_empty (s : Bag) : Bool :=
  match s with
  | empty => true
  | _ => false

end Bag

-- ## Reasoning About Lists

-- As with numbers, some proofs about list functions need only
-- rewriting...

theorem nil_app (l : NatList) : ([] : NatList) ++ l = l := by rw [nil_append]

-- ...and some need case analysis.

theorem tl_length_pred (l : NatList) :
    l.length.pred = l.tl.length := by
  cases l with
  | nil       => rw [tl_nil, length_nil]; dsimp
  | cons n l' => rw [tl_cons, length_cons]; dsimp

-- Usually, though, interesting theorems about lists require
-- induction for their proofs. We'll see how to do this next.

-- ### Induction on Lists

-- Lean generates an induction principle for every `inductive`
-- definition, including lists. We can use the `induction`
-- tactic on lists to prove things like the associativity of
-- list-append...

theorem app_assoc (l1 l2 l3 : NatList) :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  induction l1 with
  | nil =>
    rw [nil_append, nil_append]
  | cons n l1' ih =>
    rw [cons_append, cons_append, cons_append, ih]

-- For comparison, here is an informal proof of the same
-- theorem.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     What's the best Lean markup for a displayed equation?
--     The markup below is going to get squished into a
--     paragraph with all the rest by default, but IMO it would
--     look better as a separate display. Also: Are we going to
--     consistently write Qed at the end of proofs? We should
--     agree on a convention.

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

-- Sometimes statements need to be generalized to prove them by
-- induction:

example (c n : Nat) :
    myRepeat n c ++ myRepeat n c = myRepeat n (c + c) := by
  induction c with
  | zero => rw [repeat_zero, nil_append]
  | succ c' ih =>
    rw [repeat_succ]
    -- Now we seem to be stuck.  The IH only works for c' + c',
    -- but we need c' + 1 + (c' + 1).
    sorry

-- A generalization that gives a stronger inductive hypothesis:

theorem myRepeat_plus (c1 c2 n : Nat) :
    myRepeat n c1 ++ myRepeat n c2 = myRepeat n (c1 + c2) := by
  induction c1 with
  | zero =>
    rw [repeat_zero, Nat.zero_add, nil_append]
  | succ c1' ih =>
    rw [Nat.succ_add, repeat_succ, repeat_succ, cons_append, ih]

-- #### Reversing a List

-- A more interesting example of induction over lists:

def rev (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => t.rev ++ [h]

theorem rev_nil : [].rev = [] := by rfl

theorem rev_cons h (t : NatList) : (h :: t).rev = t.rev ++ [h] := by rfl

example : [1, 2, 3].rev = [3, 2, 1] := by rfl

example : ([] : NatList).rev = [] := by rfl

-- Let's try to prove `length (rev l) = length l`.

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

example (l : NatList) n :
    (l.rev ++ [n]).length = .succ l.rev.length := by
  induction l with
  | nil =>
    rw [rev_nil, nil_append, length_cons, length_nil]
  | cons n l' ih =>
    rw [rev_cons]
    -- ih not applicable
    sorry

theorem app_length_succ (l : NatList) (n : Nat) :
    (l ++ [n]).length = l.length + 1 := by
  induction l with
  | nil => rw [nil_append, length_cons]
  | cons m l' ih =>
    rw [cons_append, length_cons, ih, length_cons]

-- Now we can prove the main theorem.

theorem rev_length (l : NatList) :
    l.rev.length = l.length := by
  induction l with
  | nil => rw [rev_nil]
  | cons n l' ih =>
    rw [rev_cons, app_length_succ, ih, length_cons]

theorem app_length (l1 l2 : NatList) :
    (l1 ++ l2).length = l1.length + l2.length := by
  sorry

-- _Quiz:_

-- To prove the following theorem, which tactics will we need
-- besides `intro`, `dsimp`, `rw`, and `rfl`? (A) none, (B)
-- `cases`, (C) `induction` on `n`, (D) `induction` on `l`, or
-- (E) can't be done with the tactics we've seen.

--   theorem foo1 : ∀ n : Nat, ∀ l : NatList,
--     myRepeat n 0 = l → l.length = 0

-- _Quiz:_

-- What about the next one?

--   theorem foo2 :  ∀ n m : Nat,
--     (myRepeat n m).length = m

-- Which tactics do we need besides `intro`, `dsimp`, `rw`, and
-- `rfl`? (A) none, (B) `cases`, (C) `induction` on `n`, (D)
-- `induction` on `m`, or (E) can't be done with the tactics
-- we've seen.

-- ### Search

-- ### List Exercises, Part 1

-- ### List Exercises, Part 2

open Bag

-- ## Options

-- Suppose we'd like a function to retrieve the `n`th element
-- of a list. What to do if the list is too short?

def nth_bad (l : NatList) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' => match n with
    | 0 => a
    | n' + 1 => nth_bad l' n'

-- The solution: return a `NatOption`.

inductive NatOption : Type where
  | some (n : Nat)
  | none

def nth_error (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => .none
  | a :: l' => match n with
    | 0 => .some a
    | n' + 1 => nth_error l' n'

example : nth_error [4, 5, 6, 7] 0 = .some 4 := by rfl
example : nth_error [4, 5, 6, 7] 3 = .some 7 := by rfl
example : nth_error [4, 5, 6, 7] 9 = .none := by rfl

def option_elim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n => n
  | .none => d

theorem option_elim_none d : option_elim d .none = d := by rfl

theorem option_elim_some d1 d2 : option_elim d1 (.some d2) = d2 := by rfl

end NatList

-- ## Partial Maps

-- As a final illustration of how data structures can be
-- defined in Lean, here is a simple *partial map* data type,
-- analogous to the map or dictionary data structures found in
-- most programming languages.

-- First, we define a new type `MyId` to serve as the "keys" of
-- our partial maps.

structure MyId where
  val : Nat

-- Internally, a `MyId` is just a number. Introducing a
-- separate type by wrapping each `Nat` makes definitions more
-- readable and gives us flexibility to change representations
-- later if we want to.

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

namespace PartialMap

-- The `update` function overrides the entry for a given key in
-- a partial map by shadowing it with a new one (or simply adds
-- a new entry if the given key is not already present).

def update (d : PartialMap) (x : MyId) (value : Nat) : PartialMap :=
  record x value d

-- We can define functions on `PartialMap`s by pattern
-- matching.

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

end PartialMap

end Lists


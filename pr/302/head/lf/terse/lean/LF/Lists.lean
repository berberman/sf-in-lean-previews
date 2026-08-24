import LF.Induction
import LF.UsingLean

import LF.SFLCompat

-- # Lists: Working with Structured Data

namespace Lists

-- ## Pairs of Numbers

-- An inductive definition of pairs of numbers. It has just one
-- constructor, taking two arguments:

inductive NatProd where
  | pair (n1 n2 : Nat)

#check (NatProd.pair 3 5)

-- Note to developers (Mike Hicks @mwhicks1):
--     I would have expected us to have `namespace NatProd`
--     here when defining the following functions, so we don't
--     need qualifiers. We've already full explained namespaces
--     back in Basics. Some of the text below mentions using
--     the `NatProd` prefix specifically, but I think you can
--     drop it and it will stick work.

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

-- To expose the structure of a pair, use `cases` (or
-- destructuring).

theorem surjective_pairing : ∀ p : NatProd,
    p = ⟨p.fst, p.snd⟩ := by
  intro ⟨n, m⟩; rfl

theorem surjective_pairing_cases (p : NatProd) :
    p = ⟨p.fst, p.snd⟩ := by
  cases p; rfl

-- ## Structures

-- Lean's `structure` is shorthand for a single-constructor
-- `inductive` with the accessors auto-generated.

structure NatProd' where
  fst : Nat
  snd : Nat

#check (NatProd'.mk 3 5)
example : (NatProd'.mk 3 5).fst = 3 := by rfl
example : (⟨3, 5⟩ : NatProd').fst = 3 := by rfl

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

-- Don't worry too much about how this works.

-- THESE DETAILS CAN BE SKIPPED: List syntax

-- We first define `::` as right-associative notation for
-- `cons`, and then define list notation as a *macro*, allowing
-- us to write `[1, 2]` instead of `1 :: 2 :: []`. The
-- *unexpander* reverses the macro, translating list syntax
-- back to cons syntax.

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

-- END DETAILS

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

theorem repeat_zero (n : Nat) : myRepeat n 0 = [] := rfl

theorem repeat_succ (n count : Nat) : myRepeat n (count + 1) = n :: myRepeat n count := rfl

def length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => (length t) + 1

-- Some simple facts about list lengths:

theorem length_nil : [].length = 0 := rfl

theorem length_cons (n : Nat) (l : NatList) : (n :: l).length = l.length + 1 := rfl

-- ### Append

def append (l₁ l₂ : NatList) : NatList :=
  match l₁ with
  | [] => l₂
  | h :: t => h :: append t l₂

-- ### Type Classes and Overloading

-- Note to developers (Benjamin Pierce @bcpierce00):
--     One word, or two?

instance : HAppend NatList NatList NatList where
  hAppend := append

-- Now `l₁ ++ l₂` means `append l₁ l₂` within `NatList`.

-- Some simple facts about appending lists:

theorem nil_append (l : NatList) : [] ++ l = l := rfl

theorem cons_append (n : Nat) (l₁ l₂ : NatList) : (n :: l₁) ++ l₂ = n :: (l₁ ++ l₂) := rfl

example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := by rfl
example : [] ++ [4, 5] = [4, 5] := by rfl
example : [1, 2, 3] ++ [] = [1, 2, 3] := by rfl

-- `BEq.refl : (a == a) = true` is worth knowing by name.

-- #### Head and Tail

def head (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default
  | h :: _ => h

-- Basic theorems about how `head` behaves:

theorem head_cons (h x : Nat) (t : NatList) : (h :: t).head x = h := by rfl

theorem head_nil (x : Nat) : [].head x = x := by rfl

def tail (l : NatList) : NatList :=
  match l with
  | [] => []
  | _ :: t => t

-- Basic theorems about how `tail` behaves:

theorem tail_cons (h : Nat) (t : NatList) : (h :: t).tail = t := by rfl

theorem tail_nil : [].tail = [] := by rfl

-- _Quiz:_

-- What does the following function do?

def foo (n : Nat) : NatList :=
  match n with
  | 0 => []
  | n' + 1 => (n' + 1) :: foo n'

-- #### Exercises

-- ### Counting

-- ### Exercise (1 star): counting ⭐

-- Define a `count` function for `NatList`s that counts the
-- number of times an element `n` appears in the list.

def count (n : Nat) (l : NatList) : Nat := sorry

-- Now, prove these lemmas which should hold about your
-- definition.

theorem count_nil (n : Nat) : count n [] = 0 := sorry

theorem count_cons_def (n h : Nat) (t : NatList) :
    count n (h :: t) = bif n == h then count n t + 1 else count n t := sorry

theorem count_cons_same (n₁ n₂ : Nat) (t : NatList) (h : (n₁ == n₂) = true) :
    count n₁ (n₂ :: t) = count n₁ t + 1 := by
  sorry

theorem count_cons_diff (n₁ n₂ : Nat) (t : NatList) (h : (n₁ == n₂) = false) :
    count n₁ (n₂ :: t) = count n₁ t := by
  sorry

example : count 1 [1] = 1 := by
  rw [count_cons_same _ _ _ rfl]
  rw [count_nil]

example : count 2 [2, 2] = 2 := sorry

theorem test_count1 : count 1 [1, 1, 4] = 2 := sorry

theorem test_count2 : count 5 [1, 1, 4] = 0 := sorry

-- Again, all these proofs could be completed with just `rfl`,
-- because the proof is computationally straight-forward --
-- compute both sides of the equality and check if they are the
-- same.

example : count 1 [1, 2, 3, 1, 4, 1] = 3 := sorry
example : count 6 [1, 2, 3, 1, 4, 1] = 0 := sorry

-- ### Membership

-- ### Exercise (1 star): membership ⭐

def member (n : Nat) (l : NatList) : Bool := sorry

theorem member_nil (n : Nat) : member n [] = false := sorry

theorem member_cons_same (n₁ n₂ : Nat) (t : NatList) (h : (n₁ == n₂) = true) :
    member n₁ (n₂ :: t) = true := by
  sorry

theorem member_cons_diff (n₁ n₂ : Nat) (t : NatList) (h : (n₁ == n₂) = false) :
    member n₁ (n₂ :: t) = member n₁ t := by
  sorry

example : member 1 [1] = true := by
  rw [member_cons_same _ _ _ rfl]

example : member 2 [1] = false := sorry

theorem test_member1 : member 1 [1, 4, 1] = true := sorry

theorem test_member2 : member 2 [1, 4, 1] = false := sorry

-- ### Removing

-- ### Exercise (3 stars): removing (Optional) ⭐⭐⭐

-- Here are some more `NatList` functions for you to practice
-- with.

-- When `removeOne` is applied to a list without the number to
-- remove, it should return the same list unchanged.

def removeOne (n : Nat) (l : NatList) : NatList := sorry

theorem removeOne_nil (n : Nat) : removeOne n nil = nil := sorry

theorem removeOne_cons_same (n₁ n₂ : Nat) (t : NatList) (h : (n₁ == n₂) = true) :
    removeOne n₁ (n₂ :: t) = t := by
  sorry

theorem removeOne_cons_diff (n₁ n₂ : Nat) (t : NatList) (h : (n₁ == n₂) = false) :
    removeOne n₁ (n₂ :: t) = n₂ :: removeOne n₁ t := by
  sorry

example : removeOne 5 [1, 5, 4] = [1, 4] := by
  rw [removeOne_cons_diff _ _ _ rfl]
  rw [removeOne_cons_same _ _ _ rfl]

example : count 5 (removeOne 5 [1, 5, 4]) = 0 := sorry

theorem test_removeOne1 : count 4 (removeOne 5 [4, 5, 1, 4]) = 2 := sorry

theorem test_removeOne2 : count 5 (removeOne 5 [1, 5, 5, 4]) = 1 := sorry

def removeAll (n : Nat) (l : NatList) : NatList := sorry

theorem removeAll_nil (n : Nat) : removeAll n [] = [] := sorry

theorem removeAll_cons_same (n₁ n₂ : Nat) (t : NatList) (h : (n₁ == n₂) = true) :
    removeAll n₁ (n₂ :: t) = removeAll n₁ t := by
  sorry

theorem removeAll_cons_diff (n₁ n₂ : Nat) (t : NatList) (h : (n₁ == n₂) = false) :
    removeAll n₁ (n₂ :: t) = n₂ :: removeAll n₁ t := by
  sorry

example : count 5 (removeAll 5 [5, 1]) = 0 := by
  rw [removeAll_cons_same _ _ _ rfl]
  rw [removeAll_cons_diff _ _ _ rfl]
  rw [removeAll_nil]
  rw [count_cons_diff _ _ _ rfl]
  rw [count_nil]

example : count 5 (removeAll 5 [5, 5]) = 0 := sorry

theorem test_removeAll1 : count 4 (removeAll 5 [4, 5, 4]) = 2 := sorry

theorem test_removeAll2 : count 5 (removeAll 5 [2, 5, 5, 5, 1]) = 0 := sorry

-- ### Included

-- ### Exercise (3 stars): included (Optional) ⭐⭐⭐

def included (l₁ l₂ : NatList) : Bool := sorry

theorem included_nil (l₂ : NatList) : included nil l₂ = true := sorry

theorem included_cons_member (n : Nat) (l₁ l₂ : NatList) (h : member n l₂ = true) :
    included (cons n l₁) l₂ = included l₁ (removeOne n l₂) := by
  sorry

theorem included_cons_nonmember (n : Nat) (l₁ l₂ : NatList) (h : member n l₂ = false) :
    included (cons n l₁) l₂ = false := by
  sorry

example : included [1] [2, 1] = true := by
  rw [included_cons_member]
  · exact included_nil _
  · rw [member_cons_diff _ _ _ rfl]
    rw [member_cons_same _ _ _ rfl]

example : included [1, 1] [2, 1, 4, 1] = true := sorry

theorem test_included1 : included [1, 2] [2, 1, 4, 1] = true := sorry

theorem test_included2 : included [1, 2, 2] [2, 1, 4, 1] = false := sorry

-- ## Reasoning About Lists

-- As with numbers, some proofs about list functions need only
-- rewriting...

-- ...and some need case analysis.

theorem tail_length_pred (l : NatList) :
    l.length.pred = l.tail.length := by
  cases l with
  | nil       => rw [tail_nil, length_nil]; rfl
  | cons n l' => rw [tail_cons, length_cons]; rfl

-- Usually, though, interesting theorems about lists require
-- induction for their proofs. We'll see how to do this next.

-- ### Induction on Lists

-- Lean generates an induction principle for every `inductive`
-- definition, including lists. We can use the `induction`
-- tactic on lists to prove things like the associativity of
-- list-append...

theorem append_assoc (l₁ l₂ l₃ : NatList) :
    (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  induction l₁ with
  | nil =>
    rw [nil_append, nil_append]
  | cons n l₁' ih =>
    rw [cons_append, cons_append, cons_append, ih]

-- For comparison, here is an informal proof of the same
-- theorem.

-- *Theorem*: For all lists `l₁`, `l₂`, and `l₃`,

--   (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃).

-- *Proof*: By induction on `l₁`.

-- - First, suppose `l₁ = []`. We must show

--   ([] ++ l₂) ++ l₃ = [] ++ (l₂ ++ l₃),

-- which follows directly from the definition of `append`.

-- - Next, suppose `l₁ = n :: l₁'`, with

--   (l₁' ++ l₂) ++ l₃ = l₁' ++ (l₂ ++ l₃)

-- (the induction hypothesis). We must show

--   ((n :: l₁') ++ l₂) ++ l₃ = (n :: l₁') ++ (l₂ ++ l₃).

-- By the definition of `append`, this follows from

--   n :: ((l₁' ++ l₂) ++ l₃) = n :: (l₁' ++ (l₂ ++ l₃)),

-- which is immediate from the induction hypothesis. *Qed*.

-- #### Generalizing Statements

-- Sometimes statements need to be generalized to prove them by
-- induction:

sf_expect_failure
  theorem myRepeat_append_fail (c n : Nat) :
      myRepeat n c ++ myRepeat n c = myRepeat n (c + c) := by
    induction c with
    | zero => rw [repeat_zero, nil_append]
    | succ c' ih =>
      rw [repeat_succ]
      -- Now we seem to be stuck.
      -- The `ih` only works for `c' + c'`,
      -- but we need `c' + 1 + (c' + 1)`.

-- unsolved goals
-- case succ
-- n c' : Nat
-- ih : myRepeat n c' ++ myRepeat n c' = myRepeat n (c' + c')
-- ⊢ (n :: myRepeat n c') ++ (n :: myRepeat n c') = myRepeat n (c' + 1 + (c' + 1))

-- A generalization that gives a stronger inductive hypothesis:

theorem myRepeat_append_general (c₁ c₂ n : Nat) :
    myRepeat n c₁ ++ myRepeat n c₂ = myRepeat n (c₁ + c₂) := by
  induction c₁ with
  | zero =>
    rw [repeat_zero, Nat.zero_add, nil_append]
  | succ c1' ih =>
    rw [Nat.succ_add, repeat_succ, repeat_succ, cons_append, ih]

-- Then, we can use this more general theorem to prove the
-- original goal:

theorem myRepeat_append (c n : Nat) :
    myRepeat n c ++ myRepeat n c = myRepeat n (c + c) := by
  exact myRepeat_append_general c c n

-- #### Reversing a List

-- A more interesting example of induction over lists:

def reverse (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => t.reverse ++ [h]

theorem reverse_nil : [].reverse = [] := by rfl

theorem reverse_cons (h : Nat) (t : NatList) : (h :: t).reverse = t.reverse ++ [h] := by rfl

example : [1, 2, 3].reverse = [3, 2, 1] := by rfl

example : [].reverse = [] := by rfl

-- Let's try to prove
-- `∀ l : NatList, length (reverse l) = length l`.

sf_expect_failure
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

-- unsolved goals
-- case cons
-- n : Nat
-- l' : NatList
-- ih : l'.reverse.length = l'.length
-- ⊢ (l'.reverse ++ [n]).length = (n :: l').length

sf_expect_failure
  theorem length_append_succ (l : NatList) (n : Nat) :
      (l.reverse ++ [n]).length = l.reverse.length + 1 := by
    induction l with
    | nil =>
      rw [reverse_nil, nil_append, length_cons, length_nil]
    | cons m l' ih =>
      rw [reverse_cons]
      -- `ih` not applicable

-- unsolved goals
-- case cons
-- n m : Nat
-- l' : NatList
-- ih : (l'.reverse ++ [n]).length = l'.reverse.length + 1
-- ⊢ (l'.reverse ++ [m] ++ [n]).length = (l'.reverse ++ [m]).length + 1

theorem append_length_succ (l : NatList) (n : Nat) :
    (l ++ [n]).length = l.length + 1 := by
  induction l with
  | nil => rw [nil_append, length_cons]
  | cons m l' ih =>
    rw [cons_append, length_cons, ih, length_cons]

-- Now we can prove the main theorem.

theorem length_reverse (l : NatList) :
    l.reverse.length = l.length := by
  induction l with
  | nil => rw [reverse_nil]
  | cons n l' ih =>
    rw [reverse_cons, append_length_succ, ih, length_cons]

theorem length_append (l₁ l₂ : NatList) :
    (l₁ ++ l₂).length = l₁.length + l₂.length := by
  sorry

-- _Quiz:_

-- To prove the following theorem, which tactics will we need
-- besides `intro`, `dsimp`, `rw`, and `rfl`?

-- (A) none

-- (B) `cases`

-- (C) `induction` on `n`

-- (D) `induction` on `l`

-- (E) can't be done with the tactics we've seen.

--   example (n : Nat) (l : NatList) :
--       myRepeat n 0 = l → l.length = 0

-- _Quiz:_

-- What about the next one?

--   example (n m : Nat) : (myRepeat n m).length = m

-- To prove the following theorem, which tactics will we need
-- besides `intro`, `dsimp`, `rw`, and `rfl`?

-- (A) none

-- (B) `cases`

-- (C) `induction` on `n`

-- (D) `induction` on `m`

-- (E) can't be done with the tactics we've seen.

-- ### List Exercises, Part 1

-- ### List Exercises, Part 2

open NatList

-- ## Options

-- Suppose we'd like a function to retrieve the `n`th element
-- of a list. What to do if the list is too short?

def nthBad (l : NatList) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' => match n with
    | 0 => a
    | n' + 1 => nthBad l' n'

-- The solution: return a `NatOption`.

end NatList

inductive NatOption : Type where
  | some (n : Nat)
  | none

namespace NatList

def nth? (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => .none
  | a :: l' => match n with
    | 0 => .some a
    | n' + 1 => nth? l' n'

example : nth? [4, 5, 6, 7] 0 = .some 4 := by rfl
example : nth? [4, 5, 6, 7] 3 = .some 7 := by rfl
example : nth? [4, 5, 6, 7] 9 = .none := by rfl

def NatOption.elim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n => n
  | .none => d

theorem NatOption.elim_none (d : Nat) : elim d .none = d := by rfl

theorem NatOption.elim_some (d₁ d₂ : Nat) : elim d₁ (.some d₂) = d₂ := by rfl

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

def MyId.beq (x₁ x₂ : MyId) : Bool :=
  x₁.val == x₂.val

-- ### Exercise (1 star): MyId.beq_refl ⭐

theorem MyId.beq_refl (x : MyId) : MyId.beq x x = true := by
  sorry

-- Now we define the type of partial maps:

inductive PartialMap : Type where
  | empty : PartialMap
  | record (i : MyId) (n : Nat) (m : PartialMap) : PartialMap

namespace PartialMap

-- The `update` function overrides the entry for a given key in
-- a partial map by shadowing it with a new one (or simply adds
-- a new entry if the given key is not already present).

def update (d : PartialMap) (x : MyId) (value : Nat) : PartialMap :=
  record x value d

-- We can define functions on `PartialMap`s by pattern
-- matching.

def find (x : MyId) (d : PartialMap) : NatOption :=
  match d with
  | empty => .none
  | record y n d' =>
    bif MyId.beq x y then .some n
    else find x d'

-- _Quiz:_

-- Is the following claim true or false?

theorem quiz1 (d : PartialMap) (x : MyId) (n : Nat) :
    find x (update d x n) = .some n := by
  dsimp [update, find]
  rw [MyId.beq_refl]
  dsimp

-- (A) True (B) False (C) Not sure

-- _Quiz:_

-- Is the following claim true or false?

theorem quiz2  (d : PartialMap) (x y : MyId) (o : Nat) :
    MyId.beq x y = false →
    find x (update d y o) = find x d := by
  intro h
  dsimp [update, find]
  rw [h]
  dsimp

-- (A) True (B) False (C) Not sure

end PartialMap

end Lists


import LF.Induction
import LF.UsingLean

import SFLCompat

--  # Lists: Working with Structured Data

namespace Lists

--  ## Pairs of Numbers

--  An inductive definition of pairs of numbers. It has just
--  one constructor, taking two arguments:

inductive NatProd where
  | pair (n1 n2 : Nat)

#check (NatProd.pair 3 5)

--  Functions for extracting the first and second components
--  of a pair can then be defined by pattern matching.

def NatProd.fst (p : NatProd) : Nat :=
  match p with
  | .pair x _ => x

def NatProd.snd (p : NatProd) : Nat :=
  match p with
  | .pair _ y => y

--  Defining these functions with the `NatProd` type name
--  qualifying their names allows us to use them with `.`
--  notation:

example : (NatProd.pair 3 5).fst = 3 := by rfl

--  A nicer notation for pairs:

example : (⟨3, 5⟩ : NatProd).fst = 3 := by rfl

--  The anonymous constructor can be used both in
--  expressions and in pattern matches.

def NatProd.fst' (p : NatProd) : Nat :=
  match p with
  | ⟨x, _⟩ => x

def NatProd.snd' (p : NatProd) : Nat :=
  match p with
  | ⟨_, y⟩ => y

def NatProd.swap (p : NatProd) : NatProd :=
  ⟨snd p, fst p⟩

--  To expose the structure of a pair, use `cases` (or
--  destructuring).

theorem surjective_pairing : ∀ p : NatProd,
    p = ⟨p.fst, p.snd⟩ := by
  intro ⟨n, m⟩; rfl

theorem surjective_pairing_cases (p : NatProd) :
    p = ⟨p.fst, p.snd⟩ := by
  cases p; rfl

--  ### Structures

--  Lean's `structure` is shorthand for a single-constructor
--  `inductive` with the accessors auto-generated.

structure NatProd' where
  fst : Nat
  snd : Nat

#check (NatProd'.mk 3 5)
example : (NatProd'.mk 3 5).fst = 3 := by rfl
example : (⟨3, 5⟩ : NatProd').fst = 3 := by rfl

--  ## Lists of Numbers

--  An inductive definition of *lists* of numbers:

inductive NatList : Type where
  | nil
  | cons (n : Nat) (l : NatList)

--  By convention, we place the operations (functions) of an
--  inductive type inside the namespace implicitly created
--  by that type's definition.

namespace NatList

--  Some notation for lists to make our lives easier: `::`
--  as an infix `cons` operator and square brackets as an
--  "outfix" notation.

--  THE FOLLOWING DETAILS CAN BE SKIPPED (List syntax)
--  We first define `::` as right-associative notation for
--  `cons`, and then define list notation as a *macro*,
--  allowing us to write `[1, 2]` instead of `1 :: 2 :: []`.
--  The *unexpander* reverses the macro, translating list
--  syntax back to cons syntax.

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

--  Some useful list-manipulation functions...

--  Let's define some functions on lists.

def replicate (n count : Nat) : NatList :=
  match count with
  | 0 => []
  | count' + 1 => n :: replicate n count'

--  Some simple facts about replication:

theorem replicate_zero (n : Nat) : replicate n 0 = [] := by rfl

theorem replicate_succ (n count : Nat) :
  replicate n (count + 1) = n :: replicate n count := by rfl

def length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => (length t) + 1

--  Some simple facts about list lengths:

theorem length_nil : [].length = 0 := by rfl

theorem length_cons (n : Nat) (l : NatList) :
  (n :: l).length = l.length + 1 := by rfl

def append (l₁ l₂ : NatList) : NatList :=
  match l₁ with
  | [] => l₂
  | h :: t => h :: append t l₂

--  ### Type Classes and Overloading Notation

--  Lean overloads notation like `++` via *type classes*:
--  registering an `HAppend` instance lets `++` mean
--  `append` for `NatList`.

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

--  `BEq.refl : (a == a) = true` is worth knowing by name.

--  ### Head and Tail

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

--   ----------------------------------------

--  _Quiz:_

--  What does the following function do?

def foo (n : Nat) : NatList :=
  match n with
  | 0 => []
  | n' + 1 => (n' + 1) :: foo n'

--   ----------------------------------------

--  ## Reasoning About Lists

--  As with numbers, some proofs about list functions need
--  only rewriting.

--  ...and some need case analysis.

theorem tail_length_pred (l : NatList) :
    l.length.pred = l.tail.length := by
  cases l with
  | nil       => rw [tail_nil, length_nil]; rfl
  | cons n l' => rw [tail_cons, length_cons]; rfl

--  Usually, though, interesting theorems about lists
--  require induction for their proofs. We'll see how to do
--  this next.

--  ### Induction on Lists

--  Lean generates an induction principle for every
--  `inductive` definition, including lists. We can use the
--  `induction` tactic on lists to prove things like the
--  associativity of list-append...

theorem append_assoc (l₁ l₂ l₃ : NatList) :
    (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  induction l₁ with
  | nil =>
    rw [nil_append, nil_append]
  | cons n l₁' ih =>
    rw [cons_append, cons_append, cons_append, ih]

--  For comparison, here is an informal proof of the same
--  theorem.

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
--  - Next, suppose `l₁ = n :: l₁'`, which gives us the
--    following inductive hypothesis.
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
--  which is immediate from the induction hypothesis. *QED*.

--  #### Generalizing Statements

--  Sometimes statements need to be generalized to prove
--  them by induction:

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

--  A generalization that gives a stronger induction
--  hypothesis:

theorem replicate_append_general (c₁ c₂ n : Nat) :
    replicate n c₁ ++ replicate n c₂ = replicate n (c₁ + c₂) := by
  induction c₁ with
  | zero =>
    rw [replicate_zero, Nat.zero_add, nil_append]
  | succ c1' ih =>
    rw [Nat.succ_add, replicate_succ, replicate_succ, cons_append, ih]

--  Then, we can use this more general theorem to prove the
--  original goal:

theorem replicate_append (c n : Nat) :
    replicate n c ++ replicate n c = replicate n (c + c) := by
  exact replicate_append_general c c n

--  #### Reversing a List

--  A more interesting example of induction over lists:

def reverse (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => t.reverse ++ [h]

theorem reverse_nil : [].reverse = [] := by rfl

theorem reverse_cons (h : Nat) (t : NatList) : (h :: t).reverse = t.reverse ++ [h] := by rfl

example : [1, 2, 3].reverse = [3, 2, 1] := by rfl

example : [].reverse = [] := by rfl

--  Let's try to prove
--  `∀ l : NatList, length (reverse l) = length l`.

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

theorem length_append (l₁ l₂ : NatList) :
    (l₁ ++ l₂).length = l₁.length + l₂.length := by
  sorry

--   ----------------------------------------

--  _Quiz:_

--  To prove the following theorem, which tactics will we
--  need besides `intro`, `rw`, and `rfl`?
--
--  (A) none
--
--  (B) `cases`
--
--  (C) `induction` on `n`
--
--  (D) `induction` on `l`
--
--  (E) can't be done with the tactics we've seen.
--
--      example (n : Nat) (l : NatList) :
--          replicate n 0 = l → l.length = 0

--   ----------------------------------------

--  _Quiz:_

--  What about the next one?
--
--      example (n m : Nat) : (replicate n m).length = m
--
--  To prove the following theorem, which tactics will we
--  need besides `intro`, `rw`, and `rfl`?
--
--  (A) none
--
--  (B) `cases`
--
--  (C) `induction` on `n`
--
--  (D) `induction` on `m`
--
--  (E) can't be done with the tactics we've seen.

--   ----------------------------------------

open NatList

--  ## Options

--  Suppose we'd like a function to retrieve the `n`th
--  element of a list. What to do if the list is too short?

def nthBad (l : NatList) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' => match n with
    | 0 => a
    | n' + 1 => nthBad l' n'

--  The solution: return a `NatOption`.

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

--  ## Partial Maps

--  As a final illustration of how data structures can be
--  defined in Lean, here is a simple *partial map* data
--  type, analogous to the map or dictionary data structures
--  found in most programming languages.
--
--  First, we define a new type `MyId` to serve as the
--  "keys" of our partial maps.

structure MyId where
  val : Nat

--  Internally, a `MyId` is just a number. Introducing a
--  separate type by wrapping each `Nat` makes definitions
--  more readable and gives us flexibility to change
--  representations later if we want to.

--  We'll also need an equality test for `MyId`s:

def MyId.beq (x₁ x₂ : MyId) : Bool :=
  x₁.val == x₂.val

--  ### Exercise (1 star): MyId.beq_refl ⭐

theorem MyId.beq_refl (x : MyId) : MyId.beq x x = true := by
  sorry

--  Now we define the type of partial maps:

inductive PartialMap : Type where
  | empty : PartialMap
  | record (i : MyId) (n : Nat) (m : PartialMap) : PartialMap

namespace PartialMap

--  The `update` function overrides the entry for a given
--  key in a partial map by shadowing it with a new one (or
--  simply adds a new entry if the given key is not already
--  present).

def update (d : PartialMap) (x : MyId) (value : Nat) : PartialMap :=
  record x value d

--  We can define functions on `PartialMap`s by pattern
--  matching.

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

theorem quiz2 (d : PartialMap) (x y : MyId) (o : Nat) :
    MyId.beq x y = false →
    find x (update d y o) = find x d := by
  intro h
  rw [update, find, h, cond_false]

--  (A) True (B) False (C) Not sure

--   ----------------------------------------

end PartialMap

end Lists

-- Built on 2026-09-03 19:08 UTC

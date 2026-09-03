import LF.Induction
import LF.UsingLean

import SFLCompat

--  # Poly: Polymorphism and Higher-Order Functions

--  ## Polymorphism

--  ### Polymorphic Lists

--  Instead of defining new lists for each type, like
--  this...

inductive BoolList : Type where
  | nil
  | cons (b : Bool) (l : BoolList)

--  ... Lean lets us give a *polymorphic* definition that
--  allows list elements of any type:

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons (x : α) (l : MyList α) : MyList α

--  We can now write `MyList Nat` in place of a specialized
--  list-of-numbers type.

--  What is `MyList` itself?
--
--  It is a *type constructor* — a function from `Type`s to
--  `Type`s.

#check (MyList)

--  Output:
--    MyList : Type → Type

--  The `α` in the definition of `MyList` becomes an
--  implicit parameter to the list constructors `nil` and
--  `cons`.

#check MyList.nil

--  Output:
--    MyList.nil {α : Type} : MyList α

#check MyList.cons 3 MyList.nil

--  Output:
--    MyList.cons 3 MyList.nil : MyList Nat

#check MyList.nil

--  Output:
--    MyList.nil {α : Type} : MyList α

#check MyList.cons

--  Output:
--    MyList.cons {α : Type} (x : α) (l : MyList α) : MyList α

--  We can now define polymorphic versions of the functions
--  we've already seen...

def replicate (α : Type) (x : α) (count : Nat) : MyList α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (replicate α x count')

--  Some simple facts about `replicate`:

theorem replicate_zero (α : Type) (a : α) :
    replicate α a 0 = MyList.nil := rfl

theorem replicate_succ (α : Type) (a : α) (count : Nat) :
    replicate α a (count + 1) = MyList.cons a (replicate α a count) := rfl

example : replicate Nat 4 2 = .cons 4 (.cons 4 .nil) := by rfl

example : replicate Bool false 1 = .cons false .nil := by rfl

--   ----------------------------------------

--  _Quiz:_

--  What is the type of
--  `MyList.cons true (MyList.cons 3 MyList.nil)`?
--
--  (A) `MyList Nat`
--
--  (B) `{α : Type} → α → MyList α → MyList α`
--
--  (C) `MyList Bool`
--
--  (D) `MyList (Nat × Bool)`
--
--  (E) Ill-typed

--   ----------------------------------------

--  _Quiz:_

--  What is the type of `replicate`?
--
--  (A) `Nat → Nat → MyList Nat`
--
--  (B) `(α : Type) → α → Nat → MyList α`
--
--  (C) `(α : Type) → {β : Type} → α → Nat → MyList β`
--
--  (D) Ill-typed

--   ----------------------------------------

--  _Quiz:_

--  What is the type of `replicate 1 2`?
--
--  (A) `MyList Nat`
--
--  (B) `(α : Type) → α → Nat → MyList α`
--
--  (C) `MyList Bool`
--
--  (D) Ill-typed

--   ----------------------------------------

--  From now on we'll use Lean's built-in `List α` type with
--  notations `[]`, `::`, `[1, 2, 3]`, and `++`.

example : List Nat := [1, 2, 3]

--  #### Implicit Type Arguments and Argument Synthesis

--  Supplying every type *argument* is also boring, but Lean
--  can usually infer them:

def replicate' (α : Type) (x : α) (count : Nat) : List α :=
  match count with
  | 0 => []
  | count' + 1 => x :: replicate' _ x count'

--  Alternatively, we can declare arguments implicit by
--  surrounding them with curly braces instead of parens:

def replicate'' {α : Type} (x : α) (count : Nat) : List α :=
  match count with
  | 0 => []
  | count' + 1 => x :: replicate'' x count'

--  #### Supplying Type Arguments Explicitly

--  In general, it's fine to just let Lean infer all type
--  arguments. But occasionally this can lead to problems:

sf_expect_failure_in
  def mynil := []

--  Output:
--    Failed to infer type of definition `mynil`

--  We can fix this with an explicit type annotation.
--
--  We use the `@` prefix when we want to supply the type
--  argument explicitly. The `@` makes all implicit
--  arguments of a function explicit:

#check @List.nil

def myNil' := @List.nil Nat

--  Output:
--    @List.nil : {α : Type u_1} → List α

--   ----------------------------------------

--  _Quiz:_

--  Which type does Lean assign to the following expression?
--  (The square brackets in this quiz and the following ones
--  are list brackets.)
--
--      [1, 2, 3]
--
--  (A) `List Nat`
--
--  (B) `List Bool`
--
--  (C) `Bool`
--
--  (D) No type can be assigned

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      [3 + 4] ++ []
--
--  (A) `List Nat`
--
--  (B) `List Bool`
--
--  (C) `Bool`
--
--  (D) No type can be assigned

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      (true && false) :: []
--
--  (A) `List Nat`
--
--  (B) `List Bool`
--
--  (C) `Bool`
--
--  (D) No type can be assigned

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      [1, []]
--
--  (A) `List Nat`
--
--  (B) `List (List Nat)`
--
--  (C) `List Bool`
--
--  (D) No type can be assigned

--   ----------------------------------------

--  _Quiz:_

--  What about this one?
--
--      [[1], []]
--
--  (A) `List Nat`
--
--  (B) `List (List Nat)`
--
--  (C) `List Bool`
--
--  (D) No type can be assigned

--   ----------------------------------------

--  _Quiz:_

--  And what about this one?
--
--      [1] :: [[]]
--
--  (A) `List Nat`
--
--  (B) `List (List Nat)`
--
--  (C) `List Bool`
--
--  (D) No type can be assigned

--   ----------------------------------------

--  _Quiz:_

--  This one?
--
--      @List.nil Bool
--
--  (A) `List Nat`
--
--  (B) `List (List Nat)`
--
--  (C) `List Bool`
--
--  (D) No type can be assigned

--   ----------------------------------------

--  #### Exercises

def List.rev {α : Type} (l : List α) : List α :=
  match l with
  | .nil => .nil
  | .cons h t => rev t ++ (.cons h .nil)

theorem rev_nil {α : Type} : ([] : List α).rev = [] := by rfl

theorem rev_cons {α : Type} {x : α} {l : List α} :
    (x :: l).rev = l.rev ++ [x] := by rfl

--  ### Exercise (2 stars): poly_exercises ⭐⭐

--  Here are a few simple exercises, just like ones in the
--  Lists chapter, for practice with polymorphism. Complete
--  the proofs below. You will find the following
--  characterizing lemmas for `List.append` in Lean standard
--  library to be useful:

#check List.nil_append
#check List.cons_append

--  Output:
--    List.cons_append.{u} {α : Type u} {a : α} {as bs : List α} : a :: as ++ bs = a :: (as ++ bs)

--  Output:
--    List.nil_append.{u} {α : Type u} (as : List α) : [] ++ as = as

theorem append_nil {α : Type} {l : List α} :
    l ++ [] = l := by
  sorry

theorem append_assoc {α : Type} {l₁ l₂ l₃ : List α} :
    l₁ ++ l₂ ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  sorry

theorem append_length {α : Type} {l₁ l₂ : List α} :
    (l₁ ++ l₂).length = l₁.length + l₂.length := by
  sorry

--  ### Exercise (2 stars): more_poly_exercises ⭐⭐

--  Here are some slightly more interesting ones...

theorem reverse_append {α : Type} {l₁ l₂ : List α} :
    (l₁ ++ l₂).rev = l₂.rev ++ l₁.rev := by
  sorry

theorem reverse_reverse {α : Type} (l : List α) :
    l.rev.rev = l := by
  sorry

--  ### Polymorphic Pairs

--  Like `inductive`s, `structure`s can also be made
--  polymorphic. If we generalize the definition `NatProd`
--  of pairs of natural numbers from last chapter, we get
--  polymorphic pairs, often called *products*:

structure MyProd (α β : Type) where
  fst : α
  snd : β

--  Lean's built-in product type `Prod` provides a `Prod.mk`
--  constructor, and `Prod.fst` and `Prod.snd` functions for
--  accessing the first and second components of the pair.
--  It also has special syntax for creating products:

#check (1, true)
#eval (1, true).fst
#eval (1, true).snd

--  Output:
--    (1, true) : Nat × Bool

--  Output:
--    1

--  Output:
--    true

--  You can also use `.1` instead of `.fst` and `.2` instead
--  of `.snd`:

example : (3, 5).1 = 3 := by rfl
example : (3, 5).2 = 5 := by rfl

--  Lean writes the product type `Prod α β` as `α × β`. In
--  VS Code you can type `\times` or `\x` to enter the `×`
--  symbol.
--
--  The `dsimp only` tactic can be used to simplify
--  `(x, y).fst` into `x` and `(x, y).snd` into `y`.

--  Be careful not to get `(x, y)` and `α × β` confused!

--  What does this function do?

def zip {α β : Type} (l₁ : List α) (l₂ : List β) : List (α × β) :=
  match l₁, l₂ with
  | [], [] => []
  | _ :: _, [] => []
  | [], _ :: _ => []
  | x :: l₁', y :: l₂' => (x, y) :: zip l₁' l₂'

theorem zip_nil_left {α β : Type} (l₁ : List α) : zip l₁ [] = ([] : List (α × β)) := by
  cases l₁ <;> rfl

theorem zip_nil_right {α β : Type} (l₂ : List β) : zip [] l₂ = ([] : List (α × β)) := by
  cases l₂ <;> rfl

theorem zip_cons_cons {α β : Type} {x : α} {y : β} {l₁ : List α} {l₂ : List β} :
   zip (x :: l₁) (y :: l₂) = (x, y) :: zip l₁ l₂ := by rfl

--  Notice that the simplification lemmas `zip_nil_left` and
--  `zip_nil_right` are not proofs by `rfl`. The reason is
--  that `l₁` and `l₂` are variables, and matching on a
--  variable usually gets stuck, like we have seen before in
--  Induction when proving the `zero_add` theorem. To
--  overcome this, we destruct the list so that the `match`
--  knows which branch to take during the computation done
--  by the `rfl` tactic.

--  ### Polymorphic Options

def nth? {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | x :: l' => match n with
    | 0 => some x
    | n' + 1 => nth? l' n'

example : nth? [4, 5, 6, 7] 0 = some 4 := by rfl
example : nth? [[1], [2]] 1 = some [2] := by rfl
example : nth? [true] 2 = none := by rfl

--  ## Functions as Data

--  ### Higher-Order Functions

--  Functions that take other functions as arguments or
--  return them as results are called higher-order
--  functions.

def doIt3Times {α : Type} (f : α → α) (x : α) : α :=
  f (f (f x))

#check doIt3Times

example : doIt3Times Nat.minusTwo 9 = 3 := by rfl

example : doIt3Times not true = false := by rfl

--  Output:
--    doIt3Times {α : Type} (f : α → α) (x : α) : α

--  ### Filter

--  A *higher-order function* can take another function as
--  an argument. For example, `filter` takes a test and a
--  list.

def filter {α : Type} (test : α → Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | x :: l' =>
    bif test x then x :: filter test l'
    else filter test l'

example : filter Nat.even [1, 2, 3, 4] = [2, 4] := by rfl

--  Here are some further examples and properties of
--  `filter`.

def isLength1 {α : Type} (l : List α) : Bool :=
  l.length == 1

example : filter isLength1
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

theorem filter_nil {α : Type} {test : α → Bool} :
  filter test [] = [] := by rfl

theorem filter_cons_of_pos {α : Type} {test : α → Bool} {x : α}
    {l : List α} (h : test x = true) :
    filter test (x :: l) = x :: filter test l := by
  rw [filter, h, cond_true]

theorem filter_cons_of_neg {α : Type} {test : α → Bool} {x : α}
    {l : List α} (h : test x = false) :
    filter test (x :: l) = filter test l := by
   rw [filter, h, cond_false]

--  Note that `x` and `l` are implicit too, following a
--  general convention: any argument an equation's shape
--  determines when applied is made implicit, so using `rw`
--  lemmas requires no extra `_` arguments.

--  The `filter` function (especially when combined with
--  some other functions we'll see later) enables a powerful
--  *wholemeal* (or *collection-oriented*) programming
--  style.

def countOddMembers (l : List Nat) : Nat := (filter Nat.odd l).length

example : countOddMembers [1, 0, 3, 1, 4, 5] = 4 := by rfl
example : countOddMembers [0, 2, 4] = 0 := by rfl
example : countOddMembers [] = 0 := by rfl

--  ### Anonymous Functions

--  Functions can be constructed "on the fly" without giving
--  them names.

example : doIt3Times (fun n => n * n) 2 = 256 := by rfl

--  Lean also provides the shorter `·` notation for
--  anonymous functions.

example : doIt3Times (· + 1) 0 = 3 := by rfl

example : filter (fun l => l.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

example : filter (·.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

--  ### Map

def map {α β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | head :: tail => f head :: map f tail

example : map (· + 3) [2, 0, 2] = [5, 3, 5] := by rfl

example : map Nat.odd [2, 1, 2, 5] = [false, true, false, true] := by rfl

example : map (fun n => [n.even, n.odd]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]] := by rfl

--   ----------------------------------------

--  _Quiz:_

--  Recall the definition of `map`:

sf_recall
  def map {α β : Type} (f : α → β) (l : List α) : List β :=
    match l with
    | [] => []
    | head :: tail => f head :: map f tail

--  What is the type of `@map`?
--
--  (A) `{α β : Type} → α → β → List α → List β`
--
--  (B) `α → β → List α → List β`
--
--  (C) `{α β : Type} → (α → β) → List α → List β`
--
--  (D) `{α : Type} → (α → α) → List α → List α`

--   ----------------------------------------

--  As usual, we define the following simplification rules
--  for `map`:

theorem map_nil {α : Type} {β : Type} {f : α → β} : map f [] = [] := by rfl

theorem map_cons {α : Type} {β : Type} {f : α → β} {x : α} {l : List α} :
    map f (x :: l) = f x :: map f l := by rfl

--  Lists are not the only inductive type for which `map`
--  makes sense. Here is a `map` for the `Option` type:

def optionMap {α : Type} {β : Type} (f : α → β) (x? : Option α) : Option β :=
  match x? with
  | none => none
  | some x => some (f x)

--  ### Fold

def fold {α : Type} {β : Type} (f : α → β → β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | a :: l => f a (fold f l b)

--  This is the "reduce" in map/reduce...

example : fold (· && ·) [true, true, false, true] true = false := by rfl

example : fold (· * ·) [1, 2, 3, 4] 1 = 24 := by rfl

example : fold (· ++ ·) [[1], [], [2, 3], [4]] [] = [1, 2, 3, 4] := by rfl

example : fold (fun l n => l.length + n) [[1], [], [2, 3, 2], [4]] 0 = 5 := by rfl

theorem fold_nil {α : Type} {β : Type} {f : α → β → β} {b : β} : fold f [] b = b := by rfl

theorem fold_cons {α : Type} {β : Type} {f : α → β → β} {a : α} {l : List α} {b : β} :
    fold f (a :: l) b = f a (fold f l b) := by rfl

--   ----------------------------------------

--  _Quiz:_

--  Here is the definition of `fold` again:

sf_recall
  def fold {α β : Type} (f : α → β → β) (l : List α) (b : β) : β :=
    match l with
    | [] => b
    | a :: l => f a (fold f l b)

--  What is the type of `@fold`?
--
--  (A) `{α β : Type} → (α → β → β) → List α → β → β`
--
--  (B) `α → β → (α → β → β) → List α → β → β`
--
--  (C) `{α β : Type} → α → β → β → List α → β → β`
--
--  (D) `α → β → α → β → β → List α → β → β`

--   ----------------------------------------

--  _Quiz:_

--  What does `fold (· + ·) [1, 2, 3, 4] 0` simplify to?
--
--  (A) `[1, 2, 3, 4]`
--
--  (B) `0`
--
--  (C) `10`
--
--  (D) `[3, 7, 0]`

--   ----------------------------------------

--  ### Functions That Construct Functions

--  Here are two functions that *return* functions as
--  results.

def constFun {α : Type} (x : α) : Nat → α :=
  fun _ => x

def fTrue := constFun true

example : fTrue 0 = true := by rfl

example : constFun 5 99 = 5 := by rfl

--  A two-argument function in Lean is actually a function
--  that returns a function!

#check Nat.add

--  Output:
--    Nat.add : Nat → Nat → Nat

def plus3 := Nat.add 3
#check plus3

example : plus3 4 = 7 := by rfl
example : doIt3Times plus3 0 = 9 := by rfl
example : doIt3Times (Nat.add 3) 0 = 9 := by rfl

--  Output:
--    plus3 : Nat → Nat

--  Similarly, we can write:

def fold_plus : List Nat → Nat → Nat :=
  fold (· + ·)

#check fold_plus

--  Output:
--    fold_plus : List Nat → Nat → Nat

-- Built on 2026-09-03 15:33 UTC

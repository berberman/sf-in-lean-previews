import LF.Induction
import LF.UsingLean

import LF.SFLCompat

-- # Poly: Polymorphism and Higher-Order Functions

-- Note to developers (Daniel Sainati  @dsainati1):
--     [BCP: Old comment -- might be out of date?] None of the
--     comments at the start of the chapter motivating the
--     polymorphic definition of lists make sense with the
--     change to use `List Nat` in the previous chapter.
--
--     Using the built-in definition of `List.reverse` is
--     dramatically more complicated than implementing our own
--     reverse function, since it is implemented in terms of an
--     auxiliary function.
--
--     The associativity of `++` in Lean is different than
--     Rocq. In Rocq the definition of `app_assoc` is
--     `l ++ m ++ n = (l ++ m) ++ n`, but in Lean it's
--     `l ++ m ++ n = l ++ (m ++ n)`.

-- ### Polymorphic Lists

-- Instead of defining new lists for each type, like this...

inductive BoolList : Type where
  | bool_nil
  | bool_cons (b : Bool) (l : BoolList)

-- ... Lean lets us give a *polymorphic* definition that allows
-- list elements of any type:

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons (x : α) (l : MyList α) : MyList α

-- We can now write `MyList Nat` in place of a specialized
-- list-of-numbers type.

-- What is `MyList` itself?

-- It is a *function* from types to types.

#check (MyList : Type → Type)

-- The `α` in the definition of `MyList` becomes an implicit
-- parameter to the list constructors `nil` and `cons`.

#check (MyList.nil : MyList Nat)

#check (MyList.cons 3 MyList.nil : MyList Nat)

-- Note to developers (before next release):
--     Unclear - Reword

#check (@MyList.nil : {α : Type} → MyList α)

#check (@MyList.cons : {α : Type} → α → MyList α → MyList α)

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     Does this still apply?

-- Note to developers (Jonathan Chan  @ionathanch, NOW):
--     We should never write `forall` in place of `∀`, but
--     somewhere in `Basics` we ought to tell people that you
--     can find out how to type a symbol by hovering over it.

-- Side note: In .v files, the "forall" quantifier is spelled
-- out in letters. In the corresponding HTML files, it is
-- usually typeset as the standard mathematical "upside down
-- A."

-- We can now define polymorphic versions of the functions
-- we've already seen...

def myRepeat (α : Type) (x : α) (count : Nat) : MyList α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (myRepeat α x count')

-- Some simple facts about list lengths

theorem repeat_zero α v : myRepeat α v 0 = MyList.nil := rfl

theorem repeat_succ α v count : myRepeat α v (count + 1) = MyList.cons v (myRepeat α v count) := rfl

example : myRepeat Nat 4 2 = .cons 4 (.cons 4 .nil) := by rfl

example : myRepeat Bool false 1 = .cons false .nil := by rfl

-- _Quiz:_

-- What is the type of
-- `MyList.cons true (MyList.cons 3 MyList.nil)`?

-- (A) `MyList Nat`

-- (B) `{α : Type} → α → MyList α → MyList α`

-- (C) `MyList Bool`

-- (D) `MyList (Nat × Bool)`

-- (E) Ill-typed

-- _Quiz:_

-- What is the type of `myRepeat`?

-- (A) `Nat → Nat → MyList Nat`

-- (B) `{α : Type} → α → Nat → MyList α`

-- (C) `{α : Type} → {β : Type} → α → Nat → MyList β`

-- (D) Ill-typed

-- _Quiz:_

-- What is the type of `myRepeat 1 2`?

-- (A) `MyList Nat`

-- (B) `{α : Type} → α → Nat → MyList α`

-- (C) `MyList Bool`

-- (D) Ill-typed

-- From now on we'll use Lean's built-in `List α` type with
-- notations `[]`, `::`, `[1, 2, 3]`, and `++`.

def list123 : List Nat := [1, 2, 3]

-- #### Type Annotation Inference

-- Note to developers (Daniel Sainati  @dsainati1, NOW):
--     I copied this over mostly verbatim from Poly.v, but I
--     think the point doesn't work in Lean. The definition of
--     `repeat'` below doesn't typecheck, I think Lean does
--     less inference than Rocq here. Should we just delete
--     this?

-- Note to developers (Jonathan Chan  @ionathanch, NOW):
--     Lean can still infer the types of arguments that are
--     used dependently, so I've adapted the text below to only
--     omit `α`. The question of what Lean infers as its type
--     is still tricky to present, since `#check repeat'` alone
--     will show that `α` is universe-polymorphic as well,
--     which I suppose we want to avoid explaining at this
--     moment?

-- Let's write the definition of `repeat` again, but this time
-- we won't specify the type of the parameter `α`. Will Lean
-- still accept it?

def repeat' α (x : α) (count : Nat) : List α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (repeat' α x count')

-- Indeed it will. We can see that `α` has the type `Type`, as
-- expected.

#check (repeat' : ∀ (α : Type), α → Nat → List α)

-- Lean has used *type inference* to deduce a type for `α`.

-- #### Type Argument Synthesis

-- Supplying every type *argument* is also boring, but Lean can
-- usually infer them:

def myRepeat'' (α : Type) (x : α) (count : Nat) : List α :=
  match count with
  | 0        => []
  | count' + 1 => x :: myRepeat'' _ x count'

-- Alternatively, we can declare arguments implicit by
-- surrounding them with curly braces instead of parens:

def myRepeat''' {α : Type} (x : α) (count : Nat) : List α :=
  match count with
  | 0        => []
  | count' + 1 => x :: myRepeat''' x count'

-- #### Supplying Type Arguments Explicitly

-- In general, it's fine to just let Lean infer all type
-- arguments. But occasionally this can lead to problems:

-- This fails because Lean can't figure out the type of the
-- empty list: `def mynil := []` -- error: type not known We
-- can fix this with an explicit type annotation:

-- We can use the `@` prefix to supply the type argument
-- explicitly. The `@` makes all implicit arguments of a
-- function explicit:

-- Note to developers (Jonathan Chan  @ionathanch, NOW):
--     Didn't we alredy use this feature back on lines 121/126?

#check (@List.nil : {α : Type} → List α)

def mynil' := @List.nil Nat

-- _Quiz:_

-- Which type does Lean assign to the following expression?
-- (The square brackets in this quiz and the following ones are
-- list brackets.)

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

-- #### Exercises

def List.rev {α:Type} (l:List α) : List α :=
  match l with
  | .nil => .nil
  | .cons h t => rev t ++ (.cons h .nil)

theorem rev_nil α : ([] : List α).rev = [] := by rfl

theorem rev_cons α h (t : List α) : (h :: t).rev = t.rev ++ [h] := by rfl

-- ### Exercise (2 stars): poly_exercises ⭐⭐

-- Here are a few simple exercises, just like ones in the
-- `Lists` chapter, for practice with polymorphism. Complete
-- the proofs below. You will likely find useful the following
-- lemmas about append and length from Lean's standard library:

--   List.nil_append {α} (as : List α) : [] ++ as = as
--   List.cons_append {α} {a : α} {as bs : List α} : a :: as ++ bs = a :: (as ++ bs)

theorem app_nil_r {α : Type} : ∀ (l : List α),
    l ++ [] = l := by
  sorry

theorem app_assoc {α : Type} : ∀ (l m n : List α),
    l ++ m ++ n = l ++ (m ++ n) := by
  sorry

theorem app_length {α : Type} : ∀ (l1 l2 : List α),
    (l1 ++ l2).length = l1.length + l2.length := by
  sorry

-- ### Exercise (2 stars): more_poly_exercises ⭐⭐

-- Here are some slightly more interesting ones...

theorem rev_app_distr {α : Type} : ∀ (l1 l2 : List α),
    (l1 ++ l2).rev = l2.rev ++ l1.rev := by
  sorry

theorem rev_involutive {α : Type} : ∀ (l : List α),
    l.rev.rev = l := by
  sorry

-- ### Polymorphic Pairs

-- Like `inductive`s, `structure`s can also be made
-- polymorphic. If we generalize the definition `NatProd` of
-- pairs of natural numbers from last chapter, we get
-- polymorphic pairs, often called *products*:

structure MyProd (α β : Type) where
  fst : α
  snd : β

-- Lean's built-in product type `Prod` provides a `Prod.mk`
-- constructor, and `fst` and `snd` functions for accessing the
-- first and second components of the pair. It also has special
-- syntax for creating products:

#check (1, true)  /- (1, true) : Nat × Bool -/
#check (1, true).fst  /- access first component -/
#check (1, true).snd  /- access second component -/

-- You can also use `.1` instead of `.fst` and `.2` instead of
-- `.snd`

#check (1, true).1  /- access first component -/
#check (1, true).2  /- access second component -/

example : (3, 5).1 = 3 := by rfl
example : (3, 5).2 = 5 := by rfl

-- The notation `α × β` is syntactic sugar for `Prod α β`.

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     Do we need to tell them how to type it in vscode? (If
--     yes, then should we be doing this for every notation
--     when it is introduced? (If yes, we should record this
--     decision in the Claude prompt that we use for checking
--     nitpicky regressions like this, creating and documenting
--     it if it doesn't already exist.))

-- Be careful not to get `(x, y)` and `α × β` confused!

-- What does this function do?

def zip {α : Type} {β : Type} (lx : List α) (ly : List β) : List (α × β) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: zip tx ty

theorem zip_nil_r α β ly : zip [] ly = ([] : List (α × β)) := by rfl

theorem zip_nil_l α β lx : zip lx [] = ([] : List (α × β)) := by
   cases lx
   . rfl
   . rfl

theorem zip_cons α β lx ly (x : α) (y : β) :
   zip (x :: lx) (y :: ly) = (x, y) :: zip lx ly := by rfl

-- ### Polymorphic Options

-- Note to developers (Benjamin Pierce  @bcpierce00):
--     Did we literally see `Option Nat` or was it spelled some
--     other way?

def nthError {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | a :: l' => match n with
    | 0 => some a
    | n' + 1 => nthError l' n'

-- test*nth*error1

example : nthError [4, 5, 6, 7] 0 = some 4 := by rfl
example : nthError [[1], [2]] 1 = some [2] := by rfl
example : nthError [true] 2 = none := by rfl

-- ## Functions as Data

-- Note to developers:
--     HIDE: Robert Rand: The terse version could really use
--     words here. (Or drop the section break and rename this
--     one to "Higher-Order Functions"

-- ### Higher-Order Functions

-- Functions in Lean are *first class*.

abbrev doit3times {α : Type} (f : α → α) (n : α) : α :=
  f (f (f n))

#check @doit3times  /- @doit3times : {α : Type} → (α → α) → α → α -/

example : doit3times Nat.minustwo 9 = 3 := by rfl

example : doit3times not true = false := by rfl

-- ### Filter

def filter {α : Type} (test : α → Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | h :: t =>
    bif test h then h :: filter test t
    else filter test t

example : filter Nat.even [1, 2, 3, 4] = [2, 4] := by rfl

abbrev lengthIs1 {α : Type} (l : List α) : Bool :=
  l.length == 1

example : filter lengthIs1
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by dsimp [filter, lengthIs1]

theorem filter_nil {α : Type} {test : α → Bool} : filter test [] = [] := by rfl

theorem filter_cons_success {α : Type} {test : α → Bool} h t :
   test h -> filter test (h :: t) = h :: filter test t := by
   intro htest
   dsimp [filter]
   rw [htest]
   dsimp

theorem filter_cons_fail {α : Type} {test : α → Bool} h t :
   test h = false -> filter test (h :: t) = filter test t := by
   intro htest
   dsimp [filter]
   rw [htest]
   dsimp

-- The `filter` function (especially when combined with some
-- other functions we'll see later) enables a powerful
-- *wholemeal* (or *collection-oriented*) programming style.

abbrev countoddmembers' (l : List Nat) : Nat :=
  (filter Nat.odd l).length

example : countoddmembers' [1, 0, 3, 1, 4, 5] = 4 := by rfl
example : countoddmembers' [0, 2, 4] = 0 := by rfl
example : countoddmembers' [] = 0 := by rfl

-- ### Anonymous Functions

-- Note to developers:
--     HIDE: Why not show them `fix` here? It's not that
--     complicated and it fills out the story. At least as a
--     little optional section. BAY: I'm not convinced it's
--     "not that complicated" for people who have never seen
--     much functional programming before. I think adding a
--     discussion of fix could easily take 20 minutes of class
--     time. BCP: Yes, this doesn't belong in lecture,
--     probably. But it might still be useful as an optional
--     section for people to read. (2013: Now that we've
--     created the idea of "advanced" sections, this seems like
--     a nice candidate.)

-- Functions can be constructed "on the fly" without giving
-- them names.

example : doit3times (fun n => n * n) 2 = 256 := by rfl

-- The expression `fun n => n * n` can be read as "the function
-- that, given a number `n`, yields `n * n`."

-- Lean also supports a shorter notation using `·` as a
-- placeholder for the argument:

example : doit3times (· + 1) 0 = 3 := by rfl

example : filter (fun l => l.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

example : filter (·.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

-- ### Map

def map {α : Type} {β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | h :: t => f h :: map f t

example : map (· + 3) [2, 0, 2] = [5, 3, 5] := by rfl

example : map Nat.odd [2, 1, 2, 5] = [false, true, false, true] := by rfl

example : map (fun n => [n.even, n.odd]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]] := by rfl

-- _Quiz:_

-- Recall the definition of `map`:

--   def map (f : α → β) (l : List α) : List β :=
--     match l with
--     | [] => []
--     | h :: t => f h :: map f t

-- What is the type of `@map`?

-- (A) `{α β : Type} → α → β → List α → List β`

-- (B) `α → β → List α → List β`

-- (C) `{α β : Type} → (α → β) → List α → List β`

-- (D) `{α : Type} → (α → α) → List α → List α`

theorem map_nil {α : Type} {β : Type} (f : α → β) : map f [] = [] := by rfl

theorem map_cons {α : Type} {β : Type} (f : α → β) h t : map f (h :: t) = f h :: map f t := by rfl

-- Lists are not the only inductive type for which `map` makes
-- sense. Here is a `map` for the `Option` type:

def optionMap {α : Type} {β : Type} (f : α → β) (x? : Option α) : Option β :=
  match x? with
  | none => none
  | some x => some (f x)

-- ### Fold

def fold {α : Type} {β : Type} (f : α → β → β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)

-- This is the "reduce" in map/reduce...

example : fold (· && ·) [true, true, false, true] true = false := by rfl

example : fold (· * ·) [1, 2, 3, 4] 1 = 24 := by rfl

example : fold (· ++ ·) [[1], [], [2, 3], [4]] [] = [1, 2, 3, 4] := by rfl

example : fold (fun l n => l.length + n) [[1], [], [2, 3, 2], [4]] 0 = 5 := by rfl

theorem fold_nil {α : Type} {β : Type} (f : α → β → β) (b : β) : fold f [] b = b := by rfl

theorem fold_cons {α : Type} {β : Type} (f : α → β → β) h t (b : β) :
   fold f (h :: t) b = f h (fold f t b) := by rfl

-- _Quiz:_

-- Here is the definition of `fold` again:

--   def fold (f : α → β → β) (l : List α) (b : β) : β :=
--     match l with
--     | [] => b
--     | h :: t => f h (fold f t b)

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

-- ### Functions That Construct Functions

-- Here are two functions that *return* functions as results.

abbrev constfun {α : Type} (x : α) : Nat → α :=
  fun _ => x

abbrev ftrue := constfun true

example : ftrue 0 = true := by rfl

example : constfun 5 99 = 5 := by rfl

-- A two-argument function in Lean is actually a function that
-- returns a function!

#check (Nat.add : Nat → Nat → Nat)

abbrev plus3 := Nat.add 3
#check (plus3 : Nat → Nat)

example : plus3 4 = 7 := by rfl
example : doit3times plus3 0 = 9 := by rfl
example : doit3times (Nat.add 3) 0 = 9 := by rfl

-- Similarly, we can write:

abbrev fold_plus : List Nat → Nat → Nat :=
  fold (· + ·)

#check (fold_plus : List Nat → Nat → Nat)


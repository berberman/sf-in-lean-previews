import SFLCompat

--  # Typeclasses

--  Chapter Poly introduced **parametric polymorphism**,
--  declaring a type variable with no constraint on it.
--
--  This lets us work with a type like `List α`, writing
--  functions like `List.reverse` and `List.length` and
--  proofs like `List.length_reverse`, which use only the
--  list's structure and never inspect any particular
--  `a : α`.
--
--  Sometimes, though, we want less freedom: rather than
--  leaving `α` completely generic, we want to partially
--  specify its behavior. In Lean, this is done through a
--  form of "ad hoc polymorphism" called **typeclasses**.
--  The concept originated in Haskell and is analogous to
--  features you may know from other languages, such as
--  traits in Rust.

--  ## Why We Need Typeclasses

--  Consider the following function, which checks whether a
--  natural number occurs in a list:

def List.elemNat (n : Nat) (ms : List Nat) : Bool :=
  match ms with
  | [] => false
  | m :: ms' => bif n == m then true else elemNat n ms'

theorem List.elem_nat_nil (n : Nat) : [].elemNat n = false := rfl

theorem List.elem_nat_cons (n m : Nat) (ms : List Nat) :
    (m :: ms).elemNat n = bif n == m then true else elemNat n ms := rfl

#eval [0, 1].elemNat 0
#eval [0, 1].elemNat 1
#eval [0, 1].elemNat 2

--  What if we want this to work for lists of *any* element
--  type, not just `Nat`? Parametric polymorphism suggests
--  simply replacing `Nat` with a type variable `α`, but
--  that produces a puzzling error:

sf_expect_failure_in
  def List.elemPoly {α : Type} (x : α) (ys : List α) : Bool :=
    match ys with
    | [] => false
    | y :: ys' => bif x == y then true else elemPoly x ys'

--  Output:
--    failed to synthesize instance of type class
--      BEq α
--
--    Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

--  Lean is trying to use typeclasses to work out how `==`
--  should behave on a value of type `α`. We'll see exactly
--  why shortly; for now, here's one way to sidestep the
--  problem: have the caller supply the equality test to
--  use.

def List.elemPolyEq {α : Type} (eq : α → α → Bool) (x : α) (ys : List α) : Bool :=
  match ys with
  | [] => false
  | y :: ys' => bif eq x y then true else elemPolyEq eq x ys'

#eval [0, 1].elemPolyEq Nat.beq 0

--  This works, but it's tedious: every caller has to know,
--  and remember to supply, the right equality function.
--
--  Typeclasses automate this — instead of the programmer
--  passing the function explicitly, Lean searches for one
--  and provides it on its own. We specify something we want
--  Lean to search for by declaring a `class` with the
--  needed function as a field; a `class` is like an
--  interface in Java or a trait in Rust. Particular
--  implementations of that class are called *instances*;
--  each type can have its own instance of a class. For
--  functions that would use such instances, we specify the
--  name of the class in an *instance implicit* on the
--  polymorphic variable that the instance's function
--  applies to. This directs Lean to rely on the class
--  inside the function, and to find and fill in the
--  appropriate instance when the function is called.
--
--  Here is what this looks like for `List.elemPoly`:

def List.elemPoly {α : Type} [BEq α] (x : α) (ys : List α) : Bool :=
  match ys with
  | [] => false
  | y :: ys' => bif x == y then true else elemPoly x ys'

theorem List.elemPoly_nil {α : Type} [BEq α] (x : α) : [].elemPoly x = false := rfl

theorem List.elemPoly_cons {α : Type} [BEq α] (x y : α) (ys : List α) :
    (y :: ys).elemPoly x = bif x == y then true else elemPoly x ys := rfl

#eval [0, 1].elemPoly 0

--  Comparing `List.elemPolyEq` with `List.elemPoly`, we see
--  three differences. First, `List.elemPolyEq` takes an
--  *explicit* parameter `eq`, whereas `List.elemPoly`
--  specifies an instance implicit `[BEq α]`. The instance
--  implicit indicates that an instance of `BEq` must be
--  provided at call sites for the particular type `α` that
--  is used. Second, whereas `List.elemPolyEq` invokes
--  parameter `eq` to test equality, `List.elemPoly` uses
--  `==` instead. As Lists noted when we first used it, `==`
--  on `Nat` comes from the `BEq` typeclass. Finally,
--  whereas `[0, 1].elemPolyEq Nat.beq 0` passes the
--  equality function `Nat.beq` explicitly, in
--  `[0, 1].elemPoly 0` Lean fills it in automatically based
--  on the type `Nat` of the `List`.

--  Going back to the earlier version of `List.elemPoly`,
--  without the instance implicit, we can now understand the
--  error message: `α` was fully generic, so the `==` in its
--  body would have needed to work for *every* type `α`, and
--  no single `BEq` instance can do that. So Lean's search
--  failed.
--
--  Now it is time to dig into the details of what we have
--  seen so far. We'll see exactly how `[BEq α]` gets filled
--  in below, starting with how to define a typeclass in the
--  first place.

--  ## Defining Your Own Typeclasses

--  `BEq` comes from Lean's standard library. Let's define a
--  typeclass of our own, to see the mechanism — classes,
--  instances, and synthesis — that made `==` resolve
--  automatically above.
--
--  Suppose we want a function that returns the first
--  element of a list, defaulting to a given value if the
--  list is empty. As with `List.elemPolyEq` above, here is
--  a version that makes the default value an explicit
--  parameter:

def List.headOrEx {α : Type} (defaultValue : α) (xs : List α) : α :=
  match xs with
  | [] => defaultValue
  | x :: _ => x

#eval [1, 2, 3].headOrEx 0
#eval ([] : List Nat).headOrEx 0

--  This works, but again it's tedious: every caller has to
--  supply an element of `α` to default to, even when
--  there's an obvious choice based on the type of the
--  things in the list, like `0` for `Nat`.
--
--  Getting Lean to fill in `defaultValue` automatically
--  takes two things. One is marking the parameter as
--  "searchable," rather than something the caller always
--  supplies explicitly. The other is giving Lean some
--  information about what it should search *for*.
--
--  Considering the second problem first: the way to provide
--  this information is to *name* the data we're after — the
--  **default value** of a type. In particular, a
--  `structure` (chapter Lists) is a good way to give this
--  information a name; structures can also bundle together
--  more than one piece of data, which will come in handy
--  later, though we only need a single field here.
--
--  To address the first problem, we need to mark this
--  particular structure as one Lean should search for
--  automatically — not every `structure`-typed argument
--  should be.
--
--  Let's build up to what we want in two steps: first the
--  naming, as a plain `structure`; then the marking, by
--  upgrading it to a `class`. Here's the structure — we'll
--  put it in its own namespace so we can reuse the name
--  `DefaultValue` for the class version below:

namespace DefaultValueScratch

structure DefaultValue (α : Type) where
  value : α

--  A value of type `DefaultValue Nat` picks out a
--  particular `Nat` to serve as the type's default: it's
--  built the same way any structure is, by supplying a
--  `Nat` for the `value` field:

def natDefault : DefaultValue Nat where
  value := 0

end DefaultValueScratch

--  Now for the marking: we need to tell Lean that
--  `DefaultValue` is the sort of structure it should search
--  for automatically, the way it needs to for
--  `List.headOrEx`'s `defaultValue` argument. We do this by
--  writing `class` in place of `structure`:

class DefaultValue (α : Type) where
  value : α

--  We then provide values of this type a bit differently.
--  Instead of `def`, we use `instance`:

instance instDefaultValueNat : DefaultValue Nat where
  value := 0

--  Lean can now find this instance on its own, via
--  *typeclass synthesis* (or *typeclass inference*) — the
--  same process that found `BEq Nat` earlier. That means we
--  can rewrite `List.headOrEx` the same way we rewrote
--  `List.elemPolyEq` into `List.elemPoly` above, replacing
--  the explicit `defaultValue` parameter with an instance
--  implicit:

def List.headOr {α : Type} [DefaultValue α] (xs : List α) : α :=
  match xs with
  | [] => DefaultValue.value
  | x :: _ => x

#eval [1, 2, 3].headOr
#eval ([] : List Nat).headOr

example : DefaultValue.value = (0 : Nat) := by rfl

--  Notice that we refer to `DefaultValue.value` alone, with
--  no instance named. Because the expression equates
--  `DefaultValue.value` with the `Nat` `0`, Lean selects
--  `instDefaultValueNat`, the instance for
--  `DefaultValue Nat`. We know this because we are able to
--  prove that `DefaultValue.value` is equal to `0`.
--
--  Let's declare a second instance, for `Int`, the type of
--  integers `... -2, -1, 0, 1, 2, ...`:

instance instDefaultValueInt : DefaultValue Int where
  value := -1

--  We can also create instances for polymorphic types, like
--  `Option α`, whose default is `none`, by giving the
--  instance declaration a parameter:

instance instDefaultValueOption {α : Type} : DefaultValue (Option α) where
  value := none

--  Now, Lean can infer instances for all these types,
--  including inside `List.headOr`:

example : DefaultValue.value = (0 : Nat) := by rfl
example : DefaultValue.value = (-1 : Int) := by rfl
example : DefaultValue.value = (none : Option Bool) := by rfl
example : DefaultValue.value = (none : Option (List Nat)) := by rfl
example : ([] : List Nat).headOr = 0 := by rfl
example : ([] : List Int).headOr = -1 := by rfl
example : ([] : List (Option Bool)).headOr = none := by rfl
example : ([] : List (Option Bool)).headOr = none := by rfl

--  Synthesis infers instances we could have specified
--  explicitly:

example : instDefaultValueNat.value = (0 : Nat) := by rfl
example : instDefaultValueInt.value = (-1 : Int) := by rfl
example : instDefaultValueOption.value = (none : Option Nat) := by rfl

--  The option `pp.all` shows which instance Lean picked:

set_option pp.all true in
#check (DefaultValue.value : Nat)

--  Output:
--    @DefaultValue.value Nat instDefaultValueNat : Nat

set_option pp.all true in
#check (DefaultValue.value : Int)

--  Output:
--    @DefaultValue.value Int instDefaultValueInt : Int

--  This reveals `instDefaultValueNat` and
--  `instDefaultValueInt` as the instances Lean picked. The
--  `#synth` command runs the same search directly:

#synth DefaultValue Nat

--  Output:
--    instDefaultValueNat

--  For a typeclass like `DefaultValue` that carries data —
--  a term, such as the `1` above, rather than only proofs
--  (which we will see below) — we expect at most one
--  instance per type, so this search has a unique answer.
--
--  We'll put `DefaultValue`'s standard-library equivalent,
--  `Inhabited`, to work later in this chapter, when we
--  define maps that need a default value for a generic
--  type. First, though, let's go back to `List.elemPoly`
--  and see how its `[BEq α]` argument actually gets
--  resolved.

--  ## Using Typeclasses

--  Let's check what `==` meant for `List.elemNat`, with
--  notation display turned off:

set_option pp.notation false in
#check 1 == 2

--  Output:
--    BEq.beq 1 2 : Bool

--  Rather than `Nat.beq`, `==` turns out to be notation for
--  `BEq.beq`, a field of exactly the kind of typeclass we
--  just learned to define:

sf_recall
  class BEq (α : Type) where
      beq : α → α → Bool

--  Writing `x == y` makes Lean search for an **instance**
--  of `BEq` for the type of `x` and `y`, the same way it
--  searched for a `DefaultValue` instance above. For `Nat`,
--  that instance is:

instance (priority := low) : BEq Nat where
  beq := Nat.beq

--  This is the instance Lean supplies for `[BEq α]` when
--  `List.elemPoly` is called on a `List Nat` — no different
--  from Lean choosing `instDefaultValueNat` for
--  `DefaultValue.value` earlier when it was equated with
--  `(1 : Nat)`.

--  ### Exercise (1 star): List.elem_poly_eq_elem_nat ⭐

--  Prove that `List.elemPoly` agrees with `List.elemNat`
--  when specialized to natural numbers.

theorem List.elemPoly_eq_elemNat (ms : List Nat) (n : Nat) : ms.elemPoly n = ms.elemNat n := by
  sorry

--  ## Proof-Carrying Typeclasses

--  The above examples enforce no conditions on the data an
--  instance may carry — any value of the right type will
--  do. But sometimes enforcing constraints on data is
--  useful. For example, suppose we want to specify that a
--  type has not just a single element, but two. Here is a
--  first attempt:

sf_experiment
  class HasTwoIncomplete (α : Type) where
    one : α
    two : α

--  Unfortunately, this specification isn't precise because
--  it allows `one` and `two` to refer to the same term.
--  Fortunately, Lean's typeclasses can carry proofs along
--  with data, so we can write the following to enforce that
--  `one` and `two` are distinct.

class HasTwo (α : Type) where
  one : α
  two : α
  one_neq_two : one ≠ two

--  Declaring instances works in much the same way as
--  before, except that now the `HasTwo.one_neq_two` field
--  requires a proof:

instance : HasTwo Nat where
  one := 1
  two := 2
  one_neq_two := by intro contra; contradiction

--  In most languages that support typeclasses (or traits)
--  it is not possible to formally enforce laws such as
--  `one_neq_two`. Thus it falls to the author to check,
--  informally, that any required invariants are satisfied,
--  which can lead to bugs.

--  ### Exercise (1 star): HasThree ⭐

--  Following the pattern of `DefaultValue` and `HasTwo`,
--  define a class `HasThree` that specifies a type with at
--  least three distinct elements, and give an instance of
--  it for `Nat`.

class HasThree (α : Type) where
  one : α
  two : α
  three : α
  one_neq_two : one ≠ two
  --  FILL IN HERE

instance : HasThree Nat where
  one := 1
  two := 2
  three := 3
  one_neq_two := sorry
  --  FILL IN HERE

namespace Algebra

--  This facility is very powerful, and is used extensively
--  in Lean to define mathematical structures that carry
--  both operators and laws about how those operators
--  interact. As a simple example, let's use a typeclass to
--  define a *monoid*, a simple algebraic structure that
--  includes four things:
--
--  - an underlying set of data, represented by a type `α`,
--
--  - an operator (which we'll write `⊗`, typed otimes) that
--    combines two elements of type `α` into one,
--
--  - a particular element `id` of type `α`, which we call
--    the "identity element", and
--
--  - some laws about the interaction of `⊗` and `id`,
--    namely that:
--
--    - `∀ x, id ⊗ x = x = x ⊗ id`, and
--
--    - `∀ x y z, x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z` (i.e., that `⊗`
--      is associative)
--
--  We can express these requirements in the form of a
--  typeclass:

-- first we define a notation typeclass for our operator ⊗
class OpSet (α : Type) where
  op : α → α → α

infixr:70 " ⊗ " => OpSet.op

class Monoid (α : Type) extends (OpSet α) where
  id : α
  left_id  (x : α)  : id ⊗ x = x
  right_id (x : α)  : x ⊗ id = x
  assoc (x y z : α) : x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z

--  The `extends` keyword indicates that the `Monoid`
--  typeclass extends the `OpSet` typeclass, which just
--  defines a set with an operator and some notation for it.
--  The `Monoid` typeclass "inherits" the fields of `OpSet`,
--  similar to how a class would in an object-oriented
--  language.
--
--  As one might expect, the `+` operator over `Nat`s forms
--  a monoid, where `0` is the identity element. Note that
--  we don't have to define `Nat`'s `OpSet` instance
--  separately, we can define a single instance that
--  implements both classes.

instance : Monoid Nat where
  op := Nat.add
  id := 0
  left_id := by lia
  right_id := by lia
  assoc := by lia

--  ### Exercise (1 star): NatMonoidMul ⭐

--  However, multiplication on `Nat`s *also* forms a monoid.
--  What is its identity element?

instance : Monoid Nat where
  op := Nat.mul
  id := sorry
  left_id := sorry
  right_id := sorry
  assoc := sorry

--  ### Exercise (1 star): ListMonoidAppend ⭐

--  There are also many monoids over other types. Most
--  usefully in computer science, lists of any type also
--  form a monoid, with `List.append` as the operator in
--  question:

instance {α : Type} : Monoid (List α) where
  op := List.append
  id := sorry
  left_id := sorry
  right_id := sorry
  assoc := sorry

--  In addition to defining instances of `Monoid`, we can
--  also prove some properties about monoids in general,
--  just based on the laws defined on the typeclass. One
--  simple theorem about monoids is that the identity
--  element of a monoid is unique. That is, if we have two
--  monoids over the same set with the same operator, their
--  identity elements must also be the same:

theorem id_unique {α : Type} {m₁ m₂ : Monoid α} (h : m₁.op = m₂.op) : m₁.id = m₂.id := by
  obtain @⟨op₁, id₁, left_id₁, right_id₁, assoc₁⟩ := m₁
  obtain @⟨op₂, id₂, left_id₂, right_id₂, assoc₂⟩ := m₂
  have h' : id₁ = id₂ := by
    -- this introduces a use of m₁'s operator
    rw [← left_id₁ id₂]
    -- we use our hypothesis to rewrite m₁'s operator into m₂'s
    rw [h]
    -- then, we can use m₂'s right id
    rw [right_id₂]
  -- the goal `m₁.id = m₂.id` is equivalent with `id₁ = id₂` even though it displays `Monoid.id = Monoid.id`
  exact h'

--  In the above proof, we can destructure the monoid
--  instances `m₁` and `m₂` with the `obtain` tactic we saw
--  in the Logic chapter. When we do so however, because
--  these are class instances instead of normal structures,
--  we prepend our tuple by the `@` symbol. When stepping
--  through the above proof, if the notation is confusing to
--  you, remember that you can set `set_option pp.all true`
--  or `set_option pp.explicit true` to make Lean show you
--  more clearly what is going on. For example, the goal is
--  displayed as `Monoid.id = Monoid.id` since the instances
--  `m₁` and `m₂` are implicit arguments to `Monoid.id`.
--  Setting `pp.explicit true` displays the goal as
--  `@Eq α (@Monoid.id α m₁) (@Monoid.id α m₂)`.
--
--  A *group* is a special kind of monoid with an *inverse*
--  operation `inv`, which has the property that
--  `∀ x, inv x ⊗ x = id = x ⊗ inv x`. We can extend the
--  definition of a `Monoid` to capture this new feature:

class Group (α : Type) extends (Monoid α) where
  inv : α → α
  left_inv  (x : α) : inv x ⊗ x = id
  right_inv (x : α) : x ⊗ inv x = id

--  Now, the monoids we described earlier are not groups:
--  there is no inverse operation on the natural numbers
--  such that `∀ x, x + inv x = 0 = inv x + x`, for example.
--  However, addition does form a group over the integers:

--  ### Exercise (1 star): IntGroupAdd ⭐

instance : Group Int where
  op := Int.add
  id := sorry
  inv := sorry
  left_id := sorry
  right_id := sorry
  assoc := sorry
  left_inv := sorry
  right_inv := sorry

--  The study of groups is called *group theory* and is a
--  rich area of mathematics. Here, we will only prove a
--  handful of its simplest results:

--  ### Exercise (1 star): InverseUnique ⭐

--  Two groups defined with the same operation over the same
--  set must have the same inverse as well.

theorem inv_unique {α : Type} {g₁ g₂ : Group α} (h : g₁.op = g₂.op) : g₁.inv = g₂.inv := by
  sorry

--  ### Exercise (1 star): IdentityUnique ⭐

--  If an element of a monoid satisfies just one of the the
--  identity laws (here, we take the left), then it must be
--  equal to the monoid's identity element.

theorem Monoid.id_unique_left {α : Type} [Monoid α] (x : α)
    (hₗ : ∀ y, x ⊗ y = y) : x = id := by
  sorry

--  ### Exercise (2 stars): InverseInverse ⭐⭐

--  The inverse of the inverse of an element is itself; we
--  prove this using an intermediate lemma.

theorem inv_inv' {α : Type} {g : Group α} (x y z : α)
    (h₁ : g.inv x = y) (h₂ : g.inv y = z) : x = z := by
  sorry

theorem inv_inv {α : Type} {g : Group α} (x : α) : g.inv (g.inv x) = x := by
  sorry

end Algebra

--  ## API and Encapsulation

--  ## Maps

--  *Maps* (or "dictionaries") are ubiquitous data
--  structures both in ordinary programming and in the
--  theory of programming languages; we're going to need
--  them in many places in later volumes.
--
--  We'll define two flavors of maps: *total maps*, which
--  include a "default" element to be returned when a key
--  being looked up doesn't exist, and *partial maps*, which
--  instead return an option to indicate success or failure.
--  Partial maps are defined in terms of total maps, using
--  `none` as the default element.

--  ### Key and Value Types

--  To define maps, we first need a type for the keys that
--  we will use to index into our maps and a type for the
--  values the maps return. In this section, we'll use the
--  type variable `α` for the type of keys and `β` for
--  values. In addition to `BEq`, which we have already
--  seen, our key type `α` requires instances of the
--  `ReflBEq` and `LawfulBEq` typeclasses:

sf_recall
  class ReflBEq (α : Type) [BEq α] : Prop where
      rfl {a : α} : a == a

sf_recall
  class LawfulBEq (α : Type) [BEq α] : Prop extends ReflBEq α where
      eq_of_beq : {a b : α} → a == b → a = b

--  These classes refine `BEq`, specifying that (`==`) is
--  reflexive and coincides with proposition equality `=`.
--
--  In general, we place no constraints on the value type
--  `β`.

--  ### Total Maps

--  The Lists chapter introduced a partial map abstraction,
--  `PartialMap`, with a `find` function for lookup, based
--  on lists of key-value pairs. Here, we are going to build
--  a map abstraction using functions instead. The advantage
--  of this representation is that it offers a more
--  *extensional* view of maps, as we saw with functions in
--  the Logic chapter: two maps that respond to every query
--  in the same way will be represented as exactly the same
--  function, rather than just as "equivalent" list
--  structures. This simplifies proofs that use maps.
--
--  Instead of using functions directly, we encapsulate them
--  inside a `structure` which we call `TotalMap`.
--  Intuitively, a total map just contains a function
--  `inner` from a key of type `α` to a value of type `β`.

structure TotalMap (α : Type) (β : Type) where
  inner : α → β

namespace TotalMap

--  In order to declare a default value of `β` we will use
--  the `Inhabited` typeclass, which is the standard
--  library's implementation of our `DefaultValue` example
--  from above:
--
--  The function `TotalMap.empty` yields an empty total map,
--  given a default element; this map always returns the
--  default element when applied to any key.

def empty {α β : Type} [Inhabited β] : TotalMap α β where
  inner := fun _ => default

--  These types and implicit instances are now available
--  automatically to all the definitions in this section.
--
--  Just as declaring `BEq`/`DefaultValue` instances above
--  hooked `==` and `DefaultValue.value` up to our types, we
--  can declare an instance of the standard library's
--  `EmptyCollection` typeclass to associate `∅` with this
--  empty map.

instance {α β : Type} [Inhabited β] : EmptyCollection (TotalMap α β) where
  emptyCollection := TotalMap.empty

theorem empty_def {α β : Type} [Inhabited β] :
    (∅ : TotalMap α β) = { inner := fun _ => default } := by rfl

--  Here, for example, is an empty map that takes `Nat` keys
--  to `Nat` values:

def emptyNatMap : TotalMap Nat Nat := ∅

--  #### Getting Elements

--  While `TotalMap`s happen to be implemented as functions
--  under the hood, we would prefer not to expose this fact
--  in its public interface. Accordingly, we define new
--  operations for querying and updating mappings. We define
--  a function `get` for getting the value associated with a
--  key playing the role that `find` played for the Lists
--  chapter's list-based maps,

def get {α β : Type} (m : TotalMap α β) (a : α) := m.inner a

/-- This exposes implementation-specific details of `TotalMap`.
  Avoid using this outside the `TotalMap` namespace. -/
theorem get_def {α β : Type} {m : TotalMap α β} {a : α} : m.get a = m.inner a := by rfl

example : emptyNatMap.get 2 = 0 := by rfl

--  Here is an example that uses the API lemmas `empty_def`
--  and `get_def`:

example {n : Nat} : emptyNatMap.get n = 0 := by
  rewrite [get_def, emptyNatMap, empty_def, Nat.default_eq_zero]
  rfl

--  In the above example, we use `rewrite` and `rfl` instead
--  of the usual `rw` to highlight something interesting.
--  After the rewrites in this proof, we end up with a goal
--  that looks like `{ inner := fun x => 0 }.inner n = 0`,
--  which we can solve with `rfl`. This is because the
--  projection `.inner` on a structure of the form
--  `{ inner := x }` is definitionally equal to `x`.
--
--  `get` is the public API counterpart to `inner` which is
--  an implementation-specific detail of `TotalMap`. Because
--  `get_def` "peeks" through the abstraction, it should be
--  used sparingly, and only inside the `TotalMap`
--  namespace.
--
--  To make element-getting more convenient, let's define
--  notation so we can write `emptyNatMap[2]` rather than
--  `emptyNatMap.get`. We could notate `get` directly —
--  we'll do exactly that for `update` below — but here
--  we'll instead make "getting an element" its own
--  typeclass, `MyGetElem`, and notate it. Doing so means
--  `m[a]` resolves to `MyGetElem.getElem m a` for any type
--  with a `MyGetElem` instance, not just `TotalMap`.
--
--  Using typeclasses to define notation is typical in Lean
--  when the same notation is useful for many different
--  types. We have seen the approach already with `==`:
--  writing `x == y` is notation for `BEq.beq`, resolved by
--  instance search for whatever type `x` and `y` have. We
--  also just saw overloaded notation for `EmptyCollection`
--  above, where `∅` is notation for
--  `EmptyCollection.emptyCollection`. Our typeclass
--  `MyGetElem` is a simpler version of the standard
--  library's `GetElem` typeclass, which has many instances
--  such as `Array`, `List`, and `Vector`. We develop it to
--  illustrate the notation-as-typeclass approach.

end TotalMap

--  The `MyGetElem` typeclass takes three type parameters:
--  the collection implementation, its keys, and its values.

class MyGetElem (coll : Type) (idx : Type) (elem : outParam Type) where
  getElem (xs : coll) (i : idx) : elem

--  (Don't worry about the `outParam` qualifier; it is a
--  hint to Lean that helps typeclass inference.)
--
--  The appropriate instance of `MyGetElem` for our
--  `TotalMap` is:

instance {α β : Type} : MyGetElem (TotalMap α β) α β where
  getElem m a := m.get a

--  Now we can associate the bracket syntax with
--  `MyGetElem.getElem`. We've defined custom notation
--  before — `::` and `[...]` for lists (chapter Lists,
--  including an `app_unexpander` for printing
--  `[...]`-notation lists back out), or `+`/`*`/`==` for
--  arithmetic — but always with `infixl`/`infixr` or
--  `scoped macro`; this is the first time we reach for the
--  more general `notation`/`macro_rules` forms for getting
--  the `m[a]` syntax to work.
--
--  Don't worry about following the mechanism in detail —
--  the `macro_rules` and the `app_unexpander` below are
--  minor technicalities. However, if you do wish to learn
--  more, Chapter 5 and 6 of [Metaprogramming in Lean
--  4](https://leanprover-community.github.io/lean4-metaprogramming-book/)
--  contain more detail.

namespace MyGetElem

scoped macro_rules | `($xs[$i]) => ``(getElem $xs $i)

@[app_unexpander getElem]
def unexpandGetElem : Lean.PrettyPrinter.Unexpander
  | `($_ $xs $i) => `($xs[$i])
  | _ => throw ()
end MyGetElem

open scoped MyGetElem

--  Since the standard library already declares the `x[i]`
--  syntax for `GetElem`, we only need to define the
--  `macro_rules`, not the `notation` as we have done
--  previously. It's scoped since we don't want to override
--  the default `GetElem` everywhere, but only when
--  `open scoped MyGetElem` is in force.

--  Since we provided a `MyGetElem` instance for `TotalMap`,
--  we can now use the notation `m[a]` to access elements of
--  a map `m`.

namespace TotalMap

theorem getElem_def {α β : Type} (m : TotalMap α β) (a : α) : m[a] = m.get a := by rfl

example : emptyNatMap[1] = default := by rfl

example {n : Nat} : emptyNatMap[n] = 0 := by
  rw [getElem_def, get_def, emptyNatMap, empty_def, Nat.default_eq_zero]

--  We want the public API of `TotalMap` to use the `m[a]`
--  notation instead of `m.get a`, so we provide the reverse
--  direction of `getElem_def` as a `simp` lemma; the `m[a]`
--  notation is the `TotalMap` API's `simp` normal form.

@[simp]
theorem get_eq_getElem {α β : Type} (m : TotalMap α β) (a : α) : m.get a = m[a] := rfl

example {n : Nat} : emptyNatMap.get n = emptyNatMap[n] := by
  simp

--  This design minimizes the need to use `getElem_def`
--  outside concrete examples (which are typically solvable
--  with `rfl` anyways).

--  #### Updating Elements

--  Now we turn to the `update` function, which takes a map
--  `m`, a key `a`, and a value `b`, and returns a new map
--  that takes `a` to `b` and takes every other key to
--  whatever `m` does. We do this by wrapping a new map
--  function around the old one.

def update {α β : Type} (m : TotalMap α β) [BEq α] (a : α) (b : β) : TotalMap α β where
  inner := fun a' => bif a == a' then b else m[a']

--  For example, we can build a map taking `String` to
--  `Bool`, where `"foo"` and `"bar"` are mapped to `true`
--  and every other key is mapped to `false`, like this:

def exampleMap :=
  (∅ : TotalMap String Bool)
    |>.update "foo" true
    |>.update "bar" true

--  Here `|>` is Lean's **pipe** notation: `x |>.f y` means
--  `x.f y`, letting us chain a sequence of function or
--  method calls left to right without nested parentheses.

--  We also introduce a notation for updating maps — this
--  time, rather than going through a typeclass and its own
--  `notation`/`macro_rules` machinery as we did for
--  `MyGetElem`, we write a `notation` that references
--  `TotalMap.update` directly. Unlike indexing, `update`
--  doesn't need to work generically across container types
--  (there's no standard-library operation like `GetElem`
--  that we're mirroring here), so the simpler, direct route
--  suffices.

notation a:55 " →ₜ " b:55 " ; " m:55 => TotalMap.update m a b

/-- This exposes implementation-specific details of `TotalMap`.
  Avoid using this outside the `TotalMap` namespace.
  Prefer `update_apply` if possible. -/
theorem update_def {α β : Type} [BEq α] (m : TotalMap α β) (a : α) (b : β) :
  a →ₜ b ; m = { inner := fun a' => bif a == a' then b else m[a'] } := by rfl

theorem update_apply {α β : Type} [BEq α] (m : TotalMap α β) (a a' : α) (b : β) :
  (a →ₜ b ; m)[a'] = bif a == a' then b else m[a'] := by rfl

--  We can omit the map from the notation when we want it to
--  be empty:

notation a:55 " →ₜ " b:55 => TotalMap.update ∅ a b

--  The `examplemap` above can now be defined as follows:

def exampleMap' : TotalMap String Bool := "bar" →ₜ true ; "foo" →ₜ true ; ∅
def exampleMap'' : TotalMap String Bool := "bar" →ₜ true ; "foo" →ₜ true

example : exampleMap = exampleMap' := by rfl
example : exampleMap' = exampleMap'' := by rfl

example : exampleMap'["bar"] = true := by rfl
example : exampleMap'["foo"] = true := by rfl
example : exampleMap'["quux"] = false := by rfl

--  Let's also see a couple of examples of working with
--  updated maps using rewrites:

example : exampleMap'["bar"] = true := by
  rw [exampleMap', update_apply, BEq.rfl, cond_true]

example : exampleMap'["foo"] = true := by
  rw [exampleMap', update_apply, show ("bar" == "foo") = false by simp, cond_false]
  rw [update_apply, BEq.rfl, cond_true]

example : exampleMap'["quux"] = false := by
  rw [exampleMap', update_apply, show ("bar" == "quux") = false by simp, cond_false]
  rw [update_apply, show ("foo" == "quux") = false by rfl, cond_false]
  rw [empty_def, getElem_def, get_def, Bool.default_bool]

--  When we use maps in later volumes, we'll need several
--  fundamental facts about how they behave.
--
--  Even if you don't work the following exercises, make
--  sure you thoroughly understand the statements of the
--  lemmas!
--
--  (Some of the proofs require the extensionality tactic
--  `ext`, discussed in the Logic chapter.)
--
--  First, the empty map returns its default element for all
--  keys:

@[simp]
theorem getElem_empty {α β : Type} [BEq α] [Inhabited β] (a : α) : (∅ : TotalMap α β)[a] = default := by
  rw [empty_def, getElem_def, get_def]

--  Notice that in the example `exampleMap'["quux"] = false`
--  the last rewrite is effectively just `getElem_empty`.
--
--  Next, if we update a map `m` at a key `a` with a new
--  value `b` and then look up `a` in the map resulting from
--  the `update`, we get back `b`:

@[simp]
theorem update_eq {α β : Type} [BEq α] [ReflBEq α] (m : TotalMap α β) (a : α) (b : β) : (a →ₜ b ; m)[a] = b := by
  rw [update_def, getElem_def, get_def]
  dsimp only -- reduces `{ inner := ... }.inner` so that we get a subterm that looks like `a == a`
  rw [BEq.rfl, cond_true]

--  On the other hand, if we update a map `m` at a key `a₁`
--  and then look up a *different* key `a₂` in the resulting
--  map, we get the same result that `m` would have given:

--  ### Exercise (2 stars): update_neq (Optional) ⭐⭐

@[simp]
theorem update_neq {α β : Type} [BEq α] [LawfulBEq α] {m : TotalMap α β} {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) :
    (a₁ →ₜ b ; m)[a₂] = m[a₂] := by
  sorry

--  The two remaining facts are equalities *between maps*,
--  so we first need to say when two maps are equal. Since a
--  total map is implemented as a function, this is
--  effectively the functional extensionality principle
--  (`funext`) from the Logic chapter: two maps are equal
--  when they agree at every key. Recording it once, for
--  maps, and tagging it `@[ext]` lets the `ext` tactic
--  reduce a goal `m₁ = m₂` to the pointwise one in the
--  proofs below.
--
--  The fact that `TotalMap` is a structure complicates
--  things slightly. We need to use injectivity of its
--  constructor `mk` which Lean automatically provides for
--  us as `mk.injEq`. It lets us prove `m₁ = m₂` from
--  `m₁.inner = m₂.inner` or vice versa.

@[ext]
theorem ext {α β : Type} {m₁ m₂ : TotalMap α β} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
  rw [TotalMap.mk.injEq]
  ext a; specialize h a
  rw [getElem_def, get_def, getElem_def, get_def] at h
  exact h

--  To demonstrate this extensionality principle, let's look
--  at an example:

example : "bar" →ₜ true ; "foo" →ₜ true = "foo" →ₜ true ; "bar" →ₜ true := by
  ext a
  by_cases h : "bar" = a
  · subst h
    rw [update_eq, update_neq (show "foo" ≠ "bar" by simp), update_eq]
  · simp only [update_apply]
    rw [beq_false_of_ne h]
    simp

--  Given keys `a₁` and `a₂`, the tactic `by_cases`
--  `h : a₁ = a₂` splits the proof into the case where they
--  are equal — where `subst h` then replaces one by the
--  other — and the case where they are not, which is what
--  `update_neq` wants. Use it to prove the following
--  theorem, which states that if we update a map to assign
--  key `a` the same value as it already has in `m`, then
--  the result is equal to `m`:

--  ### Exercise (2 stars): update_same ⭐⭐

@[simp]
theorem update_same {α β : Type} [BEq α] [LawfulBEq α] (m : TotalMap α β) (a : α) : (a →ₜ m[a] ; m) = m := by
  sorry

--  Similarly, if we update a map `m` at a key `a` with a
--  value `b₁` and then update again with the same key `a`
--  and another value `b₂`, the resulting map behaves the
--  same (gives the same result when applied to any key) as
--  the simpler map obtained by performing just the second
--  `update` on `m`:

--  ### Exercise (2 stars): update_shadow (Optional) ⭐⭐

@[simp]
theorem update_shadow {α β : Type} [BEq α] [LawfulBEq α] (m : TotalMap α β) (a : α) (b₁ b₂ : β) :
    (a →ₜ b₂ ; a →ₜ b₁ ; m) = (a →ₜ b₂ ; m) := by
  sorry

--  Similarly, prove one final property of the `update`
--  function: if we update a map `m` at two distinct keys,
--  it doesn't matter in which order we do the updates.

--  ### Exercise (3 stars): update_permute ⭐⭐⭐

theorem update_permute {α β : Type} [BEq α] [LawfulBEq α] {m : TotalMap α β} {a₁ a₂ : α} {b₁ b₂ : β} (h : a₁ ≠ a₂) :
    (a₁ →ₜ b₁ ; a₂ →ₜ b₂ ; m) = (a₂ →ₜ b₂ ; a₁ →ₜ b₁ ; m) := by
  sorry

end TotalMap

--  ### Notation for Concrete Maps

--  Wouldn't it be nice if we could use a more natural
--  notation for concrete maps like
--  `{ "bar" ↦ true, "foo" ↦ true }`? To accomplish this we
--  define a simple structure that consists of a key and a
--  value along with `↦` notation for it.

/--
A key-value pair with `↦` syntax.
-/
@[ext]
structure KVPair (K : Type) (V : Type) where
  key : K
  value : V

namespace KVPair
scoped notation k " ↦ " v => KVPair.mk k v
end KVPair

open scoped KVPair

--  Next, we declare `Insert` and `Singleton` instances —
--  the standard-library typeclasses behind the
--  `{x, y, ...}` and `{x}` collection-literal notation that
--  `List`, `Finset`, and other stdlib containers already
--  support — so that `TotalMap` can use it too.

namespace TotalMap

instance {α β : Type} [BEq α] : Insert (KVPair α β) (TotalMap α β) where
  insert kv m := kv.key →ₜ kv.value ; m

instance {α β : Type} [BEq α] [Inhabited β] : Singleton (KVPair α β) (TotalMap α β) where
  singleton kv := insert kv ∅

instance {α β : Type} [BEq α] [Inhabited β] : LawfulSingleton (KVPair α β) (TotalMap α β) where
  insert_empty_eq _ := rfl

end TotalMap

--  Here are a couple of examples using the new notation:

example : ({ "bar" ↦ true, "foo" ↦ true }) = "bar" →ₜ true ; "foo" →ₜ true ; ∅ := rfl

example : ({ "foo" ↦ true } : TotalMap String Bool)["foo"] = true := rfl

example : ({ 1 ↦ 2, 1 ↦ 3 } : TotalMap Nat Nat)[1] = 2 := rfl

--  The reason we need to explicitly specify the type of the
--  map is that Lean doesn't know what type of collection
--  `{ "foo" ↦ true }` is without type hints, as we can see
--  with `#check`:

#check { "foo" ↦ true }

--  Output:
--    {"foo" ↦ true} : ?m.4

--  The type shows a `?m.4`, which indicates that Lean can't
--  infer the type. A type which can't be inferred doesn't
--  have any type classes like `MyGetElem`, so typeclass
--  resolution gets stuck in the following example:

sf_expect_failure_in
  example : ({ "foo" ↦ true })["foo"] = true := by rfl

--  ### Partial Maps

--  Lastly, we define *partial maps* on top of total maps. A
--  partial map with elements of type `β` is simply a total
--  map with elements of type `Option β`, whose default
--  element is `none`.

structure PartialMap (α : Type) (β : Type) where
  /-- The underlying total map. Lean always generates a public projection for a structure
    field, so `inner` is technically accessible, but it isn't part of the intended interface:
    use `PartialMap.toTotal` instead, so there's exactly one sanctioned way to get at it. -/
  inner : TotalMap α (Option β)

/- Note that this definition of `EmptyCollection` doesn't need `β` to have an `Inhabited`
  instance like `TotalMap` did. This is because `Option β` has its own `Inhabited` instance:
  `none` is a value of every `Option` type. -/
instance {α β : Type} : EmptyCollection (PartialMap α β) where
  emptyCollection := { inner := ∅ }

namespace PartialMap

def toTotal {α β : Type} (m : PartialMap α β) : TotalMap α (Option β) := m.inner

/-- This exposes implementation-specific details of `PartialMap`.
  Avoid using this outside the `PartialMap` namespace. -/
theorem toTotal_def {α β : Type} (m : PartialMap α β) : m.toTotal = m.inner := by rfl

instance {α β : Type} : MyGetElem (PartialMap α β) α (Option β) where
  getElem m a := m.toTotal[a]

theorem getElem_def {α β : Type} (m : PartialMap α β) (a : α) : m[a] = m.toTotal[a] := rfl

def emptyNatMap : PartialMap Nat Nat where
  inner := ∅

example : emptyNatMap[1] = default := by rfl

example {n : Nat} : emptyNatMap[n] = none := by
  rw [getElem_def, toTotal_def, emptyNatMap]
  dsimp only
  rw [TotalMap.getElem_def, TotalMap.get_def, TotalMap.empty_def, Option.default_eq_none]

@[simp]
theorem toTotal_eq_getElem {α β : Type} (m : PartialMap α β) (a : α) :
    m.toTotal[a] = m[a] := rfl

--  We previously defined `TotalMap.get` so that users can
--  retrieve elements from a `TotalMap` in a manner
--  independent of its actual implementation, which is a
--  function stored in `TotalMap.inner`. We follow a similar
--  principle with `PartialMap`s, and define
--  `PartialMap.toTotal` to be the public API counterpart to
--  `PartialMap.inner`.
--
--  We again want the public API to use the `m[a]` notation
--  instead of `m.toTotal[a]`, so we provide the reverse
--  direction of `getElem_def` as a `simp` lemma to specify
--  that the `simp` normal form is `m[a]`.
--
--  Updating a partial map at a key means storing a `some`
--  value there. To update, we create a new partial map from
--  `a →ₜ some b ; m.toTotal` by wrapping it in angle
--  brackets, i.e. using the anonymous constructor syntax.
--  This is equivalent to writing
--  `{ inner := a →ₜ some b ; m.toTotal }`. We also
--  introduce a similar notation for it as for total maps.

def update {α β : Type} [BEq α] (m : PartialMap α β) (a : α) (b : β) : PartialMap α β :=
  ⟨a →ₜ some b ; m.toTotal⟩

notation a:55 " →ₚ " b:55 " ; " m:55 => PartialMap.update m a b

notation a:55 " →ₚ " b:55 => PartialMap.update ∅ a b

def examplePmap : PartialMap String Bool := "Church" →ₚ true ; "Turing" →ₚ false

--  Next, we provide some fundamental properties about
--  `toTotal`:

@[simp]
theorem toTotal_empty {α β : Type} : (∅ : PartialMap α β).toTotal = (∅ : TotalMap α (Option β)) := rfl

@[simp]
theorem toTotal_update {α β : Type} [BEq α] (m : PartialMap α β) (a : α) (b : β) :
    (a →ₚ b ; m).toTotal = a →ₜ some b ; m.toTotal := rfl

--  As an example, here's how we can use these on some
--  concrete maps:

example : (2 →ₚ 3)[2] = some 3 := by
  rw [getElem_def, toTotal_update, toTotal_empty, TotalMap.update_eq]

--  This also holds by definition (`rfl`), since all the
--  rewrites in the above proof do the computation
--  step-by-step.

example : (2 →ₚ 3)[2] = some 3 := by rfl

--  Next, we lift all of the basic lemmas about total maps
--  to partial maps. To do this we should first prove an
--  extensionality lemma about partial maps. To prove
--  extensionality, we employ injectivity of `PartialMap`'s
--  constructor `mk` using `mk.injEq`.

theorem toTotal_eq_iff {α β : Type} (m₁ m₂ : PartialMap α β) : m₁.toTotal = m₂.toTotal ↔ m₁ = m₂ := by
  rw [mk.injEq]
  rfl

@[ext]
theorem ext {α β : Type} {m₁ m₂ : PartialMap α β} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
  rw [← toTotal_eq_iff]
  exact TotalMap.ext h

--  Now, let's lift the `TotalMap` lemmas:

@[simp]
theorem getElem_empty {α β : Type} [BEq α] (a : α) : (∅ : PartialMap α β)[a] = none := by
  rw [getElem_def, toTotal_empty, TotalMap.getElem_empty, Option.default_eq_none]

@[simp]
theorem update_eq {α β : Type} [BEq α] [ReflBEq α] (m : PartialMap α β) (a : α) (b : β) :
    (a →ₚ b ; m)[a] = some b := by
  rw [getElem_def, toTotal_update, TotalMap.update_eq]

@[simp]
theorem update_neq {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β} {a₁ a₂ : α}
    (h : a₁ ≠ a₂) (b : β) : (a₁ →ₚ b ; m)[a₂] = m[a₂] := by
  simp only [getElem_def, toTotal_update]
  rw [TotalMap.update_neq h]

theorem update_shadow {α β : Type} [BEq α] [LawfulBEq α] (m : PartialMap α β) (a : α) (b₁ b₂ : β) :
    (a →ₚ b₂ ; a →ₚ b₁ ; m) = (a →ₚ b₂ ; m) := by
  apply ext
  intro x
  simp only [getElem_def, toTotal_update]
  rw [TotalMap.update_shadow]

theorem update_same {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β} {a : α} {b : β}
    (h : m[a] = some b) : (a →ₚ b ; m) = m := by
  apply ext
  intro x
  simp only [getElem_def, toTotal_update]
  rw [← h, getElem_def, TotalMap.update_same]

theorem update_permute {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β} {a₁ a₂ : α}
    {b₁ b₂ : β} (h : a₁ ≠ a₂) : (a₁ →ₚ b₁ ; a₂ →ₚ b₂ ; m) = (a₂ →ₚ b₂ ; a₁ →ₚ b₁ ; m) := by
  apply ext
  intro x
  simp only [getElem_def, toTotal_update]
  rw [TotalMap.update_permute h]

example : (2 →ₚ 3)[2] = some 3 := by
  simp

example : examplePmap["Post"] = none := by
  rw [examplePmap]
  simp

--  And let's add `{}`-notation for partial maps as well.

instance {α β : Type} [BEq α] : Insert (KVPair α β) (PartialMap α β) where
  insert kv m := kv.key →ₚ kv.value ; m

instance {α β : Type} [BEq α] : Singleton (KVPair α β) (PartialMap α β) where
  singleton kv := insert kv ∅

instance {α β : Type} [BEq α] : LawfulSingleton (KVPair α β) (PartialMap α β) where
  insert_empty_eq _ := rfl

example : { 1 ↦ 2, 2 ↦ 3 } = 1 →ₚ 2 ; 2 →ₚ 3 := rfl

--  One last thing: for partial maps, it's convenient to
--  introduce a notion of map inclusion, stating that all
--  the entries in one map are also present in another. Lean
--  already has notation for this — `m₁ ⊆ m₂` — which we get
--  by supplying a `HasSubset` instance.

def Subset {α β : Type} (m₁ m₂ : PartialMap α β) : Prop :=
  ∀ {a : α} {b : β}, m₁[a] = some b → m₂[a] = some b

instance {α β : Type} : HasSubset (PartialMap α β) where
  Subset := PartialMap.Subset

theorem subset_def {α β : Type} (m₁ m₂ : PartialMap α β) :
    m₁ ⊆ m₂ ↔ (∀ {a : α} {b : β}, m₁[a] = some b → m₂[a] = some b) := .rfl

--  We can then show that map update preserves map
--  inclusion, that is:

theorem update_subset {α β : Type} [BEq α] [LawfulBEq α] (m₁ m₂ : PartialMap α β) (a : α) (b : β)
    (h : m₁ ⊆ m₂) : (a →ₚ b ; m₁) ⊆ (a →ₚ b ; m₂) := by
  rw [subset_def] at h ⊢
  intro a' b' hb
  by_cases ha : a = a'
  · subst ha
    rw [update_eq] at hb ⊢
    exact hb
  · rw [update_neq ha] at hb ⊢
    exact h hb

end PartialMap

--  This property is quite useful for reasoning about
--  languages with variable binding — e.g., the Simply Typed
--  Lambda Calculus, which we will see in *Type Systems*,
--  where maps are used to keep track of which program
--  variables are defined in a given scope.

--  ## Reflection

namespace Reflection

--  In this section, we will make use of some definitions
--  and theorems about natural numbers that we discussed and
--  proved in previous chapters; copy your solutions to
--  those problems here:

namespace Nat

def even (n : Nat) :=
  match n with
  | 0     => true
  | 1     => false
  | n + 2 => even n

theorem even_zero : even 0 = true := by rfl

theorem even_succ (n : Nat) :
    even (n + 1) = !(even n) := by
  sorry

def double (n : Nat) : Nat :=
  match n with
  | 0    => 0
  | n' + 1 => double n' + 2

theorem double_zero : double 0 = 0 := by rfl

theorem double_succ (n : Nat) : double (n + 1) = double n + 2 := by rfl

def Even x := ∃ n : Nat, x = Nat.double n

--  We've seen two different ways of expressing logical
--  claims in Lean: with booleans (of type `Bool`), and with
--  propositions (of type `Prop`).
--
--  Here are the key differences between `Bool` and `Prop`:

--  |                       | `Bool` | `Prop` |
--  | --------------------- | ------ | ------ |
--  | decidable?            |  yes   |   no   |
--  | useable with `match`? |  yes   |   no   |
--  | works with `rewrite`? |   no   |   yes  |

--  The crucial difference between the two worlds is
--  decidability. Every (closed) Lean expression of type
--  `Bool` can be simplified in a finite number of steps to
--  either `true` or `false` — i.e., there is a terminating
--  mechanical procedure for deciding whether or not it is
--  true.
--
--  This means that, for example, the type `Nat → Bool` is
--  inhabited only by functions that, given a `Nat`, always
--  yield either `true` or `false` in finite time; and this,
--  in turn, means (by a standard computability argument)
--  that there is no function in `Nat → Bool` that checks
--  whether a given number is the code of a terminating
--  Turing machine.
--
--  By contrast, the type `Prop` includes both decidable and
--  undecidable mathematical propositions; in particular,
--  the type `Nat → Prop` does contain functions
--  representing properties like "the nth Turing machine
--  halts." The second row in the table follows directly
--  from this essential difference. To evaluate a pattern
--  match (or conditional) on a boolean, we need to know
--  whether the scrutinee evaluates to `true` or `false`;
--  this only works for `Bool`, not `Prop`.
--
--  The third row highlights an important practical
--  difference: equality functions like `Nat.beq` that
--  return a boolean cannot be used directly to justify
--  rewriting with the rewrite tactic; propositional
--  equality is required for this. Since `Prop` includes
--  both decidable and undecidable properties, we have two
--  options when we want to formalize a property that
--  happens to be decidable: we can express it either as a
--  boolean computation or as a function into Prop.
--
--  As an example, we can write

example : even 42 := rfl

--  or that there exists some `k` such that `42 = double k`.

example : Even 42 := by exists 21

--  Of course, it would be deeply strange if these two
--  characterizations of evenness did not describe the same
--  set of natural numbers!
--
--  Fortunately, they do! To prove this, we first need two
--  helper lemmas.

theorem even_double (k : Nat) : even (double k) = true := by
  induction k with
  | zero =>
    rw [double_zero, even_zero]
  | succ n ih =>
    rw [double_succ, even_succ, even_succ, Bool.not_not]
    exact ih

--  ### Exercise (3 stars): even_double_exists ⭐⭐⭐

theorem even_double_exists (n : Nat) :
    ∃ (k : Nat), n = bif even n then double k else double k + 1 := by
  sorry

--  Now the main theorem:

theorem even_iff_Even {n : Nat} : even n = true ↔ Even n where
  mp h := by
    have ⟨k, hk⟩ := even_double_exists n
    rw [h, cond_true] at hk
    subst hk
    exists k
  mpr h := by
    obtain ⟨k, hk⟩ := h
    subst hk
    exact even_double k

end Nat

--  In view of this theorem, we can say that the boolean
--  computation `Nat.even n` is reflected in the truth of
--  the proposition `∃ (k : Nat), n = Nat.double k`.
--
--  Similarly, to state that two numbers n and m are equal,
--  we can say either
--
--  - that `n == m` returns `true`, or
--  - that `n = m`
--
--  Again, these two notions are equivalent:

example (n₁ n₂ : Nat) : n₁ == n₂ ↔ n₁ = n₂ := beq_iff_eq

--  So what should we do in situations where some claim
--  could be formalized as either a proposition or a boolean
--  computation? Which should we choose?
--
--  In general, both can be useful. Which we choose has to
--  do with the *computational* nature of Lean's core
--  language, which is designed so that every function it
--  expresses is total, and by default computable unless we
--  explicit indicate otherwise. As an example, consider
--  trying to write a function `α → α → Bool` checking for
--  equality on an arbitrary type:

--  Lean will complain here that it cannot find an instance
--  of `Decidable`. This typeclass

sf_recall
  class inductive Decidable (p : Prop) where
    /-- Proves that `p` is decidable by supplying a proof of `¬ p` -/
    | isFalse (h : Not p) : Decidable p
    /-- Proves that `p` is decidable by supplying a proof of `p` -/
    | isTrue (h : p) : Decidable p

--  is the way that we express in Lean that a given
--  proposition is decidable. This is the generalization of
--  our observation that `Nat.even_iff_Even` was reflecting
--  a proof between boolean and propositional equality. In
--  fact, we can use this theorem to directly construct a
--  `Decidable` instance.

instance (n : Nat) : Decidable (Nat.Even n) :=
  decidable_of_decidable_of_iff Nat.even_iff_Even

--  Now we are able to complete such proofs by computation
--  using the `decide` tactic:

example : Nat.Even 2 := by decide
example : Nat.Even 4 := by decide
example : Nat.Even 6 := by decide
example : Nat.Even 100 := by decide
example : ¬ Nat.Even 101 := by decide
example : ∀ n < 10, Nat.Even (2 * n) := by decide
example : ∀ n < 10, Nat.Even (2 * n) ∧ ¬ Nat.Even (2 * n + 1) := by decide

--  In general, Lean will try to use typeclass synthesis
--  with `Decidable` in order to determine when it is
--  appropriate to use `Prop` and `Bool` interchangeably.
--  For instance, while our example `eq` failed above while
--  trying to use propositional equality `=` in the
--  condition of an `if` statement, we are allowed to write

def nat_eq (m n : Nat) : Bool := if m = n then true else false

--  Why is this allowed? It is precisely because equality of
--  natural numbers is decidable, and Lean makes use of this
--  fact. If we print this definition with notation unset,
--  we would find that it is using `instDecidableEqNat`:

set_option pp.all true in
#print nat_eq

--  which proves that this equality is decidable.
--
--  This is only half the story however: while Lean's core
--  theory enables this computation, Lean is also often used
--  in applications where we don't care about computability,
--  such as pure mathematics. In particular, it is possible
--  to write a function for arbitrary equality:

sf_experiment
  open scoped Classical in
  noncomputable def eq {α : Type} (x y : α) := if x = y then true else false
  
  set_option pp.all true in
  #print eq

--  But we have indicated to Lean, using the `noncomputable`
--  keyword and `Classical` namespace, that we are *not*
--  interested in computation. What is happening in the
--  background is that this allows typeclass synthesis to
--  find the scoped instance `Classical.propDecidable`,
--  which makes use of the axiom of choice to provide a
--  proof that all propositions are *classically* decidable.
--  This sort of definition is suitable for use with proofs,
--  but is not allowed to be used in conjunction with
--  computational features of Lean such as the `decide`
--  tactic or the `#eval` command.

--  ## TODO

#check decidable_of_bool

example {p : Prop} (b : Bool) (h : b = true ↔ p) : Decidable p := by
  by_cases hb : b
  · apply isTrue
    simp [← h, hb]
  · apply isFalse
    simp [← h, hb]

#check decide_eq_false_iff_not
#check decide_eq_true_iff

example {α : Type} (x : α) [BEq α] [LawfulBEq α] (xs : List α)
    (neq : xs.filter (x == ·) ≠ []) : x ∈ xs := by
  sorry

end Reflection

-- Built on 2026-09-01 15:25 UTC

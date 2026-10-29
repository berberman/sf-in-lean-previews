import TS.Stlc
import TS.Smallstep
import LF.CustomTactics

import SFLCompat

--  # References: Typing Mutable References

--  Most real languages include *impure* features
--  ("computational effects")...
--  - mutable pointer structures
--  - non-local control constructs (exceptions,
--    continuations, etc.)
--  - inter-process synchronization and communication
--  - etc.
--
--  Goal for this chapter: Formalize pointers.

--  ## Definitions

--  In most real-world programming languages, the mechanisms
--  of *name binding* and *storage allocation* are
--  (intentionally) confused: every name refers to a mutable
--  piece of storage.
--
--  Conceptually, it's cleaner to separate the two:
--  - use the mechanisms we already have for name binding
--    (abstraction, let);
--  - introduce new operations for allocating, changing, and
--    looking up the contents of references (pointers).

--  ### Syntax

namespace STLCRef

open scoped MyGetElem

--  The basic operations on references are *allocation*,
--  *dereferencing*, and *assignment*.
--  - To allocate a reference, we use the `ref` operator,
--    providing an initial value for the new cell.
--
--    For example, `ref 5` creates a new cell containing the
--    value `5` and reduces to a reference to that cell.
--
--  - To read the current value of this cell, we use the
--    dereferencing operator `!`.
--
--    For example, `!(ref 5)` reduces to `5`.
--
--  - To change the value stored in a cell, we use the
--    assignment operator.
--
--    If `r` is a reference, `r := 7` will store the value
--    `7` in the cell referenced by `r`.

--  ### Types

--  If `τ` is a type, then `Ref τ` is the type of references
--  to cells holding values of type `τ`.

--  τ ::= Nat
--      | Unit
--      | τ → τ
--      | Ref τ

inductive Ty : Type :=
  | nat : Ty
  | unit : Ty
  | arrow : Ty → Ty → Ty
  | ref : Ty → Ty

--  ### Terms

--  Besides the usual variables, abstractions, applications,
--  terms related to natural numbers, and `unit`, we need
--  four more sorts of terms to handle mutable references:

--  t ::= ref t     (reference)
--      | ! t       (dereference)
--      | t := t    (assignment)
--      | l         (location)

inductive Tm  : Type :=
  -- STLC with numbers:
  | var    : String → Tm
  | app    : Tm → Tm → Tm
  | abs    : String → Ty → Tm → Tm
  | const  : Nat → Tm
  | succ    : Tm → Tm
  | pred    : Tm → Tm
  | mult    : Tm → Tm → Tm
  | ite0  : Tm → Tm → Tm → Tm
  -- New terms:
  | unit   : Tm
  | ref    : Tm → Tm
  | deref  : Tm → Tm
  | assign : Tm → Tm → Tm
  | loc    : Nat → Tm

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation)
scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:60 " * " stlcTm:61 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

scoped syntax:60 stlcTm:60 " := " stlcTm:61 : stlcTm
scoped syntax:60 "Ref " stlcTy:61 : stlcTy
scoped syntax:60 "ref " stlcTm:61 : stlcTm
scoped syntax:60 "loc " stlcTm:61 : stlcTm
scoped syntax:60 "!" stlcTm:61 : stlcTm
scoped syntax:55 stlcTm:56 " ; " stlcTm:55 : stlcTm

scoped syntax stlcCtx " / " term:max " ⊢ " stlcTm " ⦂ " stlcTy : stlcQuoted

abbrev Tm.tseq t₁ t₂ :=
  Tm.app (.abs "X" .unit t₂) t₁

namespace Elab

open StlcCommon
open Lean Meta Elab Term

def language : Language where
  tyType := ``Ty
  tmType := ``Tm
  arrowCtor := ``Ty.arrow
  varCtor := ``Tm.var
  appCtor := ``Tm.app
  absCtor := ``Tm.abs
  -- defined later
  subst := `STLCRef.subst
  hasType := `STLCRef.HasType

def extendedTyHandler : TyElabHandler :=
  fun recur k T => do
    match T with
    | `(stlcTy| Nat) =>
        return mkConst ``Ty.nat
    | `(stlcTy| Unit) =>
        return mkConst ``Ty.unit
    | `(stlcTy| Ref $τ:stlcTy) => do
        let τ ← recur τ
        return mkApp (mkConst ``Ty.ref) τ
    | _ => k T

def tyHandlers : TyElabHandler :=
  extendedTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy <| unsupportedTy language

def extendedTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| $n:num) => do
        return (mkApp (mkConst ``Tm.const) (mkNatLit n.getNat), free )

    | `(stlcTm| Nat) => do
        throwError "`Nat` is not a valid term."

    | `(stlcTm| succ $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.succ) t, free)

    | `(stlcTm| pred $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.pred) t, free)

    | `(stlcTm| $t₁:stlcTm * $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.mult) t₁ t₂, free)

    | `(stlcTm| if0 $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite0) c t e, free)

    | `(stlcTm| Unit) => do
        throwError "`Unit` is not a valid term."

    | `(stlcTm| unit) => do
        return (mkConst ``Tm.unit, free)

    | `(stlcTm| ref $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.ref) t, free)

    | `(stlcTm| !$t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.deref) t, free)

    | `(stlcTm| loc $n:num) => do
        return (mkApp (mkConst ``Tm.loc) (mkNatLit n.getNat), free )

    | `(stlcTm| $t₁:stlcTm := $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.assign) t₁ t₂, free)

    | `(stlcTm| $t₁:stlcTm ; $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.tseq) t₁ t₂, free)

    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  extendedTmHandler.orElse (commonTmHandler language elabTy)

partial def elabTm : TmElab :=
  tmHandlers elabTm unsupportedTm

def elabCtx : CtxElab := elabCtxCommon language elabTy

-- `HasType` takes the store typing as an extra first argument,
-- so we build typing judgments here instead of in `elabQuoted`.
def mkHasType (δ Γ t T : Expr) : TermElabM Expr := do
  let some hasType ← resolveId? (mkIdent language.hasType)
    | throwError "unknown declaration `{language.hasType}`"
  return mkApp4 hasType δ Γ t T

@[scoped term_elab StlcCommon.bracket]
def elabBracket : TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(<{ $Γ:stlcCtx / $δ:term ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
        let (Γ, scope) ← elabCtx Γ
        let (t, _) ← elabTm scope [] t
        let T ← elabTy T
        let δ ← elabTermEnsuringType δ (mkApp (mkConst ``List [levelZero]) (mkConst ``Ty))
        mkHasType δ Γ t T
    | `(<{ $_:stlcCtx ⊢ $_:stlcTm ⦂ $_:stlcTy }>) =>
        throwError "typing judgments need a store typing: write `Γ / δ ⊢ t ⦂ τ`"
    | `(<{ $q:stlcQuoted }>) =>
        elabQuoted language elabTy elabTm elabCtx q expectedType?
    | _ => throwUnsupportedSyntax

end Elab

open scoped Elab

namespace Delab

open StlcCommon Elab Delab
open Lean PrettyPrinter Delaborator

@[app_unexpander Ty.nat]
private def Ty.unexpandNat : Unexpander
  | stx => do
    let Nat := mkObjectIdentFrom stx "Nat"
    let T ← `(stlcTy| $Nat:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.unit]
private def Ty.unexpandUnit : Unexpander
  | stx => do
    let Unit := mkObjectIdentFrom stx "Unit"
    let T ← `(stlcTy| $Unit:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Ty.ref]
private def Ty.unexpandRef : Unexpander
  | `($_ $T) => do
      let T' := getTy T
      `(<{ Ref $T':stlcTy }>)
  | _ => throw ()

private def reservedNames : String → Bool
  | "Nat" | "Unit" | "succ" | "pred"
  | "if0" | "ref" | "loc" | "Ref"
  | "unit" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.const]
private def Tm.unexpandConst : Unexpander
  | `($_ $n:num) => `(<{ $n:num }>)
  | _ => throw ()

@[app_unexpander Tm.succ]
private def Tm.unexpandSucc : Unexpander
  | stx@`($_ $t) => do
      let succ := mkObjectIdentFrom stx "succ"
      let t' := getTm t
      `(<{ $succ:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.pred]
private def Tm.unexpandPred : Unexpander
  | stx@`($_ $t) => do
      let pred := mkObjectIdentFrom stx "pred"
      let t' := getTm t
      `(<{ $pred:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.mult]
private def Tm.unexpandMult : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm * $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.tseq]
private def Tm.unexpandTseq : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm ; $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.ite0]
private def Tm.unexpandIte0 : Unexpander
  | `($_ $c $t $e) => do
      let c' := getTm c
      let t' := getTm t
      let e' := getTm e
      `(<{ if0 $c':stlcTm then $t':stlcTm else $e':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.unit]
private def Tm.unexpandUnit : Unexpander
  | stx => do
      let unit := mkObjectIdentFrom stx "unit"
      let t ← `(stlcTm| $unit:ident)
      `(<{ $t:stlcTm }>)

@[app_unexpander Tm.assign]
private def Tm.unexpandAssign : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm := $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.ref]
private def Tm.unexpandRef : Unexpander
  | `($_ $t₁) => do
      let t₁' := getTm t₁
      `(<{ ref $t₁':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.deref]
private def Tm.unexpandDeref : Unexpander
  | `($_ $t₁) => do
      let t₁' := getTm t₁
      `(<{ !$t₁':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.loc]
private def Tm.unexpandLoc : Unexpander
  | `($_ $n:num) => `(<{ loc $n:num }>)
  | _ => throw ()

end Delab
--  END DETAILS

--  ### Typing (Preview)

--  Informally, the typing rules for allocation,
--  dereferencing, and assignment look roughly like this:
--
--            Γ ⊢ t₁ ⦂ τ₁
--      ---------------------  (ref)
--        Γ ⊢ ref t₁ ⦂ Ref τ₁
--
--            Γ ⊢ t₁ ⦂ Ref τ₁
--      ---------------------  (deref)
--           Γ ⊢ !t₁ ⦂ τ₁
--
--            Γ ⊢ t₁ ⦂ Ref τ₂
--            Γ ⊢ t₂ ⦂ τ₂
--      ---------------------  (assign)
--      Γ ⊢ t₁ := t₂ ⦂ Unit
--
--  The rule for locations will require a bit more
--  machinery, and this will motivate some changes to the
--  other rules; we'll come back to this later.

--  ### Values and Substitution

--  Besides abstractions, numbers, and the unit value, we
--  have one new type of value: locations.
--
--  A location is a concrete pointer value — think of it
--  like an address in memory. Locations should never be
--  written directly by programmers; they are used to keep
--  track of the intermediate states of programs involving
--  references. In particular, the result of a `ref`
--  expression is a location.

inductive Tm.IsValue : Tm → Prop :=
  | abs : forall x τ₂ t₁,
      IsValue <{λx : τ₂. t₁}>
  | nat : forall (n : Nat),
      IsValue (.const n)
  | unit :
      IsValue <{ unit }>
  | loc_ : forall (l : Nat),
      IsValue (.loc l)

attribute [StlcRefEval] Tm.IsValue.abs Tm.IsValue.nat Tm.IsValue.unit Tm.IsValue.loc_

--  Extending substitution to handle the new syntax of terms
--  is straightforward: substituting into a pointer leaves
--  it unchanged.

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- pure STLC
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ y : τ . [x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([x := s] t₁) ([x := s] t₂) }>
  -- numbers
  | .const _ =>
      t
  | .succ t₁ =>
      <{ succ ([x := s] t₁) }>
  | .pred t₁ =>
      <{ pred ([x := s] t₁) }>
  | .mult t₁ t₂ =>
      <{ ([x := s] t₁) * ([x := s] t₂) }>
  | .ite0 t₁ t₂ t₃ =>
      <{
        if0 [x := s] t₁
        then [x := s] t₂
        else [x := s] t₃
      }>
  -- unit
  | .unit => <{ unit }>
  -- references
  | .ref t₁ =>  <{ ref ([x := s] t₁) }>
  | .deref t₁ =>  <{ !([x := s] t₁) }>
  | .loc n => .loc n
  | .assign t₁ t₂ =>
      <{ ([x := s] t₁) := ([x := s] t₂) }>

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding)
open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst
--  END DETAILS

--  ## Pragmatics

--  ### Side Effects and Sequencing

--  We can write (for example)

--  R := succ (!R); !R

--  as an abbreviation for

--  (λX:Unit. !R) (r := succ(!R)).

/-- info: <{ R := succ (!R) ; !R }> : Tm -/
#guard_msgs in
#check <{R := succ (!R); !R}>

--  ### References and Aliasing

--  It is important to bear in mind the difference between
--  the *reference* that is bound to some variable `r` and
--  the *cell* in the store that is pointed to by this
--  reference.
--
--  If we make a copy of `r`, for example by binding its
--  value to another variable `s`, what gets copied is only
--  the reference, not the contents of the cell itself.
--
--  For example, after reducing
--
--      let R = ref 5 in
--      let S = R in
--      S := 82;
--      (!R)+1
--
--  the cell referenced by `R` will contain the value `82`,
--  while the result of the whole expression will be `83`.
--  The references `R` and `S` are said to be *aliases* for
--  the same cell.
--
--  The possibility of aliasing can make programs with
--  references quite tricky to reason about. For example,
--  the expression
--
--      R := 5; R := !S
--
--  assigns `5` to `R` and then immediately overwrites it
--  with `S`'s current value; this has exactly the same
--  effect as the single assignment
--
--      R := !S
--
--  *unless* we happen to do it in a context where `R` and
--  `S` are aliases for the same cell!
--
--      let R = ref 0 in
--      let S = R in
--      R := 5; R := !S

--  ### Shared State

--  Of course, aliasing is also a large part of what makes
--  references useful. In particular, it allows us to set up
--  "implicit communication channels" — shared state —
--  between different parts of a program. For example,
--  suppose we define a reference cell and two functions
--  that manipulate its contents:
--
--      let C = ref 0 in
--      let Incc = λ_:Unit. (C := succ (!C); !C) in
--      let Decc = λ_:Unit. (C := pred (!C); !C) in
--        ...
--
--  The `Unit`-abstractions ("thunks") are used here to
--  prevent reduction until later.

--  ### Objects

--  We can go a step further and write a *function* that
--  creates `C`, `Incc`, and `Decc`, packages `Incc` and
--  `Decc` together into a record, and returns this record:

--  Newcounter =
--    λ_:Unit.
--        let C = ref 0 in
--        let Incc = λ_:Unit. (C := succ (!C); !C) in
--        let Decc = λ_:Unit. (C := pred (!C); !C) in
--        {i=Incc, d=Decc}

--  Now, each time we call `Newcounter`, we get a new record
--  of functions that share access to the same storage cell
--  `C`. The caller of `Newcounter` can't get at this
--  storage cell directly, but can affect it indirectly by
--  calling the two functions. In other words, we've created
--  a simple form of *object*.

--  let C₁ = newcounter unit in
--  let C₂ = newcounter unit in
--  // we've allocated two separate storage cells now!
--  let R₁ = C₁.i unit in
--  let R₂ = C₂.i unit in
--  R₂  // yields 1, not 2!

--  ### References to Compound Types

--  A reference cell need not contain just a number: the
--  primitives we've defined above allow us to create
--  references to values of any type, including functions.
--  For example, we can use references to functions to give
--  a(n inefficient) implementation of arrays of numbers as
--  follows.
--
--  Write `NatArray` for the type `Ref (Nat→Nat)`.
--
--  To build a new array, we allocate a reference cell and
--  fill it with a function that, when given an index,
--  always returns `0`.
--
--      Newarray = λ_:Unit. ref (λN:Nat.0)
--
--  To look up an element of an array, we apply the function
--  to the desired index.
--
--      Lookup = λA:NatArray, λN:Nat. (!A) N
--
--  The interesting part of the encoding is the `Update`
--  function. It takes an array, an index, and a new value
--  to be stored at that index, and it does its job by
--  creating (and storing in the reference) a new function
--  that, when it is asked for the value at this very index,
--  returns the new value that was given to `Update`, while
--  on all other indices it passes the lookup to the
--  function that was previously stored in the reference.

--  Update = \A:NatArray, \M:Nat, \V:Nat,
--    let Oldf = !A in
--    A := (λN:Nat. if Equal M N then V else Oldf N);

--  References to values containing other references can
--  also be very useful, allowing us to define data
--  structures such as mutable lists and trees.

--  ### Null References

--  One more difference between our references and C-style
--  mutable variables: *null pointers*.
--  - In C, a pointer variable can contain either a valid
--    pointer into the heap or the special value `NULL`.
--  - A source of many errors and much tricky reasoning:
--    - (any pointer may potentially be "not there")
--    - but occasionally useful
--  - Nullable pointers are easy to implement using
--    references plus options (which can be built out of
--    disjoint sum types):
--
--      Option τ       =  Unit + τ
--      NullableRef τ  =  Ref (Option τ)

--  ### Garbage Collection

--  A last issue that we should mention before we move on
--  with formalizing references is storage *de*-allocation.
--  We have not provided any primitives for freeing
--  reference cells when they are no longer needed. Instead,
--  like many modern languages (including OCaml, Haskell,
--  Java, etc.), we rely on the run-time system to perform
--  *garbage collection*, automatically identifying and
--  reusing cells that can no longer be reached by the
--  program.
--
--  This is *not* just a question of taste in language
--  design: it is extremely difficult to achieve type safety
--  in the presence of an explicit deallocation operation.
--
--  One reason for this is the familiar *dangling reference*
--  problem: we allocate a cell holding a number, save a
--  reference to it in some data structure, use it for a
--  while, then deallocate it and allocate a new cell
--  holding a boolean, possibly reusing the same storage.
--  Now we can have two names for the same storage cell —
--  one with type `Ref Nat` and the other with type
--  `Ref Bool`.

--  ## Operational Semantics

--  ### Locations

--  A reference names a location in the *store* (a.k.a.
--  heap).
--
--  What is the store?
--  - Concretely: An array of 8-bit bytes, indexed by 32-bit
--    integers.
--  - More abstractly: a list or array of values
--  - Even more abstractly: a partial function from
--    locations to values.
--
--  We'll choose the middle way here: A store is a list of
--  values, and a location is a natural-number index into
--  this list.

--  ### Stores

--  A store is just a *list* of values. (This more concrete
--  representation will be more convenient for proofs than
--  the functional representation we used in Imp.) We will
--  use the Greek letter ρ to represent stores.

abbrev Store := List Tm

--  We use `ρ[n]` to retrieve the value of the reference
--  cell at location `n` in the store `ρ`. Note that we must
--  give a default value to `nth` in case we try looking up
--  an index which is too large. (In fact, we never actually
--  do this, but *proving* that we don't will require a bit
--  of work.)

open scoped MyGetElem
instance : MyGetElem Store Nat Tm where
  getElem ρ n := ρ.getD n <{unit}>

@[simp]
theorem Store_get_succ_tl (hd : Tm) (tl : Store) (n : Nat) :
  (hd :: tl)[n + 1] = tl[n] := by rfl

@[simp]
theorem Store_get_zero_hd (hd : Tm) (tl : Store) :
  (hd :: tl)[0] = hd := by rfl

--  To update the store, we use the `List.set` function,
--  which replaces the contents of a cell at a particular
--  index.
--
--      def List.set : (l : List α) → (n : Nat) → (a : α) → List α
--        | cons _ as, 0,          b => cons b as
--        | cons a as, Nat.succ n, b => cons a (set as n b)
--        | nil,       _,          _ => nil
--
--  As might be expected, we will also need some technical
--  lemmas; they are straightforward to prove.

theorem Store_get_set_eq (ρ : Store) (l : Nat) (x : Tm)
  (h : l < ρ.length) :
  (ρ.set l x)[l] = x := by
  induction ρ generalizing l with
  | nil => simp_all
  | cons hd tl ih => cases l <;> simp_all

theorem Store_get_set_neq (l₁ l₂ : Nat) (t : Tm) (ρ : Store) :
  l₁ ≠ l₂ ->
  (ρ.set l₂ t)[l₁] = ρ[l₁] := by
  induction ρ generalizing l₁ l₂ with
  | nil => simp
  | cons hd tl ih => cases l₁ <;> cases l₂ <;> simp_all

--  ### Reduction

--  First, we augment existing reduction rules with stores:
--
--                  v₂.IsValue
--      ------------------------------------ (appAbs)
--      (λx:τ₂. t₁) v₂ / ρ ⟶ [x:=v₂] t₁ / ρ
--
--                  t₁ / ρ ⟶ t₁' / ρ'
--      ---------------------------------    (app₁)
--               t₁ t₂ / ρ ⟶ t₁' t₂ / ρ'
--
--                 v₁.IsValue
--                  t₂ / ρ ⟶ t₂' / ρ'
--      ---------------------------------    (app₂)
--               v₁ t₂ / ρ ⟶ v₁ t₂' / ρ'
--
--  Now we can give the rules for the new constructs:
--
--      ------------------------------------    (refValue)
--           ref v / ρ ⟶ loc ρ.length / ρ,v
--
--              t₁ / ρ ⟶ t₁' / ρ'
--      ------------------------------          (ref)
--          ref t₁ / ρ ⟶ ref t₁' / ρ'
--
--            l < ρ.length
--      --------------------------              (derefLoc)
--        !(loc l) / ρ ⟶ ρ[l] / ρ
--
--              t₁ / ρ ⟶ t₁' / ρ'
--      ---------------------------             (deref)
--             !t₁ / ρ ⟶ !t₁' / ρ'
--
--                   l < ρ.length
--      --------------------------------------- (assign)
--      loc l := v / ρ ⟶ unit / List.set ρ l v
--
--              t₁ / ρ ⟶ t₁' / ρ'
--      --------------------------------        (assign₁)
--        t₁ := t₂ / ρ ⟶ t₁' := t₂ / ρ'
--
--              t₂ / ρ ⟶ t₂' / ρ'
--      --------------------------------        (assign₂)
--        v₁ := t₂ / ρ ⟶ v₁ := t₂' / ρ'

section
set_option hygiene false in
local notation:40
  t:71 " / " ρ:41 " ⟶ " t':71 " / " ρ':41 =>
  Step (t, ρ) (t', ρ')

inductive Step : Tm × Store → Tm × Store → Prop where
  -- pure STLC
  | appAbs {x : String} {τ₂ : Ty} {t₁ v₂ : Tm} {ρ : Store}
      (h : v₂.IsValue) :
      <{(λ x : τ₂ . t₁) v₂}> / ρ ⟶
      <{ [x := v₂] t₁ }> / ρ
  | app₁ {t₁ t₁' t₂ : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{t₁ t₂}> / ρ ⟶ <{t₁' t₂}> / ρ'
  | app₂ {v₁ t₂ t₂' : Tm} {ρ ρ' : Store}
      (h₁ : v₁.IsValue)
      (h₂ : t₂ / ρ ⟶ t₂' / ρ') :
      <{v₁ t₂}> / ρ ⟶ <{v₁ t₂'}> / ρ'
  -- numbers
  | succNat {n : Nat} {ρ : Store} :
      <{ succ ~(Tm.const n) }> / ρ ⟶ Tm.const (n + 1) / ρ
  | succ {t₁ t₁' : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ succ t₁ }> / ρ ⟶ <{ succ t₁' }> / ρ'
  | predConst {n : Nat} {ρ : Store} :
      <{ pred ~(Tm.const n) }> / ρ ⟶ Tm.const (n - 1) / ρ
  | pred {t₁ t₁' : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ pred t₁ }> / ρ ⟶ <{ pred t₁' }> / ρ'
  | multConst {n₁ n₂ : Nat} {ρ : Store} :
      <{ ~(Tm.const n₁) * ~(Tm.const n₂) }> / ρ ⟶
      Tm.const (n₁ * n₂) / ρ
  | mult₁ {t₁ t₁' t₂ : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ t₁ * t₂ }> / ρ ⟶ <{ t₁' * t₂ }> / ρ'
  | mult₂ {v₁ t₂ t₂' : Tm} {ρ ρ' : Store}
      (h₁ : v₁.IsValue)
      (h₂ : t₂ / ρ ⟶ t₂' / ρ') :
      <{ v₁ * t₂ }> / ρ ⟶ <{ v₁ * t₂' }> / ρ'
  | if0Step {t₁ t₁' t₂ t₃ : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ if0 t₁ then t₂ else t₃ }> / ρ ⟶
      <{ if0 t₁' then t₂ else t₃ }> / ρ'
  | if0Zero {t₂ t₃ : Tm} {ρ : Store} :
      <{ if0 0 then t₂ else t₃ }> / ρ ⟶ t₂ / ρ
  | if0Nonzero {n : Nat} {t₂ t₃ : Tm} {ρ : Store} :
      <{ if0 ~(Tm.const (n + 1)) then t₂ else t₃ }> / ρ ⟶
      t₃ / ρ
  -- references
  | refValue {v : Tm} {ρ : Store}
      (h : v.IsValue) :
      <{ ref v }> / ρ ⟶ Tm.loc ρ.length / ρ.concat v
  | ref_ {t₁ t₁' : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ ref t₁ }> / ρ ⟶ <{ ref t₁' }> / ρ'
  | derefLoc {l : Nat} {ρ : Store}
      (h : l < ρ.length) :
      <{ !~(Tm.loc l) }> / ρ ⟶ ρ[l] / ρ
  | deref {t₁ t₁' : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ !t₁ }> / ρ ⟶ <{ !t₁' }> / ρ'
  | assign {v : Tm} {l : Nat} {ρ : Store}
      (h₁ : v.IsValue)
      (h₂ : l < ρ.length) :
      <{ ~(Tm.loc l) := v }> / ρ ⟶ <{ unit }> / ρ.set l v
  | assign₁ {t₁ t₁' t₂ : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ t₁ := t₂ }> / ρ ⟶ <{ t₁' := t₂ }> / ρ'
  | assign₂ {v₁ t₂ t₂' : Tm} {ρ ρ' : Store}
      (h₁ : v₁.IsValue)
      (h₂ : t₂ / ρ ⟶ t₂' / ρ') :
      <{ v₁ := t₂ }> / ρ ⟶ <{ v₁ := t₂' }> / ρ'
end

scoped notation:40
  t:71 " / " ρ:41 " ⟶ " t':71 " / " ρ':41 =>
  Step (t, ρ) (t', ρ')
scoped notation:40
  t:71 " / " ρ:41 " ⟶* " t':71 " / " ρ':41 =>
  Multi Step (t, ρ) (t', ρ')

attribute [StlcRefEval] Step.appAbs Step.app₁ Step.app₂
    Step.succ Step.succNat Step.pred Step.predConst
    Step.multConst Step.mult₁ Step.mult₂
    Step.if0Step Step.if0Zero Step.if0Nonzero
    Step.refValue Step.ref_ Step.derefLoc Step.deref Step.assign
    Step.assign₁ Step.assign₂

--  ## Typing

--  The contexts assigning types to free variables are
--  exactly the same as for the STLC: partial maps from
--  identifiers to types.

abbrev Context := PartialMap String Ty

--  ### Store typings

--  Naturally, the key question is, "What is the type of a
--  location?"
--
--  As a first try, observe that the type of a location is
--  connected to the contents of the store `ρ`.
--
--       Γ ⊢ ρ[l] : τ₁
--      ------------------
--      Γ ⊢ loc l : Ref τ₁
--
--  But where does `ρ` come from?
--
--  We could try adding `ρ` to the judgment: `Γ; ρ ⊢ t : τ`,
--  which gives us this rule:
--
--       Γ; ρ ⊢ ρ[l] : τ₁
--      ---------------------
--      Γ; ρ ⊢ loc l : Ref τ₁
--
--  But that means the *whole* store `ρ`, including all
--  dynamically created values, is needed *during
--  typechecking*. This does not seem like something we
--  want.
--
--  Worse yet, it doesn't work at all for *cyclic* stores.
--
--  For example, what is the type of location `0` in the
--  following store?

--  λX:Nat. (!(loc 1)) X, λX:Nat. (!(loc 0)) X

--  Instead, we establish an *invariant* that the type of
--  value stored in a location never changes.
--
--  This *static* representation of the store contents is
--  called a *store typing*:

abbrev StoreTy := List Ty

--  Here we represent locations as indices into a *list* of
--  types so the type at index `i` is the type of the values
--  stored in cell `i`.

open scoped MyGetElem
instance : MyGetElem StoreTy Nat Ty where
  getElem δ n := δ.getD n <{Unit}>

@[simp]
theorem StoreTy_get_succ_tl (hd : Ty) (tl : StoreTy) (n : Nat) :
  (hd :: tl)[n + 1] = tl[n] := by rfl
@[simp]
theorem StoreTy_get_zero_hd (hd : Ty) (tl : StoreTy) :
  (hd :: tl)[0] = hd := by rfl

--  We can use the store typing `δ` to give a type to any
--  location `l` like this:
--
--           l < δ.length
--      -----------------------
--      Γ; δ ⊢ loc l : Ref δ[l]
--
--  That is, as long as `l` is a valid location, we can
--  compute the type of `l` just by looking it up in `δ`.
--  Typing is again a four-place relation, but it is
--  parameterized on a store *typing* rather than a concrete
--  store. The rest of the typing rules are analogously
--  augmented with store typings.

--  ### The Typing Relation

--           l < δ.length
--      -----------------------  (loc)
--      Γ; δ ⊢ loc l : Ref δ[l]
--
--          Γ; δ ⊢ t₁ : τ₁
--      ----------------------   (ref)
--      Γ; δ ⊢ ref t₁ : Ref τ₁
--
--        Γ; δ ⊢ t₁ : Ref τ₁
--        ------------------     (deref)
--        Γ; δ ⊢ !t₁ : τ₁
--
--        Γ; δ ⊢ t₁ : Ref τ₂
--          Γ; δ ⊢ t₂ : τ₂
--      ----------------------   (assign)
--      Γ; δ ⊢ t₁ := t₂ : Unit

inductive HasType (δ : StoreTy) : Context → Tm → Ty → Prop where
  -- pure STLC
  | var {Γ : Context} {x : String} {τ₁ : Ty}
      (h : Γ[x] = some τ₁) :
      <{ Γ / δ ⊢ ~(Tm.var x) ⦂ τ₁ }>
  | abs {Γ : Context} {x : String} {τ₁ τ₂ : Ty} {t₁ : Tm}
      (h : <{ x ↦ τ₂ ; Γ / δ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ / δ ⊢ λ x : τ₂ . t₁ ⦂ τ₂ → τ₁ }>
  | app {Γ : Context} {τ₁ τ₂ : Ty} {t₁ t₂ : Tm}
      (h₁ : <{ Γ / δ ⊢ t₁ ⦂ τ₂ → τ₁ }>)
      (h₂ : <{ Γ / δ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ / δ ⊢ t₁ t₂ ⦂ τ₁ }>
  -- numbers
  | const {Γ : Context} {n : Nat} :
      <{ Γ / δ ⊢ ~(Tm.const n) ⦂ Nat }>
  | succ {Γ : Context} {t₁ : Tm}
      (h : <{ Γ / δ ⊢ t₁ ⦂ Nat }>) :
      <{ Γ / δ ⊢ succ t₁ ⦂ Nat }>
  | pred {Γ : Context} {t₁ : Tm}
      (h : <{ Γ / δ ⊢ t₁ ⦂ Nat }>) :
      <{ Γ / δ ⊢ pred t₁ ⦂ Nat }>
  | mult {Γ : Context} {t₁ t₂ : Tm}
      (h₁ : <{ Γ / δ ⊢ t₁ ⦂ Nat }>)
      (h₂ : <{ Γ / δ ⊢ t₂ ⦂ Nat }>) :
      <{ Γ / δ ⊢ t₁ * t₂ ⦂ Nat }>
  | ite0 {Γ : Context} {t₁ t₂ t₃ : Tm} {τ : Ty}
      (h₁ : <{ Γ / δ ⊢ t₁ ⦂ Nat }>)
      (h₂ : <{ Γ / δ ⊢ t₂ ⦂ τ }>)
      (h₃ : <{ Γ / δ ⊢ t₃ ⦂ τ }>) :
      <{ Γ / δ ⊢ if0 t₁ then t₂ else t₃ ⦂ τ }>
  -- unit
  | unit {Γ : Context} :
      <{ Γ / δ ⊢ unit ⦂ Unit }>
  -- references
  | loc_ {Γ : Context} {l : Nat}
      (h : l < δ.length) :
      <{ Γ / δ ⊢ ~(Tm.loc l) ⦂ Ref ~(δ[l]) }>
  | ref_ {Γ : Context} {t₁ : Tm} {τ₁ : Ty}
      (h : <{ Γ / δ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ / δ ⊢ ref t₁ ⦂ Ref τ₁ }>
  | deref {Γ : Context} {t₁ : Tm} {τ₁ : Ty}
      (h : <{ Γ / δ ⊢ t₁ ⦂ Ref τ₁ }>) :
      <{ Γ / δ ⊢ !t₁ ⦂ τ₁ }>
  | assign {Γ : Context} {t₁ t₂ : Tm} {τ₂ : Ty}
      (h₁ : <{ Γ / δ ⊢ t₁ ⦂ Ref τ₂ }>)
      (h₂ : <{ Γ / δ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ / δ ⊢ t₁ := t₂ ⦂ Unit }>

attribute [StlcRefTyping] HasType.var HasType.abs HasType.app
    HasType.const HasType.succ HasType.pred HasType.mult
    HasType.ite0 HasType.unit
    HasType.loc_ HasType.ref_ HasType.deref HasType.assign

--  THE FOLLOWING DETAILS CAN BE SKIPPED (Notation encoding)
open Lean PrettyPrinter StlcCommon.Delab in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander
  | `($_ $δ $Γ $t $T) => do
      let Γ' ← unexpandCtx Γ
      `(<{ $Γ':stlcCtx / $δ ⊢ $(getTm t):stlcTm ⦂ $(getTy T):stlcTy }>)
  | _ => throw ()
--  END DETAILS

--  ## Properties

--  Standard theorems...
--  - Progress — pretty much same as always
--  - Preservation — needs to be stated more carefully!

--  ### Well-Typed Stores

--  The evaluation and typing relations take more parameters
--  now, so at a minimum we have to add these to the
--  statement of preservation...

sf_expect_failure_in
  theorem preservation_wrong (δ : StoreTy) (τ : Ty) (t t' : Tm) (ρ ρ' : Store) :
      <{ ∅ / δ ⊢ t ⦂ τ }> →
      t / ρ ⟶ t' / ρ' →
      <{ ∅ / δ ⊢ t' ⦂ τ }> := by

--  Obviously wrong: no relation between assumed store
--  typing and provided store!
--
--  We need a way of saying "this store satisfies the
--  assumptions of that store typing"...

def StoreWellTyped (δ:StoreTy) (ρ:Store) :=
  δ.length = ρ.length ∧
  (∀ (l : Nat), l < ρ.length → <{ ∅ / δ ⊢ ~(ρ[l]) ⦂ ~(δ[l]) }>)

--  Informally, we will write `δ ⊢ ρ` for
--  `StoreWellTyped δ ρ`.

scoped notation:40 δ:41 " ⊢ " ρ:41 => StoreWellTyped δ ρ

--  Intuitively, a store `ρ` is consistent with a store
--  typing `δ` if every value in the store has the type
--  predicted by the store typing. The only subtle point is
--  the fact that, when typing the values in the store, we
--  supply the very same store typing to the typing
--  relation. This allows us to type circular stores like
--  the one we saw above.
--
--  We can now state something closer to the desired
--  preservation property:

sf_expect_failure_in
  theorem preservation_less_wrong (δ : StoreTy) (τ : Ty) (t t' : Tm) (ρ ρ' : Store) :
    <{ ∅ / δ ⊢ t ⦂ τ }> →
    t / ρ ⟶ t' / ρ' →
    δ ⊢ ρ →
    <{ ∅ / δ ⊢ t' ⦂ τ }> := by

--  This works... for all but *one* of the reduction rules!
--  (Which?)
--
--  The `refValue` rule is the problem
--
--      -------------------------- (refValue)
--      ref v / ρ ⟶ loc |ρ| / ρ,v
--
--  It allocates a fresh location `l` and adds it to the
--  store, but the store typing `δ` doesn't know about `l`,
--  so `t'` won't be typeable under `δ`.
--
--  For example, the term `ref 5` is typeable in the ∅
--  context and ∅ store typing, but it steps to `loc 0`,
--  which is not typeable with an ∅ store typing.

--  ### Extending Store Typings

--  Intuition: Since the store can grow during reduction, we
--  need to let the store *typing* grow too...

inductive Extends : StoreTy → StoreTy → Prop where
  | nil (δ' : StoreTy) : Extends δ' []
  | cons (τ : Ty) {δ' δ : StoreTy} (h : Extends δ' δ) :
      Extends (τ::δ') (τ::δ)

attribute [StlcRefTyping] Extends.nil Extends.cons

--  For example, the store typing `[Nat]` with a single
--  location of type `Nat` extends the empty store typing.
--
--  We'll need a few technical lemmas about extended
--  contexts. First, looking up a type in an extended store
--  typing yields the same result as in the original:

theorem extends_lookup {l : Nat} {δ δ' : StoreTy}
  (h₁ : l < δ.length)
  (h₂ : Extends δ' δ) :
  δ'[l] = δ[l] := by

    induction δ generalizing l δ' with
    | nil => simp_all
    | cons hd tl ih =>
      cases δ' with
      | nil => inversion h₂
      | cons hd' tl' =>
        inversion h₂
        cases l with
        | zero => rfl
        | succ l =>
          simp only [StoreTy_get_succ_tl]; apply ih
          · simp_all
          · assumption

--  Next, if `δ'` extends `δ`, the length of `δ'` is at
--  least that of `δ`.

theorem length_extends {l : Nat} {δ δ' : StoreTy}
  (h₁ : l < δ.length)
  (h₂ : Extends δ' δ) :
  l < δ'.length := by
    induction h₂ generalizing l with
    | nil => simp_all
    | cons τ h ih =>
        simp only [List.length_cons]
        cases l with
        | zero => lia
        | succ l' =>
          apply Nat.succ_lt_succ; apply ih
          simp_all

--  Finally, `δ ++ δ'` extends `δ`, and `Extends` is
--  reflexive.

theorem extends_app (δ δ' : StoreTy) : Extends (δ ++ δ') δ := by
  induction δ generalizing δ' <;> apply_rules using StlcRefTyping

theorem extends_refl (δ : StoreTy) : Extends δ δ := by
  induction δ <;> apply_rules using StlcRefTyping

--  ### Preservation, Finally

--  We can now give the final, correct statement of the type
--  preservation property:

def preservation_theorem {δ : StoreTy} {t t' : Tm} {τ : Ty} {ρ ρ' : Store} :=
  (hTy : <{ ∅ / δ ⊢ t ⦂ τ }>) →
  (hStoreTy : δ ⊢ ρ) →
  (hEval : t / ρ ⟶ t' / ρ') →
    ∃ δ', Extends δ' δ ∧ (<{ ∅ / δ' ⊢ t' ⦂ τ }>) ∧ (δ' ⊢ ρ')

--  This gives us just what we need to "turn the crank" when
--  applying the theorem to multi-step reduction sequences.

--  #### Substitution Lemma

--  To prove preservation, we need to re-develop the rest of
--  the machinery that we saw for the pure STLC (plus a
--  couple of new things about store typings and
--  extension)...

theorem weakening {Γ Γ' : Context} {δ : StoreTy} {t : Tm} {τ: Ty}
    (hi : Γ ⊆ Γ')
    (ht : <{ Γ / δ ⊢ t ⦂ τ }>) :
     <{ Γ' / δ ⊢ t ⦂ τ }> := by
  induction ht generalizing Γ' with (apply_rules [PartialMap.update_subset] using StlcRefTyping)

theorem weakening_empty {Γ : Context} {δ : StoreTy} {t : Tm} {τ: Ty}
    (ht :<{ ∅ / δ ⊢ t ⦂ τ }>) :
    <{ Γ / δ ⊢ t ⦂ τ }> := by
  apply weakening _ ht
  intro _ _ h
  rw [PartialMap.getElem_empty] at h
  contradiction

theorem substitution_preserves_typing (Γ : Context) (δ : StoreTy) (x : String)
    (τ₁ : Ty) (t v : Tm) (τ : Ty)
    (ht : <{ x ↦ τ₁ ; Γ / δ⊢ t ⦂ τ }>)
    (hv : <{ ∅ / δ ⊢ v ⦂ τ₁ }>) :
    <{ Γ / δ ⊢ [x := v] t ⦂ τ }> := by
  induction t generalizing Γ τ with (
    rw [subst]; try (inversion ht; apply_rules using StlcRefTyping; done))
    | var y =>
        inversion ht with | _ h =>
        by_cases h₁ : x = y
        · subst h₁; simp at h; subst h;
          apply weakening_empty at hv
          simp; assumption
        · rw [PartialMap.update_neq] at h <;> simp_all
          apply_rules using StlcRefTyping
    | abs y _ _ ih =>
        inversion ht with | _ h =>
        by_cases h₁ : x = y
        · simp_all [PartialMap.update_shadow]; apply_rules using StlcRefTyping
        · rw [PartialMap.update_permute] at h
          · simp_all; apply_rules using StlcRefTyping
          · lia

--  #### Assignment Preserves Store Typing

--  Next, we must show that replacing the contents of a cell
--  in the store with a new value of appropriate type does
--  not change the overall type of the store. (This is
--  needed for the `assign` rule.)

theorem assign_pres_store_typing {δ : StoreTy} {ρ : Store} {l : Nat} {t : Tm}
  (hLen : l < ρ.length)
  (hStoreTy : δ ⊢ ρ)
  (hTy : <{ ∅ / δ ⊢ t ⦂ ~(δ[l]) }>) :
  δ ⊢ ρ.set l t := by
    have ⟨h₁, h₂⟩ := hStoreTy
    constructor
    · simp_all [List.length_set]
    · intro l' hLen'
      by_cases h₁ : l' = l
      · subst_vars
        rw [Store_get_set_eq] <;> assumption
      · rw [Store_get_set_neq] <;> try assumption
        apply h₂
        simp_all [List.length_set]

--  #### Weakening for Stores

--  Finally, we need a lemma on store typings, stating that,
--  if a store typing is extended with a new location, the
--  extended one still allows us to assign the same types to
--  the same terms as the original.

theorem store_weakening {Γ : Context} {δ δ' : StoreTy} {t : Tm} {τ : Ty}
  (hExt : Extends δ' δ)
  (hTy : <{ Γ / δ ⊢ t ⦂ τ }>) :
  <{ Γ / δ' ⊢ t ⦂ τ }> := by
    induction hTy with (try (apply_rules using StlcRefTyping; done))
    | loc_ h =>
        rw [←extends_lookup] <;> try assumption
        apply HasType.loc_
        apply length_extends <;> assumption

--  We can use the `store_weakening` lemma to prove that if
--  a store is well typed with respect to a store typing,
--  then the store extended with a new term `τ` will still
--  be well typed with respect to the store typing extended
--  with `τ`'s type.

theorem store_well_typed_app {δ : StoreTy} {ρ : Store} {t₁ : Tm} {τ₁ : Ty}
  (hStoreTy : δ ⊢ ρ)
  (hTy : <{ ∅ / δ ⊢ t₁ ⦂ τ₁ }>) :
  (δ.concat τ₁) ⊢ (ρ.concat t₁) := by
    have ⟨h₁, h₂⟩ := hStoreTy
    simp_all only [List.concat_eq_append]
    constructor
    · simp_all
    · simp_all only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      intro l hl
      inversion hl with
      | refl =>
          apply store_weakening <;> try assumption
          apply extends_app
          simp_all [MyGetElem.getElem]
      | step hl =>
          apply store_weakening <;> try assumption
          · apply extends_app
          · have hl' : l < ρ.length := by lia
            simp_all [MyGetElem.getElem, List.getElem?_append_left]

--  #### Preservation!

--  Now that we've got everything set up right, the proof of
--  preservation is actually quite straightforward:

theorem preservation {δ : StoreTy} {t t' : Tm} {τ : Ty} {ρ ρ' : Store}
  (hTy : <{ ∅ / δ ⊢ t ⦂ τ }>)
  (hStoreTy : δ ⊢ ρ)
  (hEval : t / ρ ⟶ t' / ρ') :
    ∃ δ', Extends δ' δ ∧ (<{ ∅ / δ' ⊢ t' ⦂ τ }>) ∧ (δ' ⊢ ρ') := by

    generalize heq : (∅ : Context) = Γ at hTy
    -- discharge the goals where `t` doesn't step
    induction hTy generalizing t' with (subst_vars; try (inversion hEval; done))
    | app h₁ h₂ ih₁ ih₂ =>
      inversion hEval with
      | appAbs =>
        inversion h₁ with | abs h =>
        exists δ; constructor
        apply extends_refl; constructor
        apply_rules [substitution_preserves_typing, extends_refl] using StlcRefTyping
        assumption
      | app₁ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₁ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
      | app₂ _ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₂ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | succ _ ih =>
      inversion hEval with
      | succNat =>
        exists δ; constructor
        apply extends_refl; constructor
        constructor
        assumption
      | succ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | pred _ ih =>
      inversion hEval with
      | predConst =>
        exists δ; constructor
        apply extends_refl; constructor
        constructor
        assumption
      | pred hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | mult h₁ h₂ ih₁ ih₂ =>
      inversion hEval with
      | multConst =>
        exists δ; constructor
        apply extends_refl; constructor
        constructor
        assumption
      | mult₁ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₁ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
      | mult₂ _ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₂ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | ite0 _ h₂ h₃ ih₁ _ _ =>
      inversion hEval with
      | if0Step hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₁ hs rfl
        exists δ'; constructor
        assumption; constructor
        constructor <;> solve_by_elim [store_weakening] using StlcRefTyping
        assumption
      | if0Zero =>
        exists δ; constructor
        apply extends_refl; constructor <;> assumption
      | if0Nonzero =>
        exists δ; constructor
        apply extends_refl; constructor <;> assumption
    | @ref_ _ _ τ₁ h ih =>
      inversion hEval with
      | refValue =>
        exists δ.concat τ₁; constructor
        · rw [List.concat_eq_append]; apply extends_app
        · constructor
          · have h : <{Ref τ₁}> = <{Ref ~((δ.concat τ₁)[ρ.length])}> := by
              simp_all [StoreWellTyped, MyGetElem.getElem]
            rw [h]
            constructor
            simp [StoreWellTyped] at hStoreTy ⊢; lia
          · apply store_well_typed_app <;> assumption
      | ref_ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | deref h ih =>
      inversion hEval with
      | derefLoc hl =>
        inversion h
        exists δ; constructor
        apply extends_refl; constructor
        have ⟨h₁, h₂⟩ := hStoreTy
        apply h₂ <;> assumption
        assumption
      | deref hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | assign h₁ h₂ ih₁ ih₂ =>
      inversion hEval with
      | assign _ hl =>
        inversion h₁
        exists δ; constructor
        apply extends_refl; constructor
        constructor
        apply assign_pres_store_typing <;> assumption
      | assign₁ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₁ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
      | assign₂ _ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₂ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption

--  ### Progress

--  As we've said, progress for this system is pretty easy
--  to prove; the proof is very similar to the proof of
--  progress for the STLC, with a few new cases for the new
--  syntactic constructs.

theorem progress (δ : StoreTy) (t : Tm) (τ : Ty) (ρ : Store)
  (hTy : <{ ∅ / δ ⊢ t ⦂ τ }>)
  (hStoreTy : δ ⊢ ρ) :
  (t.IsValue ∨ ∃ t' ρ', t / ρ ⟶ t' / ρ') := by
    have ⟨hLen, _⟩ := hStoreTy
    generalize heq : (∅ : Context) = Γ at hTy
    induction hTy with (subst_vars; first
      | contradiction
      -- discharge cases where `t` is obviously a value
      | try (left; constructor; done))
    | app h₁ _ ih₁ ih₂ =>
      right; cases ih₁ (by rfl) with
      -- t₁ is a value
      | inl hv₁ =>
        cases ih₂ (by rfl) with
        -- t₂ is a value
        | inl hv₂ =>
          cases hv₁ <;> try contradiction
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
        -- t₂ steps
        | inr hs₂ =>
          have ⟨t₂', ρ', hs₂⟩ := hs₂
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs₁ =>
        have ⟨t₁', ρ', hs₁⟩ := hs₁
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | succ h ih
    | pred h ih =>
      -- these two cases are the same
      right; cases ih (by rfl) with
      -- t₁ is a value
      | inl hv =>
        cases hv <;> try contradiction
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs =>
        have ⟨t₁', ρ', hs⟩ := hs
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | mult h₁ h₂ ih₁ ih₂ =>
      right; cases ih₁ (by rfl) with
      -- t₁ is a value
      | inl hv₁ =>
        cases ih₂ (by rfl) with
        -- t₂ is a value
        | inl hv₂ =>
          cases hv₁ <;> try contradiction
          cases hv₂ <;> try contradiction
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
        -- t₂ steps
        | inr hs₂ =>
          have ⟨t₂', ρ', hs₂⟩ := hs₂
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs₁ =>
        have ⟨t₁', ρ', hs₁⟩ := hs₁
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | ite0 h₁ _ _ ih₁ _ _ =>
      right; cases ih₁ (by rfl) with
      -- t₁ is a value
      | inl hv₁ =>
        cases hv₁ with (try contradiction)
        | nat n =>
          cases n <;> (apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval)
      -- t₁ steps
      | inr hs₁ =>
        have ⟨t₁', ρ', hs₁⟩ := hs₁
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | ref_ _ ih =>
      right; cases ih (by rfl) with
      -- t₁ is a value
      | inl hv =>
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs =>
        have ⟨t₁', ρ', hs⟩ := hs
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | deref h ih =>
      right; cases ih (by rfl) with
      -- t₁ is a value; its typing tells us `l < δ.length`
      | inl hv =>
        cases hv with (inversion h)
        | loc_ l => exists ρ[l], ρ; apply Step.derefLoc; lia
      -- t₁ steps
      | inr hs =>
        have ⟨t₁', ρ', hs⟩ := hs
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | @assign _ _ t₂ _ h₁ _ ih₁ ih₂ =>
      right; cases ih₁ (by rfl) with
      -- t₁ is a value
      | inl hv₁ =>
        cases ih₂ (by rfl) with
        -- t₂ is a value
        | inl hv₂ =>
          cases hv₁ with (inversion h₁)
          | loc_ l => exists <{ unit }>, ρ.set l t₂; apply Step.assign hv₂; lia
        -- t₂ steps
        | inr hs₂ =>
          have ⟨_, _, _⟩ := hs₂
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs₁ =>
        have ⟨t₁', ρ', hs₁⟩ := hs₁
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval

--  ## References and Nontermination

--  An important fact about the STLC is that it is
--  *normalizing* — that is, every well-typed term can be
--  reduced to a value in a finite number of steps.
--
--  What about STLC + references? Surprisingly, adding
--  references causes us to lose the normalization property:
--  there exist well-typed terms in the STLC + references
--  which can continue to reduce forever, without ever
--  reaching a normal form!
--
--  How can we construct such a term? The main idea is to
--  make a function which calls itself. We first make a
--  function which calls another function stored in a
--  reference cell; the trick is that we then smuggle in a
--  reference to itself!
--
--         (λR: Ref (Unit → Unit),
--              R := (λx:Unit,(!R) unit); (!R) unit)
--      (ref (λX:Unit.unit))

namespace RefsAndNontermination

def loop_fun := <{ λX : Unit. (!R) unit }>

def loop :=
  <{ (λR : Ref (Unit → Unit). (( R := (λX : Unit. (!R) unit) );  ( (! R) unit ) ))
     (ref (λX : Unit. unit)) }>

--  This term is well typed:

theorem loop_typeable : ∃ τ, <{ ∅ / [] ⊢ loop ⦂ τ }> := by
  apply Exists.intro
  apply_rules using StlcRefTyping

--  To show formally that the term diverges, we first define
--  the `step_closure` of the single-step reduction
--  relation, written `⟶+`. This is just like the reflexive
--  step closure of single-step reduction (which we're been
--  writing `⟶*`), except that it is not reflexive:
--  `t ⟶+ t'` means that `τ` can reach `t'` by *one or more*
--  steps of reduction.

inductive StepClosure {X:Type} (R: Relation X) : X → X → Prop :=
  | one {x y : X} (h₁ : R x y) : StepClosure R x y
  | step {x y z : X} (h₁ : R x y) (h₂ : StepClosure R y z) : StepClosure R x z

scoped notation:40
  t:71 " / " ρ:41 " ⟶+ " t':71 " / " ρ':41 =>
  StepClosure Step (t, ρ) (t', ρ')

--  Now, we can show that the expression `loop` reduces to
--  the expression `!(loc 0) unit` and the size-one store
--  `[R:=(loc 0)] loop_fun`.
--
--  As a convenience, we introduce a slight variant of the
--  `normalize` tactic, called `reduce`, which tries solving
--  the goal with `Multi.refl` at each step, instead of
--  waiting until the goal can't be reduced any more. Of
--  course, the whole point is that `loop` doesn't
--  normalize, so the old `normalize` tactic would just go
--  into an infinite loop reducing it forever!

syntax "reduce" " using " ident,+ : tactic

macro_rules
  | `(tactic| reduce using $xs,*) =>
    `(tactic|
      repeat
        (apply Multi.step
         · solve_by_elim (maxDepth := 15) (constructor := false) [Nat.le.refl, Nat.le.step] using $xs,*
         try apply Multi.refl))

--  Next, we use `reduce` to show that `loop` steps to
--  `!(loc 0) unit`, starting from the ∅ store.

theorem loop_steps_to_loop_fun :
  loop / [] ⟶*  <{ (! (loc 0)) unit }> / [<{ [R := loc 0] loop_fun }>] := by
    reduce using StlcRefEval

--  Finally, we show that the latter expression reduces in
--  two steps to itself!

theorem loop_fun_step_self :
  <{ (! (loc 0)) unit }> / [<{ [R := loc 0] loop_fun }>] ⟶+
  <{ (! (loc 0)) unit }> / [<{ [R := loc 0] loop_fun }>] := by
    apply StepClosure.step; solve_by_elim using StlcRefEval
    apply StepClosure.one; solve_by_elim using StlcRefEval

end RefsAndNontermination

end STLCRef

-- Source revision: b6f36ae, committed 2026-10-28 17:05 UTC

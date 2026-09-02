import LF.Logic
import LF.CustomTactics

import SFLCompat

--  # IndProp: Inductively Defined Propositions

--  Note to developers:
--      `HIDE: BCP 25: After teaching the chapter this semester, I feel
--      that (a) the Ev example, while arguably suboptimal, actually works
--      acceptably well. (I just wish that the n in ``ev_succ_succ` n H` was not
--      two smaller than the n that is being shown to be even — that's
--      always awkward.  Wonder if there is some clever way around that...)
--
--      However, (b) the chapter is very long, and quite a few of the
--      exercises are hard, especially if you do as I did this year and
--      require the advanced exercises for everybody (on the assumption
--      that they could get plenty of help from LLMs, etc.).  I think it
--      really needs to be at least significantly trimmed, if not split up.`
--
--      `HIDE: MRC 3/22: I offer a few remarks. I'm putting them here, above
--      the BCP'21 comment, not to say that they are in any way more
--      important; rather, just to preserve some chronological legibility.
--
--      - This chapter is an outlier in length. It now has the maximum line
--        length (in the FULL version) of any chapter in LF, at about 2300
--        LoC. That's a z-score of about 1.75 for the "blue arrow" chapters
--        in the dependency diagram.
--
--      - This chapter has 39 exercises, of which 25 (!) are optional.
--
--      - The running example of evenness is known to be uncompelling
--        because it is representable without inductively-defined
--        propositions. There do exist compelling examples:
--
--        + Functions like `factorial` whose "natural" definitions are not
--          structurally recursive. [Coq'Art 8.4]  [BCP 25: FWIW, I don't
--          find the "natural" definition of factorial suitable for present
--          purposes: the reasons it is better and more natural than a
--          simple fixpoint seem rather subtle.]
--
--        + Partial functions.
--
--        + Relations (that are not strictly functions).
--
--      I have a couple of personal opinions based on those observations:
--
--      - I favor BCP'21's "path 1" of de-emphasizing (to the extent
--        perhaps of eliminating) evenness.
--
--      - I favor re-factoring this chapter into two files, with a main
--        (blue) path that covers the essentials without cluttering
--        optional exercises throughout the file.`
--
--      HIDE: BCP '21: This chapter has been the subject of a lot of
--      discussion over the past couple of years, with lots of people
--      expressing dissatisfaction with the use of evenness as a main
--      example. In this revision, I have attempted a compromise: keeping
--      evenness as the running example (because, aside from the
--      artificiality of the example, it is pretty well polished) but
--      preceding it with short discussions of several better-motivated
--      examples.
--
--      I'm not yet convinced that this goes far enough, though (I was not
--      satisfied with my lecture on this part of the chapter, even after
--      adding these examples, though I did do some further streamlining
--      afterward and there are some further opportunities for streamlining
--      — perhaps enough to make the present treatment palatible). I see
--      three possible paths forward:
--
--      - 1. Choose a better example and simply replace all the even stuff.
--           (But which one is better? I don't think we've found it yet.)
--
--      - 2. Mix and match ─ use different examples from the top of the
--           chapter to make different points.
--
--      - 3. Leave the examples as-is but streamline as much as possible so
--           we don't get stuck in them.
--
--      Here, for reference, is the whole discussion from before:
--
--      -----------------
--
--      CH: In my Lyon course it became obvious to pretty much everyone
--      that the inductive definition of evenness that this chapter uses
--      intensiviely is so silly and artificial that it makes understanding
--      very hard for most students. There's zero need to define evenness
--      inductively, when `∃ k, n = 2*k` does the job fine, so inductive
--      propositions seem to students not something useful, but just
--      self-inflicted pain. All the inductive propositions, up to
--      subsequences and the matching on Regular Expressions at the end,
--      have this useless self-inflicted pain flavour. So I returned to
--      this the following morning and showed to the students how to define
--      reflexive-transitive closure as an inductive relation, and
--      afterwards the were able to follow much better. The code I quickly
--      hacked up for this is at:
--      https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/Multi.v
--
--      BCP: Yes, this chapter needs a revamp! For the moment I am going to
--      just add a couple of sentences to the opening sequence below, to
--      warn students about this potential confusion. Moving forward, I
--      wonder whether something like ordered binary trees would be a
--      simple enough running example.
--
--      BCP 20: I remain puzzled by what is the really right example for
--      this chapter. Ordered trees (and sorted lists) don't feel quite
--      right because students might think we should define them with
--      Fixpoint, not inductive. APT 21: Ordered trees are also
--      surprisingly complex to describe (see VFA/SearchTree.v). Maybe
--      Permutations would be be a good choice? The only problem is
--      convincing students that the standard Lean inductive definition is
--      actually correct (see VFA/Perm.v)!
--
--      We should also think about how to make the material flow better
--      between this chapter and ProofObjects. When lecturing about this
--      one I ended up introducing a lot of the concepts from that one.
--
--      --------
--
--      LATER: BCP 19: After lecturing on the first part of this chapter,
--      I'm afraid I have to agree that the Ev / even / evenb stuff is a
--      total mess. Besides the "why are there so many definitions of
--      evenness?" problem, evenness is just not a very natural inductively
--      defined proposition as a first example, because we already have so
--      many intuitions about what evenness is, and they clash with the new
--      definition.
--
--      So what to do?
--
--      An early version of this chapter, years ago, used a completely
--      artificial inductively defined property of numbers (0 is beautiful,
--      twice a beautiful number is beautiful, etc.). We could consider
--      going back to that. Or perhaps there is a more natural example,
--      either involving numbers or perhaps using some other inductive
--      structure like lists or binary trees. Not sure what's best.
--
--      A related issue is that later chapters (ProofObjects,
--      IndPrinciples) also rely heavily on this example. Sigh.
--
--      BCP 20: Tried to sort this out a bit better by renaming the
--      propositional definition from `Ev` to `eveni`, for symmetry with
--      `evenb`, and renaming the definition that says "a number is even if
--      it is twice something" to `evend`. What do people think of this?
--
--      BCP 20 update: In parallel, APT tried to sort it out a different
--      way; his is more consistent with the standard library, so let's try
--      to go with that one consistently...

--  Note to developers (before next release):
--      This chapter needs more (and better!) quizzes

--  ## Inductively Defined Propositions

--  In the Logic chapter, we looked at several ways of writing
--  propositions, including conjunction, disjunction, and existential
--  quantification.
--
--  In this chapter, we bring yet another new tool into the mix:
--  *inductively defined propositions*.
--
--  To begin, some examples...

--  ### Example: The Collatz Conjecture

--  The *Collatz Conjecture* is a famous open problem in number theory.
--
--  Its statement is quite simple. First, we define a function `csf` on
--  numbers, as follows (where `csf` stands for "Collatz step function"):

def div2 (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | 1      => 0
  | n' + 2 => div2 n' + 1

def csf (n : Nat) : Nat :=
  bif n.even then div2 n
  else (3 * n) + 1

--  Next, we look at what happens when we repeatedly apply `csf` to some
--  given starting number. For example, `csf 12` is `6`, and `csf 6` is
--  `3`, so by repeatedly applying `csf` we get the sequence
--  `12, 6, 3, 10, 5, 16, 8, 4, 2, 1`.
--
--  Similarly, if we start with `19`, we get the longer sequence
--  `19,
--  58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
--  4, 2, 1`.
--
--  Both of these sequences eventually reach `1`. The question posed by
--  Collatz was: Is the sequence starting from *any* positive natural
--  number guaranteed to reach `1` eventually?
--
--  To formalize this question in Lean, we might try to define a recursive
--  *function* that calculates the total number of steps that it takes for
--  such a sequence to reach `1`. You can write this definition in a
--  standard programming language, but it is rejected by Lean's termination
--  checker, since the argument to the recursive call, `csf n`, is not
--  "obviously smaller" than `n`.

sf_expect_failure_in
  def reaches1In (n : Nat) : Nat :=
    bif n == 1 then 0
    else 1 + reaches1In (csf n)

--  Output:
--    fail to show termination for
--      reaches1In
--    with errors
--    failed to infer structural recursion:
--    Cannot use parameter n:
--      failed to eliminate recursive application
--        reaches1In (csf n)
--
--
--    failed to prove termination, possible solutions:
--      - Use `have`-expressions to prove the remaining goals
--      - Use `termination_by` to specify a different well-founded relation
--      - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
--    n : Nat
--    ⊢ csf n < n

--  Indeed, this isn't just a pointless limitation: functions in Lean are
--  required to be total, to ensure logical consistency.
--
--  Moreover, we can't fix it by devising a more clever termination
--  checker: deciding whether this particular function is total would be
--  equivalent to settling the Collatz conjecture!
--
--  Another idea could be to express the concept "eventually reaches `1` in
--  the Collatz sequence" as a *recursively defined property* of numbers
--  `CollatzHoldsFor : Nat → Prop`. This is also rejected by the
--  termination checker. In principle, we could convince Lean that `div2 n`
--  is smaller than `n` by supplying an appropriate proof. However, we
--  still can't convince it that `(3 * n) + 1` is smaller than `n`!

sf_expect_failure_in
  def CollatzHoldsFor (n : Nat) : Prop :=
    match n with
    | 0 => False
    | 1 => True
    | _ => bif n.even then CollatzHoldsFor (div2 n)
                     else CollatzHoldsFor ((3 * n) + 1)

--  Output:
--    fail to show termination for
--      CollatzHoldsFor
--    with errors
--    failed to infer structural recursion:
--    Cannot use parameter n:
--      failed to eliminate recursive application
--        CollatzHoldsFor (div2 n)
--
--
--    failed to prove termination, possible solutions:
--      - Use `have`-expressions to prove the remaining goals
--      - Use `termination_by` to specify a different well-founded relation
--      - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
--    n x✝ : Nat
--    ⊢ div2 n < x✝

--  Fortunately, there is another way to do it: We can express the concept
--  "reaches `1` eventually in the Collatz sequence" as an *inductively
--  defined property* of numbers. Intuitively, this property is defined by
--  a set of rules:
--
--                    ─────────────────── (chf_one)
--                     CollatzHoldsFor 1
--
--      even n = true     CollatzHoldsFor (div2 n)
--      ─────────────────────────────────────────── (chf_even)
--                     CollatzHoldsFor n
--
--      even n = false    CollatzHoldsFor ((3 * n) + 1)
--      ─────────────────────────────────────────────── (chf_odd)
--                     CollatzHoldsFor n
--
--  So there are three ways to prove that a number `n` eventually reaches
--  `1` in the Collatz sequence:
--
--  - `n` is `1`;
--  - `n` is even and `div2 n` eventually reaches `1`;
--  - `n` is odd and `(3 * n) + 1` eventually reaches `1`.
--
--  We can prove that a number reaches `1` by constructing a (finite)
--  derivation using these rules. For instance, here is the derivation
--  proving that `12` reaches `1` (where we leave out the evenness/oddness
--  premises):
--
--      ─────────────────────── (chf_one)
--        CollatzHoldsFor 1
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 2
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 4
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 8
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 16
--      ─────────────────────── (chf_odd)
--        CollatzHoldsFor 5
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 10
--      ─────────────────────── (chf_odd)
--        CollatzHoldsFor 3
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 6
--      ─────────────────────── (chf_even)
--        CollatzHoldsFor 12
--
--  Formally in Lean, the `CollatzHoldsFor` property is *inductively
--  defined*:

inductive CollatzHoldsFor : Nat → Prop where
  | chf_one  : CollatzHoldsFor 1
  | chf_even {n : Nat} (h₁ : n.even = true)
    (h₂ : CollatzHoldsFor (div2 n)) : CollatzHoldsFor n
  | chf_odd  {n : Nat} (h₁ : n.even = false)
    (h₂ : CollatzHoldsFor ((3 * n) + 1)) : CollatzHoldsFor n

--  What we've done here is to use Lean's `inductive` definition mechanism
--  to characterize the property "Collatz holds for..." by stating three
--  different ways in which it can hold: (1) Collatz holds for `1`, (2) if
--  Collatz holds for `div2 n` and `n` is even then Collatz holds for `n`,
--  and (3) if Collatz holds for `(3 * n) + 1` and `n` is odd then Collatz
--  holds for `n`. This Lean definition directly corresponds to the three
--  rules we wrote informally above.

--  For particular numbers, we can now prove that the Collatz sequence
--  reaches `1` (we'll look more closely at how it works a bit later in the
--  chapter). Each step applies a rule and discharges the boolean evenness
--  premise by `rfl`; the recursive premise is then reduced by the kernel
--  from `CollatzHoldsFor (div2 12)` to `CollatzHoldsFor 6`, etc.

example : CollatzHoldsFor 12 := by
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_odd;   rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_odd;   rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  exact CollatzHoldsFor.chf_one

--  The Collatz conjecture then states that the sequence beginning from
--  *any* positive number reaches `1`:

def Collatz := ∀ n, n ≠ 0 → CollatzHoldsFor n

--  If you succeed in proving this conjecture, you've got a bright future
--  as a number theorist! But don't spend too long on it ─ it's been open
--  since 1937.

--  Note to developers (Chris Henson @chenson2018):
--      We may want to add an exercise later proving false if one assumes
--      Collatz' conjecture without the `n ≠ 0` assumption. We had that
--      mistake in the script for years and no one noticed, wow!
--
--      `theorem Collatz0' {n} (h₀ : n = 0) : ¬ CollatzHoldsFor n := by
--        intro h; induction h
--        case chf_one => contradiction
--        case chf_even ih => apply ih; rw [h₀]; dsimp [div2]
--        case chf_odd h _ _ => rw [h₀] at h; dsimp [Nat.even] at h; contradiction
--
--      theorem Collatz0 : ¬ (∀ n, CollatzHoldsFor n) := by
--        intro h; apply Collatz0'; rfl; apply h`

--  ### Example: Binary Relation for Comparing Numbers

--  A binary *relation* on a set `α` has Lean type `α → α → Prop`. This is
--  a family of propositions parameterized by two elements of `α` ─ i.e., a
--  proposition about pairs of elements of `α`.
--
--  For example, one familiar binary relation on `Nat` is
--  `Le : Nat → Nat → Prop`, the less-than-or-equal-to relation, which can
--  be inductively defined by the following two rules:
--
--        ─────── (le_refl)
--        Le n n
--
--        Le n m
--      ──────────── (le_step)
--      Le n (m + 1)

--  These rules say that there are two ways to show that a number is less
--  than or equal to another: either observe that they are the same number,
--  or, if the second has the form `m + 1`, give evidence that the first is
--  less than or equal to `m`.

namespace LePlayground

inductive Le : Nat → Nat → Prop where
  | refl {n : Nat}                : Le n n
  | step {n m : Nat} (h : Le n m) : Le n (m + 1)

scoped infix:50 (priority := high) " ≤ " => Le

--  This definition is a bit simpler and more elegant than the Boolean
--  function `Nat.ble` we defined in Basics. As usual, `Le` and `Nat.ble`
--  are equivalent, and there is an exercise about that later.

example : 3 ≤ 5 := by
  apply Le.step; apply Le.step; exact Le.refl

end LePlayground

--  ### Example: Transitive Closure

--  Another example: The *transitive closure* of a relation `R` is the
--  smallest relation that contains `R` and that is transitive. This can be
--  defined by the following two rules:
--
--                    R x y
--               ─────────────── (t_step)
--               ClosTrans R x y
--
--      ClosTrans R x y    ClosTrans R y z
--      ──────────────────────────────────── (t_trans)
--               ClosTrans R x z
--
--  In Lean this looks as follows:

inductive ClosTrans {α : Type} (R : α → α → Prop) : α → α → Prop where
  | t_step {x y : α} (h : R x y) : ClosTrans R x y
  | t_trans {x y z : α}
    (h₁ : ClosTrans R x y)
    (h₂ : ClosTrans R y z) :
    ClosTrans R x z

--  For example, suppose we define a "parent of" relation on a group of
--  people...

inductive Person : Type where
  | sage
  | cleo
  | ridley
  | moss

inductive ParentOf : Person → Person → Prop where
  | po_SC : ParentOf .sage .cleo
  | po_SR : ParentOf .sage .ridley
  | po_CM : ParentOf .cleo .moss

--  In this example, `sage` is a parent of both `cleo` and `ridley`; and
--  `cleo` is a parent of `moss`.

--  The `ParentOf` relation is not transitive, but we can define an
--  "ancestor of" relation as its transitive closure:

def AncestorOf : Person → Person → Prop := ClosTrans ParentOf

--  Here is a derivation showing that `sage` is an ancestor of `moss`:
--
--       ——————————————————— (po_SC)     ——————————————————— (po_CM)
--       ParentOf .sage .cleo            ParentOf .cleo .moss
--      ————————————————————— (t_step)  ————————————————————— (t_step)
--      AncestorOf .sage .cleo          AncestorOf .cleo .moss
--      ———————————————————————————————————————————————————— (t_trans)
--                      AncestorOf .sage .moss

example : AncestorOf .sage .moss := by
  apply ClosTrans.t_trans
  . apply ClosTrans.t_step; apply ParentOf.po_SC
  . apply ClosTrans.t_step; apply ParentOf.po_CM

--  Note to developers:
--      HIDE: CH: A simple exercise could be nice here?

--  Computing the transitive closure can be undecidable even for a relation
--  R that is decidable (e.g., the `CMS` relation below), so in general we
--  can't expect to define transitive closure as a boolean function.
--  Fortunately, Lean allows us to define transitive closure as an
--  inductive relation.
--
--  The transitive closure of a binary relation cannot, in general, be
--  expressed in first-order logic. The logic of Lean is, however, much
--  more powerful, and can easily define such inductive relations.

--  ### Example: Reflexive and Transitive Closure

--  As another example, the *reflexive and transitive closure* of a
--  relation `R` is the smallest relation that contains `R` and that is
--  reflexive and transitive. This can be defined by the following three
--  rules (where we added a reflexivity rule to `ClosTrans`):
--
--                         R x y
--               ——————————————————————— (rt_step)
--                 ClosReflTrans R x y
--
--               ——————————————————————— (rt_refl)
--                 ClosReflTrans R x x
--
--         ClosReflTrans R x y    ClosReflTrans R y z
--      —————————————————————————————————————————————— (rt_trans)
--                 ClosReflTrans R x z

inductive ClosReflTrans {α : Type} (R : α → α → Prop) : α → α → Prop where
  | rt_step {x y : α} (h : R x y) : ClosReflTrans R x y
  | rt_refl {x : α} : ClosReflTrans R x x
  | rt_trans {x y z : α}
    (h₁ : ClosReflTrans R x y)
    (h₂ : ClosReflTrans R y z) :
    ClosReflTrans R x z

--  For instance, this enables an equivalent definition of the Collatz
--  conjecture. First we define a binary relation corresponding to the
--  "Collatz step function" `csf`:

def CS (n m : Nat) : Prop := csf n = m

--  This Collatz step relation can be used in conjunction with the
--  reflexive and transitive closure operation to define a *Collatz
--  multi-step* (`CMS`) relation, expressing that a number `n` reaches
--  another number `m` in zero or more Collatz steps:

def CMS (n m : Nat) : Prop := ClosReflTrans CS n m
def Collatz' : Prop := ∀ (n : Nat), n ≠ 0 → CMS n 1

--  This `CMS` relation defined in terms of `ClosReflTrans` allows for more
--  interesting derivations than the linear ones of the directly-defined
--  `CollatzHoldsFor` relation:
--
--      csf 16 = 8            csf 8 = 4            csf 4 = 2            csf 2 = 1
--      —————————— (rt_step)  ————————— (rt_step)  ————————— (rt_step)  ————————— (rt_step)
--      CMS 16 8              CMS 8 4              CMS 4 2              CMS 2 1
--      ——————————————————————————————— (rt_trans) —————————————————————————————— (rt_trans)
--                 CMS 16 4                                    CMS 4 1
--                 ——————————————————————————————————————————————————— (rt_trans)
--                                       CMS 16 1

--  Note to developers:
--      HIDE: CH: Would it be helpful to add an exercise later proving CMS
--      equivalent to CollatzHoldsFor?

--  ### Exercise (1 star): clos_refl_trans_sym (Optional, Manually graded) ⭐

--  How would you modify the `ClosReflTrans` definition above so as to
--  define the reflexive, symmetric, and transitive closure?

inductive ClosReflTransSym {α : Type} (R : α → α → Prop) : α → α → Prop where
  | srt_refl {x : α} : ClosReflTransSym R x x
  | srt_step {x y : α} (h : R x y) : ClosReflTransSym R x y
  | srt_sym {x y : α}
    (h : ClosReflTransSym R y x) :
    ClosReflTransSym R x y
  | srt_trans {x y z : α}
    (h₁ : ClosReflTransSym R x y)
    (h₂ : ClosReflTransSym R y z) :
    ClosReflTransSym R x z

--  ### Example: Permutations

--  The familiar mathematical concept of *permutation* also has an elegant
--  formulation as an inductive relation. For simplicity, let's focus on
--  permutations of lists with exactly three elements.
--
--  We can define such permutations by the following rules:
--
--         ───────────────────────── (perm3_swap12)
--         Perm3 [a, b, c] [b, a, c]
--
--         ───────────────────────── (perm3_swap23)
--         Perm3 [a, b, c] [a, c, b]
--
--      Perm3 l₁ l₂       Perm3 l₂ l₃
--      ───────────────────────────── (perm3_trans)
--               Perm3 l₁ l₃
--
--  For instance we can derive `Perm3 [1, 2, 3] [3, 2, 1]` as follows:
--
--      ───────────────────────── (perm3_swap12)   ───────────────────────── (perm3_swap23)
--      Perm3 [1, 2, 3] [2, 1, 3]                  Perm3 [2, 1, 3] [2, 3, 1]
--      ──────────────────────────────────────────────────────────────────── (perm3_trans)   ───────────────────────── (perm3_swap12)
--      Perm3 [1, 2, 3] [2, 3, 1]                                                            Perm3 [2, 3, 1] [3, 2, 1]
--      ────────────────────────────────────────────────────────────────────────────────────────────────────────────── (perm3_trans)
--      Perm3 [1, 2, 3] [3, 2, 1]

--  This definition says:
--
--  - If `l₂` can be obtained from `l₁` by swapping the first and second
--    elements, then `l₂` is a permutation of `l₁`.
--
--  - If `l₂` can be obtained from `l₁` by swapping the second and third
--    elements, then `l₂` is a permutation of `l₁`.
--
--  - If `l₂` is a permutation of `l₁` and `l₃` is a permutation of`l₂`,
--    then `l₃` is a permutation of `l₁`.

--  In Lean, we can define `Perm3` as follows:

inductive Perm3 {α : Type} : List α → List α → Prop where
  | perm3_swap12 {x y z : α} : Perm3 [x, y, z] [y, x, z]
  | perm3_swap23 {x y z : α} : Perm3 [x, y, z] [x, z, y]
  | perm3_trans {l₁ l₂ l₃ : List α}
    (h₁₂ : Perm3 l₁ l₂)
    (h₂₃ : Perm3 l₂ l₃) :
    Perm3 l₁ l₃

--  ### Exercise (1 star): perm (Optional, Manually graded) ⭐

--  According to this definition, is `[1, 2, 3]` a permutation of itself?

--  Yes! Just apply `perm3_swap12` twice (or `perm3_swap23` twice).

--  ### Example: Evenness (yet again)

--  We've already seen two ways of stating a proposition that a number `n`
--  is even: We can say
--
--  (1) `Nat.even n = true` (using the recursive boolean function
--  `Nat.even`), or
--
--  (2) `∃ k, n = Nat.double k` (using an existential quantifier).
--
--  A third possibility, which we'll use as a simple running example in
--  this chapter, is to say that a number is even if we can *establish* its
--  evenness from the following two rules:
--
--          ———— (ev_0)
--          Ev 0
--
--          Ev n
--      —————————————— (ev_succ_succ)
--        Ev (n + 2)

--  Intuitively these rules say that:
--
--  - The number `0` is even.
--  - If `n` is even, then `n + 2` is even.
--
--  (Defining evenness in this way may seem a bit confusing, since we have
--  already seen two perfectly good ways of doing it. It makes a convenient
--  running example because it is simple and compact, but we will soon
--  return to the more compelling examples above.)

--  To illustrate how this new definition of evenness works, let's imagine
--  using it to show that `4` is even:
--
--                    ———— (ev_0)
--                    Ev 0
--             ———————————————————— (ev_succ_succ)
--             Ev (.succ (.succ 0))
--      ——————————————————————————————————— (ev_succ_succ)
--      Ev (.succ (.succ (.succ (.succ 0))))

--  In words, to show that `4` is even, by rule `ev_succ_succ`, it suffices
--  to show that `2` is even. This, in turn, is again guaranteed by rule
--  `ev_succ_succ`, as long as we can show that `0` is even. But this last
--  fact follows directly from the `ev_0` rule.

--  We can translate the informal definition of evenness from above into a
--  formal `inductive` declaration, where each "way that a number can be
--  even" corresponds to a separate constructor:

inductive Ev : Nat → Prop where
  | ev_0                              : Ev 0
  | ev_succ_succ {n : Nat} (h : Ev n) : Ev (n + 2)

--  Such definitions are interestingly different from previous uses of
--  `inductive` for defining inductive datatypes like `Nat` or `List`. For
--  one thing, we are defining not a `Type` (like `Nat`) or a function
--  yielding a `Type` (like `List`), but rather a function from `Nat` to
--  `Prop` ─ that is, a property of numbers. But what is really new is
--  that, because the `Nat` argument of `Ev` appears to the *right* of the
--  colon on the first line, it is allowed to take *different* values in
--  the types of different constructors: `0` in the type of `Ev.ev_0` and
--  `(n + 2)` in the type of `Ev.ev_succ_succ`. Accordingly, the type of
--  each constructor must be specified explicitly (after a colon), and each
--  constructor's type must have the form `Ev n` for some natural number
--  `n`.
--
--  In contrast, recall the definition of `List`:

sf_expect_failure_in
  inductive List (α : Type) : Type where
    | nil
    | cons (x : α) (l : List α)

--  or (equivalently but more explicitly):

sf_expect_failure_in
  inductive List (α : Type) : Type where
    | nil                       : List α
    | cons (x : α) (l : List α) : List α

--  This definition introduces the `α` parameter *globally*, to the *left*
--  of the colon, forcing the result of `List.nil` and `List.cons` to be
--  the same type (i.e., `List α`). But if we had tried to bring `Nat` to
--  the left of the colon in defining `Ev`, we would have seen an error:

sf_expect_failure_in
  inductive WrongEv (n : Nat) : Prop where
    | wrong_ev_0 : WrongEv 0
    | wrong_ev_succ_succ (h : WrongEv n) : WrongEv (n + 2)

--  Output:
--    Mismatched inductive type parameter in
--      WrongEv 0
--    The provided argument
--      0
--    is not definitionally equal to the expected parameter
--      n
--
--    Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.

--  In an `inductive` definition, an argument to the type constructor on
--  the left of the colon is called a "parameter", whereas an argument on
--  the right is called an "index" or "annotation."
--
--  For example, in `inductive List (α : Type) ...`, the `α` is a
--  parameter, while in `inductive Ev : Nat → Prop ...`, the unnamed `Nat`
--  argument is an index.

--  We can think of the inductive definition of `Ev` as defining a Lean
--  property `Ev : Nat → Prop`, together with two "evidence constructors":

#check Ev.ev_0         -- Ev 0
#check Ev.ev_succ_succ -- ∀ (n : Nat) (h : Ev n) : Ev (n + 2)

--  Indeed, Lean also accepts the following equivalent definition of `Ev`.

namespace EvPlayground

inductive Ev : Nat → Prop where
  | ev_0 : Ev 0
  | ev_succ_succ {n : Nat} (h : Ev n) : Ev (n + 2)

end EvPlayground

--  These evidence constructors can be thought of as "primitive evidence of
--  evenness", and they can be used later on just like proven theorems. In
--  particular, we can use Lean's `apply` and `exact` tactics with the
--  constructor names to obtain evidence for `Ev` of particular numbers...

namespace Ev

example : Ev 4 := by
  apply ev_succ_succ; apply ev_succ_succ; exact ev_0

--  ... or we can use function application syntax to combine several
--  constructors:

example : Ev 4 := by
  exact ev_succ_succ (ev_succ_succ ev_0)

--  ... or we can also use the `constructor` tactic we saw earlier to
--  select the appropriate inductive constructor:

example : Ev 4 := by
  constructor; constructor; constructor

--  In this way, we can also prove theorems that have hypotheses involving
--  `Ev`.

theorem plus4 (n : Nat) (h : Ev n) : Ev (4 + n) := by
  rw [Nat.add_comm]
  exact (ev_succ_succ (ev_succ_succ h))

--  ### Exercise (1 star): ev_double ⭐

theorem double (n : Nat) : Ev n.double := by
  induction n with
  | zero =>
    rw [Nat.double_zero]; exact ev_0
  | succ n ih =>
    rw [Nat.double_succ]; exact ev_succ_succ ih

end Ev

--  ### Constructing Evidence for Permutations

--  Similarly we can apply the evidence constructors to obtain evidence of
--  `Perm3 [1, 2, 3] [3, 2, 1]`:

namespace Perm3

theorem rev : Perm3 [1, 2, 3] [3, 2, 1] := by
  apply perm3_trans (l₂:= [2, 3, 1])
  . apply perm3_trans (l₂ := [2, 1, 3])
    . apply perm3_swap12
    . apply perm3_swap23
  . apply perm3_swap12

--  And again we can equivalently use function application syntax to
--  combine several constructors. (Note that the Lean type checker can
--  infer not only types, but also `Nat`s and `List`s, when they are clear
--  from the context.)

theorem rev' : Perm3 [1, 2, 3] [3, 2, 1] := by
  exact (perm3_trans
          (perm3_trans perm3_swap12 perm3_swap23)
          perm3_swap12)

--  So the informal derivation trees we drew above are not too far from
--  what's happening formally. Formally we're using the evidence
--  constructors to build *evidence trees*, similar to the finite trees we
--  built using the constructors of data types such as `Nat`, `List`,
--  binary trees, etc.

--  ### Exercise (1 star): Perm3 ⭐

theorem ex1 : Perm3 [1, 2, 3] [2, 3, 1] := by
  apply perm3_trans (l₂ := [2, 1, 3])
  . apply perm3_swap12
  . apply perm3_swap23

theorem refl (α : Type) (a b c : α) : Perm3 [a, b, c] [a, b, c] := by
  apply perm3_trans (l₂ := [b, a, c])
  . apply perm3_swap12
  . apply perm3_swap12

end Perm3

--  ## Using Evidence in Proofs

--  Besides *constructing* evidence that numbers are even, we can also
--  *destruct* such evidence, reasoning about how it could have been built.
--
--  Defining `Ev` with an `inductive` declaration tells Lean not only that
--  the constructors `Ev.ev_0` and `Ev.ev_succ_succ` are valid ways to
--  build evidence that some number is `Ev`, but also that these two
--  constructors are the *only* ways to build evidence that numbers are
--  `Ev`.
--
--  In other words, if someone gives us evidence `e` for the proposition
--  `Ev n`, then we know that `e` must be one of two things:
--
--  - `e = ev_0` and `n = 0`, or
--
--  - `e = ev_succ_succ n' e'` and `n = n' + 2`, where `e'` is evidence for
--    `Ev n'`.

--  This suggests that it should be possible to analyze a hypothesis of the
--  form `Ev n` much as we do inductively defined data structures; in
--  particular, it should be possible to argue either by *case analysis* or
--  by *induction* on such evidence. Let's look at a few examples to see
--  what this means in practice.

--  ### Destructing and Inverting Evidence

--  Suppose we are proving some fact involving a number `n`, and we are
--  given `Ev n` as a hypothesis. We already know how to perform case
--  analysis on `n` using `cases` or `induction`, generating separate
--  subgoals for the case where `n = 0` and the case where `n = n' + 1` for
--  some `n'`. But for some proofs we may instead want to analyze the
--  evidence for `Ev n` *directly*.
--
--  As a tool for such proofs, we can formalize the intuitive
--  characterization that we gave above for evidence of `Ev n`, using
--  `cases`.

theorem ev_inversion (n : Nat) (h : Ev n) :
    (n = 0) ∨ ∃ n', n = n' + 2 ∧ Ev n' := by
  cases h with
  | ev_0 => left; rfl
  | @ev_succ_succ n h => right; exists n

--  Facts like this are often called "inversion lemmas" because they allow
--  us to "invert" some given information to reason about all the different
--  ways it could have been derived.

--  Here there are two ways to prove `Ev n`, and the inversion lemma makes
--  this explicit.

--  ### Exercise (1 star): le_inversion ⭐

--  Let's prove a similar inversion lemma for `le`.

namespace LePlayground
theorem le_inversion (n m : Nat) (h : Le n m) :
    (n = m) ∨ (∃ m', m = m' + 1 ∧ Le n m') := by
  cases h with
  | refl => left; rfl
  | @step m h => right; exists m

end LePlayground

--   ----------------------------------------

--  _Quiz:_

--  Which tactics are needed to prove this goal?
--
--      ∀ (n : Nat), Ev n → n = 1 → true = false
--
--  (A) `cases` (B) `contradiction` (C) Both `cases` and `contradiction`
--  (D) these tactics are not sufficient to solve the goal.

--   ----------------------------------------

--  We can use the inversion lemma that we proved above to help structure
--  proofs:

theorem ev_succ_succ_ev (n : Nat) (h : Ev (n + 2)) : Ev n := by
  apply ev_inversion at h
  obtain ⟨⟨⟩⟩ | ⟨n', ⟨h₁,  h₂⟩⟩ := h
  injections h₁ heq
  subst heq
  exact h₂

--  Note how the inversion lemma produces two subgoals, which correspond to
--  the two ways of proving `Ev`. The first subgoal is a contradiction that
--  is discharged with `contradiction`. The second subgoal makes use of
--  `injections` and `subst`. The `subst` tactic takes an equation `x = t`
--  and replaces `x` by `t` in the context's hypotheses and in the goal,
--  then removes that equation from the context.
--
--  We've defined a handy tactic called `inversion` that factors out this
--  common pattern, saving us the trouble of explicitly stating and proving
--  an inversion lemma for every `inductive` definition we make.
--
--  Here, the `inversion` tactic can detect (1) that the first case, where
--  `n = 0`, does not apply and (2) that the `n'` that appears in the
--  `ev_succ_succ` case must be the same as `n`.
--
--  The details of how `inversion` is implemented are beyond the scope of
--  this course, but suffice to say Lean's metaprogramming capabilities are
--  such that almost any sequence of reasoning steps can be implemented as
--  a new tactic.

theorem ev_succ_succ_ev' (n : Nat) (h : Ev (n + 2)) : Ev n := by
  inversion h; assumption

--  The `inversion` tactic can apply the principle of explosion to
--  "obviously contradictory" hypotheses involving inductively defined
--  properties, something that takes a bit more work using our inversion
--  lemma. Compare:

theorem one_not_even : ¬ Ev 1 := by
  intro h; apply ev_inversion at h
  obtain ⟨⟨⟩⟩ | ⟨n', ⟨h₁,  h₂⟩⟩ := h
  injections

theorem one_not_even' : ¬ Ev 1 := by
  intro h; inversion h

--  ### Exercise (1 star): inversion_practice ⭐

--  Prove the following result using `inversion`. (For extra practice, you
--  can also prove it using the inversion lemma.)

theorem ev_4_ev_n n (h : Ev (n + 4)) : Ev n := by
  inversion h with
  | ev_succ_succ h' => apply ev_succ_succ_ev; exact h'

--  ### Exercise (1 star): ev5_nonsense ⭐

--  Prove the following result using `inversion`.

theorem ev5_nonsense (h : Ev 5) : 2 + 2 = 9 := by
  inversion h with
  | ev_succ_succ h' =>
    inversion h' with
    | ev_succ_succ h'' =>
      inversion h''

--  We can use `inversion` to re-prove some theorems from Tactics.
--
--  Note that `inversion` also works on equality propositions.

theorem inversion_ex1 (n m o : Nat) (h : [n, m] = [o, o]) : [n] = [m] := by
  inversion h; rfl

theorem inversion_ex2 n (h : n + 1 = 0) : 2 + 2 = 5 := by
  inversion h

--  Note to developers (before next release):
--      The wording there is totally awkward!

--  Here's how `inversion` works in general.
--
--  - Suppose the name `h` refers to an assumption `p` in the current
--    context, where `p` has been defined by an `inductive` declaration.
--
--  - Then, for each of the constructors of `p`, `inversion h` generates a
--    subgoal in which `h` has been replaced by the specific conditions
--    under which this constructor could have been used to prove `p`.
--
--  - Some of these subgoals will be self-contradictory; `inversion` throws
--    these away.
--
--  - The ones that are left represent the cases that must be proved to
--    establish the original goal. For those, `inversion` adds to the proof
--    context all equations that must hold of the arguments given to `p` ─
--    e.g., `n' = n` in the proof of `ev_succ_succ_ev`.

--   ----------------------------------------

--  _Quiz:_

--  Note to developers:
--      LY: Not quite a fair question because this is the first time they
--      are facing a situation where the index does not start with a
--      constructor.

--  Which tactics are needed to prove this goal, in addition to `apply` or
--  `exact`?
--
--      ∀ n, Ev (2 + n) → Ev n
--
--  (A) `inversion` (B) `inversion`, `injections` (C) `inversion`,
--  `rw [Nat.add_comm]` (D) `inversion`, `rw [Nat.add_comm]`, `injections`

--   ----------------------------------------

--  The `Ev.double` exercise above allows us to easily show that our new
--  notion of evenness is implied by the two earlier ones (since, by
--  `Nat.even_bool_prop` in the Logic chapter, we already know that those
--  are equivalent to each other). To show that all three coincide, we just
--  need the following lemma.

--  Note to developers (before next release):
--      This whole part of the section is a mess!!

sf_expect_failure_in
  example (n : Nat) : Ev n → Nat.Even n := by
    /- We could try to proceed by case analysis or induction on `n`.  But
        since `Ev` is mentioned in a premise, this strategy seems
        unpromising, because (as we've noted before) the induction
        hypothesis will talk about `n-1` (which is _not_ even!).  Thus, it
        seems better to first try `inversion` on the evidence for `Ev`.
        Indeed, the first case can be solved trivially. -/
    intro h
    inversion h with
    /- h = ev_0 -/
    | ev_0 => exists 0  -- (`0 = double 0` is closed by `exists`'s final `rfl`)
    /- h = ev_succ_succ n' h' -/
    | ev_succ_succ n' h' =>
    /- Unfortunately, the second case is harder.  We need to show
      `∃ n₀, n' + 2 = double n₀`, but the only available assumption is
      `h'`, which states that `Ev n'` holds.  Since this isn't directly
      useful, it seems that we are stuck and that performing case
      analysis on `h` was a waste of time.
  
      If we look more closely at our second goal, however, we can see
      that something interesting happened: By performing case analysis
      on `h`, we were able to reduce the original result to a similar
      one that involves a _different_ piece of evidence for `Ev`: namely
      `h'`.  More formally, we could finish our proof if we could show
      that
      ```
      ∃ k', n' = double k',
      ```
      which is the same as the original statement, but with `n'` instead
      of `n`.  Indeed, it is not difficult to convince Lean that this
      intermediate result would suffice. -/
      have he : (∃ (k' : Nat), n' = k'.double) → (∃ (n₀ : Nat), n' + 2 = n₀.double) := by
        intro ⟨k, hk⟩; exists (k + 1); rw [Nat.double_succ, hk]
      apply he
      /- Unfortunately, now we are stuck: we are trying to prove another instance
          of the same theorem we set out to prove -- only here we are
          talking about `n'` instead of `n`. -/

--  Note to developers (Benjamin Pierce @bcpierce00, before next release, 2021):
--      I agree that it's all pretty chewy. Wonder if we really need any of
--      it or if the point could be made just as well with less detail...
--      When I explained it in class this time, I just observed that the
--      destruct was giving us a hypothesis about 2 being even, which just
--      can't be what we want, and skipped all the rest... After thinking
--      about it for a bit, though, I do think the full story here is
--      useful (at least for the FULL version -- the TERSE could still be
--      streamlined). So I'm going to leave it for now.

--  Note to developers (Benjamin Pierce @bcpierce00, before next release, 2025):
--      I think best just to shorten it! And maybe make it not a
--      WORKINCLASS.

--  ### Induction on Evidence

--  If this story feels familiar, it is no coincidence: We encountered
--  similar problems in the Induction chapter, when trying to use case
--  analysis to prove results that required induction. And once again the
--  solution is... induction!

--  The behavior of `induction` on evidence is the same as its behavior on
--  data: It causes Lean to generate one subgoal for each constructor that
--  could have been used to build that evidence, while providing an
--  induction hypothesis for each recursive occurrence of the property in
--  question.
--
--  To prove that a property of `n` holds for all even numbers (i.e., those
--  for which `Ev n` holds), we can use induction on `Ev n`. This requires
--  us to prove two things, corresponding to the two ways in which `Ev n`
--  could have been constructed. If it was constructed by `Ev.ev_0`, then
--  `n = 0` and the property must hold of `0`. If it was constructed by
--  `Ev.ev_succ_succ`, then the evidence of `Ev n` is of the form
--  `Ev.ev_succ_succ n' h'`, where `n = n' + 2` and `h'` is evidence for
--  `Ev n'`. In this case, the inductive hypothesis says that the property
--  we are trying to prove holds for `n'`.

--  Let's try proving that lemma again:

theorem Nat.ev_Even (n : Nat) (h : Ev n) : Even n := by
  induction h with
  -- h = ev_0
  | ev_0 => exists 0 -- (`0 = double 0` is closed by `exists`'s final `rfl`)
  -- h = ev_succ_succ n' h', with ih : Even n'
  | ev_succ_succ h' ih =>
    let ⟨k, hk⟩ := ih
    exists k + 1; rw [double_succ, hk]

--  Here, we can see that Lean produced an `ih` that corresponds to `h`,
--  the single recursive occurrence of `Ev` in its own definition. Since
--  `h'` mentions `n'`, the induction hypothesis talks about `n'`, as
--  opposed to `n` or some other number.

--  The equivalence between the second and third definitions of evenness
--  now follows.

theorem Nat.ev_Even_iff (n : Nat) : Ev n ↔ Even n := by
  apply Iff.intro
  . intro h; exact Nat.ev_Even _ h
  . intro ⟨k, hk⟩; rw [hk]; exact Ev.double k

--  As we will see in later chapters, induction on evidence is a recurring
--  technique across many areas ─ in particular for formalizing the
--  semantics of programming languages.
--
--  The following exercises provide simpler examples of this technique, to
--  help you familiarize yourself with it.

--  ### Exercise (2 stars): ev_sum ⭐⭐

theorem ev_sum (n m : Nat) (hₙ : Ev n) (hₘ : Ev m) : Ev (n + m) := by
  induction hₙ with
  | ev_0 => rw [Nat.zero_add]; exact hₘ
  | ev_succ_succ h' ih =>
    rw [Nat.add_comm, ← Nat.add_assoc, Nat.add_comm m]
    apply Ev.ev_succ_succ; exact ih

--  ### Exercise (3 stars): ev_ev__ev (Advanced) ⭐⭐⭐

theorem ev_ev__ev (n m : Nat) (hₙₘ : Ev (n + m)) (hₙ : Ev n) : Ev m := by
  /- Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. -/
  induction hₙ generalizing m with
  | ev_0 => rw [Nat.zero_add] at hₙₘ; exact hₙₘ
  | ev_succ_succ h' ih =>
    apply ih; rw [Nat.add_comm, ←Nat.add_assoc, Nat.add_comm m] at hₙₘ
    inversion hₙₘ; assumption

--  ### Exercise (3 stars): ev_plus_plus (Optional) ⭐⭐⭐

--  This exercise can be completed without induction or case analysis. But,
--  you will need a clever `have` and some tedious rewriting. Hint: Is
--  `(n + m) + (n + k)` even?

theorem ev_plus_plus (n m k : Nat)
    (hₙₘ : Ev (n + m))
    (hₙₚ : Ev (n + k)) :
    Ev (m + k) := by
  apply (ev_ev__ev (n + n))
  . have h : n + n + (m + k) = n + m + (n + k) := by
      rw [Nat.add_assoc, Nat.add_assoc]
      congr 1
      exact Nat.add_left_comm _ _ _
    rw [h]
    apply ev_sum
    . assumption
    . assumption
  . rw [← Nat.double_add]; exact Ev.double n

--  Another example of a proposition that can be characterized both
--  recursively and inductively is the `List.In` predicate we defined in
--  the Logic chapter. As a reminder, the recursive definition we saw
--  looked like this:

def In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'

--  We can also write this definition inductively like so:

inductive In_Inductive {α : Type} (x : α) : List α → Prop
  | head {l : List α} : In_Inductive x (x :: l)
  | tail {y : α} {l : List α} (h : In_Inductive x l) : In_Inductive x (y :: l)

--  In fact, this is exactly how Lean defines this proposition, which it
--  calls `Membership.mem` and which is written `x ∈ l`. Its negation
--  `¬ x ∈ l` is also written as `x ∉ l`.
--
--  A good exercise to test your understanding of induction on evidence is
--  to prove the equivalence of these definitions:

--  ### Exercise (2 stars): in_mem ⭐⭐

theorem in_mem {α} (x : α) (l : List α) : List.In x l ↔ x ∈ l := by
  constructor
  . intro h; induction l with
    | nil => apply List.In_nil at h; contradiction
    | cons hd tl ih =>
      rw [List.In_cons] at h
      obtain h | h := h
      . subst h; constructor
      . constructor; exact ih h
  . intro h; induction h with
    | head l' => rw [List.In_cons]; left; rfl
    | tail h ih => rw [List.In_cons]; right; assumption

--  The characterizing lemmas for `∈` are called `List.mem_nil_iff` and
--  `List.mem_cons`.

--  ### Multiple Induction Hypotheses

--  Recall the definition of the reflexive, transitive, closure of a
--  relation:

namespace ClosReflTransRemainder

inductive ClosReflTrans {α : Type} (R : α → α → Prop) : α → α → Prop where
  | rt_step {x y : α} (h : R x y) : ClosReflTrans R x y
  | rt_refl {x : α} : ClosReflTrans R x x
  | rt_trans {x y z : α}
    (h₁ : ClosReflTrans R x y)
    (h₂ : ClosReflTrans R y z) :
    ClosReflTrans R x z
end ClosReflTransRemainder

--  Let's say that a relation on a type `α` is *diagonal* if it refines the
--  identity relation ─ i.e., if `R x y` implies `x = y`.

--  Note to developers:
--      NDS 25: I originally wanted to do this with the empty relation,
--      defined inductively, but this requires introducing the surprising
--      behavior of unhabitated types, which I don't think have been
--      covered (yet?). Maybe they should be? BCP 25: This one seems good.

def Diagonal {α : Type} (R : α → α → Prop) := ∀ {x y}, R x y → x = y

--  Now consider the following lemma about diagonal relations:

theorem closure_of_diagonal_is_diagonal {α} (R : α → α → Prop)
    (hDiag : Diagonal R) :
    Diagonal (ClosReflTrans R) := by
  intro x y h
  induction h with
  /- The two first cases go as you'd expect... -/
  | rt_step hr =>
    rw [hDiag hr]
  | rt_refl => rfl
  /- ...  but something interesting happens here: there are two
       induction hypotheses, `ih` and `ih'`! If you think about it, it
       is not that weird: we are in the case `rt_trans`, which has
       two recursive components, `hxy`, relating `x` to `y` and `hyz`,
       relating `y` to `z`. Hence we may want (and will actually need)
       an induction hypothesis for `hxy` and one for `hyz` ─ they are
       called `ihxy` and `ihyz` here. In general, Lean will always
       generate one induction hypothesis per recursive constructor of
       the type being inducted over. -/
  | rt_trans _ _ ihxy ihyz => rw [ihxy, ihyz]

--  Note to developers:
--      HIDE: NDS comparing the previous proof to the pen-and-paper version
--      could be an idea to consider, as the way people tend to write it on
--      paper differs a bit from the mechanized proof. BCP 25: Yes.

--  ### Exercise (4 stars): ev'_ev (Advanced, Optional) ⭐⭐⭐⭐

--  In general, there may be multiple ways of defining a property
--  inductively. For example, here's a (slightly contrived) alternative
--  definition for `Ev`:

inductive Ev' : Nat → Prop where
  | ev'_0 : Ev' 0
  | ev'_2 : Ev' 2
  | ev'_sum {n m : Nat} (h₁ : Ev' n) (h₂ : Ev' m) : Ev' (n + m)

--  Prove that this definition is logically equivalent to the old one. To
--  streamline the proof, use the technique (from the Logic chapter) of
--  applying theorems to arguments, and note that the same technique works
--  with constructors of inductively defined propositions.

theorem ev'_ev n : Ev' n ↔ Ev n := by
  apply Iff.intro
  . /- → -/
    intro h; induction h
    . constructor
    . constructor; constructor
    . apply ev_sum; assumption; assumption
  . /- <- -/
    intro h; induction h
    . constructor
    . constructor; assumption; constructor

--  We can do similar inductive proofs on the `Perm3` relation, which we
--  defined earlier as follows:

namespace Perm3Reminder

inductive Perm3 {α : Type} : List α → List α → Prop where
  | perm3_swap12 {x y z : α} : Perm3 [x, y, z] [y, x, z]
  | perm3_swap23 {x y z : α} : Perm3 [x, y, z] [x, z, y]
  | perm3_trans {l₁ l₂ l₃ : List α}
    (h₁₂ : Perm3 l₁ l₂)
    (h₂₃ : Perm3 l₂ l₃) :
    Perm3 l₁ l₃

end Perm3Reminder

namespace Perm3

theorem symm {α} (l₁ l₂ : List α)
    (h : Perm3 l₁ l₂) : Perm3 l₂ l₁ := by
  induction h with
  | perm3_swap12 => constructor
  | perm3_swap23 => constructor
  | perm3_trans _ _ ih₁₂ ih₂₃ =>
    exact perm3_trans ih₂₃ ih₁₂

--  ### Exercise (2 stars): Perm3_In ⭐⭐

--  If you find yourself dealing with deeply nested `cases` in this proof,
--  think back to Logic where you learned about the `obtain` tactic.

theorem In {α} (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm with
  | perm3_swap12 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . right; left; assumption
    . left; assumption
    . right; right; left; assumption
    . contradiction
  | perm3_swap23 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . left; assumption
    . right; right; left; assumption
    . right; left; assumption
    . contradiction
  | perm3_trans _ _  ih₁₂ ih₂₃ =>
    apply ih₂₃; apply ih₁₂; apply hIn

--  ### Exercise (1 star): Perm3_NotIn (Optional) ⭐

theorem NotIn {α} (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∉ l₁) : x ∉ l₂ := by
  intro hContra
  apply hIn; apply In
  . apply symm; exact hPerm
  . exact hContra

--  ### Exercise (2 stars): NotPerm3 (Optional) ⭐⭐

--  Proving that something is NOT a permutation is quite tricky. Some of
--  the lemmas above, like `Perm3.In` can be useful for this.

theorem Not : ¬ Perm3 [1, 2, 3] [1, 2, 4] := by
  intro h; apply (Perm3.In 3) at h
  have h4 : 3 ∉ [1, 2, 4] := by
    rw [List.mem_cons, List.mem_cons, List.mem_cons]; intro h4
    obtain h | h | h | h := h4
    . contradiction
    . contradiction
    . contradiction
    . contradiction
  apply h4; apply h
  rw [List.mem_cons, List.mem_cons, List.mem_cons]
  right; right; left; rfl

end Perm3

--  ## Exercising with Inductive Relations

--  Note to developers (Chris Henson @chenson2018, before next release):
--      Bad flow + duplication needs fixing. Could move some of this to the
--      top. In the terse version this whole section is useless, it only
--      has a (mostly) duplicated definition. For now FULLED the whole
--      thing, but better fix seems needed.

--  Just as a single-argument proposition defines a *property*, a
--  two-argument proposition defines a *relation*.
--
--  A proposition parameterized by a number (such as `Ev`) can be thought
--  of as a *property* — i.e., it defines a subset of `Nat`, namely those
--  numbers for which the proposition is provable. In the same way, a
--  two-argument proposition can be thought of as a *relation* — i.e., it
--  defines a set of pairs for which the proposition is provable.

namespace Playground

--  Just like properties, relations can be defined inductively. One useful
--  example is the "less than or equal to" relation on numbers that we
--  briefly saw above.

inductive Le : Nat → Nat → Prop where
  | refl {n : Nat}                : Le n n
  | succ {n m : Nat} (h : Le n m) : Le n (m + 1)

--  (We've written the definition a bit differently this time, giving
--  explicit names to the arguments to the constructors and moving them to
--  the left of the colons.)
--
--  Proofs of facts about `≤` using the constructors `Nat.le.refl` and
--  `Nat.le.step` follow the same patterns as proofs about properties, like
--  `Ev` above. We can `apply` the constructors to prove `≤` goals (e.g.,
--  to show that `3 ≤ 3` or `3 ≤ 6`), and we can use tactics like
--  `inversion` to extract information from `≤` hypotheses in the context
--  (e.g., to prove that `(2 ≤ 1) → 2 + 2 = 5`.)
--
--  Here are some sanity checks on the definition. (Notice that, although
--  these are the same kind of simple "unit tests" as we gave for the
--  testing functions we wrote in the first few lectures, we must construct
--  their proofs explicitly ─ `rw` and `rfl` don't do the job, because the
--  proofs aren't just a matter of simplifying computations.)
--
--  Some sanity checks...

theorem test_le1 : 3 ≤ 3 := by
  apply Nat.le.refl

theorem test_le2 : 3 ≤ 6 := by
  apply Nat.le.step; apply Nat.le.step; apply Nat.le.step; apply Nat.le.refl

theorem test_le3 (h : 2 ≤ 1) : 2 + 2 = 5 := by
  inversion h with
  | step h' => inversion h'

--  The "strictly less than" relation `n < m` can now be defined in terms
--  of `Nat.le`.

def lt (n m : Nat) : Prop := Nat.le (n + 1) m

--  The `≥` operation is defined in terms of `≤`. Lean provides a theorem
--  `ge_iff_le` allowing us to rewrite between them.

def ge (m n : Nat) : Prop := Nat.le n m

example (m n : Nat) (h : m ≥ n) : n ≤ m := by
  rw [← ge_iff_le]; assumption

end Playground

--  Note to developers:
--      HIDE: PR: Added the following paragraph to try to help reduce
--      random walks over the following exercises.

--  From the definition of `Nat.le`, we can sketch the behaviors of `cases`
--  and `induction` on a hypothesis `h` providing evidence of the form
--  `n ≤ m`. Doing `cases h` will generate two cases. In the first case,
--  `n = m`, and it will replace instances of `m` with `n` in the goal and
--  context. In the second case, `n = m' + 1` for some `m'` for which
--  `n ≤ m'` holds, and it will replace instances of `m` with `m' + 1`.
--  Doing `inversion h` will remove impossible cases and add generated
--  equalities to the context for further use. Doing `induction h` will, in
--  the second case, add the induction hypothesis that the goal holds when
--  `m` is replaced with `m'`.
--
--  Here are a number of facts about the `≤` and `<` relations that we are
--  going to need later in the course. The proofs make good practice
--  exercises.

--  ### Exercise (3 stars): le_facts ⭐⭐⭐

theorem le_trans (m n k : Nat) (h₁ : m ≤ n) (h₂ : n ≤ k) : m ≤ k := by
  induction h₂ with
  | refl => assumption
  | step _ ih => constructor; exact ih

theorem zero_le_n (n : Nat) : 0 ≤ n := by
  induction n with
  | zero => constructor
  | succ n ih => constructor; exact ih

theorem n_le_m__succ_n_le_succ_m (n m : Nat) (h : n ≤ m) : n + 1 ≤ m + 1 := by
  induction h with
  | refl => constructor
  | step h ih =>
    rw [Nat.succ_add]
    constructor; exact ih

theorem succ_n_le_succ_m__n_le_m (n m : Nat) (h : n + 1 ≤ m + 1) : n ≤ m := by
  inversion h with
  | refl => constructor
  | step h' =>
    apply le_trans _ (n + 1) _
    . constructor; constructor
    . assumption

theorem le_add_l (n m : Nat) : n ≤ n + m := by
  induction n with
  | zero => rw [Nat.zero_add]; apply zero_le_n
  | succ n' ih =>
    rw [Nat.succ_add]
    apply n_le_m__succ_n_le_succ_m
    assumption

--  ### Exercise (2 stars): plus_le_facts1 ⭐⭐

theorem add_le (n₁ n₂ m : Nat) (h : n₁ + n₂ ≤ m) : n₁ ≤ m ∧ n₂ ≤ m := by
  induction h with
  | refl =>
    constructor
    . apply le_add_l
    . rw [Nat.add_comm]; apply le_add_l
  | step =>
    constructor
    . apply le_trans (n := n₁ + n₂)
      . apply le_add_l
      . apply Nat.le.step; assumption
    . apply le_trans (n := n₁ + n₂)
      . rw [Nat.add_comm]; apply le_add_l
      . apply Nat.le.step; assumption

theorem add_le_cases (n m p q : Nat) (h : n + m ≤ p + q) : n ≤ p ∨ m ≤ q := by
  /- Hint: May be easiest to prove by induction on `n`. -/
  induction n generalizing m p q with
  | zero => left; apply zero_le_n
  | succ n' ih =>
    cases p with
    | zero =>
      right; apply add_le at h
      let ⟨_, h⟩ := h
      rw [Nat.zero_add] at h; assumption
    | succ p' =>
      rw [Nat.succ_add, Nat.succ_add] at h
      apply succ_n_le_succ_m__n_le_m at h
      apply ih at h
      cases h with
      | inl => left; apply n_le_m__succ_n_le_succ_m; assumption
      | inr => right; assumption

--  ### Exercise (2 stars): plus_le_facts2 ⭐⭐

theorem add_le_compat_l (n m p : Nat) (h : n ≤ m) : p + n ≤ p + m := by
  induction p with
  | zero =>
    rw [Nat.zero_add, Nat.zero_add]; assumption
  | succ p' ih =>
    rw [Nat.succ_add, Nat.succ_add]
    apply n_le_m__succ_n_le_succ_m
    assumption

theorem plus_le_compat_r (n m p : Nat) (h : n ≤ m) : n + p ≤ m + p := by
  rw [Nat.add_comm, Nat.add_comm m]
  apply add_le_compat_l
  assumption

theorem le_plus_trans (n m p : Nat) (h : n ≤ m) : n ≤ m + p := by
  induction p with
  | zero => rw [Nat.add_zero]; assumption
  | succ p' ih =>
    rw [← Nat.add_assoc]; constructor; assumption

--  ### Exercise (3 stars): lt_facts (Optional) ⭐⭐⭐

theorem lt_ge_cases (n m : Nat) : n < m ∨ n ≥ m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => right; constructor
    | succ _ =>
      left;
      apply n_le_m__succ_n_le_succ_m;
      apply zero_le_n
  | succ n' ih =>
    cases m with
    | zero =>
      rw [ge_iff_le]; right
      apply zero_le_n
    | succ m' =>
      cases ih m' with
      | inl ih =>
        left
        apply n_le_m__succ_n_le_succ_m
        exact ih
      | inr ih =>
        right
        apply n_le_m__succ_n_le_succ_m
        exact ih

theorem n_lt_m__n_le_m (n m : Nat) (h : n < m) : n ≤ m := by
  apply succ_n_le_succ_m__n_le_m
  constructor; assumption

theorem plus_lt (n₁ n₂ m : Nat) (h : n₁ + n₂ < m) : n₁ < m ∧ n₂ < m := by
  constructor
  . apply le_trans (n := (n₁ + n₂) + 1)
    . apply n_le_m__succ_n_le_succ_m
      apply le_add_l
    . exact h
  . apply le_trans (n := (n₂ + n₁) + 1)
    . apply n_le_m__succ_n_le_succ_m
      apply le_add_l
    . rw [Nat.add_comm n₂]; assumption

--  ### Exercise (4 stars): ble_le (Optional) ⭐⭐⭐⭐

theorem ble_sound (n m : Nat) (h : Nat.ble n m = true) : n ≤ m := by
  induction n generalizing m with
  | zero => apply zero_le_n
  | succ n' ih =>
    cases m with
    | zero =>
      contradiction
    | succ m' =>
      rw [Nat.ble] at h
      apply n_le_m__succ_n_le_succ_m
      apply ih; apply h

theorem ble_complete n m (h : n ≤ m) : Nat.ble n m = true := by
  induction n generalizing m with
  | zero => rw [Nat.ble]
  | succ n' ih =>
    cases m with
    | zero => contradiction
    | succ m' =>
      rw [Nat.ble]
      apply succ_n_le_succ_m__n_le_m at h
      apply ih at h
      assumption

--  Hint: The next two can easily be proved without using `induction`.

theorem ble_iff (n m : Nat) : Nat.ble n m = true ↔ n ≤ m := by
  apply Iff.intro
  . apply ble_sound
  . apply ble_complete

theorem ble_true_trans (n m k : Nat) :
    Nat.ble n m = true →
    Nat.ble m k = true →
    Nat.ble n k = true := by
  rw [ble_iff, ble_iff, ble_iff]
  apply le_trans

--  ### Exercise (3 stars): R_provability (Manually graded) ⭐⭐⭐

--  We can define three-place relations, four-place relations, etc., in
--  just the same way as binary relations. For example, consider the
--  following three-place relation on numbers:

inductive R : Nat → Nat → Nat → Prop where
  | c1                                               : R  0      0       0
  | c2 {m n k : Nat} (h : R  m       n       k)      : R (m + 1) n      (k + 1)
  | c3 {m n k : Nat} (h : R  m       n       k)      : R  m     (n + 1) (k + 1)
  | c4 {m n k : Nat} (h : R (m + 1) (n + 1) (k + 2)) : R  m      n       k
  | c5 {m n k : Nat} (h : R  m       n       k)      : R  n      m       k

--  Note to developers:
--      HIDE: APT 21: Reformatted the above after a student with dyslexia
--      complained. But the effect is still lost in the HTML. He also noted
--      that the kind of question that follows doesn't really require a
--      high-arity relation.
--
--      MRC 3/22: I believe that violates the OCaml Community Guidelines on
--      indentation.
--
--      https://ocaml.org/learn/tutorials/guidelines.html#Bad-indentation-of-pattern-matching-constructs
--
--      Whether those are applicable here is a matter of debate. But
--      torquing the entire textbook into this mode of alignment does not
--      seem any more desirable to me than torquing an OCaml codebase.
--
--      BCP 25: No, but for this specific problem it seems OK. Let's leave
--      it like this.

--  - Which of the following propositions are provable?
--
--  - `R 1 1 2`
--
--  - `R 2 2 6`
--
--  - If we dropped constructor `c5` from the definition of `R`, would the
--    set of provable propositions change? Briefly (1 sentence) explain
--    your answer.
--
--  - If we dropped constructor `c4` from the definition of `R`, would the
--    set of provable propositions change? Briefly (1 sentence) explain
--    your answer.

--  - The first proposition is provable and the second is not. The proof
--    term for the first is:
--
--    `(c3 _ _ _ (c2 _ _ _ c1)).`
--
--  - Dropping `c5` would not change the set of provable propositions. `c4`
--    and `c1` don't interact with `c5`, since they're already symmetric in
--    `m` and `n`; `c2` followed by `c5` is equivalent to `c3`, and vice
--    versa.
--
--  - Dropping `c4` would not change the set of provable propositions. This
--    constructor just "undoes" one application of `c2` and one application
--    of `c3`. More precisely, the only way we can construct evidence for
--    `R (S m) (S n) (S (S o))` is by applying `c2` and `c3` (in either
--    order) to evidence for `R m n o`, so the latter must already hold.
--    (This can be proved by induction, although the proof is surprisingly
--    tedious.)

--  ### Exercise (3 stars): R_fact (Optional) ⭐⭐⭐

--  The relation `R` above actually encodes a familiar function. Figure out
--  which function; then state and prove this equivalence in Lean.

def fR : Nat → Nat → Nat
  := ((· + ·))

namespace R

theorem R.equiv_fR m n k : R m n k ↔ fR m n = k := by
  unfold fR
  apply Iff.intro
  . intro h; induction h with
    | c1 => rfl
    | c2 _ ih => rw [Nat.succ_add, ih]
    | c3 _ ih => rw [Nat.add_succ, ih]
    | c4 _ ih =>
      rw [Nat.succ_add, Nat.add_succ] at ih
      injections
    | c5 _ ih => rw [Nat.add_comm]; exact ih
  . intro h; subst h
    have R0 : ∀ k, R 0 k k := by
      intro k; induction k with
      | zero => exact c1
      | succ k ih => exact c3 ih
    induction m with
    | zero => rw [Nat.zero_add]; exact R0 n
    | succ m ih => rw [Nat.succ_add]; exact c2 ih

--  ### Exercise (4 stars): subsequence (Advanced) ⭐⭐⭐⭐

--  A list is a *subsequence* of another list if all of the elements in the
--  first list occur in the same order in the second list, possibly with
--  some extra elements in between. For example,
--
--      [1, 2, 3]
--
--  is a subsequence of each of the lists
--
--      [1, 2, 3]
--      [1, 1, 1, 2, 2, 3]
--      [1, 2, 7, 3]
--      [5, 6, 1, 9, 9, 2, 7, 3, 8]
--
--  but it is *not* a subsequence of any of the lists
--
--      [1, 2]
--      [1, 3]
--      [5, 6, 2, 1, 7, 3, 8].
--
--  - Define an inductive proposition `subseq` on `List Nat` that captures
--    what it means to be a subsequence. There are a number of correct ways
--    to do this. You should make sure that your definition behaves
--    correctly on all the positive and negative examples above, but you do
--    not need to prove this formally.
--
--  - Prove `subseq_refl` that subsequence is reflexive, that is, any list
--    is a subsequence of itself.
--
--  - Prove `subseq_app` that for any lists `l₁`, `l₂`, and `l₃`, if `l₁`
--    is a subsequence of `l₂`, then `l₁` is also a subsequence of
--    `l₂ ++ l₃`.
--
--  - (Harder) Prove `subseq_trans` that subsequence is transitive ─ that
--    is, if `l₁` is a subsequence of `l₂` and `l₂` is a subsequence of
--    `l₃`, then `l₁` is a subsequence of `l₃`.

--  Note to developers (before next release):
--      `AC'21: I think that it is more atomic to consider
--      [sub_nil : subseq [] []]. The benefits is that it makes calls to
--      [inversion] produce fewer goals. The downside is that one has to
--      state as a lemma [sub_nil_l : forall l, subseq [] l], however it
--      would be nice to have this as an exercise anyway, because otherwise
--      students who go for the definition of [sub_seq [] []] are required
--      to guess the need for [sub_nil_l].
--      BCP: I agree this version could be nicer to suggest, and I agree that
--      adding this lemma as a warm-up exercise is nice.`
--
--      Sainati 25: I am generally not against proofs that can be made much
--      easier with smart inductive definitions (this is sort of the whole
--      ball game in a way, isn't it?) but one way to make sure students
--      can't trivialize the exercise is to just give them the definition
--      we want them to use? We could also add a (maybe optional) question
--      afterwards to provide a different definition that makes the proofs
--      easier (and maybe prove them equivalent).

inductive Subseq : List Nat → List Nat → Prop where
  | sub_nil {l : List Nat} : Subseq [] l
  | sub_take {x : Nat} {l₁ l₂ : List Nat}
    (h : Subseq l₁ l₂) :
    Subseq (x :: l₁) (x :: l₂)
  | sub_skip {x : Nat} {l₁ l₂ : List Nat}
    (h : Subseq l₁ l₂) :
    Subseq l₁ (x :: l₂)

namespace Subseq

theorem refl (l : List Nat) : Subseq l l := by
  induction l with
  | nil => constructor
  | cons hd tl ih =>
    constructor; assumption

theorem app (l₁ l₂ l₃ : List Nat)
    (h : Subseq l₁ l₂) : Subseq l₁ (l₂ ++ l₃) := by
  induction h with
  | sub_nil  => constructor
  | sub_take => constructor; assumption
  | sub_skip => constructor; assumption

--  Note to developers:
--      HIDE: AC'21: this exercise should probably be marked as more
--      challenging. In particular, it's not necessarily obvious at first
--      sight that the induction should go on the second hypothesis, and
--      with `l₁` generalized. BCP 21: Made it 3 points instead of 2, and
--      included a hint. CH'23: Made it 4 points, since there are 5
--      different choices here and the hint doesn't help with that.

theorem trans (l₁ l₂ l₃ : List Nat)
    (h₁₂ : Subseq l₁ l₂)
    (h₂₃ : Subseq l₂ l₃) :
    Subseq l₁ l₃ := by
  /- Hint: be careful about what you are doing induction on and which
     other things need to be generalized... -/
  induction h₂₃ generalizing l₁ with
  | sub_nil => inversion h₁₂; constructor
  | sub_take _ ih =>
    inversion h₁₂; constructor
    . constructor; apply ih; assumption
    . constructor; apply ih; assumption
  | sub_skip _ ih =>
    constructor; apply ih; assumption

end Subseq

--  ### Exercise (2 stars): R_provability2 (Optional, Manually graded) ⭐⭐

--  Suppose we give Lean the following definition:
--
--      inductive R : Nat → List Nat → Prop where
--        | c1                                            : R  0      []
--        | c2 {n : Nat} {l : List Nat} (h : R  n      l) : R (n + 1) (n :: l)
--        | c3 {n : Nat} {l : List Nat} (h : R (n + 1) l) : R  n      l
--
--  Which of the following propositions are provable?
--
--  - `R 2 [1, 0]`
--  - `R 1 [1, 2, 1, 0]`
--  - `R 6 [3, 2, 1, 0]`

--  The first two are provable, the third is not.
--
--  In case this question puzzled you, one good way to understand
--  definitions like this is to explore their implications with concrete
--  examples, e.g.
--
--      R 0 []           by c1
--      R 1 [0]          by c2 using R 0 []
--      R 2 [1, 0]       by c2 using R 1 [0]
--      R 3 [2, 1, 0]    by c2 using R 2 [1, 0]
--      R 2 [2, 1, 0]    by c3 using R 3 [2, 1, 0]
--      R 1 [2, 1, 0]    by c3 using R 2 [2, 1, 0]
--      R 2 [1, 2, 1, 0] by c2 using R 1 [2, 1, 0]
--      R 1 [1, 2, 1, 0] by c3 using R 2 [1, 2, 1, 0]
--      etc.
--
--  If you do a few more of these yourself, you should see the pattern
--  emerging.

--  ### Exercise (2 stars): total_relation (Optional) ⭐⭐

--  Define an inductive binary relation `total_relation` that holds between
--  every pair of natural numbers.

inductive TotalRelation : Nat → Nat → Prop where
  | tot (n m : Nat) : TotalRelation n m

theorem total_relation_is_total (n m : Nat) : TotalRelation n m := by
  constructor

--  ### Exercise (2 stars): empty_relation (Optional) ⭐⭐

--  Define an inductive binary relation `empty_relation` (on numbers) that
--  never holds.

inductive EmptyRelation : Nat → Nat → Prop where
-- /SOLUTION

theorem empty_relation_is_empty (n m : Nat) : ¬ EmptyRelation n m := by
  intro contra; inversion contra

--  ## Additional Exercises

--  ### Exercise (3 stars): nostutter_defn (Manually graded) ⭐⭐⭐

--  Formulating inductive definitions of properties is an important skill
--  you'll need in this course. Try to solve this exercise without any
--  help.
--
--  We say that a list "stutters" if it repeats the same element
--  consecutively. (This is different from not containing duplicates: the
--  sequence `[1, 4, 1]` has two occurrences of the element `1` but does
--  not stutter.) The property `NoStutter l` means that `l` does not
--  stutter. Formulate an inductive definition for `NoStutter`.

inductive NoStutter {α : Type} : List α → Prop where
  | nostutter0: NoStutter []
  | nostutter1 {x : α} : NoStutter (x :: [])
  | nostutter2 {x y : α} {l : List α}
    (hneq : x ≠ y) (h : NoStutter (y :: l)) :
    NoStutter (x :: y :: l)
 -- /SOLUTION

--  Make sure each of these tests succeeds, but feel free to change the
--  suggested proof (in comments) if the given one doesn't work for you.
--  Your definition might be different from ours and still be correct, in
--  which case the examples might need a different proof. (You'll notice
--  that the suggested proofs use a number of tactics we haven't talked
--  about, to make them more robust to different possible ways of defining
--  `NoStutter`. You can probably just uncomment and use them as-is, but
--  you can also prove each example with more basic tactics.)

example : NoStutter [3, 1, 4, 1, 5, 6] := by
  constructor; intro contra; contradiction
  constructor; intro contra; contradiction
  constructor; intro contra; contradiction
  constructor; intro contra; contradiction
  constructor; intro contra; contradiction
  constructor

example : NoStutter (@List.nil Nat) := by
  constructor

example :  NoStutter [5] := by
  constructor

example : ¬ (NoStutter [3, 1, 1, 4]) := by
  intro contra; inversion contra with
  | nostutter2 _ contra =>
    inversion contra with
    | nostutter2 _ h _ =>
      apply h
      rfl

--  ### Exercise (4 stars): filter_challenge (Advanced) ⭐⭐⭐⭐

--  Let's prove that our definition of `filter` from the Poly chapter
--  matches an abstract specification. Here is the specification, written
--  out informally in English:
--
--  A list `l` is an "in-order merge" of `l₁` and `l₂` if it contains all
--  the same elements as `l₁` and `l₂`, in the same order as `l₁` and `l₂`,
--  but possibly interleaved. For example,
--
--      [1, 4, 6, 2, 3]
--
--  is an in-order merge of
--
--      [1, 6, 2]
--
--  and
--
--      [4, 3].
--
--  Now, suppose we have a type `α`, a function `test : α → Bool`, and a
--  list `l` of type `List α`. Suppose further that `l` is an in-order
--  merge of two lists, `l₁` and `l₂`, such that every item in `l₁`
--  satisfies `test` and no item in `l₂` satisfies test. Then
--  `filter test l = l₁`.
--
--  First define what it means for one list to be a merge of two others. Do
--  this with an `inductive` relation, not a `def`.

inductive Merge {α:Type} : List α → List α → List α → Prop where
  | merge_empty : Merge [] [] []
  | merge_left {x : α} {l₁ l₂ l₃ : List α}
    (h : Merge l₁ l₂ l₃) :
    Merge (x :: l₁) l₂ (x :: l₃)
  | merge_right {x : α} {l₁ l₂ l₃ : List α}
    (h : Merge l₁ l₂ l₃) :
    Merge l₁ (x :: l₂) (x :: l₃)

theorem merge_filter (α : Type) (test : α → Bool) (l l₁ l₂ : List α)
  (hmerge : Merge l₁ l₂ l)
  (h₁ : List.all l₁ test)
  (h₂ : List.all l₂ (!test ·)) :
  List.filter test l = l₁ := by
  induction hmerge with
  | merge_empty => rfl
  | merge_left h' ih =>
    rw [List.all_cons, Bool.and_eq_true] at h₁
    obtain ⟨htest, h₁⟩ := h₁
    rw [List.filter_cons_of_pos htest];
    congr 1; apply ih
    . assumption
    . assumption
  | merge_right h' ih =>
    rw [List.all_cons, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h₂
    obtain ⟨htest, h₂⟩ := h₂
    rw [List.filter_cons_of_neg (ne_true_of_eq_false htest)]
    congr 1; apply ih
    . assumption
    . assumption

--  ### Exercise (5 stars): filter_challenge_2 (Advanced, Optional) ⭐⭐⭐⭐⭐

--  A different way to characterize the behavior of `filter` goes like
--  this: Among all subsequences of `l` with the property that `test`
--  evaluates to `true` on all their members, `filter test l` is the
--  longest. Formalize this claim and prove it.

namespace Sol
/- We reproduce the definition of subseq here, in a module
    so it doesn't conflict. -/

inductive Subseq {α : Type} : List α → List α → Prop where
  | sub_nil {l : List α} : Subseq [] l
  | sub_take {x : α} {l₁ l₂ : List α}
    (h : Subseq l₁ l₂) :
    Subseq (x :: l₁) (x :: l₂)
  | sub_skip {x : α} {l₁ l₂ : List α}
    (h : Subseq l₁ l₂) :
    Subseq l₁ (x :: l₂)

/- A few lemmas about subseq. -/
namespace Subseq

theorem drop_l {α} (x : α) (l₁ l₂ : List α)
    (h : Subseq (x :: l₁) l₂) : Subseq l₁ l₂ := by
  induction l₂ generalizing l₁ with
  | nil => inversion h
  | cons _ _ ih =>
    inversion h with
    | sub_take hs =>
      constructor; assumption
    | sub_skip hs =>
      constructor; apply ih; assumption

theorem drop {α} (x : α) (l₁ l₂ : List α)
    (h : Subseq (x :: l₁) (x :: l₂)) : Subseq l₁ l₂ := by
  inversion h with
  | sub_take => assumption
  | sub_skip => apply drop_l; assumption

end Subseq

/-- A list is _maximal_ with property `P` if it has the property, and
    every other list with the property is at most as long as it is. -/
def Maximal {α : Type} (lmax : List α) (P : List α → Prop) : Prop :=
  P lmax ∧ ∀ l', P l' → l'.length ≤ lmax.length

/-- A "good subsequence" for a given list `l` and a `test` is a
    subsequence of `l` all of whose members evaluate to `true` under
    the `test`. -/
def GoodSubseq {α : Type} (test : α → Bool) (l lsub : List α) :=
  Subseq lsub l ∧ List.all lsub test

/-- Good subsequences can be extended with good elements. -/
theorem good_subseq_extend (α : Type) (x : α)
    (l lsub : List α) (test : α → Bool) (hx : test x) :
    GoodSubseq test l lsub →
    GoodSubseq test (x :: l) (x :: lsub) := by
  intro ⟨hsub, hall⟩; constructor
  . constructor; assumption
  . rw [List.all_cons, Bool.and_eq_true]; constructor
    . assumption
    . assumption

/-- If `lmax` is a maximal good subsequence of `x :: l` and `x` is not good,
    then `lmax` is also a maximal good subsequence of `l`. -/
theorem maximal_strengthening (α : Type) (x : α)
    (lmax l : List α) (test : α → Bool) (hx : !test x) :
    Maximal lmax (GoodSubseq test (x :: l)) →
    Maximal lmax (GoodSubseq test l) := by
  intro ⟨⟨hsub, hall⟩, hlen⟩; constructor; constructor
  . inversion hsub with
    | sub_nil => constructor
    | sub_take l₁ hsub =>
      rw [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨ht, _⟩ := hall
      rw [Bool.not_eq_eq_eq_not, Bool.not_true] at hx
      rw [hx] at ht; contradiction
    | sub_skip => assumption
  . assumption
  . intro l ⟨hsub', hall'⟩; apply hlen; constructor
    . constructor; assumption
    . assumption

/- Some easy lemmas about filter: its result is a good subsequence of
    the original list. -/

theorem filter_subseq (α : Type) (l : List α) (test : α → Bool) :
    Subseq (List.filter test l) l := by
  induction l with
  | nil => rw [List.filter_nil]; constructor
  | cons hd tl ih =>
    cases h : (test hd)
    . rw [List.filter_cons_of_neg (ne_true_of_eq_false h)]; constructor; assumption
    . rw [List.filter_cons_of_pos h]; constructor; assumption

theorem filter_all (α : Type) (l : List α) (test : α → Bool) :
    List.all (List.filter test l) test := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases h : (test hd)
    . rw [List.filter_cons_of_neg (ne_true_of_eq_false h)]; assumption
    . rw [List.filter_cons_of_pos h, List.all_cons, Bool.and_eq_true]; constructor
      . assumption
      . assumption

/- And now for the main theorem: `lsub` is a maximal good subsequence
    of `l` if and only if `filter test l = lsub` -/
/- LATER: This could use a lot of cleanup... -/
theorem filter_spec2 (α : Type) (l lsub : List α) (test : α → Bool) :
    Maximal lsub (GoodSubseq test l) ↔ List.filter test l = lsub := by
  apply Iff.intro
  . induction l generalizing lsub with
    | nil =>
      intro ⟨⟨hsub, hall⟩, hlen⟩
      inversion hsub
      rw [List.filter_nil]
    | cons hd tl ih =>
      cases htest : test hd with
      | false =>
        rw [List.filter_cons_of_neg]
        . intro hmax; apply ih
          apply maximal_strengthening _ _ _ _ _ _ hmax
          rw [Bool.not_eq_eq_eq_not, Bool.not_true]
          assumption
        . exact ne_true_of_eq_false htest
      | true =>
        intro ⟨⟨hsub, hall⟩, hlen⟩
        rw [List.filter_cons_of_pos htest]
        /- in this case, lsub must begin with hd, since otherwise it
        wouldn't be maximal. -/
        cases lsub with
        | nil => -- lsub = [] (impossible: contradicts maximality of lsub)
          have contra : [hd].length ≤ ([] : List α).length := by
            apply hlen; constructor
            . constructor; constructor
            . rw [List.all_cons, List.all_nil, Bool.and_true]; assumption
          contradiction
        | cons hd' tl' =>
          have heq : hd = hd' := by -- because of maximality again
            inversion hsub with
            | sub_take hsub => rfl
            | sub_skip hsub =>
            -- contradiction, since hd :: hd' :: tl' would be longer
              have contra : (hd :: hd' :: tl').length ≤ (hd' :: tl').length := by
                apply hlen; constructor
                . constructor; assumption
                . rw [List.all_cons, List.all_cons, Bool.and_eq_true, Bool.and_eq_true]
                  rw [List.all_cons, Bool.and_eq_true] at hall
                  constructor; assumption; assumption
              rw [List.length_cons, List.length_cons, Nat.add_le_add_iff_right] at contra
              apply Nat.not_add_one_le_self at contra
              contradiction
          subst heq; congr; apply ih; constructor; constructor
          . exact hsub.drop hd _ _
          . rw [List.all_cons, Bool.and_eq_true] at hall
            obtain ⟨_, _⟩ := hall; assumption
          . intro l' hgood; rw [List.length_cons] at hlen
            apply succ_n_le_succ_m__n_le_m
            apply hlen (hd :: l')
            exact good_subseq_extend _ _ _ _ _ htest hgood
  . intro hfilter; constructor; rw [← hfilter]; constructor
    . apply filter_subseq
    . apply filter_all
    . intro l' ⟨hsub, hall⟩
      induction l generalizing l' lsub with
      | nil =>
        inversion hsub; rw [List.length_nil]
        apply zero_le_n
      | cons hd tl ih =>
        cases htest : test hd with
        | false =>
          rw [List.filter_cons_of_neg] at hfilter
          . apply ih _ hfilter _ _ hall
            inversion hsub with
            | sub_nil => constructor
            | sub_take l hsub =>
              rw [List.all_cons, Bool.and_eq_true] at hall
              obtain ⟨ht, _⟩ := hall
              rw [ht] at htest
              contradiction
            | sub_skip hsub => assumption
          . exact ne_true_of_eq_false htest
        | true =>
          rw [List.filter_cons_of_pos htest] at hfilter
          rw [← hfilter, List.length_cons]
          inversion hsub with
          | sub_nil => rw [List.length_nil]; apply zero_le_n
          | sub_take l hsub =>
            rw [List.length_cons]; apply n_le_m__succ_n_le_succ_m
            apply ih _ rfl _ hsub
            rw [List.all_cons, Bool.and_eq_true] at hall
            obtain ⟨_, _⟩ := hall
            assumption
          | sub_skip hsub =>
            apply Nat.le_succ_of_le
            exact ih _ rfl _ hsub hall
end Sol

--  ### Exercise (4 stars): palindromes (Optional) ⭐⭐⭐⭐

--  A palindrome is a sequence that reads the same backwards as forwards.
--
--  - Define an inductive proposition `Pal` on `List α` that captures what
--    it means to be a palindrome. (Hint: You'll need three cases.)
--
--  - Prove `pal_app_reverse`, which states that
--
--      ∀ l, Pal (l ++ l.reverse).
--
--  - Prove `pal_reverse`, which states that
--
--      ∀ l, Pal l → l = l.reverse.
--
--  For extra credit, try proving the same theorems with an alternate
--  definition with a *single* constructor of this type:
--
--      ∀ l, l = l.reverse → Pal l

--  Note to developers:
--      `HIDE: MTF 6/22: It isn't exactly clear why the single constructor approach
--      "will not work very well".  It seems to work extremely well:
--
--       inductive pal {α : Type} : List α → Prop :=
--         | palc : forall l, l = rev l → pal l.
--
--       theorem pal_app_reverse : forall (α:Type) (l : List α),
--         pal (l ++ (rev l)).
--       Proof.
--         intros α l.
--         apply palc.
--         rewrite rev_app_distr.
--         rewrite rev_involutive.
--         reflexivity.
--       Qed.
--
--       theorem pal_reverse : forall (α:Type) (l: List α) , pal l → l = rev l.
--       Proof.
--         intros α l H. destruct H. assumption.
--       Qed.
--
--       theorem palindrome_converse: forall {α: Type} (l: List α), l = rev l → pal l.
--       Proof.
--         intros α l H. apply palc. assumption.
--       Qed.
--
--         This seems to be yet another example of a property that can be expressed as a
--         non-inductive proposition being artificially formulated as an inductive
--         proposition.  Are there any other properties of the [palindrome] proposition
--         that would be difficult to prove from its specification?
--
--      BCP 25: Took away the "will not work very well" wording.`

inductive Pal {α : Type} : List α → Prop where
  | pal_nil : Pal []
  | pal_one {x : α} : Pal [x]
  | pal_consnoc {x : α} {l : List α} (h : Pal l) : Pal (x :: (l ++ [x]))

theorem pal_app_reverse (α : Type) (l : List α) :
    Pal (l ++ l.reverse) := by
  induction l with
  | nil => rw [List.reverse_nil, List.append_nil]; constructor
  | cons hd tl ih =>
    rw [List.reverse_cons, List.cons_append, ← List.append_assoc]
    constructor; assumption

theorem pal_reverse (α : Type) (l : List α) (hp : Pal l) : l = l.reverse := by
  induction hp with
  | pal_nil => rw [List.reverse_nil]
  | pal_one =>
    rw [List.reverse_cons, List.reverse_nil, List.nil_append]
  | pal_consnoc h ih =>
    rw [List.reverse_cons, List.reverse_append, ← List.cons_append, ← ih]
    congr

--  Note to developers (Daniel Sainati @dsainati1, NOW):
--      This one is super annoying without simp. I propose we move it to
--      the simp chapter

--  ### Exercise (5 stars): palindrome_converse (Optional) ⭐⭐⭐⭐⭐

--  Again, the converse direction is significantly more difficult, due to
--  the lack of evidence. Using your definition of `Pal` from the previous
--  exercise, prove that
--
--      ∀ l, l = l.reverse → Pal l.

/- Proving the converse theorem is much harder, because a standard
    induction over the list `l` doesn't work.  The trick to the
    following proof, due to Nathan Collins, is to induct over _half
    the length_ of `l`.  We make heavy use of destruct and inversion
    to clear away the impossible cases. -/

theorem reverse_pal {α : Type} (n : Nat) (l : List α)
    (hlen : l.length / 2 = n) (hrev : l = l.reverse) : Pal l := by
  induction n generalizing l with
  /- (length l) / 2 = 0 || l has length 0 or 1 -/
  | zero =>
    cases l with
    | nil => constructor
    | cons _ l =>
      cases l with
      | nil => constructor
      | cons _ l' =>
        /- impossible : l has length > 1 -/
        rw [List.length_cons, List.length_cons] at hlen
        rw [Nat.div_eq_zero_iff] at hlen
        cases hlen; contradiction; contradiction
  /- (length l) / 2 >= 1  || l has length at least 2 -/
  | succ n ih =>
    cases l with
    | nil => rw [List.length_nil, Nat.zero_div] at hlen; contradiction
    | cons x l =>
      rw [List.length_cons] at hlen
      rw [List.reverse_cons] at hrev
      cases heq : l.reverse with
      | nil =>
        have h : l = [] := by
          cases l; rfl
          simp only [List.reverse_cons, List.append_eq_nil_iff] at heq
          obtain ⟨_, _⟩ := heq; contradiction
        rw [h]; constructor
      | cons y l' =>
        rw [heq] at hrev
        injections hrev heqtl; subst hrev
        rw [heqtl, List.append_eq]
        constructor; apply ih
        . rw [heqtl] at hlen
          rw [List.append_eq, List.length_append, List.length_cons,
            List.length_nil, Nat.zero_add] at hlen
          omega
        . rw [heqtl, List.append_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.cons_append, List.nil_append] at heq
          injections _ _
          symm
          assumption


  /- And here's another solution due (modulo some fixes by BCP/AAA to
     replace snoc with app) to Michael Schulman. It uses a few tactics
     that we haven't seen yet.

  theorem eqrev_pal_gen (α : Type) : forall (l:List α) (p t:List α),
    l = p ++ t → p = rev p → pal p.
  Proof.
   induction l as [| x l'].
   - /- l = nil -/
     destruct p.
     + /- p = nil -/
       destruct t as [| x t'].
          * /- t = nil -/
            intros; constructor.
          * /- t = cons -/
            intros H; inversion H.
     + /- p = cons -/
       intros t H.
       inversion H.
   - /- l = cons -/
     destruct p as [| y p'].
     + /- p = nil -/
       intros. constructor.
     + /- p = cons -/
       intros t H K.
       inversion H.
       simpl in K.
       destruct (rev p') as [| z p''] eqn:Heqrevp'.
       * /- rev p' = nil -/
         destruct p' as [| w q].
         { /- p' = nil -/ constructor. }
         { /- p' = cons -/
           assert (L : [] = w :: q).
           { rewrite <- rev_involutive. rewrite  Heqrevp'. reflexivity. }
           inversion L. }
       * /- rev p' = cons -/
         assert (M : rev (rev p') = (rev p'') ++ [z]).
         { rewrite Heqrevp'. reflexivity. }
         rewrite rev_involutive in M.
         rewrite M.
         inversion K.
         /- Now we finally get to do -/
         constructor.
         apply (IHl' _ (z :: t)).
         { /- l' = rev p'' ++ z :: t -/
           rewrite h₂. rewrite M. rewrite <- app_assoc. reflexivity. }
         { /- rev p'' = rev (rev p'') -/
           rewrite H4 in Heqrevp'. rewrite rev_app_distr in Heqrevp'.
           inversion Heqrevp'.
           rewrite rev_involutive.
           symmetry. apply H5. } Qed.

  theorem eqrev_pal (α : Type) (l:List α) : (l = rev l) → pal l.
  Proof.
    intros H.
    apply (eqrev_pal_gen _ l l []).
    rewrite app_nil_r. reflexivity.
    apply H.
  Qed.

  /- A final possibility is adding a natural number n and a hypothesis
     "length l ≤ n" and inducting on n.  The following solution by
     Mihir Mehta follows this strategy... -/

  theorem palindrome_converse_lemma_1:
    forall {α: Type} (l: List α), length (rev l) = length l.
  Proof. {
    intros α. induction l.
    { reflexivity. }
    { simpl. rewrite → app_length. rewrite → IHl. simpl.
      rewrite → add_comm. reflexivity. }
  } Qed.

  theorem palindrome_converse_lemma_2:
    forall {α: Type} (n: nat) (l: List α), (length l ≤ n) → l = rev l → pal l.
  Proof. {
    intros α. induction n as [| n'].
    { /- n = 0 -/
      intros [| x l'] h₁ h₂.
      { /- l = [] -/ apply pal_nil. }
      { /- l = x :: l' -/ inversion h₁. }
    }
    { /- n = S n'-/
      intros [| x l'] h₃ H4.
      { /- l = [] -/ apply pal_nil. }
      { /- l = x :: l' -/
        simpl in H4.
        destruct (rev l') as [| x' l''] eqn:H5.
        { /- rev l = [] -/
          rewrite <- (rev_involutive α l'). rewrite → H5. simpl.
          apply pal_one. }
        { /- rev l = x' :: l'' -/
          inversion H4 as [[H6 H7]]. apply pal_consnoc. apply (IHn' l'').
          { /- proving: length l'' ≤ n' -/
            rewrite → H7 in h₃. simpl in h₃.
            rewrite → app_length in h₃. simpl in h₃.
            rewrite → add_comm in h₃. simpl in h₃.
            apply Sn_le_Sm__n_le_m, Sn_le_Sm__n_le_m.
            apply le_S. apply h₃.
          }
          { /- proving l'' = rev l'' -/
            rewrite → H7 in H5. rewrite → rev_app_distr in H5. simpl in H5.
            inversion H5 as [H8]. rewrite → H8, → H8. reflexivity.
          }
        }
      }
    }
  } Qed. -/

theorem palindrome_converse {α : Type} (l : List α) (h : l = l.reverse) : Pal l := by
  exact reverse_pal _ _ rfl h

--  ### Exercise (4 stars): NoDup (Advanced, Optional, Manually graded) ⭐⭐⭐⭐

--  Use the `∈` property to define a proposition `Disjoint l₁ l₂`, which
--  should be provable exactly when `l₁` and `l₂` are lists (with elements
--  of type `α`) that have no elements in common.

def Disjoint {α : Type} (l₁ l₂ : List α) : Prop :=
  ∀ (x : α), x ∈ l₁ → ¬ x ∈ l₂

--  Next, use `∈` to define an inductive proposition `NoDup l`, which
--  should be provable exactly when `l` is a list (with elements of type
--  `α`) where every member is different from every other. For example,
--  `NoDup ([1, 2, 3, 4] : List Nat)` and `NoDup ([] : List Bool)` should
--  be provable, while `NoDup ([1, 2, 1] : List Nat)` and
--  `NoDup ([true, true] : List Bool)` should not be.

inductive NoDup {α : Type} : List α → Prop where
  | NoDup_nil : NoDup []
  | NoDup_cons {x : α} {l : List α}
    (hnin : ¬ x ∈ l) (h : NoDup l) : NoDup (x :: l)

--  Finally, state and prove one or more interesting theorems relating
--  `Disjoint`, `NoDup` and `++` (list append).

/- Here are some possible answers: -/

theorem NoDup_append (α : Type) (l₁ l₂: List α)
    (h₁ : NoDup l₁) (h₂ : NoDup l₂) (hdis : Disjoint l₁ l₂) :
    NoDup (l₁ ++ l₂) := by
  induction l₁ generalizing l₂ with
  | nil => rw [List.nil_append]; assumption
  | cons hd tl ih =>
    constructor
    . intro contra; rw [List.append_eq, List.mem_append] at contra
      cases contra with
      | inl =>
        inversion h₁ with
        | _ hdup hin => apply hin; assumption
      | inr contra =>
        apply hdis hd _ contra
        rw [List.mem_cons]; left; rfl
    . apply ih _ _ h₂ _
      . inversion h₁; assumption
      . intros x hin
        apply hdis; rw [List.mem_cons]
        right; assumption

theorem NoDup_Disjoint (α : Type) (l₁ l₂: List α)
    (h : NoDup (l₁++l₂)) : Disjoint l₁ l₂ := by
  intro x hin contra
  induction l₁ generalizing l₂ x with
  | nil => rw [List.mem_nil_iff] at hin; contradiction
  | cons hd tl ih =>
    rw [List.mem_cons] at hin
    inversion h with
    | NoDup_cons hdup hnin =>
      cases hin with
      | inl hin =>
        subst hin; apply hnin
        rw [List.append_eq, List.mem_append]; right; assumption
      | inr hin => exact ih _ hdup _ hin contra

/- We can also show the following results about [NoDup] and [++]
   by themselves -/
theorem NoDup_left (α : Type) (l₁ l₂: List α)
    (hdup : NoDup (l₁ ++ l₂)) : NoDup l₁ := by
  induction l₁ generalizing l₂ with
  | nil => constructor
  | cons hd tl ih =>
    inversion hdup with
    | _ hdup' hin =>
      constructor
      . intro contra; apply hin
        rw [List.append_eq, List.mem_append]; left; assumption
      . exact ih _ hdup'

theorem NoDup_right (α : Type) (l₁ l₂ : List α)
    (hdup : NoDup (l₁ ++ l₂)) : NoDup l₂ := by
  induction l₁ generalizing l₂ with
  | nil => rw [List.nil_append] at hdup; assumption
  | cons hd tl ih =>
    inversion hdup
    apply ih; assumption

/- This theorem combines the various lemmas to give a complete
   characterization -/
theorem NoDup_Disjoint_app {α : Type} (l₁ l₂ : List α) :
    NoDup (l₁ ++ l₂) ↔
    (NoDup l₁ ∧ NoDup l₂ ∧ Disjoint l₁ l₂) := by
  apply Iff.intro
  . intro hdup
    constructor; exact NoDup_left _ _ _ hdup
    constructor; exact NoDup_right _ _ _ hdup
    exact NoDup_Disjoint _ _ _ hdup
  . intro ⟨h₁, ⟨h₂, h₃⟩⟩
    exact NoDup_append _ _ _ h₁ h₂ h₃

--  ### Exercise (5 stars): pigeonhole_principle (Advanced, Optional) ⭐⭐⭐⭐⭐

--  The *pigeonhole principle* states a basic fact about counting: if we
--  distribute more than `n` items into `n` pigeonholes, some pigeonhole
--  must contain at least two items. As often happens, this apparently
--  trivial fact about numbers requires non-trivial machinery to prove, but
--  we now have enough...
--
--  First prove an easy and useful lemma.

theorem mem_split (α : Type) (x : α) (l : List α) (hin : x ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  induction l generalizing x with
  | nil => rw [List.mem_nil_iff] at hin; contradiction
  | cons hd tl ih =>
    rw [List.mem_cons] at hin
    cases hin with
    | inl hin => subst hin; exists []; exists tl
    | inr hin =>
      have ⟨l₁', ⟨l₂', ih⟩⟩ := ih x hin
      subst ih
      exists hd :: l₁'; exists l₂'

--  Now define a property `Repeats` such that `Repeats l` asserts that `l`
--  contains at least one repeated element.

inductive Repeats {α : Type} : List α → Prop where
  | rep_here  {x : α} {l : List α} (h : x ∈ l)     : Repeats (x :: l)
  | rep_later {x : α} {l : List α} (h : Repeats l) : Repeats (x :: l)
-- /SOLUTION

--  Now, here's a way to formalize the pigeonhole principle. Suppose list
--  `l₂` represents a list of pigeonhole labels, and list `l₁` represents
--  the labels assigned to a list of items. If there are more items than
--  labels, at least two items must have the same label -- i.e., list `l₁`
--  must contain repeats.
--
--  This proof is much easier if you use the excluded middle to show that
--  `∈` is decidable, i.e., `∀ x l, (x ∈ l) ∨ ¬ (x ∈ l)`. Remember the
--  `by_cases` tactic from Logic!

--  Note to developers:
--      HIDE: APT21: Apparently, this is really quite hard; even the
--      strongest students couldn't do it this year.

theorem pigeonhole_principle (α : Type) (l₁ l₂ : List α)
    (hin : ∀ x, x ∈ l₁ → x ∈ l₂)
    (hlen : l₂.length < l₁.length) :
    Repeats l₁ := by
  induction l₁ generalizing l₂ with
  | nil =>
    rw [List.length_nil] at hlen
    apply Nat.not_lt_zero at hlen
    contradiction
  | cons x l₁' ih =>
    by_cases h : x ∈ l₁'
    . constructor; assumption
    . apply Repeats.rep_later
      have h₂ : x ∈ l₂ := by
        apply hin; rw [List.mem_cons]; left; rfl
      have ⟨l₂a, ⟨l₂b, heq⟩⟩ := mem_split _ _ _ h₂
      have hin₂ : ∀ x' : α, x' ∈ l₁' -> x' ∈ (l₂a ++ l₂b) := by
        intro x₀ hin₀
        have hneq : x ≠ x₀ := by
          intro heq; subst heq; apply h; assumption
        have h₁ : x₀ ∈ l₂ := by
          apply hin; rw [List.mem_cons]; right; assumption
        rw [heq, List.mem_append] at h₁; rcases h₁ with h₁ | h₁
        . rw [List.mem_append]; left; assumption
        . rw [List.mem_append]; right;
          rw [List.mem_cons] at h₁; rcases h₁ with h₁ | h₁
          . subst h₁; contradiction
          . assumption
      have hlen₂ : (l₂a ++ l₂b).length < l₁'.length := by
        have hlen' : l₂.length = (l₂a ++ l₂b).length + 1 := by
          rw [heq, List.length_append, List.length_append, List.length_cons, Nat.add_assoc]
        rw [hlen', List.length_append, List.length_cons] at hlen
        rw [List.length_append]
        apply succ_n_le_succ_m__n_le_m
        exact hlen
      apply ih (l₂a ++ l₂b) hin₂ hlen₂
    /-.
        destruct (EM (In x l1')) as [H | H].
        + /- In x l1' -/
          apply rep_here. apply H.
        + /- ~ In x l1' -/
          apply rep_later.
          assert (INX: In x l₂).
          {  apply INC. left. reflexivity. }
          destruct (in_split _ _ _ INX) as [l2a [l2b EQ]].
          remember (l2a ++ l2b) as l2' eqn:Heql2'.
          assert (IN2: forall x0 : α, In x0 l1' → In x0 l2').
          { intros x0 AI.
            assert (H0: x <> x0).
            { intros Heq. apply H. rewrite  Heq. apply AI. }
            assert (h₁: In x0 l₂).
            { apply INC. simpl. right. apply AI. }
            rewrite EQ in h₁. apply In_app_iff in h₁.
            rewrite Heql2'. apply In_app_iff.
            simpl in h₁. destruct h₁ as [h₁ | [h₁ | h₁]].
            - left. apply h₁.
            - exfalso. apply H0. apply h₁.
            - right. apply h₁.  }
          assert (LEN2: length l2' < length l1').
          { assert (LS: length l₂ = S(length (l2a ++ l2b))).
            { rewrite EQ.
              rewrite app_length. rewrite app_length. rewrite add_comm.
              simpl. rewrite add_comm. reflexivity. }
            rewrite LS in NR. rewrite <- Heql2' in NR. simpl in NR.
            apply Sn_le_Sm__n_le_m.  apply NR.
          }
          apply (IHl1' l2' IN2 LEN2).
  Qed. -/

--  /- Here's a clever alternative proof, based heavily on one by Daniel
--      Schepler (<dschepler@gmail.com> Coq club mailing list on Wed, 02 Oct
--      2013 02:02:12 -0700), that doesn't use decidability of [In], and hence
--      doesn't need [excluded_middle]. -/
--
--  /- First, some more auxiliary lemmas, some of which are a bit ad hoc. -/
--
--  theorem in_repeats: forall {α:Type} (l₁ l₂:List α) (x:α),
--    In x (l₁++l₂) →
--    repeats (l₁++x::l₂).
--  Proof.
--    intros α l₁. induction l₁ as [|y l1' IHl1'].
--    - /- l₁ = [] -/
--      intros l₂ x AI. simpl in AI. simpl. apply rep_here. apply AI.
--    - /- l₁ = y::l1' -/
--      intros l₂ x AI. simpl in AI. simpl. destruct AI as [AI | AI].
--      + apply rep_here. apply In_app_iff. right. left.
--        rewrite AI. reflexivity.
--      + apply rep_later. apply IHl1'. apply AI.
--  Qed.
--
--  theorem rep_insert: forall {α:Type} (l₁ l₂:List α) (x: α),
--    repeats (l₁ ++ l₂) → repeats (l₁ ++ x::l₂).
--  Proof.
--    intros α l₁. induction l₁ as [| y l1' IHl1'].
--    - /- l₁ = [] -/
--      intros l₂ x H. simpl. simpl in H. apply rep_later.  apply H.
--    - /- l₁ = y::l1' -/
--      intros l₂ x H. simpl. simpl in H. inversion H.
--      + /- rep_here -/
--        apply rep_here. apply In_app_iff. apply In_app_iff in h₁.
--        destruct h₁ as [h₁ | h₁].
--        * left. apply h₁.
--        * right. right. apply h₁.
--      + /- rep_later -/
--        apply rep_later. apply IHl1'. apply h₁.
--  Qed.
--
--  theorem repeats_app_comm : forall {α:Type} (l₁ l₂:List α),
--    repeats (l₁++l₂) → repeats(l₂++l₁).
--  Proof.
--    intros α l₁. induction l₁ as [|x l1'].
--    - /- l₁ = [] -/
--      intros l₂ H.  rewrite app_nil_r. simpl in H. apply H.
--    - /- l₁ = x::l1' -/
--      intros l₂ H. simpl in H. inversion H.
--      + /- rep_here -/
--        apply in_repeats. apply In_app_iff.
--        apply In_app_iff in h₁.
--        destruct h₁ as [h₁ | h₁].
--        * right. apply h₁.
--        * left. apply h₁.
--      + /- rep_later -/
--        apply IHl1' in h₁. apply rep_insert. apply h₁.
--  Qed.
--
--  /- Now the main lemma: -/
--
--  theorem pigeonhole_principle_aux: forall {α:Type} (l₁ l₂ ls: List α),
--    (forall x:α, In x l₁ → In x (ls++l₂)) →
--    length l₂ < length l₁ → repeats (ls++l₁).
--  Proof.
--    intros α l₁. induction l₁ as [|x l1' IHl1'].
--    - /- l₁ = [] -/
--      intros l₂ ls AI LT. inversion LT.
--    - /- l₁ = x::l1' -/
--      intros l₂ ls AI LT.
--      assert (In x (ls++l₂)).
--      { /- Proof of assertion -/
--        apply AI. left. reflexivity. }
--      assert (In x ls \/ In x l₂).
--      { /- Proof of assertion -/
--        apply In_app_iff. apply H. }
--      destruct H0.
--      + /- In x ls -/
--        apply repeats_app_comm. simpl. apply rep_here.
--        apply In_app_iff. right. apply H0.
--      + /- In x l₂ -/
--        apply in_split in H0.
--        destruct H0 as [l2a [l2b P]]. rewrite P in *.
--        assert (repeats ((x::ls) ++ l1')).
--        * /- Proof of assertion -/
--          apply (IHl1' (l2a++l2b) (x::ls)).
--          { /- re-establish inclusion relation -/
--            intros x0 AI'.
--            assert (In x0 (ls ++ l2a ++ x::l2b)).
--            { /- Proof of assertion -/
--              apply AI. right. apply AI'. }
--            apply In_app_iff in H0. inversion H0.
--              apply In_app_iff.  left. right. apply h₁.
--              apply In_app_iff in h₁. inversion h₁.
--                apply In_app_iff. right.
--                  apply In_app_iff. left. apply h₂.
--                inversion h₂.
--                  simpl. left. apply h₃.
--                  apply In_app_iff. right.
--                    apply In_app_iff. right. apply h₃. }
--          rewrite app_length in LT.  rewrite app_length.
--          simpl in LT. rewrite <- plus_n_Sm in LT.
--          unfold lt. unfold lt in LT. apply le_S_n. apply LT.
--        * simpl in H0. apply repeats_app_comm. simpl. inversion H0.
--          { apply rep_here. apply In_app_iff.
--            apply In_app_iff in h₂. inversion h₂.
--            - right. apply H4.
--            - left. apply H4. }
--          apply rep_later. apply repeats_app_comm. apply h₂.
--  Qed.
--
--  theorem stronger_pigeonhole_principle: forall {α:Type} (l₁ l₂ : List α),
--    (forall x : α, In x l₁ → In x l₂) →
--    length l₂ < length l₁ →
--    repeats l₁.
--  Proof.
--    intros α l₁ l₂ AI LT.
--    assert (H: l₁ = nil ++ l₁). { reflexivity. }
--    rewrite H. apply (pigeonhole_principle_aux l₁ l₂ nil).
--    simpl. apply AI. apply LT.
--  Qed.
--
--  /- One key to how this proof works is that at the inductive step,
--      when we re-establish the inclusion relation, the contents on the
--      list on the right-hand side of the inclusion have not changed at
--      all---they are merely re-arranged, so validity of the inclusion is
--      trivial (modulo some messy book-keeping). Compare this to the
--      equivalent step in the original proof, where we remove [x] from the
--      list on the right-hand side of the inclusion; this is only valid when
--      we know that [x] is not in the left-hand list [l1'] either---exactly
--      the knowledge that we get from decidability of [In], and cannot get
--      any other way. -/
--
--  /- ------------------------ -/
--
--  /- Finally, here is a much more elegant proof due to N. Raghavendra
--      <raghu@hri.res.in>, based on Daniel's.  It uses the following
--      sequence of observations:
--
--        theorem app_ass :
--        forall (α : Type) (l₁ l₂ l₃ : List α),
--          (l₁ ++ l₂) ++ l₃ = l₁ ++ l₂ ++ l₃.
--
--        theorem app_length :
--        forall (α : Type) (l₁ l₂ : List α),
--          length (l₁ ++ l₂) = length l₁ + length l₂.
--
--        theorem In_app_iff_split :
--        forall (α : Type) (x : α) (l : List α),
--          In x l →
--          exists (l₁ l₂ : List α), l = l₁ ++ x :: l₂.
--
--        theorem In_both_impl_repeats_app :
--        forall (α : Type) (x : α) (l₁ l₂ : List α),
--          In x l₁ → In x l₂ → repeats (l₁ ++ l₂).
--
--        theorem In_app_iff_midswap :
--        forall (α : Type) (x : α) (l₁ l₂ l₃ l4 : List α),
--          In x (l₁ ++ l₂ ++ l₃ ++ l4) →
--          In x (l₁ ++ l₃ ++ l₂ ++ l4).
--
--        theorem pigeonhole_principle_aux :
--        forall (α : Type) (l₁ l₂ u : List α),
--          (forall x : α, In x l₁ → In x (u ++ l₂)) →
--          length l₂ < length l₁ → repeats (u ++ l₁).
--
--        theorem pigeonhole_principle :
--        forall (α : Type) (l₁ l₂ : List α),
--          (forall x : α, In x l₁ → In x l₂) →
--          length l₂ < length l₁ → repeats l₁.
--  -/
--
--  /- HIDE: Some of these are already proved elsewhere. Also, this
--    vertical style is hard to read. -/
--
--  Module Pigeon.
--
--  inductive repeats {α : Type} : List α → Prop :=
--    | repeats_1 (x : α) (l : List α)
--                (H : In x l) : repeats (x :: l)
--    | repeats_2 (x : α) (l : List α)
--                (H : repeats l) : repeats (x :: l).
--
--  Definition pigeonhole_principle_prop (α : Type) : Prop :=
--    forall l₁ l₂ : List α,
--      (forall x : α, In x l₁ → In x l₂) →
--      length l₂ < length l₁ → repeats l₁.
--
--  theorem app_ass :
--    forall (α : Type) (l₁ l₂ l₃ : List α),
--      (l₁ ++ l₂) ++ l₃ = l₁ ++ l₂ ++ l₃.
--
--  Proof.
--    intros α l₁ l₂ l₃.
--    induction l₁ as [ | h t IH].
--    {
--      - /- l₁ = nil -/
--      reflexivity.
--    }
--    {
--      - /- l₁ = h :: t -/
--      simpl.
--      rewrite → IH.
--      reflexivity.
--    }
--  Qed.
--
--  theorem app_length :
--    forall (α : Type) (l₁ l₂ : List α),
--      length (l₁ ++ l₂) = length l₁ + length l₂.
--
--  Proof.
--    intros α l₁ l₂.
--    induction l₁ as [ | h t IH].
--    {
--      - /- l₁ = nil -/
--      reflexivity.
--    }
--    {
--      - /- l₁ = h :: t -/
--      simpl.
--      rewrite → IH.
--      reflexivity.
--    }
--  Qed.
--
--  theorem In_both_impl_repeats_app :
--    forall (α : Type) (x : α) (l₁ l₂ : List α),
--      In x l₁ → In x l₂ → repeats (l₁ ++ l₂).
--
--  Proof.
--    intros α x l₁.
--    induction l₁ as [ | h₁ t1 IH].
--    {
--      - /- l₁ = nil -/
--      intros l₂ h₁ h₂.
--      inversion h₁.
--    }
--    {
--      - /- l₁ = h₁ :: t1 -/
--      intros l₂ h₁ h₂. simpl in h₁.
--      destruct h₁ as [h₃ | h₃].
--      {
--        +
--        simpl.
--        apply repeats_1.
--        apply In_app_iff.
--        right.
--        rewrite h₃.
--        apply h₂.
--      }
--      {
--        + /- h₁ = ai_later z u h₃ -/
--        simpl.
--        apply repeats_2.
--        apply IH.
--        {
--          apply h₃.
--        }
--        {
--          apply h₂.
--        }
--      }
--    }
--  Qed.
--
--  theorem In_app_iff_midswap :
--    forall (α : Type) (x : α) (l₁ l₂ l₃ l4 : List α),
--      In x (l₁ ++ l₂ ++ l₃ ++ l4) → In x (l₁ ++ l₃ ++ l₂ ++ l4).
--
--  Proof.
--    intros α x l₁ l₂ l₃ l4 H.
--    apply In_app_iff in H.
--    destruct H as [h₁ | h₁r].
--    {
--      - /- In x l₁ -/
--      apply In_app_iff.
--      left.
--      apply h₁.
--    }
--    {
--      - /- In x (l₂ ++ l₃ ++ l4) -/
--      apply In_app_iff in h₁r.
--      destruct h₁r as [h₂ | h₂r].
--      {
--        + /- In x l₁ -/
--        apply In_app_iff.
--        right.
--        apply In_app_iff.
--        right.
--        apply In_app_iff.
--        left.
--        apply h₂.
--      }
--      {
--        + /- In x (l₃ ++ l4) -/
--        apply In_app_iff in h₂r.
--        destruct h₂r as [h₃ | h₃r].
--        {
--          * /- In x l₃ -/
--          apply In_app_iff.
--          right.
--          apply In_app_iff.
--          left.
--          apply h₃.
--        }
--        {
--          * /- In x l4 -/
--          apply In_app_iff.
--          right.
--          apply In_app_iff.
--          right.
--          apply In_app_iff.
--          right.
--          apply h₃r.
--        }
--      }
--    }
--  Qed.
--
--  theorem pigeonhole_principle_aux :
--    forall (α : Type) (l₁ l₂ u : List α),
--      (forall x : α, In x l₁ → In x (u ++ l₂)) →
--      length l₂ < length l₁ → repeats (u ++ l₁).
--
--  Proof.
--    intros α l₁.
--    induction l₁ as [ | h₁ t1 IH].
--    {
--      - /- l₁ = nil -/
--      intros l₂ u h₁ h₂.
--      inversion h₂.
--    }
--    {
--      - /- l₁ = h₁ :: t1 -/
--      intros l₂ u h₁ h₂.
--      assert (h₃ : In h₁ (u ++ l₂)).
--      {
--        + /- Proof of h₃ -/
--        apply h₁.
--        left. reflexivity.
--      }
--      apply In_app_iff in h₃.
--      destruct h₃ as [h₃l | h₃r].
--      {
--        + /- In h₁ u -/
--        apply (In_both_impl_repeats_app _ h₁).
--        {
--          apply h₃l.
--        }
--        {
--          left. reflexivity.
--        }
--      }
--      {
--        + /- In h₁ l₂ -/
--        apply in_split in h₃r.
--        destruct h₃r as [v2 H4].
--        destruct H4 as [w2 H5].
--        assert (H6 : u ++ h₁ :: t1 = (u ++ [h₁]) ++ t1).
--        {
--          * /- Proof of H6 -/
--          rewrite → app_ass.
--          reflexivity.
--        }
--        rewrite → H6.
--        apply (IH (v2 ++ w2)).
--        {
--          * /- Proof of first condition of IH -/
--          intros x H7.
--          rewrite → app_ass.
--          apply In_app_iff_midswap.
--          simpl.
--          rewrite <- H5.
--          apply h₁.
--          right.
--          apply H7.
--        }
--        {
--          * /- Proof of second condition of IH -/
--          unfold lt.
--          assert (H8 : length l₂ = S (length (v2 ++ w2))).
--          {
--            rewrite → H5.
--            rewrite → app_length.
--            rewrite → app_length.
--            simpl.
--            rewrite <- plus_n_Sm.
--            reflexivity.
--          }
--          rewrite <- H8.
--          apply Sn_le_Sm__n_le_m.
--          unfold lt in h₂.
--          simpl in h₂.
--          apply h₂.
--        }
--      }
--    }
--  Qed.
--
--  theorem pigeonhole_principle :
--    forall α : Type,
--      pigeonhole_principle_prop α.
--
--  Proof.
--    intros α.
--    unfold pigeonhole_principle_prop.
--    intros l₁ l₂ h₁ h₂.
--    assert (H: l₁ = nil ++ l₁). { reflexivity. }
--    rewrite H.
--    apply (pigeonhole_principle_aux _ _ l₂).
--    {
--      intros x h₃.
--      simpl.
--      apply h₁.
--      apply h₃.
--    }
--    {
--      apply h₂.
--    }
--  Qed.
--
--  End Pigeon.

-- Built on 2026-09-02 21:06 UTC

import LF.SFLCompat

-- # Postscript

-- Congratulations: We've made it to the end of *Logical Foundations*!

-- ## Looking Back

-- We've covered quite a bit of ground so far. Here's a quick review...

-- - *Functional programming*:

--   - "declarative" programming style (recursion over immutable data structures,
--     rather than looping over mutable arrays or pointer structures)

--   - higher-order functions

--   - polymorphism

-- - *Logic*, the mathematical basis for software engineering:

-- logic                        calculus
-- --------------------   ~   ----------------------------
-- software engineering       mechanical/civil engineering

-- - inductively defined sets and relations
-- - inductive proofs
-- - proof objects

-- - *Lean*, an industrial-strength proof assistant
-- - functional core language
-- - core tactics
-- - automation

-- ## Looking Forward

-- OLD: If what you've seen so far has whetted your interest, you have several
-- choices for further reading in later volumes of the *Software Foundations*
-- series. Some of these are intended to be accessible to readers immediately
-- after finishing *Logical Foundations*; others require a few chapters from
-- Volume 2, *Programming Language Foundations*. The Preface chapter in each
-- volume gives details about prerequisites.

-- FINISH: As of August 2026, there are two more volumes written in Lean.

-- *Hoare Logic*: This short volume describes one of the primary methods for
-- reasoning about *imperative* programs- programs with state and mutation,
-- like C++, Java, C, and Assembly- in a pure logic like Lean's. This method,
-- called *Hoare Logic*, is embeddable into Lean's type system and is a
-- powerful tool for determining the correct behavior of imperative code.
-- Since most of the code in the wild today is imperative, this technique is
-- both well-established and popular among industry professionals who analyze
-- and fortify the correctness of systems.

-- *Type Systems*: Another tool for reasoning about the correctness of a
-- program is a *type system*. You have interacted thoroughly with Lean's rich
-- type system, which is one of the most complex in a modern programming
-- language. Most languages have type systems that are far less complex, but
-- which still provide incredibly useful guardrails against ill-behaved
-- programs. In this volume you will explore how to read, analyze, and design
-- type systems in a proof assistant.

-- ## Resources

-- Here are some other good places to learn more...

-- - This book includes some optional chapters covering topics that you may find
--   useful. Take a look at the #<a href="toc.html">#table of contents#</a># and
--   the #<a href="deps.html">#chapter dependency diagram#</a># to find them.

-- - For questions about Rocq, the `#coq` area of Stack Overflow
--   (<https://stackoverflow.com/questions/tagged/coq>) is an excellent
--   community resource.

-- - Here are some great books on functional programming

--   - Learn You a Haskell for Great Good, by Miran Lipovaca Lipovaca 2011.

--   - Real World Haskell, by Bryan O'Sullivan, John Goerzen, and Don Stewart
--     O'Sullivan 2008

--   - ...and many other excellent books on Haskell, OCaml, Scheme, Racket, Scala,
--     F sharp, etc., etc.

-- - And some further resources for Rocq:

--   - Certified Programming with Dependent Types, by Adam Chlipala Chlipala 2013.

--   - Interactive Theorem Proving and Program Development: Coq'Art: The Calculus
--     of Inductive Constructions, by Yves Bertot and Pierre Casteran Bertot 2004.

-- - If you're interested in real-world applications of formal verification to
--   critical software, see the Postscript chapter of *Programming Language
--   Foundations*.

-- - For applications of Rocq in building verified systems, the lectures and
--   course materials for the 2017 DeepSpec Summer School are a great resource.
--   <https://deepspec.org/event/dsss17/index.html>


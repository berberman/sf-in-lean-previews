import SFLCompat

--  # Preface

--  ## Welcome

--  This is Type Systems, volume 3 of *Software Foundations in Lean*. It
--  develops *type systems*: static checks for establishing that *all*
--  programs in a given language are well behaved, in contrast to Hoare
--  Logic, which develops techniques for reasoning about the behavior of a
--  *specific* program. The two volumes can be read in either order, and
--  both build on the material in Logical Foundations.

--  ## Overview

--  To reason about a program, we represent it as a mathematical object
--  together with a mathematical function or relation for describing its
--  behavior. Our main approach to doing so is called *operational
--  semantics*, and it amounts to defining a kind of *abstract interpreter*
--  for the programs in a language. We present two styles of operational
--  semantics: the *big-step* style specifies a program's behavior by
--  relating it directly to its final value, while the *small-step* style
--  specifies a program's behavior as a series of computational steps. The
--  small-step approach is more involved, but also makes it possible to
--  reason about a program's evaluation in a more fine-grained manner.
--
--  After introducing operational semantics using a simple language of
--  arithmetic and boolean expressions (Slang), we turn to *types*, the
--  volume's central subject. A type is a static classification of what a
--  program computes, and a *type system* is a static reasoning system that
--  uses types to rule out whole categories of run-time errors before a
--  program is ever run. Working with a small language of numbers and
--  booleans, we define a type system for it and prove the two signature
--  theorems of type-system metatheory — *progress* (a well-typed term is
--  either a value or can take a step) and *preservation* (taking a step
--  preserves well-typedness) — which together guarantee that a well-typed
--  program can never "go wrong."
--
--  Finally, we turn our attention to the *simply typed lambda-calculus*
--  (STLC), a much richer language with a more interesting type system. We
--  start from a small untyped core and extend it with numbers, pairs,
--  sums, lists, and general recursion, proving progress and preservation
--  anew for the extended language. We then study *subtyping*, a mechanism
--  that lets a term of one type stand in for a term of another — motivated
--  by the way record types behave in object-oriented languages — and prove
--  progress and preservation once more for a language with subtyping. In
--  so doing, we work our way up to a fairly full featured programming
--  language.

--  ## Practicalities

--  This volume assumes you already have Lean and VS Code set up as
--  described in the Logical Foundations Preface, and that you are
--  comfortable with the basic mechanics of working through an SFL chapter.
--  The exercises here have the same "advanced"/"optional" markings, and
--  star ratings.
--
--  Briefly (see the Logical Foundations Preface for detail), to get
--  started:
--
--  If you are using this book as part of a class, your instructor will
--  have created a "student" release for you; download and unzip it, open
--  the resulting directory in VS Code, and open a `.lean` file (e.g.,
--  `TS/Slang.lean`) to get started.
--
--  If you are reading on your own, clone the
--  [SF-in-Lean](https://github.com/plclub/sf-in-lean) repository and run
--  `make
--  ts-student` from the root directory to build the student version
--  of this volume; it is written to `_out/ts/student/`, with an `html/`
--  directory and a `lean/` directory, exactly as described for Logical
--  Foundations. Run `make
--  student` instead if you want all three volumes
--  built together.

--  ### Building on Your Own Copy of Logical Foundations

--  This project includes a copy of the Logical Foundations files that
--  chapters in this volume depend on, in their own `LF/` directory, so you
--  do not need a separate Logical Foundations download to build or read
--  this volume. If you have already worked through Logical Foundations and
--  would rather this volume build on your own work, copy the whole `LF/`
--  directory from your Logical Foundations download over this project's
--  `LF/` directory, then rebuild.
--
--  Exercises in this volume use the same star ratings, and the same
--  "advanced"/"optional" markings, described in the Logical Foundations
--  Preface.

--  ### Citation Format

--  If you want to refer to this volume in your own writing, please do so
--  as follows:

--  @book            {SFL:3,
--  author       =   {Mike Hicks and Benjamin C. Pierce and the SF-in-Lean team},
--  title        =   "Type Systems",
--  series       =   "Software Foundations in Lean",
--  volume       =   "3",
--  year         =   "2026",
--  publisher    =   "Electronic textbook",
--  note         =   {Version 0.1.0, \URL<https://github.com/plclub/sf-in-lean>}
--  }

--  ## For Potential Contributors

--  If you find things you'd like to help add or improve, your
--  contributions are welcome! To get started, clone the [SF-in-Lean git
--  repo](https://github.com/plclub/sf-in-lean) and have a look at
--  `ALPHA-TESTERS.md`.

--  ### Credits

--  **Leadership:** Mike Hicks and Benjamin C. Pierce lead the SF-in-Lean
--  project.
--
--  **Authors:** The Lean adaptation of *Software Foundations* was created
--  by Mike Hicks, Benjamin C. Pierce, One An, Roger Burtonpatel, Jonathan
--  Chan, Harry Goldstein, Niklas Halonen, Chris Henson, Kihong Heo, Yipeng
--  Liu, and Daniel Sainati
--
--  **... with contributions from** Luisa Cicolini, Michael Clarkson,
--  Robert Joseph, Sati, and Shriya Thakur
--
--  **... and gratitude to** David Thrane Christiansen, for helping us
--  understand the intricacies of Lean's Verso document preparation system.
--
--  **SF in Rocq:** The first three volumes of *Software Foundations in
--  Lean* (*Logical Foundations in Lean*, *Type Systems in Lean*, and
--  *Hoare Logic in Lean*) are adapted from the *Logical Foundations* and
--  *Programming Language Foundations* volumes of the original *Software
--  Foundations* series in Roqc, developed from 2008 to 2026 by a team of
--  authors and contributors led by Benjamin C. Pierce.
--
--  The original *Logical Foundations* was written by Benjamin C. Pierce,
--  Arthur Azevedo de Amorim, Chris Casinghino, Marco Gaboardi, Michael
--  Greenberg, Cătălin Hriţcu, Vilhelm Sjöberg, and Brent Yorgey, with
--  contributions from Loris D'Antoni, Andrew W. Appel, Arthur Charguéraud,
--  Michael Clarkson, Anthony Cowley, Jeffrey Foster, Dmitri Garbuzov, Olek
--  Gierczak, Michael Hicks, Ranjit Jhala, Ori Lahav, Yishuai Li, Greg
--  Morrisett, Jennifer Paykin, Mukund Raghothaman, Chung-chieh Shan,
--  Leonid Spesivtsev, Caleb Stanford, Andrew Tolmach, Philip Wadler,
--  Stephanie Weirich, Li-Yao Xia, and Steve Zdancewic.
--
--  The original *Programming Language Foundations* was written by Benjamin
--  C. Pierce, Arthur Azevedo de Amorim, Chris Casinghino, Marco Gaboardi,
--  Michael Greenberg, Cătălin Hriţcu, Vilhelm Sjöberg, Andrew Tolmach, and
--  Brent Yorgey with contributions from Loris D'Antoni, Andrew W. Appel,
--  Arthur Chargueraud, Michael Clarkson, Anthony Cowley, Jeffrey Foster,
--  Dmitri Garbuzov, Michael Hicks, Ranjit Jhala, Ori Lahav, Yishuai Li,
--  Greg Morrisett, Jennifer Paykin, Mukund Raghothaman, Chung-Chieh Shan,
--  Leonid Spesivtsev, Caleb Stanford, Philip Wadler, Stephanie Weirich,
--  Li-Yao Xia, and Steve Zdancewic.
--
--  **Funding:** Development of the original *Software Foundations* series
--  was supported, in part, by the National Science Foundation under the
--  NSF Expeditions grant 1521523, *The Science of Deep Specification*.

--  Note to developers (Benjamin Pierce @bcpierce00):
--      Other funding should be acknowledged here...

-- Source revision: b6f36ae, committed 2026-10-28 17:05 UTC

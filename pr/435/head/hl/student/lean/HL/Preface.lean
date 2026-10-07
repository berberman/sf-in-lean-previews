import SFLCompat

--  # Preface

--  ## Welcome

--  This is Hoare Logic, volume 2 of *Software Foundations in Lean*. It
--  develops formal techniques for reasoning about what programs do. For
--  example, with the techniques we present, one can prove that an
--  algorithm sorts an array or that a compiler optimization does not
--  incorrectly change the behavior of the program it optimizes. This
--  volume complements Type Systems, which develops techniques for
--  establishing properties of *all* programs written in a given language;
--  the two volumes can be read in either order, and both build on the
--  material in Logical Foundations.

--  ## Overview

--  To reason about a program, we first need a way of representing it as a
--  mathematical object, so that we can talk about it precisely, together
--  with a way of describing its behavior in terms of a mathematical
--  function or relation. Our main tool for this is *operational semantics*
--  in "big step" style, which is a method of specifying the meaning of a
--  programming language by writing an abstract interpreter for it.
--
--  The programming language we consider throughout this volume is *Imp*, a
--  toy language capturing the core features of conventional imperative
--  programming: variables, assignment, conditionals, and loops. Imp's
--  arithmetic and boolean expressions are developed as their own simple
--  sublangage, called Slang.
--
--  We study two different ways of reasoning about the behavior of Imp
--  programs.
--
--  First, we consider what it means to say that two Imp programs are
--  *equivalent*, in the sense that they produce the same behavior when
--  started in the same initial state. This notion of equivalence becomes a
--  criterion for judging the correctness of program transformations, such
--  as those used in compilers and optimizers. We build some simple
--  optimizers for Imp and prove that they preserve the behavior of the
--  programs they transform.
--
--  Second, we develop a methodology for proving that a given Imp program
--  satisfies a formal specification of its behavior. We introduce *Hoare
--  triples* — Imp programs annotated with pre- and post-conditions
--  describing what they expect to be true of their starting state and what
--  they promise to be true of their ending state, if they terminate — and
--  the reasoning principles of *Hoare Logic*, a domain-specific logic for
--  compositional reasoning about imperative programs. We then develop
--  *decorated programs*, a practical notation for writing out Hoare Logic
--  proofs alongside the code they verify.
--
--  The techniques this volume presents are relatively simple, but they
--  nevertheless underpin many of today's real-world software and hardware
--  verification efforts.

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
--  `HL/Slang.lean`) to get started.
--
--  If you are reading on your own, clone the
--  [SF-in-Lean](https://github.com/plclub/sf-in-lean) repository and run
--  `make
--  hl-student` from the root directory to build the student version
--  of this volume; it is written to `_out/hl/student/`, with an `html/`
--  directory and a `lean/` directory, exactly as described for Logical
--  Foundations. Run `make
--  student` instead if you want all three volumes
--  built together.

--  ### Building on Your Own Copy of Logical Foundations

--  This project includes a copy of the Logical Foundations files that
--  chapters in this volme depends on, in their own `LF/` directory, so you
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

--  @book            {SFL:2,
--  author       =   {Mike Hicks and Benjamin C. Pierce and the SF-in-Lean team},
--  title        =   "Hoare Logic",
--  series       =   "Software Foundations in Lean",
--  volume       =   "2",
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

-- Source revision: 0c2455e, committed 2026-10-07 11:25 UTC

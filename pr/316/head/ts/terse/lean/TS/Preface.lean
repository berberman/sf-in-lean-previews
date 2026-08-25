import SFLCompat

--  # Preface

--  This volume is a work in progress. It will develop a
--  Lean formalization of type systems, covering the simply
--  typed lambda calculus, progress and preservation
--  theorems, and extensions such as subtyping and
--  polymorphism. Please check back later!

--  ## Recommended Citation Format

--  If you want to refer to this volume in your own writing,
--  please do so as follows:

--  @book            {SFL:2,
--  author       =   {Mike Hicks and Benjamin C. Pierce and the SF-in-Lean team},
--  title        =   "Type Systems",
--  series       =   "Software Foundations in Lean",
--  volume       =   "2",
--  year         =   "2026",
--  publisher    =   "Electronic textbook",
--  note         =   {Version 0.1.0, \URL<https://github.com/plclub/sf-in-lean>}
--  }

--  ### Credits

--  **Leadership:** Mike Hicks and Benjamin C. Pierce lead
--  the SF-in-Lean project.

--  **Authors:** The Lean adaptation of *Software
--  Foundations* was created by Mike Hicks, Benjamin C.
--  Pierce, One An, Roger Burtonpatel, Jonathan Chan, Harry
--  Goldstein, Niklas Halonen, Chris Henson, Kihong Heo,
--  Yipeng Liu, and Daniel Sainati

--  **... with contributions from** Luisa Cicolini, Michael
--  Clarkson, Robert Joseph, Sati, and Shriya Thakur

--  **... and gratitude to** David Thrane Christiansen, for
--  helping us understand the intricacies of Lean's Verso
--  document preparation system.

--  **SF in Rocq:** The first three volumes of *Software
--  Foundations in Lean* (*Logical Foundations in Lean*,
--  *Type Systems in Lean*, and *Hoare Logic in Lean*) are
--  adapted from the *Logical Foundations* and *Programming
--  Language Foundations* volumes of the original *Software
--  Foundations* series in Roqc, developed from 2008 to 2026
--  by a team of authors and contributors led by Benjamin C.
--  Pierce.

--  The original *Logical Foundations* was written by
--  Benjamin C. Pierce, Arthur Azevedo de Amorim, Chris
--  Casinghino, Marco Gaboardi, Michael Greenberg, Cătălin
--  Hriţcu, Vilhelm Sjöberg, and Brent Yorgey, with
--  contributions from Loris D'Antoni, Andrew W. Appel,
--  Arthur Charguéraud, Michael Clarkson, Anthony Cowley,
--  Jeffrey Foster, Dmitri Garbuzov, Olek Gierczak, Michael
--  Hicks, Ranjit Jhala, Ori Lahav, Yishuai Li, Greg
--  Morrisett, Jennifer Paykin, Mukund Raghothaman,
--  Chung-chieh Shan, Leonid Spesivtsev, Caleb Stanford,
--  Andrew Tolmach, Philip Wadler, Stephanie Weirich, Li-Yao
--  Xia, and Steve Zdancewic.

--  The original *Programming Language Foundations* was
--  written by Benjamin C. Pierce, Arthur Azevedo de Amorim,
--  Chris Casinghino, Marco Gaboardi, Michael Greenberg,
--  Cătălin Hriţcu, Vilhelm Sjöberg, Andrew Tolmach, and
--  Brent Yorgey with contributions from Loris D'Antoni,
--  Andrew W. Appel, Arthur Chargueraud, Michael Clarkson,
--  Anthony Cowley, Jeffrey Foster, Dmitri Garbuzov, Michael
--  Hicks, Ranjit Jhala, Ori Lahav, Yishuai Li, Greg
--  Morrisett, Jennifer Paykin, Mukund Raghothaman,
--  Chung-Chieh Shan, Leonid Spesivtsev, Caleb Stanford,
--  Philip Wadler, Stephanie Weirich, Li-Yao Xia, and Steve
--  Zdancewic.

--  **Funding:** Development of the original *Software
--  Foundations* series was supported, in part, by the
--  National Science Foundation under the NSF Expeditions
--  grant 1521523, *The Science of Deep Specification*.

--  Note to developers (Benjamin Pierce @bcpierce00):
--      Other funding should be acknowledged here...


[![Github Actions CI][1]][2]
[![HoTT Zulip chat][3]][4]

# Notice

This branch is a fork of the main
[Coq-HoTT](https://github.com/HoTT/Coq-HoTT#) repository. This branch
is created as a place to develop mathematical (and software
engineering) ideas which are not a good fit for the main Coq-HoTT repository. 
At the moment it mostly agrees with the upstream library, but it will 
steadily diverge over time.

A non-exhaustive list of differences is as follows.
- Aesthetics: The Coq-HoTT repository contains two category theory
  sub-libraries, and they use very different notations so that one can
  immediately identify the category theory library which is being
  used. We will take the approach of using the notation which seems
  most appropriate for the ideas being developed, and carefully use
  notation scopes to manage conflicting and overloaded notations.
  Also, the WildCat library does not use Unicode, and we will use
  Unicode freely.
- Namespaces and scoping: The Coq-HoTT library uses a flat module
  structure where each module lives in its own file, and a file's
  dependencies are all imported globally at the top of the file with
  `Require Import WildCat.Core.`, etc. In this fork we will explore an
  architecture where Coq's ML module system is leveraged more
  substantively, we will prefer short names in modules to long but
  globally unique names, we will explore the use of interactive
  modules to incrementally define the fields of a record, etc.
- Typeclass search: We emphasize robustness of proof over
- Automation: We will experiment with the use of Ltac2 and/or Elpi
  to design tactics and/or vernacular commands in this fork,
  such as setoid rewriting tactics, or rewriting modulo associativity.
  The use of automation will be highly context-dependent: our
  rule of thumb is that if the proof term itself is of immediate
  and direct interest (e.g., a truly homotopy-theoretic proof about
  spheres or the suspension) or if we need to prove something
  about the proof-term later (i.e. a 2-cell between 1-cells in a
  2-category will later be subject to coherence conditions)
  then we will insist on using automation tools only if the
  proof-term so generated is highly predictable. For situations
  where there is not a good reason to care about the proof-term,
  blast-style tactics are acceptable.
- SProp: We will use SProp in the library where it simplifies proofs.
- Overall goals: We intend to develop ordinary, everyday mathematics,
  using the Univalence axiom where it is convenient to simplify
  proofs. I do not currently plan to pursue any synthetic homotopy
  theory in this fork. A long-term goal is to provide rewriting tools
  which are useful even to traditional mathematics, 
  to assist in publishing papers faster: ideally, it should be
  possible to formalize some theorems in the same amount of time
  as it would take to give comprehensive, rigorous LaTeX proofs
  of these theorems with no exercises left to the reader.

- Patrick Nicodemus

# Introduction

[Homotopy Type Theory][5] is an interpretation of Martin-Löf’s
intensional type theory into abstract homotopy theory. Propositional
equality is interpreted as homotopy and type isomorphism as homotopy
equivalence. Logical constructions in type theory then correspond to
homotopy-invariant constructions on spaces, while theorems and even
proofs in the logical system inherit a homotopical meaning. As the
natural logic of homotopy, type theory is also related to higher
category theory as it is used e.g. in the notion of a higher topos.

The HoTT library is a development of homotopy-theoretic ideas in the Coq proof
assistant. It draws many ideas from Vladimir Voevodsky's [Foundations][6]
library (which has since been incorporated into the [UniMath][7] library) and
also cross-pollinates with the [HoTT-Agda][8] library. See also: [HoTT in
Lean2][9], [Spectral Sequences in Lean2][10], and [Cubical Agda][11].

More information about this library can be found in:

- _The HoTT Library: A formalization of homotopy type theory in Coq_, Andrej
  Bauer, Jason Gross, Peter LeFanu Lumsdaine, Mike Shulman, Matthieu Sozeau, Bas
  Spitters, 2016 [arXiv][12] [CPP17][13]

Other publications related to the library can be found
[here][14].

# Installation

The HoTT library is part of the [Coq
Platform][15] and can be installed using
the installation instructions there.

More detailed installation instructions are provided in the file
[INSTALL.md](/INSTALL.md).

# Usage

The HoTT library can be used like any other Coq library. If you wish to use the
HoTT library in your own project, make sure to put the following arguments in
your `_CoqProject` file:

```
-arg -noinit
-arg -indices-matter
```

For more advanced use such as contribution see [INSTALL.md](/INSTALL.md).

For **recommended text editors** see [our recommended editors
list](./INSTALL.md#4-editors). Other methods of developing in `coq` will work as
long as the correct arguments are passed.

# Contributing

Contributions to the HoTT library are very welcome! For style guidelines and
further information, see the file [STYLE.md](/STYLE.md).

# Licensing

The library is released under the permissive BSD 2-clause license, see the file
[LICENSE.txt](/LICENSE.txt) for further information. In brief, this means you
can do whatever you like with it, as long as you preserve the Copyright
messages. And of course, no warranty!

# Wiki

More information can be found in the [Wiki][22].


[1]: https://github.com/HoTT/HoTT/workflows/CI/badge.svg?branch=master
[2]: https://github.com/HoTT/HoTT/actions?query=workflow%3ACI+branch%3Amaster
[3]: https://img.shields.io/badge/zulip-join_chat-brightgreen.svg
[4]: https://hott.zulipchat.com/

[5]: http://homotopytypetheory.org/

[6]: https://github.com/vladimirias/Foundations
[7]: https://github.com/UniMath/UniMath
[8]: https://github.com/HoTT/HoTT-Agda
[9]: https://github.com/leanprover/lean2/tree/master/hott
[10]: https://github.com/cmu-phil/Spectral
[11]: https://agda.readthedocs.io/en/v2.6.0.1/language/cubical.html

[12]: https://arxiv.org/abs/1610.04591
[13]: http://cpp2017.mpi-sws.org/
[14]: https://github.com/HoTT/HoTT/wiki/Publications-based-on-the-HoTT-library
[15]: https://github.com/coq/platform/releases

[22]: https://github.com/HoTT/HoTT/wiki

# Introduction to univalent foundations of mathematics with Agda

There is a modular version of the monolotic Agda files here at [https://www.cs.bham.ac.uk/~mhe/TypeTopology/MGS](TypeTopology) also available via [https://github.com/martinescardo/TypeTopology/tree/master/source/MGS](github).

This repository has the sources to generate the lecture notes available at

   > https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html

   > https://arxiv.org/abs/1911.00580

Agda [2.6.2.1](https://agda.readthedocs.io/en/v2.6.2.1/getting-started/installation.html) or higher is required (also tested successfully with Agda 2.8.0). Consult the [installation instructions](INSTALL.md) to help you set up Agda and Emacs for the Midlands Graduate School.

* The (literate) `*.lagda` files are used to generate the `html` pages with the script `./build`.

* This make also generates `./agda/*.agda` files using  `illiterator.hs`.

* The program `agdatomd.hs` converts from `.lagda` to `.md`.

* The `install` action of the `makefile` allows to run an additional action for particular requirements of users or environments, in a file `additionally`, which is not distributed and is ignored by `git`. If this file doesn't exist, an empty executable file is created.

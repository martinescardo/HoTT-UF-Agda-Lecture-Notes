# Introduction to univalent foundations of mathematics with Agda

There is a modular version of the monolithic Agda files in [TypeTopology](https://martinescardo.github.io/TypeTopology/MGS.index.html), also available via [github](https://github.com/martinescardo/TypeTopology/tree/master/source/MGS).

This repository has the sources to generate the lecture notes available at

   > https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html

   > https://arxiv.org/abs/1911.00580

Agda [2.6.2.1](https://agda.readthedocs.io/en/v2.6.2.1/getting-started/installation.html) or higher is required (also tested successfully with Agda 2.8.0 and 2.9.0).

* The (literate) `*.lagda` files are used to generate the `html` pages and a `pdf` version with `make`, or with the script `./build`.

* The `makefile` also generates `./agda/*.agda` files using `illiterator.hs`.

* The program `agdatomd.hs` converts from `.lagda` to `.md`.

* The `install` action of the `makefile` allows to run an additional action for particular requirements of users or environments, in a file `additionally`, which is not distributed and is ignored by `git`. If this file doesn't exist, an empty executable file is created.

## Building the notes

Besides Agda, the build needs GHC to compile `illiterator.hs`, Ruby with [Jekyll](JEKYLL.md) to generate the html pages, and Google Chrome and ghostscript to generate the pdf. Once these are installed, run `bundle install` in this directory, which installs the versions of Jekyll and its libraries given in the `Gemfile`.

Then `make` generates the notes and copies them to `~/martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes`. Another destination can be given with `make DEST=...`, and another browser with `make CHROME=...`. This works on Linux and on macOS.

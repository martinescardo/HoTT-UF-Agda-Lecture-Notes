# Introduction to univalent foundations of mathematics with Agda

There is a modular version of the Agda files here at https://github.com/martinescardo/TypeTopology in the folder
`source/MGS/`.

Sources to generate the lecture notes available at

   > https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html

   > https://arxiv.org/abs/1911.00580

Agda [2.6.2.1](https://agda.readthedocs.io/en/v2.6.2.1/getting-started/installation.html) or higher is required. Consult the [installation instructions](INSTALL.md) to help you set up Agda and Emacs for the Midlands Graduate School.

* The (literate) `*.lagda` files are used to generate the `html` pages with the script `./build`.

* This make also generates `./agda/*.agda` files using  `illiterator.hs`.

* The program `agdatomd.hs` converts from `.lagda` to `.md`.

* The `install` action of the `makefile` allows to run an additional action for particular requirements of users or environments, in a file `additionally`, which is not distributed and is ignored by `git`. If this file doesn't exist, an empty executable file is created.

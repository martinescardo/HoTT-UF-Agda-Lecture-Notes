Installation of Agda and Emacs
==============================

This file describes how to install Agda 2.6.0 and Emacs.
Please follow the installation instructions for your operating system.

If you experience any issues, please take a look at the [Troubleshooting
section](#Troubleshooting).

## GNU/Linux
Start by installing `emacs`, `git`, `ghc`, `cabal-install`, `zlib`, `alex` and
`happy` using the package manager of your distribution. Under Ubuntu or Debian,
this would be:
```bash
$ sudo apt install emacs git ghc cabal-install zlib alex happy
```

### Installing Agda 2.6.0
Next, create a directory `mgs-2019` for the Midlands Graduate School 2019 in
your home directory:
```bash
$ mkdir ~/mgs-2019
```
Inside that directory, we download and install Agda 2.6.0:
```bash
$ cd ~/mgs-2019
$ git clone https://github.com/agda/agda
$ cd agda
$ git checkout release-2.6.0
$ cabal sandbox init
$ cabal update
$ cabal install
```

### Setting up Emacs to work with Agda
Finally, we set up Emacs to work with Agda:
```bash
$ cd ~/mgs-2019/agda/.cabal-sandbox/bin/
$ ./agda-mode setup
$ ./agda-mode compile
$ cd ~/mgs-2019
$ echo '#!/bin/bash' > mgs-emacs
$ echo 'PATH=$PATH:~/mgs-2019/agda/.cabal-sandbox/bin/ emacs' >> mgs-emacs
$ chmod +x mgs-emacs
```
Now to get Emacs with Agda mode, start Emacs using:
```bash
$ cd ~/mgs-2019
$ ./mgs-emacs
```

## MacOS
We will use the [Nix Package Manager](https://nixos.org/nix/).

Open a terminal and run
```bash
$ curl https://nixos.org/nix/install | sh
```
Follow the instructions output by the script. The installation script requires
that you have sudo access.

Install `alex`, `happy` and `emacs` using `nix-env`.
```bash
$ nix-env -iA nixpkgs.haskellPackages.alex nixpkgs.haskellPackages.happy emacs
```

### Installing Agda 2.6.0
Next, create a directory `mgs-2019` for the Midlands Graduate School 2019 in
your home directory:
```bash
$ mkdir ~/mgs-2019
```
Inside that directory, we download and install Agda 2.6.0 using `nix-shell`:
```bash
$ nix-shell -p zlib ghc cabal-install git
$ cd ~/mgs-2019
$ git clone https://github.com/agda/agda
$ cd agda
$ git checkout release-2.6.0
$ cabal sandbox init
$ cabal update
$ ZLIB="$(nix-build --no-out-link "<nixpkgs>" -A zlib)"
$ LIBRARY_PATH=${ZLIB}/lib cabal install
```

Close the terminal, open a new one and continue by following the GNU/Linux
instructions from [Setting up Emacs to work with
Agda](#Setting-up-Emacs-to-work-with-Agda) on.

## Windows
Coming soon...

## Troubleshooting

In this section we describe some problems that have been encountered during compilation, and how to fix them.

#### During `cabal install` Agda 2.5.4... appears, rather than Agda 2.6.0

This is not a problem and perfectly fine, albeit confusing.

#### The command `cabal install` fails with `invalid byte sequence` 

The full error looks like:
```
happy: src/full/Agda/Syntax/Parser/Parser.y: hGetContents: invalid argument (invalid byte sequence)
```

Try prefixing `cabal install` with `LANG=C.UTF-8`, i.e.
```bash
$ LANG=C.UTF-8 cabal install
```

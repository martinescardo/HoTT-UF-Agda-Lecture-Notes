
## Installing Jekyll

The html pages of the notes are generated with [Jekyll](https://jekyllrb.com/), which is written in Ruby. The versions of Jekyll and of the libraries it needs are given in the `Gemfile`, so it is enough to install Ruby and then run, in this directory,

```bash
bundle install
```

After this, `bundle exec jekyll build` generates the pages, as the `makefile` does, and `bundle exec jekyll serve` serves them up in your browser.

### macOS

With [Homebrew](https://brew.sh/), the following installs Ruby, and also ghostscript, which the `makefile` uses for the pdf version:

```bash
brew install ruby ghostscript
```

Homebrew's Ruby has to come before the Ruby of macOS in your `PATH`, as `brew info ruby` explains.

### Ubuntu

Here are steps you can follow on Ubuntu to install Ruby.

```bash
sudo apt update
sudo apt -y upgrade
sudo apt -y install make build-essential
sudo apt -y install ruby ruby-dev
export GEM_HOME=$HOME/gems
export PATH=$HOME/gems/bin:$PATH

gem install bundler
```

Jekyll's own [installation instructions](https://jekyllrb.com/docs/installation/) cover these and other systems.

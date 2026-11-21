# See "Building the notes" in README.md for what needs to be installed.

# Google Chrome is the command google-chrome on Linux and an application
# bundle on macOS. Another browser can be given with make CHROME=...

ifeq ($(shell uname -s),Darwin)
CHROME ?= "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
else
CHROME ?= google-chrome
endif

# Where the lecture notes are published.

DEST ?= ~/martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes

install : _site/HoTT-UF-Agda.html pdf/all/HoTT-UF-Agda.pdf agda/HoTT-UF-Agda.agda additionally
	cp _site/index.html $(DEST)/
	cp _site/HoTT-UF-Agda.html $(DEST)/
	cp _site/Universes.html $(DEST)/
	cp _site/Agda.Primitive.html $(DEST)/
	cp -r _site/css $(DEST)/
	cp _site/LICENSE $(DEST)/
	cp pdf/all/HoTT-UF-Agda.pdf $(DEST)/
	chmod -R a+r $(DEST)/
	./additionally

additionally :
	touch additionally
	chmod +x additionally

_site/HoTT-UF-Agda.html : HoTT-UF-Agda.lagda
	$(info )
	$(info This will take a couple of minutes...)
	$(info )
	time agda --html --html-highlight=code HoTT-UF-Agda.lagda
	cp html/HoTT-UF-Agda.tex index.md
	mv html/HoTT-UF-Agda.tex HoTT-UF-Agda.md
	mv html/Universes.tex    Universes.md
	time agda --html --css=css/Agda.css Universes.lagda
	mv html/Agda.Primitive.html Agda.Primitive.html
	$(info If the following fails you may need to run `bundler update`)
	bundle exec jekyll build

pdf/all/HoTT-UF-Agda.pdf : _site/HoTT-UF-Agda.html
	$(info )
	$(info This will likely give errors which can be ignored...)
	$(info )
	$(CHROME) --headless --print-to-pdf="pdf/all/HoTT-UF-Agda-large.pdf" _site/HoTT-UF-Agda.html
	ps2pdf pdf/all/HoTT-UF-Agda-large.pdf pdf/all/HoTT-UF-Agda.pdf

agda/HoTT-UF-Agda.agda :  HoTT-UF-Agda.lagda
	ghc --make illiterator.hs
	cat HoTT-UF-Agda.lagda | ./illiterator > agda/HoTT-UF-Agda.agda
	cat Universes.lagda    | ./illiterator > agda/Universes.agda

clean :
	rm -f *.o *.hi HoTT-UF-Agda.md index.md Universes.md Agda.Primitive.html

cleanmore :
	rm -f *.agdai *.o *.hi HoTT-UF-Agda.md index.md Universes.md Agda.Primitive.html illiterator

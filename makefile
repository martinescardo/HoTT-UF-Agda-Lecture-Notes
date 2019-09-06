# agda 2.6.0, jekyll, ghc and google-chrome need to be installed in the system

install : _site/HoTT-UF-Agda.html pdf/all/HoTT-UF-Agda.pdf agda/HoTT-UF-Agda.agda additionally
	cp _site/index.html ~/public_html/HoTT-UF-in-Agda-Lecture-Notes/
	cp _site/HoTT-UF-Agda.html ~/public_html/HoTT-UF-in-Agda-Lecture-Notes/
	cp _site/Universes.html ~/public_html/HoTT-UF-in-Agda-Lecture-Notes/
	cp _site/Agda.Primitive.html ~/public_html/HoTT-UF-in-Agda-Lecture-Notes/
	cp -r _site/css ~/public_html/HoTT-UF-in-Agda-Lecture-Notes/
	cp _site/LICENSE ~/public_html/HoTT-UF-in-Agda-Lecture-Notes/
	cp pdf/all/HoTT-UF-Agda.pdf ~/public_html/HoTT-UF-in-Agda-Lecture-Notes/
	chmod -R a+r ~/public_html/HoTT-UF-in-Agda-Lecture-Notes/
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
	time agda --html Universes.lagda
	mv html/Agda.Primitive.html Agda.Primitive.html
	jekyll build

pdf/all/HoTT-UF-Agda.pdf : _site/HoTT-UF-Agda.html
	$(info )
	$(info This will likely give errors which can be ignored...)
	$(info )
	google-chrome --headless --print-to-pdf="pdf/all/HoTT-UF-Agda.pdf" _site/HoTT-UF-Agda.html

agda/HoTT-UF-Agda.agda :  HoTT-UF-Agda.lagda
	ghc --make illiterator.hs
	cat HoTT-UF-Agda.lagda | ./illiterator > agda/HoTT-UF-Agda.agda
	cat Universes.lagda    | ./illiterator > agda/Universes.agda

clean :
	rm -f *.o *.hi HoTT-UF-Agda.md index.md Universes.md Agda.Primitive.html

cleanmore :
	rm -f *.agdai *.o *.hi HoTT-UF-Agda.md index.md Universes.md Agda.Primitive.html illiterator

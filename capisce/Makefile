##
# Capisce
#
# @version OOPSLA 2024

all:
	rm -f capisce && dune build bin/main.exe && cp _build/default/bin/main.exe capisce

install: all
	rm -f ~/.local/bin/capisce && cp _build/default/bin/main.exe ~/.local/bin/capisce

opaminstall: all
	rm -f ~/.opam/4.14.0/bin/capisce && cp _build/default/bin/main.exe ~/.opam/4.14.0/bin/capisce

clean:
	rm -fr _build
	rm -fr ./doc

check: all
	dune build ./test/tests.exe && ./_build/default/test/tests.exe test -- ${TEST}

check-q: all
	dune build ./test/tests.exe && ./_build/default/test/tests.exe test -q --tail-errors=500 -- ${TEST}

survey:
	./scripts/survey.sh 2> /dev/null

survey-tex:
	./scripts/survey_to_tex.py


doc: 
	dune build @doc;
	cp -r _build/default/_doc/_html/ ./doc
	xdg-open ./doc/capisce/index.html
# end

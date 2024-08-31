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
	./scripts/survey.sh ./survey_data_oopsla_hv ./log_hv hv 2> /dev/null
	./scripts/survey.sh ./survey_data_oopsla_df ./log_df df 2> /dev/null

survey-tex:
	./scripts/survey_to_tex.py ./survey_data_oopsla_hv 2> /dev/null > hv.tex
	./scripts/survey_to_tex.py ./survey_data_oopsla_df 2> /dev/null > df.tex
	echo "HEADER VALIDITY"
	cat hv.tex
	echo "DETERMINED FORWARDING"
	cat df.tex

survey-emit: all
	./scripts/survey-emit.sh ./survey-p4
	xdg-open ./survey-p4

doc: 
	dune build @doc;
	cp -r _build/default/_doc/_html/ ./doc
	xdg-open ./doc/capisce/index.html

coverage:
	sh ./coverage.sh
# end

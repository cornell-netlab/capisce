##
# Project Title
#
# @file
# @version 0.1

all:
	rm -f icecap && dune build bin/main.exe && cp _build/default/bin/main.exe icecap

install: all
	rm -f ~/.local/bin/icecap && cp _build/default/bin/main.exe ~/.local/bin/icecap

opaminstall: all
	rm -f ~/.opam/4.14.0/bin/icecap && cp _build/default/bin/main.exe ~/.opam/4.14.0/bin/icecap

clean:
	rm -fr _build

test: all
	bash ./testbf4.sh

time: all
	bash ./timebf4.sh

check: all
	dune build ./test/tests.exe && ./_build/default/test/tests.exe test -- ${TEST}

check-q: all
	dune build ./test/tests.exe && ./_build/default/test/tests.exe test -q -- ${TEST}
# end

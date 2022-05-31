##
# Project Title
#
# @file
# @version 0.1

all:
	rm -f icecap && dune build bin/main.exe && cp _build/default/bin/main.exe icecap

install: all
	rm -f ~/.local/bin/icecap && cp _build/default/bin/main.exe ~/.local/bin/icecap

clean:
	rm -fr _build

test: all
	bash ./testbf4.sh

time: all
	bash ./timebf4.sh

check: all
	dune build ./test/tests.exe && ./_build/default/test/tests.exe

check-q: all
	dune build ./test/tests.exe && ./_build/default/test/tests.exe -q
# end

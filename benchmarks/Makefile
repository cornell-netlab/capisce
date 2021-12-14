##
# Project Title
#
# @file
# @version 0.1

all:
	rm -f capisce && dune build bin/main.exe && cp _build/default/bin/main.exe capisce


clean:
	rm -fr _build

check:
	dune build ./test/tests.exe && ./_build/default/test/tests.exe

check-q:
	dune build ./test/tests.exe && ./_build/default/test/tests.exe -q
# end

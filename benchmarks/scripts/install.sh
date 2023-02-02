#!/usr/bin/env sh

# PRECONDITION. THIS SCRIPT MUST BE RUN FROM THE TOPLEVEL DIRECTORY OF THE REPO
cpidir=$pwd

# install opam
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"


# initialize and update opam
cd $HOME
opam init
opam update
cd $cpidir

# switch to ocaml 4.14.0
opam switch create 4.14.0
eval $(opam env --switch=4.14.0)

# install petr4 and poulet4
cd $HOME
git clone https://github.com/verified-network-toolchain/petr4.git
cd petr4
git fetch --all
git checkout inline-parser-states
sh ./.github/scripts/build-poulet4-ubuntu.sh

# install z3 4.8.8
cd $HOME
curl https://github.com/Z3Prover/z3/releases/download/z3-4.8.8/z3-4.8.8-x64-ubuntu-16.04.zip -o z3.zip
sudo apt install unzip
unzip z3-4.8.8.zip
sudo cp z3/z3 /usr/bin/z3

# move to CPI's source code
cd $cpidir
cd benchmarks

# install opam dependencies
opam install . --deps-only -y
opam install ocamlgraph

# make icecap
make opaminstall

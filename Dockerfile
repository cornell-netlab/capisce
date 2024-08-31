FROM ocaml/opam:ubuntu-20.04-ocaml-4.14

WORKDIR /home/opam
RUN mkdir ./capisce
COPY . ./capisce
USER root
RUN chown -R opam:opam .

RUN apt update
RUN apt install libgmp-dev -y

RUN apt install python3 -y
RUN apt install python3-pip -y

RUN apt install xdg-utils --fix-missing -y
RUN apt install w3m -y

USER opam
WORKDIR /home/opam/capisce/capisce
RUN opam install dune
RUN opam install . --deps-only
RUN opam install menhir
RUN opam install utop
RUN opam install odoc

RUN pip3 install sigfig
RUN pip3 install matplotlib
RUN pip3 install ipython


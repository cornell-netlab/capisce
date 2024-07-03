FROM ocaml/opam:ubuntu-20.04-ocaml-4.14

WORKDIR /home/opam
RUN mkdir ./capisce
COPY . ./capisce
USER root
RUN chown -R opam:opam .
RUN apt install libgmp-dev -y

RUN apt install python3 -y
RUN apt install python3-pip -y

USER opam
WORKDIR /home/opam/capisce/capisce
RUN opam install dune
RUN opam install . --deps-only
RUN opam install menhir

RUN pip3 install sigfig

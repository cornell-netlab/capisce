FROM ocaml/opam:ubuntu-20.04-ocaml-4.14

WORKDIR /home/opam

COPY . .
USER root
RUN chown -R opam:opam .
RUN apt install libgmp-dev -y
USER opam
WORKDIR /home/opam/capisce
RUN opam install dune
RUN opam install . --deps-only
RUN opam install menhir
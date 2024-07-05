# Capisce Artifact Overview -- OOPSLA '24

Capisce is described in the In-Revision OOPSLA paper 369 entitled _Computing Precise Control Invariant Specifications_.

The Capisce library comprises two key pieces:
- an OCAML library for writing down and specifying data plane programs called GPL.
  * Example programs can be seen in the `capisce/programs`.
  * The core interface for writing programs can be found in capisce/lib/ASTs.ml.
- an instrumentation algorithm to translate `GPL` programs into programs in the guarded command langauge
  * the instrumentation algorithm `GPL.encode_tables` van be found in `capisce/lib/AST.ml`
- an inference algorithm to infer control interface specifications for data plane programs
  * The core algorithm (`cegqe`) can be found in `capisce/lib/Qe.ml`.

Here we list the claims in the paper and how they are supported by the artifact:
1. _Capisce compute control interface specifications for real programs._
   This artifact supports this via its survey of real world programs that have
   been implemented in our library. We have provided scripts to automatically
   generate the tex for Figure 4 from the paper.
   
2. _A small proportion of paths suffice to compute control interface specifications
   for real programs_. This can be seen in the final column of Figure 4, as well as
   qualitatively in Figure 5. We have provided scripts to automatically generate the
   graphs in Figure 5.
   

## Hardware Dependencies

We ran our experiments on an Ubuntu 22.04.4 server with the following specs:
- CPU: Intel(R) Xeon(R) Silver 4216 CPU @ 2.10GHz
- RAM: 0.5 TB

## Getting started

There are two ways to get started with Docker: using Docker, and building from source.
We have tested `Capisce` on Ubuntu 20.04 and 22.04.
We recommend using docker to get started quickly.

Either way, the first step is to download the source code, by either cloning the
repository using git, or unpacking the downloaded .zip file. Then change
into the newly created directory. For instance:
```
git clone https://github.com/cornell-netlab/capisce.git
cd capisce
```

### Docker

The easiest way to get Capisce running is using Docker.

- First install Docker.
- Finally, `build` and `run` the docker image
```
docker build -t capisce .
docker run -it capisce
```

Once this succeeds (it may take a while), you should be greeted with a shell prompt similar to the following:
```
opam@1497723f4b4d:~/capisce/capisce$
```

Now to build Capisce, run `make`.

Verify your build by running `./capisce exp -?`

### Installing from source

Capiscelib is an ocaml library, so we first need to install `opam`.
Then, `switch` to the supported ocaml compiler version
```
opam switch create 4.14.0
eval $(opam env)
```
Now install some basic ocaml tooling
```
opam install dune
opam install menhir
opam install utop
```
As well as a system dependency:
```
sudo install libgmp-dev -y
```
Now, change into the nested `capisce` directory (i.e. `/path/to/repo/capisce/capisce`),
and install the dependencies in the `capisce.opam` file:
```
opam install . --deps-only
```

Now you should be ready to build `capisce` by running `make`
```
make
```
Verify your installation by running `./capisce exp -?`

#### Processing the experimental results

The experimental results are processed using some python scripts.
They have their own dependencies that need to be installed:
```
sudo apt install python3 -y
sudo apt install python3-pip -y
pip3 install sigfig
pip3 install matplotlib
pip3 install ipython
```

### Tutorial

Now that you've build `Capisce`, we'll show you how it works.

First run `dune utop`. This will load Capiscelib into a REPL.
Now, open the `Capiscelib` module:
```ocaml
utop # open Capiscelib;;
```

In this Hello-World tutorial, we'll write a program in our
IR `GPL`, which represents the guarded pipeline language described in
the paper. Then we'll write a specification that it must
satisfy. Finally, we'll infer a Control Interface Spec (CIS) that will
ensure the spec is satisfied.

#### Part 1: Writing a program in GPL

First, let open the Modules for the program syntax (`GPL`), including
Bitvector Expressions (`Expr`) and Boolean Expressions (`BExpr`).
```ocaml
utop # open ASTs.GPL;; open Expr;; open BExpr;;
```

We'll now write a simple GPL program that uses a single forwarding table to
set a single 9-bit field `port` based on the value of a 32-bit destination address `dst`. First, we can define the variables `port`and `dst`:
```ocaml
utop # let port = Var.make "port" 9;;
val port : Var.t = <abstr>
```
```ocaml
utop # let dst = Var.make "dst" 32;;
val dst : Var.t = <abstr>
```

We'll use these variables to construct our table. Lets see how we might do that by inspecting the type of the constructor `table`:
```ocaml
utop # table;;
```
should produce
```ocaml
- : string ->
    Var.t list ->
    (Var.t list * Capiscelib.Primitives.Action.t list) list ->
    Pack.t
= <fun>
```

This tells us that to construct a `table`, we need 3 arguments: a `string` name, a list
variable keys, then a list of `Var.t list *
Primitives.Action.t list`. Each pair `(xs, as)` in this list corresponds to an
anonymous function where `xs` occur free in a list of primitive actions. This list should be understood as sequential composition. Lets construct our first action.

```ocaml
utop # let nop = [], []
```

This action is the trivial action. It takes no arguments `[],` and
executes noactions `[]`.

Stepping it up a notch in complexity. We will define a action that
takes in a single argument, indicated by parameter `p`, and assigns `p` to our
previously-defined variable `port`;
```ocaml
utop # let setport =
     let p = Var.make "p" 9 in
     [p], Primitives.Action.[
     	  assign_ port (var p)
     ];;
```
The first line constructs the AST node for parameter `p`. Then the
`[p],` says that `p` is an argument for the action, which is defined
by the subsequent action list.

Now we can define a table, called `simpletable` that reads the vpalue of `port`,
and then either execute the `setport` action with some parameter, or take no action.
```ocaml
utop # let simpletable =
    table "simpletable" [port] [setport; nop];;
```

#### Part 2: Writing a Specification

Now, as an example specification, we can exclude a specific port value.
Perhaps to indicate that this port value, say `47` is disabled.
So we never want to forward a packet out on port `47`. We define a
spec that ensures this as follows:
```ocaml
utop # let port_not_47 =
     let prohibited = bvi 47 9 in
     not_ (eq_ (var port) prohibited);;
```

Now we can use assertions to specify that our table must satisfy this spec:
```ocaml
utop # let program = sequence [
    simpletable;
    assert_ port_not_47
];;
```

#### Part 3: Inferring A CIS

Inferring the control interface specification (CIS) for the table
requires two steps. First we encode the tables using the
instrumentation strategy described in the paper, and then we run our
inference algorithm.

The encoding step eliminates tables, and converts a `GPL.t` program into
a `GCL.t` program. `GCL` here stands for Dijkstra's _guarded command language_.
We run this using the `GPL.encode_tables` function:
```ocaml
utop # let gcl = GPL.encode_tables program;;
```
To see a pretty printed version of the table-free program, run the following:
```ocaml
utop # Printf.printf "%s" @@ ASTs.GCL.to_string gcl;;
```

Now we can infer the specification for this program by running the `CEGQE` algorithm:
```ocaml
utop # let cis = Qe.cegqe gcl;;
```
To pretty print the result in SMTLIB format, run the following command:

```ocaml
utop # Printf.printf "%s" @@ to_smtlib cis;;
```

This specification, says that whenever the action is `setport`,
the argument to `setport` supplied by the controller must not be equal to `47`.

## Step By Step Instructions

We've provided instructions for automatically exercising the experiments using our scripts,
and for running them manually.


### Exercising the Experiments

Now you can run the experiments from the paper. These will take
several days.

- `make survey` runs the experiments described in Figure 4. The output
  can be seen in `./survey_data_oopsla`. Running the experiments takes
  about 4 days of compute.

- `make survey-tex` generates the TeX for Figure 4. 
   Note. Run this while `make survey` is running to see the results computed so far.
- `make coverage` generates the graphs in Figure 5. This will take 2-3 hours

### Running Experiments One-by-One

To run the experiments individually, execute the following command once for each pipeline:
```
./capisce exp -name NAME -out ./survey_data_oopsla
```
where `OUT` is the output directory in which you wish to store the results, and
`NAME` is the name of the example program. The valid names are the following
```
ecmp
netpaxos_acceptor
resubmit
ndp_router
heavy_hitter_1
arp
"07-multiprotocol"
mc_nat
mc_nat_fixed
ts_switching
ts_switching_fixed
heavy_hitter_2
heavy_hitter_2_fixed
flowlet
flowlet_fixed
hula
hula_fixed
fabric
fabric_fixed
linearroad
linearroad_fixed
```

Most of these will finish in minutes, but the last four will take nearly two days. For precisetiming data, consult Figure 4.

Once youve done this, you can generate Figure 4 using the script `./scripts/survey-to-tex.py`.
```
python3 ./scripts/survey-to-tex.py
```
Notice that you can run this script after any number of examples have been run, and you will
get partial results.

To reproduce Figure 5, re-run the relevant programs with the -replay
flag. This will generate the additional data required to generate
Figure 5. The coverage analysis is slow, and may take several
hours. To generate the data run the following commands:
```
./capisce exp -name arp -replay -out survey_data_oopsla
./capisce exp -name heavy_hitter_2 -replay -out survey_data_oopsla
./capisce exp -name heavy_hitter_1 -replay -out survey_data_oopsla
./capisce exp -name flowlet -replay -out survey_data_oopsla
./capisce exp -name 07-multiprotocol -replay -out survey_data_oopsla
./capisce exp -name simple_nat -replay -out survey_data_oopsla
```
Then, to produce the graphs as seen in Figure 5, run the following script:
```
python3 scripts/graphs.py
```
Running the script will output the relative paths to the pdfs it generates.

## Reusability Guide

### Guarded Pipeline Language `GPL`

### Instrumentation and Compiler

### Specification Inference and Modelling




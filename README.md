# Capisce

Capisce is described in the OOPSLA paper entitled _Computing Precise Control Interface Specifications_.

The Capisce library comprises two key pieces:

- an OCAML library for writing down and specifying data plane programs called `GPL`.

  * Example programs can be seen in the `capisce/programs`.

  * The core interface for writing programs can be found in `capisce/lib/ASTs.ml`.

- an instrumentation algorithm to translate `GPL` programs into programs in the guarded command language

  * the instrumentation algorithm `GPL.encode_tables` van be found in `capisce/lib/AST.ml`

- an inference algorithm to infer control interface specifications for data plane programs

  * The core algorithm (`cegqe`) can be found in `capisce/lib/Qe.ml`.

Here we list the claims in the paper and how they are supported by the artifact:

1. _Capisce compute control interface specifications for real programs._
   This artifact supports this via its survey of real world programs that have
   been implemented in our library. We have provided scripts to automatically
   generate the tex for Figures 5 and 6 from the paper.
   
2. _A small proportion of paths suffice to compute control interface specifications
   for real programs_. This can be seen in the final column of Figures 5 and 6, as well as
   qualitatively in Figure 7. We have provided scripts to automatically generate the
   graphs in Figure 7.
   

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

Verify your build by running `./capisce exp -help`

##### Known Issue

On M1 Macs there may be an issue regarding the a missing `/lib64/ld-linux-x86-64.so.2` file.  If you get such an error try building with the flag `--platform linux/amd64`

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
sudo apt install libgmp-dev -y
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
Verify your installation by running `./capisce exp -help`

#### Dependencies for processing the experimental results

The experimental results are processed using some python scripts.
They have their own dependencies that need to be installed:
```
sudo apt install python3 -y
sudo apt install python3-pip -y
pip3 install sigfig
pip3 install matplotlib
pip3 install ipython
```

### Hello World: ARP

Once you've installed `Capisce`, you can verify it works, by computing a specification for
the `arp` program, which can be found in `programs/Arp.ml`.

```bash
# wd: capisce/capisce
mkdir ./survey_data_oopsla
./capisce exp arp -out ./survey_data_oopsla -hv
```

`capisce` will spit out a collection of SMT formulae whose conjunction
corresponds to the control interface specification (spec) that enforces
there are no invalid header reads (`-hv`). It should take about 5 seconds.

If the above command fails, with an error complaining about not being able to find
`../solvers/z3.4.8.13` or `../solvers/princess`, you can specify the path to these 
solvers (in the `solvers` directory) manually by using the `-z3` and `-princess` flags.
For instance:
```bash
./capisce exp -name arp -hv -out ./survey_data_oopsla -z3 /path/to/z3 -princess /path/to/princess
```
In the sequel we will omit the explicit paths flags, but they may always be added if needed.

## Step By Step Instructions

We've provided instructions for automatically exercising the experiments using our scripts,
and for running them manually.


### Exercising the Experiments

Now you can run the experiments from the paper. These will take
several days. Note that because path selection is done by Z3, there may be some variation in the precise numbers generated by this step.

- `make survey` runs the experiments described in Figures 5 and 6. The output
  can be seen in `./survey_data_oopsla`. Running the experiments takes
  about 5 days of compute.

- `make survey-tex` generates the TeX for Figures 5 and 6. 
   Note. Run this while `make survey` is running to see the results computed so far.

- `make coverage` generates the graphs in Figure 7. This will take 2-3 hours

### Running Experiments One-by-One

To run the experiments individually, execute the following command once for each pipeline:
```
./capisce exp NAME -out ./survey_data_oopsla
```
where `OUT` is the output directory in which you wish to store the results, and
`NAME` is the name of the example program. The valid names can be seen by typing `./capisce exp`.

Most of these will finish in minutes, but several will take nearly two days. 
For more-precise timing expectations, consult Figures 5 and 6.

Once you've done this, you can generate Figures 5 and 6 using the script `./scripts/survey-to-tex.py`.
```bash
python3 ./scripts/survey-to-tex.py
```
You may run this script after any number of examples have been run, and you will
get partial results. Those results that haven't finished running yet will be 
indicated by an infinity symbol in the "Result" column.

To reproduce Figure 7, re-run the relevant programs with the `-replay`
flag. This will generate the additional data required to generate
Figure 7. The coverage analysis is slow, and may take several
hours. To generate the data run the following commands:

```bash
./capisce exp arp -replay -out survey_data_oopsla -hv
./capisce exp heavy_hitter_2 -replay -out survey_data_oopsla -hv
./capisce exp heavy_hitter_1 -replay -out survey_data_oopsla -hv
./capisce exp flowlet -replay -out survey_data_oopsla -hv
./capisce exp 07-multiprotocol -replay -out survey_data_oopsla -hv
./capisce exp simple_nat -replay -out survey_data_oopsla -hv
```

Then, to produce the graphs as seen in Figure 7, run the following script:

```bash
python3 scripts/graphs.py
```
Running the script will output the relative paths to the pdfs it generates.

### Common Issues

The Capisce repo ships with solver executables in the `solvers` directory. It is common to have
are issues with the solvers---Capisce prints an inscrutable error message 
followed by `(Failure "found false")`. For instance,
```
Error: Cannot find or load the main class ap.CmdlMain
Cause: java.lang.ClassNotFoundException: ap.CmdlMain
Uncaught exception:

  (Failure "found false")
```

If these occur, please install [Z3](https://github.com/Z3Prover/z3) and 
[princess](http://www.philipp.ruemmer.org/princess.shtml). 
You can either place the executables in capisce's `solvers` directory, 
or pass the locations of the executables to `capisce` using the `-z3` and `-princess` flags.

## Reusability Guide

Our artifact supports three key pieces for reusability.

- The pipeline specification IR `GPL`, which can be found in
  `ASTs.GPL`. This AST can be used as a compiler backend for related
  dataplane analysis tools like `petr4`, `p4cub`, `p4k`, `p4-constraints`,
  or `PI4`.

- The compiler infrastructure for `GPL.t` allows for programmers to easily
  extend the core set of primitives, in a way that supports efficient reuse.

- The Counterexample-guided inductive quantifier elimination algorithm
  `QE.cegqe` is succinctly stated, and can be reimplemented or adapted to
  as new algorithms are discovered.


### Tutorial

Now that you've build `Capisce`, we'll show you how it works.

First run `dune utop`. This will load `Capisce` into a REPL.
Now, open the `Capisce` module:
```ocaml
utop # open Capisce;;
```

In this Hello-World tutorial, we'll write a program in our
IR `GPL`, which represents the guarded pipeline language described in
the paper. Then we'll write a specification that it must
satisfy. Finally, we'll infer a ccontrol interface spec that will
ensure the assertion is satisfied.

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
    [> `Exact of Var.t | `Maskable of Var.t | `MaskableDegen of Var.t ] list ->
    (Var.t list * Capiscelib.Primitives.Action.t list) list ->
    Pack.t
= <fun>
```

This tells us that to construct a `table`, we need 3 arguments: a
`string` name, a list variable keys tagged with their matchkind (`Exact`, `Maskable`, and `MaskableDegen`), then a list of `Var.t list * Primitives.Action.t list`. Each pair `(xs, as)` in this list
corresponds to an anonymous function where `xs` occur free in a list
of primitive actions. This list should be understood as sequential
composition. Lets construct our first action.

```ocaml
utop # let nop : Var.t list * Primitives.Action.t list = [],[];;
```

This action is the trivial action. It takes no arguments `[],` and
executes noactions `[]`.

Stepping it up a notch in complexity. We will define a action that
takes in a single argument, indicated by parameter `p`, and assigns `p` to our
previously-defined variable `port`:

```ocaml
utop # let setport =
     let p = Var.make "p" 9 in
     [p], Primitives.Action.[
     	  assign port (Expr.var p)
     ];;
```

The first line constructs the AST node for parameter `p`. Then the
`[p],` says that `p` is an argument for the action, which is defined
by the subsequent action list.

Now we can define a table, called `simpletable` that reads the vpalue of `port`,
and then either execute the `setport` action with some parameter, or take no action.

```ocaml
utop # let simpletable =
    table "simpletable" [`Exact port] [setport; nop];;
```

The `Exact` matchkind tells us that `simpletable` must precisely read the bits of `port`.
Using `Maskable` corresponds unifies the notions of `ternary`, `lpm` and `optional`, all 
of which allow the the table to skip reading that specific key. `MaskableDegen` is semantically
equivalent to `Exact`, but allows us to differentiate between truly maskable match data 
and degenerate cases described in the paper

#### Part 2: Writing a Specification

Now, as an example specification, we can exclude a specific port value.
Perhaps to indicate that this port value, say `47` is disabled.
So we never want to forward a packet out on port `47`. We define a
spec that ensures this as follows:
```ocaml
utop # let port_not_47 =
    let prohibited = Expr.bvi 47 9 in
    BExpr.(not_ (eq_ (Expr.var port) prohibited));;
```

Now we can use assertions to specify that our table must satisfy this spec:
```ocaml
utop # let program = sequence [
    simpletable;
    assert_ port_not_47
];;
```

#### Part 3: Inferring A Spec

Inferring the control interface spec for the table
requires two steps. First we encode the tables using the
instrumentation strategy described in the paper, and then we run our
inference algorithm.

The encoding step eliminates tables, and converts a `GPL.t` program into
a `GCL.t` program. `GCL` here stands for Dijkstra's _guarded command language_.
We run this using the `GPL.encode_tables` function:
```ocaml
utop # let gcl = ASTs.GPL.encode_tables program;;
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
utop # Printf.printf "%s" @@ BExpr.to_smtlib cis;;
```

The resulting specification has two conjucts. The first, shown below, says that whenever the action is has index `0`, that is when it corresponds to `setport`, the argument to `setport` must not be `47`.
```lisp
  (not (and
          (= _symb$simpletable$action$_$0 (_ bv1 1))
          (= _symb$simpletable$1$p$_$0 (_ bv47 9))))
``` 
The second conjunct, replicated below, says that whenever the action is `setport`,
the key that was matched by `simpletable` must not be equal to `47`.
```lisp
  (not (and
          (= _symb$simpletable$action$_$0 (_ bv0 1))
          (= _symb$simpletable$match_0$_$0 (_ bv47 9))))
```

### Guarded Pipeline Language `GPL`

Here we provide documentation of the core interface for writing `GPL.t` programs.

The `GPL` module, defined in `ASTs.ml` defines programs.
```ocaml
type t
```
It has a type `t` that corresponds to `GPL` programs themselves.

We can construct trivial programs
```ocaml
val skip : t
```

Sequential compositions of programs;
```ocaml
val sequence : t list -> t
```

Nondeterministic choice between programs:
```ocaml
val choice : t list -> ts
```

We can also construct variable assignments
```ocaml
val assign_ : Var.t -> Expr.t -> t
```

and the most important constuct, tables:
```ocaml
val table : string 
  -> [> `Exact of Var.t list | `Maskable of Var.t list | `MaskableDegen of Var.t ] list 
  -> ( Var.t * Primtives.Action.t list) list -> t
```
As described above `table name keys actions` constructs a table named
`name` that chooses an action `a` in `actions` by inspecting the variables in `keys`.

More about `Primitives.Action` can be found in the next section.

To specify desired behaviors we have two primitives, `assume` and `assert`.
```ocaml
val assume : BExpr.t -> t
val assert_ : BExpr.t -> t
```
The `assume` primitive is angelic---if it can be satisfied the program assumes it is.
Conversely, `assert_` is demonic---if it can ba falsified the program assumes it is.

#### Building the Documentation

The full documentation can be viewed using the following command. It may prompt you to
install `odoc`. Please do so using `opam install odoc`.
```
make doc -B
```
This will open the documentation in your systems default web
browser. If you do not have a web browser installed the terminal `xdg-open` command will fail.
Feel free to browse the documenation some other way.
In the docker container the docs will be opened in `w3m` (press `enter` to follow links and `q` to quit).

The documentation for the core modules can be found by clicking on
`capisce` and then navigating to modules `Cmd`, `ASTs`, and `Qe`.

### Instrumentation and Compiler

`GPL.t` is constructed using a functor `Cmd.Make` that allows users to produce
simple loop-free imperative programs with demonic nondeterminism.

`Cmd.Make` has a single module argument which must have module type `Primitive` shown below:

```ocaml
module type Primitive = sig
  type t [@@deriving quickcheck, eq, hash, sexp, compare]
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val contra : t -> t -> bool
  val to_smtlib : t -> string
  val size : t -> int
  val vars : t -> Var.t list
end
```

The `assume` and `assert_` functions construct assumptions and
assertions as before; `contra` describes when two assumptions and/or
assertions are contradictory; `to_smtlib` converts `t` into an string
that uses smtlib syntax for expressions and variables; `size` computes
the size of a primitive, and `vars` computes the variables used in a
primitive.

This structure is extremely extensible and facilitates easy reuse of
our code.  The file `Primitives.ml` serves as a great tutorial for how
to build up a higherarchical set of Primitives.  Then `ASTs.ml` uses
these Primtives to build a set of IRs and a compiler pipeline between
them.  We summarize it here.

Our compiler pipeline starts with  `GPL` and then uses `encode_tables`
to produce  a `GCL` program.  Then passify  produces a program  in the
passive form `Psv.t`  as defined in Section 3.4 of  the paper. Then we
use standard verification generation technqiues to produce formulae in
SMTLIB.

Each of these passes is a fundamentally a catamorphism over the core
structure of the programs, and eliminates a single primitive at a
time: `encode_tables` eliminates tables, and `passify` eliminates
assignments. This is captured in the types.

Starting from the bottom, `Psv.t = Cmd.Make(Passive).t`, where
`Passive.t` is either an `Assume` or an `Assert`.  Then `GCL =
Cmd.Make(Active).t`, where `Active.t` is either a `Passive.t` or an
`Assign`ment. Finally `GPL = Cmd.Make(Pipeline).t`, where `Pipeline.t`
is either a `Table` or an `Active`. The transformation functions
`encode_tables` and `passify` defined in `ASTs.ml` define this
clearly.

With this compiler infrastructure in place, it would be easy for
future researchers to extend our work with additional features. Just
as writing the compiler for `GPL` leverages the existing compiler for
`GCL`, futurue work could extend GPL add primitives for
multiple-assignment, hash functions, or stateful operations. Simply by
writing elimination passes, researchers could make ready use of our
existing verification generation and specification inference code.

### Specification Inference and Modelling

The algorithm `Qe.ceqge` in the `Qe.ml` file is straightfoward and
easy to modify. The experimental setup defined in `bin/Main.ml`
supports swapping in different algorithms for performing the
inference, which will allow future researchers to directly measure
their improvements over CegQe.

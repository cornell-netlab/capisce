# ICECAP

icecap is a tool to generate SMTLIB expressions that verify control plane validity of [P4 Language](https://p4.org) programs.


## Installing from source

1. Install OPAM and update the package lists
    ```
    bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
    opam update
    ```

2. Switch to OCAML 4.14.0
    ```
    opam switch create 4.14.0
    eval $(opam env)
    ```
    
3. Install `petr4` and `poulet4`:
   ```
   git clone git@github.com:verified-network-toolchain/petr4.git
   cd petr4
   git checkout poulet4
   sh ./.github/scripts/build-poulet4-ubuntu.sh
   make install
   cd ..
   ```
  
4. Clone this repository:
   ```
   git clone git@github.com:cornell-netlab/inference.git
   cd inference/benchmark
   ```

5. Install the package dependencies
   ```
   opam install . --deps-only
   ```

6. Compile ICECAP
   ```
   make 
   make install # to install the `icecap` binary
   ```

## Running ICECAP
    Let's say you want to generate a control plane verification expression for 'actions.p4'. You should:
    ```
    cd benchmark
    icecap infer examples/bf4_passing/actions.p4 -I examples/includes
    ```

## Running ICECAP on benchmark P4 files

    ```
    cd benchmark
    make test
    ```

## Contributing

p4pp is an open-source project. We encourage contributions!
Please file issues on
[Github](https://github.com/cornell-netlab/inference/issues).


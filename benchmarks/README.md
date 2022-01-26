# ICECAP

icecap is a tool to generate SMTLIB expressions that verify control plane validity of [P4 Language](https://p4.org) programs.


## Installing from source

1. Install OPAM (newest)
    ```
    bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
    ```

2. Switch to OCAML 4.11.1
    ```
    opam switch 4.11.1
    ```
    
    OCAML version show be now 4.11.1:    
    ```
    ocamlc -v
    ```
    ```
    The OCaml toplevel, version 4.11.1
    ```

3. Install dependencies
    ```
    opam switch import list.opam
    ```

4. Compile ICECAP
```
cd benchmark
make
```
No installation needed

## Running ICECAP
    Let's say you want to generate a control plane verification expression for 'actions.p4'. You should:
    ```
    cd benchmark
    ./icecap infer examples/bf4_passing/actions.p4 -I examples/includes -D
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

## Credits

p4pp was written by Eric Hewry.

## License

icecap is released under the [Apache2 License](LICENSE). IS IT?
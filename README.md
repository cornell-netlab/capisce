# Capisce -- OOPSLA '24

Capisce LIB comprises two pieces:
- an OCAML library for writing down and specifying data plane programs.
  * Example programs can be seen in the `capisce/programs`.
  * The core interface for writing programs can be found in capisce/lib/ASTs.ml.
- an inference algorithm to infer control interface specifications for data plane programs
  * The core algorithm (`cegqe`) can be found in `capisce/lib/Qe.ml`.

## Installing

The easiest way to get Capisce running is using Docker.

- First install Docker.
- Next, unpack the included zip file (or pull from this git repository) to some directory `<capiscedir>`
- Then `cd` into `<capiscedir>` and build and run the docker image
```
docker build -i capisce .
docker run -it capisce
```

Once this succeeds (it may take a while), you should be greeted with a shell prompt similar to the following:
```
opam@1497723f4b4d:~/capisce/capisce$
```

Now to build Capisce, run `make`.

Verify your build by running `./capisce exp -?`

### Installing from source.

To install from source, install opam, and then install the dependencies as is done in the `Dockerfile`.

## Experiments

Now you can run the experiments from the paper. These will take
several days. If you would like to run them in parallel or run only a
few of them, you can edit `./scripts/survey.sh`.

- `make survey` runs the experiments described in Figure 4. The output
  can be seen in `./survey_data_oopsla`. Running the experiments takes
  about 4 days of compute.

- `make survey-tex` generates the TeX for Figure 4. 
   Note. Run this while `make survey` is running to see the results computed so far.
- `make coverage` generates the graphs in Figure 5. This will take 2-3 hours


## Paper

Capisce is described in the In-Revision OOPSLA paper _Computing Precise Control Invariant Specifications_.

# Capisce -- OOPSLA '24

Capisce exposes two pieces:
- an OCAML library for writing down and specifying data plane programs
- an inference algorithm to infer control interface specifications for data plane programs

## Installing

The easiest way to get Capisce running is using Docker.

- First install Docker.
- Next, unpack the included zip file to some directory $CAPISCE
- Then `cd` into `$CAPISCE` and build and run the docker image
```
docker build -it capisce .
docker run -t capisce
```

Once this succeeds (it may take a while), you should be greeted with a shell prompt similar to the following:
```
opam@1497723f4b4d:~/capisce/capisce$
```

Now to build Capisce, run `make`.

Verify your build by running `./capisce exp -?`


## Experiments

Now you can run the experiments from the paper. These will take
several days. If you would like to run them in parallel or un only a
few of them, you can edit `./scripts/survey.sh`.

- `make survey` runs the experiments described in Figure 4. The output
  can be seen in `./survey_data_oopsla`. Running the experiments takes
  about 4 days of compute.

- `make survey-tex` generates the TeX for Figure 4.
- `make coverage` generates the graphs in Figure 5.


## Paper

Capisce is described in the In-Revision OOPSLA paper _Computing Precise Control Invariant Specifications_.
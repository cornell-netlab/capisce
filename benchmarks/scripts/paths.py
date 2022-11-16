#!/usr/bin/env python3

import argparse
import json
from statistics import variance, mean
import matplotlib as mpl
import matplotlib.pyplot as plt

def main():
    parser = argparse.ArgumentParser(description="analyze per-path-performance")
    parser.add_argument('f', type=str)
    parser.add_argument('o', type=str)
    args = parser.parse_args()
    path_ts = []
    print("reading from", args.f)
    with open(args.f) as f:
        path_ts = f.readlines()
    path_ts = list(float(ts) for ts in path_ts if ts.strip().replace('.', '', 1).isdigit())
    xs = list(i for (i,_) in enumerate(path_ts))
    print("plotting")
    plt.scatter(xs, path_ts)
    print("scaling")
    plt.yscale("log")
    print("labelling")
    plt.ylabel("average time to solve 1k paths (ms)")
    plt.xlabel("number of paths processed")
    print("saving to", args.o)
    plt.savefig(args.o, format="png")
    plt.close()
    print("done")


if __name__ == "__main__":
    main()

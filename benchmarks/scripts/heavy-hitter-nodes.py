#!/usr/bin/env python3

import argparse
import json
from statistics import variance, mean
import matplotlib as mpl
import matplotlib.pyplot as plt

class Path:

    def __init__(self,json_str):
        self.json_obj = json.loads(json_str)
        self.key = tuple((n["cmd"], n["idx"]) for n in self.json_obj["path"])
        self.time = self.json_obj["time"]


    def __iter__(self):
        return (k for k in self.key)

    def __contains__(self, idx0):
        for (_, idx) in self.key:
            if idx == idx0:
                return True
        return False

def process(k, idx):
    if isinstance(k, int):
        return k
    else:
        return idx


class HeavyHitters:
    def __init__(self):
        self.registry = {}

    def increment(self, idx, time):
        if idx in self.registry:
            (old_time, number) = self.registry[idx]
            self.registry[idx] = (old_time + time, number + 1)
        else:
            self.registry[idx] = (time, 1)

    def __sorted_data(self):
        data = ((process(k,idx), (t/n)) for (idx, (k, (t,n))) in enumerate(self.registry.items()))
        sorted_data = sorted(data, key=(lambda item: item[0]))
        return zip(*sorted_data) # this is supposed to be unzip (https://stackoverflow.com/questions/19339/transpose-unzip-function-inverse-of-zip)


    def plot(self, outfile):
        (xs,ys) = self.__sorted_data()
        print("plotting", xs, ys)
        plt.scatter(xs,ys)
        plt.savefig(outfile, format="png")
        plt.close()
        print("done")


def index(filename,node_idx):
    assert (filename.count(".") == 1)
    idx = filename.find(".")
    return filename[:idx] + "_" + str(node_idx) + filename[idx:]


class Distrib:
    def __init__(self):
        self.registry = {}

    def add(self, idx, time):
        if idx not in self.registry:
            self.registry[idx] = []
        self.registry[idx].append(time)

    def plot(self,outfile):
        nodes = sorted(list(self.registry.keys()))
        distribs = list(self.registry[n] for n in nodes)
        fig, ax = plt.subplots()
        ax.violinplot(distribs, [100*n for n in nodes], widths = 30)
        # plt.violinplot(nodes, distribs)
        plt.savefig(outfile, format="png")
        plt.close()
        print("done")

    def plot_hists(self, nodes, outfile, xlim, ylim):
        for (idx,distrib) in self.registry.items():
            name = nodes[idx]
            if "true" in name: continue
            plt.hist(distrib, bins=100)
            plt.title("node {0} --- {1}".format(str(idx), nodes[idx]))
            plt.xlabel("seconds to solve path containing this node")
            plt.ylabel("density")
            plt.xlim((0,xlim))
            plt.ylim((0,ylim))
            print("generating for node", idx)
            print("writing to file", index(outfile, idx))
            plt.savefig(index(outfile, idx), format="png")
            plt.close()
        print("done")

    def top_k(self, summary, k):
        variance_list = [(idx, summary(data)) for idx, data in self.registry.items() if len(data) > 1]
        variance_list.sort(key=lambda d: d[1], reverse=True)
        top_k = variance_list[:k]
        return [idx for (idx, variance) in top_k]

class Nodes:
    def __init__(self):
        self.registry = {}

    def add(self, idx, cmd):
        if idx in self.registry:
            assert (self.registry[idx] == cmd)
        else:
            self.registry[idx] = cmd

    def __getitem__(self,idx):
        return self.registry[idx]


def unary_hhs(paths,outfile):
    hh = HeavyHitters()
    nodes = Nodes()
    for pi in paths:
        for (cmd, idx) in pi:
            hh.increment(idx, pi.time)
            nodes.add(idx, cmd)
    hh.plot(outfile)

def binary_hhs(paths,outfile):
    hh = HeavyHitters()
    nodes = Nodes()
    for pi in paths:
        for (cmd1,idx1) in pi:
            nodes.add(idx1,cmd1)
            for (cmd2,idx2) in pi:
                if idx1 == idx2: continue
                lo = min(idx1,idx2)
                hi = max(idx1,idx2)
                hh.increment((lo,hi), pi.time)
    hh.plot(outfile)

def intersect(top_k, path):
    for idx in top_k:
        if idx in path:
            return True
    return False


def paths_time(paths, outfile):
    # compute the top k
    d  = Distrib()
    for pi in paths:
        for (cmd, node_idx) in pi:
            if "true" not in cmd:
                d.add(node_idx, pi.time)
    top_k = d.top_k(k=3, summary=max) # lambda data: variance(data) * mean(data))
    print("top k", top_k)

    #
    xs = []
    ys = []
    for path_idx,pi in enumerate(paths):
        if intersect(top_k, pi):
            xs.append(path_idx)
            ys.append(pi.time / 1000.0)
    print(len(xs))
    # mean = statistics.mean(ys)
    # plt.axhline(y = mean, color = 'r', linestyle = '-')

    # colors = ['#1f77b4' if intersect(top_k, p) else '#ff7f0e' for p in paths]
    plt.scatter(xs, ys)
    plt.ylabel("time to solve path (s)")
    plt.xlabel("path index")
    plt.savefig(outfile, format="png")
    plt.close()
    print("done")

def violins(paths, outfile, xmax, ymax):
    d = Distrib()
    n = Nodes()
    for pi in paths:
        if pi.time > 15000: continue
        for (cmd,idx) in pi:
            d.add(idx, pi.time)
            n.add(idx,cmd)
    d.plot_hists(n, outfile, xmax, ymax)

def main():
    parser = argparse.ArgumentParser(description="detect heavy hitters")
    parser.add_argument('f', type=str)
    parser.add_argument('o', type=str)
    args = parser.parse_args()
    paths = []
    with open(args.f) as f:
        paths = f.readlines()
    paths = list(Path(p) for p in paths)
    # unary_hhs(paths,args.o)
    # binary_hhs(paths, args.o)
    paths_time(paths, args.o)
    # violins(paths, args.o, 5000, 200)

if __name__ == "__main__":
    main()

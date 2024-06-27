#! /usr/bin/python3

import os
from sigfig import round

def file(name, attribute):
    return "./survey_data/{0}_cegps_{1}".format(name, attribute)

def exists(filename : str) -> bool:
    return os.path.isfile(filename)

def contains_one(string, possible_substrings):
    for s in possible_substrings:
        if s in string:
            return True
    return False

def unsolveable(formula_string):
    return contains_one(formula_string, ["unsolveable", "Failure"]) or formula_string == "false"

def trivial(formula_string):
    return "true" == formula_string

def underscores(n):
    return n.replace("_","\\_")

def sci(time_str):
    py_sci_not = "{}".format(float(time_str))
    if "e" not in py_sci_not:
        return py_sci_not
    if py_sci_not == "inf":
        return "\\infty"
    else:
        base, exp = py_sci_not.split('e')
        if float(base) == 0.0:
            return "0"
        else:
            return "{0:.2g} \\times 10^{{{1}}}".format(float(base), int(exp))

def timeout(time_str):
    return time_str == "inf" or time_str == "\\infty"

def readinto(data, field,  from_, default_):
    if exists(from_):
        with open(from_) as fp:
            data[field] = fp.read()
    else:
        data[field] = default_

data = {}
names = [
    "ecmp",
    "netpaxos_acceptor",
    "resubmit",
    "ndp_router",
    "heavy_hitter_1",
    "arp",
    "07-multiprotocol",
    "mc_nat",
    "mc_nat_fixed",
    "ts_switching",
    "ts_switching_fixed",
    "heavy_hitter_2",
    "heavy_hitter_2_fixed",
    "flowlet",
    "flowlet_fixed",
    "hula",
    # "hula_fixed",
    "linearroad",
    "linearroad_fixed",
    "netchain",
    "simple_nat",
    "fabric",
    "fabric_fixed"
]

for n in names:
    data[n] = {}
    attributes = [
        ("time", "inf"),
        ("formula", ""),
        ("size", ""),
        ("tot_paths", "inf"),
        ("count_paths", "0")
    ]
    for attribute, default in attributes:
        readinto(data[n], attribute, file(n, attribute), default)


print("\\footnotesize")
print("\\[\\begin{array}{l l l l l l l l}")
print("    \\text{Program} & \\text{Program Paths} &  \\text{Result} & \\text{Time (ms)} & \\text{Explored Paths} & \\text{Spec AST Size} & \\text{Explored Ratio}\\\\ \midrule")
names.sort(key=lambda t: float(data[t]["tot_paths"]))
for n in names:
    did_fail = "\\bot"     if unsolveable(data[n]["formula"]) else \
               "\\top"     if trivial(data[n]["formula"]) else \
               ""          if timeout(data[n]["time"]) else \
               "\\formula"
    print()
    print("    \\texttt{{{name}}} & {prog_paths} & {result} & {time} & {exp_paths}  & {size} & {percent} \\\\".format(
        name = underscores(n),
        prog_paths = data[n]["tot_paths"],
        result = did_fail,
        time = "\\infty" if data[n]["time"] == "inf" else round(float(data[n]["time"]), sigfigs=2),
        exp_paths = data[n]["count_paths"],
        size = data[n]["size"],
        percent = sci(round(float(data[n]["count_paths"]) / float(data[n]["tot_paths"]), sigfigs=2))
        ))
print("\\end{array}\\]")
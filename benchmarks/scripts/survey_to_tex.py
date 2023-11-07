#! /usr/bin/python3

import os

def time(name : str) -> str:
    return "./survey_data/{0}_cegps_time".format(name)

def result(name):
    return "./survey_data/{0}_cegps_formula".format(name)

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
    py_sci_not = "{:e}".format(float(time_str))
    if py_sci_not == "inf":
        return "\\infty"
    else:
        base, exp = py_sci_not.split('e')
        return "{0} \\times 10^{{{1}}}".format(base, str(int(exp)))

def timeout(time_str):
    return time_str == "inf" or time_str == "\\infty"

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
    # "heavy_hitter_2_fixed",
    "flowlet",
    # "flowlet_fixed",
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
    if exists(time(n)):
        with open(time(n)) as fp:
            data[n]["time"] = fp.read()
    else:
        data[n]["time"] = "inf"
    if exists(result(n)):
        with open(result(n)) as fp:
            data[n]["result"] = fp.read()
    else:
        data[n]["result"] = ""

print("\\footnotesize")
print("\\[\\begin{array}{l l l}")
print("    \\text{Program} & \\text{Time (s)} & \\text{Result}\\\\ \midrule")
names.sort(key=lambda t: float(data[t]["time"]))
for n in names:
    did_fail = "\\bot"     if unsolveable(data[n]["result"]) else \
               "\\top"     if trivial(data[n]["result"]) else \
               ""          if timeout(data[n]["time"]) else \
               "\\formula"
    print("    \\texttt{{{0}}} & {1} & {2} \\\\".format(underscores(n), sci(data[n]["time"]), did_fail))
print("\\end{array}\\]")
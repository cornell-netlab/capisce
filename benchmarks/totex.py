# reads out.json, outputs latex table as out.tex

import argparse
import subprocess
import sys
import os
import time
import json
import latextable
import texttable

read_dir = './'
input_file = 'out.json'
output_file = 'out.tex'


if len(sys.argv) != 1:
    print('Usage: python3 totex.py')
    exit
else:
    try:
        with open(input_file, "r") as f:
            results = json.load(f)
    except:
        results = {}
        
fields = ["\\textsc{P4 Program}"]
first_experiment = list(results)[0]
fields += list(results[first_experiment])

experiments = []
for experiment in results:
    experiments.append(experiment)

rows = [fields]
for experiment in experiments:
    row = ["\\texttt{" + experiment.replace("_","\_")[:-3] + "}"] # removes .p4 from files, adds '\' before '_', adds \tt{}
    for value in results[experiment].values():
        if value == "x":
            row += ['']
        elif value == "-":
            row += ["$\\bot$"]
        else:
            # row += [f'${float(value):.2f}$']
            row += [float(value)]
    rows.append(row)

rows[0][1] = "Time (ms)"
rows[0][2] = "NT AST Size"
rows[0][3] = "(= \\texttt{false})"

rows = [rows[0]] + sorted(rows[1:], key=lambda r: r[1])
rows = [ [ v if isinstance(v, str) else f'${v:.2f}$'
           for v in row]
         for row in rows]



table = texttable.Texttable()
table.set_cols_align(["l", "l", "l", "c"])
table.set_cols_valign(["t", "t", "t", "t"])
table.add_rows(rows)

latex_table = latextable.draw_latex(table, caption="An example table.", label="table:example_table", use_booktabs=True)
latex_table = latex_table[30:-83] # removes label,caption, table, 
with open(output_file, "w") as outfile:
    outfile.write(latex_table)
print (len(rows)-1,"entries written to latex table.")

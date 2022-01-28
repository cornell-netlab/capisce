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

else:
    try:
        with open(input_file, "r") as f:
            results = json.load(f)
    except:
        results = {}
        
fields = ["Source P4 File"]
first_experiment = list(results)[0]
fields += list(results[first_experiment])

experiments = []
for experiment in results:
    experiments.append(experiment)

rows = [fields]
for experiment in experiments:
    row = ["\\tt{" + experiment.replace("_","\_")[:-3] + "}"] # removes .p4 from files, adds '\' before '_', adds \tt{}
    for value in results[experiment].values():
        if value == "x":
            row += ['$\\times$']
        elif value == "-":
            row += ["$\\bot$"]
        else:
            row += [f'${float(value):.2f}$']
    rows.append(row)

rows[0][1] = "Elapsed time (ms)"
rows[0][2] = "Size (# AST nodes)"
rows[0][3] = "Satisfiable"

table = texttable.Texttable()
table.set_cols_align(["l", "l", "l", "l"])
table.set_cols_valign(["t", "t", "t", "t"])
table.add_rows(rows)

latex_table = latextable.draw_latex(table, caption="An example table.", label="table:example_table", use_booktabs=True)
latex_table = latex_table[30:-83] # removes label,caption, table, 
with open(output_file, "w") as outfile:
    outfile.write(latex_table)
print (len(rows)-1,"entries written to latex table.")

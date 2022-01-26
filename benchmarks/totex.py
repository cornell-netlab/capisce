# stores [label][field] = value in possibly existing json file containing experiment results

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
    row = [experiment]
    for value in results[experiment].values():
        row += [value]
    rows.append(row)

table = texttable.Texttable()
table.set_cols_align(["l", "l", "l"])
table.set_cols_valign(["t", "t", "t"])
table.add_rows(rows)

latex_table = latextable.draw_latex(table, caption="An example table.", label="table:example_table")
with open(output_file, "w") as outfile:
    outfile.write(latex_table)
print (len(rows)-1,"entries written to latex table.")

# print('Texttable Output:')
# print(table.draw())

# print('\nLatextable Output:')
# print(latex_table)


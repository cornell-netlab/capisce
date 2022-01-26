# stores [label][field] = value in possibly existing json file containing experiment results

import argparse
import subprocess
import sys
import os
import time
import json

read_dir = './'
results_file = 'out.json'


if len(sys.argv) < 2:
    print('Usage: python3 sotre.py <label> <field> <value>, e.g. python3 store dir_listing size 32MB')

else:
    try:
        with open(results_file, "r") as f:
            results = json.load(f)
    except:
        results = {}
        

    # label = sys.argv[1]
    label = sys.argv[1].split("/")[-1:][0]
    field = sys.argv[2]
    value = sys.argv[3]
    if label not in results:
        results[label] = {}
    results[label][field] = value
    
    with open(results_file, "w") as outfile:
        json.dump(results, outfile)

# with open(results_file, "r") as f:
#     results = json.load(f)
# print(results)

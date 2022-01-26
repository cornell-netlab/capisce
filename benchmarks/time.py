# times commands passed as arguments, saves in a json file

import argparse
import subprocess
import sys
import os
import time
import json

read_dir = './'
results_file = 'out.json'


if len(sys.argv) < 2:
    print('Usage: python3 time.py <label> <command>, e.g. python3 time.py dir_listing ls -l')

else:
    try:
        with open(results_file, "r") as f:
            results = json.load(f)
    except:
        results = {}
        

    # label = sys.argv[1]
    label = sys.argv[1].split("/")[-1:][0]
    results[label] = {}
    start = time.time()

    try:
        # subprocess.check_call(sys.argv[2:], cwd=read_dir, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        subprocess.check_call(sys.argv[2:], cwd=read_dir)

    except:
        None

    end = time.time()
    
    results[label]['elapsed-ms'] = (end - start) * 1000
    
    with open(results_file, "w") as outfile:
        json.dump(results, outfile)

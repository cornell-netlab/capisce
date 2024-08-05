# -*- coding: utf-8 -*-
import sys
import csv
import matplotlib as mpl
mpl.use('Agg')
import matplotlib.pyplot as plt
from cycler import cycler
from collections import defaultdict
import numpy as np
import math

from IPython.display import set_matplotlib_formats

onecolsize = (2, 0.5)   # Tweak based on figure's appearance in the paper
# seaborn_colorblind = cycler('color', ['#0072B2', '#D55E00', '#009E73', '#CC79A7', '#F0E442', '#56B4E9'])
# seaborn_muted = cycler('color', ['#4878CF', '#6ACC65', '#D65F5F', '#B47CC7', '#C4AD66', '#77BEDB'])
markers = ['o','3','^','+','*','x']
def setrcparams():
  # setup matplotlib rcparams
  plt.style.use(['seaborn-paper', 'seaborn-colorblind'])
  # color cyclers
  seaborn_colorblind = cycler('color', ['#0072B2', '#D55E00', '#009E73', '#CC79A7', '#F0E442', '#56B4E9'])
  # seaborn_muted = cycler('color', ['#4878CF', '#6ACC65', '#D65F5F', '#B47CC7', '#C4AD66', '#77BEDB'])

  # seaborn_colorblind = cycler('color',[
  #   "#490092","#006ddb","#b66dff","#6db6ff","#b6dbff",
  #   "#920000","#924900","#db6d00","#24ff24","#ffff6d",
  #   "#000000","#004949","#009292","#ff6db6","#ffb6db"
  # ])

  plt.rcParams['axes.prop_cycle'] =  seaborn_colorblind + cycler(linestyle=['-', '--', '-.', '--', '-.','-'])

  plt.rcParams['axes.axisbelow'] = True
  plt.rcParams['axes.edgecolor'] = 'lightgray'
  plt.rcParams['axes.facecolor'] = 'white'
  plt.rcParams['axes.spines.left'] = False
  plt.rcParams['axes.spines.bottom'] = False
  plt.rcParams["axes.spines.right"] = False
  plt.rcParams["axes.spines.top"] = False
  # plt.rcParams['axes.grid'] = True
  plt.rcParams['axes.linewidth'] = 0.5


  plt.rcParams['grid.alpha'] = 0.4
  plt.rcParams['grid.color'] = 'gray'
  plt.rcParams['grid.linestyle'] = ':'
  plt.rcParams['grid.linewidth'] = 1.0

  plt.rcParams['hatch.linewidth'] = 1.0

  plt.rcParams['xtick.bottom'] = False
  plt.rcParams['ytick.left'] = False
  # plt.rcParams['xtick.direction'] = 'in'
  # plt.rcParams['ytick.direction'] = 'in'


  plt.rcParams['legend.edgecolor'] = 'none'
  plt.rcParams['legend.framealpha'] = 0.4
  plt.rcParams["legend.columnspacing"] = 0.4
  plt.rcParams["legend.handletextpad"] = 0.2

  plt.rcParams['savefig.bbox'] = 'tight'
  plt.rcParams['savefig.format'] = 'pdf'
  plt.rcParams['savefig.pad_inches'] = 0

  plt.rcParams['figure.figsize'] = onecolsize

  # plt.rcParams['pdf.fonttype'] = 42
  # plt.rcParams['ps.fonttype'] = 42
  # plt.rcParams['pdf.compression'] = 9
  # plt.rcParams['text.usetex'] = True
  # plt.rcParams['pgf.texsystem']= "pdflatex"
  # plt.rcParams["font.sans-serif"] = "Linux Libertine"
  # plt.rcParams["text.latex.preamble"] = "\usepackage{libertine},\usepackage[libertine]{newtxmath},\usepackage[T1]{fontenc}"
  # plt.rcParams["pgf.preamble"] = "\usepackage{libertine},\usepackage[libertine]{newtxmath},\usepackage[T1]{fontenc}"
  # plt.rcParams["font.family"] = "sans-serif"

# Load the base config
setrcparams()

# Override some the common rcParams as needed
plt.rcParams['axes.spines.left'] = True
plt.rcParams['axes.spines.bottom'] = True
plt.rcParams["legend.columnspacing"] = 0.8
plt.rcParams["legend.handletextpad"] = 0.4
plt.rcParams["font.size"] = 4

plt.rcParams["xtick.major.pad"]="0"
plt.rcParams["ytick.major.pad"]="0"

def plot_series(data, name = "plot", xlabel = "LABELME", ylabel = "LABELME", yscale = "linear", xscale = "linear", ylim = None, xlim = None):
  fig = plt.figure(figsize=(1.5,1)) # Override fig size based on trial
  for i, (xs, ys, label) in enumerate(data):
    xaxis = np.arange(len(xs))
    plt.bar(xaxis - 0.2 + (0.4 * i), ys, 0.4, label=label)
    plt.xticks(ticks = xaxis, labels = xs)
  if ylim:
    plt.ylim(ylim)
  if xlim:
    plt.xlim(xlim)
  plt.yscale(yscale)
  plt.xscale(xscale)
  plt.yticks(fontsize=4)
  plt.ylabel(ylabel, fontsize = 6)
  plt.xlabel(xlabel, fontsize = 6)
  plt.title(name, fontsize = 6)
  if len(data) > 1:
    plt.legend(bbox_to_anchor=(1,1))
  name = "%s.pdf" % (name.replace(" ","_"))
  fig.savefig(name)
  print("saved to", name)
  plt.close(fig)
  print("done")

def bf4_file (is_hv):
  if is_hv:
    return './data/bf4-hv.csv'
  else:
    return './data/bf4-df.csv'

class BF4Data():
  def __init__(self, name, time, startbugs, endbugs):
    self.name = name
    self.time = float(time) ## time in ms
    self.startbugs = float(startbugs)
    self.endbugs = float(endbugs)

def read_data(c, f):
  data = []
  with open(f) as csvfile:
    reader = csv.reader(csvfile)
    for row in reader:
      # print(row)
      data.append(c(*row))
  return data

def plot_bugcoverage(is_hv):
  bf4_data = read_data(BF4Data, bf4_file(is_hv))
  fig = plt.figure() # Override fig size based on trial
  legal_data = [d for d in bf4_data if d.startbugs > 0]
  bf4_coverage = [100.0 * (d.startbugs - d.endbugs)/d.startbugs for d in legal_data]
  capisce_coverage = [0.0 if d.name == "linearroad" and is_hv else
                      100.0
                      for d in legal_data]
  program_names = [str(d.name) for d in legal_data]
  xaxis = [float(i) for i,_ in enumerate(legal_data)]
  width = 0.4
  bf4_xaxis = [i - (width/2.0) - 0.01 for i in xaxis]
  capisce_xaxis = [i + (width / 2.0) + 0.01 for i in xaxis]
  plt.bar(bf4_xaxis, [100.0 for _ in bf4_coverage], 0.4, color = '#56B4E9', label = "bf4 Uncontrolled")
  plt.bar(capisce_xaxis, [100.0 for _ in capisce_coverage], 0.4, color = '#009E73', label="Capisce Uncontrolled")
  plt.bar(bf4_xaxis, bf4_coverage, 0.4, color = '#0072B2', label="bf4 Controlled")
  plt.bar(capisce_xaxis, capisce_coverage, 0.4, color = '#D55E00', label="Capisce Controlled")
  plt.xticks(ticks = xaxis, labels = program_names, fontsize = 4, rotation = 45, ha="right")
  # if ylim:
  #   plt.ylim(ylim)
  # if xlim:
  #   plt.xlim(xlim)
  # plt.yscale(yscale)
  # plt.xscale(xscale)
  plt.yticks(fontsize=3)
  # plt.xlabel("Programs", fontsize = 6)
  plt.ylabel("% Controlled", fontsize = 4)
  # if is_hv:
  #   plt.title("Header Validity", fontsize = 6)
  # else:
  #   plt.title("Determined Forwarding", fontsize = 6)
  # if len(data) > 1:
  plt.legend(fontsize = 4, ncol=2, loc = (0,1))
  name = "{}_Bug_Coverage.pdf".format(("HV" if is_hv else "DF"))
  fig.savefig(name)
  print("saved to", name)
  plt.close(fig)
  print("done")

def plot_solvetime(is_hv):
  ylim = (60.0 * 60.0 * 24.0)
  if is_hv:
    capisce= {
      "mc-nat": 0.048,
      "ts-switching" : 0.10,
      "mc-nat-fixed": 0.018,
      "ts-switching-fixed" : 0.020,
      "resubmit" : 0.017,
      "ecmp" : 0.019,
      "netpaxos-acceptor": 0.043,
      "hula" : 0.043,
      "ndp-router" : 0.022,
      "arp": 1.3,
      "heavy-hitter-2": 0.20,
      "heavy-hitter-1": 0.36,
      "flowlet": 0.66, 
      "07-multiprotocol": 0.70,
      "simple-nat" : 3.5,
      "netchain" : 1.9 * (10 ** 3),
      "fabric" : 1.5 * (10 ** 5),
      "linearroad" : ylim, 
      "heavy-hitter-2-fixed": 0.023,
      "flowlet-fixed": 0.023,
      "linearroad-fixed": 1.9 * (10 ** 5),
      "fabric-fixed": 2.3 * (10 ** 2),
    }
  else: 
    capisce = {
      "resubmit" : 160.0 / 1000.0,
      "ts-switching" : 100.0 / 1000.0,
      "mc-nat": 270.0 / 1000.0,
      "ecmp" : 320 / 1000.0,
      "netpaxos-acceptor" : 120 / 1000.0,
      "heavy-hitter-2": 88000.0 / 1000.0,
      "heavy-hitter-1": 1000.0 / 1000.0,
      "flowlet" : 79000.0 / 1000.0,
      "hula" : 390.0 / 1000.0,
      "ndp-router": 40000.0 / 1000.0,
      "07-multiprotocol" : 30000.0 / 1000.0,
      "netchain" : 27000.0 / 1000.0,
      "fabric" : 7300.0 / 1000.0
    }
  bf4_data = read_data(BF4Data, bf4_file(is_hv))
  legal_data = [d for d in bf4_data if d.startbugs > 0 and d.name in capisce]
  legal_data.sort(key = lambda d: capisce[d.name])
  fig = plt.figure(figsize=(2,1)) # Override fig size based on trial
  bf4_time = [d.time for d in legal_data]
  capisce_time = [capisce[d.name] for d in legal_data]
  program_names = [str(d.name) for d in legal_data]
  xaxis = [float(i) for i,_ in enumerate(legal_data)]
  if is_hv: 
    print("linearroad", capisce["linearroad"], "netchain", capisce["netchain"])
  width = 0.4
  bf4_xaxis = [i - (width/2.0) for i in xaxis]
  capisce_xaxis = [i + (width / 2.0) for i in xaxis]
  plt.bar(bf4_xaxis, bf4_time, 0.4, label="bf4")
  if is_hv:
    plt.bar(capisce_xaxis[:-1], capisce_time[:-1], 0.4, label="Capisce")
    plt.bar(capisce_xaxis[-1], capisce_time[-1], 0.4, label="Capisce Timeout")
  else:
    plt.bar(capisce_xaxis, capisce_time, 0.4, label="Capisce")
  plt.xticks(ticks = xaxis, labels = program_names, fontsize = 4, rotation = 45, ha="right")
  plt.yticks(fontsize=4)
  # if xlim:
  #   plt.xlim(xlim)
  plt.yscale("log")
  # plt.xscale(xscale)
  # plt.xlabel("Programs", fontsize = 6)
  plt.ylabel("time (s)", fontsize = 4)
  # plt.title("Header Validity" if is_hv else "Determined Forwarding", fontsize = 6)
  # if len(data) > 1:
  plt.legend(fontsize = 4)
  name = "{}_Time.pdf".format("HV" if is_hv else "DF") 
  fig.savefig(name)
  print("saved to", name)
  plt.close(fig)
  print("done")

if __name__ == "__main__":
  for is_hv in [True,False]:
    plot_bugcoverage(is_hv)
    plot_solvetime(is_hv)
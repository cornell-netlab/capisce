# -*- coding: utf-8 -*-
import csv
import locale
import time
import matplotlib as mpl
mpl.use('Agg')
import matplotlib.pyplot as plt
from cycler import cycler
from collections import defaultdict
import numpy as np
import math

locale.setlocale(locale.LC_ALL, 'en_US.UTF8')
from IPython.display import set_matplotlib_formats

onecolsize = (4, 1.5)   # Tweak based on figure's appearance in the paper
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
  plt.rcParams['axes.grid'] = True
  plt.rcParams['axes.linewidth'] = 0.1


  plt.rcParams['grid.alpha'] = 0.4
  plt.rcParams['grid.color'] = 'gray'
  plt.rcParams['grid.linestyle'] = ':'
  plt.rcParams['grid.linewidth'] = 1.0

  plt.rcParams['hatch.linewidth'] = 1.0

  plt.rcParams['xtick.bottom'] = False
  plt.rcParams['ytick.left'] = False
  plt.rcParams['xtick.direction'] = 'in'
  plt.rcParams['ytick.direction'] = 'in'


  plt.rcParams['legend.edgecolor'] = 'none'
  plt.rcParams['legend.framealpha'] = 0.4
  plt.rcParams["legend.columnspacing"] = 0.4
  plt.rcParams["legend.handletextpad"] = 0.2

  plt.rcParams['savefig.bbox'] = 'tight'
  plt.rcParams['savefig.format'] = 'pdf'
  plt.rcParams['savefig.pad_inches'] = 0

  plt.rcParams['figure.figsize'] = onecolsize

  plt.rcParams['pdf.fonttype'] = 42
  plt.rcParams['ps.fonttype'] = 42
  plt.rcParams['pdf.compression'] = 9
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

# Example plot

def read_data():
  # Parse and extract data
  data0 = dict()
  data1 = dict()
  for key in range(1, 100):
      data0[key] = math.sqrt(key)
      data1[key] = math.log(key)

  return (data0, data1)

def plot_series(data, name = "plot", xlabel = "LABELME", ylabel = "LABELME", yscale = "linear", xscale = "linear"):
  fig = plt.figure(figsize=(3.7,1.5)) # Override fig size based on trial
  for xs, ys, label, marker in data:
    plt.scatter(xs, ys, label=label, marker=marker)
  plt.yscale(yscale)
  plt.xscale(xscale)
  plt.ylabel(ylabel)
  plt.xlabel(xlabel)
  # plt.title(name)
  if len(data) > 1:
    plt.legend(bbox_to_anchor=(1,1))
  fig.savefig("%s.pdf" % (name.replace(" ","_")))
  plt.close(fig)
  print("done")

def det_fwd_file ():
  return "./data/determined_forwarding.csv"

class DFData():
  def __init__(self, ntables, nacts, nassigns, time, form_size, npaths):
    self.ntables = int(ntables)
    self.nacts = int(nacts)
    self.nassigns = int(nassigns)
    self.time_ms = float(time)
    self.time_s = self.time_ms / 1000.0
    self.form_size = int(form_size)
    self.npaths = int(npaths)

def read_data(c, f):
  data = []
  with open(f) as csvfile:
    reader = csv.reader(csvfile)
    for row in reader:
      data.append(c(*row))
  return data

def plot_det_fwd():
  df_data = read_data(DFData, det_fwd_file())
  plot_series(
    name = "Determined Forwarding",
    xlabel = "Number of program paths", xscale = "log",
    ylabel = "Inference time (ms)", yscale = "log",
    data = [
      ([d.npaths for d in df_data if d.nassigns == o and d.nacts == a],
       [d.time_ms for d in df_data if d.nassigns == o and d.nacts == a],
       "A={0},O={1}".format(a,o),
       markers[i]
       )
      for (i,(a,o)) in enumerate((a,o) for a in [1,2,3] for o in [1,2,3] if o <= a)
    ])

def ternary_data_file():
  return "./data/ternary_explosion_encapsulation.csv"

class TData():
  def __init__(self, nternary, nexact, ntables, encap, time_ms, form_size, npaths):
    self.nternary = int(nternary)
    self.nexact = int(nexact)
    self.ntables = int(ntables)
    self.encap = encap == "true"
    self.time_ms = float(time_ms)
    self.time_s = self.time_ms / 1000.0
    self.form_size = int(form_size)
    self.npaths = int(npaths)

def plot_ternary():
  t_data = read_data(TData, ternary_data_file())
  max_tables = max(d.ntables for d in t_data)
  plot_series(
    name = "Ternary Explosion",
    xlabel = "Number of ternary matches",
    ylabel = "Inference time (ms)", yscale = "log",
    data = [
      ([d.nternary for d in t_data if d.ntables == ntables],
       [d.time_ms for d in t_data if d.ntables == ntables],
       "Tables={0}".format(ntables),
       markers[idx]
       )
      for idx,ntables in enumerate(range(1,max_tables,3))
    ]
  )

def joins_data_file():
  return "data/joins.csv"

class JData():
  def __init__(self, njoins, nvars, encap, time_ms, form_size, npaths):
    self.njoins = int(njoins)
    self.nvars = int(nvars)
    self.encap = encap == "true"
    self.time_ms = float(time_ms)
    self.time_s = self.time_ms / 1000.0
    self.form_size = int(form_size)
    self.npaths = npaths

def plot_joins():
  j_data = read_data(JData,joins_data_file())
  plot_series(
    name = "Orchestrated Hits",
    xlabel = "Number of open-close pairs",
    ylabel = "Inference Time (ms)", yscale = "log",
    data = [
      ([d.njoins for d in j_data if d.encap],
       [d.time_ms for d in j_data if d.encap],
       "Annotated", 'o'),
      ([d.njoins for d in j_data if not d.encap],
       [d.time_ms for d in j_data if not d.encap],
       "No Annotations", "s")
      ]
    )


if __name__ == "__main__":
  plot_det_fwd()
  plot_ternary()
  plot_joins()

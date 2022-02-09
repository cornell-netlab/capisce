# -*- coding: utf-8 -*-
import argparse
import csv
import locale
import time
import matplotlib as mpl
# mpl.use('TkAgg')
import matplotlib.pyplot as plt
from cycler import cycler
from collections import defaultdict
import numpy as np
import math

locale.setlocale(locale.LC_ALL, 'en_US.UTF8')
from IPython.display import set_matplotlib_formats
set_matplotlib_formats('png')

onecolsize = (4, 1.5)   # Tweak based on figure's appearance in the paper
seaborn_colorblind = cycler('color', ['#0072B2', '#D55E00', '#009E73', '#CC79A7', '#F0E442', '#56B4E9'])
seaborn_muted = cycler('color', ['#4878CF', '#6ACC65', '#D65F5F', '#B47CC7', '#C4AD66', '#77BEDB'])

def setrcparams():
  # setup matplotlib rcparams
  plt.style.use(['seaborn-paper', 'seaborn-colorblind'])
  # color cyclers
  seaborn_colorblind = cycler('color', ['#0072B2', '#D55E00', '#009E73', '#CC79A7', '#F0E442', '#56B4E9'])
  seaborn_muted = cycler('color', ['#4878CF', '#6ACC65', '#D65F5F', '#B47CC7', '#C4AD66', '#77BEDB'])

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


timeout = 60*60*1000

def lines_2 (outdir, xs, ys, ws, zs, label, xwlabel, ylabel, zlabel):
  xs = [x / (60 * 1000.0) for x in xs]
  ws = [w / (60 * 1000.0) for w in ws]
  plt.rc("font", size=9)
  plt.rc("ytick", labelsize=9)
  plt.rc("xtick", labelsize=9)
  fig, ax1 = plt.subplots(figsize=onecolsize)
  ax1.set_xlabel(xwlabel, fontsize=9)
  ax1.set_ylabel("# occurences", fontsize=9)
  ax1.set_yscale('linear')
  ax1.set_ylim(0,300) # multiproto
  # ax1.set_ylim(450,5000) # netchain
  # ax1.set_ylim(38000,39000) # switch
  ax1.grid(False)
  # ax1.yaxis.tick_right()
  # ax1.yaxis.set_ticks_position("right")
  # ax1.yaxis.set_label_position("right")
  curve2, = ax1.plot(ws, zs, c="gainsboro",label=zlabel,linestyle="solid")

  ax2 = ax1
  # ax2 = ax1.twinx()
  # ax2.yaxis.set_ticks_position("left")
  # ax2.yaxis.set_label_position("left")
  # ax2.set_ylim(0,300) #multiproto
  # ax2.set_ylim(450,800) # netchain
  # ax2.set_ylim(38000, 39000) #switch
  # ax2.set_ylabel(ylabel, fontsize=9)
  # ax2.set_yscale('linear')
  ax2.grid(False)
  curve2, = ax2.plot(xs,ys,c="#0072B2",label=ylabel,linestyle="solid")


  # fig.legend(loc=(0.2,0.7),fontsize='small') # switch
  fig.legend(loc=(0.15,0.7),fontsize='small') # Multiproto
  # fig.legend(loc=(0.55,0.7),fontsize='small') # netchain


  f = "%s/%s.png" % (outdir,label)
  f = f.replace("//","/")
  print("writing to", f)
  fig.savefig(f, format="png")
  plt.close(fig)
  print("done")

# def line (outdir, xs, ys, label, xlabel, ylabel, ylim=None,xlim=None,colors=None):
#   plt.rc("font", size=9)
#   plt.rc("ytick", labelsize=9)
#   plt.rc("xtick", labelsize=9)
#   fig = plt.figure(figsize=(3.7,1.0))
#   # fig.suptitle(label)
#   plt.xlabel(xlabel, fontsize=9)
#   plt.ylabel(ylabel, fontsize=9)
#   if ylim is not None: plt.ylim(ylim[0],ylim[1])
#   if xlim is not None: plt.xlim(xlim[0],xlim[1])
#   if colors is None:
#     c = None
#     s = None
#   else:
#     c = [-1*c for c in colors]
#     s = [c * 1000 for c in colors]
#   plt.plot(xs,ys)
#   # f =  "%s/%s.pdf" % (outdir,label)
#   f = "%s/%s.png" % (outdir,label)
#   f = f.replace("//","/")
#   print("writing to", f)
#   fig.savefig(f, format="png")
#   plt.close(fig)
#   print("done")



def gen_qd_vars_data(qrows):
  count = {}
  data = []                     #  list of time & num qvars
  goat = 0
  for r in qrows:
    if r[2] == "+":
      x = r[3]
      if x in count:
        count[x] = count[x] + 1
      else:
        count[x] = 1
      num_vars = len(count.keys())
      goat = max(num_vars, goat)
      data.append((float(r[0]), num_vars))
    elif r[2] == "-":
      x = r[3]
      if x in count:
        count[x] = count[x] - 1
      else:
        print("went negative...", q)
        return
      if count[x] == 0:
        del count[x]
      data.append((float(r[0]), len(count.keys())))
    else:
      print("unrecognized row:", q)
      return
  print("removed", goat - len(count.keys()), "vars")
  return data

def qd_vars(start, qrows):
  data = gen_qd_vars_data(qrows)
  data = [row for row in data if row[0] <= start + timeout]
  return (  [row[0] - start for row in data]
          , [row[1] for row in data] )

def size_rows(rows):
  return [row for row in rows if row[0] == "size"]

def q_rows(rows):
  return [[float(row[0])] + row[1:] for row in rows if row[0] != "size"]


def plot(rows):
  print("cleaning", len(rows), "rows")
  # number quantifiers
  qrows = q_rows(rows)
  qtime = [row[0] for row in qrows]
  start = qtime[0]
  qs = [int(row[1]) for row in qrows if row[0] <= start + timeout]
  qtime = [t - start for t in qtime if t <= start + timeout]
  # line("graphs", qtime, qs, "Netchain_Q", "Time (ms)", "# Quantifiers")
  # number of dp vars
  (vtime, num_vs) = qd_vars(start, qrows)
  # line("graphs", vtime, num_vs, "Netchain_V", "Time (ms)", "# data plane vars"  )
  lines_2("graphs", vtime, num_vs,  qtime, qs, "Netchain", "Time (mins)", "# data plane vars", "# foralls")
  return start

# def size_plot(start, rows):
#   srows = size_rows(rows)
#   stime = [float(row[1]) - start for row in srows]
#   ss = [int(row[2]) for row in srows]
#   line("graphs", stime, ss, "Netchain_S", "time (ms)", "#quantifiers")

def main ():
  parser = argparse.ArgumentParser(description="read in datafile")
  parser.add_argument('f', type=str)
  args = parser.parse_args()
  rows = []
  print("reading", args.f)
  with open(args.f) as data:
    rows = list(csv.reader(data))
  st = plot(rows)
  # size_plot(st,rows)

if __name__ == "__main__": main()

#!/usr/bin/env python3
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
  plt.rcParams['axes.grid'] = False
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

class D():
    def __init__(self, name, time, assum_size=0, annot_n=0, annot_s=0):
        self.name = name
        self.time = time
        self.assum_size = assum_size
        self.annot_n = annot_n
        self.annot_s = annot_s
        self.did_annotate = bool(assum_size + annot_n > 0 or annot_s > 0)


def data():
    return [D("ecmp", 1.4e-2),
            D("netpaxos_acceptor", 1.5e-2),
            D("resubmit", 8.7e-3),
            D("heavy_hitter_1", 1.3e0),
            D("arp",7.9e1),
            D("ndp_router", 2.3e2),
            D("07-multiprotocol", 6.6e2),
            D("mc_nat", 9.5e-3, assum_size=1),
            D("ts_switching", 1.1e-2, assum_size=3),
            D("heavy_hitter_2", 2.1e-2, assum_size=3),
            D("flowlet", 4.2e-2, assum_size=3),
            D("linearroad", 4.8e-1, annot_n=7, annot_s=63),
            D("hula", 6.2e-1, assum_size=1, annot_n=1, annot_s=7),
            D("netchain", 1.1e0, assum_size=5, annot_n=3, annot_s=25),
            D("simple_nat", 7.7e1, annot_n=3, annot_s=31)
            ]


def plot_survey():
    points = data()
    w = 0.3
    xlabels = [i + (w/2.0) for i,_ in enumerate(points)]
    x1 = [i for i,_ in enumerate(points)]
    y1 = [p.time for p in points]
    x2 = [i + w  for i,_ in enumerate(points)]
    y2 = [p.annot_s + p.assum_size for p in points]
    # Create figure and axis #1
    fig, ax1 = plt.subplots(figsize=(5,5))# plot line chart on axis #1
    plt.xticks(xlabels, [p.name for p in points], rotation="vertical", fontsize=5)
    ax1.bar(x1,y1,width=0.3)
    ax1.set_ylabel('inference time')
    ax1.legend(['inference time'], loc="upper left")
    ax1.set_yscale('log')
    # set up the 2nd axis
    ax2 = ax1.twinx()
    # plot bar chart on axis #2
    ax2.bar(x2, y2, width=0.3, color='orange')
    ax2.set_ylabel('annotation size')
    ax2.set_ylim(0,100)
    ax2.legend(['annotation size'], loc="upper right")
    fig.savefig("survey.pdf")
    plt.close(fig)
    print("done")


if __name__ == "__main__":
    plot_survey()

import pandas as pd
import time
import matplotlib.pyplot as plt
import numpy as np

import os
import subprocess
import shlex

from io import StringIO

benchmarks = ["flatten", "mlp", "curry", "graph", "filter", "parser"]
cmd = "./sandbox/target/scala-2.12/sandbox-out "
perfcmd = "perf record -F 30000 --strict-freq -o bench_results/{0}.data ./sandbox/target/scala-2.12/sandbox-out {0}"
perfrepcmd = "perf report -i bench_results/{0}.data -F Overhead,Symbol -t,"

colname = "@stack"
pow2unit = {
  -2: "s",
  -1: "ms",
  0: "μs",
  1: "ns",
}

def formatmicros(v: float):
    s = "{:.2f}".format(v)
    lead = s.split(".")[0].strip("0")
    i = 1
    if len(lead) == 0:
        while len(lead) == 0:
            v = v * 1000
            lead = "{:.2f}".format(v).split(".")[0].strip("0")
            i += 1
    if len(lead) > 3:
        while len(lead) > 3:
            v = v / 1000
            lead = "{:.2f}".format(v).split(".")[0].strip("0")
            i -= 1
    return (v, i)


def idx2name(t):
    if t[1] == 1:
        return t[0]
    elif t[1] == 2:
        return t[0] + " (" + colname + ")"
    else:
        raise ValueError("Unknown value")

def read_txt(fname):
    with open(fname) as perf:
        plines = [l for l in perf if l.strip() != "" and l[0] != "#"]
        todf = []
        for l in plines:
            (perc, sym) = l.split(",")
            (perc, sym) = perc.strip(), sym.strip()[4:]
            todf.append((perc, sym))

        df = pd.DataFrame(todf, columns=["perc", "sym"])
        df['perc'] = df['perc'].str[:-1].astype(float) / 100
        df = df.set_index('sym')
        return df

def read_txts(bench):
    df1 = read_txt(f"bench_results/{bench}1.txt")
    df2 = read_txt(f"bench_results/{bench}2.txt")
    df = df1.merge(df2, how='outer', left_index=True, right_index=True, suffixes=('1', '2')).fillna({'scalanative_localalloc': 0})
    if 'scalanative_localalloc' in df.index:
        df.loc['scalanative_localalloc'].fillna(0, inplace=True)
    return df


def heap_perc(df):
    heapcols = ['Heap_AllocSmall', 'Heap_Alloc', 'Heap_allocSmallSlow', 'Marker_MarkRoots', 'scalanative_alloc_small', 'Marker_Mark']
    heapcols = [c for c in heapcols if c in df.index]
    (p1, p2) = tuple(df.loc[heapcols].sort_values(['perc1', 'perc2'], ascending=False).iloc[0])
    return (p1, p2, df.loc['scalanative_localalloc']['perc2'] if 'scalanative_localalloc' in df.index else 0)

def barchart(speedups):
    labels = benchmarks
    heap = []
    stack = []
    lalloc = []
    for b in benchmarks:
        (h, s, l) = heap_perc(read_txts(b))
        heap.append(h * 100)
        stack.append(s * 100 / speedups.loc[b])  # TODO: divide by speedup
        lalloc.append(l * 100 / speedups.loc[b]) # TODO: divide by speedup

    width = 0.28

    x = np.arange(len(labels))
    fig, ax = plt.subplots()
    heap_bars = ax.bar(x - width / 2, heap, width, label="heap", color='none', edgecolor="#b019dd", hatch='/')
    stack_bars = ax.bar(x + width / 2, stack, width, label="heap2", color='none', edgecolor=(0, 1/2, 1/2), hatch='o')
    lalloc_bars = ax.bar(x + width / 2, lalloc, width, label="@stack", color='none', edgecolor=(0, 1/2, 1/2), hatch='++', bottom=stack)

    ax.set_ylabel('Heap Overhead (% over total)')
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    ax.legend()


    fontsize = 7
    ax.bar_label(heap_bars, padding=3, fontsize=fontsize)
    ax.bar_label(lalloc_bars, labels=[f"{s + l:.2f}" for (s, l) in zip(stack, lalloc)],padding=3, fontsize=fontsize)

    fig.tight_layout()
    fig.savefig('bars.pdf')


def main():
    global perfcmd
    perf_available = False

    if not perf_available:
        from pathlib import Path
        perfcmd = str(Path.cwd() / perfcmd[perfcmd.find("sandbox/target"):])

    for b in benchmarks:
        for mode in [1, 2]:
            name = b + str(mode)
            tmp = perfcmd.format(name)
            print("Running " + tmp)
            gc_file = "bench_results/{}.gc".format(name)
            completion = subprocess.run(shlex.split(tmp), check=True, env=dict(os.environ, SCALANATIVE_STATS_FILE=gc_file))

            if perf_available:
                tmp = perfrepcmd.format(name)
                ofile = f"bench_results/{name}.txt"
                print("Running " + tmp + f" > {ofile}")
                with open(ofile, "w") as f:
                    completion = subprocess.run(shlex.split(tmp), check=True, stdout=f)

    rows = []

    for b in benchmarks:
        for mode in [1, 2]:
            name = b + str(mode)
            tmp = cmd + name
            print("Running " + tmp)
            start = time.time_ns()
            completion = subprocess.run(shlex.split(tmp), capture_output=True, check=True)
            tottime = time.time_ns() - start

            out = completion.stderr.decode("utf-8").strip()

            gc_file = "bench_results/{}.gc".format(name)
            df = pd.read_csv(gc_file)

            n_collections = len(df)
            shstack_peak = df["shstack_peak"].max()
            mark_time_med = df["mark_time_ns"].median()
            mark_time_tot = df["mark_time_ns"].sum()
            sweep_time_med = df["sweep_time_ns"].median()
            sweep_time_tot = df["sweep_time_ns"].sum()

            out = out + f",{n_collections},{shstack_peak},{mark_time_med},{mark_time_tot},{sweep_time_med},{sweep_time_tot},{tottime}"

            rows.append(out)


    header = "name,mode,avg,std"
    other_cols = "n_collections,shstack_peak,mark_time_med,mark_time_tot,sweep_time_med,sweep_time_tot,tottime"
    csv = f"{header},{other_cols}\n" + "\n".join(rows)

    df = pd.read_csv(StringIO(csv))

    pivoted = df.drop(columns=other_cols.split(",")).pivot(index='name', columns='mode')
    pivoted.columns = pivoted.columns.to_flat_index().map(idx2name)
    pivoted = pivoted.sort_values("avg")

    speedup = pivoted["avg"] / pivoted["avg (@stack)"]
    if perf_available:
        barchart(speedup)

    units = pivoted["avg"].map(lambda v: pow2unit[formatmicros(v)[1]])
    power = pivoted["avg"].map(lambda v: formatmicros(v)[1])

    # Formatting
    numcols = pivoted.columns.tolist()

    pivoted[numcols] = pivoted[numcols].mul(power.map(lambda v: 1000**(v-1)), axis=0)

    pivoted[numcols] = pivoted[numcols].applymap("{:.2f}".format)
    pivoted["Avg Speedup"] = speedup.map("{:.2f}x".format)
    pivoted.index = pivoted.index + " (" + units + ")"


    df1 = df.drop(columns=["avg", "std"])
    df1["mark_time_tot"] = df1["mark_time_tot"].apply(lambda x: x / 10**6)
    df1["sweep_time_tot"] = df1["sweep_time_tot"].apply(lambda x: x / 10**6)
    df1["mark_time_med"] = df1["mark_time_med"].apply(lambda x: x / 10**3)
    df1["sweep_time_med"] = df1["sweep_time_med"].apply(lambda x: x / 10**3)
    df1["tottime"] = df["tottime"].apply(lambda x: x / 10**6)
    # df1 = df1.drop(columns=['tottime'])
    df1 = df1.set_index(['name', 'mode'])
    # df1["gc_perc"] = (df["mark_time_tot"] + df["sweep_time_tot"]) / df["tottime"]
    # print(df1.drop(columns=['tottime']).set_index(['name', 'mode']).round(2).to_latex(multirow=True))
    df1.to_csv("tables/gc_stats.csv")
    pivoted.to_csv("tables/runtime.csv")


if __name__ == '__main__':
    main()

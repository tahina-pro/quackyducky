#!/usr/bin/env python3
"""Summarize bench.csv (from bench_dupcheck.c) as Markdown tables.

For each family: one row per parameter value with the time per call of each
variant, then the empirical exponent of each variant, i.e. the least-squares
slope of log(time) against log(input bytes) over the points of the family
(only points >= 2 us, to avoid timer noise). A slope of 1 means linear in the
input size, 2 quadratic; for families whose parameter is a depth (B1, B3) the
exponential growth shows up as a slope that keeps increasing, so the average
time ratio between consecutive depths is also reported.
Stdlib only.
"""
import csv
import math
import sys
from collections import OrderedDict, defaultdict

VARIANTS = ["wf", "verified-b", "verified-u", "sort", "hash-canon",
            "hash-naive", "hash0-canon"]
RESULT = {"0": "ok", "1": "dup", "2": "bound"}


def fmt(ns):
    ns = float(ns)
    if ns < 1e3:
        return "%.0f ns" % ns
    if ns < 1e6:
        return "%.1f us" % (ns / 1e3)
    if ns < 1e9:
        return "%.1f ms" % (ns / 1e6)
    return "%.2f s" % (ns / 1e9)


def slope(points):
    pts = [(math.log(b), math.log(t)) for b, t in points if t >= 2000]
    if len(pts) < 2:
        return None
    n = len(pts)
    mx = sum(p[0] for p in pts) / n
    my = sum(p[1] for p in pts) / n
    sxx = sum((p[0] - mx) ** 2 for p in pts)
    if sxx == 0:
        return None
    return sum((p[0] - mx) * (p[1] - my) for p in pts) / sxx


def main(path):
    fams = OrderedDict()
    with open(path) as f:
        for r in csv.DictReader(f):
            fams.setdefault(r["family"], []).append(r)
    for fam, rows in fams.items():
        variants = [v for v in VARIANTS if any(r["variant"] == v for r in rows)]
        params = OrderedDict()
        for r in rows:
            params.setdefault(r["param"], {})[r["variant"]] = r
        print("### %s\n" % fam)
        print("| param | bytes | D | N | " + " | ".join(variants) + " |")
        print("|---" * (4 + len(variants)) + "|")
        series = defaultdict(list)
        for p, byv in params.items():
            any_r = next(iter(byv.values()))
            cells = []
            for v in variants:
                r = byv.get(v)
                if r is None:
                    cells.append("(capped)" if v in series else "-")
                    continue
                res = RESULT.get(r["result"], r["result"])
                cells.append("%s%s" % (fmt(r["ns"]),
                                       "" if res == "ok" else " (%s)" % res))
                series[v].append((float(r["bytes"]), float(r["ns"]),
                                  float(r["param"])))
            print("| %s | %s | %s | %s | %s |" % (p, any_r["bytes"], any_r["D"],
                                                 any_r["N"], " | ".join(cells)))
        print()
        line = []
        for v in variants:
            s = slope([(b, t) for b, t, _ in series[v]])
            line.append("%s: %s" % (v, "n/a" if s is None else "%.2f" % s))
        print("Empirical exponent (time vs bytes): " + ", ".join(line) + "\n")
        if fam.startswith("B1") or fam.startswith("B3"):
            line = []
            for v in variants:
                pts = series[v]
                if len(pts) >= 2:
                    k = pts[-1][2] - pts[0][2]
                    ratio = (pts[-1][1] / pts[0][1]) ** (1.0 / k) if k else 0
                    bratio = (pts[-1][0] / pts[0][0]) ** (1.0 / k) if k else 0
                    line.append("%s: x%.2f" % (v, ratio))
            print("Average time ratio per unit of depth parameter "
                  "(input bytes: x%.2f): %s\n" % (bratio, ", ".join(line)))
        # scratch sizes at the largest parameter
        last = list(params.values())[-1]
        sc = ["%s %s B" % (v, last[v]["scratch"]) for v in variants
              if v in last and last[v]["scratch"] != "0"]
        if sc:
            print("Scratch at the largest parameter: " + ", ".join(sc) + "\n")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "bench.csv")

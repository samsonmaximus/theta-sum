"""Summarize a file of "p S(p)" lines produced by `thetasum range`.

Checks the threshold claims of Proposition 1.3 within the range of the data and
prints the Table 3 statistics of S(p)/p - (1/2) log p.

Usage: python3 -I analyze.py values.txt [values2.txt ...]
"""
import math, sys

def main(paths):
    data = []
    for path in paths:
        with open(path) as fh:
            for line in fh:
                p, s = line.split()
                data.append((int(p), int(s)))
    data.sort()
    pmax = data[-1][0]
    print(f"{len(data)} odd primes, {data[0][0]} <= p <= {pmax}")

    # Proposition 1.3: last prime with S(p) <= m p, for m = 0..5
    for m in range(6):
        bad = [p for p, s in data if s <= m * p]
        last = bad[-1] if bad else None
        print(f"  S(p) > {m}p fails last at p = {last}" + ("" if last is None else f" (S = {dict(data)[last]})"))

    # Table 3 rows, restricted to the data range
    rows = [(10**3, 2 * 10**5), (2 * 10**5, 10**6), (10**6, 2 * 10**6), (2 * 10**6, 3 * 10**6), (3 * 10**6, 4 * 10**6)]
    print("  range              primes    mean   st.dev    min (at p)         max (at p)")
    for lo, hi in rows:
        vals = [(s / p - 0.5 * math.log(p), p) for p, s in data if lo < p <= hi]
        if not vals or lo >= pmax:
            continue
        n = len(vals)
        mean = sum(v for v, _ in vals) / n
        sd = math.sqrt(sum((v - mean) ** 2 for v, _ in vals) / (n - 1))
        mn, mx = min(vals), max(vals)
        print(f"  ({lo:.0e}, {hi:.0e}]  {n:7d}  {mean:.4f}  {sd:.4f}  {mn[0]:.3f} ({mn[1]})  {mx[0]:.3f} ({mx[1]})")

    # minima of S(p)/p above the thresholds, as quoted in Section 10.2
    for thr in (3119, 58013):
        sub = [(s / p, p) for p, s in data if p > thr]
        print(f"  min S(p)/p over {thr} < p <= {pmax}: {min(sub)[0]:.4f} at p = {min(sub)[1]}")

if __name__ == "__main__":
    main(sys.argv[1:])

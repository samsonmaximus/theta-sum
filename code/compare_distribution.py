"""Compare the empirical distribution of X_p - c0 = S(p)/p - (1/2)log p - c0 with samples of the
limiting law of Theorem G (output of haar_sample.c).

Usage: python3 -I compare_distribution.py values.txt samples.txt [lo hi]
"""
import math, sys
import numpy as np

C0 = 0.2399341036320695

def main(values, samples, lo=2e5, hi=1e6):
    d = np.loadtxt(values)
    p, S = d[:, 0], d[:, 1]
    obs = (S / p - 0.5 * np.log(p) - C0)[(p > lo) & (p <= hi)]
    sim = np.loadtxt(samples)
    a, b = np.sort(obs), np.sort(sim)
    grid = np.concatenate([a, b])
    ks = np.max(np.abs(np.searchsorted(a, grid, side="right") / len(a) - np.searchsorted(b, grid, side="right") / len(b)))
    ne = len(a) * len(b) / (len(a) + len(b))
    print(f"primes in ({lo:.0e},{hi:.0e}]: n={len(a)}, mean {obs.mean():+.4f}, sd {obs.std():.4f}")
    print(f"limit-law samples: n={len(b)}, mean {sim.mean():+.4f}, sd {sim.std():.4f}")
    print(f"Kolmogorov-Smirnov distance {ks:.4f} (5% critical value {1.36 / math.sqrt(ne):.4f})")
    print("quantile   primes   limit law")
    for q in (0.001, 0.01, 0.05, 0.25, 0.5, 0.75, 0.95, 0.99, 0.999):
        print(f"  {q:6.3f}  {np.quantile(obs, q):+.3f}   {np.quantile(sim, q):+.3f}")

if __name__ == "__main__":
    args = sys.argv[1:]
    main(args[0], args[1], *(float(x) for x in args[2:4]))

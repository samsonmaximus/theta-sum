"""Figure for the distribution paper: X_p - c0 over primes vs. Haar samples of (4/pi) R_K.

Usage: python3 -I plot_limit_law.py values.txt samples1.txt [samples2.txt ...] out.pdf
values.txt: lines "p S(p)" (e.g. from data/S_p_upto_6e6.txt.gz, decompressed);
samples*.txt: one value of (4/pi) R_K(x) per line (code/haar_sample.c).
"""
import sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

C0 = 0.2399341036
vals, samples, out = sys.argv[1], sys.argv[2:-1], sys.argv[-1]
L = np.loadtxt(vals)
p, s = L[:, 0], L[:, 1]
sel = p > 1e6
X = s[sel] / p[sel] - 0.5 * np.log(p[sel]) - C0
H = np.concatenate([np.loadtxt(f) for f in samples])

fig, ax = plt.subplots(1, 2, figsize=(9, 3.4))
bins = np.linspace(-3, 3, 121)
ax[0].hist(H, bins=bins, density=True, histtype="stepfilled", color="#c8d6e5", label=f"model: Haar samples ($n={len(H)}$)")
ax[0].hist(X, bins=bins, density=True, histtype="step", color="#1f3b73", lw=1.2, label=f"primes $10^6<p\\leq5.5\\cdot10^6$ ($n={len(X)}$)")
ax[0].set_xlabel(r"$X_p-c_0$")
ax[0].set_ylabel("density")
ax[0].set_ylim(0, 0.85)
ax[0].legend(fontsize=7, frameon=False, loc="upper left")
t = np.linspace(0, 2.6, 60)
for data, lab, st in [(X, "primes", "-"), (H, "model", "--")]:
    surv = [(np.abs(data) > u).mean() for u in t]
    ax[1].semilogy(t, surv, st, label=lab, color="#1f3b73" if lab == "primes" else "#7f8fa6")
ax[1].set_xlabel(r"$t$")
ax[1].set_ylabel(r"proportion with $|X_p-c_0|>t$")
ax[1].legend(fontsize=7, frameon=False)
fig.tight_layout()
fig.savefig(out)
print("saved", out)

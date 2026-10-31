"""Compare c0(q;r) from Theorem J(c) with the means of X_p over primes p = r mod q (10^3 < p), for odd q <= 45.
Usage: python3 -I class_means_test.py values.txt out.txt
"""
import os, sys, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from char_expansion import W_coefficients, C0
from sympy import primerange
primes=np.array(list(primerange(3,20000)),dtype=np.int64)
L=np.loadtxt(sys.argv[1])  # lines 'p S(p)', e.g. data/S_p_upto_6e6.txt.gz decompressed
p=L[:,0].astype(np.int64); s=L[:,1]
sel=p>1000; p=p[sel]; X=s[sel]/p-0.5*np.log(p)
cache={}
def Ws(f):
    if f not in cache: cache[f]=W_coefficients(f,primes)
    return cache[f]
rows=[]; zmax=0
for q in range(3,46,2):
    fs=[f for f in range(3,q+1,2) if q%f==0]
    for r in range(1,q):
        if math.gcd(r,q)!=1: continue
        pred=C0+4/math.pi*sum((W*chi[r%f]).real for f in fs for chi,W,_,_ in Ws(f))
        m=(p%q)==r; obs=X[m].mean(); se=X[m].std()/math.sqrt(m.sum())
        z=(obs-pred)/se; rows.append((q,r,pred,obs,se,z)); zmax=max(zmax,abs(z))
zs=np.array([r[5] for r in rows])
print("classes:",len(rows)," max|z|=%.2f  mean z=%.3f  sd z=%.3f"%(zmax,zs.mean(),zs.std()))
print("spread of predicted c0(q;r): min %.4f max %.4f"%(min(r[2] for r in rows),max(r[2] for r in rows)))
for r in sorted(rows,key=lambda r:-abs(r[5]))[:5]: print("q=%d r=%d pred=%.4f obs=%.4f se=%.4f z=%.2f"%r)
with open(sys.argv[2],'w') as fh:
    fh.write("# q r c0(q;r)_TheoremJ mean_over_primes_1e3<p<=5.5e6 std_error z\n")
    for r in rows: fh.write("%d %d %.6f %.6f %.6f %.3f\n"%r)

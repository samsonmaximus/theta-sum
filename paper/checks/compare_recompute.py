import gzip,glob
d={int(a):int(b) for a,b in (l.split() for l in gzip.open('../../data/S_p_upto_6e6.txt.gz','rt'))}
n=bad=0
for f in glob.glob('./out*.txt'):
    for l in open(f):
        p,s=map(int,l.split()); n+=1
        if d[p]!=s: bad+=1; print("MISMATCH",p,s,d[p])
print("compared",n,"mismatches",bad, "expected",sum(1 for p in d if p>4000000))

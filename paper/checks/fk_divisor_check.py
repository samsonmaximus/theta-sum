# Check: F_k(p)/k = -(1/pi) log k + O(1) if k | p+1 or k | 2p-1, and +(1/pi) log k + O(1) if k | p-1 or 2p+1.
import math
def F(k,n):
    return sum(math.tan(math.pi*n*t/k) for t in range(1,(k-1)//2+1))
for k in [101, 1001, 10001, 100001]:
    for label, n in [("p=-1 (k|p+1)", k-1), ("p=+1 (k|p-1)", 1), ("2p=1 (k|2p-1)", (k+1)//2), ("2p=-1 (k|2p+1)", (k-1)//2)]:
        v = F(k,n)/k
        print(k, label, round(v,4), "  v -/+ (log k)/pi:", round(v - (math.log(k)/math.pi if v>0 else -math.log(k)/math.pi),4))

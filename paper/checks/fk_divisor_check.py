#!/usr/bin/env python3
"""Section 1.3 of theta_sum_conj33.pdf: F_k(p)/k = -(1/pi) log k + O(1) whenever k | p + 1.
F_k(n) depends only on n mod k, so p = -1 (mod k) is the case n = k - 1; the last column,
F_k(p)/k + (log k)/pi, stays bounded as k grows.
Usage: python3 -I fk_divisor_check.py
"""
import math


def F(k, n):
    return sum(math.tan(math.pi * n * t / k) for t in range(1, (k - 1) // 2 + 1))


print("k        F_k(p)/k    F_k(p)/k + (log k)/pi   (p = -1 mod k)")
for k in [101, 1001, 10001, 100001, 1000001]:
    v = F(k, k - 1) / k
    print(f"{k:<8d} {v:10.4f}  {v + math.log(k) / math.pi:10.4f}")

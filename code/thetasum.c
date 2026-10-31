/* Exact computation of the theta-function sum
 *   S(p) = sum_{h=1}^{p-1} sum_{j=1}^{p-1} (-1)^{j+1+floor(hj/p)}
 * via Lemma 2.5 of theta_sum_v3.pdf:
 *   S(p) = (p-1)^3/4 - 4 sum_{a odd, 3<=a<=p-2} F(2p,a),
 *   F(x,y) = sum_{c=1}^{floor((y-1)/2)} floor(cx/y),
 * evaluated by the reciprocity  F(qy+r,y) = q*C(U+1,2) + F(r,y)  (U = floor((y-1)/2))
 * and  F(r,y) + F(y,r) = floor((y-1)/2)*floor((r-1)/2)  for coprime r,y.
 * All arithmetic is exact (__int128).
 *
 * Usage:
 *   thetasum brute P          compare with the O(p^2) definition for all odd primes < P
 *   thetasum one p            print S(p) for one odd prime p
 *   thetasum range A B        for every odd prime A<=p<=B print "p S(p)"
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef __int128 i128;
typedef int64_t i64;

static i128 F(i64 x, i64 y) {
    /* F(x,y) with gcd(x,y)=1, x>=0, y>=1, iterative */
    i128 acc = 0; int sign = 1;
    while (y > 1) {
        i64 U = (y - 1) / 2;
        i64 q = x / y, r = x % y;
        acc += sign * ((i128)q * ((i128)U * (U + 1) / 2));
        if (r == 0) break;               /* only when y | x; then F(0,y)=0 */
        /* F(r,y) = U*floor((r-1)/2) - F(y,r) */
        acc += sign * ((i128)U * ((r - 1) / 2));
        sign = -sign;
        x = y; y = r;
    }
    return acc;
}

static i128 S_fast(i64 p) {
    i128 s = (i128)(p - 1) * (p - 1) * (p - 1) / 4;
    i128 t = 0;
    for (i64 a = 3; a <= p - 2; a += 2) t += F(2 * p, a);
    return s - 4 * t;
}

static i64 S_brute(i64 p) {
    i64 s = 0;
    for (i64 h = 1; h < p; h++)
        for (i64 j = 1; j < p; j++) {
            i64 e = j + 1 + (h * j) / p;
            s += (e & 1) ? -1 : 1;
        }
    return s;
}

static int is_prime(i64 n) {
    if (n < 2) return 0;
    if (n % 2 == 0) return n == 2;
    for (i64 d = 3; d * d <= n; d += 2) if (n % d == 0) return 0;
    return 1;
}

static void print128(i128 v) {
    char buf[64]; int n = 0, neg = v < 0;
    unsigned __int128 u = neg ? -(unsigned __int128)v : (unsigned __int128)v;
    if (u == 0) buf[n++] = '0';
    while (u) { buf[n++] = '0' + (int)(u % 10); u /= 10; }
    if (neg) putchar('-');
    while (n) putchar(buf[--n]);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see source\n"); return 2; }
    if (!strcmp(argv[1], "brute")) {
        i64 P = atoll(argv[2]); int bad = 0, cnt = 0;
        for (i64 p = 3; p < P; p += 2) if (is_prime(p)) {
            cnt++;
            if (S_fast(p) != (i128)S_brute(p)) { printf("MISMATCH p=%lld\n", (long long)p); bad++; }
        }
        printf("checked %d odd primes < %lld, mismatches: %d\n", cnt, (long long)P, bad);
        return bad != 0;
    }
    if (!strcmp(argv[1], "one")) {
        i64 p = atoll(argv[2]);
        printf("%lld ", (long long)p); print128(S_fast(p)); putchar('\n');
        return 0;
    }
    if (!strcmp(argv[1], "range") && argc >= 4) {
        i64 A = atoll(argv[2]), B = atoll(argv[3]);
        if (A < 3) A = 3;
        if (A % 2 == 0) A++;
        for (i64 p = A; p <= B; p += 2) if (is_prime(p)) {
            printf("%lld ", (long long)p); print128(S_fast(p)); putchar('\n');
        }
        return 0;
    }
    fprintf(stderr, "bad arguments\n"); return 2;
}

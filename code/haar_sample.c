/* Sample the limiting law of Theorem G: draws of (4/pi) R_K(x), x "Haar-random"
 * (a uniform random 62-bit integer coprime to all odd primes < K; for k < K the
 * residues x mod k are then uniform and consistent up to O(k / 2^62)).
 * Usage: haar_sample K nsamples seed > samples.txt
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static uint64_t s[2];
static uint64_t rnd(void) { /* xorshift128+ */
    uint64_t x = s[0], y = s[1]; s[0] = y; x ^= x << 23; s[1] = x ^ y ^ (x >> 17) ^ (y >> 26); return s[1] + y;
}

int main(int argc, char **argv) {
    int K = atoi(argv[1]); long n = atol(argv[2]); s[0] = 0x9E3779B97F4A7C15ULL ^ atol(argv[3]); s[1] = 0xD1B54A32D192ED03ULL;
    double **F = calloc(K, sizeof(double *));
    for (int k = 3; k < K; k += 2) {
        F[k] = calloc(k, sizeof(double));
        double *T = malloc(sizeof(double) * k);
        for (int j = 0; j < k; j++) T[j] = tan(M_PI * j / k);
        for (int x = 1; x < k; x++) {
            if (gcd(x, k) != 1) continue;
            double acc = 0; int r = 0;
            for (int t = 1; t <= (k - 1) / 2; t++) { r += x; if (r >= k) r -= k; acc += T[r]; }
            F[k][x] = acc / ((double)k * k);
        }
        free(T);
    }
    int *primes = malloc(sizeof(int) * K), np = 0;
    for (int m = 3; m < K; m += 2) { int ok = 1; for (int d = 3; d * d <= m; d += 2) if (m % d == 0) { ok = 0; break; } if (ok) primes[np++] = m; }
    for (long i = 0; i < n; ) {
        uint64_t x = rnd() >> 2; int ok = 1;
        for (int j = 0; j < np; j++) if (x % primes[j] == 0) { ok = 0; break; }
        if (!ok) continue;
        double R = 0;
        for (int k = 3; k < K; k += 2) R += F[k][x % k];
        printf("%.6f\n", 4 / M_PI * R);
        i++;
    }
    return 0;
}

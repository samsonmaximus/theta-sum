/* Exact second moment of R_K(x) = sum_{3<=k<K, k odd} F_k(x)/k^2 for x uniform on the
 * reduced residues modulo lcm of the odd numbers below K ("Haar measure"), where
 * F_k(x) = sum_{t=1}^{(k-1)/2} tan(pi x t / k).
 *
 * Uses: F_k depends on x mod k; conditionally on x mod g (g = gcd(k,k')), the residues
 * x mod k and x mod k' are independent and uniform over the reduced residues lying over
 * x mod g (Chinese remainder theorem). Hence
 *   E[F_k F_k'] = E_{s in (Z/g)^*} [ a_{k,g}(s) a_{k',g}(s) ],
 * a_{k,g}(s) = mean of F_k(x) over reduced x mod k with x = s mod g.
 *
 * Output: K, E[R_K^2], sigma_K = (4/pi) sqrt(E[R_K^2]) for K = step, 2 step, ..., Kmax.
 * Usage: haar_variance Kmax step
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    int Kmax = argc > 1 ? atoi(argv[1]) : 1001;
    int step = argc > 2 ? atoi(argv[2]) : 100;
    /* cond[k][g] -> array over s in [0,g) (only reduced s used) of a_{k,g}(s); g | k, g odd >= 3 */
    double ***cond = calloc(Kmax + 1, sizeof(double **));
    for (int k = 3; k < Kmax; k += 2) {
        double *T = malloc(sizeof(double) * k);
        for (int j = 0; j < k; j++) T[j] = tan(M_PI * j / k);
        double *Fx = calloc(k, sizeof(double));
        for (int x = 1; x < k; x++) {
            if (gcd(x, k) != 1) continue;
            double s = 0; int r = 0;
            for (int t = 1; t <= (k - 1) / 2; t++) { r += x; if (r >= k) r -= k; s += T[r]; }
            Fx[x] = s;
        }
        cond[k] = calloc(k + 1, sizeof(double *));
        for (int g = 3; g <= k; g += 2) {
            if (k % g) continue;
            double *a = calloc(g, sizeof(double));
            int *cnt = calloc(g, sizeof(int));
            for (int x = 1; x < k; x++) if (gcd(x, k) == 1) { a[x % g] += Fx[x]; cnt[x % g]++; }
            for (int s = 0; s < g; s++) if (cnt[s]) a[s] /= cnt[s];
            free(cnt);
            cond[k][g] = a;
        }
        free(T); free(Fx);
    }
    double total = 0;
    int nextK = step + 1;
    /* accumulate E[R_K^2] incrementally in K: add pairs (k,k') with max(k,k') = new k */
    for (int k = 3; k < Kmax; k += 2) {
        double add = 0;
        for (int kk = 3; kk <= k; kk += 2) {
            int g = gcd(k, kk);
            if (g < 3) continue;
            double *a = cond[k][g], *b = cond[kk][g];
            double s = 0; int n = 0;
            for (int r = 1; r < g; r++) if (gcd(r, g) == 1) { s += a[r] * b[r]; n++; }
            double e = s / n / ((double)k * k * (double)kk * kk);
            add += (kk == k) ? e : 2 * e;
        }
        total += add;
        if (k + 2 >= nextK || k + 2 >= Kmax) {
            printf("%d %.10f %.8f\n", k + 2, total, 4 / M_PI * sqrt(total));
            fflush(stdout);
            nextK += step;
        }
    }
    return 0;
}

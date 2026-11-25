/* Read nauty multig -T records from stdin. For m <= 14, there are
   at most 2^14 candidate edge subsets, so tau is its residue mod 65521. */
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { P = 65521, MAX_M = 14 };
static unsigned inverse[P];

static int read_number(const char **s) {
    while (isspace((unsigned char)**s)) ++*s;
    if (!isdigit((unsigned char)**s)) return -1;
    int value = 0;
    while (isdigit((unsigned char)**s)) {
        value = 10 * value + (*(*s)++ - '0');
        if (value > MAX_M) return -1;
    }
    return value;
}

static unsigned determinant(unsigned a[MAX_M][MAX_M], int n) {
    unsigned result = 1;
    for (int col = 0; col < n; ++col) {
        int pivot = col;
        while (pivot < n && !a[pivot][col]) ++pivot;
        if (pivot == n) return 0;
        if (pivot != col) {
            for (int j = col; j < n; ++j) {
                unsigned swap = a[pivot][j];
                a[pivot][j] = a[col][j];
                a[col][j] = swap;
            }
            result = P - result;
        }
        result = (result * a[col][col]) % P;
        unsigned inv = inverse[a[col][col]];
        for (int row = col + 1; row < n; ++row) {
            if (!a[row][col]) continue;
            unsigned factor = (a[row][col] * inv) % P;
            for (int j = col + 1; j < n; ++j)
                a[row][j] = (a[row][j] + P - (factor * a[col][j]) % P) % P;
        }
    }
    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) return 1;
    int expected_n = atoi(argv[1]);
    inverse[1] = 1;
    for (unsigned i = 2; i < P; ++i)
        inverse[i] = P - ((P / i) * inverse[P % i]) % P;
    int counts[MAX_M + 1] = {0}, maxima[MAX_M + 1] = {0};
    char line[512];
    while (fgets(line, sizeof line, stdin)) {
        unsigned a[MAX_M][MAX_M] = {{0}};
        const char *s = line;
        int n = read_number(&s), pairs = read_number(&s), m = 0;
        if (n != expected_n || n < 2 || n > MAX_M || pairs < 1) return 2;
        for (int i = 0; i < pairs; ++i) {
            int u = read_number(&s), v = read_number(&s), mult = read_number(&s);
            if (u < 0 || v <= u || v >= n || mult < 1 || a[u][v]) return 3;
            m += mult;
            a[u][u] += mult;
            a[v][v] += mult;
            a[u][v] = a[v][u] = P - mult;
        }
        while (isspace((unsigned char)*s)) ++s;
        if (*s || m > MAX_M || m < n) return 4;
        int tau = (int)determinant(a, n - 1);
        if (tau <= 0 || tau > (1 << m)) return 5;
        ++counts[m];
        if (tau > maxima[m]) maxima[m] = tau;
    }
    if (ferror(stdin)) return 6;
    for (int m = 2; m <= MAX_M; ++m)
        if (counts[m]) printf("%d %d %d\n", m, counts[m], maxima[m]);
    return 0;
}

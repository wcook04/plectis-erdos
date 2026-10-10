// SPDX-FileCopyrightText: 2026 Will Cook
// SPDX-License-Identifier: Apache-2.0
//
// Support-independent carry resets for the target 1/2 at full order.
//
// For any digits with eps_1 = 0 the divisor channel satisfies
// 0 <= S_q <= d(q) - 2, so every representation of 1/2 has carries
// c_m <= floor(U(m)) with  U(m) = sum_{t>=0} (d(m+t) - 2) 2^{-(t+1)}.
//
// Part 1 lists every m in [2, N1] with U(m) < 1, certified exactly: the first
// T = 48 terms in integer arithmetic scaled by 2^T, plus the tail bound
//   sum_{t>=T} (d(m+t) - 2) 2^{-(t+1)} <= 2^{1-T} (sqrt(m+T) + 1),
// which follows from d(n) <= 2 sqrt(n).
//
// Part 2 lists every i in [2, N2] at which the cap recursion
//   g_{e+1} = 2,  g_i = floor((d(i) - 2 + g_{i+1})/2)
// vanishes for some right end e >= i.  By the floor identity
// floor((n + floor(x))/2) = floor((n + x)/2) this is the condition
//   min_{j>=0} [ sum_{t=0}^{j} (d(i+t) - 2) 2^{-(t+1)} + 2^{-j} ] < 1,
// evaluated exactly.  C = 2 is the smallest carry bound allowed in Hong's
// definition of a uniformly cap-certified depth, and larger C only raises g.
//
// Usage: full_series_cap_resets N1 N2
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define T 48

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s N1 N2\n", argv[0]); return 2; }
  long long N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  long long N = N1 > N2 ? N1 : N2;
  long long M = N + T + 2;
  uint16_t *d = calloc((size_t)M + 1, sizeof(uint16_t));
  if (!d) { fprintf(stderr, "allocation failed\n"); return 1; }
  for (long long k = 1; k <= M; ++k)
    for (long long m = k; m <= M; m += k) d[m]++;
  const unsigned long long ONE = 1ULL << T;

  long long count1 = 0;
  printf("part1 positions m<=%lld with U(m)<1:", N1);
  for (long long m = 2; m <= N1; ++m) {
    unsigned long long v = 0;
    int ok = 1;
    for (int t = 0; t < T; ++t) {
      v += (unsigned long long)(d[m + t] - 2) << (T - 1 - t);
      if (v >= ONE) { ok = 0; break; }
    }
    if (!ok) continue;
    unsigned long long tail = (unsigned long long)ceil(2.0 * (sqrt((double)(m + T)) + 1.0)) + 1;
    if (v + tail >= ONE) continue;
    printf(" %lld", m);
    count1++;
  }
  printf("\npart1 count=%lld\n", count1);

  long long count2 = 0;
  printf("part2 positions i<=%lld where the cap recursion with C=2 can vanish:", N2);
  for (long long i = 2; i <= N2; ++i) {
    unsigned long long partial = 0;
    for (int j = 0; j < T - 1; ++j) {
      partial += (unsigned long long)(d[i + j] - 2) << (T - 1 - j);
      if (partial >= ONE) break;
      if (partial + (2ULL << (T - 1 - j)) < ONE) { printf(" %lld", i); count2++; break; }
    }
  }
  printf("\npart2 count=%lld\n", count2);
  free(d);
  return 0;
}

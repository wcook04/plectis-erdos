// SPDX-FileCopyrightText: 2026 Will Cook
// SPDX-License-Identifier: Apache-2.0
//
// The C_2 pinning process for the target 1/2, written from the description in
// C. M. Hong, "On the rationality of reciprocal Mersenne subsums: carry
// pinning, quasi-polynomial certificates, and exact computation", Zenodo
// (2026), doi:10.5281/zenodo.23287959, Sections 3, 6 and 8.  The ancillary
// archive of that preprint was not used.
//
// Digits eps_n (eps_1 = 0), divisor channel S_m = sum_{j>=2, j|m} eps_{m/j},
// carry relation  eps_m + S_m + c_{m+1} = 1 + 2 c_m  (m >= 2), c_2 = 0.
// Carry bound Cb(k) = floor((d(k) - 2 + Cb(k+1))/2), started from 30000 above
// the computed range (valid because 0 <= S_q <= d(q) - 2).
// At depth k > M0 the process takes the least l for which the window
// [k+1, k+l] is pinned,
//   W = sum_{i<l} S_{k+1+i} 2^{l-1-i},   (W mod 2^l) + Cb(k+l+1) <= 2^l - 1,
// sets c_{k+1} = floor(W / 2^l) and eps_k = 1 - ((S_k + c_{k+1}) mod 2), and
// checks floor((S_k + c_{k+1})/2) = c_k.  It stops with STALL if no window
// inside [k+1, 2k-1] is pinned.
//
// Usage: hong_c2_process N PREFIX [checkpoint ...]
//   PREFIX is the string eps_1 eps_2 ... eps_M0 of the exact greedy prefix
//   (printed by exact_half_greedy.py); M0 is its length.
// Output: deterministic lines (no timings).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;

int main(int argc, char **argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: %s N PREFIX [checkpoint ...]\n", argv[0]);
    return 2;
  }
  long long N = atoll(argv[1]);
  const char *pref = argv[2];
  long long M0 = (long long)strlen(pref);
  if (N <= M0 || M0 < 2) { fprintf(stderr, "need 2 <= len(PREFIX) < N\n"); return 2; }
  long long TOP = 2 * N + 8;

  uint16_t *d = calloc(TOP + 2, 2);
  uint16_t *Cb = calloc(TOP + 2, 2);
  uint16_t *S = calloc(TOP + 2, 2);
  uint8_t *eps = calloc(N + 2, 1);
  if (!d || !Cb || !S || !eps) { fprintf(stderr, "allocation failed\n"); return 1; }
  for (long long k = 1; k <= TOP + 1; ++k)
    for (long long m = k; m <= TOP + 1; m += k) d[m]++;
  Cb[TOP + 1] = 30000;
  for (long long k = TOP; k >= 2; --k) Cb[k] = (uint16_t)((d[k] - 2 + Cb[k + 1]) / 2);

  for (long long n = 1; n <= M0; ++n) {
    char ch = pref[n - 1];
    if (ch != '0' && ch != '1') { fprintf(stderr, "PREFIX must be 0/1\n"); return 2; }
    eps[n] = (uint8_t)(ch - '0');
  }
  if (eps[1] != 0) { fprintf(stderr, "eps_1 must be 0\n"); return 2; }
  for (long long a = 2; a <= M0; ++a)
    if (eps[a]) for (long long m = 2 * a; m <= TOP; m += a) S[m]++;

  // forward carries through the prefix: c_{m+1} = 1 + 2 c_m - (eps_m + S_m)
  long long c = 0, maxc = 0;
  for (long long m = 2; m <= M0; ++m) {
    c = 1 + 2 * c - (eps[m] + S[m]);
    if (c < 0 || c > Cb[m + 1]) { printf("PREFIX CARRY OUT OF RANGE at m=%lld\n", m); return 4; }
    if (c > maxc) maxc = c;
  }

  long long nchk = argc - 3, ci = 0;
  long long hist[128] = {0};
  long long maxw = 0, maxw_at = -1, selected = 0;
  for (long long a = 1; a <= M0; ++a) selected += eps[a];
  for (long long k = M0 + 1; k <= N; ++k) {
    u128 W = 0;
    long long l, cnext = -1;
    for (l = 1; l <= k - 1 && l <= 100; ++l) {
      W = (W << 1) + S[k + l];
      u128 mask = (((u128)1) << l) - 1;
      if ((W & mask) + (u128)Cb[k + l + 1] <= mask) { cnext = (long long)(W >> l); break; }
    }
    if (cnext < 0 && l > 100) { printf("WINDOW LIMIT 100 reached at k=%lld\n", k); return 5; }
    if (cnext < 0) { printf("STALL at k=%lld\n", k); return 3; }
    if (l > maxw) { maxw = l; maxw_at = k; }
    hist[l]++;
    long long s = S[k] + cnext;
    if ((s >> 1) != c) { printf("RELATION FAILS at k=%lld\n", k); return 4; }
    eps[k] = (uint8_t)(1 - (s & 1));
    if (eps[k]) {
      selected++;
      for (long long m = 2 * k; m <= TOP; m += k) S[m]++;
    }
    c = cnext;
    if (c > maxc) maxc = c;
    while (ci < nchk && atoll(argv[3 + ci]) == k) {
      printf("checkpoint k=%lld selected=%lld largest_carry=%lld longest_window=%lld first_at=%lld\n",
             k, selected, maxc, maxw, maxw_at);
      ci++;
    }
  }
  long long half = 0;
  for (long long a = N / 2 + 1; a <= N; ++a) half += eps[a];
  printf("depth=%lld stall=none selected=%lld\n", N, selected);
  printf("selected_in_upper_half=%lld of %lld\n", half, N - N / 2);
  printf("largest_carry=%lld\n", maxc);
  printf("longest_window=%lld first_at_depth=%lld\n", maxw, maxw_at);
  for (int L = 2; L <= 34; L += 2) {
    long long t = 0;
    for (int j = L; j < 128; ++j) t += hist[j];
    printf("depths_with_window_at_least_%d=%lld\n", L, t);
  }
  long long run = 0, best1 = 0, end1 = 0, gap = 0, best0 = 0, end0 = 0;
  for (long long a = 2; a <= N; ++a) {
    if (eps[a]) { run++; gap = 0; if (run > best1) { best1 = run; end1 = a; } }
    else { gap++; run = 0; if (gap > best0) { best0 = gap; end0 = a; } }
  }
  printf("longest_run_of_elements=%lld from %lld to %lld\n", best1, end1 - best1 + 1, end1);
  printf("longest_gap=%lld from %lld to %lld\n", best0, end0 - best0 + 1, end0);
  uint64_t h = 1469598103934665603ULL;
  for (long long a = 1; a <= N; ++a) { h ^= eps[a]; h *= 1099511628211ULL; }
  printf("fnv1a64_of_digits_1_to_N=%016llx\n", (unsigned long long)h);
  return 0;
}

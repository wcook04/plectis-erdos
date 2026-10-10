// SPDX-FileCopyrightText: 2026 Will Cook
// SPDX-License-Identifier: Apache-2.0
//
// Pinning lengths ell_r of C. M. Hong, "On the rationality of reciprocal
// Mersenne subsums", Zenodo (2026), doi:10.5281/zenodo.23287959, Table 2,
// computed from the description in Section 3 of that preprint without its
// ancillary archive.
//
// Caps d_r(m) = #{2 <= j <= r : j | m}, period L_r = lcm(2..r), carry bound
// C_r = floor((r-1)/2).  For a right end e, run the recursion of Hong's
// Lemma 3.4 leftwards:  g_{e+1} = C_r,  g_i = floor((d_r(i) + g_{i+1})/2),
// and stop at the first i <= e with g_i = 0.  The longest C_r-saturated window
// ending at e is [i+1, e], of length e - i.  ell_r is the maximum over all
// right ends e modulo L_r.  We also count the right ends attaining the maximum
// and report the least such e in [0, L_r).
//
// Caps are produced block by block: a table of d_22 with period L_22 (or of d_r
// with period L_r when r <= 22) plus divisibility indicators for 23 <= j <= r,
// sieved over each block.  Every scan must stay inside the block's lookback
// margin, otherwise the program aborts.
//
// Usage: hong_pinning_lengths RMIN RMAX [threads]
// The result does not depend on the number of threads.
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BLOCK (1LL << 22)
#define MARGIN 8192

static int R;
static long long Lr, Lbase;
static int Cr;
static uint8_t *base;  // d_min(r,22) with period Lbase
static int nthreads;

typedef struct {
  long long blk_lo, blk_hi;  // block indices [lo, hi)
  long long best, nbest, first;
  long long hist[4096];
  int fail;
} Job;

static long long gcdll(long long a, long long b) { while (b) { long long t = a % b; a = b; b = t; } return a; }

static void *work(void *arg) {
  Job *jb = (Job *)arg;
  uint8_t *cap = malloc(BLOCK + MARGIN);
  jb->best = -1; jb->nbest = 0; jb->first = -1; jb->fail = 0;
  memset(jb->hist, 0, sizeof(jb->hist));
  for (long long b = jb->blk_lo; b < jb->blk_hi; ++b) {
    long long start = b * BLOCK;               // first right end in block
    long long end = start + BLOCK;             // exclusive
    if (end > Lr) end = Lr;
    long long lo = start - MARGIN;             // first position whose cap we need
    long long n = end - lo;
    // base caps (period Lbase), positions taken modulo Lr then modulo Lbase
    long long p = ((lo % Lr) + Lr) % Lr;
    long long q = p % Lbase;
    for (long long t = 0; t < n; ++t) {
      cap[t] = base[q];
      if (++q == Lbase) q = 0;
    }
    // extra divisors 23..R (only when R > 22); position lo+t is congruent to p+t mod Lr,
    // and every j <= R divides Lr, so divisibility of the true position is that of p+t.
    for (int j = 23; j <= R; ++j) {
      long long first = (j - (p % j)) % j;     // smallest t with j | p+t
      for (long long t = first; t < n; t += j) cap[t]++;
    }
    for (long long e = start; e < end; ++e) {
      long long idx = e - lo;
      int g = Cr;
      long long i = idx;
      for (;;) {
        g = (cap[i] + g) >> 1;
        if (g == 0) break;
        if (--i < 0) { jb->fail = 1; break; }
      }
      if (jb->fail) { free(cap); return NULL; }
      long long len = idx - i;                 // window [i+1, idx]
      if (len < 4096) jb->hist[len]++;
      if (len > jb->best) { jb->best = len; jb->nbest = 1; jb->first = e; }
      else if (len == jb->best) jb->nbest++;
    }
  }
  free(cap);
  return NULL;
}

static void run_one(int r) {
  R = r;
  Lr = 1;
  for (int j = 2; j <= R; ++j) Lr = Lr / gcdll(Lr, j) * j;
  Cr = (R - 1) / 2;
  int rb = R < 22 ? R : 22;
  Lbase = 1;
  for (int j = 2; j <= rb; ++j) Lbase = Lbase / gcdll(Lbase, j) * j;
  base = malloc(Lbase);
  memset(base, 0, Lbase);
  for (int j = 2; j <= rb; ++j)
    for (long long m = 0; m < Lbase; m += j) base[m]++;
  long long nblocks = (Lr + BLOCK - 1) / BLOCK;
  int nt = nthreads;
  if (nt > nblocks) nt = (int)nblocks;
  Job *jobs = calloc(nt, sizeof(Job));
  pthread_t *th = malloc(sizeof(pthread_t) * nt);
  for (int t = 0; t < nt; ++t) {
    jobs[t].blk_lo = nblocks * t / nt;
    jobs[t].blk_hi = nblocks * (t + 1) / nt;
    pthread_create(&th[t], NULL, work, &jobs[t]);
  }
  long long best = -1, nbest = 0, first = -1;
  long long hist[4096] = {0};
  int failed = 0;
  for (int t = 0; t < nt; ++t) {
    pthread_join(th[t], NULL);
    if (jobs[t].fail) failed = 1;
    for (int k = 0; k < 4096; ++k) hist[k] += jobs[t].hist[k];
    if (jobs[t].best > best) { best = jobs[t].best; nbest = jobs[t].nbest; first = jobs[t].first; }
    else if (jobs[t].best == best) {
      nbest += jobs[t].nbest;
      if (first < 0 || jobs[t].first < first) first = jobs[t].first;
    }
  }
  if (failed) { printf("r=%d scan left the lookback margin\n", R); exit(1); }
  long long total = 0;
  for (int k = 0; k < 4096; ++k) total += hist[k];
  uint64_t h = 1469598103934665603ULL;
  char buf[64];
  for (int k = 0; k < 4096; ++k) if (hist[k]) {
    int n = snprintf(buf, sizeof buf, "%d:%lld;", k, hist[k]);
    for (int c = 0; c < n; ++c) { h ^= (uint8_t)buf[c]; h *= 1099511628211ULL; }
  }
  printf("r=%d L_r=%lld C_r=%d ell_r=%lld maximizing_right_ends=%lld first_maximizing_right_end=%lld right_ends_scanned=%lld histogram_fnv1a64=%016llx\n",
         R, Lr, Cr, best, nbest, first, total, (unsigned long long)h);
  fflush(stdout);
  free(base); free(jobs); free(th);
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s RMIN RMAX [threads]\n", argv[0]); return 2; }
  int rmin = atoi(argv[1]), rmax = atoi(argv[2]);
  nthreads = argc > 3 ? atoi(argv[3]) : 8;
  if (rmin < 2 || rmax > 30 || rmin > rmax || nthreads < 1) { fprintf(stderr, "need 2 <= RMIN <= RMAX <= 30\n"); return 2; }
  for (int r = rmin; r <= rmax; ++r) run_one(r);
  return 0;
}

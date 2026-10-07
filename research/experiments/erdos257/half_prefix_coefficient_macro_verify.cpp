// SPDX-FileCopyrightText: 2026 Will Cook
// SPDX-License-Identifier: Apache-2.0
#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Clock = std::chrono::steady_clock;

static constexpr int P = 256;
static constexpr int EXTRA = 16;

struct Window {
  mpz_class lo;
  mpz_class strict_hi;
  long long integer_part;
};

static long long as_ll(const mpz_class &x) {
  return x.get_si();
}

static Window tail_window(const std::vector<uint16_t> &g, int m) {
  mpz_class a = 0;
  for (int j = 1; j <= P; ++j) {
    a += mpz_class(g[m + j]) << (P - j);
  }
  // For r=m+j, g(r) < r. Therefore the omitted scaled tail is strictly
  // below sum_{j>P} (m+j) 2^(P-j) = m+P+2.
  mpz_class hi = a + (m + P + 2);
  mpz_class q0 = a >> P;
  mpz_class q1 = (hi - 1) >> P;
  if (q0 != q1) throw std::runtime_error("tail floor not certified");
  return {a, hi, as_ll(q0)};
}

struct StepResult {
  std::vector<uint8_t> support;
  std::vector<uint16_t> g;
  int from;
  int to;
  int crossing_v;
  bool crossed;
  long long selected_count;
  long long vmin;
  long long vmax;
  double seconds;
};

static StepResult macro_step(const std::vector<uint8_t> &old, int n) {
  auto started = Clock::now();
  const int base = 2 * n;
  const int limit = base + EXTRA + P;
  std::vector<uint16_t> g(limit + 1, 0);
  for (int d = 1; d <= n; ++d) {
    if (!old[d]) continue;
    for (int r = 2 * d; r <= limit; r += d) {
      if (g[r] == std::numeric_limits<uint16_t>::max())
        throw std::runtime_error("coefficient overflow");
      ++g[r];
    }
  }

  Window wb = tail_window(g, base);
  mpz_class scale = mpz_class(1) << P;
  // The checked tail bound gives 2^(2n) eta_n <= 1/3 + (2/7) 2^(-n).
  // Since n>P, scaling by 2^P leaves an error <1/7, while the distance
  // from 2^P/3 to ceil(2^P/3) is at least 1/3.  Thus ceil(2^P/3) is a
  // strict scaled upper bound.
  mpz_class eta_hi = (scale + 2) / 3;
  mpz_class enclosure_hi = wb.strict_hi + eta_hi;
  mpz_class lo_cell = wb.lo >> P;
  mpz_class hi_cell = (enclosure_hi - 1) >> P;

  bool crossed = lo_cell != hi_cell;
  int crossing_v = -1;
  int natural = -1;

  if (crossed) {
    if (hi_cell != lo_cell + 1)
      throw std::runtime_error("enclosure crosses more than one base cell");
    long long carry = wb.integer_part;
    int trailing_ones = 0;
    bool still_trailing = true;
    for (int r = base; r >= 2; --r) {
      long long s = static_cast<long long>(g[r]) + carry;
      int bit = static_cast<int>(s & 1);
      carry = s >> 1;
      if (still_trailing) {
        if (bit == 1) ++trailing_ones;
        else still_trailing = false;
      }
    }
    if (carry != 0) throw std::runtime_error("nonzero reverse carry at root");
    crossing_v = trailing_ones;
    natural = base - trailing_ones - 1;
  } else {
    int last_common = 0;
    bool found_cross = false;
    for (int k = 1; k <= EXTRA; ++k) {
      mpz_class l = wb.lo << k;
      mpz_class h = enclosure_hi << k;
      if ((l >> P) == ((h - 1) >> P)) {
        last_common = k;
      } else {
        found_cross = true;
        break;
      }
    }
    if (!found_cross) throw std::runtime_error("EXTRA too small");
    natural = base + last_common;
  }

  Window wm = tail_window(g, natural);
  long long carry = wm.integer_part;
  std::vector<uint8_t> out(natural + 1, 0);
  out[1] = 0;
  for (int r = natural; r >= 2; --r) {
    long long s = static_cast<long long>(g[r]) + carry;
    int bit = static_cast<int>(s & 1);
    carry = s >> 1;
    out[r] = static_cast<uint8_t>(1 - bit);
  }
  if (carry != 0) throw std::runtime_error("nonzero output reverse carry at root");
  for (int r = 1; r <= n; ++r) {
    if (out[r] != old[r])
      throw std::runtime_error("generated prefix mismatch at " + std::to_string(r));
  }

  long long selected = 0;
  for (int r = 1; r <= natural; ++r) selected += out[r];

  // When natural <= 2n+1, every proper divisor of r<=natural is <=n, so
  // this g is also the full proper-divisor coefficient of the new support.
  long long v = 1, vmin = 1, vmax = 1;
  for (int r = 2; r <= natural; ++r) {
    long long f = static_cast<long long>(g[r]) + out[r];
    v = 2 * v - f;
    vmin = std::min(vmin, v);
    vmax = std::max(vmax, v);
  }

  double secs = std::chrono::duration<double>(Clock::now() - started).count();
  return {std::move(out), std::move(g), n, natural, crossing_v, crossed,
          selected, vmin, vmax, secs};
}

static std::vector<uint8_t> extend_to(const std::vector<uint8_t> &old, int n,
                                      int m) {
  std::vector<uint16_t> g(m + P + 1, 0);
  for (int d = 1; d <= n; ++d) {
    if (!old[d]) continue;
    for (int r = 2 * d; r <= m + P; r += d) ++g[r];
  }
  Window w = tail_window(g, m);
  long long carry = w.integer_part;
  std::vector<uint8_t> out(m + 1, 0);
  out[1] = 0;
  for (int r = m; r >= 2; --r) {
    long long s = static_cast<long long>(g[r]) + carry;
    out[r] = static_cast<uint8_t>(1 - (s & 1));
    carry = s >> 1;
  }
  if (carry != 0) throw std::runtime_error("fixed-step root carry");
  for (int r = 1; r <= n; ++r)
    if (out[r] != old[r]) throw std::runtime_error("fixed-step prefix mismatch");
  return out;
}

int main(int argc, char **argv) {
  int n;
  std::vector<uint8_t> support;
  if (argc == 2) {
    std::ifstream in(argv[1], std::ios::binary);
    if (!in) throw std::runtime_error("cannot open support bytes");
    std::vector<uint8_t> raw((std::istreambuf_iterator<char>(in)), {});
    n = static_cast<int>(raw.size());
    support.assign(n + 1, 0);
    for (int i = 1; i <= n; ++i) support[i] = raw[i - 1];
  } else {
    const int targets[] = {3, 6, 12, 25, 51, 103, 207, 414, 827,
                           1654, 3308, 6615, 13230, 26461, 52922,
                           105845, 211690, 423377};
    n = 1;
    support.assign(2, 0);
    for (int m : targets) {
      support = extend_to(support, n, m);
      n = m;
    }
    std::ofstream seed("/tmp/coefficient_support_423377.bin", std::ios::binary);
    seed.write(reinterpret_cast<const char *>(support.data() + 1), n);
    std::ofstream seed_csv("/tmp/coefficient_selected_423377.csv", std::ios::binary);
    bool first_seed = true;
    for (int i = 1; i <= n; ++i) if (support[i]) {
      if (!first_seed) seed_csv << ',';
      first_seed = false;
      seed_csv << i;
    }
    std::cout << "reconstructed_seed_depth=" << n << "\n";
  }

  std::vector<uint16_t> last_g;
  int steps = 5;
  if (const char *s = std::getenv("STEPS")) steps = std::stoi(s);
  for (int step = 0; step < steps; ++step) {
    StepResult r = macro_step(support, n);
    std::cout << "row " << (step + 1)
              << " from=" << r.from << " to=" << r.to
              << " defect=" << (2 * r.from - r.to)
              << " crossed=" << (r.crossed ? "true" : "false")
              << " crossing_v=" << (r.crossed ? std::to_string(r.crossing_v) : "none")
              << " selected=" << r.selected_count
              << " Vrange=[" << r.vmin << "," << r.vmax << "]"
              << " seconds=" << r.seconds << "\n";
    support = std::move(r.support);
    last_g = std::move(r.g);
    n = r.to;
  }

  std::ofstream bits("/tmp/coefficient_support_final.bin", std::ios::binary);
  bits.write(reinterpret_cast<const char *>(support.data() + 1), n);
  std::ofstream csv("/tmp/coefficient_selected_final.csv", std::ios::binary);
  bool first = true;
  long long count = 0;
  for (int i = 1; i <= n; ++i) {
    if (!support[i]) continue;
    if (!first) csv << ',';
    first = false;
    csv << i;
    ++count;
  }
  std::cout << "final_depth=" << n << " selected=" << count << "\n";
}


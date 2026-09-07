// Corpus navigation metadata: problem_id = "erdos_68".
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

namespace {

struct Row {
  std::uint64_t q = 0;
  std::int64_t first_support = -1;
  std::int64_t first_square = -1;
  std::int64_t first_cube = -1;
  std::uint64_t support_count = 0;
  std::uint64_t square_count = 0;
  std::uint64_t cube_count = 0;
};

std::uint64_t parse_positive(const char* raw, const char* name) {
  const std::string value(raw);
  std::size_t consumed = 0;
  const auto parsed = std::stoull(value, &consumed);
  if (consumed != value.size() || parsed < 2) {
    throw std::invalid_argument(std::string(name) +
                                " must be an integer at least 2");
  }
  return parsed;
}

std::vector<std::uint64_t> primes_through(std::uint64_t bound) {
  std::vector<bool> sieve(bound + 1, true);
  sieve[0] = false;
  sieve[1] = false;
  for (std::uint64_t q = 2; q * q <= bound; ++q) {
    if (!sieve[q]) {
      continue;
    }
    for (std::uint64_t multiple = q * q; multiple <= bound;
         multiple += q) {
      sieve[multiple] = false;
    }
  }
  std::vector<std::uint64_t> primes;
  for (std::uint64_t q = 2; q <= bound; ++q) {
    if (sieve[q]) {
      primes.push_back(q);
    }
  }
  return primes;
}

std::uint64_t mul_mod(std::uint64_t left, std::uint64_t right,
                      std::uint64_t modulus) {
  return static_cast<std::uint64_t>(
      (static_cast<unsigned __int128>(left) * right) % modulus);
}

bool factorial_is_one_mod_cube(std::uint64_t q, std::uint64_t index) {
  const unsigned __int128 cube =
      static_cast<unsigned __int128>(q) * q * q;
  unsigned __int128 residue = 1;
  for (std::uint64_t factor = 2; factor <= index; ++factor) {
    residue = (residue * factor) % cube;
  }
  return residue == 1;
}

Row scan_prime(std::uint64_t q) {
  Row row;
  row.q = q;
  const std::uint64_t modulus = q * q;
  std::uint64_t residue = 1;
  for (std::uint64_t index = 2; index < q; ++index) {
    residue = mul_mod(residue, index, modulus);
    if (residue % q != 1) {
      continue;
    }
    ++row.support_count;
    if (row.first_support < 0) {
      row.first_support = static_cast<std::int64_t>(index);
    }
    if (residue != 1) {
      continue;
    }
    ++row.square_count;
    if (row.first_square < 0) {
      row.first_square = static_cast<std::int64_t>(index);
    }
    if (factorial_is_one_mod_cube(q, index)) {
      ++row.cube_count;
      if (row.first_cube < 0) {
        row.first_cube = static_cast<std::int64_t>(index);
      }
    }
  }
  return row;
}

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc != 4) {
      std::cerr << "usage: check_erdos68_arbitrary_valuation_records_fast "
                   "<min-prime> <max-prime> <threads>\n";
      return 2;
    }
    const std::uint64_t min_prime =
        parse_positive(argv[1], "min_prime");
    const std::uint64_t max_prime =
        parse_positive(argv[2], "max_prime");
    if (min_prime > max_prime) {
      throw std::invalid_argument("min_prime must not exceed max_prime");
    }
    if (max_prime > 2'000'000'000ULL) {
      throw std::invalid_argument(
          "max_prime must not exceed 2000000000");
    }
    const std::uint64_t requested_threads =
        parse_positive(argv[3], "threads");
    auto primes = primes_through(max_prime);
    primes.erase(
        primes.begin(),
        std::lower_bound(primes.begin(), primes.end(), min_prime));
    std::vector<Row> rows(primes.size());
    std::atomic<std::size_t> next{0};
    const auto worker = [&]() {
      while (true) {
        const std::size_t position = next.fetch_add(1);
        if (position >= primes.size()) {
          return;
        }
        rows[position] = scan_prime(primes[position]);
      }
    };
    const std::size_t thread_count = std::min<std::size_t>(
        requested_threads, std::max<std::size_t>(1, primes.size()));
    std::vector<std::thread> threads;
    threads.reserve(thread_count);
    for (std::size_t index = 0; index < thread_count; ++index) {
      threads.emplace_back(worker);
    }
    for (auto& thread : threads) {
      thread.join();
    }
    std::cout << "V\t1\n";
    for (const auto& row : rows) {
      std::cout << "P\t" << row.q << '\t' << row.first_support << '\t'
                << row.first_square << '\t' << row.first_cube << '\t'
                << row.support_count << '\t' << row.square_count << '\t'
                << row.cube_count << '\n';
    }
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}

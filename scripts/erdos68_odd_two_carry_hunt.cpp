// Corpus navigation metadata: problem_id = "erdos_68".
//
// Sparse exact hunter for the sufficient odd two-carry condition proved in
// ErdosProblems/Erdos68/PrimeThresholdParity.lean.  This is deliberately a
// separate executable from check_erdos68_strict_successor_gmp.cpp: it omits
// the enormous strict-successor accumulator and dense per-index output, and
// exits as soon as it finds a counterexample.
#include <gmpxx.h>

#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>

namespace {

mpz_class ceil_div(const mpz_class& numerator, const mpz_class& denominator) {
  mpz_class quotient;
  mpz_cdiv_q(quotient.get_mpz_t(), numerator.get_mpz_t(),
             denominator.get_mpz_t());
  return quotient;
}

unsigned long parse_index(const char* raw, const char* name,
                          unsigned long minimum) {
  const std::string value(raw);
  std::size_t consumed = 0;
  const unsigned long parsed = std::stoul(value, &consumed);
  if (consumed != value.size() || parsed < minimum) {
    throw std::invalid_argument(std::string(name) + " must be an integer at least " +
                                std::to_string(minimum));
  }
  return parsed;
}

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc != 4) {
      std::cerr << "usage: erdos68_odd_two_carry_hunt "
                   "<max-index> <guard-bits> <first-odd-index>\n";
      return 2;
    }

    const unsigned long max_index = parse_index(argv[1], "max_index", 3);
    const unsigned long guard_bits = parse_index(argv[2], "guard_bits", 1);
    const unsigned long first_odd = parse_index(argv[3], "first_odd_index", 3);
    if ((first_odd & 1UL) == 0) {
      throw std::invalid_argument("first_odd_index must be odd");
    }
    if (max_index <= first_odd) {
      throw std::invalid_argument(
          "max_index must exceed first_odd_index so its successor is checked");
    }

    mpz_class factorial = 1;
    for (unsigned long m = 2; m <= max_index; ++m) {
      factorial *= m;
    }
    const mp_bitcnt_t precision_bits =
        mpz_sizeinbase(factorial.get_mpz_t(), 2) + guard_bits;

    mpz_class scale = 1;
    mpz_mul_2exp(scale.get_mpz_t(), scale.get_mpz_t(), precision_bits);

    // Delta_2 = 1.  The interval is propagated exactly as in the dense GMP
    // certificate; each reciprocal is enclosed by adjacent scale-grid points.
    mpz_class lower = scale;
    mpz_class upper = scale;
    factorial = 2;
    mpz_class factorial_quotient = scale / factorial;
    mpz_class factorial_remainder = scale % factorial;

    unsigned long pending_odd_unit = 0;
    unsigned long odd_unit_count = 0;
    unsigned long minimum_odd_carry = max_index;

    std::cout << "V\t" << gmp_version << '\n';
    std::cout << "P\t" << precision_bits << '\n';

    for (unsigned long m = 3; m <= max_index; ++m) {
      const mpz_class previous_factorial = factorial;
      factorial *= m;
      const mpz_class denominator = factorial - 1;

      const mpz_class radix_remainder = factorial_quotient % m;
      factorial_quotient /= m;
      factorial_remainder += radix_remainder * previous_factorial;
      if (!(0 <= factorial_remainder && factorial_remainder < factorial)) {
        throw std::runtime_error("invalid factorial quotient remainder at m=" +
                                 std::to_string(m));
      }
      const mpz_class reciprocal_floor =
          factorial_quotient +
          (factorial_quotient + factorial_remainder) / denominator;

      const mpz_class raw_lower = m * lower - reciprocal_floor - 1;
      const mpz_class raw_upper = m * upper - reciprocal_floor;
      const mpz_class carry = ceil_div(raw_upper, scale) - 1;
      const mpz_class cell_lower = carry * scale;
      const mpz_class cell_upper = (carry + 1) * scale;

      if (!(raw_lower > cell_lower && raw_upper <= cell_upper)) {
        throw std::runtime_error("interval crosses a carry boundary at m=" +
                                 std::to_string(m));
      }
      lower = raw_lower - cell_lower;
      upper = raw_upper - cell_lower;
      if (!(0 < lower && lower <= upper && upper <= scale)) {
        throw std::runtime_error("invalid normalized interval at m=" +
                                 std::to_string(m));
      }
      if (!mpz_fits_ulong_p(carry.get_mpz_t())) {
        throw std::runtime_error("carry does not fit an unsigned long at m=" +
                                 std::to_string(m));
      }
      const unsigned long carry_value = carry.get_ui();

      if (pending_odd_unit != 0) {
        if (m != pending_odd_unit + 1) {
          throw std::runtime_error("internal pending-index mismatch");
        }
        if (carry_value < 3) {
          std::cout << "X\tunit_successor\t" << pending_odd_unit << '\t'
                    << carry_value << '\n';
          return 3;
        }
        std::cout << "U\t" << pending_odd_unit << '\t' << carry_value << '\n';
        pending_odd_unit = 0;
      }

      if (m >= first_odd && (m & 1UL) == 1) {
        if (carry_value < minimum_odd_carry) {
          minimum_odd_carry = carry_value;
        }
        if (carry_value == 0) {
          std::cout << "X\tzero_carry\t" << m << "\t0\n";
          return 3;
        }
        if (carry_value == 1) {
          pending_odd_unit = m;
          ++odd_unit_count;
        }
      }
    }

    if (pending_odd_unit != 0) {
      throw std::runtime_error(
          "horizon ended before the successor of a pending odd unit carry");
    }
    std::cout << "OK\t" << first_odd << '\t' << max_index << '\t'
              << odd_unit_count << '\t' << minimum_odd_carry << '\n';
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}

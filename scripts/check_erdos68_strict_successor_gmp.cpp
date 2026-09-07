// Corpus navigation metadata: problem_id = "erdos_68".
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

unsigned long parse_positive_index(const char* raw) {
  const std::string value(raw);
  std::size_t consumed = 0;
  const unsigned long parsed = std::stoul(value, &consumed);
  if (consumed != value.size() || parsed < 3) {
    throw std::invalid_argument("max_index must be an integer at least 3");
  }
  return parsed;
}

unsigned long parse_positive_guard(const char* raw) {
  const std::string value(raw);
  std::size_t consumed = 0;
  const unsigned long parsed = std::stoul(value, &consumed);
  if (consumed != value.size() || parsed < 1) {
    throw std::invalid_argument("guard_bits must be a positive integer");
  }
  return parsed;
}

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc != 3) {
      std::cerr << "usage: check_erdos68_strict_successor_gmp "
                   "<max-index> <guard-bits>\n";
      return 2;
    }

    const unsigned long max_index = parse_positive_index(argv[1]);
    const unsigned long guard_bits = parse_positive_guard(argv[2]);

    mpz_class factorial = 1;
    for (unsigned long m = 2; m <= max_index; ++m) {
      factorial *= m;
    }
    const mp_bitcnt_t precision_bits =
        mpz_sizeinbase(factorial.get_mpz_t(), 2) + guard_bits;

    mpz_class scale = 1;
    mpz_mul_2exp(scale.get_mpz_t(), scale.get_mpz_t(), precision_bits);

    // Delta_2 = 1 and N_2 = floor(2!/(2!-1)) + 1 = 3.
    mpz_class lower = scale;
    mpz_class upper = scale;
    mpz_class strict_successor = 3;
    factorial = 2;
    mpz_class factorial_quotient = scale / factorial;
    mpz_class factorial_remainder = scale % factorial;

    std::cout << "V\t" << gmp_version << '\n';
    std::cout << "P\t" << precision_bits << '\n';

    for (unsigned long m = 3; m <= max_index; ++m) {
      const mpz_class previous_factorial = factorial;
      factorial *= m;
      const mpz_class denominator = factorial - 1;

      // If B=q_(m-1)(m-1)!+r_(m-1), divide q_(m-1) only by
      // the machine-sized radix m:
      //
      //   q_(m-1) = m q_m + s_m,
      //   r_m = r_(m-1) + s_m (m-1)!.
      //
      // Then B=q_m m!+r_m and
      //
      //   floor(B/(m!-1)) = q_m + floor((q_m+r_m)/(m!-1)).
      //
      // This exact identity avoids a fresh scale-by-factorial division.
      const mpz_class radix_remainder = factorial_quotient % m;
      factorial_quotient /= m;
      factorial_remainder += radix_remainder * previous_factorial;
      if (!(0 <= factorial_remainder && factorial_remainder < factorial)) {
        throw std::runtime_error(
            "invalid factorial quotient remainder at m=" +
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

      if (!(raw_lower > cell_lower)) {
        throw std::runtime_error(
            "lower interval crosses a carry boundary at m=" +
            std::to_string(m));
      }
      if (!(raw_upper <= cell_upper)) {
        throw std::runtime_error(
            "upper interval crosses a carry boundary at m=" +
            std::to_string(m));
      }

      lower = raw_lower - cell_lower;
      upper = raw_upper - cell_lower;
      if (!(0 < lower && lower <= upper && upper <= scale)) {
        throw std::runtime_error("invalid normalized interval at m=" +
                                 std::to_string(m));
      }

      strict_successor = m * strict_successor + 1 - carry;
      if (!mpz_fits_slong_p(carry.get_mpz_t())) {
        throw std::runtime_error("carry does not fit a signed long at m=" +
                                 std::to_string(m));
      }
      std::cout << "E\t" << m << '\t' << carry.get_si() << '\n';
    }

    std::cout << "L\t" << lower.get_str(16) << '\n';
    std::cout << "U\t" << upper.get_str(16) << '\n';
    std::cout << "N\t" << strict_successor.get_str(16) << '\n';
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}

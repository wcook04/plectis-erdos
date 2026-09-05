"""Exact helpers for binary affine-word and endpoint-shadowing experiments."""

from __future__ import annotations

from collections.abc import Iterable


def binary_word_block(digits: Iterable[int]) -> int:
    """Return the exact block obtained by repeatedly applying ``B <- 2B+d``."""

    block = 0
    for digit in digits:
        block = 2 * block + int(digit)
    return block


def fixed_quotient_errors(digits: Iterable[int], quotient: int) -> list[int]:
    """Return ``E_H=B_H-k(2^H-1)`` after every supplied letter."""

    errors: list[int] = []
    error = 0
    for digit in digits:
        error = 2 * error + int(digit) - quotient
        errors.append(error)
    return errors


def constant_boundary_mode(letter: int, depth: int) -> dict[str, object]:
    """Certify the constant-letter fixed-quotient boundary mode exactly."""

    if letter <= 0 or depth < 0:
        raise ValueError("letter must be positive and depth nonnegative")
    digits = [letter] * depth
    block = binary_word_block(digits)
    modulus = (1 << depth) - 1
    errors = fixed_quotient_errors(digits, letter)
    if block != letter * modulus or any(errors):
        raise AssertionError("constant boundary identity failed")
    return {
        "letter": letter,
        "depth": depth,
        "block": block,
        "mersenne_modulus": modulus,
        "fixed_quotient": letter,
        "all_endpoint_errors_zero": True,
    }

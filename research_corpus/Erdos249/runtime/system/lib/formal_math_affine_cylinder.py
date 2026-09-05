"""Exact helpers for affine-cylinder experiments in formal mathematics.

The module deliberately knows nothing about a particular problem.  It turns
constraints of the form

    0 < modulus * z - forcing <= upper

into an exact rational interval and searches that interval for a rational
whose denominator lies in a required band.  It also intersects closed integer
bands ``lower <= scale*seed+offset <= upper`` exactly, so a recurrence probe can
decide its complete initial-seed cone without seed enumeration.  These are the
reusable cores behind experiments where a modular recurrence becomes affine.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd
from typing import Iterable, Sequence


@dataclass(frozen=True)
class AffineCylinderConstraint:
    """One exact constraint ``0 < modulus*z-forcing <= upper``."""

    modulus: int
    forcing: int
    upper: Fraction
    label: str = ""

    def __post_init__(self) -> None:
        if self.modulus <= 0:
            raise ValueError("modulus must be positive")
        if self.upper < 0:
            raise ValueError("upper must be nonnegative")

    @property
    def lower_endpoint(self) -> Fraction:
        return Fraction(self.forcing, self.modulus)

    @property
    def upper_endpoint(self) -> Fraction:
        return Fraction(self.forcing, self.modulus) + self.upper / self.modulus


@dataclass(frozen=True)
class AffineCylinderInterval:
    """Intersection with an open lower and closed upper endpoint."""

    lower: Fraction
    upper: Fraction
    active_lower_label: str
    active_upper_label: str

    @property
    def nonempty(self) -> bool:
        return self.lower < self.upper

    @property
    def width(self) -> Fraction:
        return max(Fraction(0), self.upper - self.lower)

    def contains(self, value: Fraction) -> bool:
        return self.lower < value <= self.upper


@dataclass(frozen=True)
class RationalBandWitness:
    """A possibly non-reduced numerator/denominator inside a cylinder."""

    numerator: int
    denominator: int
    reduced_value: Fraction
    target_numerator: int
    target_denominator: int
    denominator_cap: int


@dataclass(frozen=True)
class AffineCylinderNestingCertificate:
    """Exact certificate that every constraint contains its successor."""

    constraint_count: int
    nested: bool
    first_failure_index: int | None

    @property
    def collapses_to_final_constraint(self) -> bool:
        return self.nested and self.constraint_count > 0


@dataclass(frozen=True)
class ExactRationalBandCertificate:
    """Complete rational-point count and first witness in a denominator band."""

    count: int
    first_witness: Fraction | None
    first_denominator: int | None


@dataclass(frozen=True)
class IntegerAffineConstraint:
    """Closed integer constraint ``lower <= scale*seed+offset <= upper``."""

    scale: int
    offset: int
    lower: int
    upper: int
    label: str = ""

    def __post_init__(self) -> None:
        if self.scale <= 0:
            raise ValueError("scale must be positive")
        if self.lower > self.upper:
            raise ValueError("lower must not exceed upper")

    @property
    def seed_lower(self) -> int:
        return -((-(self.lower - self.offset)) // self.scale)

    @property
    def seed_upper(self) -> int:
        return (self.upper - self.offset) // self.scale


@dataclass(frozen=True)
class IntegerPreimageInterval:
    """Exact closed integer intersection pulled back to the initial seed."""

    lower: int
    upper: int
    active_lower_label: str
    active_upper_label: str

    @property
    def nonempty(self) -> bool:
        return self.lower <= self.upper

    @property
    def count(self) -> int:
        return max(0, self.upper - self.lower + 1)

    def contains(self, value: int) -> bool:
        return self.lower <= value <= self.upper


@dataclass(frozen=True)
class IntegerPreimageMembershipCertificate:
    """Exact membership check for one seed and a complete affine preimage.

    The certificate records both sides of the equivalence

    ``seed belongs to the intersected preimage``
    ``iff every original affine band contains its trajectory value``.

    This is useful as a proof boundary in finite recurrence experiments: once
    an observed trajectory satisfies every band in a finite prefix, its own
    seed is an explicit survivor, so that prefix's complete cone cannot be
    empty.
    """

    seed: int
    constraint_count: int
    satisfies_every_band: bool
    interval_contains_seed: bool
    first_failed_constraint_index: int | None
    first_failed_constraint_label: str | None

    @property
    def equivalence_verified(self) -> bool:
        return self.satisfies_every_band == self.interval_contains_seed

    @property
    def proves_nonempty(self) -> bool:
        return self.satisfies_every_band and self.interval_contains_seed


def intersect_affine_cylinder(
    constraints: Sequence[AffineCylinderConstraint],
) -> AffineCylinderInterval:
    """Intersect a nonempty sequence of exact affine constraints."""

    if not constraints:
        raise ValueError("at least one constraint is required")
    lower_row = max(constraints, key=lambda row: row.lower_endpoint)
    upper_row = min(constraints, key=lambda row: row.upper_endpoint)
    return AffineCylinderInterval(
        lower=lower_row.lower_endpoint,
        upper=upper_row.upper_endpoint,
        active_lower_label=lower_row.label,
        active_upper_label=upper_row.label,
    )


def intersect_integer_affine_preimages(
    constraints: Sequence[IntegerAffineConstraint],
) -> IntegerPreimageInterval:
    """Intersect exact affine bands as a complete interval of integer seeds.

    This is the integer analogue of :func:`intersect_affine_cylinder`.  It is
    useful for recurrences whose state at each time is ``scale*seed+offset``:
    the result decides the entire initial-seed cone without enumerating seeds.
    """

    if not constraints:
        raise ValueError("at least one constraint is required")
    lower_row = max(constraints, key=lambda row: row.seed_lower)
    upper_row = min(constraints, key=lambda row: row.seed_upper)
    return IntegerPreimageInterval(
        lower=lower_row.seed_lower,
        upper=upper_row.seed_upper,
        active_lower_label=lower_row.label,
        active_upper_label=upper_row.label,
    )


def certify_integer_seed_in_affine_preimages(
    constraints: Sequence[IntegerAffineConstraint], seed: int
) -> IntegerPreimageMembershipCertificate:
    """Certify seed membership by checking both equivalent exact forms.

    The intersection routine computes the complete integer preimage of all
    supplied bands.  Evaluating the bands directly provides an independent,
    source-level witness check and identifies the first failed constraint.
    """

    interval = intersect_integer_affine_preimages(constraints)
    first_failed_index: int | None = None
    for index, row in enumerate(constraints):
        value = row.scale * seed + row.offset
        if not row.lower <= value <= row.upper:
            first_failed_index = index
            break
    satisfies_every_band = first_failed_index is None
    interval_contains_seed = interval.contains(seed)
    if satisfies_every_band != interval_contains_seed:
        raise AssertionError("integer affine preimage membership mismatch")
    return IntegerPreimageMembershipCertificate(
        seed=seed,
        constraint_count=len(constraints),
        satisfies_every_band=satisfies_every_band,
        interval_contains_seed=interval_contains_seed,
        first_failed_constraint_index=first_failed_index,
        first_failed_constraint_label=(
            None
            if first_failed_index is None
            else constraints[first_failed_index].label
        ),
    )


def certify_affine_cylinder_nesting(
    constraints: Sequence[AffineCylinderConstraint],
) -> AffineCylinderNestingCertificate:
    """Check exact consecutive containment of open-lower/closed-upper intervals.

    When this certificate succeeds, the intersection of the full constraint
    sequence is exactly its final constraint.  This separates a dynamical
    nesting question from the remaining Diophantine rational-point question.
    """

    if not constraints:
        raise ValueError("at least one constraint is required")
    for index, (previous, current) in enumerate(zip(constraints, constraints[1:])):
        if not (
            previous.lower_endpoint <= current.lower_endpoint
            and current.upper_endpoint <= previous.upper_endpoint
        ):
            return AffineCylinderNestingCertificate(
                constraint_count=len(constraints),
                nested=False,
                first_failure_index=index,
            )
    return AffineCylinderNestingCertificate(
        constraint_count=len(constraints),
        nested=True,
        first_failure_index=None,
    )


def _scaled_denominator_in_band(
    reduced_denominator: int,
    minimum_denominator: int,
    maximum_denominator: int,
    coprime_to: int,
) -> int | None:
    scale_min = max(1, (minimum_denominator + reduced_denominator - 1) // reduced_denominator)
    scale_max = maximum_denominator // reduced_denominator
    for scale in range(scale_min, min(scale_max, scale_min + 512) + 1):
        denominator = scale * reduced_denominator
        if gcd(denominator, coprime_to) == 1:
            return denominator
    return None


def _floor_sum(n: int, modulus: int, multiplier: int, offset: int) -> int:
    """Return ``sum(floor((multiplier*i+offset)/modulus), i=0..n-1)``."""

    if n < 0 or modulus <= 0 or multiplier < 0 or offset < 0:
        raise ValueError("floor-sum inputs must be nonnegative with positive modulus")
    answer = 0
    while True:
        if multiplier >= modulus:
            answer += (n - 1) * n * (multiplier // modulus) // 2
            multiplier %= modulus
        if offset >= modulus:
            answer += n * (offset // modulus)
            offset %= modulus
        total = multiplier * n + offset
        if total < modulus:
            return answer
        n = total // modulus
        offset = total % modulus
        modulus, multiplier = multiplier, modulus


def _sum_floor_multiples(value: Fraction, maximum_denominator: int, step: int) -> int:
    """Sum ``floor(B*value)`` for positive ``B <= maximum`` divisible by step."""

    count = maximum_denominator // step
    if count == 0:
        return 0
    numerator = step * value.numerator
    quotient, remainder = divmod(numerator, value.denominator)
    linear_part = quotient * count * (count + 1) // 2
    return linear_part + _floor_sum(
        count, value.denominator, remainder, remainder
    )


def _squarefree_divisor_signs(value: int) -> list[tuple[int, int]]:
    """Inclusion-exclusion divisors and Möbius signs for coprimality."""

    if value <= 0:
        raise ValueError("coprime_to must be positive")
    primes: list[int] = []
    remainder = value
    candidate = 2
    while candidate * candidate <= remainder:
        if remainder % candidate == 0:
            primes.append(candidate)
            while remainder % candidate == 0:
                remainder //= candidate
        candidate += 1
    if remainder > 1:
        primes.append(remainder)
    rows = [(1, 1)]
    for prime in primes:
        rows += [(divisor * prime, -sign) for divisor, sign in rows]
    return rows


def _cumulative_rational_count(
    interval: AffineCylinderInterval,
    maximum_denominator: int,
    coprime_to: int,
) -> int:
    if maximum_denominator <= 0 or not interval.nonempty:
        return 0
    answer = 0
    for step, sign in _squarefree_divisor_signs(coprime_to):
        upper = _sum_floor_multiples(interval.upper, maximum_denominator, step)
        lower = _sum_floor_multiples(interval.lower, maximum_denominator, step)
        answer += sign * (upper - lower)
    return answer


def certify_rationals_in_denominator_band(
    interval: AffineCylinderInterval,
    minimum_denominator: int,
    maximum_denominator: int,
    *,
    coprime_to: int = 1,
) -> ExactRationalBandCertificate:
    """Completely count admissible rationals and recover the least denominator.

    This is a decision procedure, unlike the continued-fraction witness
    heuristic below. It sums ``floor(B*upper)-floor(B*lower)`` by exact
    floor-sum reciprocity and inclusion-exclusion. Runtime is logarithmic in
    the potentially enormous denominator endpoints.
    """

    if minimum_denominator <= 0 or maximum_denominator < minimum_denominator:
        raise ValueError("invalid denominator band")
    if coprime_to <= 0:
        raise ValueError("coprime_to must be positive")
    before = _cumulative_rational_count(interval, minimum_denominator - 1, coprime_to)
    through = _cumulative_rational_count(interval, maximum_denominator, coprime_to)
    count = through - before
    if count == 0:
        return ExactRationalBandCertificate(0, None, None)
    low, high = minimum_denominator, maximum_denominator
    while low < high:
        middle = (low + high) // 2
        if _cumulative_rational_count(interval, middle, coprime_to) > before:
            high = middle
        else:
            low = middle + 1
    denominator = low
    numerator = denominator * interval.lower.numerator // interval.lower.denominator + 1
    witness = Fraction(numerator, denominator)
    if gcd(denominator, coprime_to) != 1 or not interval.contains(witness):
        raise AssertionError("floor-sum witness reconstruction failed")
    return ExactRationalBandCertificate(count, witness, denominator)


def count_rationals_in_denominator_band(
    interval: AffineCylinderInterval,
    minimum_denominator: int,
    maximum_denominator: int,
    *,
    coprime_to: int = 1,
) -> int:
    """Completely count admissible rationals without reconstructing a witness."""

    if minimum_denominator <= 0 or maximum_denominator < minimum_denominator:
        raise ValueError("invalid denominator band")
    if coprime_to <= 0:
        raise ValueError("coprime_to must be positive")
    return _cumulative_rational_count(
        interval, maximum_denominator, coprime_to
    ) - _cumulative_rational_count(
        interval, minimum_denominator - 1, coprime_to
    )


def find_rational_in_denominator_band(
    interval: AffineCylinderInterval,
    minimum_denominator: int,
    maximum_denominator: int,
    *,
    coprime_to: int = 1,
    subdivisions: int = 64,
    cap_ratios: Iterable[tuple[int, int]] = (
        (1, 1),
        (31, 32),
        (15, 16),
        (7, 8),
        (3, 4),
        (1, 2),
        (1, 4),
    ),
) -> RationalBandWitness | None:
    """Find a deterministic exact rational witness in a denominator band.

    ``Fraction.limit_denominator`` supplies continued-fraction candidates at
    several interior targets and caps.  A reduced candidate may be scaled when
    doing so preserves the requested coprimality.  The search is intentionally
    a witness constructor, not a completeness claim about the interval.
    """

    if not interval.nonempty:
        return None
    if minimum_denominator <= 0 or maximum_denominator < minimum_denominator:
        raise ValueError("invalid denominator band")
    if coprime_to <= 0:
        raise ValueError("coprime_to must be positive")
    if subdivisions < 2:
        raise ValueError("subdivisions must be at least two")

    for cap_numerator, cap_denominator in cap_ratios:
        if cap_numerator <= 0 or cap_denominator <= 0:
            raise ValueError("cap ratios must be positive")
        cap = min(
            maximum_denominator,
            maximum_denominator * cap_numerator // cap_denominator,
        )
        if cap < minimum_denominator:
            continue
        for target_numerator in range(1, subdivisions):
            target = (
                interval.lower * (subdivisions - target_numerator)
                + interval.upper * target_numerator
            ) / subdivisions
            reduced = target.limit_denominator(cap)
            if not interval.contains(reduced):
                continue
            denominator = _scaled_denominator_in_band(
                reduced.denominator,
                minimum_denominator,
                maximum_denominator,
                coprime_to,
            )
            if denominator is None:
                continue
            scale = denominator // reduced.denominator
            return RationalBandWitness(
                numerator=reduced.numerator * scale,
                denominator=denominator,
                reduced_value=reduced,
                target_numerator=target_numerator,
                target_denominator=subdivisions,
                denominator_cap=cap,
            )
    return None

#!/usr/bin/env python3
"""Exact ownership compression after the rank-29 recut of M(4,5)."""

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations


def weight(rank: int) -> Fraction:
    return Fraction(1, 2**rank - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def front(value: Fraction) -> int:
    """Least rank r for which w_r <= value."""
    assert value > 0
    rank = 2
    while weight(rank) > value:
        rank += 1
    return rank


@dataclass(frozen=True)
class Cohort:
    """A positive cone value together with its indivisible source owners."""

    name: str
    value: Fraction
    owners: frozenset[str]

    @staticmethod
    def source(name: str, value: Fraction) -> "Cohort":
        assert value > 0
        return Cohort(name, value, frozenset({name}))


def assert_partition(state: list[Cohort], all_owners: frozenset[str]) -> None:
    seen: set[str] = set()
    for cohort in state:
        assert cohort.value > 0
        assert cohort.value.denominator % 2 == 1
        assert seen.isdisjoint(cohort.owners)
        seen.update(cohort.owners)
    assert frozenset(seen) == all_owners


def state_value(state: list[Cohort]) -> Fraction:
    return sum((cohort.value for cohort in state), Fraction())


def replace_pool(
    state: list[Cohort],
    pool: list[Cohort],
    emitted: tuple[int, ...],
    name: str,
) -> Cohort:
    """Consume whole cohorts, emit atoms, and install their positive recode."""
    assert len(set(pool)) == len(pool)
    assert all(cohort in state for cohort in pool)
    owners = frozenset().union(*(cohort.owners for cohort in pool))
    assert sum(len(cohort.owners) for cohort in pool) == len(owners)
    remainder = sum((cohort.value for cohort in pool), Fraction())
    remainder -= sum((weight(rank) for rank in emitted), Fraction())
    assert remainder > 0
    assert remainder.denominator % 2 == 1
    for cohort in pool:
        state.remove(cohort)
    result = Cohort(name, remainder, owners)
    state.append(result)
    return result


def assert_minimal_pool(pool: list[Cohort], rank: int) -> None:
    """Every proper subpool is too small to emit w_rank."""
    total = sum((cohort.value for cohort in pool), Fraction())
    assert total >= weight(rank)
    for size in range(len(pool)):
        for subpool in combinations(pool, size):
            assert sum((cohort.value for cohort in subpool), Fraction()) < weight(rank)


def assert_greedy_front(state: list[Cohort], rank: int) -> None:
    assert front(state_value(state)) == rank


def main() -> None:
    # The sixteen physical sources remaining after the stable outer atoms.
    sources = {
        "a1": Cohort.source("a1", cylinder(9, 13)),
        "a2": Cohort.source("a2", cylinder(13, 17)),
        "a3": Cohort.source("a3", cylinder(17, 21)),
        "a4": Cohort.source("a4", cylinder(21, 25)),
        "b1": Cohort.source("b1", cylinder(9, 14)),
        "b2": Cohort.source("b2", cylinder(14, 19)),
        "b3": Cohort.source("b3", cylinder(19, 24)),
        "child1": Cohort.source("child1", cylinder(25, 29)),
        "child2": Cohort.source("child2", cylinder(5, 29)),
        "child3": Cohort.source("child3", cylinder(24, 29)),
    }
    for bit in range(1, 7):
        sources[f"lift{bit}"] = Cohort.source(
            f"lift{bit}", 2 ** (4 * bit) * cylinder(28, 29)
        )
    all_owners = frozenset(sources)
    assert len(all_owners) == 16

    stable_outer = {9, 13, 14, 17, 19, 21, 24, 25, 28}
    assert cylinder(4, 5) == sum(
        (weight(rank) for rank in stable_outer), Fraction()
    ) + sum((cohort.value for cohort in sources.values()), Fraction())

    # Retire the two exact heads whose residual owners enter the rank-29 pool.
    state = list(sources.values())
    r22 = replace_pool(state, [sources["a1"]], (22,), "R22")
    r23 = replace_pool(state, [sources["b1"]], (23,), "R23")
    pool29 = [r22, r23, sources["a2"], sources["b2"], sources["lift6"]]
    assert_minimal_pool(pool29, 29)
    y = replace_pool(state, pool29, (29,), "Y")
    assert front(y.value) == 35
    assert len(state) == 12
    assert_partition(state, all_owners)

    prefix = stable_outer | {22, 23, 29}
    assert cylinder(4, 5) == sum(
        (weight(rank) for rank in prefix), Fraction()
    ) + state_value(state)
    assert_greedy_front(state, 34)

    # Complete the second ownership layer.  Each listed pool is not only
    # ownership-closed but inclusion-minimal for its emitted head.
    c34 = replace_pool(state, [sources["child2"]], (34,), "C34")
    assert front(c34.value) == 39
    prefix.add(34)
    assert_greedy_front(state, 35)

    y1 = replace_pool(state, [y], (35,), "Y1")
    assert front(y1.value) == 37
    prefix.add(35)
    assert_greedy_front(state, 36)

    pool36 = [y1, sources["lift5"]]
    assert_minimal_pool(pool36, 36)
    z = replace_pool(state, pool36, (36,), "Z")
    assert front(z.value) == 40
    prefix.add(36)
    assert_greedy_front(state, 37)

    pool37 = [z, sources["a3"], c34, sources["lift4"]]
    assert_minimal_pool(pool37, 37)
    q = replace_pool(state, pool37, (37,), "Q")
    assert front(q.value) == 43
    prefix.add(37)
    assert_greedy_front(state, 42)

    pool42 = [q, sources["b3"]]
    assert_minimal_pool(pool42, 42)
    w42 = replace_pool(state, pool42, (42,), "W42")
    assert front(w42.value) == 44
    prefix.add(42)
    assert_greedy_front(state, 43)

    pool43 = [w42, sources["lift3"], sources["a4"]]
    assert_minimal_pool(pool43, 43)
    v = replace_pool(state, pool43, (43,), "V")
    assert front(v.value) == 47
    prefix.add(43)
    assert_greedy_front(state, 47)

    v1 = replace_pool(state, [v], (47,), "V1")
    assert front(v1.value) == 49
    prefix.add(47)
    assert_greedy_front(state, 48)

    pool48 = [v1, sources["lift2"]]
    assert_minimal_pool(pool48, 48)
    x48 = replace_pool(state, pool48, (48,), "X48")
    assert front(x48.value) == 55
    prefix.add(48)

    # The only untouched equal-front pair may be harmlessly grouped.  This
    # closes the whole first frontier into three disjoint positive cohorts.
    g52 = replace_pool(
        state, [sources["lift1"], sources["child3"]], (), "G52"
    )
    c54 = sources["child1"]
    assert sorted(front(cohort.value) for cohort in state) == [52, 54, 55]
    assert {cohort.name for cohort in state} == {"G52", "child1", "X48"}
    assert len(state) == 3
    assert_partition(state, all_owners)

    # Direct heads of the three compressed cohorts.
    assert_greedy_front(state, 52)
    g77 = replace_pool(state, [g52], (52,), "G77")
    assert front(g77.value) == 77
    prefix.add(52)

    assert_greedy_front(state, 54)
    c79 = replace_pool(state, [c54], (54,), "C79")
    assert front(c79.value) == 79
    prefix.add(54)

    direct_x = (55, 59, 61, 63, 64, 68, 70, 72, 74)
    for rank in direct_x:
        assert_greedy_front(state, rank)
        x48 = replace_pool(state, [x48], (rank,), f"X_after_{rank}")
        prefix.add(rank)
    x77 = x48
    assert front(x77.value) == 77

    # Synchronized-predecessor lemma, instantiated at r=77, s=84:
    # two front-77 cohorts cross w_76+w_77, and the remainder after both
    # atoms lies exactly in the rank-84 front interval.
    assert front(g77.value) == front(x77.value) == 77
    synchronized = g77.value + x77.value
    assert weight(76) + weight(77) + weight(84) <= synchronized
    assert synchronized < weight(76) + weight(77) + weight(83)
    assert g77.value < weight(76)
    assert x77.value < weight(76)

    assert_greedy_front(state, 76)
    r76 = replace_pool(state, [g77, x77], (76,), "R76")
    assert front(r76.value) == 77
    prefix.add(76)

    assert_greedy_front(state, 77)
    r84 = replace_pool(state, [r76], (77,), "R84")
    assert front(r84.value) == 84
    prefix.add(77)

    assert_greedy_front(state, 79)
    c83 = replace_pool(state, [c79], (79,), "C83")
    assert front(c83.value) == 83
    prefix.add(79)

    # Exact final conservation and physical-owner partition.
    assert len(state) == 2
    assert sorted(front(cohort.value) for cohort in state) == [83, 84]
    assert_partition(state, all_owners)
    assert cylinder(4, 5) == sum(
        (weight(rank) for rank in prefix), Fraction()
    ) + state_value(state)
    assert_greedy_front(state, 83)

    expected_prefix = {
        9, 13, 14, 17, 19, 21, 22, 23, 24, 25, 28, 29,
        34, 35, 36, 37, 42, 43, 47, 48, 52, 54, 55, 59,
        61, 63, 64, 68, 70, 72, 74, 76, 77, 79,
    }
    assert prefix == expected_prefix

    print("rank-29 state: 12 cohorts partitioning 16 physical owners")
    print("second-layer recut arities: 1,1,2,4,2,3,1,2")
    print("rank-48 compression: fronts [52,54,55]")
    print("synchronized predecessor: fronts [77,77] -> atoms [76,77] -> front 84")
    print("rank-79 state: two cohorts at fronts [83,84]")
    print("M(4,5) ownership compression: PASS")


if __name__ == "__main__":
    main()

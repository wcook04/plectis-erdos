#!/usr/bin/env python3
"""Exact receipts for StaticGenealogyMinCutObstruction.md."""

from fractions import Fraction


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return w(a) * w(b)


def split_children(node: tuple[int, int]) -> tuple[tuple[int, int], tuple[int, int]]:
    a, b = node
    assert 2 <= a <= b
    return (a, a + b), (b, a + b)


def follow(root: tuple[int, int], choices: str) -> tuple[int, int]:
    node = root
    for choice in choices:
        children = split_children(node)
        node = children[int(choice)]
    return node


def check_split_identity(max_endpoint: int = 40) -> int:
    checks = 0
    for a in range(2, max_endpoint + 1):
        for b in range(a, max_endpoint + 1):
            left, right = split_children((a, b))
            assert cylinder(a, b) == w(a + b) + cylinder(*left) + cylinder(*right)
            checks += 1
    return checks


def check_root_cut() -> dict[str, object]:
    root = (2, 3)

    # The first path uses right then left; the second uses left three times.
    rank_11_a = follow(root, "10")
    rank_11_b = follow(root, "000")
    assert rank_11_a == (3, 8)
    assert rank_11_b == (2, 9)
    assert sum(rank_11_a) == sum(rank_11_b) == 11

    rho = Fraction(31, 60)
    root_load = Fraction(1, 8)
    depth = 18
    boundary_load_bound = root_load * rho**depth
    boundary_value_bound = Fraction(4, 9) * boundary_load_bound
    tax_11 = cylinder(10, 11)

    assert boundary_value_bound == Fraction(1, 18) * rho**depth
    assert tax_11 == Fraction(1, 2_094_081)
    assert boundary_value_bound < tax_11

    # The actual j=0 split contracts load by at most 1/2, giving depth 17.
    sharp_depth = 17
    sharp_value_bound = Fraction(1, 18) * Fraction(1, 2) ** sharp_depth
    assert sharp_value_bound < tax_11

    return {
        "root": "M(2,3)",
        "rank_11_paths": [rank_11_a, rank_11_b],
        "cut_depth_using_31_over_60": depth,
        "boundary_value_upper_bound": str(boundary_value_bound),
        "mandatory_rank_11_tax": str(tax_11),
        "cut_margin_upper_bound": str(boundary_value_bound - tax_11),
        "sharper_half_contraction_depth": sharp_depth,
        "static_prefix_cut_feasible": False,
    }


def main() -> None:
    print(
        {
            "split_identity_checks": check_split_identity(),
            "root_cut": check_root_cut(),
            "ordinary_static_max_flow_models_dynamic_recuts": False,
            "required_extension": "exclusive supply-or-expand recut",
        }
    )


if __name__ == "__main__":
    main()

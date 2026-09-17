<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Exact limiting-sign certificate

For every one of the four nonreal-critical arms in the near-pentagon family,
the limiting real part is strictly negative. Run `python3 certify_hub_limits.py`
from this directory. Only the Python standard library is required. The script uses rational interval arithmetic, with 180 bisections for the algebraic radicals, and writes `certified_hub_limits.json` beside itself.

It verifies the four strictly negative real parts used to eliminate four arms of a nonreal critical point, their printed coarse rational enclosures, and the positive central length coefficient. The lower nonreal point follows by conjugation in the written proof.

This is **not** a floating-point root search, an explicit remainder bound, a proof for every ε≤1/100, a Lean theorem or an independent check of the implicit-function argument. The written proof uses finitely many strict limiting signs to obtain an unspecified sufficiently-small positive threshold. Numerical experiments from the working session are not needed for the theorem and are deliberately not used as its evidence.

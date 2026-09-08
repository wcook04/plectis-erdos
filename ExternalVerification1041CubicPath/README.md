# A cubic polygonal connector

A monic cubic is given by its three roots, counted with multiplicity, all strictly inside the unit disc. Two distinct indices admit an explicit two-segment path through a hub. Every point of this path lies in the open unit lemniscate, and its actual extended variation on [0,2] is less than two. The path is continuous and of bounded variation. Squarefreeness guarantees distinct endpoint values; repeated-root indices may yield a constant path.

The Challenge imports only Mathlib. It writes the factorization hypothesis and curve conclusions explicitly and defines the hub by its two affine pieces. No root-count supplier, critical-value bound or path theorem is a hypothesis. The Solution unfolds the source curve definitions and transports `PaperCubicCompletion.cubic_paper_complete`.

This is a degree-three result with strict root containment. It claims neither the closed-disc boundary nor the general-degree problem. Novelty is unassessed. The focused wrapper build and axiom audit passed on 8 September 2026. The selected theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. Supported-runner Comparator replay remains pending; no Palomar submission has been made.

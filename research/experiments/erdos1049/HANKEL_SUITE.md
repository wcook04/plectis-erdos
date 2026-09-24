# Rank-8 Hankel / cyclotomic / interval suite

The packet rank-8 determinant, residue, and interval certificates live at
repository-root `computations/` (drivers) and `computations/certificates/`
(exact JSON). That path matches the papers' `computations/intervals.py`
locator. This directory holds the other finite computations of the long
Erdős 1049 paper; see [README.md](README.md). Its `cyclotomic_content.py` is a
separate standard-library implementation of the cyclotomic contents and the 76
residue witnesses, and it reproduces
`computations/certificates/cyclotomic_residue_witnesses.json` exactly.

#!/usr/bin/env python3
"""Register verified r7 modules in the barrel and verified wrap packages in the lakefile.

WHY
---
Every desk disposition lists `barrel_imports_needed` (modules that compiled) and
`lakefile_libs_needed` (Palomar wrap dirs whose Solution elaborated).  Landing
those by hand across eight problems loses lines and duplicates entries.  This
does the mechanical move idempotently: an import or lib already present is left
alone, a wrap dir without Challenge.lean + Solution.lean + comparator.json is
refused, and a module whose source file does not exist is refused.

USAGE
-----
    ./repo-python formal_math/erdos257_period_noncollapse/scripts/r7_register_modules.py \
        --disposition <work/erdos_N/disposition.json> [...] [--dry-run]
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve()
PROJECT = HERE.parents[1]
BARREL = PROJECT / "ErdosProblems.lean"
LAKEFILE = PROJECT / "lakefile.toml"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--disposition", type=Path, action="append", required=True)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    barrel_text = BARREL.read_text(encoding="utf-8")
    existing_imports = set(re.findall(r"^import\s+(\S+)", barrel_text, re.M))
    lake_text = LAKEFILE.read_text(encoding="utf-8")
    existing_libs = set(re.findall(r'^\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"', lake_text, re.M))
    add_imports: list[str] = []
    add_libs: list[str] = []
    refused: list[str] = []
    for dpath in args.disposition:
        d = json.loads(dpath.read_text(encoding="utf-8"))
        for mod in d.get("barrel_imports_needed") or []:
            src = PROJECT / (mod.replace(".", "/") + ".lean")
            if not src.is_file():
                refused.append(f"{mod}: no source file")
            elif mod not in existing_imports and mod not in add_imports:
                add_imports.append(mod)
        for lib in d.get("lakefile_libs_needed") or []:
            # Desk dispositions vary: a bare name, a name with a trailing note, or {"lib": name, ...}.
            if isinstance(lib, dict):
                lib = str(lib.get("lib") or lib.get("name") or "")
            lib = re.split(r"[\s(]", str(lib).strip(), maxsplit=1)[0]
            if not lib:
                continue
            d_lib = PROJECT / lib
            need = ["Challenge.lean", "Solution.lean", "comparator.json"]
            missing = [f for f in need if not (d_lib / f).is_file()]
            if missing:
                refused.append(f"{lib}: missing {missing}")
            elif lib not in existing_libs and lib not in add_libs:
                add_libs.append(lib)
    print(json.dumps({"add_imports": add_imports, "add_libs": add_libs, "refused": refused, "dry_run": args.dry_run}, indent=1))
    if args.dry_run or refused:
        return 1 if refused else 0
    if add_imports:
        # Lean requires every `import` before any other command: insert after the last existing import.
        lines = barrel_text.splitlines()
        last = max(i for i, l in enumerate(lines) if l.startswith("import "))
        lines[last + 1:last + 1] = [f"import {m}" for m in add_imports]
        BARREL.write_text("\n".join(lines) + "\n", encoding="utf-8")
    if add_libs:
        new = lake_text.rstrip("\n") + "\n" + "".join(f'\n[[lean_lib]]\nname = "{l}"\n' for l in add_libs)
        LAKEFILE.write_text(new, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

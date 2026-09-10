#!/usr/bin/env python3
"""Non-Lean unit checks for the dedicated #249 Comparator receipt gate."""

import importlib.util
from pathlib import Path
import json
import tempfile
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("write_erdos249_totient_kernel_comparator_receipt.py")
SPEC = importlib.util.spec_from_file_location("receipt", SCRIPT)
assert SPEC and SPEC.loader
receipt = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(receipt)


def main() -> int:
    assert receipt.negative_is_semantic(1, receipt.EXPECTED_MISMATCH)
    assert not receipt.negative_is_semantic(0, receipt.EXPECTED_MISMATCH)
    assert not receipt.negative_is_semantic(124, receipt.EXPECTED_MISMATCH)
    assert not receipt.negative_is_semantic(125, receipt.EXPECTED_MISMATCH)
    assert not receipt.negative_is_semantic(1, "unrelated elaboration failure")

    workflow = (SCRIPT.parent.parent / ".github/workflows/lean.yml").read_text()
    required = [
        "NANODA_REV: " + receipt.PINS["nanoda"],
        "cargo build --release --locked --bin nanoda_bin",
        'export COMPARATOR_NANODA="$RUNNER_TEMP/nanoda/target/release/nanoda_bin"',
        '--nanoda-bin "$RUNNER_TEMP/nanoda/target/release/nanoda_bin"',
    ]
    if any(token not in workflow for token in required):
        raise RuntimeError("CI does not provision the pinned additional kernel")
    if workflow.count('-E COMPARATOR_NANODA="$COMPARATOR_NANODA"') != 2:
        raise RuntimeError("both sandbox routes must receive the Nanoda executable")

    # A missing additional kernel must fail even when both Comparator exits
    # look correct. This caught CI enabling Nanoda without installing it.
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        positive, negative = root / "positive.log", root / "negative.log"
        positive.write_text("accepted")
        negative.write_text(receipt.EXPECTED_MISMATCH)
        binary = root / "tool"
        binary.write_bytes(b"fixture binary")
        output = root / "receipt.json"
        argv = [
            str(SCRIPT),
            "--expected-commit",
            "a" * 40,
            "--positive-exit",
            "0",
            "--negative-exit",
            "1",
            "--positive-log",
            str(positive),
            "--negative-log",
            str(negative),
            "--sandbox-mode",
            "user-manager",
            "--output",
            str(output),
        ]
        for name, revision in receipt.PINS.items():
            argv += [
                "--" + name + "-rev",
                revision,
                "--" + name + "-bin",
                str(root / "missing") if name == "nanoda" else str(binary),
            ]
        with (
            patch.object(receipt, "ROOT", root),
            patch.object(receipt, "INPUTS", {}),
            patch.object(receipt.subprocess, "check_output", return_value="a" * 40),
            patch("sys.argv", argv),
        ):
            if receipt.main() != 1:
                raise RuntimeError("missing Nanoda binary was accepted")
        result = json.loads(output.read_text())
        if (
            result["checks"]["tool_binaries_recorded"]
            or result["binary_sha256"]["nanoda"] is not None
        ):
            raise RuntimeError("missing Nanoda was not recorded")
    print("#249 dedicated Comparator receipt semantics: pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

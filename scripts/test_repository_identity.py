#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial checks for the public repository identity authority reader."""

from __future__ import annotations

import os
import tempfile
from pathlib import Path

import repository_identity


ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    """Keep identity-boundary checks active when Python is run with ``-O``."""
    if not condition:
        raise AssertionError(message)


def rejected(path: Path, phrase: str) -> None:
    try:
        repository_identity.load_identity(path)
    except repository_identity.IdentityError as exc:
        require(phrase in str(exc), str(exc))
    else:
        raise AssertionError(f"identity loader accepted unsafe path: {path}")


def main() -> int:
    identity = repository_identity.load_identity()
    require(
        identity["schema"] == "public-repository-identity/1",
        "live repository identity did not load from its authority file",
    )

    with tempfile.TemporaryDirectory(prefix="repository-identity-safety-") as raw:
        root = Path(raw)
        valid = root / "identity.json"
        valid.write_bytes((ROOT / "docs" / "repository_identity.json").read_bytes())
        require(
            repository_identity.load_identity(valid)["current"]["slug"]
            == identity["current"]["slug"],
            "regular identity fixture did not load",
        )

        linked = root / "linked.json"
        linked.symlink_to(valid)
        rejected(linked, "symbolic links")

        directory = root / "directory.json"
        directory.mkdir()
        rejected(directory, "regular file")

        if hasattr(os, "mkfifo"):
            fifo = root / "identity.fifo"
            os.mkfifo(fifo)
            rejected(fifo, "regular file")

    print(
        "test_repository_identity: regular authority loads; symlink, directory, "
        "and FIFO inputs are rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Resolve production helpers and sibling tests for direct and module runs."""
from pathlib import Path
import sys

TESTS = Path(__file__).resolve().parent
SCRIPTS = TESTS.parent
ROOT = SCRIPTS.parent
for directory in (SCRIPTS, TESTS):
    value = str(directory)
    if value not in sys.path:
        sys.path.insert(0, value)

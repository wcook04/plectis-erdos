# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Behavioural tests for the public repository tools."""
from . import _test_bootstrap
import sys

sys.modules.setdefault("_test_bootstrap", _test_bootstrap)

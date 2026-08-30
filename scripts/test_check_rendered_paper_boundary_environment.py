#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep Poppler boundary checks independent of ambient process state."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path
from unittest.mock import patch

import check_rendered_paper_boundary as boundary


def require(condition: bool, message: str) -> None:
    """Keep the external-tool contract active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-release",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    pdftotext = "/opt/poppler/bin/pdftotext"
    pdftohtml = "/opt/poppler/bin/pdftohtml"
    pdf = boundary.ROOT / "erdos249-257-main-paper.pdf"
    completed = [
        subprocess.CompletedProcess([], 0, stdout="plain text\n"),
        subprocess.CompletedProcess([], 0, stdout=""),
        subprocess.CompletedProcess([], 0, stdout="page text\n"),
    ]
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(boundary.subprocess, "run", side_effect=completed) as run:
            require(
                boundary.rendered_text(pdf, pdftotext) == "plain text\n",
                "pdftotext output was not returned",
            )
            require(
                boundary.rendered_hrefs(pdf, pdftohtml) == set(),
                "pdftohtml output was not parsed",
            )
            require(
                boundary.rendered_pages(pdf, pdftotext, 1, 2)
                == "page text\n",
                "paged pdftotext output was not returned",
            )

    require(len(run.call_args_list) == 3, "all Poppler calls were not exercised")
    for call in run.call_args_list:
        kwargs = call.kwargs
        sanitized = kwargs["env"]
        for key in (
            "GIT_DIR",
            "GIT_NAMESPACE",
            "GIT_REPLACE_REF_BASE",
            "PYTHONPATH",
        ):
            require(key not in sanitized, f"ambient {key} leaked into Poppler")
        require(sanitized["LC_ALL"] == "C.UTF-8", "canonical locale missing")
        require(sanitized["LANG"] == "C.UTF-8", "canonical LANG missing")
        require(
            sanitized["PATH"].split(os.pathsep)[0] == "/opt/poppler/bin",
            "Poppler executable directory was not preserved",
        )
        require(
            kwargs["timeout"] == boundary.EXTERNAL_TOOL_TIMEOUT_SECONDS,
            "Poppler timeout drifted",
        )

    require(
        boundary.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "rendered-paper environment contract drifted",
    )
    print(
        "test_check_rendered_paper_boundary_environment: Poppler checks use a "
        "clean snapshot environment and bounded subprocesses"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

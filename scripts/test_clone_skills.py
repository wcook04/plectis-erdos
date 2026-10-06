#!/usr/bin/env python3
"""Test clone-local skill discovery, installation, and first-action routes."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
INSTALLER = ROOT / "scripts" / "install_agent_skills.py"
PYTHON_COMMAND_RE = re.compile(
    r"python3\s+(scripts/[A-Za-z0-9_./-]+\.py)([^`\n]*)"
)
OPTION_RE = re.compile(r"(?<![A-Za-z0-9_-])(--[a-z][a-z0-9-]*)")


def local_skill_references(source: str) -> set[str]:
    """Return exact clone-local paths advertised in Markdown links or code spans."""
    candidates = set(re.findall(r"\[[^]]+\]\(([^)]+)\)", source))
    candidates.update(re.findall(r"`([^`\n]+)`", source))
    prefixes = (
        ".github/",
        "AGENTS",
        "ARCHITECTURE",
        "CONTRIBUTING",
        "HUMAN_ENTRY",
        "METHODOLOGY",
        "README",
        "docs/",
        "scripts/",
        "skills/",
    )
    result: set[str] = set()
    for candidate in candidates:
        value = candidate.split("#", 1)[0].strip().rstrip(".,:;")
        if not value.startswith(prefixes):
            continue
        if any(marker in value for marker in ("<", ">", "*", " ", "://", "::")):
            continue
        result.add(value)
    return result


def advertised_python_commands(source: str) -> list[tuple[str, str | None, set[str]]]:
    """Extract tracked Python CLIs and options from runnable documentation."""
    joined = re.sub(r"\\\s*\n\s*", " ", source)
    commands: list[tuple[str, str | None, set[str]]] = []
    for match in PYTHON_COMMAND_RE.finditer(joined):
        script = match.group(1)
        tail = match.group(2).strip()
        first = tail.split(maxsplit=1)[0] if tail else ""
        positional = first if re.fullmatch(r"[a-z][a-z0-9_-]*", first) else None
        commands.append((script, positional, set(OPTION_RE.findall(tail))))
    return commands


def validate_advertised_python_commands(documents: dict[str, str]) -> None:
    """Require every advertised CLI selector to exist in that command's help."""
    help_cache: dict[tuple[str, str | None], str] = {}
    for document, source in documents.items():
        for script, positional, options in advertised_python_commands(source):
            path = ROOT / script
            assert path.is_file(), (document, script)
            if not options:
                continue
            cache_key = (script, None)
            if cache_key not in help_cache:
                result = subprocess.run(
                    [sys.executable, str(path), "--help"],
                    cwd=ROOT,
                    text=True,
                    capture_output=True,
                    check=False,
                )
                assert result.returncode == 0, (document, script, result.stderr)
                help_cache[cache_key] = result.stdout + result.stderr
            help_text = help_cache[cache_key]
            if positional is not None:
                assert positional in help_text, (document, script, positional)
            missing = options - set(OPTION_RE.findall(help_text))
            if missing and positional is not None:
                cache_key = (script, positional)
                if cache_key not in help_cache:
                    result = subprocess.run(
                        [sys.executable, str(path), positional, "--help"],
                        cwd=ROOT,
                        text=True,
                        capture_output=True,
                        check=False,
                    )
                    assert result.returncode == 0, (document, script, positional, result.stderr)
                    help_cache[cache_key] = result.stdout + result.stderr
                missing -= set(OPTION_RE.findall(help_cache[cache_key]))
            assert not missing, (document, script, sorted(missing))


def run(*args: str, expected: int = 0) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        ["python3", str(INSTALLER), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != expected:
        raise AssertionError(
            f"command returned {result.returncode}, expected {expected}:\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def check_invalid_destination_cli() -> None:
    """Reject a file destination before preview or apply, preserving its bytes."""
    with tempfile.TemporaryDirectory(prefix="plectis-invalid-skills-") as tmp:
        root = Path(tmp)
        blocked = root / "existing-file"
        original = b"existing contributor material\n"
        blocked.write_bytes(original)
        link = root / "file-link"
        link.symlink_to(blocked)
        for target in (blocked, blocked / "skills", link):
            for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
                result = run("--target-dir", str(target), "--skill", "explain-public-system",
                             *options, expected=2)
                if "must be a directory" not in result.stderr or "Traceback" in result.stderr:
                    raise AssertionError(result.stderr)
                if result.stdout or blocked.read_bytes() != original or not link.is_symlink():
                    raise AssertionError("invalid destination advertised a skill or changed user material")


def check_companion_installation_default() -> None:
    """Host defaults cannot install generic workflows without explicit selection."""
    spec = importlib.util.spec_from_file_location("clone_skill_installer", INSTALLER)
    assert spec and spec.loader
    installer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(installer)
    registry = json.loads((ROOT / "skills/registry.json").read_text(encoding="utf-8"))
    catalog_names = {row["id"] for row in registry["skills"]}
    assert "plectis-frontier" not in catalog_names
    with tempfile.TemporaryDirectory(prefix="plectis-default-skills-") as temp:
        base = Path(temp)
        environments = {"CODEX_HOME": str(base / "legacy"),
                        "CLAUDE_CONFIG_DIR": str(base / "claude")}
        def invoke(*args: str) -> str:
            with mock.patch.object(installer.Path, "home", return_value=base), \
                    mock.patch.object(installer.os, "environ", environments), \
                    mock.patch.object(sys, "argv", [str(INSTALLER), *args]), \
                    contextlib.redirect_stdout(io.StringIO()) as output:
                result = installer.main()
                if result != 0:
                    raise AssertionError(f"installer returned {result}: {args}")
                return output.getvalue()
        for host, target in (("codex", base / ".agents/skills"),
                             ("claude", base / "claude/skills"),
                             ("codex-legacy", base / "legacy/skills")):
            preview = invoke("--target", host)
            assert "plectis-frontier" in preview and "preview only" in preview
            assert not target.exists(), "default preview changed a host directory"
            invoke("--target", host, "--apply")
            assert {p.name for p in target.iterdir()} == {"plectis-frontier"}
            invoke("--target", host, "--check")
            invoke("--target", host, "--companion", "--check")
        custom = base / "custom"
        run("--target-dir", str(custom), "--apply")
        assert {p.name for p in custom.iterdir()} == {"plectis-frontier"}
        run("--target-dir", str(custom), "--check")
        full = base / "explicit-catalog"
        preview = run("--target-dir", str(full), "--all-clone-skills")
        assert not full.exists() and "preview only" in preview.stdout
        run("--target-dir", str(full), "--all-clone-skills", "--apply")
        assert {p.name for p in full.iterdir()} == catalog_names
        run("--target-dir", str(full), "--all-clone-skills", "--check")
        # A default apply preserves previously chosen generic workflows.
        run("--target-dir", str(full), "--apply")
        assert {p.name for p in full.iterdir()} == catalog_names | {"plectis-frontier"}
        chosen = base / "selected"
        names = ("explain-public-system", "mine-open-problem")
        run("--target-dir", str(chosen), "--skill", names[0], "--skill", names[1], "--apply")
        assert {p.name for p in chosen.iterdir()} == set(names)
        listed_catalog = run("--list").stdout
        listed_explicit_catalog = run("--list", "--all-clone-skills").stdout
        listed_companion = run("--list", "--companion").stdout
        listed_selection = run("--list", "--skill", names[0]).stdout
        assert set(listed_catalog.splitlines()) == set(listed_explicit_catalog.splitlines())
        assert len(listed_companion.splitlines()) == 1
        assert listed_selection.startswith(names[0] + "\t")
        for flags in (("--companion", "--all-clone-skills"),
                      ("--companion", "--skill", names[0]),
                      ("--all-clone-skills", "--skill", names[0])):
            forbidden = base / "conflicting-selectors"
            result = run("--target-dir", str(forbidden), *flags, "--apply", expected=2)
            assert "not allowed with argument" in result.stderr
            assert not forbidden.exists(), "conflicting flags modified a destination"
        run("--list", "--skill", "missing-workflow", expected=2)


def main() -> int:
    check_invalid_destination_cli()
    check_companion_installation_default()
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    skill_index = (ROOT / "skills" / "README.md").read_text(encoding="utf-8")
    entry = (ROOT / "AGENTS.md").read_text(encoding="utf-8")
    registry = json.loads((ROOT / "skills" / "registry.json").read_text(encoding="utf-8"))
    registered = {row["id"] for row in registry["skills"]}
    skills = tuple(row["id"] for row in registry["skills"])
    command_documents: dict[str, str] = {}

    listed = run("--list").stdout
    for name in skills:
        skill = ROOT / "skills" / name / "SKILL.md"
        assert skill.is_file(), skill
        source = skill.read_text(encoding="utf-8")
        command_documents[str(skill.relative_to(ROOT))] = source
        assert f"name: {name}" in source, name
        assert name in listed, name
        description = next(
            line.removeprefix("description: ")
            for line in source.splitlines()
            if line.startswith("description: ")
        )
        assert description in listed, name
        assert name in skill_index, name
        assert name in registered, name
        assert "/Users/" not in source and "src/ai_workflow" not in source, name
        for reference in local_skill_references(source):
            assert (ROOT / reference).exists(), (name, reference)
        for reference in set(
            re.findall(r"(?<![A-Za-z0-9_.-])(scripts/[A-Za-z0-9_./-]+\.py)", source)
        ):
            assert (ROOT / reference).is_file(), (name, reference)

    return_template = "docs/research-commons/RETURN_PACKAGE_TEMPLATE.md"
    command_documents[return_template] = (ROOT / return_template).read_text(encoding="utf-8")
    validate_advertised_python_commands(command_documents)

    assert re.search(r"\[[^]]+\]\(AGENTS\.md(?:#[^)]*)?\)", readme)
    assert "](CONTRIBUTING.md)" in readme
    assert 'agent_entry.py --entry "<task in ordinary language>"' in entry
    assert "agent_entry.py --skills" in entry

    with tempfile.TemporaryDirectory(prefix="plectis-skill-test-") as temp:
        target = Path(temp) / "skills"
        preview = run("--target-dir", str(target), "--skill", "explain-public-system")
        assert "preview only" in preview.stdout
        assert not target.exists(), "preview mutated the destination"

        run(
            "--target-dir",
            str(target),
            "--skill",
            "explain-public-system",
            "--apply",
        )
        installed = target / "explain-public-system" / "SKILL.md"
        assert installed.is_file()
        run(
            "--target-dir",
            str(target),
            "--skill",
            "explain-public-system",
            "--check",
        )

        # A user edit can preserve copy2's source timestamp and byte count.
        # The check and preview must detect it, and ordinary apply must keep it.
        original = installed.read_bytes()
        stamp = installed.stat()
        modified = bytes([original[0] ^ 1]) + original[1:]
        installed.write_bytes(modified)
        os.utime(installed, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
        stale = run(
            "--target-dir", str(target), "--skill", "explain-public-system",
            "--check", expected=1,
        )
        assert "different" in stale.stdout
        preview = run(
            "--target-dir", str(target), "--skill", "explain-public-system",
        )
        assert "different" in preview.stdout and "preview only" in preview.stdout
        run(
            "--target-dir", str(target), "--skill", "explain-public-system",
            "--apply", expected=1,
        )
        assert installed.read_bytes() == modified, "collision replaced user content"
        run(
            "--target-dir", str(target), "--skill", "explain-public-system",
            "--force", "--apply",
        )
        assert installed.read_bytes() == original
        run(
            "--target-dir", str(target), "--skill", "explain-public-system",
            "--check",
        )

        installed.write_text(installed.read_text(encoding="utf-8") + "\nchanged\n")
        collision = run(
            "--target-dir",
            str(target),
            "--skill",
            "explain-public-system",
            "--apply",
            expected=1,
        )
        assert "already contains different material" in collision.stderr

        link_target = Path(temp) / "links"
        run(
            "--target-dir",
            str(link_target),
            "--skill",
            "mine-open-problem",
            "--mode",
            "symlink",
            "--apply",
        )
        link = link_target / "mine-open-problem"
        assert link.is_symlink()
        run(
            "--target-dir",
            str(link_target),
            "--skill",
            "mine-open-problem",
            "--mode",
            "symlink",
            "--check",
        )

    print(
        "clone skills: companion defaults, explicit catalog, selection conflicts, discovery, live CLI grammar, preview, copy, symlink, "
        "collision, and routes PASS"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

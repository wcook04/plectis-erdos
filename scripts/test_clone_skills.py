#!/usr/bin/env python3
"""Test clone-local skill discovery, installation, and first-action routes."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest import mock
from unittest.mock import patch

import install_agent_skills as installer


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
        [sys.executable, str(INSTALLER), *args],
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


def check_overlapping_source_cli() -> None:
    """Real CLI refuses self-links/nested copies without losing clone instructions."""
    driver = [sys.executable, *(["-O"] * sys.flags.optimize)]
    with tempfile.TemporaryDirectory(prefix="plectis-overlap-skills-") as temporary:
        clone = Path(temporary) / "parent with spaces and 'quotes" / "mine-open-problem"
        (clone / "scripts").mkdir(parents=True)
        for name in ("install_agent_skills.py", "agent_skill_catalog.py"):
            shutil.copy2(ROOT / "scripts" / name, clone / "scripts" / name)
        shutil.copytree(ROOT / "skills", clone / "skills")
        companion = clone / ".agents/skills/plectis-frontier"
        shutil.copytree(ROOT / ".agents/skills/plectis-frontier", companion)
        companion_bytes = {path.relative_to(companion): path.read_bytes()
                           for path in companion.rglob("*") if path.is_file()}
        name = "mine-open-problem"
        source = clone / "skills" / name
        original = (source / "SKILL.md").read_bytes()
        foreign = source / "local-notes.txt"
        foreign.write_bytes(b"contributor notes\n")
        alias = clone / "skills-alias"
        alias.symlink_to(clone / "skills", target_is_directory=True)
        parent_alias = Path(temporary) / "parent-alias"
        parent_alias.symlink_to(clone.parent, target_is_directory=True)
        source_bytes = {path.relative_to(clone / "skills"): path.read_bytes()
                        for path in (clone / "skills").rglob("*") if path.is_file()}
        cases = [
            ("skills", "symlink"),
            (str(alias), "symlink"),
            (str(source), "copy"),
            (str(source), "symlink"),
            (str(clone.parent), "copy"),
            (str(parent_alias), "copy"),
        ]
        for target, mode in cases:
            result = subprocess.run(
                [*driver, str(clone / "scripts/install_agent_skills.py"),
                 "--target-dir", target, "--skill", name,
                 "--mode", mode, "--apply", "--force"],
                cwd=clone, text=True, capture_output=True, check=False,
            )
            if result.returncode != 2 or "refusing overlapping source skill" not in result.stderr:
                raise AssertionError((target, mode, result.returncode, result.stdout, result.stderr))
            if "Traceback" in result.stderr or source.is_symlink():
                raise AssertionError("overlap produced a traceback or replaced the source")
            if (source / "SKILL.md").read_bytes() != original or foreign.read_bytes() != b"contributor notes\n":
                raise AssertionError("overlap changed clone instructions or contributor notes")
            if (source / name).exists() or (source / name).is_symlink():
                raise AssertionError("nested destination created despite overlap refusal")
        # The first choice would create a disjoint sibling, but a later choice
        # encloses the whole clone. The complete plan must refuse before either.
        result = subprocess.run(
            [*driver, str(clone / "scripts/install_agent_skills.py"),
             "--target-dir", str(clone.parent),
             "--skill", "explain-public-system", "--skill", name,
             "--mode", "copy", "--apply", "--force"],
            cwd=clone, text=True, capture_output=True, check=False,
        )
        if result.returncode != 2 or "refusing overlapping source skill" not in result.stderr:
            raise AssertionError(("multi-selection", result.returncode, result.stderr))
        if (clone.parent / "explain-public-system").exists() or result.stdout:
            raise AssertionError("first selection wrote or advertised work before plan rejection")
        # Installing a different skill under an unselected source is also unsafe.
        result = subprocess.run(
            [*driver, str(clone / "scripts/install_agent_skills.py"),
             "--target-dir", str(source), "--skill", "explain-public-system",
             "--apply", "--force"],
            cwd=clone, text=True, capture_output=True, check=False,
        )
        if result.returncode != 2 or "refusing overlapping source skill" not in result.stderr:
            raise AssertionError(("unselected source", result.returncode, result.stderr))
        if (source / "explain-public-system").exists():
            raise AssertionError("installation wrote under an unselected source")
        if (source / "SKILL.md").read_bytes() != original or foreign.read_bytes() != b"contributor notes\n":
            raise AssertionError("plan rejection changed source material")
        # Default companion selection and explicit clone workflows share the
        # same source boundary, even when the overlapped source is unselected.
        companion_cases = (
            (companion.parent, []),
            (companion, ["--skill", "explain-public-system"]),
            (source, []),
        )
        for target, selection in companion_cases:
            result = subprocess.run(
                [*driver, str(clone / "scripts/install_agent_skills.py"),
                 "--target-dir", str(target), *selection, "--apply", "--force"],
                cwd=clone, text=True, capture_output=True, check=False,
            )
            if result.returncode != 2 or "refusing overlapping source skill" not in result.stderr:
                raise AssertionError(("companion overlap", str(target), selection,
                                      result.returncode, result.stdout, result.stderr))
            if result.stdout or "Traceback" in result.stderr:
                raise AssertionError("companion overlap advertised work or raised a traceback")
        if companion.is_symlink() or {
                path.relative_to(companion): path.read_bytes()
                for path in companion.rglob("*") if path.is_file()} != companion_bytes:
            raise AssertionError("overlap plan changed companion source bytes")
        after_bytes = {path.relative_to(clone / "skills"): path.read_bytes()
                       for path in (clone / "skills").rglob("*") if path.is_file()}
        if after_bytes != source_bytes:
            raise AssertionError("overlap plan changed selected or unselected source bytes")
        # A disjoint existing link to source remains current in link mode;
        # explicit copy replacement unlinks it without deleting its source.
        target = clone / "host skills"
        target.mkdir()
        installed = target / name
        installed.symlink_to(source, target_is_directory=True)
        for mode, options in (("symlink", ["--check"]), ("copy", ["--apply", "--force"])):
            result = subprocess.run(
                [*driver, str(clone / "scripts/install_agent_skills.py"),
                 "--target-dir", str(target), "--skill", name, "--mode", mode, *options],
                cwd=clone, text=True, capture_output=True, check=False,
            )
            if result.returncode != 0:
                raise AssertionError((mode, result.stderr))
        if installed.is_symlink() or (installed / "SKILL.md").read_bytes() != original:
            raise AssertionError("valid link-to-copy replacement failed")
        if (source / "SKILL.md").read_bytes() != original or foreign.read_bytes() != b"contributor notes\n":
            raise AssertionError("valid link replacement changed source material")


def require(condition: bool, message: object) -> None:
    """Keep fixture calls and preservation checks active under optimized Python."""
    if not condition:
        raise AssertionError(message)


def check_overlapping_installation_paths() -> None:
    """Invalid selections must fail before preview, staging, or replacement."""
    with tempfile.TemporaryDirectory(prefix="plectis-skill-overlap-") as temp:
        root = Path(temp)
        name = "writing"
        source = root / name
        source.mkdir()
        original = b"source instructions\n"
        (source / "SKILL.md").write_bytes(original)
        parent_alias = root / "source-alias"
        parent_alias.symlink_to(source, target_is_directory=True)
        ancestor = root / "ancestor" / name
        nested_source = ancestor / "nested"
        nested_source.mkdir(parents=True)
        (ancestor / "SKILL.md").write_bytes(b"ancestor material\n")
        (nested_source / "SKILL.md").write_bytes(original)
        source_alias = ancestor / "source-alias"
        source_alias.symlink_to(source, target_is_directory=True)
        checkout_alias = ancestor / "checkout-alias"
        checkout_alias.symlink_to(root, target_is_directory=True)
        chained_alias = root / "chained-alias"
        chained_alias.symlink_to(checkout_alias / name, target_is_directory=True)

        cases = (
            (source, source / "references"),
            (source, parent_alias / "references"),
            (nested_source, ancestor.parent),
            (source_alias, ancestor.parent),
            (checkout_alias / name, ancestor.parent),
            (chained_alias, ancestor.parent),
        )
        # Linux commonly uses case-sensitive filesystems; macOS commonly does
        # not. Exercise the real alias only where both spellings are one entry.
        case_alias = root / name.upper()
        if case_alias.exists() and os.path.samefile(source, case_alias):
            cases += ((source, case_alias / "references"),)
        for mode in ("copy", "symlink"):
            for selected, target in cases:
                destination = target / name
                for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
                    stdout, stderr = io.StringIO(), io.StringIO()
                    args = [str(INSTALLER), "--target-dir", str(target), "--skill", name,
                            "--mode", mode, *options]
                    with patch.object(sys, "argv", args), \
                            patch.object(installer, "skill_directories", return_value={name: selected}), \
                            contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                        require(installer.main() == 2, 'installer safeguard assertion failed')
                    require(not stdout.getvalue(), stdout.getvalue())
                    require('must not overlap' in stderr.getvalue() and 'Traceback' not in stderr.getvalue(), 'installer safeguard assertion failed')
                    require((selected / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
                    require((ancestor / 'SKILL.md').read_bytes() == b'ancestor material\n', 'installer safeguard assertion failed')
                    require(parent_alias.is_symlink(), 'installer safeguard assertion failed')
                    require(source_alias.is_symlink(), 'installer safeguard assertion failed')
                    require(checkout_alias.is_symlink(), 'installer safeguard assertion failed')
                    require(chained_alias.is_symlink(), 'installer safeguard assertion failed')
                with patch.object(installer.tempfile, "mkdtemp", side_effect=AssertionError("staged unsafe install")):
                    try:
                        installer.install_one(selected, destination, mode, True)
                    except ValueError as error:
                        require('must not overlap' in str(error), 'installer safeguard assertion failed')
                    else:
                        raise AssertionError("direct unsafe installation accepted")

        # A selected source can be disjoint while its destination encloses
        # access links used by an unselected source. Check the entire plan.
        for unselected in (source_alias, checkout_alias / name, chained_alias):
            for mode in ("copy", "symlink"):
                stdout, stderr = io.StringIO(), io.StringIO()
                args = [str(INSTALLER), "--target-dir", str(ancestor.parent),
                        "--skill", name, "--mode", mode, "--force", "--apply"]
                with patch.object(sys, "argv", args), \
                        patch.object(installer, "skill_directories",
                                     return_value={name: source, "unselected": unselected}), \
                        contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                    result = installer.main()
                if result != 2 or stdout.getvalue() or "must not overlap" not in stderr.getvalue():
                    raise AssertionError(("cross-source alias", unselected, mode,
                                          result, stdout.getvalue(), stderr.getvalue()))
                if ((ancestor / "SKILL.md").read_bytes() != b"ancestor material\n"
                        or (source / "SKILL.md").read_bytes() != original
                        or not all(path.is_symlink() for path in
                                   (source_alias, checkout_alias, chained_alias))):
                    raise AssertionError("cross-source alias refusal changed source access")

        # The source boundary refuses even identical-source
        # copies. No-op identity is not an exception to source protection.
        with patch.object(installer.tempfile, "mkdtemp", side_effect=AssertionError("staged own source")):
            try:
                installer.install_one(source, source, "copy", True)
            except ValueError as error:
                if "must not overlap" not in str(error):
                    raise AssertionError(str(error))
            else:
                raise AssertionError("identical-source copy accepted")
        for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
            stdout, stderr = io.StringIO(), io.StringIO()
            args = [str(INSTALLER), "--target-dir", str(root), "--skill", name,
                    "--mode", "symlink", *options]
            with patch.object(sys, "argv", args), \
                    patch.object(installer, "skill_directories", return_value={name: source}), \
                    contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                require(installer.main() == 2, 'installer safeguard assertion failed')
            require(not stdout.getvalue() and 'must not overlap' in stderr.getvalue(), 'installer safeguard assertion failed')
            require((source / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
        if case_alias.exists() and os.path.samefile(source, case_alias):
            with patch.object(installer.tempfile, "mkdtemp", side_effect=AssertionError("staged case alias")):
                for mode in ("copy", "symlink"):
                    try:
                        installer.install_one(source, case_alias, mode, True)
                    except ValueError as error:
                        if "must not overlap" not in str(error):
                            raise AssertionError(str(error))
                    else:
                        raise AssertionError("case alias replaced the source")

        # A leaf symlink may legitimately be replaced by a copy. Its target
        # must remain intact; resolving the leaf would wrongly reject this.
        destination = root / "installed" / name
        destination.parent.mkdir()
        destination.symlink_to(source, target_is_directory=True)
        installer.install_one(source, destination, "copy", True)
        require(not destination.is_symlink(), 'installer safeguard assertion failed')
        require((source / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
        require((destination / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
        safe_alias = root / "outside-checkout-alias"
        safe_alias.symlink_to(root, target_is_directory=True)
        for mode in ("copy", "symlink"):
            safe_destination = root / f"safe-{mode}" / name
            installer.install_one(safe_alias / name, safe_destination, mode, True)
            require((safe_destination / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
            require(safe_alias.is_symlink(), 'installer safeguard assertion failed')
        require(not (source / 'references').exists(), 'installer safeguard assertion failed')
        require(not list(root.rglob('.writing.install-*')), 'installer safeguard assertion failed')



def check_failed_installation_preserves_material() -> None:
    with tempfile.TemporaryDirectory(prefix="plectis-failed-skill-test-") as temp:
        root = Path(temp)
        source = root / "source"
        source.mkdir()
        (source / "SKILL.md").write_bytes(b"new instructions\n")
        name = "public-mathematical-writing"

        def failed_cli(target: Path, fault, *, mode="copy") -> str:
            args = [str(INSTALLER), "--target-dir", str(target), "--skill", name,
                    "--mode", mode, "--force", "--apply"]
            stderr = io.StringIO()
            with patch.object(sys, "argv", args), \
                    patch.object(installer, "skill_directories", return_value={name: source}), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(stderr), fault:
                require(installer.main() == 1, 'installer safeguard assertion failed')
            require(stderr.getvalue().startswith('error:'), stderr.getvalue())
            require('Traceback' not in stderr.getvalue(), 'installer safeguard assertion failed')
            return stderr.getvalue()

        def interrupted_copy(_source, incoming):
            incoming.mkdir()
            (incoming / "SKILL.md").write_bytes(b"partial instructions\n")
            raise OSError("simulated interrupted copy")

        for kind in ("missing", "directory", "file", "symlink"):
            target = root / kind
            target.mkdir()
            destination = target / name
            outside = root / f"outside-{kind}"
            if kind == "directory":
                destination.mkdir()
                (destination / "SKILL.md").write_bytes(b"old instructions\n")
                (destination / "companion.md").write_bytes(b"old companion\n")
            elif kind == "file":
                destination.write_bytes(b"unrelated user file\n")
            elif kind == "symlink":
                outside.mkdir()
                (outside / "SKILL.md").write_bytes(b"outside instructions\n")
                destination.symlink_to(outside, target_is_directory=True)
            failed_cli(target, patch.object(installer.shutil, "copytree", side_effect=interrupted_copy))
            if kind == "missing":
                require(not destination.exists(), 'installer safeguard assertion failed')
            elif kind == "directory":
                require((destination / 'SKILL.md').read_bytes() == b'old instructions\n', 'installer safeguard assertion failed')
                require((destination / 'companion.md').read_bytes() == b'old companion\n', 'installer safeguard assertion failed')
            elif kind == "file":
                require(destination.read_bytes() == b'unrelated user file\n', 'installer safeguard assertion failed')
            else:
                require(destination.is_symlink() and destination.resolve() == outside.resolve(), 'installer safeguard assertion failed')
                require((outside / 'SKILL.md').read_bytes() == b'outside instructions\n', 'installer safeguard assertion failed')
            require(set(target.iterdir()) == (set() if kind == 'missing' else {destination}), 'installer safeguard assertion failed')

        target = root / "promotion"
        destination = target / name
        destination.mkdir(parents=True)
        (destination / "SKILL.md").write_bytes(b"old instructions\n")
        original_replace = os.replace

        def failed_promotion(source_path, target_path):
            if Path(source_path).name == "incoming":
                raise OSError("simulated promotion failure")
            return original_replace(source_path, target_path)

        failed_cli(target, patch.object(installer.os, "replace", side_effect=failed_promotion))
        require((destination / 'SKILL.md').read_bytes() == b'old instructions\n', 'installer safeguard assertion failed')
        require(set(target.iterdir()) == {destination}, 'installer safeguard assertion failed')
        failed_cli(target, patch.object(Path, "symlink_to", side_effect=OSError("cannot create link")),
                   mode="symlink")
        require((destination / 'SKILL.md').read_bytes() == b'old instructions\n', 'installer safeguard assertion failed')
        require(set(target.iterdir()) == {destination}, 'installer safeguard assertion failed')

        readonly = destination / "references"
        readonly.mkdir()
        (readonly / "guide.md").write_bytes(b"old readonly guide\n")
        readonly.chmod(0o555)
        installer.install_one(source, destination, "copy", True)
        require((destination / 'SKILL.md').read_bytes() == b'new instructions\n', 'installer safeguard assertion failed')
        require(set(target.iterdir()) == {destination}, 'installer safeguard assertion failed')

        # A cleanup error after promotion must describe a successful install
        # and the retained staging folder, rather than claim installation failed.
        (destination / "SKILL.md").write_bytes(b"old instructions\n")
        stderr = io.StringIO()
        with patch.object(installer.shutil, "rmtree", side_effect=OSError("cannot clean staging")), \
                contextlib.redirect_stderr(stderr):
            installer.install_one(source, destination, "copy", True)
        require((destination / 'SKILL.md').read_bytes() == b'new instructions\n', 'installer safeguard assertion failed')
        retained = next(target.glob(f".{name}.install-*"))
        require('warning: installed' in stderr.getvalue() and str(retained) in stderr.getvalue(), 'installer safeguard assertion failed')
        installer.shutil.rmtree(retained)
        (destination / "SKILL.md").write_bytes(b"old instructions\n")

        def failed_promotion_and_restore(source_path, target_path):
            if Path(source_path).name in {"incoming", "previous"}:
                raise OSError("simulated unavailable destination")
            return original_replace(source_path, target_path)

        error = failed_cli(target, patch.object(installer.os, "replace", side_effect=failed_promotion_and_restore))
        backup = next(target.glob(f".{name}.install-*/previous"))
        require((backup / 'SKILL.md').read_bytes() == b'old instructions\n', 'installer safeguard assertion failed')
        require(str(backup) in error, 'failed restoration must identify the surviving original')



def check_copied_links_and_complete_tree() -> None:
    """A current copy has independent content at every installed entry."""
    import shutil

    with tempfile.TemporaryDirectory(prefix="plectis-skill-copy-links-") as temp:
        root = Path(temp)
        source = root / "writing"
        source.mkdir()
        original = b"source instructions\n"
        (source / "SKILL.md").write_bytes(original)
        (source / "references").mkdir()
        (source / "references" / "guide.md").write_bytes(b"bundled guide\n")
        # Generic dircmp ignores these names. A copy check must include them.
        (source / "tags").write_bytes(b"source tags\n")
        (source / ".git").mkdir()
        (source / ".git" / "record").write_bytes(b"copied record\n")

        def cli(target, options=(), *, expected=0):
            stdout, stderr = io.StringIO(), io.StringIO()
            args = [str(INSTALLER), "--target-dir", str(target), "--all-clone-skills", *options]
            with patch.object(sys, "argv", args), \
                    patch.object(installer, "skill_directories", return_value={"writing": source}), \
                    contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                actual = installer.main()
            require(actual == expected, (actual, expected, stdout.getvalue(), stderr.getvalue()))
            require('Traceback' not in stderr.getvalue(), 'installer safeguard assertion failed')
            return stdout.getvalue(), stderr.getvalue()

        for kind, relative in (("file", "references/guide.md"),
                               ("directory", "references"),
                               ("dangling", "references/guide.md"),
                               ("recursive", "references"),
                               ("ignored_file", "tags"),
                               ("ignored_directory", ".git")):
            target = root / kind / "installed"
            destination = target / "writing"
            outside = root / kind / "outside"
            shutil.copytree(source, destination)
            shutil.copytree(source, outside)
            entry = destination / relative
            if entry.is_dir():
                shutil.rmtree(entry)
            else:
                entry.unlink()
            link_target = (destination if kind == "recursive" else
                           outside / "missing" if kind == "dangling" else outside / relative)
            entry.symlink_to(link_target, target_is_directory=kind in {
                "directory", "recursive", "ignored_directory",
            })
            link_text = entry.readlink()
            for options, expected in (((), 0), (("--check",), 1), (("--apply",), 1)):
                output, error = cli(target, options, expected=expected)
                require('different' in output, 'installer safeguard assertion failed')
                require(entry.is_symlink() and entry.readlink() == link_text, 'installer safeguard assertion failed')
                require((outside / 'references' / 'guide.md').read_bytes() == b'bundled guide\n', 'installer safeguard assertion failed')
            output, error = cli(target, ("--force", "--apply"))
            require('different' in output and (not error), 'installer safeguard assertion failed')
            require(not entry.is_symlink(), 'installer safeguard assertion failed')
            require((outside / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
            require((outside / 'references' / 'guide.md').read_bytes() == b'bundled guide\n', 'installer safeguard assertion failed')
            require((outside / 'tags').read_bytes() == b'source tags\n', 'installer safeguard assertion failed')
            require((outside / '.git' / 'record').read_bytes() == b'copied record\n', 'installer safeguard assertion failed')
            shutil.rmtree(outside)
            output, error = cli(target, ("--check",))
            require('current' in output and (not error), 'installer safeguard assertion failed')
            require((destination / 'references' / 'guide.md').read_bytes() == b'bundled guide\n', 'installer safeguard assertion failed')
            require((destination / '.git' / 'record').read_bytes() == b'copied record\n', 'installer safeguard assertion failed')
            require(set(target.iterdir()) == {destination}, 'installer safeguard assertion failed')

        target = root / "ignored-drift"
        destination = target / "writing"
        shutil.copytree(source, destination)
        for relative in ("tags", ".git/record"):
            altered = destination / relative
            original_bytes = altered.read_bytes()
            altered.write_bytes(b"changed material\n")
            output, error = cli(target, ("--check",), expected=1)
            require('different' in output, 'installer safeguard assertion failed')
            cli(target, ("--apply",), expected=1)
            require(altered.read_bytes() == b'changed material\n', 'installer safeguard assertion failed')
            cli(target, ("--force", "--apply"))
            require(altered.read_bytes() == original_bytes, 'installer safeguard assertion failed')
        (destination / ".git" / "extra").write_bytes(b"extra material\n")
        cli(target, ("--check",), expected=1)
        cli(target, ("--apply",), expected=1)
        require((destination / '.git' / 'extra').read_bytes() == b'extra material\n', 'installer safeguard assertion failed')
        cli(target, ("--force", "--apply"))
        require(not (destination / '.git' / 'extra').exists(), 'installer safeguard assertion failed')
        require((source / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')

        # Source links are intentionally materialized by copytree; this must
        # remain compatible with rejecting links in the installed copy.
        (source / "guide-link.md").symlink_to(source / "references" / "guide.md")
        (source / "reference-link").symlink_to(source / "references", target_is_directory=True)
        target = root / "materialized-source-links"
        cli(target, ("--apply",))
        destination = target / "writing"
        require(not (destination / 'guide-link.md').is_symlink(), 'installer safeguard assertion failed')
        require(not (destination / 'reference-link').is_symlink(), 'installer safeguard assertion failed')
        require((destination / 'guide-link.md').read_bytes() == b'bundled guide\n', 'installer safeguard assertion failed')
        require((destination / 'reference-link' / 'guide.md').read_bytes() == b'bundled guide\n', 'installer safeguard assertion failed')
        output, error = cli(target, ("--check",))
        require('current' in output and (not error), 'installer safeguard assertion failed')



def check_current_symlink_identity() -> None:
    """An alternate spelling of the same target is current without replacement."""
    with tempfile.TemporaryDirectory(prefix="plectis-skill-link-identity-") as temp:
        root = Path(temp)
        source = root / "Writing"
        source.mkdir()
        original = b"source instructions\n"
        (source / "SKILL.md").write_bytes(original)
        target = root / "installed"
        target.mkdir()
        destination = target / "writing"
        destination.symlink_to(source, target_is_directory=True)
        case_alias = root / "writing"
        real_resolve, real_lstat = Path.resolve, Path.lstat

        def aliased_resolve(path, *args, **kwargs):
            if path == destination:
                return case_alias
            return real_resolve(path, *args, **kwargs)

        def aliased_lstat(path, *args, **kwargs):
            return real_lstat(source if path == case_alias else path, *args, **kwargs)

        def cli(options, *, expected=0, state="current"):
            stdout, stderr = io.StringIO(), io.StringIO()
            args = [str(INSTALLER), "--target-dir", str(target), "--skill", "writing",
                    "--mode", "symlink", *options]
            before = destination.readlink(), destination.lstat().st_ino
            with patch.object(sys, "argv", args), \
                    patch.object(installer, "skill_directories", return_value={"writing": source}), \
                    patch.object(installer.tempfile, "mkdtemp", side_effect=AssertionError("staged current link")), \
                    contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                result = installer.main()
            require(result == expected, (options, result, stdout.getvalue(), stderr.getvalue()))
            require(state in stdout.getvalue(), 'installer safeguard assertion failed')
            if expected == 0:
                require(not stderr.getvalue(), 'installer safeguard assertion failed')
            require(destination.is_symlink(), 'installer safeguard assertion failed')
            require((destination.readlink(), destination.lstat().st_ino) == before, 'installer safeguard assertion failed')
            require((source / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
            require(set(target.iterdir()) == {destination}, 'installer safeguard assertion failed')

        # Simulate the inode behavior on case-sensitive CI as well.
        with patch.object(Path, "resolve", aliased_resolve), \
                patch.object(Path, "lstat", aliased_lstat):
            for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
                cli(options)

        # Replay the actual alias on filesystems that support it.
        if case_alias.exists() and os.path.samefile(source, case_alias):
            destination.unlink()
            destination.symlink_to(case_alias, target_is_directory=True)
            for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
                cli(options)


        # Equal instruction bytes in a different target do not make it current.
        other = root / "Other"
        other.mkdir()
        (other / "SKILL.md").write_bytes(original)
        destination.unlink()
        destination.symlink_to(other, target_is_directory=True)
        for options, expected in (((), 0), (("--check",), 1), (("--apply",), 1)):
            cli(options, expected=expected, state="different")
        installer.install_one(source, destination, "symlink", True)
        require(installer.status(source, destination, 'symlink') == 'current', 'installer safeguard assertion failed')
        require((other / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
        require((source / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')



def check_inspection_failures_and_identity() -> None:
    with tempfile.TemporaryDirectory(prefix="plectis-skill-inspection-") as temp:
        root = Path(temp)
        source = root / "writing"
        source.mkdir()
        original = b"source instructions\n"
        (source / "SKILL.md").write_bytes(original)
        name = "writing"

        def cli(target, options=(), *, mode="copy", expected=0, available=None):
            stdout, stderr = io.StringIO(), io.StringIO()
            args = [str(INSTALLER), "--target-dir", str(target), "--all-clone-skills", "--mode", mode, *options]
            selected = {name: source} if available is None else available
            with patch.object(sys, "argv", args), \
                    patch.object(installer, "skill_directories", return_value=selected), \
                    contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                actual = installer.main()
            require(actual == expected, (actual, expected, stdout.getvalue(), stderr.getvalue()))
            require('Traceback' not in stderr.getvalue(), 'installer safeguard assertion failed')
            return stdout.getvalue(), stderr.getvalue()

        # Identical-source copies are refused without traversing recursive
        # descendants.
        reference = source / "references"
        reference.symlink_to(source, target_is_directory=True)
        for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
            with patch.object(installer.tempfile, "mkdtemp", side_effect=AssertionError("staged identical source")), \
                    patch.object(installer.shutil, "copytree", side_effect=AssertionError("copied identical source")):
                output, error = cli(root, options, expected=2)
                if output or "must not overlap" not in error:
                    raise AssertionError((output, error))
                try:
                    installer.install_one(source, source, "copy", True)
                except ValueError as refused:
                    if "must not overlap" not in str(refused):
                        raise AssertionError(str(refused))
                else:
                    raise AssertionError("direct identical-source copy accepted")
            require(reference.is_symlink() and (source / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
        reference.unlink()
        reference.mkdir()
        (reference / "guide.md").write_bytes(b"source guide\n")

        target = root / "installed"
        destination = target / name
        installer.install_one(source, destination, "copy", False)
        locked = destination / "references"
        # Inject the directory-listing failure so root runners also exercise
        # this boundary. Preserve the user's actual directory permissions.
        previous_mode = locked.stat().st_mode
        locked.chmod(0)
        try:
            for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
                fault = PermissionError(13, "simulated unreadable directory", str(locked))
                with patch.object(installer.filecmp, "dircmp", side_effect=fault):
                    output, error = cli(target, options, expected=1)
                require(not output and 'cannot inspect writing' in error and (str(destination) in error), 'installer safeguard assertion failed')
                require(locked.stat().st_mode == previous_mode & ~511, 'installer safeguard assertion failed')
                require((destination / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
            # On ordinary POSIX user runners, replay the real permission fault.
            try:
                list(locked.iterdir())
            except PermissionError:
                output, error = cli(target, ("--force", "--apply"), expected=1)
                require(not output and 'cannot inspect writing' in error, 'installer safeguard assertion failed')
        finally:
            locked.chmod(previous_mode)
        require((locked / 'guide.md').read_bytes() == b'source guide\n', 'installer safeguard assertion failed')
        require(set(target.iterdir()) == {destination}, 'installer safeguard assertion failed')

        unreadable_file = destination / "SKILL.md"
        original_read = Path.read_bytes

        def failed_read(path):
            if path.resolve() == unreadable_file.resolve():
                raise PermissionError(13, "simulated unreadable file", str(path))
            return original_read(path)

        for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
            with patch.object(Path, "read_bytes", failed_read):
                output, error = cli(target, options, expected=1)
            require(not output and 'cannot inspect writing' in error, 'installer safeguard assertion failed')
            require(unreadable_file.read_bytes() == original, 'installer safeguard assertion failed')
            require((locked / 'guide.md').read_bytes() == b'source guide\n', 'installer safeguard assertion failed')

        for mode in ("copy", "symlink"):
            for kind in ("loop", "dangling"):
                link_target = root / f"{mode}-{kind}"
                link_target.mkdir()
                link = link_target / name
                link.symlink_to(name if kind == "loop" else "absent")
                before = link.readlink()
                for options, expected in (((), 0), (("--check",), 1), (("--apply",), 1)):
                    output, _ = cli(link_target, options, mode=mode, expected=expected)
                    require('different' in output and link.is_symlink() and (link.readlink() == before), 'installer safeguard assertion failed')
                cli(link_target, ("--force", "--apply"), mode=mode)
                cli(link_target, ("--check",), mode=mode)
                require((link / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')
                require((source / 'SKILL.md').read_bytes() == original, 'installer safeguard assertion failed')

        invalid_target = root / "looped-target"
        invalid_target.symlink_to(invalid_target.name)
        for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
            output, error = cli(invalid_target, options, expected=2)
            require(not output and 'error:' in error, 'installer safeguard assertion failed')
            require(invalid_target.is_symlink() and invalid_target.readlink() == Path(invalid_target.name), 'installer safeguard assertion failed')



def main() -> int:
    check_invalid_destination_cli()
    check_companion_installation_default()
    check_overlapping_source_cli()
    check_overlapping_installation_paths()
    check_failed_installation_preserves_material()
    check_copied_links_and_complete_tree()
    check_current_symlink_identity()
    check_inspection_failures_and_identity()
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

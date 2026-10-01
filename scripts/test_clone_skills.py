#!/usr/bin/env python3
"""Test clone-local skill discovery, installation, and first-action routes."""

from __future__ import annotations

import json
import contextlib
import io
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
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
                        assert installer.main() == 2
                    assert not stdout.getvalue(), stdout.getvalue()
                    assert "must not overlap" in stderr.getvalue() and "Traceback" not in stderr.getvalue()
                    assert (selected / "SKILL.md").read_bytes() == original
                    assert (ancestor / "SKILL.md").read_bytes() == b"ancestor material\n"
                    assert parent_alias.is_symlink()
                    assert source_alias.is_symlink()
                    assert checkout_alias.is_symlink()
                    assert chained_alias.is_symlink()
                with patch.object(installer.tempfile, "mkdtemp", side_effect=AssertionError("staged unsafe install")):
                    try:
                        installer.install_one(selected, destination, mode, True)
                    except ValueError as error:
                        assert "must not overlap" in str(error)
                    else:
                        raise AssertionError("direct unsafe installation accepted")

        # The source itself is already a current copy. Replacing it with a
        # symlink would delete the tree and point the installed link at itself.
        with patch.object(installer.tempfile, "mkdtemp", side_effect=AssertionError("staged current copy")):
            installer.install_one(source, source, "copy", True)
        for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
            stdout, stderr = io.StringIO(), io.StringIO()
            args = [str(INSTALLER), "--target-dir", str(root), "--skill", name,
                    "--mode", "symlink", *options]
            with patch.object(sys, "argv", args), \
                    patch.object(installer, "skill_directories", return_value={name: source}), \
                    contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                assert installer.main() == 2
            assert not stdout.getvalue() and "must not overlap" in stderr.getvalue()
            assert (source / "SKILL.md").read_bytes() == original
        if case_alias.exists() and os.path.samefile(source, case_alias):
            with patch.object(installer.tempfile, "mkdtemp", side_effect=AssertionError("staged case alias")):
                installer.install_one(source, case_alias, "copy", True)
                try:
                    installer.install_one(source, case_alias, "symlink", True)
                except ValueError as error:
                    assert "must not overlap" in str(error)
                else:
                    raise AssertionError("case alias replaced the source")

        # A leaf symlink may legitimately be replaced by a copy. Its target
        # must remain intact; resolving the leaf would wrongly reject this.
        destination = root / "installed" / name
        destination.parent.mkdir()
        destination.symlink_to(source, target_is_directory=True)
        installer.install_one(source, destination, "copy", True)
        assert not destination.is_symlink()
        assert (source / "SKILL.md").read_bytes() == original
        assert (destination / "SKILL.md").read_bytes() == original
        safe_alias = root / "outside-checkout-alias"
        safe_alias.symlink_to(root, target_is_directory=True)
        for mode in ("copy", "symlink"):
            safe_destination = root / f"safe-{mode}" / name
            installer.install_one(safe_alias / name, safe_destination, mode, True)
            assert (safe_destination / "SKILL.md").read_bytes() == original
            assert safe_alias.is_symlink()
        assert not (source / "references").exists()
        assert not list(root.rglob(".writing.install-*"))


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
                assert installer.main() == 1
            assert stderr.getvalue().startswith("error:"), stderr.getvalue()
            assert "Traceback" not in stderr.getvalue()
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
                assert not destination.exists()
            elif kind == "directory":
                assert (destination / "SKILL.md").read_bytes() == b"old instructions\n"
                assert (destination / "companion.md").read_bytes() == b"old companion\n"
            elif kind == "file":
                assert destination.read_bytes() == b"unrelated user file\n"
            else:
                assert destination.is_symlink() and destination.resolve() == outside.resolve()
                assert (outside / "SKILL.md").read_bytes() == b"outside instructions\n"
            assert set(target.iterdir()) == (set() if kind == "missing" else {destination})

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
        assert (destination / "SKILL.md").read_bytes() == b"old instructions\n"
        assert set(target.iterdir()) == {destination}
        failed_cli(target, patch.object(Path, "symlink_to", side_effect=OSError("cannot create link")),
                   mode="symlink")
        assert (destination / "SKILL.md").read_bytes() == b"old instructions\n"
        assert set(target.iterdir()) == {destination}

        readonly = destination / "references"
        readonly.mkdir()
        (readonly / "guide.md").write_bytes(b"old readonly guide\n")
        readonly.chmod(0o555)
        installer.install_one(source, destination, "copy", True)
        assert (destination / "SKILL.md").read_bytes() == b"new instructions\n"
        assert set(target.iterdir()) == {destination}

        # A cleanup error after promotion must describe a successful install
        # and the retained staging folder, rather than claim installation failed.
        (destination / "SKILL.md").write_bytes(b"old instructions\n")
        stderr = io.StringIO()
        with patch.object(installer.shutil, "rmtree", side_effect=OSError("cannot clean staging")), \
                contextlib.redirect_stderr(stderr):
            installer.install_one(source, destination, "copy", True)
        assert (destination / "SKILL.md").read_bytes() == b"new instructions\n"
        retained = next(target.glob(f".{name}.install-*"))
        assert "warning: installed" in stderr.getvalue() and str(retained) in stderr.getvalue()
        installer.shutil.rmtree(retained)
        (destination / "SKILL.md").write_bytes(b"old instructions\n")

        def failed_promotion_and_restore(source_path, target_path):
            if Path(source_path).name in {"incoming", "previous"}:
                raise OSError("simulated unavailable destination")
            return original_replace(source_path, target_path)

        error = failed_cli(target, patch.object(installer.os, "replace", side_effect=failed_promotion_and_restore))
        backup = next(target.glob(f".{name}.install-*/previous"))
        assert (backup / "SKILL.md").read_bytes() == b"old instructions\n"
        assert str(backup) in error, "failed restoration must identify the surviving original"


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
            args = [str(INSTALLER), "--target-dir", str(target), "--mode", mode, *options]
            selected = {name: source} if available is None else available
            with patch.object(sys, "argv", args), \
                    patch.object(installer, "skill_directories", return_value=selected), \
                    contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                actual = installer.main()
            assert actual == expected, (actual, expected, stdout.getvalue(), stderr.getvalue())
            assert "Traceback" not in stderr.getvalue()
            return stdout.getvalue(), stderr.getvalue()

        # Physical identity is a current copy without inspecting descendants,
        # even if the source contains a recursive reference.
        reference = source / "references"
        reference.symlink_to(source, target_is_directory=True)
        for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
            with patch.object(installer.tempfile, "mkdtemp", side_effect=AssertionError("staged identical source")), \
                    patch.object(installer.shutil, "copytree", side_effect=AssertionError("copied identical source")):
                output, error = cli(root, options)
                assert "current" in output and not error
                installer.install_one(source, source, "copy", True)
            assert reference.is_symlink() and (source / "SKILL.md").read_bytes() == original
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
                assert not output and "cannot inspect writing" in error and str(destination) in error
                assert locked.stat().st_mode == (previous_mode & ~0o777)
                assert (destination / "SKILL.md").read_bytes() == original
            # On ordinary POSIX user runners, replay the real permission fault.
            try:
                list(locked.iterdir())
            except PermissionError:
                output, error = cli(target, ("--force", "--apply"), expected=1)
                assert not output and "cannot inspect writing" in error
        finally:
            locked.chmod(previous_mode)
        assert (locked / "guide.md").read_bytes() == b"source guide\n"
        assert set(target.iterdir()) == {destination}

        unreadable_file = destination / "SKILL.md"
        original_read = Path.read_bytes

        def failed_read(path):
            if path.resolve() == unreadable_file.resolve():
                raise PermissionError(13, "simulated unreadable file", str(path))
            return original_read(path)

        for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
            with patch.object(Path, "read_bytes", failed_read):
                output, error = cli(target, options, expected=1)
            assert not output and "cannot inspect writing" in error
            assert unreadable_file.read_bytes() == original
            assert (locked / "guide.md").read_bytes() == b"source guide\n"

        for mode in ("copy", "symlink"):
            for kind in ("loop", "dangling"):
                link_target = root / f"{mode}-{kind}"
                link_target.mkdir()
                link = link_target / name
                link.symlink_to(name if kind == "loop" else "absent")
                before = link.readlink()
                for options, expected in (((), 0), (("--check",), 1), (("--apply",), 1)):
                    output, _ = cli(link_target, options, mode=mode, expected=expected)
                    assert "different" in output and link.is_symlink() and link.readlink() == before
                cli(link_target, ("--force", "--apply"), mode=mode)
                cli(link_target, ("--check",), mode=mode)
                assert (link / "SKILL.md").read_bytes() == original
                assert (source / "SKILL.md").read_bytes() == original

        invalid_target = root / "looped-target"
        invalid_target.symlink_to(invalid_target.name)
        for options in ((), ("--check",), ("--apply",), ("--force", "--apply")):
            output, error = cli(invalid_target, options, expected=2)
            assert not output and "error:" in error
            assert invalid_target.is_symlink() and invalid_target.readlink() == Path(invalid_target.name)


def main() -> int:
    check_invalid_destination_cli()
    check_inspection_failures_and_identity()
    check_overlapping_installation_paths()
    check_failed_installation_preserves_material()
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
        "clone skills: discovery, live CLI grammar, preview, copy, symlink, "
        "collision, and routes PASS"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

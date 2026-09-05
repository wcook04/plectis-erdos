#!/usr/bin/env python3
"""Exercise source transport against real Git history and damaged attachments."""
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import source_packet as packet


class SourcePacketTests(unittest.TestCase):
    def test_committed_text_binary_and_offline_verification(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(["git", "-C", directory, *args], stderr=subprocess.DEVNULL)
            git("init")
            (root / "claim.txt").write_text("α claim\nSOURCE {fake delimiter}\n", encoding="utf-8")
            (root / "binary.dat").write_bytes(b"\xff\x00\x80")
            (root / "link").symlink_to("claim.txt")
            git("add", ".")
            git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-m", "sources")
            original = git("rev-parse", "HEAD").decode().strip()
            (root / "claim.txt").write_text("uncommitted replacement")
            (root / "private.txt").write_text("untracked material")
            encoded = packet.build(root, original, ["claim.txt", "binary.dat"], "Inspect the claim", 10000)
            self.assertIn("α claim".encode(), encoded)
            self.assertNotIn(b"uncommitted replacement", encoded)
            with patch.object(packet, "git", side_effect=AssertionError("offline verifier called Git")):
                self.assertEqual(packet.verify(encoded)["source_count"], 2)
            with self.assertRaisesRegex(ValueError, "checksum"):
                packet.verify(encoded.replace(b"claim\n", b"CLAIM\n"))
            with self.assertRaises(ValueError):
                packet.verify(encoded[:-1])
            with self.assertRaises(ValueError):
                packet.verify(encoded + b"extra")
            for path in ("link", "private.txt", "../claim.txt", "/claim.txt"):
                with self.subTest(path=path), self.assertRaises(ValueError):
                    packet.build(root, original, [path], "Inspect", 10000)
            with self.assertRaisesRegex(ValueError, "budget"):
                packet.build(root, original, ["claim.txt"], "Inspect", 10)

    def test_cli_preserves_existing_attachment(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "sent.txt"
            output.write_text("already sent")
            result = subprocess.run(["python3", str(Path(packet.__file__)), "build", "--path", "README.md",
                                     "--question", "Explain", "--output", str(output)], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_text(), "already sent")


if __name__ == "__main__":
    unittest.main()

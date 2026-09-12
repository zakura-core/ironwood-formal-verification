"""Adversarial checks for provenance authentication and the prepared test runner."""

import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from check_zakura_release import (
    MANIFEST, PinnedArchive, VerificationError, read_manifest, sha256,
)
from prepare_zakura_release import RUNNER, build_commands, extract_source


class ReleaseVerificationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def archive(self, members):
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w:gz") as archive:
            for name, data, link in members:
                member = tarfile.TarInfo(name)
                if link is not None:
                    member.type = tarfile.SYMTYPE
                    member.linkname = link
                    archive.addfile(member)
                else:
                    member.size = len(data)
                    member.mode = 0o644
                    archive.addfile(member, io.BytesIO(data))
        data = buffer.getvalue()
        entry = {"file": "source.tar.gz", "prefix": "source", "sha256": sha256(data)}
        (self.root / entry["file"]).write_bytes(data)
        return entry

    def open_archive(self, entry):
        archive = PinnedArchive(entry, self.root)
        self.addCleanup(archive.close)
        return archive

    def test_corruption_rejected_before_archive_parsing(self):
        entry = self.archive([("source/code.rs", b"authenticated", None)])
        (self.root / entry["file"]).write_bytes(b"not even a gzip archive")
        with self.assertRaisesRegex(VerificationError, "checksum mismatch"):
            PinnedArchive(entry, self.root)

    def test_duplicate_archive_members_rejected(self):
        entry = self.archive([
            ("source/code.rs", b"first", None), ("source/code.rs", b"replacement", None),
        ])
        with self.assertRaisesRegex(VerificationError, "duplicate archive member"):
            PinnedArchive(entry, self.root)

    def test_archive_traversal_rejected_without_writing(self):
        entry = self.archive([("source/../outside", b"payload", None)])
        archive = self.open_archive(entry)
        with self.assertRaises(VerificationError):
            extract_source(archive, self.root / "output")
        self.assertFalse((self.root / "output").exists())
        self.assertFalse((self.root / "outside").exists())

    def test_external_link_rejected_without_writing(self):
        entry = self.archive([("source/link", b"", "../../outside")])
        archive = self.open_archive(entry)
        with self.assertRaises(VerificationError):
            extract_source(archive, self.root / "output")
        self.assertFalse((self.root / "output").exists())

    def test_link_cycle_rejected(self):
        entry = self.archive([
            ("source/first", b"", "second"), ("source/second", b"", "first"),
        ])
        archive = self.open_archive(entry)
        with self.assertRaisesRegex(VerificationError, "link cycle"):
            extract_source(archive, self.root / "output")

    def test_internal_license_link_materialized_and_recorded(self):
        entry = self.archive([
            ("source/LICENSE", b"license", None),
            ("source/crates/example/LICENSE", b"", "../../LICENSE"),
        ])
        archive = self.open_archive(entry)
        # The ordinary source reader never follows a link implicitly.
        with self.assertRaisesRegex(VerificationError, "regular archive member"):
            archive.read("crates/example/LICENSE")
        hashes, links = extract_source(archive, self.root / "output")
        target = self.root / "output/crates/example/LICENSE"
        self.assertFalse(target.is_symlink())
        self.assertEqual(target.read_bytes(), b"license")
        self.assertEqual(hashes["LICENSE"], hashes["crates/example/LICENSE"])
        self.assertEqual(links, {"crates/example/LICENSE": "../../LICENSE"})

    def test_manifest_rejects_changed_scope_pins_and_capture(self):
        original = json.loads(MANIFEST.read_text())
        def reject(change):
            manifest = json.loads(json.dumps(original))
            change(manifest)
            path = self.root / "release.json"
            path.write_text(json.dumps(manifest))
            with self.assertRaises(VerificationError):
                read_manifest(path)
        reject(lambda m: m["protocol"].update(automatic_retries=True))
        reject(lambda m: m["protocol"].update(automatic_retries=0))
        reject(lambda m: m["packages"].append(m["packages"][0]))
        reject(lambda m: m["sources"].append(m["sources"][0]))
        reject(lambda m: m["existing_capture"].update(sha256="0" * 64))
        reject(lambda m: m.update(model_endpoint="Unrelated.action_simulation_error_bound"))
        reject(lambda m: m.update(model_endpoint="Zcash.Snark.ZeroKnowledge.Zakura.Unrelated.action_simulation_error_bound"))
        reject(lambda m: m["common"]["archive"].update(url="https://example.org/mutable.tar.gz"))

    def test_prepared_runner_rejects_empty_or_ignored_test_filters(self):
        namespace = {"__name__": "prepared_runner_test"}
        # Defining the runner's functions does not call main or any build command.
        exec(compile(RUNNER, "prepared-runner.py", "exec"), namespace)
        check = namespace["check_test_result"]
        check("test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 12 filtered out;")
        for output in [
            "", "test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 42 filtered out;",
            "test result: ok. 0 passed; 0 failed; 1 ignored;",
            "test result: ok. 2 passed; 0 failed; 0 ignored;",
            "test result: ok. 1 passed; 0 failed; 0 ignored;\n"
            "test result: ok. 1 passed; 0 failed; 0 ignored;",
        ]:
            with self.subTest(output=output), self.assertRaises(RuntimeError):
                check(output)

    def test_fixture_plan_covers_exactly_the_existing_artifacts(self):
        source = self.root / "common"
        fingerprint = source / "crates/orchard/src/circuit/fingerprint/mod.rs"
        fingerprint.parent.mkdir(parents=True)
        fingerprint.write_text("""
fn fingerprint_capture() {}
fn fingerprint_capture_two_actions() {}
fn fingerprint_capture_random() {}
fn fingerprint_capture_random_two_actions() {}
fn fingerprint_capture_random_three_actions() {}
""")
        commands = build_commands(read_manifest(), "aarch64-apple-darwin", source)
        self.assertEqual(len(commands), 5)
        tests = [command for command in commands if command["kind"] == "test"]
        self.assertEqual(len(tests), 4)
        outputs = [output for command in tests for output in command["outputs"]]
        repo = Path(__file__).resolve().parents[1]
        fixture_root = repo / "Zcash/Snark/Fixtures"
        existing = {str(path.relative_to(repo)) for path in fixture_root.rglob("*")
                    if path.is_file() and (path.name == "Fixture.lean" or path.suffix == ".hex")}
        self.assertEqual(len(outputs), len(existing))
        self.assertEqual({output["destination"] for output in outputs}, existing)
        for command in commands:
            self.assertIn("--locked", command["argv"])
            self.assertIn("verifier-fingerprint", command["argv"])
            self.assertEqual(command["environment"]["RAYON_NUM_THREADS"], "1")
        for command in tests:
            self.assertIn("--exact", command["argv"])
            self.assertTrue(all(output["path"].startswith("captures/") for output in command["outputs"]))

        fingerprint.write_text("fn unrelated_test() {}")
        with self.assertRaisesRegex(VerificationError, "capture function absent"):
            build_commands(read_manifest(), "aarch64-apple-darwin", source)


if __name__ == "__main__":
    unittest.main()

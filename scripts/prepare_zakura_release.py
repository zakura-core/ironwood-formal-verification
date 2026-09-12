#!/usr/bin/env python3
"""Prepare existing verifier fixtures from the authenticated Zakura release without building.

The output directory must be new. Run its generated run.py separately to build
and execute the four released capture drivers. Captures never overwrite Lean
fixtures. The regressions suite adds optional backend comparisons.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import posixpath
import re
import tarfile
import tempfile

from check_zakura_release import (
    MANIFEST, REPO, PinnedArchive, VerificationError, read_manifest, relative_path,
    require, sha256, verify_sources,
)


# (package, source path, full Rust module path, test names, requires multicore)
TEST_GROUPS = [
    ("zakura-halo2-proofs", "crates/halo2_proofs/src/plonk/prover.rs", "plonk::prover", [
        "instance_preparation_preserves_proofs_and_validates_batch_first",
        "instance_failures_do_not_run_synthesis_or_consume_rng",
        "v1_proving_key_reuses_floor_plan", "compressed_selector_cache_preserves_proof",
    ], False),
    ("zakura-halo2-proofs", "crates/halo2_proofs/src/plonk/prover.rs", "plonk::prover", [
        "parallel_advice_evaluation_preserves_proof_bytes",
    ], True),
    ("zakura-halo2-proofs", "crates/halo2_proofs/src/plonk/lookup/prover.rs",
     "plonk::lookup::prover::tests", [
        "sorted_lookup_permutation_matches_reference_exhaustively",
        "sorted_lookup_permutation_preserves_output_order",
        "sorted_lookup_permutation_rejects_missing_value",
        "table_sort_matches_field_order", "permuted_pair_commitments_reuse_table_vesta",
    ], False),
    ("zakura-halo2-proofs", "crates/halo2_proofs/src/plonk/lookup/prover.rs",
     "plonk::lookup::prover::tests", ["sorted_u10_commitment_matches_lagrange_vesta"], True),
    ("zakura-halo2-proofs", "crates/halo2_proofs/src/plonk.rs",
     "plonk::prefix_products_of_fractions_tests", [
        "matches_batch_inversion_for_random_nonzero_products",
        "zero_denominators_match_zero_skipping_batch_inversion",
        "zero_denominator_bitmasks_match_zero_skipping_batch_inversion",
        "random_and_full_length_zero_patterns_match_the_reference",
        "zero_numerators_match_the_reference_prefix_chain", "leaves_blinding_rows_untouched",
    ], False),
    ("zakura-halo2-proofs", "crates/halo2_proofs/src/plonk/permutation/prover.rs",
     "plonk::permutation::prover::tests", [
        "identity_product_remains_valid_when_a_shared_factor_is_zero",
    ], True),
    ("zakura-halo2-proofs", "crates/halo2_proofs/src/poly/multiopen/prover.rs",
     "poly::multiopen::prover::tests", [
        "parallel_q_prime_matches_ordered_operator_fold_fp",
        "parallel_evaluations_match_serial_order_fp",
        "zero_challenge_selects_last_polynomial_fp", "in_place_kate_division_matches_allocating_fp",
    ], False),
    ("zakura-halo2-proofs", "crates/halo2_proofs/src/poly/commitment/prover.rs",
     "poly::commitment::prover::tests", [
        "precomputed_evaluation_and_powers_preserve_proof_bytes",
        "compact_b_state_matches_explicit_folds_vesta_base",
        "masking_polynomial_is_sparse_and_commits_correctly_vesta",
        "masking_basis_detects_every_non_evaluation_fold_vesta",
    ], False),
    ("zakura-halo2-proofs", "crates/halo2_proofs/src/poly/commitment/prover.rs",
     "poly::commitment::prover::tests", [
        "prepared_first_round_preserves_unprepared_opening_proof_vesta",
        "prepared_deferred_rounds_preserve_opening_proof_vesta",
        "deferred_materialization_matches_native_vesta", "deferred_ipa_policy_is_limited_to_k_11",
    ], True),
    ("zakura-orchard", "crates/orchard/src/circuit.rs", "circuit::tests", [
        "embedded_orchard_params_match_generation",
        "post_nu6_3_cross_address_restriction_is_conditional",
        "post_nu6_3_restricted_statement_proves_and_verifies",
        "round_trip_post_nu6_3", "post_nu6_3_proof_verifies_only_against_matching_version",
    ], False),
    ("zakura-orchard", "crates/orchard/src/circuit.rs", "circuit::tests", [
        "proof_creation_inside_single_worker_pool",
    ], True),
]

CAPTURES = [
    ("single-honest", "fingerprint_capture", "SINGLE", False, "0x53"),
    ("multi-honest", "fingerprint_capture_two_actions", "MULTI", False, "0x4d"),
    ("single-random", "fingerprint_capture_random", "SINGLE_RANDOM", True, "0x52"),
    ("multi-random", "fingerprint_capture_random_two_actions", "MULTI_RANDOM", True, "0x72"),
    ("triple-random", "fingerprint_capture_random_three_actions", "TRIPLE_RANDOM", True, "0x33"),
]

FIXTURE_DESTINATIONS = {
    "single-honest": "Zcash/Snark/Fixtures/SingleAction/Honest",
    "multi-honest": "Zcash/Snark/Fixtures/MultiAction/Honest",
    "single-random": "Zcash/Snark/Fixtures/SingleAction/Random",
    "multi-random": "Zcash/Snark/Fixtures/MultiAction/Random",
}

PROVER_DESTINATIONS = {
    "single-prover": "Zcash/Snark/Fixtures/Prover/SingleAction.lean",
    "multi-prover": "Zcash/Snark/Fixtures/Prover/MultiAction.lean",
}
PROVER_PIN = REPO / "Zcash/Snark/Fixtures/Prover/producer.json"


def fixture_source(manifest: dict, suite: str) -> dict:
    """Select the released verifier exporter or Common's pinned prover exporter."""
    if suite != "prover-fixtures":
        return manifest["common"]
    source = json.loads(PROVER_PIN.read_text())
    require(source["schema_version"] == 1 and
            source["repository"] == "https://github.com/zakura-core/common", "invalid prover source")
    commit, archive = source["commit"], source["archive"]
    require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None, "prover source needs a full commit")
    require(archive["url"] == f"https://codeload.github.com/zakura-core/common/tar.gz/{commit}" and
            archive["prefix"] == f"common-{commit}" and
            archive["file"] == "common-prover-source.tar.gz" and
            re.fullmatch(r"[0-9a-f]{64}", archive["sha256"]) is not None,
            "prover archive must use its canonical commit and checksum")
    require(source["release_commit"] == manifest["common"]["commit"], "prover release changed")
    require(isinstance(source["release_delta"], dict) and source["release_delta"], "missing release delta")
    return source


def extract_fixture_source(manifest: dict, suite: str, cache: Path, destination: Path) -> tuple[dict, dict]:
    """Authenticate the exporter and its complete delta from the released implementation."""
    source = fixture_source(manifest, suite)
    archive = PinnedArchive(source["archive"], cache)
    try:
        hashes, links = extract_source(archive, destination)
    finally:
        archive.close()
    if suite == "prover-fixtures":
        archive = PinnedArchive(manifest["common"]["archive"], cache)
        try:
            with tempfile.TemporaryDirectory(prefix="prover-release-") as directory:
                released, _ = extract_source(archive, Path(directory) / "common")
        finally:
            archive.close()
        delta = {path: {"release_sha256": released.get(path), "producer_sha256": hashes.get(path)}
                 for path in sorted(set(released) | set(hashes)) if released.get(path) != hashes.get(path)}
        require(delta == source["release_delta"], "prover/release source differences changed")
        require(all(hashes[path] == released[path] for path in ["Cargo.lock", "rust-toolchain.toml"]),
                "prover exporter changed release dependencies")
    return hashes, links


RUNNER = '''#!/usr/bin/env python3
"""Execute this prepared native test plan. This command DOES build Rust."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_test_result(output):
    summaries = re.findall(r"test result: ok\\. (\\d+) passed; (\\d+) failed; (\\d+) ignored;", output)
    if summaries != [("1", "0", "0")]:
        raise RuntimeError("Expected exactly one executed passing test, with no ignored tests")


def main():
    root = Path(__file__).resolve().parent
    plan_path = root / "plan.json"
    plan = json.loads(plan_path.read_text())
    if (root / "results.json").exists():
        raise RuntimeError("Results already exist; prepare a new directory for another run")
    def check_sources():
        for relative, expected in plan["source_files"].items():
            if digest(root / "common" / relative) != expected:
                raise RuntimeError("Prepared source changed: " + relative)
        if digest(root / "release.json") != plan["manifest_sha256"]:
            raise RuntimeError("Prepared release manifest changed")
    check_sources()
    env = os.environ.copy()
    for key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"):
        env.pop(key, None)
    env.update(CARGO_TARGET_DIR=env.get("CARGO_TARGET_DIR", str(root / "target")), CARGO_TERM_COLOR="never")
    report = {"status": "running", "plan_sha256": digest(plan_path), "commands": [],
              "captures": [], "started_unix": time.time(), "lean_built": False,
              "rust_correspondence_proved": False}
    def save():
        (root / "results.json").write_text(json.dumps(report, indent=2) + "\\n")
    save()
    try:
        version = subprocess.run(["rustc", "+" + plan["toolchain"], "-vV"], env=env,
                                 check=True, capture_output=True, text=True).stdout
        (root / "rustc.txt").write_text(version)
        if "host: " + plan["target"] + "\\n" not in version:
            raise RuntimeError("Run on the named native target; cross-compilation is not a test run")
        for i, command in enumerate(plan["commands"]):
            print(f'[{i + 1}/{len(plan["commands"])}] {command["label"]}', flush=True)
            run_env = env | command["environment"]
            for output in command["outputs"]:
                path = root / output["path"]
                if path.exists():
                    raise RuntimeError("Refusing to reuse an existing capture: " + str(path))
                path.parent.mkdir(parents=True, exist_ok=True)
            # Only output-path variables use the prepared directory; do not log unrelated environment.
            for key in command["output_variables"]:
                run_env[key] = str(root / run_env[key])
            log_path = root / f"command-{i:03d}.log"
            with log_path.open("w") as log:
                result = subprocess.run(command["argv"], cwd=root / "common", env=run_env,
                                        stdout=log, stderr=subprocess.STDOUT)
            record = {"label": command["label"], "argv": command["argv"],
                      "environment": command["environment"],
                      "returncode": result.returncode,
                      "log": log_path.name, "log_sha256": digest(log_path)}
            report["commands"].append(record)
            save()
            if result.returncode:
                raise RuntimeError("Command failed; see " + str(log_path))
            if command["kind"] == "test":
                check_test_result(log_path.read_text(errors="replace"))
            for output in command["outputs"]:
                path = root / output["path"]
                if not path.is_file() or not path.stat().st_size:
                    raise RuntimeError("Missing or empty capture: " + str(path))
                report["captures"].append(output | {"sha256": digest(path)})
        check_sources()
        comparisons = {}
        for capture in report["captures"]:
            comparisons.setdefault(capture["comparison"], set()).add(capture["sha256"])
        if any(len(hashes) != 1 for hashes in comparisons.values()):
            raise RuntimeError("Seeded captures differ across profiles; inspect the recorded artifacts")
        report["capture_profiles_equal"] = True
        report["status"] = "passed"
    except BaseException as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        report["finished_unix"] = time.time()
        save()


if __name__ == "__main__":
    main()
'''


def extract_source(archive: PinnedArchive, destination: Path) -> tuple[dict, dict]:
    """Materialize authenticated files and internal file links into a new tree."""
    prefix = relative_path(archive.entry["prefix"])
    files = []
    links = {}
    def contents(member, seen):
        require(member.name not in seen, f"archive link cycle: {member.name}")
        seen = seen | {member.name}
        if member.issym() or member.islnk():
            target = member.linkname
            if member.issym():
                target = posixpath.join(posixpath.dirname(member.name), target)
            path = relative_path(posixpath.normpath(target))
            require(path.is_relative_to(prefix), f"archive link outside source root: {member.name}")
            return contents(archive.archive.getmember(str(path)), seen)
        require(member.isfile(), f"expected regular archive target: {member.name}")
        relative = relative_path(member.name).relative_to(prefix)
        return archive.read(str(relative)), member.mode & 0o777
    for member in archive.archive.getmembers():
        path = relative_path(member.name)
        require(path.is_relative_to(prefix), f"archive member outside source root: {path}")
        relative = path.relative_to(prefix)
        if member.isdir():
            continue
        require(bool(relative.parts), f"unsupported archive member: {path}")
        if member.issym() or member.islnk():
            links[str(relative)] = member.linkname
        data, mode = contents(member, set())
        files.append((relative, data, mode))
    destination.mkdir()
    hashes = {}
    for relative, data, mode in files:
        path = destination / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as output:
            output.write(data)
        path.chmod(mode)
        hashes[str(relative)] = sha256(data)
    return hashes, links


def build_commands(manifest: dict, target: str, source: Path, *, suite: str = "fixtures") -> list[dict]:
    """Capture the existing families; backend/profile regressions are an optional suite."""
    require(suite in {"fixtures", "prover-fixtures", "regressions"}, "unknown release validation suite")
    if suite == "prover-fixtures":
        package = ["--locked", "--target", target, "-p", "zakura-orchard", "--features", "prover-fingerprint"]
        prefix = ["cargo", "+" + manifest["common"]["toolchain"]]
        commands = [{"kind": "features", "label": "prover/features",
                     "argv": prefix + ["tree"] + package + ["-e", "features"],
                     "environment": {"RAYON_NUM_THREADS": "1"}, "outputs": [], "output_variables": []}]
        rust = (source / "crates/orchard/src/circuit/prover_fingerprint.rs").read_text()
        for name, test, variable, seed in [
                ("single-prover", "prover_capture", "SINGLE", "0x53"),
                ("multi-prover", "prover_capture_two_actions", "MULTI", "0x4d")]:
            require(re.search(rf"\bfn {test}\s*\(", rust) is not None, "missing prover export driver")
            output = f"captures/{name}.lean"
            key = f"ORCHARD_LEAN_{variable}_PROVER_OUT"
            commands.append({"kind": "test", "label": "prover/" + name,
                "argv": prefix + ["test"] + package + ["--release", "--lib",
                    "circuit::prover_fingerprint::" + test, "--", "--exact", "--nocapture", "--test-threads=1"],
                "environment": {"RAYON_NUM_THREADS": "1", key: output}, "output_variables": [key],
                "outputs": [{"path": output, "comparison": name + "/fixture", "seed_byte": seed,
                             "destination": PROVER_DESTINATIONS[name]}]})
        return commands
    profiles = manifest["profiles"]
    if suite == "fixtures":
        defaults = [profile for profile in profiles if profile["id"] == "default"]
        require(len(defaults) == 1 and not defaults[0]["no_default_features"],
                "fixture capture requires the default release profile")
        profiles = [defaults[0] | {"threads": [1]}]
    commands = []
    for profile in profiles:
        for threads in profile["threads"]:
            label = f"{profile['id']}-threads-{threads}"
            def args(package, capture=False):
                result = ["--locked", "--target", target, "-p", package]
                if profile["no_default_features"]:
                    result.append("--no-default-features")
                features = list(profile.get("features_by_package", {}).get(package, []))
                if package == "zakura-halo2-proofs" and "floor-planner-v1-legacy-pdqsort" not in features:
                    features.append("floor-planner-v1-legacy-pdqsort")
                if capture:
                    features.append("verifier-fingerprint")
                if features:
                    result += ["--features", ",".join(features)]
                return result
            def add(kind, name, package, extra, capture=False, outputs=None, variables=None):
                command = ["cargo", "+" + manifest["common"]["toolchain"],
                           "test" if kind == "test" else "tree"]
                command += args(package, capture) + extra
                variables = variables or {}
                commands.append({
                    "kind": kind, "label": label + "/" + name, "argv": command,
                    "environment": {"RAYON_NUM_THREADS": str(threads), **variables},
                    "outputs": outputs or [], "output_variables": list(variables),
                })
            if suite == "fixtures":
                add("features", "zakura-orchard", "zakura-orchard", ["-e", "features"], capture=True)
            else:
                for package in ("zakura-halo2-proofs", "zakura-orchard"):
                    add("features", package, package, ["-e", "features"])
            for package, path, module, names, multicore in TEST_GROUPS if suite == "regressions" else []:
                if multicore and profile["no_default_features"]:
                    continue
                rust = (source / path).read_text()
                for name in names:
                    require(re.search(rf"\bfn {name}\s*\(", rust) is not None,
                            f"test function absent from pinned source: {name}")
                    add("test", name, package,
                        ["--release", "--lib", module + "::" + name, "--",
                         "--exact", "--nocapture", "--test-threads=1"])
            fingerprint = (source / "crates/orchard/src/circuit/fingerprint/mod.rs").read_text()
            for name, test, variable, random, seed in CAPTURES:
                destination = FIXTURE_DESTINATIONS.get(name)
                if suite == "fixtures" and destination is None:
                    continue
                require(re.search(rf"\bfn {test}\s*\(", fingerprint) is not None,
                        f"capture function absent from pinned source: {test}")
                output = f"captures/{label}/{name}/Fixture.lean"
                variables = {f"ORCHARD_LEAN_{variable}_FIXTURE_OUT": output}
                outputs = [{"path": output, "comparison": name + "/fixture", "seed_byte": seed}]
                if destination is not None:
                    outputs[0]["destination"] = destination + "/Fixture.lean"
                if random:
                    proof = f"captures/{label}/{name}/proof.hex"
                    variables[f"ORCHARD_LEAN_{variable}_PROOF_OUT"] = proof
                    outputs.append({"path": proof, "comparison": name + "/proof", "seed_byte": seed})
                    if destination is not None:
                        outputs[-1]["destination"] = destination + "/proof-bytes.hex"
                add("test", name, "zakura-orchard",
                    ["--release", "--lib", "circuit::fingerprint::" + test, "--",
                     "--exact", "--nocapture", "--test-threads=1"],
                    capture=True, outputs=outputs, variables=variables)
    return commands


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--suite", choices=["fixtures", "prover-fixtures", "regressions"], default="fixtures",
                        help="select verifier fixtures, prover fixtures, or optional backend regressions")
    parser.add_argument("--target", required=True, choices=[
        "x86_64-unknown-linux-gnu", "aarch64-apple-darwin", "aarch64-unknown-linux-gnu"])
    args = parser.parse_args()
    try:
        manifest = read_manifest()
        evidence = verify_sources(manifest, args.cache_dir)
        require(not args.output_dir.exists(), "output directory must be new")
        args.output_dir.mkdir(parents=True)
        hashes, links = extract_fixture_source(manifest, args.suite, args.cache_dir, args.output_dir / "common")
        commands = build_commands(manifest, args.target, args.output_dir / "common", suite=args.suite)
        plan = {"status": "prepared_not_executed", "target": args.target,
                "suite": args.suite,
                "toolchain": manifest["common"]["toolchain"], "release": manifest["target"],
                "manifest_sha256": sha256(MANIFEST.read_bytes()),
                "source_evidence": evidence, "source_files": hashes,
                "materialized_source_links": links, "commands": commands}
        if args.suite == "prover-fixtures":
            plan["producer_sha256"] = sha256(PROVER_PIN.read_bytes())
        (args.output_dir / "plan.json").write_text(json.dumps(plan, indent=2) + "\n")
        (args.output_dir / "release.json").write_bytes(MANIFEST.read_bytes())
        (args.output_dir / "run.py").write_text(RUNNER)
        print(f"Prepared {len(commands)} commands in {args.output_dir}; no Rust or Lean command was run.")
    except (VerificationError, OSError, KeyError, ValueError, tarfile.TarError) as error:
        parser.exit(1, f"preparation failed: {error}\n")


if __name__ == "__main__":
    main()

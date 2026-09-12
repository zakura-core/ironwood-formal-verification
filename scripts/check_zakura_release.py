#!/usr/bin/env python3
"""Check the Zakura prover target without compiling or executing Rust or Lean.

With no cache argument this checks the manifest and its local capture pin.
With --cache-dir it also authenticates source archives and compares public data.
--fetch explicitly permits downloading missing pinned archives into that cache.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile
import tempfile
import tomllib
from urllib.request import urlopen


REPO = Path(__file__).resolve().parent.parent
MANIFEST = REPO / "Zcash/Snark/ZeroKnowledge/Zakura/release.json"
REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"


class VerificationError(ValueError):
    """A pinned input or a claimed equality failed validation."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def relative_path(value: str) -> PurePosixPath:
    path = PurePosixPath(value)
    require(bool(value) and not path.is_absolute() and ".." not in path.parts,
            f"invalid relative path: {value!r}")
    return path


def archives(manifest: dict) -> list[dict]:
    return [manifest["zakura"]["archive"], manifest["common"]["archive"]] + [
        package["archive"] for package in manifest["packages"]
    ]


def read_manifest(path: Path = MANIFEST, repo: Path = REPO) -> dict:
    manifest = json.loads(path.read_text())
    require(manifest["schema_version"] == 1, "unsupported release manifest schema")
    for name in ("zakura", "common"):
        source = manifest[name]
        require(re.fullmatch(r"[0-9a-f]{40}", source["commit"]) is not None,
                f"{name}: a full commit is required")
        require(source["repository"] == f"https://github.com/zakura-core/{name}",
                f"{name}: unexpected source repository")
        require(source["archive"]["url"] ==
                f"https://codeload.github.com/zakura-core/{name}/tar.gz/{source['commit']}",
                f"{name}: archive URL must use the recorded commit")
        require(source["archive"]["prefix"] == f"{name}-{source['commit']}",
                f"{name}: archive root must use the recorded commit")
    packages = manifest["packages"]
    names = [package["name"] for package in packages]
    require(sorted(names) == ["zakura-halo2-gadgets", "zakura-halo2-legacy-pdqsort",
                             "zakura-halo2-proofs", "zakura-orchard", "zakura-pasta-curves"],
            "the five circuit/prover package pins must appear exactly once")
    for package in packages:
        stem = f"{package['name']}-{package['version']}"
        require(package["archive"]["url"] ==
                f"https://static.crates.io/crates/{package['name']}/{stem}.crate",
                f"{stem}: unexpected package URL")
        require(package["archive"]["prefix"] == stem, f"{stem}: unexpected package root")
        relative_path(package["path"])
    entries = archives(manifest)
    require(len({entry["file"] for entry in entries}) == len(entries), "duplicate archive filename")
    for entry in entries:
        require(relative_path(entry["file"]).name == entry["file"], "archive filenames must be basenames")
        require(re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]) is not None, "invalid archive checksum")
    source_paths = [entry["path"] for entry in manifest["sources"]]
    require(len(set(source_paths)) == len(source_paths) and source_paths, "duplicate or missing source pins")
    for entry in manifest["sources"]:
        relative_path(entry["path"])
        require(re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]) is not None, "invalid source checksum")
    protocol = manifest["protocol"]
    require(protocol["automatic_retries"] is False, "release call must have automatic_retries=false")
    require((protocol["circuit"], protocol["k"], protocol["instance_rows"],
             protocol["words_per_field_sample"], protocol["automatic_retries"]) ==
            ("PostNu6_3", 11, 10, 8, False), "manifest changes the reviewed protocol profile")
    require(protocol["private_field_samples"] == {"per_action": 148, "constant": 46},
            "manifest changes the reviewed private randomness schedule")
    capture = manifest["existing_capture"]
    capture_path = repo / relative_path(capture["path"])
    require(sha256(capture_path.read_bytes()) == capture["sha256"], "existing Lean capture changed")
    require(manifest["model_endpoint"] ==
            "Zcash.Snark.ZeroKnowledge.Zakura.action_simulation_error_bound",
            "model endpoint must name the released-call observation theorem exactly")
    endpoint = manifest["model_endpoint"].rsplit(".", 1)[1]
    action = repo / "Zcash/Snark/ZeroKnowledge/Zakura/Action.lean"
    require(re.search(rf"^theorem {re.escape(endpoint)}\b", action.read_text(), re.M) is not None,
            "recorded model endpoint is missing")
    return manifest


class PinnedArchive:
    """Read regular members only after authenticating the complete archive."""

    def __init__(self, entry: dict, cache: Path, fetch: bool = False):
        self.entry = entry
        self.path = cache / entry["file"]
        if not self.path.exists() and fetch:
            cache.mkdir(parents=True, exist_ok=True)
            with urlopen(entry["url"], timeout=60) as response:
                require(response.geturl().startswith("https://"), "download redirected away from HTTPS")
                data = response.read()
            require(sha256(data) == entry["sha256"], f"download checksum mismatch: {entry['file']}")
            with tempfile.NamedTemporaryFile(dir=cache, delete=False) as temporary:
                temporary.write(data)
                temporary_path = Path(temporary.name)
            temporary_path.replace(self.path)
        require(self.path.is_file(), f"missing archive: {self.path}; use --fetch to download")
        data = self.path.read_bytes()
        require(sha256(data) == entry["sha256"], f"archive checksum mismatch: {self.path}")
        self.archive = tarfile.open(fileobj=io.BytesIO(data), mode="r:gz")
        members = self.archive.getmembers()
        require(len({member.name for member in members}) == len(members), "duplicate archive member")

    def read(self, path: str) -> bytes:
        member = self.archive.getmember(f"{self.entry['prefix']}/{relative_path(path)}")
        require(member.isfile(), f"expected regular archive member: {member.name}")
        stream = self.archive.extractfile(member)
        require(stream is not None, f"unreadable archive member: {member.name}")
        return stream.read()

    def close(self) -> None:
        self.archive.close()


def lock_entry(lock: dict, name: str, version: str) -> dict:
    entries = [package for package in lock["package"]
               if package["name"] == name and package["version"] == version]
    require(len(entries) == 1, f"lockfile must resolve {name} {version} exactly once")
    return entries[0]


def capture_points(source: str) -> list[tuple[int, int]]:
    lines = [line for line in source.splitlines() if line.startswith("def capturedPointCoordinates :")]
    require(len(lines) == 1, "capture must contain one coordinate list")
    limb_vectors = re.findall(r"\(mkFq (\d+) (\d+) (\d+) (\d+)\)", lines[0])
    require(bool(limb_vectors) and len(limb_vectors) % 2 == 0, "incomplete captured coordinates")
    values = [sum(int(limb) << (64 * i) for i, limb in enumerate(vector)) for vector in limb_vectors]
    return list(zip(values[::2], values[1::2]))


def capture_indices(source: str, name: str) -> list[int]:
    lines = [line for line in source.splitlines() if line.startswith(f"def {name} :")]
    require(len(lines) == 1, f"capture must contain exactly one {name}")
    return [int(index) for index in re.findall(r"capturedPoint (\d+)", lines[0])]


def compare_public_artifacts(common: PinnedArchive, manifest: dict, repo: Path = REPO) -> dict:
    source = (repo / manifest["existing_capture"]["path"]).read_text()
    require('def capturedCircuitId : String := "PostNu6_3"' in source, "capture uses another circuit")
    points = capture_points(source)
    modulus_match = re.search(r"q = (0x[0-9a-f]+)",
                              common.read("crates/pasta_curves/src/fields/fq.rs").decode())
    require(modulus_match is not None, "missing released Vesta base-field modulus")
    modulus = int(modulus_match.group(1), 16)

    def encode(point: tuple[int, int]) -> bytes:
        x, y = point
        require(0 <= x < modulus and 0 <= y < modulus, "noncanonical captured coordinate")
        require((y * y - x * x * x - 5) % modulus == 0, "captured point is not on Vesta")
        return (x | ((y & 1) << 255)).to_bytes(32, "little")

    params = common.read("crates/orchard/src/circuit_data/orchard_k11_params.bin")
    k = int.from_bytes(params[:4], "little")
    require(k == manifest["protocol"]["k"], "embedded parameters have the wrong exponent")
    n = 1 << k
    require(len(params) == 4 + (2 * n + 2) * 32, "embedded parameter length is incorrect")
    indices = capture_indices(source, "capturedUrsG")
    require(len(indices) == n, "captured coefficient basis is incomplete")
    for i, index in enumerate(indices):
        require(encode(points[index]) == params[4 + i * 32:4 + (i + 1) * 32],
                f"coefficient generator {i} differs")
    urs = re.search(r"^def capturedURS .*?w := capturedPoint (\d+), u := capturedPoint (\d+)", source, re.M)
    require(urs is not None, "missing captured W/U routing")
    for offset, index in enumerate(map(int, urs.groups())):
        require(encode(points[index]) == params[4 + (2 * n + offset) * 32:4 + (2 * n + offset + 1) * 32],
                f"embedded {'W' if offset == 0 else 'U'} differs")
    description = common.read("crates/orchard/src/circuit_data/circuit_description_post_nu6_3").decode()
    blocks = {
        "fixed_commitments": (description.split("    fixed_commitments: [", 1)[1].split("    ],", 1)[0],
                              "capturedFixedCommitments", 29),
        "permutation_commitments": (description.split("    permutation: VerifyingKey {", 1)[1],
                                    "capturedPermutationCommonCommitments", 15),
    }
    counts = {}
    for label, (block, captured_name, expected) in blocks.items():
        actual = [(int(x, 16), int(y, 16))
                  for x, y in re.findall(r"\((0x[0-9a-f]+), (0x[0-9a-f]+)\)", block)]
        captured = [points[index] for index in capture_indices(source, captured_name)]
        require(len(actual) == expected and actual == captured, f"stored {label} differ")
        counts[label] = len(actual)
    result = {"coefficient_generators": n, "blinding_generator_w": True, "ipa_generator_u": True, **counts}
    require(result == manifest["existing_capture"]["comparison"], "artifact comparison counts changed")
    return result


def verify_sources(manifest: dict, cache: Path, fetch: bool = False, repo: Path = REPO) -> dict:
    opened = []
    try:
        def open_archive(entry):
            archive = PinnedArchive(entry, cache, fetch)
            opened.append(archive)
            return archive

        zakura = open_archive(manifest["zakura"]["archive"])
        common = open_archive(manifest["common"]["archive"])
        locks = {}
        for name, archive in (("zakura", zakura), ("common", common)):
            data = archive.read("Cargo.lock")
            require(sha256(data) == manifest[name]["lockfile_sha256"], f"{name}: lockfile checksum mismatch")
            locks[name] = tomllib.loads(data.decode())
        toolchain = tomllib.loads(common.read("rust-toolchain.toml").decode())["toolchain"]["channel"]
        require(toolchain == manifest["common"]["toolchain"], "Common toolchain pin differs")
        sources = {entry["path"]: entry["sha256"] for entry in manifest["sources"]}
        for path, digest in sources.items():
            require(sha256(common.read(path)) == digest, f"inspected source checksum mismatch: {path}")
        packages = []
        for package in manifest["packages"]:
            entry = lock_entry(locks["zakura"], package["name"], package["version"])
            require(entry.get("source") == REGISTRY and entry.get("checksum") == package["archive"]["sha256"],
                    f"{package['name']}: release lockfile does not authenticate the published archive")
            published = open_archive(package["archive"])
            vcs = json.loads(published.read(".cargo_vcs_info.json"))
            require(vcs["git"]["sha1"] == manifest["common"]["commit"] and not vcs["git"].get("dirty", False),
                    f"{package['name']}: published VCS revision differs or is dirty")
            require(vcs["path_in_vcs"] == package["path"], f"{package['name']}: package path differs")
            package_manifest = tomllib.loads(published.read("Cargo.toml").decode())["package"]
            require((package_manifest["name"], package_manifest["version"]) ==
                    (package["name"], package["version"]), "published package identity differs")
            # Cargo normalizes manifests when publishing; compare the original
            # manifest and every inspected source/artifact belonging to the package.
            require(published.read("Cargo.toml.orig") == common.read(f"{package['path']}/Cargo.toml"),
                    f"{package['name']}: original published manifest differs from the commit")
            prefix = package["path"] + "/"
            for path in sources:
                if path.startswith(prefix) and path != prefix + "Cargo.toml":
                    require(published.read(path[len(prefix):]) == common.read(path),
                            f"published source differs from Common: {path}")
            packages.append(package["name"])
        for dependency in manifest["shared_dependencies"]:
            for name, lock in locks.items():
                entry = lock_entry(lock, dependency["name"], dependency["version"])
                require(entry.get("source") == REGISTRY and entry.get("checksum") == dependency["checksum"],
                        f"{name}: shared dependency {dependency['name']} differs")
        return {"target": manifest["target"], "common_commit": manifest["common"]["commit"],
                "verified_packages": packages, "verified_source_files": len(sources),
                "public_artifacts": compare_public_artifacts(common, manifest, repo),
                "builds_run": False, "rust_correspondence_proved": False,
                "limitations": manifest["existing_capture"]["limitations"]}
    finally:
        for archive in opened:
            archive.close()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=MANIFEST)
    parser.add_argument("--cache-dir", type=Path)
    parser.add_argument("--fetch", action="store_true")
    parser.add_argument("--output", type=Path, help="write the check result as JSON")
    args = parser.parse_args()
    if args.fetch and args.cache_dir is None:
        parser.error("--fetch requires --cache-dir")
    try:
        manifest = read_manifest(args.manifest)
        result = verify_sources(manifest, args.cache_dir, args.fetch) if args.cache_dir else {
            "target": manifest["target"], "manifest_and_local_capture": "checked",
            "external_sources_checked": False, "builds_run": False,
        }
        encoded = json.dumps(result, indent=2) + "\n"
        if args.output:
            args.output.write_text(encoded)
        print(encoded, end="")
    except (VerificationError, OSError, KeyError, IndexError, ValueError, tarfile.TarError) as error:
        print(f"release check failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()

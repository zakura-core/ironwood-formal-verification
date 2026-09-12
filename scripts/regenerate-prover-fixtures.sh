#!/usr/bin/env bash
# Copy Common's pinned Rust-exported prover Lean fixtures and enforce exact regeneration.
# The shared driver authenticates the producer, runs its two capture tests, and
# compares their outputs. --update copies the complete files and updates MANIFEST.tsv.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/regenerate_fingerprint_fixtures.py --prover "$@"

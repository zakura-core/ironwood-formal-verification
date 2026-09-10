#!/usr/bin/env bash
# Regenerate the six existing verifier-fingerprint artifacts from the pinned
# Zakura release. --check-set performs local inventory checks only; --from-run
# checks completed captures without running Rust. --update installs generated
# files and updates their provenance together. See Fixtures/PROVENANCE.md.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/regenerate_fingerprint_fixtures.py "$@"

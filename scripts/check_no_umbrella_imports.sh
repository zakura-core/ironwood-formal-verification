#!/usr/bin/env bash
# Check that no Lean file imports the Mathlib umbrella modules.
#
# `import Mathlib` pulls in all of Mathlib, which peaks around 6.5 GB RSS per Lean process.
# During a parallel Lake build several such processes create severe memory and GC pressure —
# one observed `PermutationInstantiation` build took 648 seconds despite compiling in about
# five seconds in isolation. PR #144 replaced every umbrella import with `Mathlib.Tactic` or
# narrower module imports.
#
# `import Mathlib.Tactic` is the same failure mode at smaller scale: it transitively pulls a
# large slice of Mathlib's theory (measured for issue #153 at roughly +1.6 s import-load time
# and +1.3 GB RSS per Lean process against the narrow tactic modules a file actually needs).
# It was the accepted broad-import compromise until issue #153 swept the last 83 uses; the
# sweep holds only if the umbrella cannot creep back in, since nothing else fails when it
# does — builds just quietly get slow again.
#
# The rule: no tracked or unignored new `.lean` file may contain a bare `import Mathlib` or a bare
# `import Mathlib.Tactic` (with or without a trailing comment). Specific submodule imports
# such as `import Mathlib.Tactic.Ring` are fine. If an umbrella import is ever legitimately
# needed, extend this script with an explicit allowlist rather than deleting the check.
#
# Run from the repository root; exits non-zero on violation.
set -euo pipefail

# One-or-more whitespace after `import` (not exactly one space), and optional
# `public`/`meta` modifiers, so spacing variants and module-system prefixes
# cannot slip a banned umbrella past the anchor.
python3 - <<'PY'
import os
from pathlib import Path
import re
import subprocess

paths = subprocess.check_output([
    "git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "--", "*.lean",
]).split(b"\0")
pattern = re.compile(r"^(public\s+)?(meta\s+)?import\s+Mathlib(\.Tactic)?(\s|$)")
violations = []
for raw in sorted(set(paths) - {b""}):
    path = Path(os.fsdecode(raw))
    try:
        lines = path.read_text().splitlines()
    except FileNotFoundError:
        # Unstaged deletions remain in the index but have no source to inspect.
        continue
    violations.extend(f"{path}:{number}:{line}" for number, line in enumerate(lines, 1)
                      if pattern.search(line))
if violations:
    print("::error::bare 'import Mathlib' / 'import Mathlib.Tactic' umbrella imports are not allowed; "
          "import the specific Mathlib modules instead (see scripts/check_no_umbrella_imports.sh):")
    print("\n".join(violations))
    raise SystemExit(1)
PY

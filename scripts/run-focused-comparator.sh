#!/usr/bin/env bash
set -euo pipefail
: "${ENTRY:?Expected focused entry}" "${EXPECTED_COMMIT:?Expected immutable checkout}" "${RUNNER_TEMP:?Runner scratch root}"
mkdir -p artifacts
export GOTOOLCHAIN=local
export COMPARATOR_LEAN4EXPORT="$RUNNER_TEMP/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_NANODA="$RUNNER_TEMP/nanoda/target/release/nanoda_bin"
export PALOMAR_LANDRUN_BIN="$RUNNER_TEMP/landrun"
export COMPARATOR_LANDRUN="$PWD/scripts/landrun-wrapper.sh"
comparator="$RUNNER_TEMP/comparator/.lake/build/bin/comparator"
test "$(git rev-parse HEAD)" = "$EXPECTED_COMMIT"
python3 - <<'SNAPSHOT'
import json, subprocess
from pathlib import Path
result = subprocess.run(['git', 'diff', '--name-only', '-z', 'HEAD', '--'], capture_output=True)
paths = [p.decode('utf-8', errors='surrogateescape') for p in result.stdout.split(b'\0') if p]
receipt = {'phase': 'pre_replay', 'git_exit': result.returncode, 'tracked_dirty_paths': paths,
           'matches_commit': result.returncode == 0 and not paths}
Path('artifacts/source-preflight.json').write_text(json.dumps(receipt, indent=2) + '\n')
if not receipt['matches_commit']:
    print(json.dumps(receipt))
    raise SystemExit(76)
SNAPSHOT
test "$(tr -d '[:space:]' < lean-toolchain)" = "$(tr -d '[:space:]' < "$RUNNER_TEMP/lean4export/lean-toolchain")"
for bin in "$comparator" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_NANODA" "$PALOMAR_LANDRUN_BIN" "$COMPARATOR_LANDRUN"; do
  if ! test -x "$bin"; then
    echo "Focused Comparator executable missing or not executable: $bin" >&2
    exit 126
  fi
done
if systemd-run --user --property=RestrictAddressFamilies=AF_UNIX --wait --collect --pipe -- true > artifacts/systemd.log 2>&1; then
  manager=(systemd-run --user)
  export SANDBOX_MODE=user-manager
elif sudo -n systemd-run --uid="$(id -un)" --gid="$(id -gn)" --property=RestrictAddressFamilies=AF_UNIX --wait --collect --pipe -- true >> artifacts/systemd.log 2>&1; then
  manager=(sudo -n systemd-run --uid="$(id -un)" --gid="$(id -gn)")
  export SANDBOX_MODE=system-manager-nonprivileged-unit
else
  echo 'No supported systemd boundary; no Comparator verdict.' >&2
  exit 75
fi
run_one() {
  timeout 20m "${manager[@]}" --property=RestrictAddressFamilies=AF_UNIX --wait --collect --pipe \
    -E "PATH=$PATH" -E "GOTOOLCHAIN=$GOTOOLCHAIN" \
    -E "COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" -E "COMPARATOR_NANODA=$COMPARATOR_NANODA" \
    -E "PALOMAR_LANDRUN_BIN=$PALOMAR_LANDRUN_BIN" -E "COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" \
    --working-directory="$PWD" -- bash -c 'exec lake env "$1" "$2"' comparator-replay "$comparator" "$1"
}
set +e
run_one "$ENTRY/comparator.json" > artifacts/positive.log 2>&1
positive=$?
run_one "$ENTRY/comparator-negative-mismatch.json" > artifacts/negative.log 2>&1
negative=$?
set -e
python3 scripts/record_focused_comparator.py --entry "$ENTRY" --expected-commit "$EXPECTED_COMMIT" \
  --positive-exit "$positive" --negative-exit "$negative"

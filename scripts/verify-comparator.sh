#!/usr/bin/env bash
set -euo pipefail

# The supported workflow installs Go 1.24.0.  Prevent `go install` from
# silently downloading and selecting a newer toolchain on a fresh runner.
export GOTOOLCHAIN=local

repository_root=$(cd "$(dirname "$0")/.." && pwd)
configured_cache_root=${PALOMAR_COMPARATOR_CACHE:-"${TMPDIR:-/tmp}/palomar-comparator"}
if [[ "$configured_cache_root" = /* ]]; then
  cache_root=$configured_cache_root
else
  cache_root="$repository_root/$configured_cache_root"
fi
# Feed the canonical absolute path to the Python preflight as well as the
# shell replay, so both layers describe and use the same cache identity.
export PALOMAR_COMPARATOR_CACHE="$cache_root"
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

# Comparator, Landrun, and NanoDa are the fixed verifier pins used by the
# current Palomar verifier.  lean4export is pinned to the tag matching this
# project's submitted Lean release, because its export format is toolchain
# specific.
comparator_commit=68a064109f01c08f47c8edc9f51d6a2bbffaa188
lean4export_commit=6f4e21dd70c3c11d7fbd07d39e3192792c657448
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

# The Comparator replay must run behind the Linux systemd user boundary.  Fail
# before cloning or building pinned tools when that boundary is unavailable;
# exit 75 matches the bounded diagnostic actuator's environment-unavailable
# contract and prevents a host limitation from being reported as a replay
# verdict or from creating a misleading partial cache.
if ! command -v systemd-run >/dev/null 2>&1; then
  echo "environment unavailable: systemd-run is required for Comparator cold replay" >&2
  exit 75
fi
if ! systemd-run \
  --property=RestrictAddressFamilies=AF_UNIX \
  --user \
  --wait \
  --collect \
  --pipe \
  -- \
  true >/dev/null 2>&1; then
  echo "environment unavailable: systemd user boundary is not usable for Comparator cold replay" >&2
  exit 75
fi

# Keep the positive and deliberate-negative fixtures bound to the same
# project metadata and declaration names before invoking any external tool.
python3 "$repository_root/ErdosProblems/Erdos1049/scripts/run_comparator_replay.py" --dry-run

mkdir -p "$cache_root" "$bin_dir"
checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none --no-tags "$repository" "$destination"
  fi
  # A reusable cache directory is not evidence of the intended upstream.
  # Refuse a pre-existing repository whose origin differs before its pinned
  # SHA is fetched, so a warm replay cannot silently verify an object from a
  # different public project.
  local expected_origin=${repository%.git}
  expected_origin=${expected_origin%/}
  local actual_origin
  if ! actual_origin=$(git -C "$destination" remote get-url origin 2>/dev/null); then
    echo "error: replay cache $destination has no readable origin" >&2
    exit 1
  fi
  actual_origin=${actual_origin%.git}
  actual_origin=${actual_origin%/}
  if [ "$actual_origin" != "$expected_origin" ]; then
    echo "error: replay cache $destination has origin $actual_origin" >&2
    echo "error: expected pinned source origin $expected_origin" >&2
    exit 1
  fi
  if ! git -C "$destination" diff --quiet || ! git -C "$destination" diff --cached --quiet; then
    echo "error: replay cache $destination contains tracked modifications" >&2
    echo "error: refusing to build a non-clean pinned dependency checkout" >&2
    exit 1
  fi
  # Ignore only files covered by the dependency's ignore rules (normally
  # rebuildable outputs).  Non-ignored untracked files are possible source
  # contamination and must not survive into a pinned replay.
  local untracked_files
  if ! untracked_files=$(git -C "$destination" status --porcelain --untracked-files=all); then
    echo "error: replay cache $destination status could not be read" >&2
    echo "error: refusing to build an unverifiable dependency checkout" >&2
    exit 1
  fi
  if [ -n "$untracked_files" ]; then
    echo "error: replay cache $destination contains non-ignored untracked files" >&2
    echo "error: refusing to build a dependency checkout with untracked source" >&2
    exit 1
  fi
  git -C "$destination" fetch --no-tags --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git \
  "$lean4export_dir" "$lean4export_commit"
if [ ! -f "$lean4export_dir/lean-toolchain" ]; then
  echo "error: pinned lean4export revision has no lean-toolchain file" >&2
  exit 1
fi

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  echo "error: project toolchain $project_toolchain does not match" >&2
  echo "the pinned lean4export toolchain $lean4export_toolchain" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git \
  "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git \
  "$nanoda_dir" "$nanoda_commit"

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"
(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)
for required_binary in \
  "$bin_dir/landrun" \
  "$comparator_dir/.lake/build/bin/comparator" \
  "$lean4export_dir/.lake/build/bin/lean4export" \
  "$nanoda_dir/target/release/nanoda_bin"; do
  if [ ! -x "$required_binary" ]; then
    echo "error: pinned replay executable is missing or not executable: $required_binary" >&2
    echo "error: refusing to report Comparator replay status from an incomplete tool build" >&2
    exit 1
  fi
done
cd "$repository_root"
lake exe cache get

run_comparator() {
  local config=$1
  # Keep the Comparator process itself inside the same Linux systemd user
  # boundary used by the bounded Python actuator and the documented manual
  # replay route.  Landrun still provides the nested filesystem sandbox for
  # Comparator's exported Lean/NanoDa processes.
  systemd-run \
    --property=RestrictAddressFamilies=AF_UNIX \
    --user \
    --wait \
    --collect \
    --pipe \
    -E "PATH=$PATH" \
    -E "GOTOOLCHAIN=$GOTOOLCHAIN" \
    -E "PALOMAR_LANDRUN_BIN=$bin_dir/landrun" \
    -E "COMPARATOR_LEAN4EXPORT=$lean4export_dir/.lake/build/bin/lean4export" \
    -E "COMPARATOR_NANODA=$nanoda_dir/target/release/nanoda_bin" \
    -E "COMPARATOR_LANDRUN=$repository_root/scripts/landrun-wrapper.sh" \
    --working-directory "$repository_root" \
    -- \
    bash -c 'exec lake env "$1" "$2"' \
    comparator-replay \
    "$comparator_dir/.lake/build/bin/comparator" \
    "$config"
}

negative_output=$(mktemp)
trap 'rm -f "$negative_output"' EXIT

run_comparator_pair() {
  local label=$1
  local positive_config=$2
  local negative_config=$3
  local expected_diagnostic=$4

  echo "Running the positive Comparator replay for $label"
  run_comparator "$positive_config"

  : >"$negative_output"
  echo "Running the deliberate-negative Comparator replay for $label"
  set +e
  run_comparator "$negative_config" >"$negative_output" 2>&1
  local negative_status=$?
  set -e
  cat "$negative_output"

  if [ "$negative_status" -eq 0 ]; then
    echo "error: deliberate-negative Comparator replay for $label was accepted" >&2
    exit 1
  fi
  if ! grep -Fq "$expected_diagnostic" "$negative_output"; then
    echo "error: deliberate-negative Comparator replay for $label lacked the expected mismatch diagnostic" >&2
    exit 1
  fi
  echo "Positive replay for $label accepted; deliberate-negative replay rejected as expected."
}

run_comparator_pair \
  "the #1049 numerical-height fixture" \
  comparator.json \
  ExternalVerification1049/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification1049.comparator_sevenHalves_numericalHeight'"

run_comparator_pair \
  "the #257 reciprocal-summable-support theorem" \
  ExternalVerification257ReciprocalSupport/comparator.json \
  ExternalVerification257ReciprocalSupport/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification257ReciprocalSupport.irrational_supportPowerSeries_of_summable_reciprocal'"

run_comparator_pair \
  "the #257 unconditional finite-period noncollapse theorem" \
  ExternalVerification257FinitePeriodNoncollapse/comparator.json \
  ExternalVerification257FinitePeriodNoncollapse/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification257FinitePeriodNoncollapse.finite_period_noncollapse_rat_den'"

run_comparator_pair \
  "the #257 terminal scaled-vanishing counterexample endpoint" \
  ExternalVerification257TerminalScaledVanishing/comparator.json \
  ExternalVerification257TerminalScaledVanishing/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification257TerminalScaledVanishing.terminalScaledVanishing_completeCounterexample'"

run_comparator_pair \
  "the #257 actual upper-successor counterexample endpoint" \
  ExternalVerification257ActualUpperSuccessor/comparator.json \
  ExternalVerification257ActualUpperSuccessor/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification257ActualUpperSuccessor.actualUpperSuccessorLinearEscape_completeCounterexample'"

run_comparator_pair \
  "the #68 finite prime-pole numerator formula" \
  ExternalVerification68PrimePole/comparator.json \
  ExternalVerification68PrimePole/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification68PrimePole.factorialGapPrefixLCMNumerator_mod_prime'"

run_comparator_pair \
  "the #68 companion-orbit and strict-successor characterizations" \
  ExternalVerification68StrictSuccessorCarry/comparator.json \
  ExternalVerification68StrictSuccessorCarry/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification68StrictSuccessorCarry.companionOrbit_completeCharacterization'"

run_comparator_pair \
  "the #251 exact polynomial-shift countermodel" \
  ExternalVerification251PolynomialShiftCountermodel/comparator.json \
  ExternalVerification251PolynomialShiftCountermodel/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification251PolynomialShiftCountermodel.polynomialGapTailCountermodel'"

run_comparator_pair \
  "the #1041 sharp collinear, primitive quintic, and cubic-fibre kernels" \
  ExternalVerification1041SolvedFamilies/comparator.json \
  ExternalVerification1041SolvedFamilies/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification1041SolvedFamilies.SharpCollinear.existsPeakLeComparisonBound'"

run_comparator_pair \
  "the #1049 prime-supported rational-gap and two-selector family" \
  ExternalVerification1049PrimeSupportSelectors/comparator.json \
  ExternalVerification1049PrimeSupportSelectors/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification1049PrimeSupportSelectors.primeSupportedTwoSelector_rationalGap'"

run_comparator_pair \
  "the #1049 first transformed normalized-Hankel row and adelic obstruction family" \
  ExternalVerification1049AdelicHeightBridge/comparator.json \
  ExternalVerification1049AdelicHeightBridge/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification1049AdelicHeightBridge.zudilin_firstTransformedRow_initialMonomial'"

run_comparator_pair \
  "the #243 bounded-negative-part complete rigidity theorem" \
  ExternalVerification243BoundedNegativePartRigidity/comparator.json \
  ExternalVerification243BoundedNegativePartRigidity/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification243BoundedNegativePartRigidity.boundedNegativePart_completeRigidity'"

run_comparator_pair \
  "the #249 complete dyadic totient-kernel theorem" \
  ExternalVerification249DyadicTotientKernel/comparator.json \
  ExternalVerification249DyadicTotientKernel/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification249DyadicTotientKernel.dyadicTotientKernelOddCoreBasisAndFiniteRanks'"

run_comparator_pair \
  "the #269 exact three-prime structural theorems" \
  ExternalVerification269ThreePrimeStructure/comparator.json \
  ExternalVerification269ThreePrimeStructure/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification269ThreePrimeStructure.kernel_235_minor_eq_neg_one_fifteen'"

run_comparator_pair \
  "the #269 carry-faithfulness and local-window consumer" \
  ExternalVerification269CarryMechanism/comparator.json \
  ExternalVerification269CarryMechanism/comparator-negative-mismatch.json \
  "Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification269CarryMechanism.no_positive_reducedCarry_of_cofinalLocalWindowEscape'"

echo "All configured positive replays were accepted and all deliberate negatives were rejected."

#!/usr/bin/env bash
set -euo pipefail

# Stable textual anchors for scripts/audit_final_physical_carrier_routing.py.
# audit final physical carrier routing
# python3 scripts/audit_final_physical_carrier_routing.py

BASE="${1:-origin/main}"

fetch_base_ref() {
  local base="$1"
  local remote_branch="main"

  if [[ "${base}" == origin/* ]]; then
    remote_branch="${base#origin/}"
    if git rev-parse --is-shallow-repository >/dev/null 2>&1; then
      git fetch origin "${remote_branch}" --depth=200 || git fetch origin main --depth=200 || true
    else
      git fetch origin "${remote_branch}" || git fetch origin main || true
    fi
    return
  fi

  if [[ "${base}" =~ ^[0-9a-fA-F]{40}$ ]]; then
    if git cat-file -e "${base}^{commit}" 2>/dev/null; then
      return
    fi
    if git rev-parse --is-shallow-repository >/dev/null 2>&1; then
      git fetch --deepen=200 origin main || true
    else
      git fetch origin main || true
    fi
    return
  fi

  if git rev-parse --is-shallow-repository >/dev/null 2>&1; then
    git fetch origin main --depth=200 || true
  else
    git fetch origin main || true
  fi
}

fetch_base_ref "${BASE}"

if ! git diff --name-only "${BASE}"...HEAD >/dev/null 2>&1; then
  echo "[fast] base ${BASE} is unavailable for triple-dot diff; falling back to HEAD^"
  BASE="HEAD^"
fi

changed_files="$(git diff --name-only "${BASE}"...HEAD || true)"
changed_lean_files="$(printf '%s\n' "${changed_files}" | grep '^MGAP4D/.*\.lean$\|^MGAP4D\.lean$' || true)"
changed_scripts="$(printf '%s\n' "${changed_files}" | grep -E '^scripts/.*\.(py|sh)$' || true)"
changed_lake_inputs="$(printf '%s\n' "${changed_files}" | grep -E '^(lean-toolchain|lakefile\.lean|lake-manifest\.json)$' || true)"

# Fast lane checks only changed non-aggregate leaf modules. Aggregate import roots
# are text-audited here and belong to the full/manual integration lane.
aggregate_root_lean_files="$(printf '%s\n' "${changed_lean_files}" | grep -E '^(MGAP4D\.lean|MGAP4D/MathlibAnalytic\.lean)$' || true)"
non_root_changed_lean_files="$(printf '%s\n' "${changed_lean_files}" | grep -Ev '^(MGAP4D\.lean|MGAP4D/MathlibAnalytic\.lean)$' || true)"

printf '[fast] base: %s\n' "${BASE}"
printf '[fast] changed Lean files:\n%s\n' "${changed_lean_files:-<none>}"
printf '[fast] changed aggregate root Lean files:\n%s\n' "${aggregate_root_lean_files:-<none>}"
printf '[fast] changed non-root Lean files:\n%s\n' "${non_root_changed_lean_files:-<none>}"
printf '[fast] changed scripts:\n%s\n' "${changed_scripts:-<none>}"
printf '[fast] changed Lake inputs:\n%s\n' "${changed_lake_inputs:-<none>}"

run_audit_if_present() {
  local script="$1"
  if [ -f "${script}" ]; then
    echo "[fast] audit ${script}"
    python3 "${script}"
  fi
}

lakefile_requires_mathlib() {
  [ -f lakefile.lean ] && grep -q 'require[[:space:]]\+mathlib' lakefile.lean
}

lake_manifest_has_mathlib() {
  [ -f lake-manifest.json ] && grep -Eq '"name"[[:space:]]*:[[:space:]]*"mathlib"|mathlib4\.git|leanprover-community/mathlib4' lake-manifest.json
}

lake_manifest_empty_packages() {
  [ -f lake-manifest.json ] && grep -Eq '"packages"[[:space:]]*:[[:space:]]*\[[[:space:]]*\]' lake-manifest.json
}

ensure_lake_manifest() {
  if [ ! -f lake-manifest.json ]; then
    echo "[fast] lake manifest missing; run lake update once"
    lake update
    return
  fi

  if lakefile_requires_mathlib && lake_manifest_empty_packages; then
    echo "[fast] lake manifest has empty package list but lakefile requires mathlib; run lake update"
    lake update
    return
  fi

  if lakefile_requires_mathlib && ! lake_manifest_has_mathlib; then
    echo "[fast] lake manifest missing mathlib dependency; run lake update"
    lake update
    return
  fi

  echo "[fast] lake manifest present and JSON-compatible; skip lake update"
}

ensure_mathlib_cache() {
  if [ -d ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ]; then
    echo "[fast] mathlib cache present; skip lake exe cache get"
  else
    echo "[fast] mathlib cache missing; lake exe cache get"
    lake exe cache get || true
  fi
}

if [ -n "${changed_lean_files}" ]; then
  echo "[fast] preflight changed Lean static audit"
  # shellcheck disable=SC2086
  python3 scripts/audit_changed_lean_preflight.py ${changed_lean_files}
fi

echo "[fast] audit Lean forbidden tokens"
python3 scripts/audit_lean_forbidden_tokens.py

echo "[fast] audit hard physical residual ledger"
python3 scripts/audit_hard_physical_residual_ledger.py

echo "[fast] audit analytic bridge coherence"
python3 scripts/audit_bridge_coherence.py

echo "[fast] audit final physical carrier routing"
python3 scripts/audit_final_physical_carrier_routing.py

echo "[fast] audit OS/Wightman mass-gap bridge"
python3 scripts/audit_os_wightman_mass_gap_bridge.py

declare -a audit_sensitive_targets=()
if printf '%s\n' "${changed_scripts}" | grep -qx 'scripts/audit_os_wightman_mass_gap_bridge.py'; then
  audit_sensitive_targets+=(MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge)
fi

if [ -n "${aggregate_root_lean_files}" ]; then
  echo "[fast] aggregate root imports changed; Lean execution is restricted to changed leaf modules"
fi

if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2HilbertNormOneTarget\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_hilbert_norm_one_target.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2R2ProgressIndex\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_r2_progress_index.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2ObstructionIndex\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_obstruction_index.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2UnboundednessObstruction\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_unboundedness_obstruction.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2DiagonalWeightThreshold\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_diagonal_weight_threshold.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2DiagonalWeightProbe\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_diagonal_weight_probe.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2FiniteSupportCore\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_finite_support_core.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2DiagonalGraphNorm\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_diagonal_graph_norm.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2DiagonalGraph\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_diagonal_graph.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineL2RealSequence\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_l2_real_sequence.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineOperatorLaneCheckpoint\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_operator_lane_checkpoint.py
fi
if printf '%s\n' "${changed_lean_files}" | grep -q 'ConcreteAnalyticSpineOperatorLane\.lean'; then
  run_audit_if_present scripts/audit_concrete_analytic_spine_operator_lane.py
fi

if [ -z "${changed_lean_files}" ]; then
  if [ "${#audit_sensitive_targets[@]}" -gt 0 ]; then
    ensure_lake_manifest
    ensure_mathlib_cache
    printf '[fast] lake build audit-sensitive targets:'
    printf ' %s' "${audit_sensitive_targets[@]}"
    printf '\n'
    lake build "${audit_sensitive_targets[@]}"
    exit 0
  fi
  echo "[fast] no Lean files changed; skip Lake manifest, Mathlib cache, and Lean execution"
  exit 0
fi

if [ -z "${non_root_changed_lean_files}" ]; then
  if [ "${#audit_sensitive_targets[@]}" -gt 0 ]; then
    ensure_lake_manifest
    ensure_mathlib_cache
    printf '[fast] lake build audit-sensitive targets:'
    printf ' %s' "${audit_sensitive_targets[@]}"
    printf '\n'
    lake build "${audit_sensitive_targets[@]}"
    exit 0
  fi
  echo "[fast] no non-aggregate Lean leaf files changed; skip Lean execution in fast lane"
  exit 0
fi

ensure_lake_manifest
ensure_mathlib_cache

# Directly elaborate each changed leaf against restored project and Mathlib olean
# caches. This avoids Lake scheduling the full transitive build graph on the
# common path. Toolchain or manifest changes deliberately retain the Lake build
# path because their cache compatibility cannot be assumed.
direct_lean_allowed=true
if [ -n "${changed_lake_inputs}" ]; then
  direct_lean_allowed=false
  echo "[fast] Lake inputs changed; use dependency-aware lake build"
fi

if [ "${direct_lean_allowed}" = true ]; then
  direct_lean_ok=true
  while IFS= read -r file; do
    [ -z "${file}" ] && continue
    echo "[fast] direct Lean elaboration: ${file}"
    if ! lake env lean -DautoImplicit=false "${file}"; then
      direct_lean_ok=false
      echo "[fast] direct elaboration failed; retry through lake build for dependency recovery"
      break
    fi
  done <<< "$(printf '%s\n' "${non_root_changed_lean_files}" | sort -u)"

  if [ "${direct_lean_ok}" = true ] && [ "${#audit_sensitive_targets[@]}" -eq 0 ]; then
    echo "[fast] direct changed-file Lean elaboration passed"
    exit 0
  fi
fi

# Fallback: build only maximal changed non-aggregate modules. If changed module A
# imports changed module B, building A already covers B.
declare -A changed_target_set=()
declare -A imported_by_changed=()
targets=()

while IFS= read -r file; do
  [ -z "${file}" ] && continue
  target="${file%.lean}"
  target="${target//\//.}"
  changed_target_set["${target}"]=1
  targets+=("${target}")
done <<< "$(printf '%s\n' "${non_root_changed_lean_files}" | sort -u)"

while IFS= read -r file; do
  [ -z "${file}" ] && continue
  while IFS= read -r imported; do
    [ -z "${imported}" ] && continue
    if [ -n "${changed_target_set[${imported}]+x}" ]; then
      imported_by_changed["${imported}"]=1
    fi
  done <<< "$(grep -E '^import[[:space:]]+MGAP4D\.' "${file}" 2>/dev/null | awk '{print $2}' || true)"
done <<< "$(printf '%s\n' "${non_root_changed_lean_files}" | sort -u)"

maximal_targets=()
for target in "${targets[@]}"; do
  if [ -z "${imported_by_changed[${target}]+x}" ]; then
    maximal_targets+=("${target}")
  fi
done

if [ "${#maximal_targets[@]}" -eq 0 ]; then
  echo "[fast] maximal target reduction was empty; fall back to all changed non-aggregate targets"
  maximal_targets=("${targets[@]}")
fi

if [ "${#audit_sensitive_targets[@]}" -gt 0 ]; then
  maximal_targets+=("${audit_sensitive_targets[@]}")
fi

printf '[fast] fallback lake build maximal changed non-aggregate targets:'
printf ' %s' "${maximal_targets[@]}"
printf '\n'
lake build "${maximal_targets[@]}"

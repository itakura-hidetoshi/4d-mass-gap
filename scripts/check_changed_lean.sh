#!/usr/bin/env bash
set -euo pipefail

BASE="${1:-origin/main}"

if git rev-parse --is-shallow-repository >/dev/null 2>&1; then
  git fetch origin main --depth=200 || true
else
  git fetch origin main || true
fi

changed_files="$(git diff --name-only "${BASE}"...HEAD || true)"
changed_lean_files="$(printf '%s\n' "${changed_files}" | grep '^MGAP4D/.*\.lean$' || true)"
changed_scripts="$(printf '%s\n' "${changed_files}" | grep -E '^scripts/.*\.(py|sh)$' || true)"
non_root_changed_lean_files="$(printf '%s\n' "${changed_lean_files}" | grep -v '^MGAP4D/MathlibAnalytic\.lean$' || true)"

printf '[fast] base: %s\n' "${BASE}"
printf '[fast] changed Lean files:\n%s\n' "${changed_lean_files:-<none>}"
printf '[fast] changed non-root Lean files:\n%s\n' "${non_root_changed_lean_files:-<none>}"
printf '[fast] changed scripts:\n%s\n' "${changed_scripts:-<none>}"

run_audit_if_present() {
  local script="$1"
  if [ -f "${script}" ]; then
    echo "[fast] audit ${script}"
    python3 "${script}"
  fi
}

# Always keep the hard safety gates.
echo "[fast] audit Lean forbidden tokens"
python3 scripts/audit_lean_forbidden_tokens.py

echo "[fast] audit hard physical residual ledger"
python3 scripts/audit_hard_physical_residual_ledger.py

echo "[fast] audit analytic bridge coherence"
python3 scripts/audit_bridge_coherence.py

# Run targeted audits for changed concrete analytic spine files when available.
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

lakefile_requires_mathlib() {
  [ -f lakefile.lean ] && grep -q 'require[[:space:]]\+mathlib' lakefile.lean
}

lake_manifest_has_mathlib() {
  [ -f lake-manifest.json ] && grep -Eq '"name"[[:space:]]*:[[:space:]]*"mathlib"|mathlib4\.git|leanprover-community/mathlib4' lake-manifest.json
}

ensure_lake_manifest() {
  if [ ! -f lake-manifest.json ]; then
    echo "[fast] lake manifest missing; run lake update once"
    lake update
    return
  fi

  if lakefile_requires_mathlib && ! lake_manifest_has_mathlib; then
    echo "[fast] lake manifest present but stale for mathlib; run lake update"
    lake update
    return
  fi

  echo "[fast] lake manifest present and dependency-compatible; skip lake update"
}

ensure_lake_manifest

echo "[fast] lake exe cache get"
lake exe cache get || true

if [ -z "${changed_lean_files}" ]; then
  echo "[fast] no Lean files changed"
  exit 0
fi

# Building the root import module on every PR defeats the fast lane, because the
# root intentionally imports the whole analytic surface.  When root and leaf
# modules both changed, build only the changed leaf modules; root-level full
# integration remains covered by Full Local Check on main/manual runs.
if [ -z "${non_root_changed_lean_files}" ]; then
  if printf '%s\n' "${changed_lean_files}" | grep -q '^MGAP4D/MathlibAnalytic\.lean$'; then
    echo "[fast] only root import changed; build root module"
    lake build MGAP4D.MathlibAnalytic
  else
    echo "[fast] no non-root Lean files changed"
  fi
  exit 0
fi

while IFS= read -r file; do
  [ -z "${file}" ] && continue
  target="${file%.lean}"
  target="${target//\//.}"
  echo "[fast] lake build ${target}"
  lake build "${target}"
done <<< "${non_root_changed_lean_files}"

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
changed_scripts="$(printf '%s\n' "${changed_files}" | grep '^scripts/.*\.(py|sh)$' || true)"

printf '[fast] base: %s\n' "${BASE}"
printf '[fast] changed Lean files:\n%s\n' "${changed_lean_files:-<none>}"
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

# Avoid lake update in PR fast checks.  Use the existing manifest/cache path.
echo "[fast] lake exe cache get"
lake exe cache get || true

if printf '%s\n' "${changed_lean_files}" | grep -q '^MGAP4D/MathlibAnalytic\.lean$'; then
  echo "[fast] root import changed; build root module"
  lake build MGAP4D.MathlibAnalytic
  exit 0
fi

if [ -z "${changed_lean_files}" ]; then
  echo "[fast] no Lean files changed"
  exit 0
fi

while IFS= read -r file; do
  [ -z "${file}" ] && continue
  target="${file%.lean}"
  target="${target//\//.}"
  echo "[fast] lake build ${target}"
  lake build "${target}"
done <<< "${changed_lean_files}"

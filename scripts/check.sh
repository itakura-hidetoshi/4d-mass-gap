#!/usr/bin/env bash
set -euo pipefail

echo "[check] verify manifest"
python3 scripts/verify_manifest.py

echo "[check] audit Lean forbidden tokens"
python3 scripts/audit_lean_forbidden_tokens.py

echo "[check] audit major theorem non-placeholder surfaces"
python3 scripts/audit_major_theorem_nonplaceholder.py

echo "[check] audit analytic bridge coherence"
python3 scripts/audit_bridge_coherence.py

echo "[check] audit infinite-dimensional Yang-Mills target layer"
python3 scripts/audit_infinite_dimensional_target_layer.py

echo "[check] audit infinite-dimensional residual filling bridge"
python3 scripts/audit_infinite_dimensional_residual_filling.py

echo "[check] replay summary"
python3 scripts/replay_summary.py

echo "[check] lake update"
lake update

echo "[check] lake build"
lake build

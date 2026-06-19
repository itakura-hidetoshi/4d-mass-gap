#!/usr/bin/env bash
set -euo pipefail

# Stable textual anchors for scripts/audit_final_physical_carrier_routing.py.
# audit final physical carrier routing
# python3 scripts/audit_final_physical_carrier_routing.py

base="${1:-origin/main}"
tmp_script="$(mktemp)"
trap 'rm -f "${tmp_script}"' EXIT

git fetch origin main --depth=200 || true
git show origin/main:scripts/check_changed_lean.sh > "${tmp_script}"
bash "${tmp_script}" "${base}" 2>&1 | tail -n 160

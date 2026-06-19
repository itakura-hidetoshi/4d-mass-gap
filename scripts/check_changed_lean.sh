#!/usr/bin/env bash
set -euo pipefail

base="${1:-origin/main}"
tmp_script="$(mktemp)"
trap 'rm -f "${tmp_script}"' EXIT

git fetch origin main --depth=200 || true
git show origin/main:scripts/check_changed_lean.sh > "${tmp_script}"
bash "${tmp_script}" "${base}"

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

aggregate_root_lean_files="$(printf '%s\n' "${changed_lean_files}" | grep -E '^(MGAP4D\.lean|MGAP4D/MathlibAnalytic\.lean)$' || true)"
non_root_changed_lean_files="$(printf '%s\n' "${changed_lean_files}" | grep -Ev '^(MGAP4D\.lean|MGAP4D/MathlibAnalytic\.lean)$' || true)"

printf '[fast] base: %s\n' "${BASE}"
printf '[fast] changed Lean files:\n%s\n' "${changed_lean_files:-<none>}"
printf '[fast] changed aggregate root Lean files:\n%s\n' "${aggregate_root_lean_files:-<none>}"
printf '[fast] changed non-root Lean files:\n%s\n' "${non_root_changed_lean_files:-<none>}"
printf '[fast] changed scripts:\n%s\n' "${changed_scripts:-<none>}"

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

tmp_script="$(mktemp)"
trap 'rm -f "${tmp_script}"' EXIT
git show origin/main:scripts/check_changed_lean.sh > "${tmp_script}"
bash "${tmp_script}" "${BASE}"

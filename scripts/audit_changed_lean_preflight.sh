#!/usr/bin/env bash
set -euo pipefail

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
  echo "[preflight] base ${BASE} is unavailable for triple-dot diff; falling back to HEAD^"
  BASE="HEAD^"
fi

changed_files="$(git diff --name-only "${BASE}"...HEAD || true)"
changed_lean_files="$(printf '%s\n' "${changed_files}" | grep '^MGAP4D/.*\.lean$\|^MGAP4D\.lean$' || true)"

printf '[preflight] base: %s\n' "${BASE}"
printf '[preflight] changed Lean files:\n%s\n' "${changed_lean_files:-<none>}"

if [ -z "${changed_lean_files}" ]; then
  echo "[preflight] no Lean files changed"
  exit 0
fi

# shellcheck disable=SC2086
python3 scripts/audit_changed_lean_preflight.py ${changed_lean_files}

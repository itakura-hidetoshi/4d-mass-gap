#!/usr/bin/env bash
set -euo pipefail

TAG_NAME="phase3-pre-release-hygiene-ci-green"
TARGET_COMMIT="d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b"
TAG_MESSAGE="Phase 3 pre-release hygiene CI green"
REMOTE="origin"

echo "Preparing bounded tag creation"
echo "Tag: ${TAG_NAME}"
echo "Target commit: ${TARGET_COMMIT}"

git fetch "${REMOTE}" main --tags

if git rev-parse -q --verify "refs/tags/${TAG_NAME}" >/dev/null; then
  existing="$(git rev-list -n 1 "${TAG_NAME}")"
  echo "Tag already exists locally: ${TAG_NAME} -> ${existing}"
  if [ "${existing}" != "${TARGET_COMMIT}" ]; then
    echo "ERROR: existing local tag does not match target commit" >&2
    exit 1
  fi
else
  git cat-file -e "${TARGET_COMMIT}^{commit}"
  git tag -a "${TAG_NAME}" "${TARGET_COMMIT}" -m "${TAG_MESSAGE}"
fi

git push "${REMOTE}" "${TAG_NAME}"

echo "Verifying remote tag"
remote_line="$(git ls-remote --tags "${REMOTE}" "refs/tags/${TAG_NAME}" | head -n 1 || true)"
if [ -z "${remote_line}" ]; then
  echo "ERROR: remote tag was not found after push" >&2
  exit 1
fi

remote_ref="$(printf '%s\n' "${remote_line}" | awk '{print $1}')"
echo "Remote tag object or commit: ${remote_ref}"

resolved="$(git rev-list -n 1 "${TAG_NAME}")"
echo "Resolved tag commit: ${resolved}"

if [ "${resolved}" != "${TARGET_COMMIT}" ]; then
  echo "ERROR: resolved tag commit does not match target commit" >&2
  exit 1
fi

echo "Tag creation verified: ${TAG_NAME} -> ${TARGET_COMMIT}"
echo "Boundary preserved: this tag is a Phase 3 pre-release hygiene checkpoint, not final theorem release."

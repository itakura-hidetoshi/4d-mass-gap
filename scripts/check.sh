#!/usr/bin/env bash
set -euo pipefail

python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build

# Full Check CI Ledger — 2026-05-16

Repository: `itakura-hidetoshi/4d-mass-gap`
Branch: `main`

## Confirmed GitHub Actions run

- Workflow run ID: `25962449266`
- Workflow job ID: `76320024932`
- Job name: `Run scripts/check.sh`
- Head SHA checked out by CI: `4f762dc5d0d161d2102f505e143805be74e7f850`
- Result: `success`
- Runner image: `ubuntu-24.04`
- Lean version: `4.30.0-rc2`
- Lake version: `5.0.0-src+3dc1a08`

## Successful job steps

- Set up job: `success`
- Checkout repository: `success`
- Cache elan and Lake build artifacts: `success`
- Install elan and Lean toolchain: `success`
- Show Lean and Lake versions: `success`
- Run full local check script: `success`
- Post Cache elan and Lake build artifacts: `success`
- Post Checkout repository: `success`
- Complete job: `success`

## Confirmed check surfaces

The CI log confirms that `bash scripts/check.sh` completed successfully.

Confirmed surfaces include:

- archived manifest verification passed
- Lean forbidden-token audit passed
- Lean files scanned: `457`
- `sorry`: `0`
- `admit`: `0`
- `axiom`: `0`
- `constant`: `0`
- major theorem non-placeholder audit passed
- major theorem specs audited: `12`
- analytic bridge coherence audit passed
- infinite-dimensional Yang-Mills target layer audit passed
- infinite-dimensional residual filling bridge audit passed
- hard physical residual hardening map audit passed
- Hilbert construction lane hardening audit passed
- self-adjoint HPhys lane hardening audit passed
- continuum Yang-Mills lane hardening audit passed
- plaquette spectral weight lane hardening audit passed
- four-lane residual closure audit passed
- internal review residual closure gate audit passed
- external audit readiness gate audit passed
- replay summary generated
- Lean replay summary `lean_files`: `457`
- Lean replay summary `imports`: `1191`
- Lean replay summary `declaration_like_lines`: `2602`
- Lean replay summary `namespace_lines`: `938`
- Lean replay summary `total_lines`: `27203`
- `lake update` completed
- external audit readiness gate build completed successfully
- Lake build completed successfully

## Build surface

The CI log confirms:

- `Build completed successfully (8368 jobs).`
- `Build completed successfully (0 jobs).`

The first build includes the external audit readiness gate target and its dependency surface. The second build confirms that the Lake project remained up to date after the targeted build.

## Boundary

This ledger records configured CI passage and reproducibility evidence for the referenced run and job.

This ledger does not grant:

- independent mathematical acceptance
- external peer-review acceptance
- final theorem authority beyond the checked repository state
- clinical authority
- execution authority
- governance-bypass authority

CI green confirms that the configured repository checks passed for the referenced commit. It does not by itself replace external audit, independent reproduction, or formal publication review.

## Append-only rule

Future CI observations, external-audit results, proof-hardening updates, or publication records must be added as same-root append-only entries or as a new dated ledger file. Destructive replacement of this CI green evidence or its authority boundary is forbidden.

Version: `full-check-ci-ledger-2026-05-16`
Date: `2026-05-16`
Author: Hidetoshi Itakura / 板倉英俊

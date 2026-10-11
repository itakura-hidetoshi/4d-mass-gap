# Historical Lean CI diagnostic logs (2026-10-11 UTC)

This archive preserves **plain-text** fast-check diagnostics that were previously downloaded as GitHub Actions ZIP artifacts. No ZIP files are checked into this repository.

The contents were recovered from the corresponding authoritative GitHub Actions **Changed Lean fast check** job logs. Runner timestamp prefixes were removed to reconstruct the original `lean-fast.log` text. **All 10 reconstructed `.log` files were verified to be byte-for-byte identical to the original uncompressed `lean-fast.log` entries in the corresponding ZIP archives**, by comparing their Git blob SHA-1 digests. No ZIP archive was committed.

All PRs refer to the sole theorem-bearing branch `formal/real-hilbert-uniform-coercive-strong-limit`. The logs include both failed attempts (useful for Lean4 syntax and tactic debugging) and successfully compiled revisions. Warnings from pre-existing, unrelated Lean modules can occur within otherwise successful logs; distinguish these from warnings on changed files.

| Prior local ZIP filename | PR / front | GitHub Actions run | Changed Lean job | Outcome | Saved text |
|---|---|---|---|---|---|
| `ck-ci-logs.zip` | [#5436](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5436) / CK | [38138971377](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38138971377) | `114468665599` | FAILED | [plain log](./PR5436_CK_run38138971377_FAILED.log) |
| `ck-second-ci-log.zip` | [#5436](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5436) / CK | [38139379883](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38139379883) | `114469892992` | FAILED | [plain log](./PR5436_CK_run38139379883_FAILED.log) |
| `ck-third-ci-log.zip` | [#5436](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5436) / CK | [38139764917](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38139764917) | `114471026115` | GREEN | [plain log](./PR5436_CK_run38139764917_GREEN.log) |
| `cl-pr5437-ci-38141251539.zip` | [#5437](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5437) / CL | [38141251539](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38141251539) | `114475410321` | GREEN | [plain log](./PR5437_CL_run38141251539_GREEN.log) |
| `CN-ci-38143909183.zip` | [#5439](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5439) / CN | [38143909183](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38143909183) | `114483174561` | GREEN | [plain log](./PR5439_CN_run38143909183_GREEN.log) |
| `CO-first-ci-38145584049.zip` | [#5440](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5440) / CO | [38145584049](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38145584049) | `114488101868` | GREEN | [plain log](./PR5440_CO_run38145584049_GREEN.log) |
| `cp-first-ci-38146777264.zip` | [#5441](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5441) / CP | [38146777264](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38146777264) | `114491692238` | FAILED | [plain log](./PR5441_CP_run38146777264_FAILED.log) |
| `cp-second-ci-38147158879.zip` | [#5441](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5441) / CP | [38147158879](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38147158879) | `114492817970` | GREEN | [plain log](./PR5441_CP_run38147158879_GREEN.log) |
| `cr5443-first-ci.zip` | [#5443](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5443) / CR | [38163645065](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38163645065) | `114541580755` | FAILED | [plain log](./PR5443_CR_run38163645065_FAILED.log) |
| `cr5443-green-ci.zip` | [#5443](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5443) / CR | [38163964217](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38163964217) | `114542534872` | GREEN | [plain log](./PR5443_CR_run38163964217_GREEN.log) |

## Provenance and scope

- Exact CI provenance is the corresponding GitHub Actions run and job, not this documentation-only copy.
- Original build artifacts remain in GitHub Actions for as long as artifact retention allows; this Git archive preserves the diagnostic text.
- These logs are not new formal Lean proofs, axioms, or evidence of a continuum 4D Yang–Mills mass gap.
- For subsequent CI debugging, prefer GitHub run links or checked-in `.log` files over sharing ZIP downloads.
- Scope: this folder archives the **10 previously shared diagnostic ZIPs available in the active conversation**. It does not silently import unrelated historical release bundles or KuuOS archives from the user's Library.

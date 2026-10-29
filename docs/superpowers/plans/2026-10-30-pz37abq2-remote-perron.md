# P4-Q2-PZ37ABQ2 Implementation Plan

> Execute inline using the established GitHub MCP workflow. No git/gh CLI.

**Goal:** Integrate the unchanged remote temporal Wilson factors against the actual spatial half-weight times the positive continuous Perron representative, and derive the actual four-edge kernel-section formula and volume-independent relative comparison.

**Architecture:** Reconstruct complete configurations from MY's embedded four edges and their true complement. Prove product-Haar Fubini for that reconstruction. Define the remote integral from the original factors, prove integrability/positivity and ABQ's exp(56*b) comparison after integration; connect to the full one-slab kernel without identifying temporal mass with physical norm.

**Tech Stack:** Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

**Spec:** User-approved continuation after #6022; original theorem branch HEAD 1e776fa1820e926d55d5cc0276ac5cfb528ff2cc.

## Global Constraints

Append new files only. Preserve all existing definitions, assumptions, no-go statements and physical normalization. All H including zero; b >= 0. The four-edge relative comparison is not an absolute physical GI floor. No changes to workflows, dependency pins or prior Lean files.

## Review Focus

Explicit selected/remote evaluation; finite subtype instances and DecidableEq coherence; continuous rather than arbitrary L2 pointwise Perron representative; genuine integrability before monotonicity/Fubini; physical norm t and both spatial half-weights retained.

## Tasks

- [ ] Add finite-product embedding assembly, selected/remote identities, joint continuity, finite-product factorization and continuous-test Fubini.
- [ ] Add actual remote temporal kernel and actual remote spatial/Perron integral; prove integrability, positivity and exp(56*b) relative comparison with no unknown analytic assumptions.
- [ ] Connect the remote integral to the full one-slab kernel-section integral, and retain its true mass t*Omega(B).
- [ ] Validate all new declarations with exact-source completed Lean CI, zero changed-file diagnostics, standard three axioms only, no sorryAx, independent completion receipt. Read full changed files on any error.

## Verification

The theorem signatures are the proof specifications; their complete proof terms and #print axioms are the acceptance checks. No local Lean executable is present in this session. GitHub CI is the kernel-checking authority; uncompiled code must not be called proved. A static absence/readiness check is not a substitute for kernel validation.

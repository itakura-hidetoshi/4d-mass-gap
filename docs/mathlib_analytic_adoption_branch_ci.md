# Mathlib analytic adoption branch CI

PR: #10
Branch: mathlib-adoption/exact-gap-analytic
Run ID: 25887334136
Audit job ID: 76082194535
Build job ID: 76082215125
Head commit: 37d6ebdd9ce30a1a1047c486eb652e7f9602813e
PR merge commit checked out by CI: e4dd24ebf2a0117f0b4957f2b8dcd9331eb4d2a6
Result: success

Status: CI green.

Confirmed jobs:

```text
Audit metadata and Lean source: success
Build Lean project via direct elan: success
```

Build job confirmed steps:

```text
Checkout PR #10 merge ref: success
Cache elan and Lake build artifacts: success
Show Lean and Lake versions: success
Generate Lake manifest: success
Mathlib post-update cache download: success
lake exe cache get: success
lake build: success
```

Observed toolchain:

```text
Lean: 4.30.0-rc2
Lake: 5.0.0-src+3dc1a08
```

Mathlib evidence from log:

```text
mathlib: running post-update hooks
Using cache from leanprover-community/mathlib4
Downloaded 8297 file(s)
Decompressed 8297 file(s)
lake exe cache get: No files to download
Build completed successfully
```

Artifacts checked by this CI:

```text
lakefile.lean
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D.lean
```

Boundary:

```text
Mathlib adoption is green on PR #10 / adoption branch
main remains pre-Mathlib
final theorem release not opened
public theorem boundary held
analytic replacement remains review-gated
```

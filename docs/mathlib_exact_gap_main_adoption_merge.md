# Mathlib exact-gap main adoption merge

PR: #10
Merge commit: ba1a17e43513b7f256be41c78f3c1e5c912d3ce9
Status: merged to main

## Adopted on main

```text
Mathlib dependency in lakefile.lean
MGAP4D/MathlibAnalytic.lean root module
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/GapInfimumReal.lean
MGAP4D/MathlibAnalytic/RayleighLowerBoundReal.lean
MGAP4D/MathlibAnalytic/RayleighAttainmentReal.lean
MGAP4D/MathlibAnalytic/SpectralMassReal.lean
MGAP4D/MathlibAnalytic/ExactGapAnalyticRealClosure.lean
MGAP4D/MathlibAnalytic/ExactGapAnalyticAdoptionReviewClosure.lean
```

## Meaning

```text
pre-Mathlib boundary is resolved for the real-order analytic prototype layer
exact value = 33/20 as Real
0 < 33/20
1 < 33/20
Rayleigh lower-bound prototype available
Rayleigh attainment prototype available
positive spectral-mass prototype available
analytic real closure available
adoption review closure available
```

## Boundary preserved

```text
final theorem release remains closed
public theorem boundary remains held
full Hilbert-space Rayleigh theorem remains open
full self-adjoint H_phys theorem remains open
full spectral theorem integration remains open
full projection-valued-measure theorem remains open
observable atom theorem in operator-measure form remains open
```

## CI expectation

```text
main should now run Lean Direct Elan CI with Mathlib
lake update
lake exe cache get
lake build
```

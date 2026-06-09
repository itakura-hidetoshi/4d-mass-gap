# R6 exact atom 33/20 value-origin boundary

Status: active boundary note for external review.

## Core correction

The equality

```lean
MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
```

is currently backed at the carrier layer by

```lean
noncomputable def exactGapValueReal : ℝ := (33 : ℝ) / 20

theorem exactGapValueReal_eq : exactGapValueReal = (33 : ℝ) / 20 := by
  rfl
```

This is a normalized carrier check.  It is not, by itself, a proof that the
value `33 / 20` is forced by the concrete spectral data.

## Current R6 interpretation

The current R6 exact-atom route should be read as:

```text
carrier value exactGapValueReal = 33/20
  -> transported through observable-atom membership
  -> transported through PVM mass compatibility
  -> retained at R6/R7/terminal audit surfaces
```

It should not be read as:

```text
concrete self-adjoint operator spectrum forces 33/20 without using the carrier equality
```

## Lean firewall

The boundary is now represented by:

```lean
MGAP4D/R6/Theorem/ExactAtom3320SpectralOriginFirewall.lean
```

with the public marker:

```lean
ExactAtom3320SpectralOriginPublicBoundaryHeld
```

and the open obligation:

```lean
ExactAtom3320GenuineSpectralValueDerivationStillOpen
```

The existing R6 origin file also carries:

```lean
ExactAtom3320SpectralValueDerivationStillOpenAtR6Origin
```

so `ExactAtom3320NonDefinitionalDerivationTarget` no longer silently reads as a
completed spectral-origin proof.

## Required future discharge

A genuine value-origin discharge must derive the number `33 / 20` from the
concrete spectral data of the self-adjoint operator, without using
`exactGapValueReal_eq` as the source of the numeric value.

A future acceptable route should expose theorem anchors of the following kind:

```text
concrete self-adjoint operator
  -> actual Borel spectral measure / PVM
  -> nontrivial spectral atom or threshold law
  -> calculation forcing 33/20
  -> exactGapValueReal = 33/20 only as final identification, not as source
```

Until then, the correct public statement is:

```text
R6 transports the normalized carrier value 33/20 through the observable-atom/PVM
mass lane; the genuine non-definitional spectral origin of 33/20 remains open.
```

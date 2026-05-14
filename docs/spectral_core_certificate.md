# Spectral core certificate

This note records a pre-Mathlib core certificate for the spectral gap formalization surface.

## Lean artifacts

```text
MGAP4D/Spectral/CoreCertificate.lean
MGAP4D/Spectral.lean
MGAP4D/SpectralGapFormalizationGate.lean
```

## Added surface

```text
SpectralCoreCertificate
SpectralCoreCertificate.ready
spectral_gap_3320_formalization_ready
spectral3320CoreCertificate
spectral_core_certificate_pack
spectral_3320_core_certificate_ready
spectral_3320_core_certificate_value
spectral_3320_core_certificate_lower_bound_value
spectral_3320_core_certificate_positive_numerator
spectral_gap_formalization_gate_sees_core_certificate
```

## Meaning

The core certificate bundles the current formalization surface, lower-bound certificate, positive witness, and sector-boundary readiness into one structural proof surface.

```text
formalization is ready
lower-bound certificate is ready
formalization value matches lower-bound value
formalization witness matches lower-bound positive-gap witness
sector-boundary certificate is ready
```

This does not claim final theorem release.

## Gate update

`SpectralGapFormalizationGate` now includes:

```text
coreCertificateVisible : Prop
```

and exposes:

```text
spectral_gap_formalization_gate_sees_core_certificate
```

## Boundary

```text
main remains pre-Mathlib
Mathlib on main is not introduced
R1--R7 theorem completions are not claimed
final gap theorem release is not unlocked
public theorem boundary remains held
```

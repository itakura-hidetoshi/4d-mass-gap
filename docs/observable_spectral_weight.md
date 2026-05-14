# Observable spectral weight

This note records a pre-Mathlib certificate for observable spectral weight at the normalized 33/20 value.

## Lean artifacts

```text
MGAP4D/Plaquette/ObservableSpectralWeight.lean
MGAP4D/Plaquette.lean
```

## Added surface

```text
ObservableSpectralWeightCertificate
ObservableSpectralWeightCertificate.ready
observableSpectralWeight3320Certificate
observable_spectral_weight_certificate_pack
observable_spectral_weight_3320_certificate_ready
observable_spectral_weight_3320_value
observable_spectral_weight_3320_mass_value
observable_spectral_weight_3320_positive_mass
observable_spectral_weight_3320_centered
observable_spectral_weight_3320_compact_support
observable_spectral_weight_3320_witness_orthogonal
observable_spectral_weight_3320_witness_not_vacuum
```

## Meaning

The certificate lifts the existing positive spectral-mass witness into a structured proof surface.

```text
observable = A_pg
observable is centered
smearing has compact support
rho_Apg_3320 witness is used
spectral weight value = 33/20
positive mass flag is true
sector separation is ready
witness sector is orthogonal
witness sector is not vacuum
```

## Boundary

```text
pre-Mathlib structural observable spectral weight only
R1--R7 theorem completions not claimed
Mathlib on main not introduced
public theorem boundary held
```

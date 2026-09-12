import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumSwap12
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumSwap23
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumParity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumChargeConjugation
import Mathlib.Tactic

/-!
# Discrete-channel certificate for the all-spatial zero-momentum Wilson observable

The concrete equal-weight all-spatial plaquette observable now has separate theorem-generated
receipts for

* zero spatial momentum: invariance under every periodic spatial translation;
* invariance under the adjacent spatial-axis swaps `(1 2)` and `(2 3)`;
* spatial parity `P = +`;
* charge conjugation `C = +`.

This file packages exactly those already-proved statements into one proposition-valued certificate.
It deliberately does **not** rename the package as a full cubic `A₁⁺⁺` or continuum `J^PC = 0⁺⁺`
certificate: the remaining signed cubic generators / continuum-spin identification must be proved
separately before those stronger labels are theorem-generated.

No new physical, continuum, spectral, or analytic assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance discreteChannelSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Audit-visible bundle of the exact finite-lattice discrete transformation laws already proved for
the equal-weight all-spatial zero-momentum normalized-real-trace observable. -/
structure PeriodicHypercubicEvenAllSpatialZeroMomentumDiscreteChannelCertificate
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : Prop where
  spatialTranslationInvariant :
    ∀ b : PeriodicHypercubicEvenSpatialDisplacement H,
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
          (periodicHypercubicConfigurationTranslationMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (PeriodicHypercubicEvenSideLength H) b.1 A) =
        periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A
  swap12Invariant :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicConfigurationSpatialAxisSwap12 A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A
  swap23Invariant :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicConfigurationSpatialAxisSwap23 A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A
  parityEven :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicEvenConfigurationSpatialParity H A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A
  chargeConjugationEven :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicEvenConfigurationChargeConjugation H N A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A

/-- The concrete Wilson observable automatically carries the discrete-channel certificate; every
field is discharged by a canonical theorem from the preceding additive layers. -/
theorem periodicHypercubicEvenAllSpatialZeroMomentumDiscreteChannelCertificate
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenAllSpatialZeroMomentumDiscreteChannelCertificate H N A where
  spatialTranslationInvariant := fun b =>
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_translationInvariant
      H N b A
  swap12Invariant :=
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_swap12Invariant
      H N A
  swap23Invariant :=
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_swap23Invariant
      H N A
  parityEven :=
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_parityInvariant
      H N A
  chargeConjugationEven :=
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_chargeConjugationInvariant
      H N A

end

end MathlibAnalytic
end MGAP4D

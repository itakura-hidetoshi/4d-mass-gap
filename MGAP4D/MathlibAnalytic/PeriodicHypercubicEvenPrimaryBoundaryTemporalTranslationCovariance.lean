import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarTimeTranslationArithmetic
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundarySpatialCylinderReflectionPositivity
import Mathlib.Tactic

/-!
# Exact temporal covariance of the one-sided primary spatial readout

The one-sided primary spatial readout at lattice time `m` is obtained by translating each primary
fixed-slice spatial edge forward by `m` lattice units and reading the same actual finite
configuration.  The existing integer temporal configuration translation is the inverse pullback on
those translated edges.

This file records the resulting exact covariance

`R_{k+m}(T_k A) = R_m(A)`

and the equivalent future-readout identity

`R_{k+m}(A) = R_m(T_{-k} A)`.

The same identities are lifted pointwise to scalar cylinders.  This is pure finite Wilson geometry:
no measure invariance, floor alignment, continuum stationarity, OS contraction, semigroup,
Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Translating the configuration forward by `k` and reading the primary spatial slice at time
`k + m` exactly reproduces the original readout at time `m`. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_configurationTranslation
    {Gauge : Type} [MeasurableSpace Gauge]
    (H m k : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H (k + m)
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (k : ℤ) A) =
      periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H m A := by
  funext e
  change
    periodicHypercubicIntegerTemporalConfigurationTranslation
        (PeriodicHypercubicEvenSideLength H) (k : ℤ) A
        (periodicHypercubicEdgeTranslationEquiv
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicIntegerTemporalDisplacement
            (PeriodicHypercubicEvenSideLength H) ((k + m : ℕ) : ℤ)) e.1) =
      A
        (periodicHypercubicEdgeTranslationEquiv
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicIntegerTemporalDisplacement
            (PeriodicHypercubicEvenSideLength H) (m : ℤ)) e.1)
  have hkm : ((k + m : ℕ) : ℤ) = (k : ℤ) + (m : ℤ) := by
    omega
  rw [hkm]
  rw [periodicHypercubicIntegerTemporalEdgeTranslation_add_apply]
  exact
    periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge
      (PeriodicHypercubicEvenSideLength H) (k : ℤ) A
      (periodicHypercubicEdgeTranslationEquiv
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) (m : ℤ)) e.1)

/-- In particular, translating the source by `k` turns the time-`k` primary readout into the
untranslated primary fixed-slice readout. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_configurationTranslation_self
    {Gauge : Type} [MeasurableSpace Gauge]
    (H k : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H k
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (k : ℤ) A) =
      periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H 0 A := by
  simpa using
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_configurationTranslation
      H 0 k A)

/-- Equivalently, a future readout of `A` is the present readout of the source translated backward
by the same number of lattice units. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_eq_neg_configurationTranslation
    {Gauge : Type} [MeasurableSpace Gauge]
    (H m k : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H (k + m) A =
      periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H m
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A) := by
  have h :=
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_configurationTranslation
      H m k
      (periodicHypercubicIntegerTemporalConfigurationTranslation
        (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A)
  simpa using h

/-- Scalar primary-boundary cylinders satisfy the same exact source covariance. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime_add_configurationTranslation
    {Gauge : Type} [MeasurableSpace Gauge]
    (H m k : ℕ)
    (g : (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H (k + m) g
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (k : ℤ) A) =
      periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H m g A := by
  exact congrArg g
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_configurationTranslation
      H m k A)

/-- Future scalar cylinders are exact pullbacks by the inverse integer source translation. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime_add_eq_neg_configurationTranslation
    {Gauge : Type} [MeasurableSpace Gauge]
    (H m k : ℕ)
    (g : (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H (k + m) g A =
      periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H m g
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A) := by
  exact congrArg g
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_eq_neg_configurationTranslation
      H m k A)

end

end MathlibAnalytic
end MGAP4D

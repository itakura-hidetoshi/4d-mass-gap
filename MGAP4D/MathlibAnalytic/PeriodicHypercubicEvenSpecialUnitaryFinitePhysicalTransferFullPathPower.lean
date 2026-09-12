import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferFullPathIntegrability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finitePhysicalTransferFullPathPowerTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finitePhysicalTransferFullPathPowerCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finitePhysicalTransferFullPathPowerSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finitePhysicalTransferFullPathPowerMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finitePhysicalTransferFullPathPowerBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finitePhysicalTransferFullPathPowerSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The complete two-ended temporal-gauge path amplitude is the matrix
coefficient of the actual physical transfer across the whole positive
half-cylinder.  Since that operator is definitionally the `(h+2)`-fold power
of the physical one-slab transfer at spatial parameter `h+1`, this is the
operator-power closure of the finite Markov/Fubini path construction. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude_eq_physicalPositiveHalfCylinderTransfer_inner
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude
        h N beta f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          (h + 1) N hN beta hbeta f) g := by
  simpa [periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand] using
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_temporalGauge_integral_eq_physicalTransfer
      (h + 1) N hN beta hbeta f g)

/-- The projected physical finite Wilson recursion constructed from the first
Markov slabs is therefore exactly the matrix coefficient of the complete
positive-half physical transfer power. -/
theorem periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude_eq_physicalPositiveHalfCylinderTransfer_inner
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude
        h N hN beta hbeta f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          (h + 1) N hN beta hbeta f) g := by
  calc
    periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude
        h N hN beta hbeta f g =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude
        h N beta f g :=
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude_eq_projectedPhysicalRecursion
        h N hN beta hbeta f g).symm
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          (h + 1) N hN beta hbeta f) g :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude_eq_physicalPositiveHalfCylinderTransfer_inner
        h N hN beta hbeta f g

/-- Equivalently, the literal adjacent-slab Wilson Haar amplitude itself is the
matrix coefficient of the same physical transfer power. -/
theorem periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude_eq_physicalPositiveHalfCylinderTransfer_inner
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
        h N beta f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          (h + 1) N hN beta hbeta f) g := by
  calc
    periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
        h N beta f g =
      periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude
        h N hN beta hbeta f g :=
      (periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude_eq_literal
        h N hN beta hbeta f g).symm
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          (h + 1) N hN beta hbeta f) g :=
      periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude_eq_physicalPositiveHalfCylinderTransfer_inner
        h N hN beta hbeta f g

end

end MathlibAnalytic
end MGAP4D

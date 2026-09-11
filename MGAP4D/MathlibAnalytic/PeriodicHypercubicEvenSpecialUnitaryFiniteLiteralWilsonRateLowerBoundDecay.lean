import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFiniteLiteralWilsonSpectralDecayPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finiteLiteralWilsonRateLowerBoundTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteLiteralWilsonRateLowerBoundCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteLiteralWilsonRateLowerBoundSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteLiteralWilsonRateLowerBoundMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteLiteralWilsonRateLowerBoundBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finiteLiteralWilsonRateLowerBoundSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Any lower bound on the canonical finite-volume excitation decay rate
immediately gives the corresponding literal Wilson path decay exponent.

This theorem is the exact seam needed by a future scale-uniform estimate:
no uniform lower bound is asserted here; one is accepted explicitly as
`hmass`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_norm_le_exp_of_rate_lower_bound
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (mass : ℝ)
    (hmass : mass ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        (h + 1) N hN beta hbeta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (h + 1) N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude
        h N hN beta hbeta f g‖ ≤
      (Real.exp (-(((h + 2 : ℕ) : ℝ)) * mass) * ‖f‖) * ‖g‖ := by
  have htime : 0 ≤ ((h + 2 : ℕ) : ℝ) := by positivity
  have hexp :
      Real.exp
          (-(((h + 2 : ℕ) : ℝ)) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              (h + 1) N hN beta hbeta) ≤
        Real.exp (-(((h + 2 : ℕ) : ℝ)) * mass) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hmass (neg_nonpos.mpr htime)
  exact
    (periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_norm_le_exp_h_add_two
      h N hN beta hbeta f g).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hexp (norm_nonneg f))
        (norm_nonneg g))

/-- The same lower-bound transport for the raw literal Wilson Haar path.  The
physical top-transfer scale is retained exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude_norm_le_physicalNormPow_mul_exp_of_rate_lower_bound
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (mass : ℝ)
    (hmass : mass ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        (h + 1) N hN beta hbeta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (h + 1) N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
        h N beta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (h + 1) N hN beta hbeta‖ ^ (h + 2) *
        ((Real.exp (-(((h + 2 : ℕ) : ℝ)) * mass) * ‖f‖) * ‖g‖) := by
  have htime : 0 ≤ ((h + 2 : ℕ) : ℝ) := by positivity
  have hexp :
      Real.exp
          (-(((h + 2 : ℕ) : ℝ)) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              (h + 1) N hN beta hbeta) ≤
        Real.exp (-(((h + 2 : ℕ) : ℝ)) * mass) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hmass (neg_nonpos.mpr htime)
  have hinner :
      (Real.exp
          (-(((h + 2 : ℕ) : ℝ)) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖ ≤
        (Real.exp (-(((h + 2 : ℕ) : ℝ)) * mass) * ‖f‖) * ‖g‖ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp (norm_nonneg f))
      (norm_nonneg g)
  have htoppos :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (h + 1) N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      (h + 1) N hN beta hbeta
  exact
    (periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude_norm_le_physicalNormPow_mul_exp_h_add_two
      h N hN beta hbeta f g).trans
      (mul_le_mul_of_nonneg_left hinner
        (pow_nonneg htoppos.le (h + 2)))

end

end MathlibAnalytic
end MGAP4D

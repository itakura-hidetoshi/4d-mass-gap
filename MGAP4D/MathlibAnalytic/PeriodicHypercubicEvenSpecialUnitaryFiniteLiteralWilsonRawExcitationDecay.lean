import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFiniteLiteralWilsonExcitationDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finiteLiteralWilsonRawDecayTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteLiteralWilsonRawDecayCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteLiteralWilsonRawDecaySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteLiteralWilsonRawDecayMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteLiteralWilsonRawDecayBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finiteLiteralWilsonRawDecaySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The raw literal finite Wilson Haar path on the full physical excitation
sector is bounded by the exact top-transfer scale times the canonical
finite-volume exponential decay.  Unlike the transfer-normalized theorem, the
factor `‖T_phys‖^n` is retained explicitly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude_norm_le_physicalNormPow_mul_exp
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (h + 1) N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
        h N beta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (h + 1) N hN beta hbeta‖ ^
          periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) *
        ((Real.exp
          (-(periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖) := by
  let t :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      (h + 1) N hN beta hbeta‖
  let n := periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1)
  let Araw :=
    periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
      h N beta
      (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (h + 1) N)
      (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (h + 1) N)
  let Anorm :=
    periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude
      h N hN beta hbeta f g
  have htpos : 0 < t := by
    simpa [t] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        (h + 1) N hN beta hbeta
  have hrecover : t ^ n * Anorm = Araw := by
    change t ^ n * (t⁻¹ ^ n * Araw) = Araw
    rw [← mul_assoc, ← mul_pow]
    rw [mul_inv_cancel₀ htpos.ne', one_pow, one_mul]
  have hdecay :
      ‖Anorm‖ ≤
        (Real.exp
          (-(n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖ := by
    simpa [Anorm, n] using
      (periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_norm_le_exp
        h N hN beta hbeta f g)
  change ‖Araw‖ ≤
    t ^ n *
      ((Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖)
  calc
    ‖Araw‖ = ‖t ^ n * Anorm‖ := by rw [hrecover]
    _ = t ^ n * ‖Anorm‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg htpos.le n)]
    _ ≤ t ^ n *
        ((Real.exp
          (-(n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖) :=
      mul_le_mul_of_nonneg_left hdecay (pow_nonneg htpos.le n)

/-- Audit-visible raw-path estimate with the exact geometric slab count `h+2`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude_norm_le_physicalNormPow_mul_exp_h_add_two
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
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
        ((Real.exp
          (-(((h + 2 : ℕ) : ℝ)) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖) := by
  simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount, Nat.add_assoc] using
    (periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude_norm_le_physicalNormPow_mul_exp
      h N hN beta hbeta f g)

end

end MathlibAnalytic
end MGAP4D

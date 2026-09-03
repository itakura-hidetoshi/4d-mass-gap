import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferFullPathPower
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSNormalizedGramExcitationDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finiteLiteralWilsonExcitationDecayTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteLiteralWilsonExcitationDecayCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteLiteralWilsonExcitationDecaySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteLiteralWilsonExcitationDecayMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteLiteralWilsonExcitationDecayBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finiteLiteralWilsonExcitationDecaySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Vacuum-normalized literal two-ended Wilson amplitude on the full physical
top-eigenspace orthogonal sector.  The factor is the exact inverse top-transfer
power for the `h+2` adjacent slabs in the literal path. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (h + 1) N hN beta hbeta) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      (h + 1) N hN beta hbeta‖⁻¹ ^
      periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) *
    periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
      h N beta
      (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (h + 1) N)
      (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (h + 1) N)

/-- The transfer-normalized literal finite Wilson Haar path is exactly the
matrix coefficient of the normalized physical excitation transfer across the
whole positive half-cylinder. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_eq_excitationTransfer_inner
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (h + 1) N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude
        h N hN beta hbeta f g =
      inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
          (h + 1) N hN beta hbeta f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              (h + 1) N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (h + 1) N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N) := by
  unfold periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude
  rw [periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude_eq_physicalPositiveHalfCylinderTransfer_inner]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator_coe]
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator_apply_eq_invNormPow_smul_physical]
  simp [inner_smul_left]

/-- The literal finite Wilson Haar path, after the canonical vacuum/top-transfer
normalization, inherits the finite-volume exponential excitation bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_norm_le_exp
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (h + 1) N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude
        h N hN beta hbeta f g‖ ≤
      (Real.exp
        (-(periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_eq_excitationTransfer_inner]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator_matrixCoefficient_norm_le_exp
      (h + 1) N hN beta hbeta f g

/-- Audit-visible `h+2` form of the finite-volume Euclidean-path decay bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_norm_le_exp_h_add_two
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (h + 1) N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude
        h N hN beta hbeta f g‖ ≤
      (Real.exp
        (-(((h + 2 : ℕ) : ℝ)) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖ := by
  simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount, Nat.add_assoc] using
    (periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_norm_le_exp
      h N hN beta hbeta f g)

end

end MathlibAnalytic
end MGAP4D

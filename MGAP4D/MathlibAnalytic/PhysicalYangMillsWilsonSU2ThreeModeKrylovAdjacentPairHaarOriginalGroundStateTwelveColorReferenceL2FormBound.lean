import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwelveColorSchurPositiveFrameBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialPhysicalTopOrthogonalGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialUniformGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateSixSpatialMeanProjectionGap
import Mathlib.Tactic

/-!
# P4-Q2-BE: L²-bounded original Wilson Haar reference and physical transfer gap

BD's ORIGINAL physical Wilson mass-weighted right/left twelve-color Haar
reference is bounded above by twelve times the genuine twelve-color conditional
expectation energy. This file proves the distinct Hilbert-space upper bound
`E₁₂(f) ≤ ‖f‖²`, using the exact Pythagorean identity for the already
established family of genuine self-adjoint idempotent color projections.

Consequences:
* the real original reference is bounded by `12 * ‖f‖²` with NO beta cutoff;
* it vanishes whenever the bounded original observable is zero in physical L²;
* the existing G1/G2 physical gap can be packaged with the original reference;
* the certified G4 interval has the explicit volume-free `1/3072` transfer gap.

The reference bound is ONE-SIDED: it does not prove that reference energy
controls physical variance, or construct an L² extension automatically.
Nothing here establishes a spacing-scaled continuum Hamiltonian mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1500000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta
local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta

/-- The normalized genuine twelve-color projection energy is bounded by the
physical joint L² norm squared. This is an all-beta estimate and requires
neither a Schur cutoff nor independence of distinct color projections. -/
theorem p4Q2BE_physicalTwelveResidualEnergy_le_jointNormSq
    (f : J) :
    E12 f ≤ ‖f‖ ^ 2 := by
  have hmean :
      0 ≤ groundStateJointColorMeanProjectedNormSq P12 f := by
    unfold groundStateJointColorMeanProjectedNormSq
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun c _hc => sq_nonneg ‖P12 c f‖))
  have hidentity :
      groundStateJointColorNormalizedResidualEnergy P12 f =
        ‖f‖ ^ 2 - groundStateJointColorMeanProjectedNormSq P12 f :=
    groundStateJointColorNormalizedResidualEnergy_eq_norm_sq_sub_meanProjectedNormSq
      P12
      (fun c =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_idempotent
          H N hN beta hbeta c)
      (fun c =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_symmetric
          H N hN beta hbeta c)
      f
  change groundStateJointColorNormalizedResidualEnergy P12 f ≤ ‖f‖ ^ 2
  rw [hidentity]
  linarith

/-- Bounded concrete Wilson observables have a finite ORIGINAL physical
all-link twelve-color Haar reference whose real scalar is controlled directly
by their physical joint L² norm. No small-beta cutoff is used. -/
theorem p4Q2BE_originalWilsonReferenceReal_le_twelve_jointNormSq
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F ≤
      (12 : ℝ) *
        ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound‖ ^ 2 := by
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  calc
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
        H N hN beta hbeta F ≤
        (12 : ℝ) * E12 f :=
      p4Q2BD_originalWilsonTwelveColorHaarReferenceReal_le_realEnergy
        H N hN beta hbeta F hF bound hbound
    _ ≤ (12 : ℝ) * ‖f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (p4Q2BE_physicalTwelveResidualEnergy_le_jointNormSq
          H N hN beta hbeta f) (by norm_num)

/-- A concrete original-Wilson observable which is zero in the ACTUAL physical
joint L² carrier has zero real-valued Haar reference. This is a necessary
well-definedness check for a subsequent L² quadratic-form extension. -/
theorem p4Q2BE_originalWilsonReferenceReal_eq_zero_of_jointL2_zero
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hzero :
      p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound = 0) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F = 0 := by
  have hnonneg :
      0 ≤ p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
        H N hN beta hbeta F := by
    unfold p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
    exact ENNReal.toReal_nonneg
  have hupper :=
    p4Q2BE_originalWilsonReferenceReal_le_twelve_jointNormSq
      H N hN beta hbeta F hF bound hbound
  rw [hzero, norm_zero] at hupper
  have hle :
      p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
        H N hN beta hbeta F ≤ 0 := by
    nlinarith
  exact le_antisymm hle hnonneg

/-- The same original-Wilson bounded core admits both the cutoff-free L²
reference upper bound and the previously verified strictly positive physical
twelve-color relative frame and top-orthogonal transfer-gap lower bound. -/
theorem p4Q2BE_originalWilsonReference_and_physicalTransferGap
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F ≤
      (12 : ℝ) *
        ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound‖ ^ 2 ∧
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
      s beta *
      ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
        B (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2 ≤
      E12 (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound) ∧
    3 * GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
      s beta / 4 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  exact ⟨
    p4Q2BE_originalWilsonReferenceReal_le_twelve_jointNormSq
      H N hN beta hbeta F hF bound hbound,
    p4Q2BD_boundedOriginalWilsonJointSchurRelativePoincare
      H N hN beta hbeta s hs hcut F hF bound hbound,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialRelativeFrame_implies_transferGap
      H N hN beta hbeta s hs hcut⟩

/-- On the stricter certified G4 high-temperature interval, the genuine
physical transfer gap is at least 1/3072 while the same original Wilson
reference obeys a cutoff-free L² form upper bound. Neither estimate is a
reverse reference Poincare or a continuum spacing-scaled generator gap. -/
theorem p4Q2BE_originalWilsonReference_and_explicitHighTemperatureTransferGap
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff s hs)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F ≤
      (12 : ℝ) *
        ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound‖ ^ 2 ∧
    (1 / 3072 : ℝ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have hframeCut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff
          s hs :=
    hcut.trans
      (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff_le_frameCutoff
        s hs)
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialRelativeFrame_implies_transferGap
      H N hN beta hbeta s hs hframeCut
  have hkappa :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient_le_relativeFrameCoefficient
      s hs beta hbeta hcut
  unfold
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient
    at hkappa
  constructor
  · exact
      p4Q2BE_originalWilsonReferenceReal_le_twelve_jointNormSq
        H N hN beta hbeta F hF bound hbound
  · nlinarith

end
end

end MathlibAnalytic
end MGAP4D

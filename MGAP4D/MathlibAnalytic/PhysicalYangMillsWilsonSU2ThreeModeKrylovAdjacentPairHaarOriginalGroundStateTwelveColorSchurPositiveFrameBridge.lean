import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwelveColorRealEnergyInterface
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialRelativeFrame
import Mathlib.Tactic

/-!
# P4-Q2-BD: actual Wilson reference energy and proven positive Schur frame

This imports the ALREADY THEOREM-BEARING G1 two-sided twelve-spatial relative
Poincare inequality, which has a strictly positive volume-free coefficient on
its explicitly restricted high-temperature beta interval. BD DOES NOT
reconstruct it from a bare Schur norm statement and DOES NOT claim it holds
outside the existing beta cutoff.

BC identifies the actual mass-weighted original Wilson all-link right/left
Haar reference energy with an upper comparison against the SAME physical joint
Hilbert space's real twelve-spatial conditional-expectation residual.

The combined results prove:
* bounded concrete original Wilson Haar reference energies are FINITE;
* their real-valued sum is <= twelve times the real physical 12-color energy;
* independently, the actual physical 12-color energy >= kappa times the
  squared distance from the intrinsic joint constant-line projection;
* the variance can be bounded by the reciprocal of the proven kappa.

The inequalities BOTH bound the physical energy from below. No reverse
comparison of the original Haar reference to the physical variance follows.
In particular this is NOT a continuum spacing-scaled Yang-Mills mass gap.
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

/-- The inherited G1 positive Schur twelve-color coefficient is exactly
1/576 at zero coupling (for every s); no additional volume factor. -/
theorem p4Q2BD_twelveSpatialSchurFrameCoefficient_betaZero
    (s : ℝ) :
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
      s 0 = 1 / 576 := by
  simp [GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient]

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
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta
local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta

/-- The literal original physical ground-state all-link twelve-color Haar
reference sum, now viewed as a real number. The finiteness theorem below
certifies that this conversion never discards an infinite mass on bounded
concrete joint observables. -/
noncomputable def p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
    (F : Joint → ℝ) : ℝ :=
  (∑ c : C12,
    p4Q2BB_twelveColorOriginalHaarReferenceAverage
      H N hN beta hbeta c F).toReal

/-- The actual original Wilson fiber-mass-weighted all-link right/left Haar
reference sum is FINITE for any bounded strongly measurable concrete joint
observable. No fixed positive lower bound on fiber mass is needed. -/
theorem p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∑ c : C12,
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c F) ≠ ∞ := by
  have h :=
    p4Q2BC_originalReference_le_realTwelveNormalizedHilbertEnergy
      H N hN beta hbeta F hF bound hbound
  exact (lt_of_le_of_lt h ENNReal.ofReal_lt_top).ne

/-- The real-valued original Wilson Haar sum is controlled by the REAL
physical joint twelve-color Dirichlet energy, with the exact factor twelve.
This does not reverse the original local-energy inequality. -/
theorem p4Q2BD_originalWilsonTwelveColorHaarReferenceReal_le_realEnergy
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F ≤
      (12 : ℝ) * E12
        (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound) := by
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  have hnonneg :
      0 ≤ p4Q2BC_twelvePhysicalResidualSum H N hN beta hbeta f := by
    unfold p4Q2BC_twelvePhysicalResidualSum
    exact Finset.sum_nonneg (fun c _ => sq_nonneg _)
  have hcmp :=
    p4Q2BC_originalTwelveReferenceSum_le_realPhysicalResidualSum
      H N hN beta hbeta F hF bound hbound
  have hreal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hcmp
  rw [ENNReal.toReal_ofReal hnonneg] at hreal
  change p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F ≤
    p4Q2BC_twelvePhysicalResidualSum H N hN beta hbeta f at hreal
  simpa only [p4Q2BC_realPhysicalResidualSum_eq_twelve_mul_normalized] using hreal

/-- Direct instantiation of the previously verified G1 relative Poincare
frame on the bounded ORIGINAL Wilson joint core, with the true positive
two-boundary Schur cutoff and coefficient. -/
theorem p4Q2BD_boundedOriginalWilsonJointSchurRelativePoincare
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
      s beta *
      ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
        B (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2 ≤
    E12 (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound) := by
  exact
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatial_ordered_relativePoincare
      H N hN beta hbeta s hs hcut
      (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)

/-- The proven strictly positive G1 frame coefficient bounds the entire
joint Hilbert constant-centered squared norm by the reciprocal coefficient
times the actual twelve-color residual. It is NOT a statement about Haar
reference energies controlling variance. -/
theorem p4Q2BD_jointCenteredVariance_le_inverseSchur_mul_realEnergy
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs)
    (f : J) :
    ‖f - B f‖ ^ 2 ≤
      (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
        s beta)⁻¹ * E12 f := by
  have hpos :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient_pos
      s hs beta hbeta hcut
  have hframe :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatial_ordered_relativePoincare
      H N hN beta hbeta s hs hcut f
  have hdiv :
      ‖f - B f‖ ^ 2 ≤
        E12 f /
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
            s beta :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hframe)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- A nonconstant physical joint-L2 vector has a strictly positive twelve
spatial color energy under the explicit beta cutoff, quantitatively by G1. -/
theorem p4Q2BD_nonconstant_joint_twelveColorPhysicalEnergy_pos
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs)
    (f : J) (hnot : f ≠ B f) :
    0 < E12 f := by
  have hpos :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient_pos
      s hs beta hbeta hcut
  have hn : 0 < ‖f - B f‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hnot)
  have hframe :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatial_ordered_relativePoincare
      H N hN beta hbeta s hs hcut f
  exact (mul_pos hpos (pow_pos hn 2)).trans_le hframe

/-- BD MAIN: the true original Wilson mass-weighted 12-color all-link Haar
reference, and the full positive two-boundary Schur joint frame, are BOTH
controlled by the SAME real physical 12-color Hilbert Dirichlet energy.

Neither bound is inverted: there is no unproved claim that the original Haar
reference itself controls the total physical variance or the continuum gap. -/
theorem p4Q2BD_originalWilsonReference_and_positiveTwelveColorSchurFrame
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    0 <
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
        s beta ∧
    (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
      s beta) *
      ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
        B (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2 ≤
      E12 (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound) ∧
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F ≤
      (12 : ℝ) *
        E12 (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound) := by
  refine ⟨
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient_pos
      s hs beta hbeta hcut,
    p4Q2BD_boundedOriginalWilsonJointSchurRelativePoincare
      H N hN beta hbeta s hs hcut F hF bound hbound,
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal_le_realEnergy
      H N hN beta hbeta F hF bound hbound⟩

end
end
end MathlibAnalytic
end MGAP4D

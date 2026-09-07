import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialConditionalExpectation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferScaleUniformDefectBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1500000

section TwoSidedTwelveSpatialFrame

variable (H N : ℕ)
variable (hN : 0 < N)
variable (beta : ℝ)
variable (hbeta : 0 ≤ beta)

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "V" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
    H N hN beta hbeta
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN beta hbeta
local notation "PR" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
    H N hN beta hbeta
local notation "PL" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
    H N hN beta hbeta
local notation "P8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCondExpL2
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta

/-- Two-sided twelve-spatial-color residual with the physical eight-color
normalization `1/8`.

The first summand is exactly the already-concrete six-spatial plus two identity
temporal residual.  The second summand adds the six genuine left-boundary
conditional-expectation residuals with the same `1/8` normalization.  Thus this
is `3/2` times the conventional `1/12` average over the twelve spatial colors,
but it matches the physical eight-color normalization on right-boundary lifts
without any coefficient loss. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy
    (x : J) : ℝ :=
  groundStateJointColorNormalizedResidualEnergy P8 x +
    ((8 : ℝ)⁻¹) * ∑ c : Fin 6, ‖x - PL c x‖ ^ 2

/-- The two-sided twelve-spatial residual is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy_nonneg
    (x : J) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy
        H N hN beta hbeta x := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy
  have hfirst : 0 ≤ groundStateJointColorNormalizedResidualEnergy P8 x :=
    groundStateJointColorNormalizedResidualEnergy_nonneg P8 x
  have hsecond : 0 ≤ ((8 : ℝ)⁻¹) * ∑ c : Fin 6, ‖x - PL c x‖ ^ 2 := by
    positivity
  linarith

/-- On a right-boundary lift, all six left-update residuals vanish exactly.
Hence the two-sided spatial energy reduces to the already-concrete physical
eight-color residual without any comparison loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy_rightBoundary_eq_eightColorResidual
    (u : V) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy
        H N hN beta hbeta (R u) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
        H N hN beta hbeta P8 u := by
  have hleft :
      (∑ c : Fin 6, ‖R u - PL c (R u)‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro c _hc
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2_rightBoundary_fixed
      H N hN beta hbeta c u]
    simp
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy
  rw [hleft, mul_zero, add_zero]
  rfl

/-- A frame estimate for the genuine two-sided joint conditional-expectation
energy on transformed physical top-orthogonal vectors gives the literal raw
physical squared-defect lower bound with the same dimensionless coefficient.

This theorem introduces no frame coefficient: `hframe` is exactly the remaining
model-facing `L²` obligation.  The Wilson marginal / conditional-expectation
comparison itself is lossless (`eta = 1`). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialFrame_mul_transferNormSq_le_rawPhysicalDefect
    (kappa : ℝ)
    (hframe : ∀ x : K,
      kappa * ‖(x : Phys)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy
          H N hN beta hbeta
          (R (U ((x : Phys) : HaarL2))))
    (x : K) :
    kappa * ‖T‖ ^ 2 * ‖(x : Phys)‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
        H N hN beta hbeta x := by
  let f : Phys := x
  let u : V := U (f : HaarL2)
  have hframe_x := hframe x
  have henergy :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy_rightBoundary_eq_eightColorResidual
      H N hN beta hbeta u
  have hframe8 :
      kappa * ‖f‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8 u := by
    simpa [f, u] using hframe_x.trans_eq henergy
  have hscaled :
      kappa * ‖f‖ ^ 2 * ‖T‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8 u * ‖T‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hframe8 (sq_nonneg ‖T‖)
  have hraw0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorResidual_eta_mul_transferNormSq_le_rawPhysicalDefect
      H N hN beta hbeta 1 (by norm_num) (by norm_num) f
  have hraw :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8 u * ‖T‖ ^ 2 ≤
        ‖T‖ ^ 2 * ‖f‖ ^ 2 - ‖T f‖ ^ 2 := by
    simpa [u] using hraw0
  change
    kappa * ‖T‖ ^ 2 * ‖f‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖f‖ ^ 2 - ‖T f‖ ^ 2
  calc
    kappa * ‖T‖ ^ 2 * ‖f‖ ^ 2 =
        kappa * ‖f‖ ^ 2 * ‖T‖ ^ 2 := by ring
    _ ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8 u * ‖T‖ ^ 2 := hscaled
    _ ≤ ‖T‖ ^ 2 * ‖f‖ ^ 2 - ‖T f‖ ^ 2 := hraw

/-- Once the two-sided joint frame coefficient is known on the physical
full-top-orthogonal sector, the existing squared-defect bridge turns it into an
explicit transfer-gap lower bound `kappa / 2`.

The entire remaining quantitative problem is therefore the proof of `hframe`
with a scale-uniform positive `kappa`; Wilson marginal comparison contributes no
additional `eta` loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialFrame_implies_transferGap
    (kappa : ℝ)
    (hkappa0 : 0 ≤ kappa)
    (hkappa1 : kappa ≤ 1)
    (hframe : ∀ x : K,
      kappa * ‖(x : Phys)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialEightNormalizedResidualEnergy
          H N hN beta hbeta
          (R (U ((x : Phys) : HaarL2)))) :
    kappa / 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_rawDefect_lower_bound_implies_transferGap
      H N hN beta hbeta kappa hkappa0 hkappa1
  intro x
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialFrame_mul_transferNormSq_le_rawPhysicalDefect
      H N hN beta hbeta kappa hframe x

end TwoSidedTwelveSpatialFrame

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateSixSpatialMeanProjectionGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialFrame
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- Splitting a twelve-color family into two six-color halves changes only the
normalization: the conventional `1/12` residual is one half of the sum of the
two conventional `1/6` residuals. -/
theorem groundStateJointTwoSixNormalizedResidualEnergy_eq_half
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P Q : Fin 6 → E →L[ℝ] E)
    (x : E) :
    groundStateJointColorNormalizedResidualEnergy
        (fun c : Sum (Fin 6) (Fin 6) => Sum.elim P Q c) x =
      (1 / 2 : ℝ) *
        (groundStateJointColorNormalizedResidualEnergy P x +
          groundStateJointColorNormalizedResidualEnergy Q x) := by
  unfold groundStateJointColorNormalizedResidualEnergy
  simp [Fintype.sum_sum_type]
  ring

section FiniteVolume

variable (H N : ℕ)
variable (hN : 0 < N)
variable (beta : ℝ)
variable (hbeta : 0 ≤ beta)

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta
local notation "V" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
    H N hN beta hbeta
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN beta hbeta
local notation "P6" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
    H N hN beta hbeta
local notation "L6" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
    H N hN beta hbeta
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H N hN beta hbeta

/-- The conventional `1/12` residual energy of the twelve genuine spatial
conditional expectations on the ground-state joint law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    (z : J) : ℝ :=
  groundStateJointColorNormalizedResidualEnergy P12 z

/-- The conventional twelve-spatial residual is exactly one half of the sum of
the right-six and left-six normalized residuals. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_half_right_add_left
    (z : J) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H N hN beta hbeta z =
      (1 / 2 : ℝ) *
        (groundStateJointColorNormalizedResidualEnergy P6 z +
          groundStateJointColorNormalizedResidualEnergy L6 z) := by
  change
    groundStateJointColorNormalizedResidualEnergy P12 z =
      (1 / 2 : ℝ) *
        (groundStateJointColorNormalizedResidualEnergy P6 z +
          groundStateJointColorNormalizedResidualEnergy L6 z)
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2]
    using groundStateJointTwoSixNormalizedResidualEnergy_eq_half P6 L6 z

/-- On a right-boundary lift all six left updates are exactly fixed.  Therefore
the genuine conventional twelve-color residual is exactly one half of the
six-spatial residual, with no comparison loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_rightBoundary_eq_half_sixSpatial
    (u : V) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H N hN beta hbeta (R u) =
      (1 / 2 : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
          H N hN beta hbeta u := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_half_right_add_left]
  have hleft : groundStateJointColorNormalizedResidualEnergy L6 (R u) = 0 := by
    unfold groundStateJointColorNormalizedResidualEnergy
    simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2_rightBoundary_fixed]
  rw [hleft, add_zero]
  rfl

/-- A conventional twelve-spatial Poincare estimate on the physical
right-boundary lifts gives the six-spatial frame coefficient `2 * κ`.

The harmless normalization hypothesis `κ ≤ 1/2` merely ensures the resulting
six-color coefficient lies in `[0,1]`; any positive Poincare coefficient can be
reduced to one satisfying this bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_implies_sixSpatialFrame
    (κ : ℝ)
    (hκ0 : 0 ≤ κ)
    (hκhalf : κ ≤ 1 / 2)
    (hpoincare : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
          H N hN beta hbeta
          (R (U ((x : G) : HaarL2)))) :
    ∀ x : K,
      (2 * κ) * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
          H N hN beta hbeta (U ((x : G) : HaarL2)) := by
  intro x
  have hx := hpoincare x
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_rightBoundary_eq_half_sixSpatial]
    at hx
  nlinarith

/-- A positive conventional twelve-spatial Poincare coefficient on the actual
right-boundary physical sector gives the explicit physical transfer-gap lower
bound `3 * κ / 4`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_implies_transferGap
    (κ : ℝ)
    (hκ0 : 0 ≤ κ)
    (hκhalf : κ ≤ 1 / 2)
    (hpoincare : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
          H N hN beta hbeta
          (R (U ((x : G) : HaarL2)))) :
    3 * κ / 4 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have hframe :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_implies_sixSpatialFrame
      H N hN beta hbeta κ hκ0 hκhalf hpoincare
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_implies_transferGap
      H N hN beta hbeta (2 * κ) (by positivity) (by nlinarith) hframe
  nlinarith

/-- Strictly positive twelve-spatial Poincare coercivity on the physical
right-boundary sector implies a positive finite-volume physical transfer gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_positive_transferGap
    (κ : ℝ)
    (hκ : 0 < κ)
    (hκhalf : κ ≤ 1 / 2)
    (hpoincare : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
          H N hN beta hbeta
          (R (U ((x : G) : HaarL2)))) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta := by
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_implies_transferGap
      H N hN beta hbeta κ hκ.le hκhalf hpoincare
  have hpos : 0 < 3 * κ / 4 :=
    div_pos (mul_pos (by norm_num) hκ) (by norm_num)
  exact lt_of_lt_of_le hpos hgap

end FiniteVolume

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- The next model-facing quantitative target stated on the genuine two-sided
joint dynamics: a single positive scale-independent conventional `1/12`
Poincare coefficient on the physical right-boundary lifts. -/
def PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateTwelveSpatialPoincareOnPhysicalRightLifts : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 2 ∧
    ∀ (n : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)),
      κ *
          ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
          (halfExtent n) N hN (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
            (halfExtent n) N hN (beta n) (hbeta n)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
              (halfExtent n) N hN (beta n) (hbeta n)
              ((x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                (halfExtent n) N) :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                    (halfExtent n) N))))

/-- A scale-independent positive conventional twelve-spatial Poincare
coefficient on the physical right-boundary lifts produces a uniform positive
physical transfer gap, with explicit lower bound `3 * κ / 4`. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformGroundStateTwelveSpatialPoincareOnPhysicalRightLifts_implies_uniformTransferGap
    (hpoincare :
      PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateTwelveSpatialPoincareOnPhysicalRightLifts
        halfExtent N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta := by
  rcases hpoincare with ⟨κ, hκ, hκhalf, hpoincare⟩
  have hpos : 0 < 3 * κ / 4 :=
    div_pos (mul_pos (by norm_num) hκ) (by norm_num)
  refine ⟨3 * κ / 4, hpos, ?_⟩
  intro n
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_implies_transferGap
      (halfExtent n) N hN (beta n) (hbeta n)
      κ hκ.le hκhalf (fun x => hpoincare n x)

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D

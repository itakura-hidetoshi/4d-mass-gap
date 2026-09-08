import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateConcreteEightColorFrameGap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- Extending six spatial projections by two identity temporal colors changes
only the normalization: the `Fin 8` residual energy is exactly `3/4` of the
`Fin 6` residual energy.  This is the exact temporal-gauge bookkeeping needed
before any quantitative six-spatial frame estimate is introduced. -/
theorem groundStateJointSixSpatialTwoTemporalFamily_normalizedResidualEnergy
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (Psp : Fin 6 → E →L[ℝ] E)
    (x : E) :
    groundStateJointColorNormalizedResidualEnergy
        (groundStateJointSixSpatialTwoTemporalFamily Psp) x =
      (3 / 4 : ℝ) * groundStateJointColorNormalizedResidualEnergy Psp x := by
  unfold groundStateJointColorNormalizedResidualEnergy
  simp [groundStateJointSixSpatialTwoTemporalFamily, Fin.sum_univ_succ]
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
local notation "P8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCondExpL2
    H N hN beta hbeta

/-- The normalized residual energy of the six genuine spatial conditional
expectations on the ground-state joint law.  Its normalization is exactly
`1/6`, independently of the lattice volume. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
    (u : V) : ℝ :=
  groundStateJointColorNormalizedResidualEnergy P6 (R u)

/-- For the literal concrete family, the existing eight-color residual is
exactly `3/4` of the six-spatial residual.  The two temporal identity colors
contribute zero, and no estimate is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorResidual_eq_three_fourths_sixSpatial
    (u : V) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
        H N hN beta hbeta P8 u =
      (3 / 4 : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
          H N hN beta hbeta u := by
  change
    groundStateJointColorNormalizedResidualEnergy
        (groundStateJointSixSpatialTwoTemporalFamily P6) (R u) =
      (3 / 4 : ℝ) * groundStateJointColorNormalizedResidualEnergy P6 (R u)
  exact groundStateJointSixSpatialTwoTemporalFamily_normalizedResidualEnergy P6 (R u)

/-- A frame estimate stated only for the six genuine spatial conditional
expectations gives the physical transfer-gap lower bound `3 * κ / 8`.

The factor `3/4` is solely the six-versus-eight color normalization, while the
additional factor `1/2` is the already-proved squared-defect-to-linear-gap
conversion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_implies_transferGap
    (κ : ℝ)
    (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
          H N hN beta hbeta
          (U ((x : G) : HaarL2))) :
    3 * κ / 8 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have hcoeff0 : 0 ≤ (3 / 4 : ℝ) * κ := by positivity
  have hcoeff1 : (3 / 4 : ℝ) * κ ≤ 1 := by nlinarith
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorFrame_implies_transferGap
      H N hN beta hbeta ((3 / 4 : ℝ) * κ) hcoeff0 hcoeff1
      (fun x => by
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorResidual_eq_three_fourths_sixSpatial]
        exact mul_le_mul_of_nonneg_left (hframe x) (by norm_num))
  nlinarith

/-- Positive six-spatial ground-state frame coercivity implies a positive
finite-volume physical transfer gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_positive_transferGap
    (κ : ℝ)
    (hκ : 0 < κ)
    (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
          H N hN beta hbeta
          (U ((x : G) : HaarL2))) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta := by
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_implies_transferGap
      H N hN beta hbeta κ hκ.le hκ1 hframe
  have hpos : 0 < 3 * κ / 8 := by positivity
  exact lt_of_lt_of_le hpos hgap

end FiniteVolume

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- The sharpened remaining model-facing target: a single positive
scale-independent frame constant for the six genuine spatial conditional
expectations, with the natural `1/6` color normalization and no temporal
identity slots. -/
def PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateSixSpatialFrame : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∀ (n : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)),
      κ *
          ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
          (halfExtent n) N hN (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            (halfExtent n) N hN (beta n) (hbeta n)
            ((x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N) :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  (halfExtent n) N)))

/-- A positive scale-independent six-spatial frame constant produces a uniform
positive physical transfer gap.  The explicit output constant is `3 * κ / 8`. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformGroundStateSixSpatialFrame_implies_uniformTransferGap
    (hframe :
      PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateSixSpatialFrame
        halfExtent N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta := by
  rcases hframe with ⟨κ, hκ, hκ1, hframe⟩
  refine ⟨3 * κ / 8, by positivity, ?_⟩
  intro n
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_implies_transferGap
      (halfExtent n) N hN (beta n) (hbeta n)
      κ hκ.le hκ1 (fun x => hframe n x)

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D

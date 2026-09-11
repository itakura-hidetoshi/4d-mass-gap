import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixSpatialConditionalExpectation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferScaleUniformDefectBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

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
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "P8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCondExpL2
    H N hN beta hbeta

/-- A frame estimate for the literal ground-state six-spatial conditional
expectations (with the two temporal slots equal to the identity) gives the
canonical finite-volume top-orthogonal transfer gap with coefficient `κ / 2`.

This removes the abstract bounded-color family and the separate raw-comparison
hypothesis from the final model-facing route.  The only analytic input left is
the frame inequality for the already-concrete ground-state conditional
expectations on the physical top-orthogonal sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorFrame_implies_transferGap
    (κ : ℝ)
    (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8
          (U ((x : G) : HaarL2))) :
    κ / 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_rawDefect_lower_bound_implies_transferGap
      H N hN beta hbeta κ hκ0 hκ1
  intro x
  have hscaled :
      κ * ‖(x : G)‖ ^ 2 * ‖T‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8
          (U ((x : G) : HaarL2)) * ‖T‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (hframe x) (sq_nonneg ‖T‖)
  have hraw0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorResidual_eta_mul_transferNormSq_le_rawPhysicalDefect
      H N hN beta hbeta 1 (by norm_num) (by norm_num) (x : G)
  have hraw :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8
          (U ((x : G) : HaarL2)) * ‖T‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x := by
    simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect]
      using hraw0
  calc
    κ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 =
        κ * ‖(x : G)‖ ^ 2 * ‖T‖ ^ 2 := by ring
    _ ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8
          (U ((x : G) : HaarL2)) * ‖T‖ ^ 2 := hscaled
    _ ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x := hraw

/-- Positive concrete ground-state color-frame coercivity implies a positive
finite-volume physical transfer gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorFrame_positive_transferGap
    (κ : ℝ)
    (hκ : 0 < κ)
    (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8
          (U ((x : G) : HaarL2))) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta := by
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorFrame_implies_transferGap
      H N hN beta hbeta κ hκ.le hκ1 hframe
  have : 0 < κ / 2 := by positivity
  exact lt_of_lt_of_le this hgap

end FiniteVolume

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- The exact remaining scale-uniform ground-state frame target after the raw
physical comparison has been discharged by the concrete six-spatial/two-
temporal conditional-expectation family.

The coefficient is dimensionless and the color normalization is fixed at
`1 / 8`, so the statement introduces no lattice-volume normalization. -/
def PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateConcreteEightColorFrame : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∀ (n : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)),
      κ *
          ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          (halfExtent n) N hN (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCondExpL2
            (halfExtent n) N hN (beta n) (hbeta n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            (halfExtent n) N hN (beta n) (hbeta n)
            ((x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N) :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  (halfExtent n) N)))

/-- A single positive scale-independent frame constant for the literal
six-spatial ground-state conditional expectations gives a uniform positive
physical top-eigenspace transfer gap.  The explicit output constant is
`κ / 2`. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformGroundStateConcreteEightColorFrame_implies_uniformTransferGap
    (hframe :
      PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateConcreteEightColorFrame
        halfExtent N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta := by
  rcases hframe with ⟨κ, hκ, hκ1, hframe⟩
  refine ⟨κ / 2, by positivity, ?_⟩
  intro n
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorFrame_implies_transferGap
      (halfExtent n) N hN (beta n) (hbeta n)
      κ hκ.le hκ1 (fun x => hframe n x)

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D

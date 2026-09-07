import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateDoobEightColorDefect
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- Extend six genuine spatial projections to the eight-color boundary family by
using the identity on the two temporal colors.  On the temporal-gauge-fixed
one-slab boundary carrier there are no temporal link variables left to update,
so these two colors contribute zero residual exactly. -/
def groundStateJointSixSpatialTwoTemporalFamily
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (Psp : Fin 6 → E →L[ℝ] E) : Fin 8 → E →L[ℝ] E :=
  fun c =>
    if h : c.val < 6 then
      Psp ⟨c.val, h⟩
    else
      ContinuousLinearMap.id ℝ E

/-- Idempotence of the six spatial projections extends automatically across the
two identity temporal colors. -/
theorem groundStateJointSixSpatialTwoTemporalFamily_idempotent
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (Psp : Fin 6 → E →L[ℝ] E)
    (hPid : ∀ c, (Psp c).comp (Psp c) = Psp c)
    (c : Fin 8) :
    (groundStateJointSixSpatialTwoTemporalFamily Psp c).comp
        (groundStateJointSixSpatialTwoTemporalFamily Psp c) =
      groundStateJointSixSpatialTwoTemporalFamily Psp c := by
  by_cases h : c.val < 6
  · simpa [groundStateJointSixSpatialTwoTemporalFamily, h] using
      hPid ⟨c.val, h⟩
  · ext x
    simp [groundStateJointSixSpatialTwoTemporalFamily, h]

/-- Symmetry of the six spatial projections extends automatically across the
two identity temporal colors. -/
theorem groundStateJointSixSpatialTwoTemporalFamily_symmetric
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (Psp : Fin 6 → E →L[ℝ] E)
    (hPsymm : ∀ c, ((Psp c : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric)
    (c : Fin 8) :
    ((groundStateJointSixSpatialTwoTemporalFamily Psp c : E →L[ℝ] E) :
        E →ₗ[ℝ] E).IsSymmetric := by
  by_cases h : c.val < 6
  · simpa [groundStateJointSixSpatialTwoTemporalFamily, h] using
      hPsymm ⟨c.val, h⟩
  · intro x y
    simp [groundStateJointSixSpatialTwoTemporalFamily, h]

/-- Any vector fixed by every spatial projection is fixed by the full family;
the two temporal colors are identities. -/
theorem groundStateJointSixSpatialTwoTemporalFamily_fixed
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (Psp : Fin 6 → E →L[ℝ] E)
    (z : E)
    (hfixed : ∀ c, Psp c z = z)
    (c : Fin 8) :
    groundStateJointSixSpatialTwoTemporalFamily Psp c z = z := by
  by_cases h : c.val < 6
  · simpa [groundStateJointSixSpatialTwoTemporalFamily, h] using
      hfixed ⟨c.val, h⟩
  · simp [groundStateJointSixSpatialTwoTemporalFamily, h]

section GroundStateDoobSixSpatialTwoTemporal

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "V" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
    H N hN beta hbeta
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "Q" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
    H N hN beta hbeta
local notation "D" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN beta hbeta

/-- The eight-color Doob-defect comparison needs genuine data only for the six
spatial colors: the two temporal colors are discharged by identity projections. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialTwoTemporalResidual_le_doobDefect
    (Psp : Fin 6 → J →L[ℝ] J)
    (hPid : ∀ c, (Psp c).comp (Psp c) = Psp c)
    (hPsymm : ∀ c, ((Psp c : J →L[ℝ] J) : J →ₗ[ℝ] J).IsSymmetric)
    (hfixed : ∀ c u, Psp c (Q (R u)) = Q (R u))
    (u : V) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
        H N hN beta hbeta
        (groundStateJointSixSpatialTwoTemporalFamily Psp) u ≤
      ‖u‖ ^ 2 - ‖D u‖ ^ 2 := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_le_doobDefect
      H N hN beta hbeta
      (groundStateJointSixSpatialTwoTemporalFamily Psp)
  · intro c
    exact groundStateJointSixSpatialTwoTemporalFamily_idempotent Psp hPid c
  · intro c
    exact groundStateJointSixSpatialTwoTemporalFamily_symmetric Psp hPsymm c
  · intro c v
    exact groundStateJointSixSpatialTwoTemporalFamily_fixed
      Psp (Q (R v)) (fun s => hfixed s v) c

/-- Loss-factor version of the six-spatial/two-temporal reduction.  This is the
form used by the physical squared-defect route. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialTwoTemporalResidual_eta_le_doobDefect
    (Psp : Fin 6 → J →L[ℝ] J)
    (hPid : ∀ c, (Psp c).comp (Psp c) = Psp c)
    (hPsymm : ∀ c, ((Psp c : J →L[ℝ] J) : J →ₗ[ℝ] J).IsSymmetric)
    (hfixed : ∀ c u, Psp c (Q (R u)) = Q (R u))
    (eta : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1)
    (u : V) :
    eta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta
          (groundStateJointSixSpatialTwoTemporalFamily Psp) u ≤
      ‖u‖ ^ 2 - ‖D u‖ ^ 2 := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_eta_le_doobDefect
      H N hN beta hbeta
      (groundStateJointSixSpatialTwoTemporalFamily Psp)
  · intro c
    exact groundStateJointSixSpatialTwoTemporalFamily_idempotent Psp hPid c
  · intro c
    exact groundStateJointSixSpatialTwoTemporalFamily_symmetric Psp hPsymm c
  · intro c v
    exact groundStateJointSixSpatialTwoTemporalFamily_fixed
      Psp (Q (R v)) (fun s => hfixed s v) c
  · exact heta0
  · exact heta1
  · exact u

end GroundStateDoobSixSpatialTwoTemporal

end

end MathlibAnalytic
end MGAP4D

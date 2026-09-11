import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixSpatialConditionalExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- The normalized joint finite-color residual is invariant under subtraction
of a vector fixed by every color projection.  This is the quotient-space
centering identity needed before asking for a genuine joint-frame/Poincare
estimate. -/
theorem groundStateJointColorNormalizedResidualEnergy_sub_of_fixed
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (x z : E)
    (hz : ∀ c, P c z = z) :
    groundStateJointColorNormalizedResidualEnergy P (x - z) =
      groundStateJointColorNormalizedResidualEnergy P x := by
  unfold groundStateJointColorNormalizedResidualEnergy
  apply congrArg
    (fun s : ℝ => ((Fintype.card C : ℝ)⁻¹) * s)
  apply Finset.sum_congr rfl
  intro c _
  have hres : x - z - P c (x - z) = x - P c x := by
    rw [map_sub, hz c]
    abel
  rw [hres]

section ConcreteJointCenteredFrame

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
local notation "Q" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
    H N hN beta hbeta
local notation "D" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
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

/-- The squared distance from the right-boundary lift to the coarse
left-boundary conditional-expectation image is exactly the Doob squared
defect.  This exposes the centered norm already used internally by the
finite-color comparison. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift_sub_coarse_norm_sq_eq_doobDefect
    (u : V) :
    ‖R u - Q (R u)‖ ^ 2 = ‖u‖ ^ 2 - ‖D u‖ ^ 2 := by
  have hPyth :
      ‖R u - Q (R u)‖ ^ 2 = ‖R u‖ ^ 2 - ‖Q (R u)‖ ^ 2 :=
    realHilbert_groundStateJoint_projection_residual_sq_eq_defect
      Q
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_idempotent
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_inner_symm
        H N hN beta hbeta)
      (R u)
  have hR : ‖R u‖ ^ 2 = ‖u‖ ^ 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift_norm_sq
      H N hN beta hbeta u
  have hQnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_rightBoundary_norm
      H N hN beta hbeta u
  have hQ : ‖Q (R u)‖ ^ 2 = ‖D u‖ ^ 2 := by
    have hnorm : ‖Q (R u)‖ = ‖D u‖ := by
      simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift] using
        hQnorm
    rw [hnorm]
  calc
    ‖R u - Q (R u)‖ ^ 2 = ‖R u‖ ^ 2 - ‖Q (R u)‖ ^ 2 := hPyth
    _ = ‖u‖ ^ 2 - ‖D u‖ ^ 2 := by rw [hR, hQ]

/-- Centering the concrete six-spatial plus two-temporal joint residual by the
coarse left-boundary image does not change it, because every one of the eight
concrete projections fixes that image. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorResidual_centered_eq
    (u : V) :
    groundStateJointColorNormalizedResidualEnergy P8
        (R u - Q (R u)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
        H N hN beta hbeta P8 u := by
  have hfixed : ∀ c : Fin 8, P8 c (Q (R u)) = Q (R u) := by
    intro c
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCondExpL2_coarse_fixed
        H N hN beta hbeta c u
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy] using
    groundStateJointColorNormalizedResidualEnergy_sub_of_fixed
      P8 (R u) (Q (R u)) hfixed

/-- A centered frame estimate for the concrete joint eight-color family feeds
straight into the literal raw physical squared defect with no additional
comparison loss: the already-proved concrete residual comparison is used at
`eta = 1`.

Thus after this theorem the only model-facing quantitative input is the frame
coefficient `kappa` on the genuine ground-state joint carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCenteredFrame_mul_transferNormSq_le_rawPhysicalDefect
    (kappa : ℝ)
    (hframe : ∀ u : V,
      kappa * ‖R u - Q (R u)‖ ^ 2 ≤
        groundStateJointColorNormalizedResidualEnergy P8
          (R u - Q (R u)))
    (f : Phys) :
    kappa *
        ‖R (U (f : HaarL2)) - Q (R (U (f : HaarL2)))‖ ^ 2 *
        ‖T‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖f‖ ^ 2 - ‖T f‖ ^ 2 := by
  let u : V := U (f : HaarL2)
  have hframe_u := hframe u
  have hcenter :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorResidual_centered_eq
      H N hN beta hbeta u
  rw [hcenter] at hframe_u
  have hscaled :
      kappa * ‖R u - Q (R u)‖ ^ 2 * ‖T‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8 u * ‖T‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right hframe_u (sq_nonneg ‖T‖)
  have hraw0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorResidual_eta_mul_transferNormSq_le_rawPhysicalDefect
      H N hN beta hbeta 1 (by norm_num) (by norm_num) f
  have hraw :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P8 u * ‖T‖ ^ 2 ≤
        ‖T‖ ^ 2 * ‖f‖ ^ 2 - ‖T f‖ ^ 2 := by
    simpa [u] using hraw0
  simpa [u] using hscaled.trans hraw

/-- Equivalent Doob-defect presentation of the centered-frame reduction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCenteredFrame_doobDefect_mul_transferNormSq_le_rawPhysicalDefect
    (kappa : ℝ)
    (hframe : ∀ u : V,
      kappa * ‖R u - Q (R u)‖ ^ 2 ≤
        groundStateJointColorNormalizedResidualEnergy P8
          (R u - Q (R u)))
    (f : Phys) :
    kappa *
        (‖U (f : HaarL2)‖ ^ 2 - ‖D (U (f : HaarL2))‖ ^ 2) *
        ‖T‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖f‖ ^ 2 - ‖T f‖ ^ 2 := by
  have hmain :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCenteredFrame_mul_transferNormSq_le_rawPhysicalDefect
      H N hN beta hbeta kappa hframe f
  have hcenter :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift_sub_coarse_norm_sq_eq_doobDefect
      H N hN beta hbeta (U (f : HaarL2))
  rw [hcenter] at hmain
  exact hmain

end ConcreteJointCenteredFrame

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateBoundaryProjection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- Normalized residual energy for a finite family of orthogonal projections on
the ground-state joint Hilbert carrier.  This definition is intentionally kept
inside the ground-state lane so no global-Gibbs carrier import is required. -/
def groundStateJointColorNormalizedResidualEnergy
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (x : E) : ℝ :=
  ((Fintype.card C : ℝ)⁻¹) * ∑ c : C, ‖x - P c x‖ ^ 2

/-- Ground-state joint finite-color residual energy is nonnegative. -/
theorem groundStateJointColorNormalizedResidualEnergy_nonneg
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (x : E) :
    0 ≤ groundStateJointColorNormalizedResidualEnergy P x := by
  unfold groundStateJointColorNormalizedResidualEnergy
  positivity

/-- A self-adjoint idempotent is the metric projection against every vector
already fixed by it. -/
theorem realHilbert_groundStateJoint_projection_residual_sq_le_of_fixed
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E)
    (hPid : P.comp P = P)
    (hPsymm : (P : E →ₗ[ℝ] E).IsSymmetric)
    (x z : E)
    (hz : P z = z) :
    ‖x - P x‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
  have hPpx : P (P x) = P x := by
    have h := congrArg (fun Q : E →L[ℝ] E => Q x) hPid
    simpa using h
  have hfixedDiff : P (P x - z) = P x - z := by
    rw [map_sub, hPpx, hz]
  have horth : inner ℝ (x - P x) (P x - z) = 0 := by
    rw [inner_sub_left]
    have hs :
        inner ℝ (P x) (P x - z) =
          inner ℝ x (P (P x - z)) :=
      hPsymm x (P x - z)
    rw [hs, hfixedDiff, sub_self]
  have hdecomp : x - z = (x - P x) + (P x - z) := by
    abel
  rw [hdecomp, norm_add_sq_real, horth]
  nlinarith [sq_nonneg ‖P x - z‖]

/-- Pythagoras for a self-adjoint idempotent on the joint Hilbert carrier. -/
theorem realHilbert_groundStateJoint_projection_residual_sq_eq_defect
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (Q : E →L[ℝ] E)
    (hQid : Q.comp Q = Q)
    (hQsymm : (Q : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) :
    ‖x - Q x‖ ^ 2 = ‖x‖ ^ 2 - ‖Q x‖ ^ 2 := by
  have hQQ : Q (Q x) = Q x := by
    have h := congrArg (fun R : E →L[ℝ] E => R x) hQid
    simpa using h
  have hs : inner ℝ (Q x) (Q x) = inner ℝ x (Q (Q x)) :=
    hQsymm x (Q x)
  rw [hQQ] at hs
  have hinner : inner ℝ x (Q x) = ‖Q x‖ ^ 2 := by
    calc
      inner ℝ x (Q x) = inner ℝ (Q x) (Q x) := hs.symm
      _ = ‖Q x‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [norm_sub_sq_real, hinner]
  ring

/-- Averaging finitely many joint conditional-expectation residuals cannot
exceed one coarser conditional-expectation residual when the coarse image is
fixed by every color projection. -/
theorem groundStateJointColorNormalizedResidualEnergy_le_coarseResidual_sq
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric)
    (Q : E →L[ℝ] E)
    (x : E)
    (hQfixed : ∀ c, P c (Q x) = Q x) :
    groundStateJointColorNormalizedResidualEnergy P x ≤
      ‖x - Q x‖ ^ 2 := by
  have hterm : ∀ c : C, ‖x - P c x‖ ^ 2 ≤ ‖x - Q x‖ ^ 2 := by
    intro c
    exact realHilbert_groundStateJoint_projection_residual_sq_le_of_fixed
      (P c) (hPid c) (hPsymm c) x (Q x) (hQfixed c)
  have hsum :
      (∑ c : C, ‖x - P c x‖ ^ 2) ≤
        (Fintype.card C : ℝ) * ‖x - Q x‖ ^ 2 := by
    calc
      (∑ c : C, ‖x - P c x‖ ^ 2) ≤
          ∑ _c : C, ‖x - Q x‖ ^ 2 :=
        Finset.sum_le_sum fun c _hc => hterm c
      _ = (Fintype.card C : ℝ) * ‖x - Q x‖ ^ 2 := by simp
  have hcard : 0 < (Fintype.card C : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  unfold groundStateJointColorNormalizedResidualEnergy
  calc
    (Fintype.card C : ℝ)⁻¹ * (∑ c : C, ‖x - P c x‖ ^ 2) ≤
        (Fintype.card C : ℝ)⁻¹ *
          ((Fintype.card C : ℝ) * ‖x - Q x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖x - Q x‖ ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

section GroundStateDoobMarginal

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "V" =>
  Lp ℝ 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta)
local notation "J" =>
  Lp ℝ 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta)
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
    H N hN beta hbeta
local notation "Q" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
    H N hN beta hbeta
local notation "D" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
    H N hN beta hbeta
local notation "Color" => Fin 8

/-- The right-boundary pullback as a continuous linear isometric lift into the
genuine ground-state one-slab joint Hilbert carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift :
    V →L[ℝ] J :=
  R.toContinuousLinearMap

/-- Exact norm-square preservation of the ground-state right-boundary lift. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift_norm_sq
    (u : V) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
        H N hN beta hbeta u‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift]
  rw [R.norm_map]

/-- The actual eight-color residual energy on the ground-state one-slab joint
carrier.  The normalization is exactly `1/8` through the fixed type `Fin 8`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
    (P : Color → J →L[ℝ] J)
    (u : V) : ℝ :=
  groundStateJointColorNormalizedResidualEnergy P
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
      H N hN beta hbeta u)

/-- Any genuine eight-color orthogonal conditional-expectation family on the
joint law whose fixed ranges contain the coarse left-boundary image has its
normalized residual energy bounded by the exact Doob squared defect. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_le_doobDefect
    (P : Color → J →L[ℝ] J)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : J →L[ℝ] J) : J →ₗ[ℝ] J).IsSymmetric)
    (hfixed : ∀ c u,
      P c (Q (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
        H N hN beta hbeta u)) =
        Q (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
          H N hN beta hbeta u))
    (u : V) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
        H N hN beta hbeta P u ≤
      ‖u‖ ^ 2 - ‖D u‖ ^ 2 := by
  let y :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
      H N hN beta hbeta u
  have hMarginal :
      groundStateJointColorNormalizedResidualEnergy P y ≤ ‖y - Q y‖ ^ 2 :=
    groundStateJointColorNormalizedResidualEnergy_le_coarseResidual_sq
      P hPid hPsymm Q y (fun c => hfixed c u)
  have hPyth :
      ‖y - Q y‖ ^ 2 = ‖y‖ ^ 2 - ‖Q y‖ ^ 2 :=
    realHilbert_groundStateJoint_projection_residual_sq_eq_defect
      Q
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_idempotent
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_inner_symm
        H N hN beta hbeta)
      y
  have hy : ‖y‖ ^ 2 = ‖u‖ ^ 2 := by
    simpa [y] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift_norm_sq
        H N hN beta hbeta u
  have hnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_rightBoundary_norm
      H N hN beta hbeta u
  have hQsq : ‖Q y‖ ^ 2 = ‖D u‖ ^ 2 := by
    have hnorm' : ‖Q y‖ = ‖D u‖ := by
      simpa [y,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift] using hnorm
    rw [hnorm']
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
  change groundStateJointColorNormalizedResidualEnergy P y ≤ _
  calc
    groundStateJointColorNormalizedResidualEnergy P y ≤ ‖y - Q y‖ ^ 2 := hMarginal
    _ = ‖y‖ ^ 2 - ‖Q y‖ ^ 2 := hPyth
    _ = ‖u‖ ^ 2 - ‖D u‖ ^ 2 := by rw [hy, hQsq]

/-- The same concrete Doob comparison with a retained loss factor
`eta ∈ [0,1]`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_eta_le_doobDefect
    (P : Color → J →L[ℝ] J)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : J →L[ℝ] J) : J →ₗ[ℝ] J).IsSymmetric)
    (hfixed : ∀ c u,
      P c (Q (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
        H N hN beta hbeta u)) =
        Q (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
          H N hN beta hbeta u))
    (eta : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1)
    (u : V) :
    eta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P u ≤
      ‖u‖ ^ 2 - ‖D u‖ ^ 2 := by
  have hmain :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_le_doobDefect
      H N hN beta hbeta P hPid hPsymm hfixed u
  have hE0 :
      0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
        H N hN beta hbeta P u := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
    exact groundStateJointColorNormalizedResidualEnergy_nonneg P _
  have hetaE :
      eta *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
            H N hN beta hbeta P u ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P u := by
    nlinarith
  exact hetaE.trans hmain

end GroundStateDoobMarginal

end

end MathlibAnalytic
end MGAP4D

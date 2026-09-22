import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateSixSpatialMeanProjectionGap
import Mathlib.Tactic

/-!
# Genuine six-spatial ground-state random-scan Rayleigh receiver

The six spatial one-link conditional expectations are already realized as
self-adjoint idempotent continuous linear maps on the genuine ground-state
joint L2 carrier.

This file forms their normalized random-scan average and identifies its
Rayleigh quadratic form exactly with the previously introduced mean projected
squared norm. Consequently:

* six-spatial frame/Poincare coercivity is exactly equivalent to a centered
  Rayleigh contraction for this genuine random-scan operator;
* a uniform Rayleigh contraction factor q < 1 feeds directly into the already
  proved physical transfer-gap receiver with lower bound 3(1-q)/8.

No Dobrushin-to-Rayleigh implication is asserted here. The remaining
model-facing analytic task is precisely to prove this Rayleigh contraction
from the physical interdependence/influence estimates.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

/-- Normalized average of a finite family of continuous linear maps. For a
family of conditional-expectation projections this is the genuine random-scan
operator. -/
noncomputable def groundStateJointColorRandomScanOperator
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E) :
    E →L[ℝ] E :=
  ((Fintype.card C : ℝ)⁻¹) • ∑ c : C, P c

@[simp] theorem groundStateJointColorRandomScanOperator_apply
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (x : E) :
    groundStateJointColorRandomScanOperator P x =
      ((Fintype.card C : ℝ)⁻¹) • ∑ c : C, P c x := by
  simp [groundStateJointColorRandomScanOperator]

/-- A self-adjoint idempotent has Rayleigh form equal to the squared norm of
its projected vector. -/
theorem realHilbert_groundStateJoint_projection_inner_self_eq_norm_sq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E)
    (hPid : P.comp P = P)
    (hPsymm : ((P : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) :
    inner ℝ (P x) x = ‖P x‖ ^ 2 := by
  have hPpx : P (P x) = P x := by
    have h := congrArg (fun Q : E →L[ℝ] E => Q x) hPid
    simpa using h
  have hs :
      inner ℝ (P x) (P x) = inner ℝ x (P (P x)) :=
    hPsymm x (P x)
  rw [hPpx, real_inner_self_eq_norm_sq] at hs
  rw [real_inner_comm]
  exact hs.symm

/-- For a finite family of orthogonal projections, the normalized random-scan
Rayleigh quadratic form is exactly the mean retained squared norm. -/
theorem groundStateJointColorRandomScanOperator_inner_eq_meanProjectedNormSq
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) :
    inner ℝ (groundStateJointColorRandomScanOperator P x) x =
      groundStateJointColorMeanProjectedNormSq P x := by
  rw [groundStateJointColorRandomScanOperator_apply]
  simp only [real_inner_smul_left, sum_inner]
  unfold groundStateJointColorMeanProjectedNormSq
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  exact
    realHilbert_groundStateJoint_projection_inner_self_eq_norm_sq
      (P c) (hPid c) (hPsymm c) x

/-- Exact Hilbert form of finite-color Poincare coercivity: the residual frame
inequality is equivalent to a Rayleigh contraction of the normalized
random-scan average. -/
theorem groundStateJointColorFrame_iff_randomScanRayleigh_le
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric)
    (kappa : ℝ)
    (x : E) :
    kappa * ‖x‖ ^ 2 ≤ groundStateJointColorNormalizedResidualEnergy P x ↔
      inner ℝ (groundStateJointColorRandomScanOperator P x) x ≤
        (1 - kappa) * ‖x‖ ^ 2 := by
  rw [
    groundStateJointColorRandomScanOperator_inner_eq_meanProjectedNormSq
      P hPid hPsymm x]
  exact
    groundStateJointColorFrame_iff_meanProjectedNormSq_le
      P hPid hPsymm kappa x

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

/-- Genuine normalized random-scan average of the six right-boundary spatial
conditional expectations on the ground-state joint L2 carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanL2 :
    J →L[ℝ] J :=
  groundStateJointColorRandomScanOperator P6

/-- The six-spatial random-scan Rayleigh form on a right-boundary vacuum lift
is exactly the existing six-spatial mean projected squared norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanL2_inner_eq_meanProjectedNormSq
    (u : V) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanL2
          H N hN beta hbeta (R u))
        (R u) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
        H N hN beta hbeta u := by
  exact
    groundStateJointColorRandomScanOperator_inner_eq_meanProjectedNormSq
      P6
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_idempotent
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_symmetric
        H N hN beta hbeta)
      (R u)

/-- On the physical top-orthogonal sector, the actual six-spatial frame
inequality is exactly equivalent to Rayleigh contraction of the genuine
six-spatial random-scan operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_iff_randomScanRayleighContraction
    (kappa : ℝ)
    (x : K) :
    kappa * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
          H N hN beta hbeta (U ((x : G) : HaarL2)) ↔
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanL2
            H N hN beta hbeta
            (R (U ((x : G) : HaarL2))))
          (R (U ((x : G) : HaarL2))) ≤
        (1 - kappa) * ‖(x : G)‖ ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanL2_inner_eq_meanProjectedNormSq]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_iff_meanProjectionContraction
      H N hN beta hbeta kappa x

/-- A Rayleigh contraction factor q ≤ 1 for the genuine six-spatial
ground-state random-scan operator yields the explicit physical transfer-gap
lower bound 3(1-q)/8. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanRayleighContraction_implies_transferGap
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hRayleigh : ∀ x : K,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanL2
            H N hN beta hbeta
            (R (U ((x : G) : HaarL2))))
          (R (U ((x : G) : HaarL2))) ≤
        q * ‖(x : G)‖ ^ 2) :
    3 * (1 - q) / 8 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectionContraction_implies_transferGap
      H N hN beta hbeta q hq0 hq1
  intro x
  rw [←
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanL2_inner_eq_meanProjectedNormSq
      H N hN beta hbeta]
  exact hRayleigh x

/-- Strict Rayleigh contraction of the genuine six-spatial random scan implies
a positive physical transfer gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanRayleighContraction_positive_transferGap
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hRayleigh : ∀ x : K,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanL2
            H N hN beta hbeta
            (R (U ((x : G) : HaarL2))))
          (R (U ((x : G) : HaarL2))) ≤
        q * ‖(x : G)‖ ^ 2) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanRayleighContraction_implies_transferGap
      H N hN beta hbeta q hq0 hq1.le hRayleigh
  have hpos : 0 < 3 * (1 - q) / 8 := by
    positivity
  exact lt_of_lt_of_le hpos hgap

end FiniteVolume

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)

/-- Scale-uniform genuine random-scan Rayleigh target for the six actual
ground-state spatial conditional expectations. -/
def PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateSixSpatialRandomScanRayleighContraction :
    Prop :=
  ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
    ∀ (n : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)),
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanL2
            (halfExtent n) N hN (beta n) (hbeta n)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
              (halfExtent n) N hN (beta n) (hbeta n)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
                (halfExtent n) N hN (beta n) (hbeta n)
                ((x :
                    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                      (halfExtent n) N) :
                  Lp ℝ 2
                    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                      (halfExtent n) N)))))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
            (halfExtent n) N hN (beta n) (hbeta n)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
              (halfExtent n) N hN (beta n) (hbeta n)
              ((x :
                  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                    (halfExtent n) N) :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                    (halfExtent n) N)))) ≤
        q *
          ‖(x :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                (halfExtent n) N)‖ ^ 2

/-- A single strict Rayleigh contraction factor for the genuine six-spatial
random-scan operators gives a scale-uniform positive physical transfer gap. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformGroundStateSixSpatialRandomScanRayleighContraction_implies_uniformTransferGap
    (hRayleigh :
      PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateSixSpatialRandomScanRayleighContraction
        halfExtent N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta := by
  rcases hRayleigh with ⟨q, hq0, hq1, hRayleigh⟩
  have hpos : 0 < 3 * (1 - q) / 8 := by
    positivity
  refine ⟨3 * (1 - q) / 8, hpos, ?_⟩
  intro n
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialRandomScanRayleighContraction_implies_transferGap
      (halfExtent n) N hN (beta n) (hbeta n)
      q hq0 hq1.le (fun x => hRayleigh n x)

end ScalingFamily

end

end MGAP4D.MathlibAnalytic

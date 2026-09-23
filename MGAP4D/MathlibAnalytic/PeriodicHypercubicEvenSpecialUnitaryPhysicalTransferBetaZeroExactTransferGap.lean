import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroRankOne
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import Mathlib.Tactic

/-!
# Exact beta-zero physical top-orthogonal transfer gap

At beta = 0 the normalized physical one-slab transfer is the self rank-one
projection onto the canonical constant Gauss-law unit vector.

That constant vector belongs to the full eigenvalue-one top eigenspace.
Therefore every vector in the orthogonal complement of the full top eigenspace
has zero coefficient against the rank-one vector.  The normalized transfer
restricted to the top-eigenspace orthogonal sector is consequently the zero
operator.

Hence the finite-volume physical transfer-gap quantity used by the downstream
formal spine is exactly one at beta = 0, uniformly in the finite volume.

This is an exact finite-volume endpoint statement.  It does not by itself
assert a positive-beta uniform gap or a continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- The canonical constant physical vector belongs to the full beta-zero
eigenvalue-one top eigenspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_mem_topEigenspace_zero
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN 0 (by norm_num) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem]
  exact
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_constantUnit
      H N hN

/-- Every vector in the beta-zero top-eigenspace orthogonal sector has zero
inner product with the canonical constant physical unit vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal_zero_inner_constantUnit
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
        (x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N) = 0 := by
  have hxOrth :
      (x :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          H N) ∈
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H N hN 0 (by norm_num))ᗮ := by
    change
      (x :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          H N) ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN 0 (by norm_num)
    exact x.property
  rw [Submodule.mem_orthogonal] at hxOrth
  exact hxOrth
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_mem_topEigenspace_zero
      H N hN)

/-- The normalized physical beta-zero transfer annihilates every vector in the
orthogonal complement of its full top eigenspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_apply_topEigenspaceOrthogonal
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN 0 (by norm_num)
        (x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N) = 0 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_eq_rankOne
      H N hN,
    InnerProductSpace.rankOne_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal_zero_inner_constantUnit
      H N hN x,
    zero_smul]

/-- The actual beta-zero top-eigenspace orthogonal restriction is exactly the
zero continuous linear map. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_zero_eq_zero
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN 0 (by norm_num) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN 0 (by norm_num)
        (x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N) = 0
  exact
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_apply_topEigenspaceOrthogonal
      H N hN x

/-- Exact norm of the beta-zero top-orthogonal restriction. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_zero_norm
    (H N : ℕ)
    (hN : 0 < N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN 0 (by norm_num)‖ = 0 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN 0 (by norm_num)
  letI : NormedSpace ℝ K := Submodule.normedSpace K
  have hzero :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN 0 (by norm_num) =
        (0 : K →L[ℝ] K) := by
    simpa [K] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_zero_eq_zero
        H N hN)
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN 0 (by norm_num)‖ =
        ‖(0 : K →L[ℝ] K)‖ := congrArg norm hzero
    _ = 0 := ContinuousLinearMap.opNorm_zero

/-- Exact finite-volume beta-zero transfer gap: it is one, independently of
the finite spatial volume. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_zero
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN 0 (by norm_num) = 1 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_zero_norm]
  norm_num

end

end MGAP4D.MathlibAnalytic

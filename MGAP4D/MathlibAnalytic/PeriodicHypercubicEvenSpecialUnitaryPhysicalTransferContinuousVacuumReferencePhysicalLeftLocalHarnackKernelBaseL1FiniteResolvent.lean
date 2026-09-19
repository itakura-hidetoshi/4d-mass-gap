import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackKernelBaseL1Propagation
import MGAP4D.MathlibAnalytic.FiniteExponentialShellGeometricBound
import Mathlib.Tactic

/-!
# Base-L1 geometric finite resolvent for the physical local Harnack kernel

The actual continuous-vacuum physical influence envelope has been split exactly
into the intrinsic active-neighbor Harnack kernel plus the remote physical
vacuum residual.  The preceding local propagation file proves both finite
base-L1 propagation and the pointwise power bound for recursive powers of the
actual local kernel.

This file packages those facts into the corresponding finite local resolvent.
For

`rho_local(beta) =
  18 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence beta`,

a base-L1 separation of at least `2 * D` removes every degree below `D`
exactly.  Under the strict local threshold `rho_local(beta) < 1`, every finite
truncation is therefore bounded uniformly by

`rho_local(beta)^D / (1 - rho_local(beta))`.

Only the actual local Harnack carrier is summed here.  The source-aligned remote
physical residual is not discarded or identified with this local resolvent, and
no covariance-remainder, ergodicity, infinite-resolvent, or mass-gap statement
is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite Neumann resolvent entry of the actual physical local Harnack kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (M : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ d ∈ Finset.range M,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
      H beta hbeta d target source

/-- Every finite local-Harnack resolvent entry is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (M : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
        H beta hbeta M target source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
  exact
    Finset.sum_nonneg fun d _ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_nonneg
        H beta hbeta d target source

/-- Base-L1 separation kills the entire local-Harnack resolvent prefix below
degree `D` exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_prefix_eq_zero_of_two_mul_le_baseL1Distance
    (H D : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      2 * D ≤
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)) :
    (∑ d ∈ Finset.range D,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
        H beta hbeta d target source) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d hd
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_eq_zero_of_two_mul_le_baseL1Distance
      H D d beta hbeta target source hDistance (Finset.mem_range.mp hd)

/-- The shifted finite tail of the actual local-Harnack powers is bounded by
the full geometric tail beginning at degree `D`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_tail_le_geometric
    (H D M : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ k ∈ Finset.range M,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
        H beta hbeta (D + k) target source) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ D /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta) := by
  classical
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  have hEta :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  have hRho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hRhoLt : rho < 1 := by
    simpa [rho] using hThreshold
  calc
    (∑ k ∈ Finset.range M,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
        H beta hbeta (D + k) target source) ≤
        ∑ k ∈ Finset.range M, rho ^ (D + k) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa [rho] using
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_le_pow
          H beta hbeta (D + k) target source)
    _ = ∑ k ∈ Finset.range M, rho ^ D * rho ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_add]
    _ = rho ^ D * ∑ k ∈ Finset.range M, rho ^ k := by
      rw [Finset.mul_sum]
    _ ≤ rho ^ D * (1 / (1 - rho)) := by
      exact
        mul_le_mul_of_nonneg_left
          (FiniteDistanceShellGeometricSum.sum_range_pow_le_one_div_one_sub
            rho hRho hRhoLt M)
          (pow_nonneg hRho D)
    _ = rho ^ D / (1 - rho) := by
      rw [div_eq_mul_inv]
    _ =
        (18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta) ^ D /
          (1 -
            18 *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
                beta) := by
      rfl

/-- When `D ≤ M`, the finite local-Harnack resolvent is exactly its shifted
tail because the complete degree-`< D` prefix vanishes by base-L1 separation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry_eq_tail_of_two_mul_le_baseL1Distance
    (H D M : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      2 * D ≤
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source))
    (hDM : D ≤ M) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
        H beta hbeta M target source =
      ∑ k ∈ Finset.range (M - D),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
          H beta hbeta (D + k) target source := by
  classical
  have hPrefix :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_prefix_eq_zero_of_two_mul_le_baseL1Distance
      H D beta hbeta target source hDistance
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
  rw [show M = D + (M - D) by omega]
  rw [Finset.sum_range_add]
  rw [hPrefix, zero_add]

/-- Uniform-in-`M` base-L1 geometric bound for the finite resolvent of the
actual physical local Harnack kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry_le_geometric_of_two_mul_le_baseL1Distance
    (H D M : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      2 * D ≤
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
        H beta hbeta M target source ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ D /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta) := by
  classical
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  have hEta :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  have hRho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hRhoLt : rho < 1 := by
    simpa [rho] using hThreshold
  by_cases hDM : D ≤ M
  · rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry_eq_tail_of_two_mul_le_baseL1Distance
        H D M beta hbeta target source hDistance hDM]
    simpa [rho] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_tail_le_geometric
        H D (M - D) beta hbeta hThreshold target source)
  · have hMD : M < D := Nat.lt_of_not_ge hDM
    have hZero :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
            H beta hbeta M target source = 0 := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
      apply Finset.sum_eq_zero
      intro d hd
      apply
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel_eq_zero_of_two_mul_le_baseL1Distance
          H D d beta hbeta target source hDistance
      have hdM : d < M := Finset.mem_range.mp hd
      omega
    rw [hZero]
    have hDenom : 0 ≤ 1 - rho := by
      exact le_of_lt (sub_pos.mpr hRhoLt)
    have hBound : 0 ≤ rho ^ D / (1 - rho) := by
      exact div_nonneg (pow_nonneg hRho D) hDenom
    simpa [rho] using hBound

end

end MathlibAnalytic
end MGAP4D

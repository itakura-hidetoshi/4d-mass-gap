import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopPowerDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferUniformTopOrthogonalPowerDecay
import Mathlib.Tactic

/-!
# Scale-uniform q0 decay on the full physical pair non-top sector

The physical pair carrier already has the completed orthogonal three-block
non-top sector

  K tensor Omega + Omega tensor K + K tensor K,

where K is the full one-slice top-eigenspace orthogonal sector.

Existing finite-volume theorems prove that the normalized pair transfer
restricted to this completed non-top sector has norm at most the one-slice
restricted norm ||R||, and powers decay with ||R||^k.

PR #4983 proves the scale-uniform estimate

  ||R_n|| <= q0,  q0 = 3071 / 3072.

This file combines the two results.  Hence the whole completed physical pair
non-top sector, not merely one one-sided block, satisfies the uniform q0^k
bound at every scale.

No vacuum-line identification or top-eigenspace simplicity is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

private theorem real_pow_mono_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ k : ℕ, a ^ k ≤ b ^ k
  | 0 => by simp
  | k + 1 => by
      have hb : 0 ≤ b := ha.trans hab
      rw [pow_succ, pow_succ]
      exact mul_le_mul
        (real_pow_mono_nonneg ha hab k) hab ha (pow_nonneg hb k)

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- The completed physical pair non-top transfer has the same explicit
scale-independent one-step contraction factor q0 as the one-slice
top-orthogonal transfer. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopTransferOperator_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor := by
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_le
        (halfExtent n) N hN (beta n) (hbeta n)
    _ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor :=
      periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_norm_le
        halfExtent N hN beta hbeta s hs hcut n

/-- Uniform q0^k operator-norm decay on the full completed physical pair
non-top sector. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopTransferOperator_pow_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ) :
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)) ^ k‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  have hR :
      ‖R‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_norm_le
        halfExtent N hN beta hbeta s hs hcut n
  calc
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)) ^ k‖ ≤
      ‖R‖ ^ k :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_norm_le
        (halfExtent n) N hN (beta n) (hbeta n) k
    _ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k :=
      real_pow_mono_nonneg (norm_nonneg R) hR k

/-- Uniform q0^k pointwise decay for every vector in the completed physical
pair non-top sector. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopTransferOperator_pow_apply_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n)) :
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)) ^ k) x‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖x‖ := by
  calc
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)) ^ k) x‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)‖ ^ k * ‖x‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_apply_norm_le
        (halfExtent n) N hN (beta n) (hbeta n) k x
    _ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖x‖ := by
      apply mul_le_mul_of_nonneg_right
      · exact real_pow_mono_nonneg
          (norm_nonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              (halfExtent n) N hN (beta n) (hbeta n)))
          (periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_norm_le
            halfExtent N hN beta hbeta s hs hcut n)
          k
      · exact norm_nonneg x

/-- Ambient pair-Haar formulation: any vector already known to belong to the
completed physical non-top block obeys the same uniform q0^k decay. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N)
    (hx :
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n)) :
    ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) ^ k) x‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖x‖ := by
  calc
    ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) ^ k) x‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)‖ ^ k * ‖x‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
        (halfExtent n) N hN (beta n) (hbeta n) k x hx
    _ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖x‖ := by
      apply mul_le_mul_of_nonneg_right
      · exact real_pow_mono_nonneg
          (norm_nonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              (halfExtent n) N hN (beta n) (hbeta n)))
          (periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_norm_le
            halfExtent N hN beta hbeta s hs hcut n)
          k
      · exact norm_nonneg x

/-- Audit-visible rank/volume/scale-uniform pair non-top decay package. -/
structure PeriodicHypercubicEvenSpecialUnitaryUniformPhysicalPairNonTopDecayPackage :
    Prop where
  factorStrict :
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor < 1
  oneStepNorm :
    ∀ n,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor
  powerNorm :
    ∀ n k,
      ‖(periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)) ^ k‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k
  vectorDecay :
    ∀ n k
      (x :
        periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
          (halfExtent n) N hN (beta n) (hbeta n)),
      ‖((periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)) ^ k) x‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
          ‖x‖

theorem
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopDecayPackage
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    PeriodicHypercubicEvenSpecialUnitaryUniformPhysicalPairNonTopDecayPackage
      halfExtent N hN beta hbeta := by
  refine
    { factorStrict :=
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_lt_one
      oneStepNorm := ?_
      powerNorm := ?_
      vectorDecay := ?_ }
  · intro n
    exact
      periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopTransferOperator_norm_le
        halfExtent N hN beta hbeta s hs hcut n
  · intro n k
    exact
      periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopTransferOperator_pow_norm_le
        halfExtent N hN beta hbeta s hs hcut n k
  · intro n k x
    exact
      periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopTransferOperator_pow_apply_norm_le
        halfExtent N hN beta hbeta s hs hcut n k x

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D

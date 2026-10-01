import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryOneSidedExcitationTransfer
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferUniformTopOrthogonalPowerDecay
import Mathlib.Tactic

/-!
# Scale-uniform q0 decay on the one-sided shared-boundary excitation sector

PR #4983 gives the explicit scale-independent contraction factor

  q0 = 3071 / 3072

on every physical one-slab top-eigenspace-orthogonal sector.

The one-sided shared-boundary excitation sector is already known to be
isometrically equivalent to that physical sector.  This file transports the
#4983 estimate through that exact equivalence.

Thus the actual shared-boundary one-particle sector satisfies, uniformly in
scale,

  ||B_n^k y|| <= q0^k ||y||.

No identification of the full canonical OS boundary-vacuum-orthogonal sector
with the one-sided top-orthogonal range is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace

noncomputable section

@[reducible] local instance oneSidedUniformDecayPhysicalOrthogonalNormedSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  Submodule.normedSpace
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- Uniform q0^k decay on the concrete one-sided shared-boundary sector. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformOneSidedExcitationBoundarySectorTransfer_apply_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ)
    (hk : 0 < k)
    (y :
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
        (halfExtent n) N hN (beta n) (hbeta n)) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        (halfExtent n) N hN (beta n) (hbeta n) k y‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖y‖ := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryEquiv
      (halfExtent n) N hN (beta n) (hbeta n)
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  calc
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        (halfExtent n) N hN (beta n) (hbeta n) k y‖ =
      ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        (halfExtent n) N hN (beta n) (hbeta n) k (U (U.symm y))‖ := by
      rw [U.apply_symm_apply]
    _ = ‖U ((T ^ k) (U.symm y))‖ := by
      rw [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer_apply_image]
    _ = ‖(T ^ k) (U.symm y)‖ := by
      exact U.norm_map _
    _ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖U.symm y‖ := by
      exact
        periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_pow_apply_norm_le
          halfExtent N hN beta hbeta s hs hcut n k hk (U.symm y)
    _ =
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖y‖ := by
      rw [U.symm.norm_map]

/-- Operator-norm form of the same scale-uniform boundary contraction. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformOneSidedExcitationBoundarySectorTransfer_opNorm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ)
    (hk : 0 < k) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        (halfExtent n) N hN (beta n) (hbeta n) k‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact pow_nonneg
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_nonneg
      k
  · intro y
    exact
      periodicHypercubicEvenSpecialUnitary_uniformOneSidedExcitationBoundarySectorTransfer_apply_norm_le
        halfExtent N hN beta hbeta s hs hcut n k hk y

/-- One-step specialization on the concrete shared-boundary excitation sector. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformOneSidedExcitationBoundarySectorTransfer_one_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n : ℕ)
    (y :
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
        (halfExtent n) N hN (beta n) (hbeta n)) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        (halfExtent n) N hN (beta n) (hbeta n) 1 y‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor *
        ‖y‖ := by
  simpa using
    periodicHypercubicEvenSpecialUnitary_uniformOneSidedExcitationBoundarySectorTransfer_apply_norm_le
      halfExtent N hN beta hbeta s hs hcut n 1 (by norm_num) y

/-- Audit-visible package for the shared-boundary finite dynamics. -/
structure PeriodicHypercubicEvenSpecialUnitaryUniformOneSidedBoundaryDecayPackage : Prop where
  factorStrict :
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor < 1
  vectorDecay :
    ∀ (n k : ℕ), 0 < k →
      ∀ y :
        periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
          (halfExtent n) N hN (beta n) (hbeta n),
        ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
            (halfExtent n) N hN (beta n) (hbeta n) k y‖ ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
            ‖y‖
  operatorDecay :
    ∀ (n k : ℕ), 0 < k →
      ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
          (halfExtent n) N hN (beta n) (hbeta n) k‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k

theorem
    periodicHypercubicEvenSpecialUnitary_uniformOneSidedBoundaryDecayPackage
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    PeriodicHypercubicEvenSpecialUnitaryUniformOneSidedBoundaryDecayPackage
      halfExtent N hN beta hbeta := by
  refine
    { factorStrict :=
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_lt_one
      vectorDecay := ?_
      operatorDecay := ?_ }
  · intro n k hk y
    exact
      periodicHypercubicEvenSpecialUnitary_uniformOneSidedExcitationBoundarySectorTransfer_apply_norm_le
        halfExtent N hN beta hbeta s hs hcut n k hk y
  · intro n k hk
    exact
      periodicHypercubicEvenSpecialUnitary_uniformOneSidedExcitationBoundarySectorTransfer_opNorm_le
        halfExtent N hN beta hbeta s hs hcut n k hk

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D

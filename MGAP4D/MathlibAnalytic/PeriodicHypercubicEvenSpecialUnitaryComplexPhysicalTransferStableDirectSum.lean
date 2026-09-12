import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferIntrinsicStableDecomposition
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set Filter Topology
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexStableDirectSumCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

local instance periodicHypercubicEvenSpecialUnitaryComplexStableDirectSumTopCompleteSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta) := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace, S] using
    (complexHilbertTopEigenspace_isClosed S).completeSpace_coe

/-- The transient subspace of the normalized complex Wilson transfer.  By the
intrinsic asymptotic theorem this is exactly the set of vectors whose positive
transfer orbit converges strongly to zero. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Submodule ℂ (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta

/-- Membership in the transient subspace is intrinsic: it is exactly strong
decay of the positive normalized Wilson-transfer orbit. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace_mem_iff_pow_succ_tendsto_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    f ∈ periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta ↔
      Tendsto
        (fun n : ℕ =>
          ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) f)
        atTop (𝓝 0) := by
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal] using
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal_mem_iff_pow_succ_tendsto_zero
      H N hN beta hbeta f

/-- The transient subspace is exactly the kernel of the intrinsic asymptotic CFC
projection.  This is the algebraic form of the dynamical characterization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace_eq_cfcTop_ker
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta =
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta).toLinearMap.ker := by
  ext f
  change
    f ∈ periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta ↔
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f = 0
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection]
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal] using
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_apply_eq_zero_iff
      H N hN beta hbeta f).symm

/-- The full fixed sector and the transient sector are complementary subspaces of
the genuine complex physical Hilbert space.  No simplicity or rank-one
assumption is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_isCompl_transientSubspace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsCompl
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta) := by
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal] using
    (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
      (K := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta))

/-- The intrinsic CFC asymptotic projection acts identically on the whole fixed
sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_self_of_mem_topEigenspace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f = f := by
  apply
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_self_iff_fixed
      H N hN beta hbeta f).2
  exact
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem
      H N hN beta hbeta f).1 hf

/-- The intrinsic CFC asymptotic projection annihilates the whole transient
sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_of_mem_transientSubspace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f = 0 := by
  exact
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_iff_pow_succ_tendsto_zero
      H N hN beta hbeta f).2
      ((periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace_mem_iff_pow_succ_tendsto_zero
        H N hN beta hbeta f).1 hf)

/-- The CFC component is the stable/fixed part of every physical vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_mem_topEigenspace_stableDirectSum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f ∈
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_mem_topEigenspace
    H N hN beta hbeta f

/-- The residual after removing the intrinsic CFC component lies in the
transient direct summand. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlab_sub_cfcTop_mem_transientSubspace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    f - periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f ∈
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta := by
  apply
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace_mem_iff_pow_succ_tendsto_zero
      H N hN beta hbeta
      (f - periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f)).2
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_sub_cfcTop_tendsto_zero
      H N hN beta hbeta f

/-- Every physical vector is the sum of its fixed CFC component and its transient
residual. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlab_cfcTop_add_transient_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f +
      (f - periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f) = f := by
  abel

/-- Audit-visible stable direct-sum package for the genuine complex Wilson
transfer.  It records the full fixed/transient decomposition and the strict
contraction of the transient block. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferStableDirectSumPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  directSum :
    IsCompl
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta)
  transientKernel :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta =
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta).toLinearMap.ker
  transientDynamics :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      f ∈ periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
          H N hN beta hbeta ↔
        Tendsto
          (fun n : ℕ =>
            ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) f)
          atTop (𝓝 0)
  stablePart :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f ∈
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta
  transientPart :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      f - periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f ∈
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
          H N hN beta hbeta
  decomposition :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f +
        (f - periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f) = f
  transientNormLtOne :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ < 1

/-- The genuine normalized complex Wilson transfer carries the stable direct-sum
package. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferStableDirectSumPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferStableDirectSumPackage
      H N hN beta hbeta where
  directSum :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_isCompl_transientSubspace
      H N hN beta hbeta
  transientKernel :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace_eq_cfcTop_ker
      H N hN beta hbeta
  transientDynamics :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace_mem_iff_pow_succ_tendsto_zero
      H N hN beta hbeta
  stablePart :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_mem_topEigenspace_stableDirectSum
      H N hN beta hbeta
  transientPart :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlab_sub_cfcTop_mem_transientSubspace
      H N hN beta hbeta
  decomposition :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlab_cfcTop_add_transient_eq
      H N hN beta hbeta
  transientNormLtOne :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta

end
end MathlibAnalytic
end MGAP4D

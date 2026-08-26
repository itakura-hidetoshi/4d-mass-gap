import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferPowerCFCConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- Operator-norm convergence of the genuine normalized complex Wilson transfer
to its full CFC top sector gives the corresponding quantitative convergence of
every complex Hilbert matrix element.  No top-sector simplicity is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_sub_cfcTop_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖inner ℂ f
        (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) g) -
      inner ℂ f
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta g)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ * ‖g‖ := by
  have hpoint :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_sub_cfcTop_norm_le
      H N hN beta hbeta n g
  calc
    ‖inner ℂ f
        (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) g) -
      inner ℂ f
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta g)‖ =
        ‖inner ℂ f
          ((((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) g) -
            periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
              H N hN beta hbeta g)‖ := by
      rw [inner_sub_right]
    _ ≤ ‖f‖ *
        ‖(((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) g) -
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
            H N hN beta hbeta g‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖f‖ *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ ^ (n + 1) * ‖g‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg f)
    _ =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ * ‖g‖ := by
      ring

/-- A vector orthogonal to the entire full complex top eigenspace is killed by
the isolated CFC top projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_of_mem_topOrthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N}
    (hg : g ∈
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta g = 0 := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection]
  exact
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_apply_eq_zero_iff
      H N hN beta hbeta g).2 hg

/-- If the right state is orthogonal to the full top sector, its normalized
Wilson transfer matrix element decays geometrically at the exact excited-sector
rate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_norm_le_of_right_mem_topOrthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
    (hg : g ∈
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ) :
    ‖inner ℂ f
      (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1)) g)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ * ‖g‖ := by
  have hPg :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_of_mem_topOrthogonal
      H N hN beta hbeta hg
  simpa [hPg] using
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_sub_cfcTop_norm_le
      H N hN beta hbeta n f g

/-- The CFC top component of any vector lies in the full complex top eigenspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_mem_topEigenspace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta g ∈
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta := by
  rw [← periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_range]
  exact ⟨g, rfl⟩

/-- If the left state is orthogonal to the full top sector, the CFC limiting
matrix element vanishes as well. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlab_inner_cfcTop_eq_zero_of_left_mem_topOrthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
    (hf : f ∈
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ) :
    inner ℂ f
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta g) = 0 := by
  rw [Submodule.mem_orthogonal] at hf
  have hPg :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_mem_topEigenspace
      H N hN beta hbeta g
  exact (inner_eq_zero_symm).2 (hf _ hPg)

/-- If the left state is orthogonal to the full top sector, the same exact
geometric matrix-element decay follows. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_norm_le_of_left_mem_topOrthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
    (hf : f ∈
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ) :
    ‖inner ℂ f
      (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1)) g)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ * ‖g‖ := by
  have hTop :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlab_inner_cfcTop_eq_zero_of_left_mem_topOrthogonal
      H N hN beta hbeta f g hf
  simpa [hTop] using
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_sub_cfcTop_norm_le
      H N hN beta hbeta n f g

/-- Audit-visible matrix-element clustering package for the genuine complex
normalized finite Wilson transfer. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCMatrixElementClusteringPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  matrixElementConvergence :
    ∀ (n : ℕ)
      (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N),
      ‖inner ℂ f
          (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) g) -
        inner ℂ f
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
            H N hN beta hbeta g)‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ * ‖g‖
  rightTopOrthogonalDecay :
    ∀ (n : ℕ)
      (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N),
      g ∈
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta)ᗮ →
      ‖inner ℂ f
        (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1)) g)‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ * ‖g‖
  leftTopOrthogonalDecay :
    ∀ (n : ℕ)
      (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N),
      f ∈
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta)ᗮ →
      ‖inner ℂ f
        (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1)) g)‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ * ‖g‖

/-- Construct the exact CFC matrix-element clustering package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCMatrixElementClusteringPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCMatrixElementClusteringPackage
      H N hN beta hbeta :=
  { matrixElementConvergence :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_sub_cfcTop_norm_le
        H N hN beta hbeta
    rightTopOrthogonalDecay :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_norm_le_of_right_mem_topOrthogonal
        H N hN beta hbeta
    leftTopOrthogonalDecay :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_norm_le_of_left_mem_topOrthogonal
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
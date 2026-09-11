import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszRepresentation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCMatrixElementClustering

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexRieszDynamicsCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The normalized complex Wilson transfer absorbs every admissible Riesz
projector on the right. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_mul_rieszProjectorAtRadius
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r =
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_mul_cfcTopProjection
      H N hN beta hbeta

/-- Every admissible Riesz projector absorbs the normalized complex Wilson
transfer on the right. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_mul_transferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r *
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_normalizedTransferOperator
      H N hN beta hbeta

/-- Every admissible Riesz projector is idempotent in the bounded-operator algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_mul_self
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r *
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r =
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_self
      H N hN beta hbeta

/-- The centered transfer annihilates every admissible Riesz top projector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_mul_rieszProjectorAtRadius
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r = 0 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_mul_cfcTopProjection
      H N hN beta hbeta

/-- Every admissible Riesz top projector annihilates the centered transfer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_mul_centeredTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r *
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta = 0 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_centeredTransferOperator
      H N hN beta hbeta

/-- Every positive transfer power splits into the contour-defined Riesz top
projector plus the corresponding centered power. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_eq_rieszProjectorAtRadius_add_centered_pow
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    (n : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta) ^ (n + 1) =
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r +
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta) ^ (n + 1) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_eq_cfcTop_add_centered_pow
      H N hN beta hbeta n

/-- Exact residual identity after subtracting an admissible Riesz top projector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_rieszProjectorAtRadius_eq_centered_pow
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    (n : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta) ^ (n + 1) -
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r =
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta) ^ (n + 1) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_cfcTop_eq_centered_pow
      H N hN beta hbeta n

/-- Quantitative operator-norm convergence of positive transfer powers to every
admissible Riesz top projector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_rieszProjectorAtRadius_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    (n : ℕ) :
    ‖(periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1) -
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ (n + 1) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_cfcTop_norm_le
      H N hN beta hbeta n

/-- Pointwise geometric convergence to the contour-defined Riesz top component. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_sub_rieszProjectorAtRadius_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1)) f -
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r f‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_sub_cfcTop_norm_le
      H N hN beta hbeta n f

/-- Matrix elements converge geometrically to the contour-defined Riesz top
component at the same exact excited-sector rate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_sub_rieszProjectorAtRadius_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    (n : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖inner ℂ f
        (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) g) -
      inner ℂ f
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r g)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ * ‖g‖ := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_sub_cfcTop_norm_le
      H N hN beta hbeta n f g

/-- An admissible Riesz top projector kills every vector orthogonal to the full
top eigenspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_apply_eq_zero_of_mem_topOrthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    {g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N}
    (hg : g ∈
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r g = 0 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_of_mem_topOrthogonal
      H N hN beta hbeta hg

/-- Audit-visible dynamical characterization of every admissible contour-defined
Riesz top projector. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszDynamicsPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  transferAbsorbsRiesz :
    ∀ r : ℝ, 0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta *
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r =
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r
  rieszAbsorbsTransfer :
    ∀ r : ℝ, 0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r *
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta =
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r
  powerDecomposition :
    ∀ (r : ℝ), 0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      ∀ n : ℕ,
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1) =
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r +
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
          H N hN beta hbeta) ^ (n + 1)
  operatorNormConvergence :
    ∀ (r : ℝ), 0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      ∀ n : ℕ,
      ‖(periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1) -
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ (n + 1)
  matrixElementConvergence :
    ∀ (r : ℝ), 0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      ∀ (n : ℕ)
        (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N),
      ‖inner ℂ f
          (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) g) -
        inner ℂ f
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
            H N hN beta hbeta r g)‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ * ‖g‖

/-- Construct the contour-defined Riesz dynamics package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszDynamicsPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszDynamicsPackage
      H N hN beta hbeta :=
  { transferAbsorbsRiesz :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_mul_rieszProjectorAtRadius
        H N hN beta hbeta
    rieszAbsorbsTransfer :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_mul_transferOperator
        H N hN beta hbeta
    powerDecomposition :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_eq_rieszProjectorAtRadius_add_centered_pow
        H N hN beta hbeta
    operatorNormConvergence :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_rieszProjectorAtRadius_norm_le
        H N hN beta hbeta
    matrixElementConvergence :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_sub_rieszProjectorAtRadius_norm_le
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D

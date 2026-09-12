import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCMatrixElementClustering
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

universe u v

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- If an idempotent sector is fixed on the right by `S`, then on every point
of the resolvent set the corresponding right block has the exact simple-pole
coefficient `P` at the scalar value `1`.  This is purely algebraic and does not
assume that `P` has rank one. -/
theorem resolvent_mul_fixedSector_residue
    {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (S P : A) (z : R)
    (hSP : S * P = P)
    (hz : z ∈ resolventSet R S) :
    (z - 1) • (resolvent S z * P) = P := by
  have hzUnit : IsUnit (algebraMap R A z - S) := hz
  have hShiftP :
      (algebraMap R A z - S) * P = (z - 1) • P := by
    calc
      (algebraMap R A z - S) * P = algebraMap R A z * P - P := by
        rw [sub_mul, hSP]
      _ = z • P - P := by
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      _ = (z - 1) • P := by
        rw [sub_smul, one_smul]
  calc
    (z - 1) • (resolvent S z * P) =
        resolvent S z * ((z - 1) • P) := by
      exact (mul_smul_comm (z - 1) (resolvent S z) P).symm
    _ = resolvent S z * ((algebraMap R A z - S) * P) := by
      rw [hShiftP]
    _ = P := by
      rw [← mul_assoc, resolvent, Ring.inverse_mul_cancel _ hzUnit, one_mul]

/-- Left-fixed sectors satisfy the symmetric exact resolvent-pole identity. -/
theorem fixedSector_mul_resolvent_residue
    {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (S P : A) (z : R)
    (hPS : P * S = P)
    (hz : z ∈ resolventSet R S) :
    (z - 1) • (P * resolvent S z) = P := by
  have hzUnit : IsUnit (algebraMap R A z - S) := hz
  have hPShift :
      P * (algebraMap R A z - S) = (z - 1) • P := by
    calc
      P * (algebraMap R A z - S) = P * algebraMap R A z - P := by
        rw [mul_sub, hPS]
      _ = z • P - P := by
        rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      _ = (z - 1) • P := by
        rw [sub_smul, one_smul]
  calc
    (z - 1) • (P * resolvent S z) =
        ((z - 1) • P) * resolvent S z := by
      exact (smul_mul_assoc (z - 1) P (resolvent S z)).symm
    _ = (P * (algebraMap R A z - S)) * resolvent S z := by
      rw [hPShift]
    _ = P := by
      rw [mul_assoc, resolvent, Ring.mul_inverse_cancel _ hzUnit, mul_one]

local instance periodicHypercubicEvenSpecialUnitaryComplexResolventPoleRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryComplexResolventPoleComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- On the already-proved punctured right-half-plane resolvent region, the
right top block of the genuine complex Wilson resolvent has exact pole
coefficient equal to the full CFC top projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_mul_cfcTop_residue
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : ℂ)
    (hzq :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ < z.re)
    (hz1 : z ≠ 1) :
    (z - 1) •
        (resolvent
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) z *
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
            H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta := by
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  have hSP : S * P = P := by
    simpa [S, P] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_mul_cfcTopProjection
        H N hN beta hbeta
  have hzRes : z ∈ resolventSet ℂ S := by
    apply
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rightHalfPlane_except_one_subset_complex_resolventSet
        H N hN beta hbeta
    exact ⟨by simpa [S] using hzq, hz1⟩
  simpa [S, P] using resolvent_mul_fixedSector_residue S P z hSP hzRes

/-- The left top block has the same exact CFC pole coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_cfcTop_mul_resolvent_residue
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : ℂ)
    (hzq :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ < z.re)
    (hz1 : z ≠ 1) :
    (z - 1) •
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
            H N hN beta hbeta *
          resolvent
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) z) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta := by
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  have hPS : P * S = P := by
    simpa [S, P] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_normalizedTransferOperator
        H N hN beta hbeta
  have hzRes : z ∈ resolventSet ℂ S := by
    apply
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rightHalfPlane_except_one_subset_complex_resolventSet
        H N hN beta hbeta
    exact ⟨by simpa [S] using hzq, hz1⟩
  simpa [S, P] using fixedSector_mul_resolvent_residue S P z hPS hzRes

/-- Audit-visible rank-free top-pole package for the genuine complex normalized
Wilson transfer resolvent. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventTopPolePackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  rightTopPole :
    ∀ z : ℂ,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re →
      z ≠ 1 →
      (z - 1) •
          (resolvent
              (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
                H N hN beta hbeta) z *
            periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
              H N hN beta hbeta) =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta
  leftTopPole :
    ∀ z : ℂ,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re →
      z ≠ 1 →
      (z - 1) •
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
              H N hN beta hbeta *
            resolvent
              (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
                H N hN beta hbeta) z) =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta

/-- Construct the exact CFC top-resolvent-pole package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventTopPolePackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventTopPolePackage
      H N hN beta hbeta :=
  { rightTopPole :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_mul_cfcTop_residue
        H N hN beta hbeta
    leftTopPole :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_cfcTop_mul_resolvent_residue
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
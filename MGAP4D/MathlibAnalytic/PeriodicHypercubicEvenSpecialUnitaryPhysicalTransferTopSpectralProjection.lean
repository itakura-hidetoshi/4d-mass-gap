import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

local instance realHilbertTopEigenspace_completeSpace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) :
    CompleteSpace (realHilbertTopEigenspace S) :=
  (realHilbertTopEigenspace_isClosed S).completeSpace_coe

local instance realHilbertTopEigenspaceOrthogonal_completeSpace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) :
    CompleteSpace (realHilbertTopEigenspace S)ᗮ :=
  (realHilbertTopEigenspace S).isClosed_orthogonal.completeSpace_coe

/-- Canonical orthogonal projection onto the full eigenvalue-one space of a
bounded operator on a complete real Hilbert space.  This is Mathlib's
`Submodule.starProjection`, not a separately chosen rank-one vacuum
projection. -/
noncomputable def realHilbertTopEigenspaceProjection
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) : E →L[ℝ] E :=
  (realHilbertTopEigenspace S).starProjection

/-- The canonical top-eigenspace projection has exactly the full fixed-point
space as its range. -/
@[simp] theorem realHilbertTopEigenspaceProjection_range
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) :
    (realHilbertTopEigenspaceProjection S).range = realHilbertTopEigenspace S := by
  simpa [realHilbertTopEigenspaceProjection] using
    (Submodule.range_starProjection (realHilbertTopEigenspace S))

/-- Mathlib certifies the canonical top-eigenspace projection as a symmetric
idempotent projection. -/
@[simp] theorem realHilbertTopEigenspaceProjection_isSymmetricProjection
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) :
    (realHilbertTopEigenspaceProjection S).IsSymmetricProjection := by
  simpa [realHilbertTopEigenspaceProjection] using
    (Submodule.isSymmetricProjection_starProjection (realHilbertTopEigenspace S))

/-- A vector is fixed by the canonical projection exactly when it is fixed by
the original operator. -/
@[simp] theorem realHilbertTopEigenspaceProjection_apply_eq_self_iff
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) (x : E) :
    realHilbertTopEigenspaceProjection S x = x ↔ S x = x := by
  rw [realHilbertTopEigenspaceProjection,
    Submodule.starProjection_eq_self_iff,
    realHilbertTopEigenspace_mem]

/-- The kernel of the canonical projection is precisely the orthogonal
complement of the full top eigenspace. -/
@[simp] theorem realHilbertTopEigenspaceProjection_apply_eq_zero_iff
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) (x : E) :
    realHilbertTopEigenspaceProjection S x = 0 ↔
      x ∈ (realHilbertTopEigenspace S)ᗮ := by
  simpa [realHilbertTopEigenspaceProjection] using
    (Submodule.starProjection_apply_eq_zero_iff
      (K := realHilbertTopEigenspace S) (v := x))

/-- A bounded operator acts as the identity after projecting onto its full
eigenvalue-one subspace. -/
theorem realHilbertTopEigenspace_comp_projection
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) :
    S.comp (realHilbertTopEigenspaceProjection S) =
      realHilbertTopEigenspaceProjection S := by
  apply ContinuousLinearMap.ext
  intro x
  change S ((realHilbertTopEigenspace S).starProjection x) =
    (realHilbertTopEigenspace S).starProjection x
  exact (realHilbertTopEigenspace_mem S _).1
    ((realHilbertTopEigenspace S).starProjection_apply_mem x)

/-- For a symmetric operator, projecting after applying the operator gives the
same top-sector component as projecting first.  The proof uses only the
canonical orthogonal decomposition: `x - P x` lies in the orthogonal
complement, and symmetry makes that complement invariant. -/
theorem realHilbertTopEigenspace_projection_comp
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) :
    (realHilbertTopEigenspaceProjection S).comp S =
      realHilbertTopEigenspaceProjection S := by
  let F := realHilbertTopEigenspace S
  have hFclosed : IsClosed (F : Set E) := by
    simpa [F] using realHilbertTopEigenspace_isClosed S
  letI : CompleteSpace F := hFclosed.completeSpace_coe
  apply ContinuousLinearMap.ext
  intro x
  change F.starProjection (S x) = F.starProjection x
  have hPxF : F.starProjection x ∈ F := F.starProjection_apply_mem x
  have hSPx : S (F.starProjection x) = F.starProjection x := by
    exact (realHilbertTopEigenspace_mem S _).1 (by simpa [F] using hPxF)
  have horth : x - F.starProjection x ∈ Fᗮ :=
    F.sub_starProjection_mem_orthogonal x
  have horth' : x - F.starProjection x ∈ (realHilbertTopEigenspace S)ᗮ := by
    change x - F.starProjection x ∈ Fᗮ
    exact horth
  have hSorth : S (x - F.starProjection x) ∈ Fᗮ := by
    exact realHilbertTopEigenspace_orthogonal_invariant S hS horth'
  have hPSorth : F.starProjection (S (x - F.starProjection x)) = 0 :=
    F.starProjection_apply_eq_zero_iff.mpr hSorth
  have hx : x = F.starProjection x + (x - F.starProjection x) := by
    abel
  calc
    F.starProjection (S x) =
        F.starProjection
          (S (F.starProjection x + (x - F.starProjection x))) :=
      congrArg (fun y : E => F.starProjection (S y)) hx
    _ = F.starProjection
          (S (F.starProjection x) + S (x - F.starProjection x)) := by
      rw [map_add]
    _ = F.starProjection
          (F.starProjection x + S (x - F.starProjection x)) := by
      rw [hSPx]
    _ = F.starProjection (F.starProjection x) +
          F.starProjection (S (x - F.starProjection x)) := by
      rw [map_add]
    _ = F.starProjection x + 0 := by
      rw [F.starProjection_eq_self_iff.mpr hPxF, hPSorth]
    _ = F.starProjection x := by
      rw [add_zero]

/-- Consequently a symmetric operator commutes with its canonical projection
onto the full eigenvalue-one sector. -/
theorem realHilbertTopEigenspace_projection_commutes
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) :
    S.comp (realHilbertTopEigenspaceProjection S) =
      (realHilbertTopEigenspaceProjection S).comp S := by
  rw [realHilbertTopEigenspace_comp_projection S,
    realHilbertTopEigenspace_projection_comp S hS]

/-- Canonical orthogonal projection onto the excited sector, the orthogonal
complement of the full eigenvalue-one space. -/
noncomputable def realHilbertTopEigenspaceOrthogonalProjection
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) : E →L[ℝ] E :=
  ((realHilbertTopEigenspace S)ᗮ).starProjection

/-- The excited-sector projection is exactly `I - P`, as supplied by Mathlib's
orthogonal-projection calculus. -/
theorem realHilbertTopEigenspaceOrthogonalProjection_eq_id_sub
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) :
    realHilbertTopEigenspaceOrthogonalProjection S =
      ContinuousLinearMap.id ℝ E - realHilbertTopEigenspaceProjection S := by
  simpa [realHilbertTopEigenspaceOrthogonalProjection,
    realHilbertTopEigenspaceProjection] using
    (Submodule.starProjection_orthogonal (realHilbertTopEigenspace S))

/-- The canonical excited-sector projection has exactly the orthogonal
complement as its range. -/
@[simp] theorem realHilbertTopEigenspaceOrthogonalProjection_range
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) :
    (realHilbertTopEigenspaceOrthogonalProjection S).range =
      (realHilbertTopEigenspace S)ᗮ := by
  simpa [realHilbertTopEigenspaceOrthogonalProjection] using
    (Submodule.range_starProjection ((realHilbertTopEigenspace S)ᗮ))

local instance periodicHypercubicEvenSpecialUnitaryTopSpectralProjectionPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- Canonical Mathlib orthogonal projection onto the entire eigenvalue-one
sector of the normalized finite Wilson physical transfer operator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  realHilbertTopEigenspaceProjection
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

/-- Its range is exactly the already-constructed full physical top eigenspace. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_range
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H N hN beta hbeta).range =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace] using
    (realHilbertTopEigenspaceProjection_range
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta))

/-- The finite Wilson top-sector projection is a canonical symmetric
projection in Mathlib's sense. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_isSymmetricProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H N hN beta hbeta).IsSymmetricProjection := by
  exact realHilbertTopEigenspaceProjection_isSymmetricProjection
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

/-- The chosen normalized physical vacuum is fixed by the canonical projection
onto the entire top sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_vacuum_fixed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta := by
  change
    realHilbertTopEigenspaceProjection
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta
  exact
    (realHilbertTopEigenspaceProjection_apply_eq_self_iff
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta)).2
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
        H N hN beta hbeta)

/-- The normalized physical transfer acts as the identity after projection onto
the full top sector. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_comp_topSpectralProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta := by
  exact realHilbertTopEigenspace_comp_projection
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

/-- Projecting after the normalized physical transfer gives the same top-sector
component. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_comp_normalizedTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H N hN beta hbeta).comp
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta := by
  exact realHilbertTopEigenspace_projection_comp
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta)

/-- Canonical projection onto the finite Wilson excited sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitedSpectralProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  realHilbertTopEigenspaceOrthogonalProjection
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

/-- The two canonical finite Wilson spectral-sector projections sum to the
identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitedSpectralProjection_eq_id_sub_top
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitedSpectralProjection
        H N hN beta hbeta =
      ContinuousLinearMap.id ℝ
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta := by
  exact realHilbertTopEigenspaceOrthogonalProjection_eq_id_sub
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

/-- Audit-visible reducing-decomposition package for the finite normalized
physical Wilson transfer.  The canonical Mathlib projection is linked to the
existing strict excited-sector contraction and positive transfer separation. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  projectionSymmetric :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H N hN beta hbeta).IsSymmetricProjection
  projectionRange :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H N hN beta hbeta).range =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta
  chosenVacuumFixed :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta
  transferAfterProjection :
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta
  projectionAfterTransfer :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H N hN beta hbeta).comp
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta
  excitedProjectionComplement :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitedSpectralProjection
        H N hN beta hbeta =
      ContinuousLinearMap.id ℝ
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta
  strictExcitedContraction :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ < 1
  transferGapPositive :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta

/-- Construct the canonical finite Wilson reducing spectral-sector package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjectionPackage
      H N hN beta hbeta :=
  { projectionSymmetric :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_isSymmetricProjection
        H N hN beta hbeta
    projectionRange :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_range
        H N hN beta hbeta
    chosenVacuumFixed :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_vacuum_fixed
        H N hN beta hbeta
    transferAfterProjection :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_comp_topSpectralProjection
        H N hN beta hbeta
    projectionAfterTransfer :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_comp_normalizedTransferOperator
        H N hN beta hbeta
    excitedProjectionComplement :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitedSpectralProjection_eq_id_sub_top
        H N hN beta hbeta
    strictExcitedContraction :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
    transferGapPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_pos
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferStableDirectSum
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set Filter Topology
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexBlockDiagonalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

local instance periodicHypercubicEvenSpecialUnitaryComplexBlockDiagonalTopCompleteSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta) := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace, S] using
    (complexHilbertTopEigenspace_isClosed S).completeSpace_coe

/-- Linear coordinates adapted to the intrinsic stable decomposition: the first
coordinate is the entire fixed/top sector and the second is the transient
sector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta ×
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta) ≃ₗ[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  Submodule.prodEquivOfIsCompl
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_isCompl_transientSubspace
      H N hN beta hbeta)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (uv :
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta ×
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv
        H N hN beta hbeta uv =
      (uv.1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) +
        (uv.2 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) := rfl

/-- The intrinsic CFC asymptotic projection is precisely the algebraic
projection onto the fixed summand along the transient summand. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_toLinearMap_eq_topTransientProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta hbeta).toLinearMap =
      Submodule.IsCompl.projection
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_isCompl_transientSubspace
          H N hN beta hbeta) := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection]
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection,
    complexHilbertTopEigenspaceProjection,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal] using
    (Submodule.toLinearMap_starProjection_eq_isComplProjection
      (K := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta))

/-- The normalized transfer restricted to the transient direct summand.  This is
only a naming layer over the already-constructed full-top orthogonal
restriction. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta →L[ℂ]
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta := by
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal] using
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator_coe
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
      H N hN beta hbeta) :
    ((periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator
        H N hN beta hbeta v :
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
        H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) =
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (v : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) := by
  rfl

/-- The transient block is a strict contraction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator_norm_lt_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator
      H N hN beta hbeta‖ < 1 := by
  simpa [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal] using
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta

/-- In stable/transient coordinates the genuine normalized complex Wilson
transfer is block diagonal: identity on the whole fixed sector and the strict
contraction on the transient sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_apply_topTransientLinearEquiv
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (uv :
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta ×
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv
          H N hN beta hbeta uv) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv
        H N hN beta hbeta
        (uv.1,
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator
            H N hN beta hbeta uv.2) := by
  change
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        ((uv.1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) +
          (uv.2 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) =
      (uv.1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) +
        ((periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator
            H N hN beta hbeta uv.2 :
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
            H N hN beta hbeta) :
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
  rw [map_add]
  have hu :
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta
          (uv.1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) =
        (uv.1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem
      H N hN beta hbeta
      (uv.1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)).1 uv.1.property
  rw [hu]
  rfl

/-- Equivalently, conjugating the normalized Wilson transfer by the intrinsic
stable/transient coordinate equivalence gives the diagonal action `(id, R)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv_symm_transfer_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (uv :
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta ×
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
          H N hN beta hbeta) :
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv
      H N hN beta hbeta).symm
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv
          H N hN beta hbeta uv)) =
      (uv.1,
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator
          H N hN beta hbeta uv.2) := by
  apply
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv
      H N hN beta hbeta).injective
  rw [LinearEquiv.apply_symm_apply]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_apply_topTransientLinearEquiv
      H N hN beta hbeta uv

/-- Audit-visible block-diagonal package for the genuine normalized complex
Wilson transfer. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferBlockDiagonalPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  projectionCoordinates :
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta hbeta).toLinearMap =
      Submodule.IsCompl.projection
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_isCompl_transientSubspace
          H N hN beta hbeta)
  blockAction :
    ∀ uv :
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta ×
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientSubspace
          H N hN beta hbeta,
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv
        H N hN beta hbeta).symm
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv
            H N hN beta hbeta uv)) =
        (uv.1,
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator
            H N hN beta hbeta uv.2)
  transientNormLtOne :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator
      H N hN beta hbeta‖ < 1

/-- The genuine normalized complex Wilson transfer has the exact intrinsic
block-diagonal form `id_F ⊕ R` with `‖R‖ < 1`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferBlockDiagonalPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferBlockDiagonalPackage
      H N hN beta hbeta where
  projectionCoordinates :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_toLinearMap_eq_topTransientProjection
      H N hN beta hbeta
  blockAction :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopTransientLinearEquiv_symm_transfer_apply
      H N hN beta hbeta
  transientNormLtOne :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransientTransferOperator_norm_lt_one
      H N hN beta hbeta

end
end MathlibAnalytic
end MGAP4D

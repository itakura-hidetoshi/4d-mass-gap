import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance physicalTopEigenspaceDecompositionCompleteSpace (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- The full normalized-transfer top eigenspace and its orthogonal complement
form an actual complementary pair in the finite-volume physical one-slice
Hilbert carrier.  No one-dimensionality of the top eigenspace is used. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isCompl_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsCompl
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) := by
  let F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta
  have hFclosed : IsClosed
      (F : Set
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
        H N hN beta hbeta
  letI : CompleteSpace F := hFclosed.completeSpace_coe
  simpa [F,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal] using
    (Submodule.isCompl_orthogonal (K := F))

/-- The full top eigenspace and its orthogonal complement span the entire
finite-volume physical one-slice Hilbert carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_sup_orthogonal_eq_top
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta ⊔
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta = ⊤ := by
  let F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta
  have hFclosed : IsClosed
      (F : Set
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
        H N hN beta hbeta
  letI : CompleteSpace F := hFclosed.completeSpace_coe
  simpa [F,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal] using
    (Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := F))

/-- Every physical one-slice vector decomposes into a vector in the full top
eigenspace plus a vector in its orthogonal complement. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_exists_top_add_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ∃ u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      u ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H N hN beta hbeta ∧
      ∃ f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
        f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H N hN beta hbeta ∧
        u + f = x := by
  have hx : x ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H N hN beta hbeta ⊔
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_sup_orthogonal_eq_top
      H N hN beta hbeta]
    trivial
  rwa [Submodule.mem_sup] at hx

/-- Audit-visible exact orthogonal decomposition of the finite-volume physical
one-slice Hilbert carrier into the full normalized-transfer top eigenspace and
its orthogonal complement. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopOrthogonalDecompositionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  complementary :
    IsCompl
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta)
  spansPhysicalCarrier :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta ⊔
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta = ⊤
  decomposes :
    ∀ x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      ∃ u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
        u ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
            H N hN beta hbeta ∧
        ∃ f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
          f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta ∧
          u + f = x

/-- Construct the exact one-slice top/orthogonal decomposition package from the
closed full top eigenspace and Mathlib's orthogonal projection theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopOrthogonalDecompositionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopOrthogonalDecompositionPackage
      H N hN beta hbeta :=
  { complementary :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isCompl_orthogonal
        H N hN beta hbeta
    spansPhysicalCarrier :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_sup_orthogonal_eq_top
        H N hN beta hbeta
    decomposes :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_exists_top_add_orthogonal
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
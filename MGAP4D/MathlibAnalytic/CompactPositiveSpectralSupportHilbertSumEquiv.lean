import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Module End
open scoped InnerProductSpace lp

noncomputable section

universe u

local instance realHilbertZeroEigenspaceSupportHilbertSumComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- Canonical intrinsic spectral coordinates on the strictly-positive support
of a compact positive real-Hilbert operator.  No enumeration of eigenvalues is
introduced: the coordinate index is Mathlib's intrinsic `Eigenvalues` subtype
of the support restriction. -/
noncomputable def realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    realHilbertZeroEigenspaceSupport T ≃ₗᵢ[ℝ]
      lp
        (fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        2 :=
  (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspaces_isHilbertSum
    T hCompact hPositive).linearIsometryEquiv

open Classical in
/-- A one-eigenspace coordinate reconstructs exactly the corresponding vector
in the actual positive spectral-support Hilbert space. -/
theorem realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
    (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive).symm (lp.single 2 mu v) =
      (v : realHilbertZeroEigenspaceSupport T) := by
  let hSum :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspaces_isHilbertSum
      T hCompact hPositive
  exact hSum.linearIsometryEquiv_symm_apply_single v

open Classical in
/-- On a reconstructed one-eigenspace coordinate the actual support
restriction acts by its strictly-positive eigenvalue. -/
theorem realHilbertZeroEigenspaceSupportRestriction_apply_eigenspacesHilbertSumEquiv_symm_single
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
    realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric
        ((realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
          T hCompact hPositive).symm (lp.single 2 mu v)) =
      (mu : ℝ) •
        (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
          T hCompact hPositive).symm (lp.single 2 mu v) := by
  rw [realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single]
  exact mem_eigenspace_iff.mp v.property

end

end MathlibAnalytic
end MGAP4D

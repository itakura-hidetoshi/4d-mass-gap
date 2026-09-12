import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportHilbertSumEquiv
import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalLinearPMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Module End
open scoped InnerProductSpace lp

noncomputable section

universe u

local instance spectralSupportLogGeneratorComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- Natural domain of the logarithmic generator on the actual positive spectral
support.  It is the inverse image, under the canonical spectral-coordinate
isometry, of the maximal weighted diagonal domain with weight `-log mu`. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGeneratorDomain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    Submodule ℝ (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
      T hCompact hPositive).domain.comap
    (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive).toLinearEquiv.toLinearMap

@[simp] theorem mem_realHilbertCompactPositiveZeroSupportLogGeneratorDomain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (x : realHilbertZeroEigenspaceSupport T) :
    x ∈ realHilbertCompactPositiveZeroSupportLogGeneratorDomain T hCompact hPositive ↔
      realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
          T hCompact hPositive x ∈
        (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
          T hCompact hPositive).domain :=
  Iff.rfl

/-- The logarithmic Hamiltonian directly on the actual positive spectral
support.  It is the maximal weighted diagonal operator in intrinsic spectral
coordinates, transported back by the canonical Hilbert-sum isometry. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGenerator
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    realHilbertZeroEigenspaceSupport T →ₗ.[ℝ]
      realHilbertZeroEigenspaceSupport T := by
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A :=
    realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
      T hCompact hPositive
  let D := realHilbertCompactPositiveZeroSupportLogGeneratorDomain T hCompact hPositive
  let lift : D →ₗ[ℝ] A.domain :=
    { toFun := fun x => ⟨U (x : realHilbertZeroEigenspaceSupport T), x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact U.map_add (x : realHilbertZeroEigenspaceSupport T) y
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact U.map_smul c (x : realHilbertZeroEigenspaceSupport T) }
  exact
    { domain := D
      toFun := U.symm.toLinearEquiv.toLinearMap.comp (A.toFun.comp lift) }

@[simp] theorem realHilbertCompactPositiveZeroSupportLogGenerator_domain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain =
      realHilbertCompactPositiveZeroSupportLogGeneratorDomain T hCompact hPositive := by
  rfl

/-- Exact coordinate formula for the support logarithmic generator: applying
the canonical spectral-coordinate isometry recovers the maximal weighted
coordinate operator. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain) :
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
        T hCompact hPositive
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x) =
      realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive
        ⟨realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
            T hCompact hPositive
            (x : realHilbertZeroEigenspaceSupport T),
          x.property⟩ := by
  exact (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
    T hCompact hPositive).apply_symm_apply _

end

end MathlibAnalytic
end MGAP4D

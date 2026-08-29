import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGenerator
import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalDenseSymmetric
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Module End
open scoped InnerProductSpace lp

noncomputable section

universe u

local instance spectralSupportLogGeneratorDenseSymmetricComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- The natural logarithmic-generator domain is dense in the actual positive
spectral-support Hilbert space.  This is the unitary pullback of the dense
maximal weighted diagonal domain in intrinsic spectral coordinates. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_dense_domain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    Dense
      (((realHilbertCompactPositiveZeroSupportLogGenerator
          T hCompact hPositive).domain :
        Submodule ℝ (realHilbertZeroEigenspaceSupport T)) :
        Set (realHilbertZeroEigenspaceSupport T)) := by
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A :=
    realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
      T hCompact hPositive
  have hDenseA : Dense (A.domain : Set _) := by
    simpa [A, realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates] using
      realHilbertSumWeightedDiagonalLinearPMap_dense_domain
        (G := fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
  change Dense (U ⁻¹' (A.domain : Set _))
  rw [dense_iff_closure_eq]
  rw [← U.toHomeomorph.preimage_closure]
  rw [hDenseA.closure_eq]
  simp

/-- The actual support logarithmic generator is formally symmetric.  The proof
is intrinsic: transport both inner products to the eigenspace Hilbert sum,
apply symmetry of the real weighted diagonal operator, and transport back. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_isFormalAdjoint_self
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    LinearPMap.IsFormalAdjoint (𝕜 := ℝ)
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive) := by
  intro x y
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A :=
    realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
      T hCompact hPositive
  let ux : A.domain := ⟨U (x : realHilbertZeroEigenspaceSupport T), x.property⟩
  let uy : A.domain := ⟨U (y : realHilbertZeroEigenspaceSupport T), y.property⟩
  have hA : LinearPMap.IsFormalAdjoint (𝕜 := ℝ) A A := by
    simpa [A, realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates] using
      realHilbertSumWeightedDiagonalLinearPMap_isFormalAdjoint_self
        (G := fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
  calc
    inner ℝ
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x)
        (y : realHilbertZeroEigenspaceSupport T) =
      inner ℝ
        (U (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x))
        (U (y : realHilbertZeroEigenspaceSupport T)) := by
          symm
          exact U.inner_map_map _ _
    _ = inner ℝ (A ux) (uy : _) := by
      rw [realHilbertCompactPositiveZeroSupportLogGenerator_coordinates]
      rfl
    _ = inner ℝ (ux : _) (A uy) := hA ux uy
    _ = inner ℝ
        (U (x : realHilbertZeroEigenspaceSupport T))
        (U (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive y)) := by
      rw [realHilbertCompactPositiveZeroSupportLogGenerator_coordinates]
      rfl
    _ = inner ℝ
        (x : realHilbertZeroEigenspaceSupport T)
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive y) :=
      U.inner_map_map _ _

/-- Audit package for the first actual-support operator-theoretic stage of the
spectral logarithm. -/
structure RealHilbertCompactPositiveZeroSupportLogGeneratorDenseSymmetricPackage
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) : Prop where
  denseDomain : Dense
    (((realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).domain : Submodule ℝ (realHilbertZeroEigenspaceSupport T)) :
      Set (realHilbertZeroEigenspaceSupport T))
  formallySymmetric : LinearPMap.IsFormalAdjoint (𝕜 := ℝ)
    (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
    (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)

/-- Construct the dense/formally-symmetric actual-support logarithmic package. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorDenseSymmetricPackage
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    RealHilbertCompactPositiveZeroSupportLogGeneratorDenseSymmetricPackage
      T hCompact hPositive :=
  ⟨realHilbertCompactPositiveZeroSupportLogGenerator_dense_domain T hCompact hPositive,
    realHilbertCompactPositiveZeroSupportLogGenerator_isFormalAdjoint_self
      T hCompact hPositive⟩

end

end MathlibAnalytic
end MGAP4D

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
  have hDenseCoord :
      Dense
        ((((realHilbertSumWeightedDiagonalLinearPMap
          (G := fun mu : Eigenvalues
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
            eigenspace
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
          (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)).domain :
            Submodule ℝ
              (lp
                (fun mu : Eigenvalues
                  (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                    Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
                  eigenspace
                    (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                      Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
                2)) : Set _) :=
    realHilbertSumWeightedDiagonalLinearPMap_dense_domain
      (G := fun mu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
      (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
  change Dense
    (U ⁻¹'
      ((((realHilbertSumWeightedDiagonalLinearPMap
        (G := fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)).domain :
          Submodule ℝ _) : Set _))
  rw [dense_iff_closure_eq]
  rw [← U.toHomeomorph.preimage_closure]
  rw [hDenseCoord.closure_eq]
  simp

/-- The actual support logarithmic generator is formally symmetric.  The proof
stays entirely on the support Hilbert carrier: both inner products are
transported to intrinsic spectral coordinates, expanded by `lp.inner_eq_tsum`,
and compared pointwise using the reality of the logarithmic weights.  No
adjoint or formal-adjoint structure is instantiated on the dependent `lp`
carrier, avoiding the algebraic/Hilbert module-instance diamond there. -/
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
  calc
    inner ℝ
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x)
        (y : realHilbertZeroEigenspaceSupport T) =
      inner ℝ
        (U (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x))
        (U (y : realHilbertZeroEigenspaceSupport T)) := by
          symm
          exact U.inner_map_map _ _
    _ = inner ℝ
        (⟨fun mu =>
            realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
              (U (x : realHilbertZeroEigenspaceSupport T)) mu,
          x.property⟩ : lp _ 2)
        (U (y : realHilbertZeroEigenspaceSupport T)) := by
      rw [realHilbertCompactPositiveZeroSupportLogGenerator_coordinates]
    _ = inner ℝ
        (U (x : realHilbertZeroEigenspaceSupport T))
        (⟨fun mu =>
            realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
              (U (y : realHilbertZeroEigenspaceSupport T)) mu,
          y.property⟩ : lp _ 2) := by
      rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
      apply tsum_congr
      intro mu
      rw [real_inner_smul_left, real_inner_smul_right]
    _ = inner ℝ
        (U (x : realHilbertZeroEigenspaceSupport T))
        (U (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive y)) := by
      rw [realHilbertCompactPositiveZeroSupportLogGenerator_coordinates]
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

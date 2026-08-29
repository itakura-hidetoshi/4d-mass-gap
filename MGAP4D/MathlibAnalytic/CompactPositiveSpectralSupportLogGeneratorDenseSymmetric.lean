import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGenerator
import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalDenseSymmetric
import Mathlib.Analysis.InnerProductSpace.Basic
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
        (((realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
          T hCompact hPositive).domain : Submodule ℝ _) : Set _) := by
    simpa [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates] using
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
      (((realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive).domain : Submodule ℝ _) : Set _))
  rw [dense_iff_closure_eq]
  rw [← U.toHomeomorph.preimage_closure]
  rw [hDenseCoord.closure_eq]
  simp

/-- A real linear isometric equivalence preserves inner products even when its
target carries two propositionally equal but non-definitional module-instance
paths.  The proof only uses the metric data of the equivalence and real
polarization, so it does not ask Lean to identify those module structures. -/
theorem realHilbertCompactPositive_zeroSupportHilbertSumEquiv_inner_map_map
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (x y : realHilbertZeroEigenspaceSupport T) :
    inner ℝ
        (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
          T hCompact hPositive x)
        (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
          T hCompact hPositive y) =
      inner ℝ x y := by
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
      (U x) (U y),
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y]
  rw [← U.map_add]
  rw [U.norm_map, U.norm_map, U.norm_map]

/-- The actual support logarithmic generator is formally symmetric.  The proof
stays entirely on the support Hilbert carrier.  Metric polarization transports
the two inner products to intrinsic spectral coordinates, and the already
kernel-checked coordinate action theorem reduces symmetry pointwise to the
reality of the logarithmic weights.  No adjoint structure is instantiated on
the dependent `lp` carrier. -/
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
  let xCoord :
      (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive).domain :=
    ⟨U (x : realHilbertZeroEigenspaceSupport T), x.property⟩
  let yCoord :
      (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive).domain :=
    ⟨U (y : realHilbertZeroEigenspaceSupport T), y.property⟩
  calc
    inner ℝ
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x)
        (y : realHilbertZeroEigenspaceSupport T) =
      inner ℝ
        (U (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x))
        (U (y : realHilbertZeroEigenspaceSupport T)) := by
      symm
      exact realHilbertCompactPositive_zeroSupportHilbertSumEquiv_inner_map_map
        T hCompact hPositive _ _
    _ = inner ℝ
        (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
          T hCompact hPositive xCoord)
        (U (y : realHilbertZeroEigenspaceSupport T)) := by
      rw [realHilbertCompactPositiveZeroSupportLogGenerator_coordinates]
    _ = inner ℝ
        (U (x : realHilbertZeroEigenspaceSupport T))
        (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
          T hCompact hPositive yCoord) := by
      rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
      apply tsum_congr
      intro mu
      rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply,
        realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply,
        real_inner_smul_left, real_inner_smul_right]
    _ = inner ℝ
        (U (x : realHilbertZeroEigenspaceSupport T))
        (U (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive y)) := by
      rw [realHilbertCompactPositiveZeroSupportLogGenerator_coordinates]
    _ = inner ℝ
        (x : realHilbertZeroEigenspaceSupport T)
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive y) :=
      realHilbertCompactPositive_zeroSupportHilbertSumEquiv_inner_map_map
        T hCompact hPositive _ _

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

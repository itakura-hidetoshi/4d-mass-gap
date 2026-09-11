import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformInverseSquareRootPositiveBranchEigenvalue
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- Bounded inverse data for the canonical positive shifted square `1 + A²`.

This isolates the coercive inverse problem from the subsequent bounded positive-square-root
problem. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  inverse : H →L[ℝ] H
  selfAdjoint : IsSelfAdjoint inverse
  quadraticForm_nonnegative :
    ∀ x : H, 0 ≤ inner ℝ (inverse x) x
  norm_le_one : ‖inverse‖ ≤ 1
  range_mem_shiftedSquare_domain :
    ∀ x : H,
      inverse x ∈
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain
  shiftedSquare_inverse :
    ∀ x : H,
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          ⟨inverse x, range_mem_shiftedSquare_domain x⟩ = x

/-- A positive bounded square root of the bounded shifted-square inverse.

The square-root stage is deliberately separated from construction of the inverse itself. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) where
  squareRoot : H →L[ℝ] H
  selfAdjoint : IsSelfAdjoint squareRoot
  quadraticForm_nonnegative :
    ∀ x : H, 0 ≤ inner ℝ (squareRoot x) x
  range_mem_shiftedSquare_domain :
    ∀ x : H,
      squareRoot x ∈
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain
  squareRoot_sq :
    ∀ x : H, squareRoot (squareRoot x) = K.inverse x

/-- Combining a bounded shifted-square inverse with its positive bounded square root
recovers the preceding positive inverse-square-root boundary. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootData.toPositiveInverseSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootData K) :
    StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootData A where
  inverseSquareRoot := R.squareRoot
  selfAdjoint := R.selfAdjoint
  quadraticForm_nonnegative := R.quadraticForm_nonnegative
  range_mem_shiftedSquare_domain := R.range_mem_shiftedSquare_domain
  shiftedSquare_inverseSquareRoot_sq := fun x => by
    have hDomainEq :
        (⟨R.squareRoot (R.squareRoot x),
            R.range_mem_shiftedSquare_domain (R.squareRoot x)⟩ :
          (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain) =
        ⟨K.inverse x, K.range_mem_shiftedSquare_domain x⟩ := by
      apply Subtype.ext
      exact R.squareRoot_sq x
    rw [hDomainEq]
    exact K.shiftedSquare_inverse x

/-- Uniform construction of bounded inverses for the canonical shifted square. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A

/-- Uniform construction of positive bounded square roots of already-constructed bounded
shifted-square inverses. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (core : RealHilbertSelfAdjointCore A)
      (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A),
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootData K

/-- The two independent generic stages reconstruct the preceding positive inverse-square-root
constructor. -/
def standardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootDataConstructor_of_boundedInverse_and_squareRoot
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor)
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootDataConstructor where
  construct := fun A core =>
    let inverseData := K.construct A core
    (R.construct A core inverseData).toPositiveInverseSquareRootData

/-- Operator-construction pipeline factored through the bounded inverse of `1 + A²` and a
positive bounded square root of that inverse. -/
structure BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  boundedInverse :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor
  positiveSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Collapse the bounded-inverse factorization to the preceding positive-branch pipeline. -/
def BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toPositiveBranch
    (P : BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    PositiveBranchStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  inverseSquareRoot :=
    standardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootDataConstructor_of_boundedInverse_and_squareRoot
      P.boundedInverse P.positiveSquareRoot
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The factored route supplies the unchanged bounded-transform operator-data constructor. -/
def BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toPositiveBranch.toOperatorDataConstructor

/-- The bounded-inverse-factored operator construction followed by the independent spectral
pullback and bounded Borel spectral theorem. -/
structure BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the bounded-inverse-factored route to the preceding positive-branch Borel route. -/
def BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toPositiveBranch
    (P : BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toPositiveBranch
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The factored route yields the unchanged generic real-Hilbert spectral-resolution
constructor. -/
def BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toPositiveBranch.toConstructor

/-- The factored route specializes to the unchanged reconstructed Wightman OS interface. -/
def BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toPositiveBranch.toExplicitWightmanOSConstructor

end

end MathlibAnalytic
end MGAP4D

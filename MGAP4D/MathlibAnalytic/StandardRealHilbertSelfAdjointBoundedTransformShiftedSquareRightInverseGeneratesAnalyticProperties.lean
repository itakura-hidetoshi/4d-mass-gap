import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformInverseSquareRootFactorsThroughBoundedInverse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The strictly smaller bounded-inverse boundary for the canonical positive shifted square.

Self-adjointness, quadratic-form nonnegativity, and the contraction estimate are omitted:
they follow from formal symmetry, positivity, and the norm lower bound of `1 + A²`. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  inverse : H →L[ℝ] H
  range_mem_shiftedSquare_domain :
    ∀ x : H,
      inverse x ∈
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain
  shiftedSquare_inverse :
    ∀ x : H,
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          ⟨inverse x, range_mem_shiftedSquare_domain x⟩ = x

/-- The coercive lower bound of `1 + A²` gives the pointwise contraction estimate for
its bounded right inverse. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData.inverse_norm_apply_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    ‖K.inverse x‖ ≤ ‖x‖ := by
  let xDomain :
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain :=
    ⟨K.inverse x, K.range_mem_shiftedSquare_domain x⟩
  have h :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_norm_lower_bound_one
      A core xDomain
  rw [K.shiftedSquare_inverse x] at h
  simpa [xDomain] using h

/-- The operator-norm contraction is generated from the pointwise coercive estimate. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData.inverse_norm_le_one
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    ‖K.inverse‖ ≤ 1 := by
  apply K.inverse.opNorm_le_bound zero_le_one
  intro x
  simpa using K.inverse_norm_apply_le core x

/-- Formal symmetry of `1 + A²`, together with the right-inverse law, makes the bounded
inverse symmetric on the ambient Hilbert space. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData.inverse_isSymmetric
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    (K.inverse : H →ₗ[ℝ] H).IsSymmetric := by
  intro x y
  let xDomain :
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain :=
    ⟨K.inverse x, K.range_mem_shiftedSquare_domain x⟩
  let yDomain :
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain :=
    ⟨K.inverse y, K.range_mem_shiftedSquare_domain y⟩
  have hFormal :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_isFormalAdjoint
      A core xDomain yDomain
  calc
    inner ℝ (K.inverse x) y =
        inner ℝ (K.inverse x)
          (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A yDomain) := by
      rw [K.shiftedSquare_inverse y]
    _ = inner ℝ
          (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A xDomain)
          (K.inverse y) := by
      symm
      exact hFormal
    _ = inner ℝ x (K.inverse y) := by
      rw [K.shiftedSquare_inverse x]

/-- Every bounded symmetric operator on a complete Hilbert space is self-adjoint. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData.inverse_selfAdjoint
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    IsSelfAdjoint K.inverse := by
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (K.inverse_isSymmetric core)

/-- Positivity of `1 + A²` transfers to its bounded right inverse. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData.inverse_quadraticForm_nonnegative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    0 ≤ inner ℝ (K.inverse x) x := by
  let xDomain :
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain :=
    ⟨K.inverse x, K.range_mem_shiftedSquare_domain x⟩
  have hPositive :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_quadraticForm_nonnegative
      A core xDomain
  calc
    0 ≤ inner ℝ
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A xDomain)
        (xDomain : H) := hPositive
    _ = inner ℝ (K.inverse x) x := by
      rw [K.shiftedSquare_inverse x]
      exact real_inner_comm _ _

/-- Reconstruct the preceding bounded-inverse certificate from only a bounded right inverse
whose range lies in the natural square domain. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData.toBoundedInverseData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A where
  inverse := K.inverse
  selfAdjoint := K.inverse_selfAdjoint core
  quadraticForm_nonnegative := K.inverse_quadraticForm_nonnegative core
  norm_le_one := K.inverse_norm_le_one core
  range_mem_shiftedSquare_domain := K.range_mem_shiftedSquare_domain
  shiftedSquare_inverse := K.shiftedSquare_inverse

/-- Uniform construction of only the remaining bounded-right-inverse data. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A

/-- Recover the preceding bounded-inverse constructor. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseDataConstructor.toBoundedInverseDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor where
  construct := fun A core => (C.construct A core).toBoundedInverseData core

/-- The bounded-transform construction with all analytic properties of the shifted-square
inverse generated from its right-inverse law. -/
structure RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  rightInverse :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseDataConstructor
  positiveSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Collapse the right-inverse route to the preceding bounded-inverse factorization. -/
def RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toBoundedInverseFactored
    (P : RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  boundedInverse := P.rightInverse.toBoundedInverseDataConstructor
  positiveSquareRoot := P.positiveSquareRoot
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The right-inverse route supplies the unchanged bounded-transform operator-data constructor. -/
def RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toBoundedInverseFactored.toOperatorDataConstructor

/-- The right-inverse-factored operator construction followed by the independent spectral
pullback and bounded Borel spectral theorem. -/
structure RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the right-inverse route to the preceding bounded-inverse-factored Borel route. -/
def RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toBoundedInverseFactored
    (P : RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    BoundedInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toBoundedInverseFactored
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The right-inverse route yields the unchanged generic real-Hilbert spectral-resolution
constructor. -/
def RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toBoundedInverseFactored.toConstructor

/-- The right-inverse route specializes to the unchanged reconstructed Wightman OS interface. -/
def RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toBoundedInverseFactored.toExplicitWightmanOSConstructor

/-- The right-inverse route plus actual-model measurable PVM identification yields physical
indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_rightInverseFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_positiveBranchFactoredStandardBoundedTransformBorelPipeline
      P.toBoundedInverseFactored.toPositiveBranch M X

/-- Adding the scalar-measure quadratic law yields the unchanged canonical physical
eigenprojection law. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_rightInverseFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_positiveBranchFactoredStandardBoundedTransformBorelPipeline
      P.toBoundedInverseFactored.toPositiveBranch M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

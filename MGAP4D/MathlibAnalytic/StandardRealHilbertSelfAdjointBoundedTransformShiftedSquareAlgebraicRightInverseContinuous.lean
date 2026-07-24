import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformShiftedSquareRightInverseGeneratesAnalyticProperties
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The canonical shifted-square inverse before continuity is imposed.

The inverse lands directly in the natural square domain.  Coercivity of `1 + A²`
will generate the ambient norm estimate and hence the continuous linear inverse. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  inverseToDomain :
    H →ₗ[ℝ]
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain
  shiftedSquare_inverse :
    ∀ x : H,
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          (inverseToDomain x) = x

/-- The ambient linear map underlying the algebraic domain-valued inverse. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData.ambientLinearMap
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData A) :
    H →ₗ[ℝ] H :=
  (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain.subtype.comp
    J.inverseToDomain

@[simp] theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData.ambientLinearMap_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData A)
    (x : H) :
    J.ambientLinearMap x = (J.inverseToDomain x : H) :=
  rfl

/-- Coercivity makes the algebraic inverse contractive in the ambient Hilbert norm. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData.ambientLinearMap_norm_apply_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    ‖J.ambientLinearMap x‖ ≤ ‖x‖ := by
  have h :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_norm_lower_bound_one
      A core (J.inverseToDomain x)
  rw [J.shiftedSquare_inverse x] at h
  simpa using h

/-- The algebraic inverse becomes continuous with sharp bound one. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData.inverse
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    H →L[ℝ] H :=
  J.ambientLinearMap.mkContinuous 1 (fun x => by
    simpa using J.ambientLinearMap_norm_apply_le core x)

@[simp] theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData.inverse_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    J.inverse core x = (J.inverseToDomain x : H) :=
  rfl

/-- The continuous inverse still lands in the canonical square domain. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData.inverse_mem_shiftedSquare_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    J.inverse core x ∈
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain := by
  change (J.inverseToDomain x : H) ∈
    (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain
  exact (J.inverseToDomain x).property

/-- Continuization preserves the exact shifted-square right-inverse law. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData.shiftedSquare_continuousInverse
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
        ⟨J.inverse core x, J.inverse_mem_shiftedSquare_domain core x⟩ = x := by
  have hDomainEq :
      (⟨J.inverse core x, J.inverse_mem_shiftedSquare_domain core x⟩ :
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain) =
      J.inverseToDomain x := by
    apply Subtype.ext
    rfl
  rw [hDomainEq]
  exact J.shiftedSquare_inverse x

/-- Recover the preceding bounded right-inverse boundary from purely algebraic,
domain-valued inverse data. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData.toRightInverseData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A where
  inverse := J.inverse core
  range_mem_shiftedSquare_domain := J.inverse_mem_shiftedSquare_domain core
  shiftedSquare_inverse := J.shiftedSquare_continuousInverse core

/-- Uniform construction of algebraic domain-valued right inverses. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseData A

/-- Recover the preceding bounded-right-inverse constructor by coercive continuization. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseDataConstructor.toRightInverseDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseDataConstructor where
  construct := fun A core => (C.construct A core).toRightInverseData core

/-- The bounded-transform construction with the shifted-square inverse supplied only as an
algebraic map into the natural square domain. -/
structure AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  algebraicRightInverse :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAlgebraicRightInverseDataConstructor
  positiveSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Collapse the algebraic-right-inverse route to the preceding continuous right-inverse
factorization. -/
def AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toRightInverseFactored
    (P : AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  rightInverse := P.algebraicRightInverse.toRightInverseDataConstructor
  positiveSquareRoot := P.positiveSquareRoot
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The algebraic-right-inverse route supplies the unchanged bounded-transform operator-data
constructor. -/
def AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toRightInverseFactored.toOperatorDataConstructor

/-- The algebraic-right-inverse operator construction followed by the independent spectral
pullback and bounded Borel spectral theorem. -/
structure AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the algebraic-right-inverse Borel route to the preceding continuous route. -/
def AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toRightInverseFactored
    (P : AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toRightInverseFactored
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The algebraic-right-inverse route yields the unchanged generic real-Hilbert
spectral-resolution constructor. -/
def AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toRightInverseFactored.toConstructor

/-- The same route specializes to the unchanged reconstructed Wightman OS interface. -/
def AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toRightInverseFactored.toExplicitWightmanOSConstructor

/-- The algebraic-right-inverse route plus actual-model measurable PVM identification yields
physical indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_algebraicRightInverseFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_rightInverseFactoredStandardBoundedTransformBorelPipeline
      P.toRightInverseFactored M X

/-- Adding the scalar-measure quadratic law yields the unchanged canonical physical
eigenprojection law. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_algebraicRightInverseFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : AlgebraicRightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_rightInverseFactoredStandardBoundedTransformBorelPipeline
      P.toRightInverseFactored M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformSquareDomain
import Mathlib.Algebra.Module.Submodule.Map

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The natural square domain transported from the subtype `A.domain` to the ambient
Hilbert space. -/
def standardRealHilbertSelfAdjointAmbientSquareDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) : Submodule ℝ H :=
  (standardRealHilbertSelfAdjointSquareDomain A).map A.domain.subtype

/-- The subtype square domain and its ambient image are canonically linearly equivalent
because the domain inclusion is injective. -/
noncomputable def standardRealHilbertSelfAdjointSquareDomainEquivAmbient
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) :
    standardRealHilbertSelfAdjointSquareDomain A ≃ₗ[ℝ]
      standardRealHilbertSelfAdjointAmbientSquareDomain A :=
  Submodule.equivMapOfInjective A.domain.subtype
    (Submodule.subtype_injective A.domain)
    (standardRealHilbertSelfAdjointSquareDomain A)

@[simp] theorem standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H)
    (x : standardRealHilbertSelfAdjointSquareDomain A) :
    ((standardRealHilbertSelfAdjointSquareDomainEquivAmbient A x :
        standardRealHilbertSelfAdjointAmbientSquareDomain A) : H) =
      ((x : A.domain) : H) := by
  exact
    Submodule.coe_equivMapOfInjective_apply A.domain.subtype
      (Submodule.subtype_injective A.domain)
      (standardRealHilbertSelfAdjointSquareDomain A) x

/-- The canonical ambient `LinearPMap` realization of `1 + A²` on its natural square
domain.  No extension certificate is needed for the operator or its domain. -/
def standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) : H →ₗ.[ℝ] H where
  domain := standardRealHilbertSelfAdjointAmbientSquareDomain A
  toFun :=
    (standardRealHilbertSelfAdjointShiftedSquareAction A).comp
      (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).symm.toLinearMap

@[simp] theorem standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) :
    (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain =
      standardRealHilbertSelfAdjointAmbientSquareDomain A :=
  rfl

/-- On the transported natural domain, the canonical ambient `LinearPMap` agrees with
the already-constructed algebraic shifted-square action. -/
@[simp] theorem standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H)
    (x : standardRealHilbertSelfAdjointSquareDomain A) :
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
        (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A x) =
      standardRealHilbertSelfAdjointShiftedSquareAction A x := by
  change
    standardRealHilbertSelfAdjointShiftedSquareAction A
        ((standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).symm
          (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A x)) =
      standardRealHilbertSelfAdjointShiftedSquareAction A x
  rw [LinearEquiv.symm_apply_apply]

/-- The exact residual after constructing the ambient domain and `LinearPMap` itself.
Only the three analytic properties of the canonical shifted square remain. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  selfAdjoint :
    IsSelfAdjoint (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A)
  quadraticForm_nonnegative :
    ∀ x : (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain,
      0 ≤ ⟪standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x,
        (x : H)⟫_ℝ
  norm_lower_bound_one :
    ∀ x : (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain,
      ‖(x : H)‖ ≤
        ‖standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x‖

/-- The three analytic properties of the canonical operator supply the previous ambient
extension boundary; its operator, domain lift, and agreement law are now canonical. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticData.toPositiveShiftedSquareExtensionData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (X : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticData A) :
    StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionData A where
  positiveShiftedSquare :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
  squareDomainLift :=
    (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).toLinearMap
  squareDomainLift_coe := by
    intro x
    exact standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe A x
  agrees_with_shiftedSquareAction := by
    intro x
    exact standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply A x
  selfAdjoint := X.selfAdjoint
  quadraticForm_nonnegative := X.quadraticForm_nonnegative
  norm_lower_bound_one := X.norm_lower_bound_one

/-- Uniform construction of the three remaining analytic properties of the canonical
positive shifted square. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticData A

/-- Recover the previous extension constructor from the strictly smaller analytic
certificate. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticDataConstructor.toPositiveShiftedSquareExtensionDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticDataConstructor) :
    StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionDataConstructor where
  construct := fun A core =>
    (C.construct A core).toPositiveShiftedSquareExtensionData

/-- The standard bounded-transform operator construction with the first stage reduced to
three analytic properties of the canonical ambient `1 + A²` operator. -/
structure AmbientSquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  positiveShiftedSquareAnalytic :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticDataConstructor
  inverseSquareRoot :
    StandardRealHilbertSelfAdjointInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Forget the canonical ambient-domain refinement and recover the square-domain
pipeline from the preceding stage. -/
def AmbientSquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toSquareDomain
    (P : AmbientSquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    SquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  positiveShiftedSquareExtension :=
    P.positiveShiftedSquareAnalytic.toPositiveShiftedSquareExtensionDataConstructor
  inverseSquareRoot := P.inverseSquareRoot
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The canonical ambient-domain construction supplies the existing bounded-transform
operator-data constructor. -/
def AmbientSquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : AmbientSquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toSquareDomain.toOperatorDataConstructor

/-- The canonical ambient shifted square followed by the independent measurable
pullback and bounded Borel spectral theorem. -/
structure AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    AmbientSquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the ambient-domain route to the preceding square-domain factored route. -/
def AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toSquareDomainFactored
    (P : AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toSquareDomain
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The ambient-domain-refined route yields the unchanged generic spectral-resolution
constructor. -/
def AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toSquareDomainFactored.toConstructor

/-- The same route specializes to the reconstructed Wightman OS boundary. -/
def AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toSquareDomainFactored.toExplicitWightmanOSConstructor

/-- With the independent actual-model measurable PVM identification certificate, the
ambient-domain route yields indicator evaluation in the physical model. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_ambientSquareDomainFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_squareDomainFactoredStandardBoundedTransformBorelPipeline
      P.toSquareDomainFactored M X

/-- Adding the scalar-measure quadratic law yields the canonical eigenprojection law
without changing the actual physical-model assumptions. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_ambientSquareDomainFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_squareDomainFactoredStandardBoundedTransformBorelPipeline
      P.toSquareDomainFactored M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

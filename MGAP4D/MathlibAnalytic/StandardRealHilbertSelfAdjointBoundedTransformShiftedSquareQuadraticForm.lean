import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformAmbientSquareDomain
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- A real-Hilbert self-adjoint core makes its operator a formal adjoint of itself on
its domain. -/
theorem realHilbertSelfAdjointCore_isFormalSelfAdjoint
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (core : RealHilbertSelfAdjointCore A) :
    A.IsFormalAdjoint A := by
  have hFormal : A.adjoint.IsFormalAdjoint A :=
    LinearPMap.adjoint_isFormalAdjoint core.denseDomain
  have hAdjoint : A.adjoint = A :=
    LinearPMap.isSelfAdjoint_def.mp core.selfAdjoint
  rw [hAdjoint] at hFormal
  exact hFormal

/-- On the natural square domain, the quadratic form of the canonical shifted square
is exactly `‖x‖² + ‖A x‖²`. -/
theorem standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_quadraticForm_identity
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : standardRealHilbertSelfAdjointSquareDomain A) :
    inner ℝ
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A x))
        ((standardRealHilbertSelfAdjointSquareDomainEquivAmbient A x :
          standardRealHilbertSelfAdjointAmbientSquareDomain A) : H) =
      ‖((x : A.domain) : H)‖ ^ 2 + ‖A (x : A.domain)‖ ^ 2 := by
  have hFormal : A.IsFormalAdjoint A :=
    realHilbertSelfAdjointCore_isFormalSelfAdjoint core
  have hSquare :
      inner ℝ
          (standardRealHilbertSelfAdjointSquareAction A x)
          ((x : A.domain) : H) =
        ‖A (x : A.domain)‖ ^ 2 := by
    rw [standardRealHilbertSelfAdjointSquareAction_apply]
    calc
      inner ℝ
          (A (standardRealHilbertSelfAdjointSquareToDomain A x))
          ((x : A.domain) : H) =
          inner ℝ
            ((standardRealHilbertSelfAdjointSquareToDomain A x : A.domain) : H)
            (A (x : A.domain)) :=
        hFormal (standardRealHilbertSelfAdjointSquareToDomain A x) (x : A.domain)
      _ = inner ℝ (A (x : A.domain)) (A (x : A.domain)) := by
        rw [standardRealHilbertSelfAdjointSquareToDomain_coe]
      _ = ‖A (x : A.domain)‖ ^ 2 := by
        exact real_inner_self_eq_norm_sq (A (x : A.domain))
  rw [standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply,
    standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe,
    standardRealHilbertSelfAdjointShiftedSquareAction_apply,
    inner_add_left, real_inner_self_eq_norm_sq, hSquare]

/-- The canonical shifted square has nonnegative quadratic form.  This is generated
from formal self-adjointness of `A`; it is no longer residual certificate data. -/
theorem standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_quadraticForm_nonnegative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain) :
    0 ≤ inner ℝ
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x)
      (x : H) := by
  let y : standardRealHilbertSelfAdjointSquareDomain A :=
    (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).symm x
  have hx :
      standardRealHilbertSelfAdjointSquareDomainEquivAmbient A y = x :=
    LinearEquiv.apply_symm_apply
      (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A) x
  rw [← hx,
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_quadraticForm_identity
      A core y]
  positivity

/-- The canonical shifted square is bounded below by one in norm.  The proof is the
standard coercivity argument: the quadratic identity followed by real Cauchy--Schwarz. -/
theorem standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_norm_lower_bound_one
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain) :
    ‖(x : H)‖ ≤
      ‖standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x‖ := by
  have hquad :
      ‖(x : H)‖ ^ 2 ≤
        inner ℝ
          (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x)
          (x : H) := by
    let y : standardRealHilbertSelfAdjointSquareDomain A :=
      (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).symm x
    have hx :
        standardRealHilbertSelfAdjointSquareDomainEquivAmbient A y = x :=
      LinearEquiv.apply_symm_apply
        (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A) x
    rw [← hx,
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_quadraticForm_identity
        A core y,
      standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe]
    positivity
  have hcs :
      inner ℝ
          (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x)
          (x : H) ≤
        ‖standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x‖ *
          ‖(x : H)‖ :=
    real_inner_le_norm
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x)
      (x : H)
  by_cases hpos : 0 < ‖(x : H)‖
  · have hmul :
        ‖(x : H)‖ * ‖(x : H)‖ ≤
          ‖standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x‖ *
            ‖(x : H)‖ := by
      calc
        ‖(x : H)‖ * ‖(x : H)‖ = ‖(x : H)‖ ^ 2 := by ring
        _ ≤ inner ℝ
            (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x)
            (x : H) := hquad
        _ ≤ ‖standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x‖ *
            ‖(x : H)‖ := hcs
    nlinarith
  · have hxnorm : ‖(x : H)‖ = 0 :=
      le_antisymm (le_of_not_gt hpos) (norm_nonneg _)
    rw [hxnorm]
    exact norm_nonneg _

/-- After the quadratic form identity and coercive norm bound are generated, the sole
remaining first-stage datum is self-adjointness of the canonical `1 + A²` operator. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSelfAdjointData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  selfAdjoint :
    IsSelfAdjoint (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A)

/-- The self-adjointness-only certificate reconstructs the previous three-field analytic
data because nonnegativity and the norm lower bound are now theorems. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSelfAdjointData.toAnalyticData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (X : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSelfAdjointData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticData A where
  selfAdjoint := X.selfAdjoint
  quadraticForm_nonnegative :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_quadraticForm_nonnegative
      A core
  norm_lower_bound_one :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_norm_lower_bound_one
      A core

/-- Uniform construction of only the remaining self-adjointness property. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSelfAdjointDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSelfAdjointData A

/-- Recover the preceding three-field analytic constructor from self-adjointness alone. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSelfAdjointDataConstructor.toAnalyticDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSelfAdjointDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareAnalyticDataConstructor where
  construct := fun A core => (C.construct A core).toAnalyticData core

/-- The standard bounded-transform construction with its first stage reduced to
self-adjointness of the canonical ambient shifted square. -/
structure SelfAdjointShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  positiveShiftedSquareSelfAdjoint :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSelfAdjointDataConstructor
  inverseSquareRoot :
    StandardRealHilbertSelfAdjointInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Forget the quadratic-form closure and recover the preceding ambient-domain pipeline. -/
def SelfAdjointShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toAmbientSquareDomain
    (P : SelfAdjointShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    AmbientSquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  positiveShiftedSquareAnalytic :=
    P.positiveShiftedSquareSelfAdjoint.toAnalyticDataConstructor
  inverseSquareRoot := P.inverseSquareRoot
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The self-adjointness-only first stage supplies the existing bounded-transform
operator-data constructor. -/
def SelfAdjointShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : SelfAdjointShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toAmbientSquareDomain.toOperatorDataConstructor

/-- The self-adjointness-only shifted-square route followed by the independent measurable
pullback and bounded Borel spectral theorem. -/
structure SelfAdjointShiftedSquareFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    SelfAdjointShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the self-adjointness-only route to the preceding ambient-domain route. -/
def SelfAdjointShiftedSquareFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toAmbientSquareDomainFactored
    (P : SelfAdjointShiftedSquareFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    AmbientSquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toAmbientSquareDomain
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The self-adjointness-only route yields the unchanged generic spectral-resolution
constructor. -/
def SelfAdjointShiftedSquareFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : SelfAdjointShiftedSquareFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toAmbientSquareDomainFactored.toConstructor

/-- The same route specializes to the reconstructed Wightman OS boundary. -/
def SelfAdjointShiftedSquareFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : SelfAdjointShiftedSquareFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toAmbientSquareDomainFactored.toExplicitWightmanOSConstructor

/-- With the independent measurable PVM identification certificate, the route with only
shifted-square self-adjointness residual yields physical indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_selfAdjointShiftedSquareFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : SelfAdjointShiftedSquareFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_ambientSquareDomainFactoredStandardBoundedTransformBorelPipeline
      P.toAmbientSquareDomainFactored M X

/-- Adding the scalar-measure quadratic law yields the unchanged canonical
physical eigenprojection law. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_selfAdjointShiftedSquareFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : SelfAdjointShiftedSquareFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_ambientSquareDomainFactoredStandardBoundedTransformBorelPipeline
      P.toAmbientSquareDomainFactored M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

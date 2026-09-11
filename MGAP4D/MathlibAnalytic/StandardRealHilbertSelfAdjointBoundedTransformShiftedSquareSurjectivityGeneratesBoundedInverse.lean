import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformShiftedSquareRightInverseGeneratesAnalyticProperties
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- A domain-valued algebraic right inverse of the canonical positive shifted square.

Continuity in the ambient Hilbert norm is deliberately omitted.  It follows from the
already-proved coercive lower bound for `1 + A²`. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  inverseToDomain :
    H →ₗ[ℝ] (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain
  shiftedSquare_inverse :
    ∀ x : H,
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          (inverseToDomain x) = x

/-- The ambient linear map underlying a domain-valued right inverse. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData.inverseLinearMap
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A) :
    H →ₗ[ℝ] H :=
  (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain.subtype.comp
    J.inverseToDomain

@[simp]
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData.inverseLinearMap_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A)
    (x : H) :
    J.inverseLinearMap x = (J.inverseToDomain x : H) :=
  rfl

/-- Coercivity makes the algebraic domain-valued inverse pointwise contractive in the
ambient Hilbert norm. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData.inverseToDomain_norm_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    ‖(J.inverseToDomain x : H)‖ ≤ ‖x‖ := by
  have h :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_norm_lower_bound_one
      A core (J.inverseToDomain x)
  rw [J.shiftedSquare_inverse x] at h
  exact h

/-- The ambient algebraic inverse satisfies the same pointwise contraction estimate. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData.inverseLinearMap_norm_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    ‖J.inverseLinearMap x‖ ≤ ‖x‖ := by
  simpa using J.inverseToDomain_norm_le core x

/-- Coercivity upgrades the algebraic ambient inverse to a continuous linear contraction. -/
noncomputable def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData.inverse
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    H →L[ℝ] H :=
  J.inverseLinearMap.mkContinuous 1 (by
    intro x
    simpa only [one_mul] using J.inverseLinearMap_norm_le core x)

@[simp]
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData.inverse_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    J.inverse core x = (J.inverseToDomain x : H) :=
  rfl

/-- The generated continuous inverse still lands in the natural square domain. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData.inverse_mem_shiftedSquare_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    J.inverse core x ∈
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain := by
  rw [J.inverse_apply core x]
  exact (J.inverseToDomain x).property

/-- Recover the preceding bounded right-inverse boundary from only a domain-valued linear
right inverse. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData.toRightInverseData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (J : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A where
  inverse := J.inverse core
  range_mem_shiftedSquare_domain := J.inverse_mem_shiftedSquare_domain core
  shiftedSquare_inverse := fun x => by
    have hDomainEq :
        (⟨J.inverse core x, J.inverse_mem_shiftedSquare_domain core x⟩ :
          (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain) =
          J.inverseToDomain x := by
      apply Subtype.ext
      exact J.inverse_apply core x
    rw [hDomainEq]
    exact J.shiftedSquare_inverse x

/-- The final first-stage boundary: surjectivity of the canonical positive shifted square.

Injectivity is already theorem-generated from coercivity, so surjectivity alone produces a
linear equivalence, its domain-valued inverse, and hence the complete bounded inverse. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  surjective :
    Function.Surjective
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A)

/-- Surjectivity plus the coercive injectivity theorem makes `1 + A²` a linear equivalence
from its natural square domain onto the ambient Hilbert space. -/
noncomputable def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData.linearEquiv
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (S : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData A)
    (core : RealHilbertSelfAdjointCore A) :
    (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain ≃ₗ[ℝ] H :=
  LinearEquiv.ofBijective
    (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).toFun
    ⟨standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_injective A core,
      S.surjective⟩

@[simp]
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData.linearEquiv_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (S : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain) :
    S.linearEquiv core x =
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A x :=
  rfl

/-- The inverse of the shifted-square linear equivalence is the required domain-valued
linear right inverse. -/
noncomputable def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData.toDomainLinearRightInverseData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (S : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A where
  inverseToDomain := (S.linearEquiv core).symm.toLinearMap
  shiftedSquare_inverse := fun x => by
    change S.linearEquiv core ((S.linearEquiv core).symm x) = x
    exact LinearEquiv.apply_symm_apply _ x

/-- Surjectivity alone reconstructs the preceding bounded right-inverse certificate. -/
noncomputable def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData.toRightInverseData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (S : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseData A :=
  (S.toDomainLinearRightInverseData core).toRightInverseData core

/-- Uniform construction of domain-valued linear right inverses. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseData A

/-- Recover the preceding bounded right-inverse constructor. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseDataConstructor.toRightInverseDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseDataConstructor where
  construct := fun A core => (C.construct A core).toRightInverseData core

/-- Uniform construction of the sole remaining first-stage datum: surjectivity of `1 + A²`. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData A

/-- Surjectivity uniformly generates domain-valued algebraic inverses. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveDataConstructor.toDomainLinearRightInverseDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareDomainLinearRightInverseDataConstructor where
  construct := fun A core => (C.construct A core).toDomainLinearRightInverseData core

/-- Surjectivity uniformly generates the complete bounded right-inverse certificate. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveDataConstructor.toRightInverseDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareRightInverseDataConstructor :=
  C.toDomainLinearRightInverseDataConstructor.toRightInverseDataConstructor

/-- The bounded-transform construction with the entire shifted-square bounded inverse generated
from surjectivity. -/
structure SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  shiftedSquareSurjective :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveDataConstructor
  positiveSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Collapse the surjectivity-only route to the preceding bounded right-inverse route. -/
def SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toRightInverseFactored
    (P : SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  rightInverse := P.shiftedSquareSurjective.toRightInverseDataConstructor
  positiveSquareRoot := P.positiveSquareRoot
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The surjectivity-only route supplies the unchanged bounded-transform operator-data
constructor. -/
def SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toRightInverseFactored.toOperatorDataConstructor

/-- The surjectivity-generated operator construction followed by the independent spectral
pullback and bounded Borel spectral theorem. -/
structure SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the surjectivity-only route to the preceding right-inverse-factored Borel route. -/
def SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toRightInverseFactored
    (P : SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RightInverseFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toRightInverseFactored
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The surjectivity-only route yields the unchanged generic real-Hilbert spectral-resolution
constructor. -/
def SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toRightInverseFactored.toConstructor

/-- The surjectivity-only route specializes to the unchanged reconstructed Wightman OS
interface. -/
def SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toRightInverseFactored.toExplicitWightmanOSConstructor

/-- The surjectivity-only route plus actual-model measurable PVM identification yields
physical indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_surjectiveShiftedSquareStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
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
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_surjectiveShiftedSquareStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
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

import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformInverseSquareRootGeneratesShiftedSquareSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- A reduced canonical inverse-square-root boundary.

The range in the original operator domain and the contraction estimate are omitted:
they follow from the stronger range in the natural square domain, the shifted-square
square law, and bounded self-adjointness. -/
structure StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  inverseSquareRoot : H →L[ℝ] H
  selfAdjoint : IsSelfAdjoint inverseSquareRoot
  range_mem_shiftedSquare_domain :
    ∀ x : H,
      inverseSquareRoot x ∈
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain
  shiftedSquare_inverseSquareRoot_sq :
    ∀ x : H,
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          ⟨inverseSquareRoot (inverseSquareRoot x),
            range_mem_shiftedSquare_domain (inverseSquareRoot x)⟩ =
        x
  eigenvector_evaluation :
    ∀ {E : ℝ} (x : A.domain),
      A x = E • (x : H) →
        inverseSquareRoot (x : H) =
          (1 / Real.sqrt (1 + E ^ 2)) • (x : H)

/-- Membership in the natural square domain already implies membership in the original
operator domain.  Thus the canonical inverse square root needs no separate
`range_mem_original_domain` field. -/
theorem StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData.range_mem_original_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData A)
    (x : H) :
    R.inverseSquareRoot x ∈ A.domain := by
  have hxAmbient :
      R.inverseSquareRoot x ∈
        standardRealHilbertSelfAdjointAmbientSquareDomain A := by
    simpa only [standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_domain] using
      R.range_mem_shiftedSquare_domain x
  let z : standardRealHilbertSelfAdjointAmbientSquareDomain A :=
    ⟨R.inverseSquareRoot x, hxAmbient⟩
  let y : standardRealHilbertSelfAdjointSquareDomain A :=
    (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).symm z
  have hy :
      ((y : A.domain) : H) = R.inverseSquareRoot x := by
    calc
      ((y : A.domain) : H) =
          ((standardRealHilbertSelfAdjointSquareDomainEquivAmbient A y :
            standardRealHilbertSelfAdjointAmbientSquareDomain A) : H) := by
        symm
        exact standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe A y
      _ = (z : H) := by
        rw [LinearEquiv.apply_symm_apply]
      _ = R.inverseSquareRoot x := rfl
  rw [← hy]
  exact (y : A.domain).property

/-- The square law and the shifted-square lower bound control the second iterate of the
canonical inverse square root. -/
theorem StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData.inverseSquareRoot_sq_norm_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    ‖R.inverseSquareRoot (R.inverseSquareRoot x)‖ ≤ ‖x‖ := by
  have h :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_norm_lower_bound_one
      A core
      ⟨R.inverseSquareRoot (R.inverseSquareRoot x),
        R.range_mem_shiftedSquare_domain (R.inverseSquareRoot x)⟩
  rw [R.shiftedSquare_inverseSquareRoot_sq x] at h
  exact h

/-- Bounded self-adjointness turns control of `R²` into the pointwise contraction
estimate for `R`. -/
theorem StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData.inverseSquareRoot_norm_apply_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    ‖R.inverseSquareRoot x‖ ≤ ‖x‖ := by
  have hAdjoint :
      R.inverseSquareRoot.adjoint = R.inverseSquareRoot :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp R.selfAdjoint
  have hInner :
      inner ℝ (R.inverseSquareRoot x) (R.inverseSquareRoot x) =
        inner ℝ x (R.inverseSquareRoot (R.inverseSquareRoot x)) := by
    calc
      inner ℝ (R.inverseSquareRoot x) (R.inverseSquareRoot x) =
          inner ℝ x
            (R.inverseSquareRoot.adjoint (R.inverseSquareRoot x)) := by
        symm
        exact ContinuousLinearMap.adjoint_inner_right
          R.inverseSquareRoot x (R.inverseSquareRoot x)
      _ = inner ℝ x (R.inverseSquareRoot (R.inverseSquareRoot x)) := by
        rw [hAdjoint]
  have hsq :
      ‖R.inverseSquareRoot x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    calc
      ‖R.inverseSquareRoot x‖ ^ 2 =
          inner ℝ (R.inverseSquareRoot x) (R.inverseSquareRoot x) :=
        (real_inner_self_eq_norm_sq (R.inverseSquareRoot x)).symm
      _ = inner ℝ x (R.inverseSquareRoot (R.inverseSquareRoot x)) := hInner
      _ ≤ ‖x‖ * ‖R.inverseSquareRoot (R.inverseSquareRoot x)‖ :=
        real_inner_le_norm x (R.inverseSquareRoot (R.inverseSquareRoot x))
      _ ≤ ‖x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (R.inverseSquareRoot_sq_norm_le core x)
          (norm_nonneg x)
      _ = ‖x‖ ^ 2 := by ring
  nlinarith [norm_nonneg (R.inverseSquareRoot x), norm_nonneg x]

/-- The operator-norm contraction is generated from the pointwise estimate and is no
longer residual inverse-square-root data. -/
theorem StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData.inverseSquareRoot_norm_le_one
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData A)
    (core : RealHilbertSelfAdjointCore A) :
    ‖R.inverseSquareRoot‖ ≤ 1 := by
  apply R.inverseSquareRoot.opNorm_le_bound zero_le_one
  intro x
  simpa using R.inverseSquareRoot_norm_apply_le core x

/-- Reconstruct the preceding canonical inverse-square-root datum from the strictly
smaller core boundary. -/
def StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData.toCanonicalInverseSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData A where
  inverseSquareRoot := R.inverseSquareRoot
  selfAdjoint := R.selfAdjoint
  norm_le_one := R.inverseSquareRoot_norm_le_one core
  range_mem_original_domain := R.range_mem_original_domain
  range_mem_shiftedSquare_domain := R.range_mem_shiftedSquare_domain
  shiftedSquare_inverseSquareRoot_sq := R.shiftedSquare_inverseSquareRoot_sq
  eigenvector_evaluation := R.eigenvector_evaluation

/-- Uniform construction of the reduced canonical inverse-square-root boundary. -/
structure StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData A

/-- Recover the preceding canonical inverse-square-root constructor. -/
def StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreDataConstructor.toCanonicalInverseSquareRootDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalInverseSquareRootDataConstructor where
  construct := fun A core => (C.construct A core).toCanonicalInverseSquareRootData core

/-- The standard bounded-transform construction with original-domain membership and the
contraction estimate generated from the reduced inverse-square-root core. -/
structure DerivedDomainContractionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  inverseSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Forget the generated domain and contraction proofs and recover the preceding
inverse-square-root-generated route. -/
def DerivedDomainContractionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toInverseSquareRootGenerated
    (P : DerivedDomainContractionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    InverseSquareRootGeneratedStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  inverseSquareRoot :=
    P.inverseSquareRoot.toCanonicalInverseSquareRootDataConstructor
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The reduced inverse-square-root boundary supplies the unchanged bounded-transform
operator-data constructor. -/
def DerivedDomainContractionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : DerivedDomainContractionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toInverseSquareRootGenerated.toOperatorDataConstructor

/-- The reduced inverse-square-root operator construction followed by the independent
spectral pullback and bounded Borel spectral theorem. -/
structure DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    DerivedDomainContractionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the reduced route to the preceding inverse-square-root-generated route. -/
def DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toInverseSquareRootGenerated
    (P : DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toInverseSquareRootGenerated
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The reduced route yields the unchanged generic real-Hilbert spectral-resolution
constructor. -/
def DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toInverseSquareRootGenerated.toConstructor

/-- The reduced route specializes to the unchanged reconstructed Wightman OS interface. -/
def DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toInverseSquareRootGenerated.toExplicitWightmanOSConstructor

/-- The reduced route plus actual-model measurable PVM identification yields physical
indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_derivedDomainContractionFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_inverseSquareRootGeneratedFactoredStandardBoundedTransformBorelPipeline
      P.toInverseSquareRootGenerated M X

/-- Adding the scalar-measure quadratic law yields the unchanged canonical physical
eigenprojection law. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_derivedDomainContractionFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_inverseSquareRootGeneratedFactoredStandardBoundedTransformBorelPipeline
      P.toInverseSquareRootGenerated M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

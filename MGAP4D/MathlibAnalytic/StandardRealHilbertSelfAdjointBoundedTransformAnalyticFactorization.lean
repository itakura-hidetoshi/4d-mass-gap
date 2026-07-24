import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformOperatorData

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The positive shifted-square stage representing `1 + A²`.

The pinned Mathlib API does not construct this unbounded operator uniformly from an
arbitrary real-Hilbert self-adjoint `LinearPMap`. This certificate records its exact
operator-theoretic obligations, including positivity, the lower bound by one, and its
evaluation on eigenvectors of `A`. -/
structure StandardRealHilbertSelfAdjointPositiveShiftedSquareData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  positiveShiftedSquare : H →ₗ.[ℝ] H
  selfAdjoint : IsSelfAdjoint positiveShiftedSquare
  quadraticForm_nonnegative :
    ∀ x : positiveShiftedSquare.domain,
      0 ≤ ⟪positiveShiftedSquare x, (x : H)⟫_ℝ
  norm_lower_bound_one :
    ∀ x : positiveShiftedSquare.domain,
      ‖(x : H)‖ ≤ ‖positiveShiftedSquare x‖
  eigenvector_mem_domain :
    ∀ {E : ℝ} (x : A.domain),
      A x = E • (x : H) →
        (x : H) ∈ positiveShiftedSquare.domain
  eigenvector_evaluation :
    ∀ {E : ℝ} (x : A.domain) (hE : A x = E • (x : H)),
      positiveShiftedSquare
          ⟨(x : H), eigenvector_mem_domain x hE⟩ =
        (1 + E ^ 2) • (x : H)

/-- The inverse-square-root stage for the positive shifted square.

Besides the bounded self-adjoint contraction, this certificate records the range in
the original operator domain, the square-root inverse law, and scalar evaluation on
`A`-eigenvectors. -/
structure StandardRealHilbertSelfAdjointInverseSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (S : StandardRealHilbertSelfAdjointPositiveShiftedSquareData A) where
  inverseSquareRoot : H →L[ℝ] H
  selfAdjoint : IsSelfAdjoint inverseSquareRoot
  norm_le_one : ‖inverseSquareRoot‖ ≤ 1
  range_mem_original_domain :
    ∀ x : H, inverseSquareRoot x ∈ A.domain
  range_mem_shiftedSquare_domain :
    ∀ x : H, inverseSquareRoot x ∈ S.positiveShiftedSquare.domain
  shiftedSquare_inverseSquareRoot_sq :
    ∀ x : H,
      S.positiveShiftedSquare
          ⟨inverseSquareRoot (inverseSquareRoot x),
            range_mem_shiftedSquare_domain (inverseSquareRoot x)⟩ =
        x
  eigenvector_evaluation :
    ∀ {E : ℝ} (x : A.domain),
      A x = E • (x : H) →
        inverseSquareRoot (x : H) =
          (1 / Real.sqrt (1 + E ^ 2)) • (x : H)

/-- Domain-compatible composition of `A` with the inverse square root. -/
structure StandardRealHilbertSelfAdjointBoundedTransformDomainActionData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {S : StandardRealHilbertSelfAdjointPositiveShiftedSquareData A}
    (R : StandardRealHilbertSelfAdjointInverseSquareRootData S) where
  domainAction : H →ₗ[ℝ] H
  domainAction_apply :
    ∀ x : H,
      domainAction x =
        A ⟨R.inverseSquareRoot x, R.range_mem_original_domain x⟩

/-- A continuous bounded realization of the everywhere-defined domain action. -/
structure StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {S : StandardRealHilbertSelfAdjointPositiveShiftedSquareData A}
    {R : StandardRealHilbertSelfAdjointInverseSquareRootData S}
    (D : StandardRealHilbertSelfAdjointBoundedTransformDomainActionData R) where
  boundedOperator : H →L[ℝ] H
  agrees_with_domainAction :
    ∀ x : H, boundedOperator x = D.domainAction x

/-- The final analytic properties of the bounded realization.

These are kept separate from existence of the continuous extension so that closed-
graph or functional-calculus constructions can discharge the stages independently. -/
structure StandardRealHilbertSelfAdjointBoundedTransformAnalyticProperties
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {S : StandardRealHilbertSelfAdjointPositiveShiftedSquareData A}
    {R : StandardRealHilbertSelfAdjointInverseSquareRootData S}
    {D : StandardRealHilbertSelfAdjointBoundedTransformDomainActionData R}
    (B : StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionData D) where
  selfAdjoint : IsSelfAdjoint B.boundedOperator
  norm_le_one : ‖B.boundedOperator‖ ≤ 1
  eigenvector_evaluation :
    ∀ {E : ℝ} (x : A.domain),
      A x = E • (x : H) →
        B.boundedOperator (x : H) =
          standardRealHilbertBoundedTransformSpectralCoordinate E • (x : H)

/-- The complete analytic construction route for the standard bounded-transform
operator, with each unavailable Mathlib boundary exposed independently. -/
structure StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipeline
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  positiveShiftedSquare :
    StandardRealHilbertSelfAdjointPositiveShiftedSquareData A
  inverseSquareRoot :
    StandardRealHilbertSelfAdjointInverseSquareRootData positiveShiftedSquare
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionData inverseSquareRoot
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionData domainAction
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticProperties boundedExtension

/-- Collapse the analytic construction stages to the operator-data boundary isolated
by the preceding PR. -/
def StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipeline.toOperatorData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (P : StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipeline A) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorData A where
  boundedOperator := P.boundedExtension.boundedOperator
  boundedSelfAdjoint := P.analyticProperties.selfAdjoint
  boundedOperator_norm_le_one := P.analyticProperties.norm_le_one
  eigenvector_forward := P.analyticProperties.eigenvector_evaluation

/-- Uniform construction of `1 + A²` from the self-adjoint core. -/
structure StandardRealHilbertSelfAdjointPositiveShiftedSquareDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointPositiveShiftedSquareData A

/-- Uniform inverse-square-root construction for every supplied shifted square. -/
structure StandardRealHilbertSelfAdjointInverseSquareRootDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (_core : RealHilbertSelfAdjointCore A)
      (S : StandardRealHilbertSelfAdjointPositiveShiftedSquareData A),
      StandardRealHilbertSelfAdjointInverseSquareRootData S

/-- Uniform domain-compatible composition stage. -/
structure StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (_core : RealHilbertSelfAdjointCore A)
      (S : StandardRealHilbertSelfAdjointPositiveShiftedSquareData A)
      (R : StandardRealHilbertSelfAdjointInverseSquareRootData S),
      StandardRealHilbertSelfAdjointBoundedTransformDomainActionData R

/-- Uniform bounded-extension stage. -/
structure StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (_core : RealHilbertSelfAdjointCore A)
      (S : StandardRealHilbertSelfAdjointPositiveShiftedSquareData A)
      (R : StandardRealHilbertSelfAdjointInverseSquareRootData S)
      (D : StandardRealHilbertSelfAdjointBoundedTransformDomainActionData R),
      StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionData D

/-- Uniform proof of self-adjointness, contraction, and eigenvector evaluation for the
bounded extension. -/
structure StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (_core : RealHilbertSelfAdjointCore A)
      (S : StandardRealHilbertSelfAdjointPositiveShiftedSquareData A)
      (R : StandardRealHilbertSelfAdjointInverseSquareRootData S)
      (D : StandardRealHilbertSelfAdjointBoundedTransformDomainActionData R)
      (B : StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionData D),
      StandardRealHilbertSelfAdjointBoundedTransformAnalyticProperties B

/-- The five independent analytic constructors for the standard bounded operator. -/
structure StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  positiveShiftedSquare :
    StandardRealHilbertSelfAdjointPositiveShiftedSquareDataConstructor
  inverseSquareRoot :
    StandardRealHilbertSelfAdjointInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- The five analytic constructors produce the operator-data constructor required by
the factored bounded-transform route. -/
def StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor where
  construct := fun A core =>
    let S := P.positiveShiftedSquare.construct A core
    let R := P.inverseSquareRoot.construct A core S
    let D := P.domainAction.construct A core S R
    let B := P.boundedExtension.construct A core S R D
    let Q := P.analyticProperties.construct A core S R D B
    ({ positiveShiftedSquare := S
       inverseSquareRoot := R
       domainAction := D
       boundedExtension := B
       analyticProperties := Q } :
      StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipeline A).toOperatorData

/-- The analytic stages are sufficient for the previously isolated operator-data
constructor. -/
theorem standard_real_hilbert_selfAdjoint_boundedTransform_operatorData_constructor_nonempty_of_analyticFactorization
    (S : StandardRealHilbertSelfAdjointPositiveShiftedSquareDataConstructor)
    (R : StandardRealHilbertSelfAdjointInverseSquareRootDataConstructor)
    (D : StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor)
    (B : StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor)
    (Q : StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor) :
    Nonempty StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor := by
  exact ⟨
    StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
      .toOperatorDataConstructor
      ({ positiveShiftedSquare := S
         inverseSquareRoot := R
         domainAction := D
         boundedExtension := B
         analyticProperties := Q } :
        StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor)⟩

/-- The fully analytic factorization followed by measurable pullback and bounded
Borel resolution. -/
structure AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the analytic factorization to the previously established factored
standard pipeline. -/
def AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toFactored
    (P : AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransformOperator := P.operatorConstruction.toOperatorDataConstructor
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The analytically factored route yields the unchanged global spectral-resolution
constructor. -/
def AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toConstructor

/-- The same route specializes to the reconstructed Wightman OS boundary. -/
def AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toExplicitWightmanOSConstructor

/-- With the independent actual-model measurable PVM identification certificate, the
analytic factorization yields ambient indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_analyticallyFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_standardBoundedTransformBorelPipeline
      P.toFactored.toStandard M X

/-- Adding the scalar-measure quadratic law yields the canonical eigenprojection law
without changing the actual physical-model assumptions. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_analyticallyFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_standardBoundedTransformBorelPipeline
      P.toFactored.toStandard M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

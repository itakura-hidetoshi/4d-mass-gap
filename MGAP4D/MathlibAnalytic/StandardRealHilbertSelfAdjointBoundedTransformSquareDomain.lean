import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformAnalyticFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The natural domain of `A²`, represented as a submodule of `A.domain`:
those vectors `x` for which `A x` again belongs to `A.domain`. -/
def standardRealHilbertSelfAdjointSquareDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) : Submodule ℝ A.domain :=
  A.domain.comap A.toFun

@[simp] theorem mem_standardRealHilbertSelfAdjointSquareDomain_iff
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) (x : A.domain) :
    x ∈ standardRealHilbertSelfAdjointSquareDomain A ↔ A x ∈ A.domain := by
  rfl

/-- On the square domain, the first application of `A` canonically lands back in
`A.domain`. -/
def standardRealHilbertSelfAdjointSquareToDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) :
    standardRealHilbertSelfAdjointSquareDomain A →ₗ[ℝ] A.domain :=
  (A.toFun.domRestrict (standardRealHilbertSelfAdjointSquareDomain A)).codRestrict
    A.domain fun x => x.property

@[simp] theorem standardRealHilbertSelfAdjointSquareToDomain_coe
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H)
    (x : standardRealHilbertSelfAdjointSquareDomain A) :
    ((standardRealHilbertSelfAdjointSquareToDomain A x : A.domain) : H) =
      A (x : A.domain) := by
  rfl

/-- The canonical algebraic square action `x ↦ A (A x)` on the natural square
domain. -/
def standardRealHilbertSelfAdjointSquareAction
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) :
    standardRealHilbertSelfAdjointSquareDomain A →ₗ[ℝ] H :=
  A.toFun.comp (standardRealHilbertSelfAdjointSquareToDomain A)

@[simp] theorem standardRealHilbertSelfAdjointSquareAction_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H)
    (x : standardRealHilbertSelfAdjointSquareDomain A) :
    standardRealHilbertSelfAdjointSquareAction A x =
      A (standardRealHilbertSelfAdjointSquareToDomain A x) := by
  rfl

/-- The canonical algebraic shifted-square action `x ↦ x + A²x` on the natural
square domain. -/
def standardRealHilbertSelfAdjointShiftedSquareAction
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) :
    standardRealHilbertSelfAdjointSquareDomain A →ₗ[ℝ] H :=
  (A.domain.subtype.comp
      (standardRealHilbertSelfAdjointSquareDomain A).subtype) +
    standardRealHilbertSelfAdjointSquareAction A

@[simp] theorem standardRealHilbertSelfAdjointShiftedSquareAction_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H)
    (x : standardRealHilbertSelfAdjointSquareDomain A) :
    standardRealHilbertSelfAdjointShiftedSquareAction A x =
      (x : A.domain) + standardRealHilbertSelfAdjointSquareAction A x := by
  rfl

/-- Every eigenvector in `A.domain` automatically belongs to the natural square
domain. -/
theorem standardRealHilbertSelfAdjoint_eigenvector_mem_squareDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) {E : ℝ} (x : A.domain)
    (hE : A x = E • (x : H)) :
    x ∈ standardRealHilbertSelfAdjointSquareDomain A := by
  change A x ∈ A.domain
  rw [hE]
  exact A.domain.smul_mem E x.property

/-- The canonical square action evaluates to `E²` on an `E`-eigenvector. -/
theorem standardRealHilbertSelfAdjointSquareAction_eigenvector_evaluation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) {E : ℝ} (x : A.domain)
    (hE : A x = E • (x : H)) :
    standardRealHilbertSelfAdjointSquareAction A
        ⟨x, standardRealHilbertSelfAdjoint_eigenvector_mem_squareDomain A x hE⟩ =
      E ^ 2 • (x : H) := by
  have hToDomain :
      standardRealHilbertSelfAdjointSquareToDomain A
          ⟨x, standardRealHilbertSelfAdjoint_eigenvector_mem_squareDomain A x hE⟩ =
        E • x := by
    apply Subtype.ext
    exact hE
  rw [standardRealHilbertSelfAdjointSquareAction_apply, hToDomain,
    A.map_smul, hE]
  simp [pow_two, smul_smul]

/-- The shifted-square action evaluates to `1 + E²` on an `E`-eigenvector. -/
theorem standardRealHilbertSelfAdjointShiftedSquareAction_eigenvector_evaluation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) {E : ℝ} (x : A.domain)
    (hE : A x = E • (x : H)) :
    standardRealHilbertSelfAdjointShiftedSquareAction A
        ⟨x, standardRealHilbertSelfAdjoint_eigenvector_mem_squareDomain A x hE⟩ =
      (1 + E ^ 2) • (x : H) := by
  rw [standardRealHilbertSelfAdjointShiftedSquareAction_apply,
    standardRealHilbertSelfAdjointSquareAction_eigenvector_evaluation A x hE]
  simp [add_smul]

/-- The exact residual needed to realize the canonical algebraic shifted-square action
as an unbounded `LinearPMap` on the ambient Hilbert space.

The square domain and its action are already constructed above. This certificate only
supplies an ambient-domain lift together with self-adjointness, nonnegativity, and the
lower bound required by the inverse-square-root stage. -/
structure StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  positiveShiftedSquare : H →ₗ.[ℝ] H
  squareDomainLift :
    standardRealHilbertSelfAdjointSquareDomain A →ₗ[ℝ]
      positiveShiftedSquare.domain
  squareDomainLift_coe :
    ∀ x : standardRealHilbertSelfAdjointSquareDomain A,
      ((squareDomainLift x : positiveShiftedSquare.domain) : H) =
        ((x : A.domain) : H)
  agrees_with_shiftedSquareAction :
    ∀ x : standardRealHilbertSelfAdjointSquareDomain A,
      positiveShiftedSquare (squareDomainLift x) =
        standardRealHilbertSelfAdjointShiftedSquareAction A x
  selfAdjoint : IsSelfAdjoint positiveShiftedSquare
  quadraticForm_nonnegative :
    ∀ x : positiveShiftedSquare.domain,
      0 ≤ ⟪positiveShiftedSquare x, (x : H)⟫_ℝ
  norm_lower_bound_one :
    ∀ x : positiveShiftedSquare.domain,
      ‖(x : H)‖ ≤ ‖positiveShiftedSquare x‖

/-- An eigenvector belongs to the ambient shifted-square domain supplied by an
extension certificate. -/
theorem StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionData.eigenvector_mem_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (X : StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionData A)
    {E : ℝ} (x : A.domain) (hE : A x = E • (x : H)) :
    (x : H) ∈ X.positiveShiftedSquare.domain := by
  let y : standardRealHilbertSelfAdjointSquareDomain A :=
    ⟨x, standardRealHilbertSelfAdjoint_eigenvector_mem_squareDomain A x hE⟩
  have hmem := (X.squareDomainLift y).property
  rw [X.squareDomainLift_coe y] at hmem
  exact hmem

/-- The ambient shifted-square realization inherits the already-proved `1 + E²`
eigenvector evaluation. -/
theorem StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionData.eigenvector_evaluation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (X : StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionData A)
    {E : ℝ} (x : A.domain) (hE : A x = E • (x : H)) :
    X.positiveShiftedSquare
        ⟨(x : H), X.eigenvector_mem_domain x hE⟩ =
      (1 + E ^ 2) • (x : H) := by
  let y : standardRealHilbertSelfAdjointSquareDomain A :=
    ⟨x, standardRealHilbertSelfAdjoint_eigenvector_mem_squareDomain A x hE⟩
  have harg :
      (⟨(x : H), X.eigenvector_mem_domain x hE⟩ :
        X.positiveShiftedSquare.domain) = X.squareDomainLift y := by
    apply Subtype.ext
    exact (X.squareDomainLift_coe y).symm
  rw [harg, X.agrees_with_shiftedSquareAction y]
  exact standardRealHilbertSelfAdjointShiftedSquareAction_eigenvector_evaluation A x hE

/-- Collapse the exact square-domain extension boundary to the shifted-square data
required by the analytic bounded-transform pipeline. -/
def StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionData.toPositiveShiftedSquareData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (X : StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionData A) :
    StandardRealHilbertSelfAdjointPositiveShiftedSquareData A where
  positiveShiftedSquare := X.positiveShiftedSquare
  selfAdjoint := X.selfAdjoint
  quadraticForm_nonnegative := X.quadraticForm_nonnegative
  norm_lower_bound_one := X.norm_lower_bound_one
  eigenvector_mem_domain := X.eigenvector_mem_domain
  eigenvector_evaluation := X.eigenvector_evaluation

/-- Uniform construction of the exact ambient extension boundary. -/
structure StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionData A

/-- The extension constructor supplies the shifted-square constructor used by the
five-stage analytic factorization. -/
def StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionDataConstructor.toPositiveShiftedSquareDataConstructor
    (C : StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionDataConstructor) :
    StandardRealHilbertSelfAdjointPositiveShiftedSquareDataConstructor where
  construct := fun A core => (C.construct A core).toPositiveShiftedSquareData

/-- The standard bounded-transform operator construction with its first stage refined
to the explicit square-domain extension boundary. -/
structure SquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  positiveShiftedSquareExtension :
    StandardRealHilbertSelfAdjointPositiveShiftedSquareExtensionDataConstructor
  inverseSquareRoot :
    StandardRealHilbertSelfAdjointInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Forget the explicit square-domain refinement and recover the existing five-stage
analytic constructor. -/
def SquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toAnalytic
    (P : SquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  positiveShiftedSquare :=
    P.positiveShiftedSquareExtension.toPositiveShiftedSquareDataConstructor
  inverseSquareRoot := P.inverseSquareRoot
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The square-domain-refined construction supplies the previously isolated standard
bounded-transform operator-data constructor. -/
def SquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : SquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toAnalytic.toOperatorDataConstructor

/-- The square-domain-refined operator construction followed by the independent
measurable pullback and bounded Borel spectral theorem. -/
structure SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    SquareDomainStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the square-domain route to the existing analytically factored pipeline. -/
def SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toAnalyticallyFactored
    (P : SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    AnalyticallyFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toAnalytic
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The square-domain-refined route yields the unchanged generic spectral-resolution
constructor. -/
def SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toAnalyticallyFactored.toConstructor

/-- The same route specializes to the reconstructed Wightman OS boundary. -/
def SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toAnalyticallyFactored.toExplicitWightmanOSConstructor

/-- With the independent measurable PVM identification certificate, the square-domain
route yields ambient indicator evaluation in the actual physical model. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_squareDomainFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_analyticallyFactoredStandardBoundedTransformBorelPipeline
      P.toAnalyticallyFactored M X

/-- Adding the scalar-measure quadratic law yields the canonical eigenprojection law
without changing the actual physical-model assumptions. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_squareDomainFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : SquareDomainFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_analyticallyFactoredStandardBoundedTransformBorelPipeline
      P.toAnalyticallyFactored M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

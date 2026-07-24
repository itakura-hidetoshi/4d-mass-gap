import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformShiftedSquareSurjectivityGeneratesBoundedInverse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- Weak graph-form solutions for the canonical shifted-square equation.

For each ambient right-hand side `x`, the supplied vector `u ∈ D(A)` satisfies

`⟪u,v⟫ + ⟪Au,Av⟫ = ⟪x,v⟫`

for every `v ∈ D(A)`.  Membership in `D(A²)` and the strong equation
`(1 + A²)u = x` are deliberately omitted: they follow from self-adjointness. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  solve : H → A.domain
  variational_identity :
    ∀ (x : H) (v : A.domain),
      inner ℝ (solve x : H) (v : H) + inner ℝ (A (solve x)) (A v) =
        inner ℝ x (v : H)

/-- The weak graph-form equation implies that `A u` belongs to the adjoint domain. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData.solve_image_mem_adjoint_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (V : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData A)
    (x : H) :
    A (V.solve x) ∈ A.adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists
  refine ⟨x - (V.solve x : H), ?_⟩
  intro v
  have hV := V.variational_identity x v
  rw [inner_sub_left]
  linarith

/-- Self-adjointness upgrades the weak solution to the natural square domain. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData.solve_image_mem_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (V : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    A (V.solve x) ∈ A.domain := by
  have hAdjointEq : A.adjoint = A :=
    LinearPMap.isSelfAdjoint_def.mp core.selfAdjoint
  rw [← hAdjointEq]
  exact V.solve_image_mem_adjoint_domain x

/-- The weak variational identity becomes the strong second-order equation
`A²u = x - u`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData.strong_square_equation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (V : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    A (⟨A (V.solve x), V.solve_image_mem_domain core x⟩ : A.domain) =
      x - (V.solve x : H) := by
  apply core.denseDomain.eq_of_inner_left ℝ
  intro v hv
  let vDomain : A.domain := ⟨v, hv⟩
  have hFormal : A.IsFormalAdjoint A :=
    realHilbertSelfAdjointCore_isFormalSelfAdjoint core
  calc
    inner ℝ
        (A (⟨A (V.solve x), V.solve_image_mem_domain core x⟩ : A.domain)) v =
      inner ℝ (A (V.solve x)) (A vDomain) := by
        exact hFormal
          (⟨A (V.solve x), V.solve_image_mem_domain core x⟩ : A.domain)
          vDomain
    _ = inner ℝ (x - (V.solve x : H)) v := by
      have hV := V.variational_identity x vDomain
      rw [inner_sub_left]
      linarith

/-- A weak graph-form solution is an exact preimage under the canonical ambient `1 + A²`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData.shiftedSquare_preimage
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (V : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    ∃ u : (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain,
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A u = x := by
  let uSquare : standardRealHilbertSelfAdjointSquareDomain A :=
    ⟨V.solve x, V.solve_image_mem_domain core x⟩
  let uAmbient :
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain :=
    standardRealHilbertSelfAdjointSquareDomainEquivAmbient A uSquare
  refine ⟨uAmbient, ?_⟩
  change
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
        (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A uSquare) = x
  rw [standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply,
    standardRealHilbertSelfAdjointShiftedSquareAction_apply,
    standardRealHilbertSelfAdjointSquareAction_apply]
  have hToDomain :
      standardRealHilbertSelfAdjointSquareToDomain A uSquare =
        (⟨A (V.solve x), V.solve_image_mem_domain core x⟩ : A.domain) := by
    apply Subtype.ext
    rfl
  rw [hToDomain, V.strong_square_equation core x]
  change (V.solve x : H) + (x - (V.solve x : H)) = x
  abel

/-- Weak graph-form solvability for every right-hand side generates surjectivity of `1 + A²`. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData.toSurjectiveData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (V : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveData A where
  surjective := fun x => V.shiftedSquare_preimage core x

/-- Uniform construction of weak graph-form solutions. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData A

/-- Weak graph-form solution constructors generate the preceding surjectivity-only boundary. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionDataConstructor.toSurjectiveDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveDataConstructor where
  construct := fun A core => (C.construct A core).toSurjectiveData core

/-- The bounded-transform construction with shifted-square surjectivity generated from
weak graph-form solvability. -/
structure VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  variationalSolution :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionDataConstructor
  positiveSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Collapse the variational route to the preceding surjectivity-only route. -/
def VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toSurjectiveShiftedSquare
    (P : VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  shiftedSquareSurjective := P.variationalSolution.toSurjectiveDataConstructor
  positiveSquareRoot := P.positiveSquareRoot
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The variational route supplies the unchanged bounded-transform operator-data constructor. -/
def VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toSurjectiveShiftedSquare.toOperatorDataConstructor

/-- The variational operator construction followed by the independent spectral pullback and
bounded Borel spectral theorem. -/
structure VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the variational route to the preceding surjectivity-only Borel route. -/
def VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toSurjectiveShiftedSquare
    (P : VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    SurjectiveShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toSurjectiveShiftedSquare
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The variational route yields the unchanged generic real-Hilbert spectral-resolution
constructor. -/
def VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toSurjectiveShiftedSquare.toConstructor

/-- The variational route specializes to the unchanged reconstructed Wightman OS interface. -/
def VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toSurjectiveShiftedSquare.toExplicitWightmanOSConstructor

/-- The variational route plus actual-model measurable PVM identification yields physical
indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_variationalShiftedSquareStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_surjectiveShiftedSquareStandardBoundedTransformBorelPipeline
      P.toSurjectiveShiftedSquare M X

/-- Adding the scalar-measure quadratic law yields the unchanged canonical physical
eigenprojection law. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_variationalShiftedSquareStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : VariationalShiftedSquareStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_surjectiveShiftedSquareStandardBoundedTransformBorelPipeline
      P.toSurjectiveShiftedSquare M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

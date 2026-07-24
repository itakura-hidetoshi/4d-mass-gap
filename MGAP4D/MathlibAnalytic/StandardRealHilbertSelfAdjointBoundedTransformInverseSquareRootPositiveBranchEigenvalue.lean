import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformInverseSquareRootDerivedDomainContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The canonical positive shifted square is injective on its natural ambient domain.
The already-proved lower bound by one is sufficient; no self-adjointness argument is
needed here. -/
theorem standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_injective
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A) :
    Function.Injective
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A) := by
  intro x y hxy
  apply Subtype.ext
  let z : (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain := x - y
  have hzImage :
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A z = 0 := by
    dsimp [z]
    change
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).toFun (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hzNorm :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_norm_lower_bound_one
      A core z
  rw [hzImage, norm_zero] at hzNorm
  have hzNormZero : ‖(z : H)‖ = 0 :=
    le_antisymm hzNorm (norm_nonneg _)
  have hzZero : (z : H) = 0 := norm_eq_zero.mp hzNormZero
  dsimp [z] at hzZero
  exact sub_eq_zero.mp hzZero

/-- The strictly smaller positive-branch inverse-square-root boundary.

The eigenvector formula is omitted.  It follows from uniqueness of the shifted-square
preimage, the square law, and nonnegativity of the bounded quadratic form, which selects
the positive square-root branch. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  inverseSquareRoot : H →L[ℝ] H
  selfAdjoint : IsSelfAdjoint inverseSquareRoot
  quadraticForm_nonnegative :
    ∀ x : H, 0 ≤ inner ℝ (inverseSquareRoot x) x
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

/-- On an `E`-eigenvector of `A`, the square of the positive inverse square root has
scalar value `(1 + E²)⁻¹`.  This is forced by injectivity of the canonical shifted
square and its known `1 + E²` eigenvector action. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootData.inverseSquareRoot_sq_eigenvector_evaluation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootData A)
    (core : RealHilbertSelfAdjointCore A)
    {E : ℝ} (x : A.domain)
    (hE : A x = E • (x : H)) :
    R.inverseSquareRoot (R.inverseSquareRoot (x : H)) =
      (1 / (1 + E ^ 2)) • (x : H) := by
  let lambda : ℝ := 1 + E ^ 2
  have hlambdaPos : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hlambdaNe : lambda ≠ 0 := ne_of_gt hlambdaPos
  let xSquare : standardRealHilbertSelfAdjointSquareDomain A :=
    ⟨x, standardRealHilbertSelfAdjoint_eigenvector_mem_squareDomain A x hE⟩
  let xAmbient : standardRealHilbertSelfAdjointAmbientSquareDomain A :=
    standardRealHilbertSelfAdjointSquareDomainEquivAmbient A xSquare
  have hxAmbientCoe : (xAmbient : H) = (x : H) := by
    dsimp [xAmbient]
    exact standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe A xSquare
  have hShiftedSquareX :
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A xAmbient =
        lambda • (x : H) := by
    dsimp [xAmbient, lambda]
    rw [standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply]
    exact
      standardRealHilbertSelfAdjointShiftedSquareAction_eigenvector_evaluation
        A x hE
  let candidate :
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain :=
    (1 / lambda) • xAmbient
  have hShiftedSquareCandidate :
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A candidate =
        (x : H) := by
    dsimp [candidate]
    change
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).toFun
          ((1 / lambda) • xAmbient) =
        (x : H)
    rw [map_smul, hShiftedSquareX]
    simp [smul_smul, hlambdaNe]
  let iterated :
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain :=
    ⟨R.inverseSquareRoot (R.inverseSquareRoot (x : H)),
      R.range_mem_shiftedSquare_domain (R.inverseSquareRoot (x : H))⟩
  have hShiftedSquareIterated :
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A iterated =
        (x : H) := by
    exact R.shiftedSquare_inverseSquareRoot_sq (x : H)
  have hIteratedEq : iterated = candidate :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_injective A core
      (hShiftedSquareIterated.trans hShiftedSquareCandidate.symm)
  have hCoe := congrArg
    (fun z : (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain =>
      (z : H)) hIteratedEq
  change
    R.inverseSquareRoot (R.inverseSquareRoot (x : H)) =
      (1 / lambda) • (xAmbient : H) at hCoe
  rw [hxAmbientCoe] at hCoe
  simpa [lambda] using hCoe

/-- Quadratic-form nonnegativity selects the positive root of the scalar square law.
Thus the standard inverse-square-root eigenvector formula is theorem-generated rather
than independent residual data. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootData.eigenvector_evaluation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootData A)
    (core : RealHilbertSelfAdjointCore A)
    {E : ℝ} (x : A.domain)
    (hE : A x = E • (x : H)) :
    R.inverseSquareRoot (x : H) =
      (1 / Real.sqrt (1 + E ^ 2)) • (x : H) := by
  let lambda : ℝ := 1 + E ^ 2
  let s : ℝ := 1 / Real.sqrt lambda
  have hlambdaPos : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hsPos : 0 < s := by
    dsimp [s]
    positivity
  have hsSq : s ^ 2 = 1 / lambda := by
    dsimp [s]
    rw [div_pow, one_pow, Real.sq_sqrt hlambdaPos.le]
  have hR2 :
      R.inverseSquareRoot (R.inverseSquareRoot (x : H)) =
        (1 / lambda) • (x : H) := by
    simpa [lambda] using
      R.inverseSquareRoot_sq_eigenvector_evaluation core x hE
  let y : H := R.inverseSquareRoot (x : H) - s • (x : H)
  have hPlus : R.inverseSquareRoot y + s • y = 0 := by
    dsimp [y]
    rw [map_sub, map_smul, hR2]
    simp only [smul_sub, smul_smul]
    rw [← pow_two s, hsSq]
    abel
  have hRy : R.inverseSquareRoot y = -(s • y) :=
    eq_neg_of_add_eq_zero_left hPlus
  have hPositive := R.quadraticForm_nonnegative y
  rw [hRy] at hPositive
  simp [real_inner_self_eq_norm_sq] at hPositive
  have hyNorm : ‖y‖ = 0 := by
    nlinarith [sq_nonneg ‖y‖, norm_nonneg y]
  have hy : y = 0 := norm_eq_zero.mp hyNorm
  dsimp [y] at hy
  have hResult : R.inverseSquareRoot (x : H) = s • (x : H) :=
    sub_eq_zero.mp hy
  simpa [s, lambda] using hResult

/-- Recover the preceding inverse-square-root core data with its eigenvector formula now
proved from the positive-branch boundary. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootData.toCoreData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreData A where
  inverseSquareRoot := R.inverseSquareRoot
  selfAdjoint := R.selfAdjoint
  range_mem_shiftedSquare_domain := R.range_mem_shiftedSquare_domain
  shiftedSquare_inverseSquareRoot_sq := R.shiftedSquare_inverseSquareRoot_sq
  eigenvector_evaluation := R.eigenvector_evaluation core

/-- Uniform construction of the positive-branch canonical inverse square root. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootData A

/-- Recover the preceding reduced-core constructor. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootDataConstructor.toCoreDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalInverseSquareRootCoreDataConstructor where
  construct := fun A core => (C.construct A core).toCoreData core

/-- The standard bounded-transform construction with the inverse-square-root eigenvector
formula generated from positivity. -/
structure PositiveBranchStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  inverseSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalPositiveInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Collapse the positive-branch route to the preceding derived-domain-contraction route. -/
def PositiveBranchStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toDerivedDomainContraction
    (P : PositiveBranchStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    DerivedDomainContractionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  inverseSquareRoot := P.inverseSquareRoot.toCoreDataConstructor
  domainAction := P.domainAction
  boundedExtension := P.boundedExtension
  analyticProperties := P.analyticProperties

/-- The positive-branch boundary supplies the unchanged bounded-transform operator-data
constructor. -/
def PositiveBranchStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : PositiveBranchStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toDerivedDomainContraction.toOperatorDataConstructor

/-- The positive-branch operator construction followed by the independent spectral
pullback and bounded Borel spectral theorem. -/
structure PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    PositiveBranchStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the positive-branch route to the preceding factored route. -/
def PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toDerivedDomainContraction
    (P : PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    DerivedDomainContractionFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction := P.operatorConstruction.toDerivedDomainContraction
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The positive-branch route yields the unchanged generic real-Hilbert spectral-resolution
constructor. -/
def PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toDerivedDomainContraction.toConstructor

/-- The positive-branch route specializes to the unchanged reconstructed Wightman OS
interface. -/
def PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toDerivedDomainContraction.toExplicitWightmanOSConstructor

/-- The positive-branch route plus actual-model measurable PVM identification yields
physical indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_positiveBranchFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_derivedDomainContractionFactoredStandardBoundedTransformBorelPipeline
      P.toDerivedDomainContraction M X

/-- Adding the scalar-measure quadratic law yields the unchanged canonical physical
eigenprojection law. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_positiveBranchFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : PositiveBranchFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_derivedDomainContractionFactoredStandardBoundedTransformBorelPipeline
      P.toDerivedDomainContraction M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

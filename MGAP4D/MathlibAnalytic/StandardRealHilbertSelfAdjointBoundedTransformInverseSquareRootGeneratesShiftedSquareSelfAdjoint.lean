import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformShiftedSquareQuadraticForm
import Mathlib.Tactic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A densely defined symmetric partially defined operator is self-adjoint once the
operator itself is surjective.  This is the zero-shift analogue of the existing
`oneShift` maximal-symmetry criterion. -/
theorem isSelfAdjoint_of_isFormalAdjoint_of_surjective
    (A : E →ₗ.[ℝ] E)
    (hDense : Dense (A.domain : Set E))
    (hSymmetric : A.IsFormalAdjoint A)
    (hSurjective : Function.Surjective A) :
    IsSelfAdjoint A := by
  have hA_le_adjoint : A ≤ A.adjoint :=
    hSymmetric.le_adjoint hDense
  have hAdjoint_le_A : A.adjoint ≤ A := by
    refine ⟨?_, ?_⟩
    · intro x hx
      let xAdjoint : A.adjoint.domain := ⟨x, hx⟩
      obtain ⟨u, hu⟩ := hSurjective (A.adjoint xAdjoint)
      let w : E := x - (u : E)
      have horthogonal (v : A.domain) :
          inner ℝ (A v) w = 0 := by
        have hAdjointPairing :
            inner ℝ (A v) x =
              inner ℝ (v : E) (A.adjoint xAdjoint) := by
          calc
            inner ℝ (A v) x = inner ℝ x (A v) :=
              real_inner_comm _ _
            _ = inner ℝ (A.adjoint xAdjoint) (v : E) := by
              symm
              exact (LinearPMap.adjoint_isFormalAdjoint hDense) xAdjoint v
            _ = inner ℝ (v : E) (A.adjoint xAdjoint) :=
              real_inner_comm _ _
        have hSymmetricPairing :
            inner ℝ (A v) (u : E) =
              inner ℝ (v : E) (A u) :=
          hSymmetric v u
        calc
          inner ℝ (A v) w =
              inner ℝ (A v) x - inner ℝ (A v) (u : E) := by
            simp only [w, inner_sub_right]
          _ = inner ℝ (v : E) (A.adjoint xAdjoint) -
                inner ℝ (v : E) (A u) := by
            rw [hAdjointPairing, hSymmetricPairing]
          _ = inner ℝ (v : E) (A.adjoint xAdjoint - A u) := by
            rw [inner_sub_right]
          _ = 0 := by
            rw [← hu, sub_self, inner_zero_right]
      have hself : inner ℝ w w = 0 := by
        obtain ⟨v, hv⟩ := hSurjective w
        have hvOrthogonal := horthogonal v
        rw [hv] at hvOrthogonal
        exact hvOrthogonal
      have hnormSq : ‖w‖ ^ 2 = 0 := by
        simpa only [real_inner_self_eq_norm_sq] using hself
      have hnorm : ‖w‖ = 0 := by
        nlinarith [norm_nonneg w]
      have hw : x = (u : E) := by
        apply sub_eq_zero.mp
        exact norm_eq_zero.mp hnorm
      exact hw.symm ▸ u.property
    · intro x y hxy
      exact (hA_le_adjoint.2 hxy.symm).symm
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hAdjoint_le_A hA_le_adjoint

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

/-- The canonical ambient `1 + A²` operator is formally self-adjoint on its natural
square domain. -/
theorem standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_isFormalAdjoint
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A) :
    (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).IsFormalAdjoint
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A) := by
  have hFormal : A.IsFormalAdjoint A :=
    realHilbertSelfAdjointCore_isFormalSelfAdjoint core
  intro x y
  let x₀ : standardRealHilbertSelfAdjointSquareDomain A :=
    (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).symm x
  let y₀ : standardRealHilbertSelfAdjointSquareDomain A :=
    (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).symm y
  have hx :
      standardRealHilbertSelfAdjointSquareDomainEquivAmbient A x₀ = x :=
    LinearEquiv.apply_symm_apply
      (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A) x
  have hy :
      standardRealHilbertSelfAdjointSquareDomainEquivAmbient A y₀ = y :=
    LinearEquiv.apply_symm_apply
      (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A) y
  have hSquare :
      inner ℝ
          (standardRealHilbertSelfAdjointSquareAction A x₀)
          ((y₀ : A.domain) : H) =
        inner ℝ
          ((x₀ : A.domain) : H)
          (standardRealHilbertSelfAdjointSquareAction A y₀) := by
    rw [standardRealHilbertSelfAdjointSquareAction_apply,
      standardRealHilbertSelfAdjointSquareAction_apply]
    calc
      inner ℝ
          (A (standardRealHilbertSelfAdjointSquareToDomain A x₀))
          ((y₀ : A.domain) : H) =
          inner ℝ
            ((standardRealHilbertSelfAdjointSquareToDomain A x₀ : A.domain) : H)
            (A (y₀ : A.domain)) :=
        hFormal (standardRealHilbertSelfAdjointSquareToDomain A x₀) (y₀ : A.domain)
      _ = inner ℝ (A (x₀ : A.domain)) (A (y₀ : A.domain)) := by
        rw [standardRealHilbertSelfAdjointSquareToDomain_coe]
      _ = inner ℝ
          ((x₀ : A.domain) : H)
          (A (standardRealHilbertSelfAdjointSquareToDomain A y₀)) := by
        rw [← standardRealHilbertSelfAdjointSquareToDomain_coe A y₀]
        exact hFormal (x₀ : A.domain)
          (standardRealHilbertSelfAdjointSquareToDomain A y₀)
  rw [← hx, ← hy,
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply,
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply,
    standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe,
    standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe,
    standardRealHilbertSelfAdjointShiftedSquareAction_apply,
    standardRealHilbertSelfAdjointShiftedSquareAction_apply,
    inner_add_left, inner_add_right, hSquare]

/-- Inverse-square-root data stated directly for the canonical ambient `1 + A²`
operator, without assuming that shifted square is already self-adjoint.

The square law is strong enough to generate surjectivity of `1 + A²`; bounded
self-adjointness and the same law generate dense range of the inverse square root and
therefore density of the natural square domain. -/
structure StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  inverseSquareRoot : H →L[ℝ] H
  selfAdjoint : IsSelfAdjoint inverseSquareRoot
  norm_le_one : ‖inverseSquareRoot‖ ≤ 1
  range_mem_original_domain :
    ∀ x : H, inverseSquareRoot x ∈ A.domain
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

/-- The canonical inverse square root is injective because applying the shifted square
to its iterated value recovers the original vector. -/
theorem StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData.inverseSquareRoot_injective
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData A) :
    Function.Injective R.inverseSquareRoot := by
  intro x y hxy
  calc
    x = standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
        ⟨R.inverseSquareRoot (R.inverseSquareRoot x),
          R.range_mem_shiftedSquare_domain (R.inverseSquareRoot x)⟩ :=
      (R.shiftedSquare_inverseSquareRoot_sq x).symm
    _ = standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
        ⟨R.inverseSquareRoot (R.inverseSquareRoot y),
          R.range_mem_shiftedSquare_domain (R.inverseSquareRoot y)⟩ := by
      apply congrArg
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A)
      apply Subtype.ext
      exact congrArg R.inverseSquareRoot hxy
    _ = y := R.shiftedSquare_inverseSquareRoot_sq y

/-- A bounded self-adjoint injective operator has dense range. -/
theorem StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData.inverseSquareRoot_range_dense
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData A) :
    Dense (R.inverseSquareRoot.range : Set H) := by
  have hAdjoint :
      R.inverseSquareRoot.adjoint = R.inverseSquareRoot :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp R.selfAdjoint
  have hKer : R.inverseSquareRoot.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr R.inverseSquareRoot_injective
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range, hAdjoint, hKer]
  simp

/-- The natural square domain is dense because it contains the dense range of the
canonical inverse square root. -/
theorem StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData.shiftedSquare_dense_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData A) :
    Dense
      ((standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain : Set H) := by
  have hRangeLe :
      R.inverseSquareRoot.range ≤
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain := by
    rintro z ⟨x, rfl⟩
    exact R.range_mem_shiftedSquare_domain x
  have hRangeClosure :
      R.inverseSquareRoot.range.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp R.inverseSquareRoot_range_dense
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply le_antisymm le_top
  rw [← hRangeClosure]
  exact Submodule.topologicalClosure_mono hRangeLe

/-- The square law makes the canonical shifted square surjective. -/
theorem StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData.shiftedSquare_surjective
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData A) :
    Function.Surjective
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A) := by
  intro x
  refine ⟨
    ⟨R.inverseSquareRoot (R.inverseSquareRoot x),
      R.range_mem_shiftedSquare_domain (R.inverseSquareRoot x)⟩,
    ?_⟩
  exact R.shiftedSquare_inverseSquareRoot_sq x

/-- The canonical `1 + A²` is self-adjoint once its inverse-square-root square law is
available.  Formal symmetry is theorem-generated from self-adjointness of `A`, while
density and surjectivity are theorem-generated from the inverse-square-root data. -/
theorem StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData.shiftedSquare_isSelfAdjoint
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData A)
    (core : RealHilbertSelfAdjointCore A) :
    IsSelfAdjoint
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A) := by
  exact LinearPMap.isSelfAdjoint_of_isFormalAdjoint_of_surjective
    (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A)
    R.shiftedSquare_dense_domain
    (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_isFormalAdjoint A core)
    R.shiftedSquare_surjective

/-- The canonical inverse-square-root datum reconstructs the positive shifted-square
data required by the existing analytic pipeline; shifted-square self-adjointness is no
longer a separate constructor input. -/
def StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData.toPositiveShiftedSquareData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointPositiveShiftedSquareData A :=
  let X : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSelfAdjointData A :=
    { selfAdjoint := R.shiftedSquare_isSelfAdjoint core }
  ((X.toAnalyticData core).toPositiveShiftedSquareExtensionData).toPositiveShiftedSquareData

/-- The same canonical datum reconstructs the existing dependent inverse-square-root
stage after generating its shifted-square argument. -/
def StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData.toInverseSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (R : StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointInverseSquareRootData
      (R.toPositiveShiftedSquareData core) where
  inverseSquareRoot := R.inverseSquareRoot
  selfAdjoint := R.selfAdjoint
  norm_le_one := R.norm_le_one
  range_mem_original_domain := R.range_mem_original_domain
  range_mem_shiftedSquare_domain := by
    intro x
    change R.inverseSquareRoot x ∈
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain
    exact R.range_mem_shiftedSquare_domain x
  shiftedSquare_inverseSquareRoot_sq := by
    intro x
    change standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
        ⟨R.inverseSquareRoot (R.inverseSquareRoot x),
          R.range_mem_shiftedSquare_domain (R.inverseSquareRoot x)⟩ = x
    exact R.shiftedSquare_inverseSquareRoot_sq x
  eigenvector_evaluation := R.eigenvector_evaluation

/-- Uniform construction of the canonical inverse square root before shifted-square
self-adjointness has been supplied. -/
structure StandardRealHilbertSelfAdjointCanonicalInverseSquareRootDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointCanonicalInverseSquareRootData A

/-- The standard bounded-transform construction with shifted-square self-adjointness
generated from the canonical inverse-square-root stage. -/
structure InverseSquareRootGeneratedStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  inverseSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalInverseSquareRootDataConstructor
  domainAction :
    StandardRealHilbertSelfAdjointBoundedTransformDomainActionDataConstructor
  boundedExtension :
    StandardRealHilbertSelfAdjointBoundedTransformBoundedExtensionDataConstructor
  analyticProperties :
    StandardRealHilbertSelfAdjointBoundedTransformAnalyticPropertiesConstructor

/-- Collapse the inverse-square-root-generated route directly to the existing bounded
operator-data constructor. -/
def InverseSquareRootGeneratedStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : InverseSquareRootGeneratedStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor where
  construct := fun A core =>
    let R₀ := P.inverseSquareRoot.construct A core
    let S := R₀.toPositiveShiftedSquareData core
    let R := R₀.toInverseSquareRootData core
    let D := P.domainAction.construct A core S R
    let B := P.boundedExtension.construct A core S R D
    let Q := P.analyticProperties.construct A core S R D B
    ({ positiveShiftedSquare := S
       inverseSquareRoot := R
       domainAction := D
       boundedExtension := B
       analyticProperties := Q } :
      StandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipeline A).toOperatorData

/-- The inverse-square-root-generated operator construction followed by the independent
spectral pullback and bounded Borel spectral theorem. -/
structure InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    InverseSquareRootGeneratedStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Forget the inverse-square-root generation proof and recover the existing fully
factored standard route. -/
def InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toFactored
    (P : InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransformOperator := P.operatorConstruction.toOperatorDataConstructor
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The new route yields the unchanged generic real-Hilbert spectral-resolution
constructor. -/
def InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toConstructor

/-- The new route specializes to the unchanged reconstructed Wightman OS interface. -/
def InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toExplicitWightmanOSConstructor

/-- The inverse-square-root-generated route plus actual-model measurable PVM
identification yields physical indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_inverseSquareRootGeneratedFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_standardBoundedTransformBorelPipeline
      P.toFactored.toStandard M X

/-- Adding the scalar-measure quadratic law yields the unchanged canonical physical
eigenprojection law. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_inverseSquareRootGeneratedFactoredStandardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : InverseSquareRootGeneratedFactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
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

end MathlibAnalytic
end MGAP4D

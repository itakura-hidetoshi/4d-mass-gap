import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformCanonicalBoundedExtension
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The shifted-square right-inverse law decomposes every vector as
`x = K x + A² K x`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverse_shiftedSquare_decomposition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (_core : RealHilbertSelfAdjointCore A)
    (x : H) :
    K.inverse x +
        standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain x) =
      x := by
  let xSquare : standardRealHilbertSelfAdjointSquareDomain A :=
    K.inverseToSquareDomain x
  have hAmbient :
      standardRealHilbertSelfAdjointSquareDomainEquivAmbient A xSquare =
        (⟨K.inverse x, K.range_mem_shiftedSquare_domain x⟩ :
          (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain) := by
    apply Subtype.ext
    exact K.inverseToSquareDomain_coe x
  have h := K.shiftedSquare_inverse x
  rw [← hAmbient,
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply,
    standardRealHilbertSelfAdjointShiftedSquareAction_apply] at h
  simpa [xSquare] using h

/-- The everywhere-defined action `A K` is bounded.  The estimate factors through the positive
square root: `‖A K x‖ ≤ ‖R x‖ ≤ ‖x‖`. -/
noncomputable def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.inverseOriginalActionContinuous
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) :
    H →L[ℝ] H :=
  K.inverseOriginalAction.mkContinuous 1 (by
    intro x
    calc
      ‖K.inverseOriginalAction x‖ ≤ ‖R.squareRoot x‖ :=
        R.toAlgebraicSquareRootData.inverseOriginalAction_norm_le_squareRoot core x
      _ ≤ ‖x‖ := R.squareRoot_norm_apply_le x
      _ = 1 * ‖x‖ := by simp)

@[simp]
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.inverseOriginalActionContinuous_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    R.inverseOriginalActionContinuous core x = K.inverseOriginalAction x :=
  rfl

/-- The generated bounded realization of `A K` is a contraction. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.inverseOriginalActionContinuous_norm_le_one
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) :
    ‖R.inverseOriginalActionContinuous core‖ ≤ 1 := by
  apply (R.inverseOriginalActionContinuous core).opNorm_le_bound zero_le_one
  intro x
  change ‖K.inverseOriginalAction x‖ ≤ 1 * ‖x‖
  calc
    ‖K.inverseOriginalAction x‖ ≤ ‖R.squareRoot x‖ :=
      R.toAlgebraicSquareRootData.inverseOriginalAction_norm_le_squareRoot core x
    _ ≤ ‖x‖ := R.squareRoot_norm_apply_le x
    _ = 1 * ‖x‖ := by simp

/-- Formal self-adjointness of `A` and the decomposition
`x = Kx + A²Kx` make the bounded operator `A K` symmetric. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.inverseOriginalActionContinuous_isSymmetric
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) :
    (R.inverseOriginalActionContinuous core : H →ₗ[ℝ] H).IsSymmetric := by
  intro x y
  have hFormal : A.IsFormalAdjoint A :=
    realHilbertSelfAdjointCore_isFormalSelfAdjoint core
  have hFirst :
      inner ℝ (K.inverseOriginalAction x) (K.inverse y) =
        inner ℝ (K.inverse x) (K.inverseOriginalAction y) := by
    simpa only [
      StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalAction_apply,
      StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToOriginalDomain_coe] using
      hFormal (K.inverseToOriginalDomain x) (K.inverseToOriginalDomain y)
  have hMiddle :
      inner ℝ
          (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain y))
          (K.inverseOriginalAction x) =
        inner ℝ
          (K.inverseOriginalAction y)
          (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain x)) := by
    simpa only [standardRealHilbertSelfAdjointSquareAction_apply,
      standardRealHilbertSelfAdjointSquareToDomain_coe,
      StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalAction_apply,
      StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToOriginalDomain_coe] using
      hFormal
        (standardRealHilbertSelfAdjointSquareToDomain A (K.inverseToSquareDomain y))
        (standardRealHilbertSelfAdjointSquareToDomain A (K.inverseToSquareDomain x))
  have hSecond :
      inner ℝ
          (K.inverseOriginalAction x)
          (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain y)) =
        inner ℝ
          (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain x))
          (K.inverseOriginalAction y) := by
    calc
      inner ℝ
          (K.inverseOriginalAction x)
          (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain y)) =
          inner ℝ
            (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain y))
            (K.inverseOriginalAction x) := real_inner_comm _ _
      _ = inner ℝ
            (K.inverseOriginalAction y)
            (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain x)) := hMiddle
      _ = inner ℝ
            (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain x))
            (K.inverseOriginalAction y) := real_inner_comm _ _
  change inner ℝ (K.inverseOriginalAction x) y =
    inner ℝ x (K.inverseOriginalAction y)
  calc
    inner ℝ (K.inverseOriginalAction x) y =
        inner ℝ (K.inverseOriginalAction x)
          (K.inverse y +
            standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain y)) := by
      rw [K.inverse_shiftedSquare_decomposition core y]
    _ = inner ℝ (K.inverseOriginalAction x) (K.inverse y) +
          inner ℝ (K.inverseOriginalAction x)
            (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain y)) := by
      rw [inner_add_right]
    _ = inner ℝ (K.inverse x) (K.inverseOriginalAction y) +
          inner ℝ
            (standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain x))
            (K.inverseOriginalAction y) := by
      rw [hFirst, hSecond]
    _ = inner ℝ
          (K.inverse x +
            standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain x))
          (K.inverseOriginalAction y) := by
      rw [inner_add_left]
    _ = inner ℝ x (K.inverseOriginalAction y) := by
      rw [K.inverse_shiftedSquare_decomposition core x]

/-- Since `A K` is bounded and symmetric on the complete Hilbert space, it is self-adjoint. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.inverseOriginalActionContinuous_selfAdjoint
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) :
    IsSelfAdjoint (R.inverseOriginalActionContinuous core) := by
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (R.inverseOriginalActionContinuous_isSymmetric core)

/-- On the dense range of `R`, the canonical bounded transform is the bounded operator `A K`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.canonicalBoundedOperator_apply_squareRoot
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    R.canonicalBoundedOperator (R.squareRoot x) =
      R.inverseOriginalActionContinuous core x := by
  change
    R.toAlgebraicSquareRootData.extendedOriginalAction (R.squareRoot x) =
      K.inverseOriginalAction x
  exact R.toAlgebraicSquareRootData.extendedOriginalAction_apply_squareRoot core x

/-- The exact residual commutation relation.  The two bounded self-adjoint contractions are
`A K` and `R = K¹ᐟ²`. -/
structure StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) where
  commute : Commute (R.inverseOriginalActionContinuous core) R.squareRoot

/-- Commutation of `A K` with `R` makes the canonical bounded transform symmetric on the dense
range of `R`, hence everywhere by continuity. -/
theorem StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationData.canonicalBoundedOperator_isSymmetric
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    {R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K}
    {core : RealHilbertSelfAdjointCore A}
    (Q : StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationData R core) :
    (R.canonicalBoundedOperator : H →ₗ[ℝ] H).IsSymmetric := by
  let T : H →L[ℝ] H := R.inverseOriginalActionContinuous core
  have hTSymmetric : (T : H →ₗ[ℝ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (R.inverseOriginalActionContinuous_selfAdjoint core)
  have hRSymmetric : (R.squareRoot : H →ₗ[ℝ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp R.selfAdjoint
  have hCommEq : T * R.squareRoot = R.squareRoot * T := Q.commute.eq
  have hCommApply (x : H) : T (R.squareRoot x) = R.squareRoot (T x) := by
    have h := congrArg (fun S : H →L[ℝ] H => S x) hCommEq
    change T (R.squareRoot x) = R.squareRoot (T x) at h
    exact h
  intro x y
  refine R.toAlgebraicSquareRootData.squareRoot_denseRange.induction_on₂
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro u v
  calc
    inner ℝ
        (R.canonicalBoundedOperator (R.squareRoot u))
        (R.squareRoot v) =
        inner ℝ (T u) (R.squareRoot v) := by
          rw [R.canonicalBoundedOperator_apply_squareRoot core]
    _ = inner ℝ u (T (R.squareRoot v)) := hTSymmetric u (R.squareRoot v)
    _ = inner ℝ u (R.squareRoot (T v)) := by rw [hCommApply]
    _ = inner ℝ (R.squareRoot u) (T v) :=
      (hRSymmetric u (T v)).symm
    _ = inner ℝ
        (R.squareRoot u)
        (R.canonicalBoundedOperator (R.squareRoot v)) := by
          rw [R.canonicalBoundedOperator_apply_squareRoot core]

/-- The commutation relation generates the previously residual self-adjointness datum. -/
def StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationData.toSelfAdjointData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    {R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K}
    {core : RealHilbertSelfAdjointCore A}
    (Q : StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationData R core) :
    StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformSelfAdjointData R where
  selfAdjoint := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    Q.canonicalBoundedOperator_isSymmetric

/-- Uniform proof of the exact commutation relation between `A K` and `R`. -/
structure StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (core : RealHilbertSelfAdjointCore A)
      (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
      (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K),
        StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationData R core

/-- After `A K` has been generated as bounded self-adjoint, commutation with `R` supplies all
bounded-transform operator data. -/
structure CommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  boundedInverse :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor
  positiveSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootDataConstructor
  commutation :
    StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationDataConstructor

/-- Collapse the commutation-only route to the preceding self-adjointness-only route. -/
def CommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toCanonicalBoundedExtension
    (P : CommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    CanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  boundedInverse := P.boundedInverse
  positiveSquareRoot := P.positiveSquareRoot
  boundedTransformSelfAdjoint :=
    { construct := fun A core K R =>
        (P.commutation.construct A core K R).toSelfAdjointData }

/-- The commutation-only route supplies the unchanged bounded-transform operator data. -/
def CommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : CommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toCanonicalBoundedExtension.toOperatorDataConstructor

/-- The graph-Riesz inverse and generic real self-adjoint CFC now leave only commutation of
`A K` with the CFC-generated positive square root. -/
structure ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  boundedInverse :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor
  continuousFunctionalCalculus :
    RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusDataConstructor
  commutation :
    StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationDataConstructor

/-- Expose the CFC-generated square root and the commutation-only operator construction. -/
def ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toCommutingCanonicalBoundedTransform
    (P : ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    CommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  boundedInverse := P.boundedInverse
  positiveSquareRoot :=
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootDataConstructor.toNaturalDomainSquareRootDataConstructor
      P.continuousFunctionalCalculus.toAlgebraicSquareRootDataConstructor
  commutation := P.commutation

/-- The CFC-factored commutation-only route supplies the unchanged operator-data constructor. -/
def ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toCommutingCanonicalBoundedTransform.toOperatorDataConstructor

/-- Add the unchanged measurable pullback and bounded Borel spectral resolution. -/
structure ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the commutation-only route to the existing factored standard pipeline. -/
def ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toFactored
    (P : ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransformOperator := P.operatorConstruction.toOperatorDataConstructor
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The commutation-only route yields the unchanged generic real-Hilbert spectral-resolution
constructor. -/
def ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toConstructor

/-- The same route specializes to the unchanged reconstructed Wightman OS interface. -/
def ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : ContinuousFunctionalCalculusCommutingCanonicalBoundedTransformStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toExplicitWightmanOSConstructor

end

end MathlibAnalytic
end MGAP4D

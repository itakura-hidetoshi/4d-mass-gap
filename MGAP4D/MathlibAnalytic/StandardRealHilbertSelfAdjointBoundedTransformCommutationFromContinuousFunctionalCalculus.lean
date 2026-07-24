import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformSelfAdjointFromCommutation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The shifted-square decomposition identifies the square action on `K x`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.squareAction_inverse_eq_sub
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    standardRealHilbertSelfAdjointSquareAction A (K.inverseToSquareDomain x) =
      x - K.inverse x := by
  rw [eq_sub_iff_add_eq]
  simpa [add_comm] using K.inverse_shiftedSquare_decomposition core x

/-- For `x ∈ D(A)`, the vector `A K x` belongs to the natural square domain. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalActionToSquareDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : A.domain) :
    standardRealHilbertSelfAdjointSquareDomain A :=
  ⟨standardRealHilbertSelfAdjointSquareToDomain A
      (K.inverseToSquareDomain (x : H)), by
    change A (standardRealHilbertSelfAdjointSquareToDomain A
      (K.inverseToSquareDomain (x : H))) ∈ A.domain
    rw [← standardRealHilbertSelfAdjointSquareAction_apply,
      K.squareAction_inverse_eq_sub core (x : H)]
    have hKDomain : K.inverse (x : H) ∈ A.domain := by
      simpa only [
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToOriginalDomain_coe]
        using (K.inverseToOriginalDomain (x : H)).property
    exact A.domain.sub_mem x.property hKDomain⟩

/-- The second application of `A` to `K x` is `x - K x`, as an equality in `D(A)`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalActionToSquareDomain_image
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : A.domain) :
    standardRealHilbertSelfAdjointSquareToDomain A
        (K.inverseOriginalActionToSquareDomain core x) =
      x - K.inverseToOriginalDomain (x : H) := by
  apply Subtype.ext
  simpa [
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalActionToSquareDomain,
    standardRealHilbertSelfAdjointSquareAction_apply] using
      K.squareAction_inverse_eq_sub core (x : H)

/-- Applying `1 + A²` to `A K x` gives `A x` for every `x ∈ D(A)`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.shiftedSquare_inverseOriginalActionToSquareDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : A.domain) :
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
        (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A
          (K.inverseOriginalActionToSquareDomain core x)) =
      A x := by
  rw [standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply,
    standardRealHilbertSelfAdjointShiftedSquareAction_apply,
    standardRealHilbertSelfAdjointSquareAction_apply,
    K.inverseOriginalActionToSquareDomain_image core x]
  change A (K.inverseToOriginalDomain (x : H)) +
      A (x - K.inverseToOriginalDomain (x : H)) = A x
  rw [A.map_sub]
  abel

/-- The square-domain transport of the bounded inverse is definitionally the ambient-domain lift. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.squareDomainEquiv_inverseToSquareDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (x : H) :
    standardRealHilbertSelfAdjointSquareDomainEquivAmbient A
        (K.inverseToSquareDomain x) =
      K.inverseToShiftedSquareDomain x := by
  dsimp [StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToSquareDomain]
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Uniqueness for `1 + A²` proves `K (A x) = A (K x)` on `D(A)`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverse_apply_image_eq_inverseOriginalAction
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    (x : A.domain) :
    K.inverse (A x) = K.inverseOriginalAction (x : H) := by
  have hSquare :
      K.inverseToSquareDomain (A x) =
        K.inverseOriginalActionToSquareDomain core x := by
    apply (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).injective
    apply standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_injective A core
    calc
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A
            (K.inverseToSquareDomain (A x))) =
          standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
            (K.inverseToShiftedSquareDomain (A x)) := by
              rw [K.squareDomainEquiv_inverseToSquareDomain]
      _ = A x := K.shiftedSquare_inverse (A x)
      _ = standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A
            (K.inverseOriginalActionToSquareDomain core x)) :=
        (K.shiftedSquare_inverseOriginalActionToSquareDomain core x).symm
  have hCoe := congrArg
    (fun z : standardRealHilbertSelfAdjointSquareDomain A => ((z : A.domain) : H)) hSquare
  simpa [StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalActionToSquareDomain,
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalAction_apply]
    using hCoe

/-- The bounded self-adjoint operators `A K` and `K` commute. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.inverseOriginalActionContinuous_commute_inverse
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) :
    Commute (R.inverseOriginalActionContinuous core) K.inverse := by
  rw [commute_iff_eq]
  ext x
  change K.inverseOriginalAction (K.inverse x) =
    K.inverse (K.inverseOriginalAction x)
  have h := K.inverse_apply_image_eq_inverseOriginalAction core
    (K.inverseToOriginalDomain x)
  simpa only [
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalAction_apply,
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToOriginalDomain_coe]
    using h.symm

/-- The canonical CFC square root of the positive bounded inverse. -/
noncomputable def RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData.toCanonicalAlgebraicSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H)
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K := by
  letI : ContinuousFunctionalCalculus ℝ (H →L[ℝ] H) IsSelfAdjoint :=
    C.continuousFunctionalCalculus
  letI : StarOrderedRing (H →L[ℝ] H) :=
    ContinuousLinearMap.instStarOrderedRingRCLike
  have hKPositive : K.inverse.IsPositive :=
    (ContinuousLinearMap.isPositive_iff' K.inverse).2
      ⟨K.selfAdjoint, K.quadraticForm_nonnegative⟩
  have hKNonnegative : 0 ≤ K.inverse :=
    (ContinuousLinearMap.nonneg_iff_isPositive K.inverse).mpr hKPositive
  let R : H →L[ℝ] H := CFC.sqrt K.inverse
  have hRNonnegative : 0 ≤ R := by
    dsimp [R]
    exact CFC.sqrt_nonneg K.inverse
  have hRPositive : R.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive R).mp hRNonnegative
  have hRSquare : R ^ 2 = K.inverse := by
    dsimp [R]
    exact CFC.sq_sqrt K.inverse hKNonnegative
  refine
    { squareRoot := R
      selfAdjoint := hRPositive.isSelfAdjoint
      quadraticForm_nonnegative := fun x => hRPositive.inner_nonneg_left x
      squareRoot_sq := fun x => ?_ }
  have hApply := congrArg (fun T : H →L[ℝ] H => T x) hRSquare
  simpa [pow_two] using hApply

/-- The explicit CFC square root, upgraded to the theorem-generated natural-domain data. -/
noncomputable def RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData.toCanonicalNaturalDomainSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H)
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K :=
  (C.toCanonicalAlgebraicSquareRootData K).toNaturalDomainSquareRootData core

/-- CFC functoriality turns `A K`--`K` commutation into commutation with `K¹ᐟ²`. -/
theorem RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData.canonicalSquareRoot_commute_inverseOriginalActionContinuous
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H)
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    let R := C.toCanonicalNaturalDomainSquareRootData K core
    Commute (R.inverseOriginalActionContinuous core) R.squareRoot := by
  letI : ContinuousFunctionalCalculus ℝ (H →L[ℝ] H) IsSelfAdjoint :=
    C.continuousFunctionalCalculus
  letI : StarOrderedRing (H →L[ℝ] H) :=
    ContinuousLinearMap.instStarOrderedRingRCLike
  let R := C.toCanonicalNaturalDomainSquareRootData K core
  have hKPositive : K.inverse.IsPositive :=
    (ContinuousLinearMap.isPositive_iff' K.inverse).2
      ⟨K.selfAdjoint, K.quadraticForm_nonnegative⟩
  have hKNonnegative : 0 ≤ K.inverse :=
    (ContinuousLinearMap.nonneg_iff_isPositive K.inverse).mpr hKPositive
  have hTK : Commute (R.inverseOriginalActionContinuous core) K.inverse :=
    R.inverseOriginalActionContinuous_commute_inverse core
  change Commute (R.inverseOriginalActionContinuous core) (CFC.sqrt K.inverse)
  rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hKNonnegative]
  exact (hTK.symm.cfc_real (fun x : ℝ => x ^ (1 / 2 : ℝ))).symm

/-- The generic real CFC now generates the previously residual commutation certificate. -/
noncomputable def RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData.toCanonicalCommutationData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H)
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformCommutationData
      (C.toCanonicalNaturalDomainSquareRootData K core) core where
  commute := C.canonicalSquareRoot_commute_inverseOriginalActionContinuous K core

/-- A bounded inverse and generic real CFC generate all bounded-transform operator data. -/
noncomputable def RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData.toCanonicalOperatorData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H)
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorData A := by
  let R := C.toCanonicalNaturalDomainSquareRootData K core
  exact R.toOperatorData_of_canonicalBoundedOperator_selfAdjoint core
    (C.toCanonicalCommutationData K core).toSelfAdjointData

/-- The graph-Riesz bounded inverse plus a generic real CFC now close the entire operator stage. -/
noncomputable def ContinuousFunctionalCalculusFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor.toCanonicalOperatorDataConstructor
    (P : ContinuousFunctionalCalculusFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor where
  construct := fun A core =>
    let K := P.boundedInverse.construct A core
    P.continuousFunctionalCalculus.construct.toCanonicalOperatorData K core

/-- Add only the unchanged measurable pullback and bounded Borel resolution after the CFC-closed
operator stage. -/
structure ContinuousFunctionalCalculusClosedStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    ContinuousFunctionalCalculusFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the CFC-closed operator route to the unchanged factored standard pipeline. -/
def ContinuousFunctionalCalculusClosedStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toFactored
    (P : ContinuousFunctionalCalculusClosedStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransformOperator := P.operatorConstruction.toCanonicalOperatorDataConstructor
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The CFC-closed route yields the unchanged generic real-Hilbert spectral-resolution constructor. -/
def ContinuousFunctionalCalculusClosedStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : ContinuousFunctionalCalculusClosedStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toConstructor

/-- The same CFC-closed route specializes to the reconstructed Wightman OS interface. -/
def ContinuousFunctionalCalculusClosedStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : ContinuousFunctionalCalculusClosedStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toExplicitWightmanOSConstructor

end

end MathlibAnalytic
end MGAP4D

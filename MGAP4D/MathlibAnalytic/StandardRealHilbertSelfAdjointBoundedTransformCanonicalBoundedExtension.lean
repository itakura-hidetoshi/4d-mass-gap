import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformNaturalDomainCanonicalAction
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- Forget the theorem-generated natural-domain regularity and retain the algebraic positive
square-root data. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.toAlgebraicSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K where
  squareRoot := R.squareRoot
  selfAdjoint := R.selfAdjoint
  quadraticForm_nonnegative := R.quadraticForm_nonnegative
  squareRoot_sq := R.squareRoot_sq

/-- The dense-range extension lies in the graph of `A` at every point.  This is the closed-graph
argument used previously to generate `R(H) ⊆ D(A)`, now retained with its second-coordinate
information. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.extendedOriginalAction_mem_graph
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    (R.squareRoot x, R.extendedOriginalAction x) ∈ A.graph := by
  let D : H →L[ℝ] H := R.extendedOriginalAction
  have hClosed :
      IsClosed {z : H | (R.squareRoot z, D z) ∈ A.graph} := by
    change IsClosed
      ((fun z : H => (R.squareRoot z, D z)) ⁻¹' (A.graph : Set (H × H)))
    exact core.selfAdjoint.isClosed.preimage
      (R.squareRoot.continuous.prodMk D.continuous)
  have hGraph : ∀ z : H, (R.squareRoot z, D z) ∈ A.graph := by
    exact R.squareRoot_denseRange.induction
      (fun z hz => by
        rcases hz with ⟨w, rfl⟩
        have hD : D (R.squareRoot w) = K.inverseOriginalAction w := by
          exact R.extendedOriginalAction_apply_squareRoot core w
        rw [R.squareRoot_sq w, hD]
        simpa only [
          StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToOriginalDomain_coe,
          StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalAction_apply]
          using A.mem_graph (K.inverseToOriginalDomain w))
      hClosed
  exact hGraph x

/-- The extended action is exactly `A (R x)` on all of `H`, not only on the dense range used in
its construction. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.extendedOriginalAction_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    R.extendedOriginalAction x =
      A ⟨R.squareRoot x, R.range_mem_original_domain core x⟩ := by
  exact (A.image_iff (R.range_mem_original_domain core x)).2
    (R.extendedOriginalAction_mem_graph core x)

/-- The dense-range norm estimate gives the operator-norm contraction of the extension. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.extendedOriginalAction_norm_le_one
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) :
    ‖R.extendedOriginalAction‖ ≤ 1 := by
  exact LinearMap.opNorm_extendOfNorm_le
    (f := K.inverseOriginalAction)
    (e := R.squareRoot.toLinearMap)
    R.squareRoot_denseRange zero_le_one
    (fun z => by
      simpa only [one_mul] using R.inverseOriginalAction_norm_le_squareRoot core z)

/-- The canonical bounded realization of `A (1 + A²)⁻¹ᐟ²`. -/
noncomputable def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.canonicalBoundedOperator
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K) :
    H →L[ℝ] H :=
  R.toAlgebraicSquareRootData.extendedOriginalAction

/-- The canonical bounded operator agrees pointwise with the generated algebraic domain action. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.canonicalBoundedOperator_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    R.canonicalBoundedOperator x = R.canonicalDomainAction x := by
  change R.toAlgebraicSquareRootData.extendedOriginalAction x = _
  rw [R.toAlgebraicSquareRootData.extendedOriginalAction_apply core x,
    R.canonicalDomainAction_apply]
  congr 1

/-- The canonical bounded transform is automatically a contraction. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.canonicalBoundedOperator_norm_le_one
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) :
    ‖R.canonicalBoundedOperator‖ ≤ 1 := by
  exact R.toAlgebraicSquareRootData.extendedOriginalAction_norm_le_one core

/-- Package the theorem-generated canonical bounded operator as the preceding extension datum. -/
noncomputable def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.toCanonicalBoundedExtensionData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointNaturalDomainBoundedTransformBoundedExtensionData R where
  boundedOperator := R.canonicalBoundedOperator
  agrees_with_canonicalDomainAction := R.canonicalBoundedOperator_apply core

/-- After extension and contraction have been generated, only self-adjointness of the canonical
bounded transform remains as operator-side data. -/
structure StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformSelfAdjointData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K) where
  selfAdjoint : IsSelfAdjoint R.canonicalBoundedOperator

/-- The natural-domain square root and self-adjointness of its canonical bounded transform generate
all bounded-transform operator data. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.toOperatorData_of_canonicalBoundedOperator_selfAdjoint
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    (Q : StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformSelfAdjointData R) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorData A where
  boundedOperator := R.canonicalBoundedOperator
  boundedSelfAdjoint := Q.selfAdjoint
  boundedOperator_norm_le_one := R.canonicalBoundedOperator_norm_le_one core
  eigenvector_forward := fun x hE =>
    (R.toCanonicalBoundedExtensionData core).eigenvector_evaluation core x hE

/-- Uniform proof of self-adjointness for the theorem-generated canonical bounded transform. -/
structure StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformSelfAdjointDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (_core : RealHilbertSelfAdjointCore A)
      (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
      (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K),
        StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformSelfAdjointData R

/-- The operator-construction route after continuous extension, contraction, and eigenvector
evaluation have all become theorem-generated. -/
structure CanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  boundedInverse :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor
  positiveSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootDataConstructor
  boundedTransformSelfAdjoint :
    StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformSelfAdjointDataConstructor

/-- Collapse the self-adjointness-only route to the unchanged bounded-transform operator data. -/
def CanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : CanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor where
  construct := fun A core =>
    let K := P.boundedInverse.construct A core
    let R := P.positiveSquareRoot.construct A core K
    let Q := P.boundedTransformSelfAdjoint.construct A core K R
    R.toOperatorData_of_canonicalBoundedOperator_selfAdjoint core Q

/-- The graph-Riesz inverse and a generic real self-adjoint CFC leave only self-adjointness of the
canonical bounded transform as an operator-construction boundary. -/
structure ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  boundedInverse :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor
  continuousFunctionalCalculus :
    RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusDataConstructor
  boundedTransformSelfAdjoint :
    StandardRealHilbertSelfAdjointNaturalDomainCanonicalBoundedTransformSelfAdjointDataConstructor

/-- Expose the CFC-generated natural-domain square root and the theorem-generated bounded
extension. -/
def ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toCanonicalBoundedExtension
    (P : ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    CanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor where
  boundedInverse := P.boundedInverse
  positiveSquareRoot :=
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootDataConstructor.toNaturalDomainSquareRootDataConstructor
      P.continuousFunctionalCalculus.toAlgebraicSquareRootDataConstructor
  boundedTransformSelfAdjoint := P.boundedTransformSelfAdjoint

/-- The CFC-factored self-adjointness-only route supplies the unchanged operator-data constructor. -/
def ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor.toOperatorDataConstructor
    (P : ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor :=
  P.toCanonicalBoundedExtension.toOperatorDataConstructor

/-- Add the unchanged measurable pullback and bounded Borel resolution to the reduced operator
construction. -/
structure ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  operatorConstruction :
    ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformOperatorConstructionPipelineConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the self-adjointness-only route to the existing factored standard pipeline. -/
def ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toFactored
    (P : ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransformOperator := P.operatorConstruction.toOperatorDataConstructor
  spectralPullback := P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The reduced route yields the unchanged generic real-Hilbert spectral-resolution constructor. -/
def ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toConstructor

/-- The same route specializes to the unchanged reconstructed Wightman OS interface. -/
def ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : ContinuousFunctionalCalculusCanonicalBoundedExtensionStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toFactored.toExplicitWightmanOSConstructor

end

end MathlibAnalytic
end MGAP4D

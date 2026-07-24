import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformSpectralCoordinate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The operator-theoretic part of the standard bounded transform
`A ↦ A (1 + A²)⁻¹ᐟ²`.

The scalar spectral coordinate is no longer data: it is fixed by
`standardRealHilbertBoundedTransformSpectralCoordinate`.  This structure isolates
exactly the bounded operator, self-adjointness, contraction bound, and eigenvector
evaluation that must be obtained from the unbounded self-adjoint operator. -/
structure StandardRealHilbertSelfAdjointBoundedTransformOperatorData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  boundedOperator : H →L[ℝ] H
  boundedSelfAdjoint : IsSelfAdjoint boundedOperator
  boundedOperator_norm_le_one : ‖boundedOperator‖ ≤ 1
  eigenvector_forward :
    ∀ {E : ℝ} (x : A.domain),
      A x = E • (x : H) →
        boundedOperator (x : H) =
          standardRealHilbertBoundedTransformSpectralCoordinate E • (x : H)

/-- The independent measurable spectral pullback for one standard bounded-transform
operator.  This is intentionally separated from construction of the operator itself:
it is the exact descent from a bounded Borel PVM resolution to an unbounded
real-Hilbert spectral resolution. -/
structure StandardRealHilbertSelfAdjointBoundedTransformSpectralPullback
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (T : StandardRealHilbertSelfAdjointBoundedTransformOperatorData A) where
  transfer :
    RealHilbertBoundedSelfAdjointBorelSpectralResolution T.boundedOperator →
      RealHilbertSelfAdjointSpectralResolution A

/-- Recombine the operator-theoretic data and its measurable spectral pullback into
the standard bridge used by the existing bounded-transform/Borel pipeline. -/
def StandardRealHilbertSelfAdjointBoundedTransformOperatorData.toBridge
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (T : StandardRealHilbertSelfAdjointBoundedTransformOperatorData A)
    (P : StandardRealHilbertSelfAdjointBoundedTransformSpectralPullback T) :
    StandardRealHilbertSelfAdjointBoundedTransformBridge A where
  boundedOperator := T.boundedOperator
  boundedSelfAdjoint := T.boundedSelfAdjoint
  boundedOperator_norm_le_one := T.boundedOperator_norm_le_one
  eigenvector_forward := T.eigenvector_forward
  transfer := P.transfer

/-- Uniform construction of only the operator-theoretic standard bounded transform
from the Mathlib-discharged self-adjoint core. -/
structure StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointBoundedTransformOperatorData A

/-- Uniform construction of the measurable pullback after the standard bounded
operator has been supplied. -/
structure StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (core : RealHilbertSelfAdjointCore A)
      (T : StandardRealHilbertSelfAdjointBoundedTransformOperatorData A),
      StandardRealHilbertSelfAdjointBoundedTransformSpectralPullback T

/-- The two independent standard bounded-transform residuals reconstruct the bridge
constructor required by the existing pipeline. -/
def standardRealHilbertSelfAdjointBoundedTransformBridgeConstructor_of_operatorData_and_pullback
    (O : StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor)
    (P : StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor) :
    StandardRealHilbertSelfAdjointBoundedTransformBridgeConstructor where
  construct := fun A core =>
    let T := O.construct A core
    T.toBridge (P.construct A core T)

/-- A fully factored standard route: operator construction, measurable pullback, and
the independent bounded Borel spectral theorem. -/
structure FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransformOperator :
    StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor
  spectralPullback :
    StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Collapse the factored route to the standard pipeline already connected to the
generic spectral theorem and the OS/Wightman interfaces. -/
def FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toStandard
    (P : FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransform :=
    standardRealHilbertSelfAdjointBoundedTransformBridgeConstructor_of_operatorData_and_pullback
      P.boundedTransformOperator P.spectralPullback
  boundedBorelResolution := P.boundedBorelResolution

/-- The factored standard route yields the global real-Hilbert spectral-resolution
constructor without changing its theorem statement. -/
def FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toStandard.toConstructor

/-- Separate operator, pullback, and bounded-Borel constructors suffice for the full
generic self-adjoint spectral theorem. -/
theorem real_hilbert_selfAdjoint_spectralResolution_constructor_nonempty_of_standardOperator_pullback_and_borel
    (O : StandardRealHilbertSelfAdjointBoundedTransformOperatorDataConstructor)
    (P : StandardRealHilbertSelfAdjointBoundedTransformSpectralPullbackConstructor)
    (B : RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor) :
    Nonempty RealHilbertSelfAdjointSpectralResolutionConstructor := by
  exact ⟨
    ({ boundedTransformOperator := O
       spectralPullback := P
       boundedBorelResolution := B } :
      FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline).toConstructor⟩

/-- The factored standard route remains directly available at the reconstructed
OS/Wightman model boundary. -/
def FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline
    .toExplicitWightmanOSConstructor
    (P : FactoredStandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toStandard.toExplicitWightmanOSConstructor

end

end MathlibAnalytic
end MGAP4D

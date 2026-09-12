import MGAP4D.MathlibAnalytic.RealHilbertSelfAdjointSpectralResolutionCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Borel spectral-resolution data for one bounded self-adjoint operator on a real
Hilbert space.  This is deliberately stronger than continuous functional calculus:
it includes measurable-set projections and indicator-function evaluation. -/
structure RealHilbertBoundedSelfAdjointBorelSpectralResolution
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (B : H →L[ℝ] H) where
  selfAdjoint : IsSelfAdjoint B
  spectralPVM : OrthogonalProjectionValuedSetFunction H
  integral : (ℝ → ℝ) → H → H
  indicator_integral_eq_projection :
    ∀ (s : Set ℝ), MeasurableSet s → ∀ ψ : H,
      integral (s.indicator fun _ => (1 : ℝ)) ψ =
        spectralPVM.projection s ψ
  eigenvector_integral_evaluation :
    ∀ {E : ℝ} (x : H),
      B x = E • x →
        ∀ f : ℝ → ℝ,
          integral f x = f E • x

/-- The bounded real-Hilbert Borel spectral theorem required after a bounded
transform has been constructed.  The pinned Mathlib continuous functional
calculus does not itself provide this measurable indicator/PVM package. -/
structure RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (B : H →L[ℝ] H),
      IsSelfAdjoint B →
        RealHilbertBoundedSelfAdjointBorelSpectralResolution B

/-- Data connecting an unbounded self-adjoint `LinearPMap` to a bounded
self-adjoint operator.  Besides the bounded operator and its spectral-coordinate
map, the bridge carries the exact pullback/descent operation which turns a Borel
resolution of the bounded transform into a resolution of the original operator. -/
structure RealHilbertSelfAdjointBoundedTransformBridge
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  boundedOperator : H →L[ℝ] H
  boundedSelfAdjoint : IsSelfAdjoint boundedOperator
  boundedOperator_norm_le_one : ‖boundedOperator‖ ≤ 1
  spectralCoordinate : ℝ → ℝ
  spectralCoordinate_injective : Function.Injective spectralCoordinate
  spectralCoordinate_mem_openUnit :
    ∀ E : ℝ, spectralCoordinate E ∈ Set.Ioo (-1 : ℝ) 1
  eigenvector_forward :
    ∀ {E : ℝ} (x : A.domain),
      A x = E • (x : H) →
        boundedOperator (x : H) = spectralCoordinate E • (x : H)
  transfer :
    RealHilbertBoundedSelfAdjointBorelSpectralResolution boundedOperator →
      RealHilbertSelfAdjointSpectralResolution A

/-- Uniform bounded-transform construction from the Mathlib-discharged
self-adjoint core.  This is the first independent residual in the standard
unbounded-to-bounded spectral-theorem route. -/
structure RealHilbertSelfAdjointBoundedTransformBridgeConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        RealHilbertSelfAdjointBoundedTransformBridge A

/-- The exact two-certificate pipeline for the generic real-Hilbert unbounded
spectral theorem:

1. construct a bounded self-adjoint transform and the spectral pullback bridge;
2. construct a Borel PVM resolution for every bounded self-adjoint operator.

No OS/Wightman or Yang--Mills field occurs in this package. -/
structure RealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransform : RealHilbertSelfAdjointBoundedTransformBridgeConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- The bounded-transform/Borel pipeline extends every Mathlib self-adjoint core
to a full real-Hilbert spectral resolution. -/
def RealHilbertSelfAdjointBoundedTransformBorelPipeline.toExtension
    (P : RealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionExtension where
  extend := fun A core =>
    let T := P.boundedTransform.construct A core
    T.transfer
      (P.boundedBorelResolution.construct
        T.boundedOperator T.boundedSelfAdjoint)

/-- Consequently, the two-certificate pipeline yields the model-independent
self-adjoint spectral-resolution constructor. -/
def RealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : RealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toExtension.toConstructor

/-- Separate bounded-transform and bounded-Borel constructors are sufficient for
the full extension theorem. -/
theorem real_hilbert_selfAdjoint_spectralResolution_extension_nonempty_of_boundedTransform_and_borel
    (T : RealHilbertSelfAdjointBoundedTransformBridgeConstructor)
    (B : RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor) :
    Nonempty RealHilbertSelfAdjointSpectralResolutionExtension := by
  exact ⟨
    ({ boundedTransform := T
       boundedBorelResolution := B } :
      RealHilbertSelfAdjointBoundedTransformBorelPipeline).toExtension⟩

/-- The same two independent constructors are sufficient for the global
self-adjoint spectral-resolution constructor. -/
theorem real_hilbert_selfAdjoint_spectralResolution_constructor_nonempty_of_boundedTransform_and_borel
    (T : RealHilbertSelfAdjointBoundedTransformBridgeConstructor)
    (B : RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor) :
    Nonempty RealHilbertSelfAdjointSpectralResolutionConstructor := by
  exact ⟨
    ({ boundedTransform := T
       boundedBorelResolution := B } :
      RealHilbertSelfAdjointBoundedTransformBorelPipeline).toConstructor⟩

/-- Specialize the pure bounded-transform/Borel pipeline to the reconstructed
OS/Wightman model interface. -/
def RealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : RealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toConstructor.toExplicitWightmanOSConstructor

/-- The pure bounded-transform/Borel pipeline, together with the exact actual-model
measurable PVM identification certificate, yields ambient indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_boundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : RealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_realHilbertSpectralResolution
      P.toConstructor M X

/-- Together with the scalar-measure quadratic law, the same pipeline and
actual-model identification certificate yield the canonical singleton
spectral-projection law. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_boundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : RealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_realHilbertSpectralResolution
      P.toConstructor M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

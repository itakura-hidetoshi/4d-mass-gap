import MGAP4D.MathlibAnalytic.RealHilbertSelfAdjointBoundedTransformBorelPipeline
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Artanh

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The standard real bounded-transform spectral coordinate
`E ↦ E / √(1 + E²)`, expressed as `tanh (arsinh E)` so that the pinned
Mathlib inverse-hyperbolic API discharges injectivity and range. -/
def standardRealHilbertBoundedTransformSpectralCoordinate (E : ℝ) : ℝ :=
  Real.tanh (Real.arsinh E)

/-- The hyperbolic presentation is exactly the usual bounded-transform formula. -/
theorem standardRealHilbertBoundedTransformSpectralCoordinate_eq_div_sqrt
    (E : ℝ) :
    standardRealHilbertBoundedTransformSpectralCoordinate E =
      E / Real.sqrt (1 + E ^ 2) := by
  exact Real.tanh_arsinh E

/-- The standard bounded-transform coordinate is injective on the whole real line. -/
theorem standardRealHilbertBoundedTransformSpectralCoordinate_injective :
    Function.Injective standardRealHilbertBoundedTransformSpectralCoordinate := by
  exact Real.tanh_injective.comp Real.arsinh_injective

/-- Every standard bounded-transform spectral value lies in the open unit interval. -/
theorem standardRealHilbertBoundedTransformSpectralCoordinate_mem_openUnit
    (E : ℝ) :
    standardRealHilbertBoundedTransformSpectralCoordinate E ∈ Set.Ioo (-1 : ℝ) 1 := by
  exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

/-- The scalar part of the standard bounded transform is already fully discharged
by pinned Mathlib.  What remains is the bounded operator, its self-adjointness and
norm bound, eigenvector transport, and spectral-resolution pullback. -/
structure StandardRealHilbertSelfAdjointBoundedTransformBridge
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
  transfer :
    RealHilbertBoundedSelfAdjointBorelSpectralResolution boundedOperator →
      RealHilbertSelfAdjointSpectralResolution A

/-- Forget that the spectral coordinate has been fixed to the standard formula. -/
def StandardRealHilbertSelfAdjointBoundedTransformBridge.toGeneric
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (T : StandardRealHilbertSelfAdjointBoundedTransformBridge A) :
    RealHilbertSelfAdjointBoundedTransformBridge A where
  boundedOperator := T.boundedOperator
  boundedSelfAdjoint := T.boundedSelfAdjoint
  boundedOperator_norm_le_one := T.boundedOperator_norm_le_one
  spectralCoordinate := standardRealHilbertBoundedTransformSpectralCoordinate
  spectralCoordinate_injective :=
    standardRealHilbertBoundedTransformSpectralCoordinate_injective
  spectralCoordinate_mem_openUnit :=
    standardRealHilbertBoundedTransformSpectralCoordinate_mem_openUnit
  eigenvector_forward := T.eigenvector_forward
  transfer := T.transfer

/-- Uniform construction of the standard bounded transform from the
Mathlib-discharged self-adjoint core. -/
structure StandardRealHilbertSelfAdjointBoundedTransformBridgeConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        StandardRealHilbertSelfAdjointBoundedTransformBridge A

/-- A standard-coordinate constructor supplies the generic bounded-transform
constructor required by the two-certificate pipeline. -/
def StandardRealHilbertSelfAdjointBoundedTransformBridgeConstructor.toGeneric
    (T : StandardRealHilbertSelfAdjointBoundedTransformBridgeConstructor) :
    RealHilbertSelfAdjointBoundedTransformBridgeConstructor where
  construct := fun A core => (T.construct A core).toGeneric

/-- The standard bounded-transform route consists of the now-fixed standard
operator bridge and the independent bounded Borel spectral theorem. -/
structure StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransform :
    StandardRealHilbertSelfAdjointBoundedTransformBridgeConstructor
  boundedBorelResolution :
    RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor

/-- Convert the standard-coordinate pipeline to the generic pipeline. -/
def StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toGeneric
    (P : StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointBoundedTransformBorelPipeline where
  boundedTransform := P.boundedTransform.toGeneric
  boundedBorelResolution := P.boundedBorelResolution

/-- The standard-coordinate pipeline yields the full real-Hilbert spectral
resolution extension. -/
def StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExtension
    (P : StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionExtension :=
  P.toGeneric.toExtension

/-- The standard-coordinate pipeline yields the global self-adjoint spectral
resolution constructor. -/
def StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toConstructor
    (P : StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    RealHilbertSelfAdjointSpectralResolutionConstructor :=
  P.toGeneric.toConstructor

/-- The remaining standard route is sufficient for the generic spectral theorem. -/
theorem real_hilbert_selfAdjoint_spectralResolution_constructor_nonempty_of_standardBoundedTransform_and_borel
    (T : StandardRealHilbertSelfAdjointBoundedTransformBridgeConstructor)
    (B : RealHilbertBoundedSelfAdjointBorelSpectralResolutionConstructor) :
    Nonempty RealHilbertSelfAdjointSpectralResolutionConstructor := by
  exact ⟨
    ({ boundedTransform := T
       boundedBorelResolution := B } :
      StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline).toConstructor⟩

/-- Specialize the standard-coordinate pipeline to the reconstructed OS/Wightman
model interface. -/
def StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline.toExplicitWightmanOSConstructor
    (P : StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor :=
  P.toConstructor.toExplicitWightmanOSConstructor

/-- The standard-coordinate pipeline plus actual-model measurable PVM
identification yields ambient indicator evaluation. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_standardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_boundedTransformBorelPipeline
      P.toGeneric M X

/-- With the scalar-measure quadratic law, the same data yields canonical
singleton spectral-projection compatibility. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_standardBoundedTransformBorelPipeline
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : StandardRealHilbertSelfAdjointBoundedTransformBorelPipeline)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        P.toExplicitWightmanOSConstructor M)
    (Q : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel Q) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_boundedTransformBorelPipeline
      P.toGeneric M X Q hQuadratic

end

end MathlibAnalytic
end MGAP4D

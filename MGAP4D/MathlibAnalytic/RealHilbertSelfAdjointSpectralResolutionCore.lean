import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentification
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The part of the unbounded self-adjoint theory already supplied by Mathlib's
`LinearPMap` API: self-adjointness, density of the operator domain, and closedness.
The spectral PVM and Borel integral are deliberately not included here. -/
structure RealHilbertSelfAdjointCore
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  selfAdjoint : IsSelfAdjoint A
  denseDomain : Dense (A.domain : Set H)
  closed : A.IsClosed

/-- Mathlib discharges the core analytic consequences of self-adjointness for a
real Hilbert-space `LinearPMap`. -/
def realHilbertSelfAdjointCoreOfSelfAdjoint
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) (hA : IsSelfAdjoint A) :
    RealHilbertSelfAdjointCore A :=
  { selfAdjoint := hA
    denseDomain := hA.dense_domain
    closed := hA.isClosed }

/-- Pure real-Hilbert spectral-resolution data for one unbounded self-adjoint
operator.  This is independent of OS/Wightman or Yang--Mills model fields. -/
structure RealHilbertSelfAdjointSpectralResolution
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) where
  core : RealHilbertSelfAdjointCore A
  spectralPVM : OrthogonalProjectionValuedSetFunction H
  integral : (ℝ → ℝ) → H → H
  indicator_integral_eq_projection :
    ∀ (s : Set ℝ), MeasurableSet s → ∀ ψ : H,
      integral (s.indicator fun _ => (1 : ℝ)) ψ =
        spectralPVM.projection s ψ
  eigenvector_integral_evaluation :
    ∀ {E : ℝ} (x : A.domain),
      A x = E • (x : H) →
        ∀ f : ℝ → ℝ,
          integral f (x : H) = f E • (x : H)

/-- The exact remaining extension step after Mathlib has supplied density and
closedness: extend every self-adjoint core to its spectral PVM and real Borel
functional calculus. -/
structure RealHilbertSelfAdjointSpectralResolutionExtension where
  extend :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      RealHilbertSelfAdjointCore A →
        RealHilbertSelfAdjointSpectralResolution A

/-- Model-independent formulation of the unbounded real self-adjoint spectral
resolution theorem required by the OS/Wightman chain. -/
structure RealHilbertSelfAdjointSpectralResolutionConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H),
      IsSelfAdjoint A →
        RealHilbertSelfAdjointSpectralResolution A

/-- Extending the Mathlib self-adjoint core is sufficient for the generic
self-adjoint spectral-resolution constructor. -/
def RealHilbertSelfAdjointSpectralResolutionExtension.toConstructor
    (E : RealHilbertSelfAdjointSpectralResolutionExtension) :
    RealHilbertSelfAdjointSpectralResolutionConstructor where
  construct := fun A hA =>
    E.extend A (realHilbertSelfAdjointCoreOfSelfAdjoint A hA)

/-- Conversely, a generic self-adjoint spectral-resolution constructor extends
exactly the Mathlib core, using the self-adjointness proof stored in that core. -/
def RealHilbertSelfAdjointSpectralResolutionConstructor.toExtension
    (C : RealHilbertSelfAdjointSpectralResolutionConstructor) :
    RealHilbertSelfAdjointSpectralResolutionExtension where
  extend := fun A core => C.construct A core.selfAdjoint

/-- Exact existence reduction: a model-independent spectral-resolution theorem is
available if and only if every Mathlib self-adjoint core can be extended by the
missing spectral PVM and Borel integral data. -/
theorem real_hilbert_selfAdjoint_spectralResolution_constructor_nonempty_iff_extension_nonempty :
    Nonempty RealHilbertSelfAdjointSpectralResolutionConstructor ↔
      Nonempty RealHilbertSelfAdjointSpectralResolutionExtension := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.toExtension⟩
  · rintro ⟨E⟩
    exact ⟨E.toConstructor⟩

/-- Forget the pure real-Hilbert wrapper and obtain the reconstructed-model
spectral resolution when the operator is the model Hamiltonian. -/
def RealHilbertSelfAdjointSpectralResolution.toExplicitWightmanOS
    {M : ExplicitWightmanOSReconstructedModel}
    (R : RealHilbertSelfAdjointSpectralResolution M.hamiltonian) :
    ExplicitWightmanOSSelfAdjointSpectralResolution M where
  spectralPVM := R.spectralPVM
  integral := R.integral
  indicator_integral_eq_projection := R.indicator_integral_eq_projection
  eigenvector_integral_evaluation := R.eigenvector_integral_evaluation

/-- The pure Hilbert-space theorem specializes to the existing reconstructed-model
spectral-resolution constructor without adding any QFT hypothesis. -/
def RealHilbertSelfAdjointSpectralResolutionConstructor.toExplicitWightmanOSConstructor
    (C : RealHilbertSelfAdjointSpectralResolutionConstructor) :
    ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor where
  construct := fun M hSelfAdjoint =>
    (C.construct M.hamiltonian hSelfAdjoint).toExplicitWightmanOS

/-- A pure real-Hilbert spectral theorem plus the exact actual-model measurable
PVM identification certificate yields the ambient indicator-evaluation law. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_realHilbertSpectralResolution
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : RealHilbertSelfAdjointSpectralResolutionConstructor)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        C.toExplicitWightmanOSConstructor M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_measurablePVMIdentification
      M X

/-- Together with the scalar-measure quadratic law, the same pure Hilbert theorem
and actual-model identification certificate yield canonical singleton
spectral-projection compatibility. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_realHilbertSpectralResolution
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : RealHilbertSelfAdjointSpectralResolutionConstructor)
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (X :
      EuclideanYangMillsOSPhysicalMeasurableSpectralPVMIdentificationCertificate
        C.toExplicitWightmanOSConstructor M)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel P) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact
    euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_measurablePVMIdentification
      M X P hQuadratic

end

end MathlibAnalytic
end MGAP4D

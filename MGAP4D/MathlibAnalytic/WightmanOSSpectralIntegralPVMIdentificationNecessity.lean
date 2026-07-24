import MGAP4D.MathlibAnalytic.WightmanOSSelfAdjointSpectralResolutionIdentification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The intrinsic spectral-theorem PVM and the PVM stored in the reconstructed
model agree on every measurable spectral set.  This is the exact amount of PVM
identification used by the real spectral-integral interface. -/
def ExplicitWightmanOSSelfAdjointSpectralResolution.HasMeasurablePVMIdentification
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSSelfAdjointSpectralResolution M) : Prop :=
  ∀ (s : Set ℝ), MeasurableSet s → ∀ ψ : M.H,
    R.spectralPVM.projection s ψ = M.spectralPVM.projection s ψ

/-- Full equality of the intrinsic and stored PVMs implies their measurable-set
identification. -/
theorem ExplicitWightmanOSSelfAdjointSpectralResolution.hasMeasurablePVMIdentification_of_eq
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSSelfAdjointSpectralResolution M)
    (hIdent : R.spectralPVM = M.spectralPVM) :
    R.HasMeasurablePVMIdentification := by
  intro s hs ψ
  rw [hIdent]

/-- Measurable-set PVM identification is sufficient to turn an intrinsic
self-adjoint spectral resolution into the existing real spectral integral. -/
def ExplicitWightmanOSSelfAdjointSpectralResolution.toRealSpectralIntegralOfMeasurablePVMIdentification
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSSelfAdjointSpectralResolution M)
    (hIdent : R.HasMeasurablePVMIdentification) :
    ExplicitWightmanOSRealSpectralIntegral M where
  integral := R.integral
  indicator_integral_eq_projection := by
    intro s hs ψ
    calc
      R.integral (s.indicator fun _ => (1 : ℝ)) ψ =
          R.spectralPVM.projection s ψ :=
        R.indicator_integral_eq_projection s hs ψ
      _ = M.spectralPVM.projection s ψ := hIdent s hs ψ
  eigenvector_integral_evaluation := R.eigenvector_integral_evaluation

/-- Necessity: if a real spectral integral on the reconstructed model uses the
same integral as the intrinsic self-adjoint spectral resolution, then the
intrinsic and stored PVMs must agree on every measurable set. -/
theorem ExplicitWightmanOSSelfAdjointSpectralResolution.measurablePVMIdentification_of_realSpectralIntegral_same_integral
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSSelfAdjointSpectralResolution M)
    (I : ExplicitWightmanOSRealSpectralIntegral M)
    (hIntegral :
      ∀ (f : ℝ → ℝ), ∀ ψ : M.H,
        R.integral f ψ = I.integral f ψ) :
    R.HasMeasurablePVMIdentification := by
  intro s hs ψ
  calc
    R.spectralPVM.projection s ψ =
        R.integral (s.indicator fun _ => (1 : ℝ)) ψ :=
      (R.indicator_integral_eq_projection s hs ψ).symm
    _ = I.integral (s.indicator fun _ => (1 : ℝ)) ψ :=
      hIntegral _ ψ
    _ = M.spectralPVM.projection s ψ :=
      I.indicator_integral_eq_projection s hs ψ

/-- Exact characterization of the previously missing mathematical obligation:
an intrinsic self-adjoint spectral resolution descends to a real spectral
integral with the same integral if and only if its PVM agrees with the stored
model PVM on every measurable set. -/
theorem ExplicitWightmanOSSelfAdjointSpectralResolution.exists_realSpectralIntegral_same_integral_iff_measurablePVMIdentification
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSSelfAdjointSpectralResolution M) :
    (∃ I : ExplicitWightmanOSRealSpectralIntegral M,
      ∀ (f : ℝ → ℝ), ∀ ψ : M.H,
        R.integral f ψ = I.integral f ψ) ↔
      R.HasMeasurablePVMIdentification := by
  constructor
  · rintro ⟨I, hIntegral⟩
    exact R.measurablePVMIdentification_of_realSpectralIntegral_same_integral
      I hIntegral
  · intro hIdent
    refine ⟨R.toRealSpectralIntegralOfMeasurablePVMIdentification hIdent, ?_⟩
    intro f ψ
    rfl

/-- If measurable PVM identification fails, no real spectral integral compatible
with the stored model PVM can preserve the intrinsic spectral-theorem integral. -/
theorem ExplicitWightmanOSSelfAdjointSpectralResolution.no_realSpectralIntegral_same_integral_of_not_measurablePVMIdentification
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSSelfAdjointSpectralResolution M)
    (hNotIdent : ¬ R.HasMeasurablePVMIdentification) :
    ¬ ∃ I : ExplicitWightmanOSRealSpectralIntegral M,
      ∀ (f : ℝ → ℝ), ∀ ψ : M.H,
        R.integral f ψ = I.integral f ψ := by
  intro hExists
  apply hNotIdent
  exact
    R.exists_realSpectralIntegral_same_integral_iff_measurablePVMIdentification.mp
      hExists

/-- A single measurable set and vector on which the two projections disagree is
already a certificate that no common spectral integral with the intrinsic
integral can exist. -/
theorem ExplicitWightmanOSSelfAdjointSpectralResolution.no_realSpectralIntegral_same_integral_of_projection_disagreement
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSSelfAdjointSpectralResolution M)
    {s : Set ℝ} (hs : MeasurableSet s) {ψ : M.H}
    (hDisagree :
      R.spectralPVM.projection s ψ ≠ M.spectralPVM.projection s ψ) :
    ¬ ∃ I : ExplicitWightmanOSRealSpectralIntegral M,
      ∀ (f : ℝ → ℝ), ∀ x : M.H,
        R.integral f x = I.integral f x := by
  apply R.no_realSpectralIntegral_same_integral_of_not_measurablePVMIdentification
  intro hIdent
  exact hDisagree (hIdent s hs ψ)

/-- Constructor-level measurable PVM identification.  This is the precise
additional data required to descend a self-adjoint spectral-resolution
constructor to the existing spectral-integral constructor. -/
structure ExplicitWightmanOSModelMeasurableSpectralPVMIdentification
    (C : ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor) where
  identified :
    ∀ (M : ExplicitWightmanOSReconstructedModel)
      (hSelfAdjoint : IsSelfAdjoint M.hamiltonian),
      (C.construct M hSelfAdjoint).HasMeasurablePVMIdentification

/-- Measurable PVM identification is sufficient at constructor level. -/
def ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor.toSpectralIntegralConstructorOfMeasurableIdentification
    (C : ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor)
    (J : ExplicitWightmanOSModelMeasurableSpectralPVMIdentification C) :
    ExplicitWightmanOSSelfAdjointSpectralIntegralConstructor where
  construct := fun M hSelfAdjoint =>
    (C.construct M hSelfAdjoint).toRealSpectralIntegralOfMeasurablePVMIdentification
      (J.identified M hSelfAdjoint)

/-- The earlier full PVM equality obligation supplies the exact measurable
identification used by spectral integration. -/
def ExplicitWightmanOSModelSpectralPVMIdentification.toMeasurable
    {C : ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor}
    (J : ExplicitWightmanOSModelSpectralPVMIdentification C) :
    ExplicitWightmanOSModelMeasurableSpectralPVMIdentification C where
  identified := by
    intro M hSelfAdjoint
    exact
      (C.construct M hSelfAdjoint).hasMeasurablePVMIdentification_of_eq
        (J.identified M hSelfAdjoint)

/-- Constructor-level necessity: every spectral-integral constructor preserving
the intrinsic integral determines measurable identification of its generated PVM
with the PVM stored in every reconstructed model. -/
theorem explicit_wightman_os_model_measurable_spectralPVM_identification_necessary
    (C : ExplicitWightmanOSSelfAdjointSpectralResolutionConstructor)
    (K : ExplicitWightmanOSSelfAdjointSpectralIntegralConstructor)
    (hSameIntegral :
      ∀ (M : ExplicitWightmanOSReconstructedModel)
        (hSelfAdjoint : IsSelfAdjoint M.hamiltonian)
        (f : ℝ → ℝ) (ψ : M.H),
        (C.construct M hSelfAdjoint).integral f ψ =
          (K.construct M hSelfAdjoint).integral f ψ) :
    ExplicitWightmanOSModelMeasurableSpectralPVMIdentification C where
  identified := by
    intro M hSelfAdjoint
    exact
      (C.construct M hSelfAdjoint).measurablePVMIdentification_of_realSpectralIntegral_same_integral
        (K.construct M hSelfAdjoint)
        (hSameIntegral M hSelfAdjoint)

end

end MathlibAnalytic
end MGAP4D
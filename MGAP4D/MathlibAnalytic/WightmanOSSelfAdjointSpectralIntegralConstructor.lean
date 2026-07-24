import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalSpectralIntegral

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Abstract constructor supplied by an unbounded self-adjoint spectral theorem.
It assigns the real spectral integral compatible with the reconstructed PVM to
any reconstructed model whose Hamiltonian is self-adjoint. -/
structure ExplicitWightmanOSSelfAdjointSpectralIntegralConstructor where
  construct :
    ∀ (M : ExplicitWightmanOSReconstructedModel),
      IsSelfAdjoint M.hamiltonian →
        ExplicitWightmanOSRealSpectralIntegral M

/-- Apply a self-adjoint spectral-integral constructor to the actual OS physical
Hilbert reconstructed Yang--Mills model.  Its self-adjointness input is discharged
by the certificate already contained in the model. -/
def ExplicitWightmanOSSelfAdjointSpectralIntegralConstructor.constructOSPhysical
    (C : ExplicitWightmanOSSelfAdjointSpectralIntegralConstructor)
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    ExplicitWightmanOSRealSpectralIntegral M.toExplicitModel :=
  C.construct M.toExplicitModel M.toExplicitModel.hamiltonianSelfAdjoint

/-- The generic self-adjoint spectral theorem constructor also supplies the
model-specific OS physical spectral-integral package. -/
def ExplicitWightmanOSSelfAdjointSpectralIntegralConstructor.constructOSPhysicalSpecialized
    (C : ExplicitWightmanOSSelfAdjointSpectralIntegralConstructor)
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    EuclideanYangMillsOSPhysicalSpectralIntegral M where
  integral := (C.constructOSPhysical M).integral
  indicator_integral_eq_projection :=
    (C.constructOSPhysical M).indicator_integral_eq_projection
  eigenvector_integral_evaluation :=
    (C.constructOSPhysical M).eigenvector_integral_evaluation

/-- A self-adjoint spectral-integral constructor yields measurable indicator
evaluation for the actual OS physical reconstructed model. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_selfAdjointConstructor
    (C : ExplicitWightmanOSSelfAdjointSpectralIntegralConstructor)
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact explicit_wightman_os_ambient_indicator_evaluation_of_spectralIntegral
    M.toExplicitModel (C.constructOSPhysical M)

/-- Together with exact scalar-measure quadratic realization, the self-adjoint
spectral theorem constructor yields canonical singleton eigenprojection
compatibility for the actual OS physical reconstructed model. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_selfAdjointConstructor
    (C : ExplicitWightmanOSSelfAdjointSpectralIntegralConstructor)
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel P) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact explicit_wightman_os_canonical_eigenprojection_law_of_spectralIntegral
    M.toExplicitModel P hQuadratic (C.constructOSPhysical M)

end

end MathlibAnalytic
end MGAP4D

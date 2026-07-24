import MGAP4D.MathlibAnalytic.WightmanOSEigenvectorIndicatorEvaluationAnnihilation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Abstract real Borel functional calculus attached to the reconstructed
Hamiltonian and its spectral PVM.  The two compatibility fields isolate the exact
spectral-integral obligations needed by the eigenvector route. -/
structure ExplicitWightmanOSRealBorelFunctionalCalculus
    (M : ExplicitWightmanOSReconstructedModel) where
  apply : (ℝ → ℝ) → M.H → M.H
  indicator_eq_projection :
    ∀ (s : Set ℝ), MeasurableSet s → ∀ ψ : M.H,
      apply (s.indicator fun _ => (1 : ℝ)) ψ =
        M.spectralPVM.projection s ψ
  eigenvector_evaluation :
    ∀ {E : ℝ} (x : M.hamiltonian.domain),
      M.hamiltonian x = E • (x : M.H) →
        ∀ f : ℝ → ℝ,
          apply f (x : M.H) = f E • (x : M.H)

/-- A real Borel functional calculus satisfying indicator/PVM compatibility and
functional-calculus evaluation on Hamiltonian eigenvectors yields the measurable
indicator evaluation law. -/
theorem explicit_wightman_os_ambient_indicator_evaluation_of_borelFunctionalCalculus
    (M : ExplicitWightmanOSReconstructedModel)
    (F : ExplicitWightmanOSRealBorelFunctionalCalculus M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M := by
  intro E x hEigen s hs
  constructor
  · intro hMem
    rw [← F.indicator_eq_projection s hs (x : M.H),
      F.eigenvector_evaluation x hEigen]
    simp [Set.indicator_of_mem hMem]
  · intro hNotMem
    rw [← F.indicator_eq_projection s hs (x : M.H),
      F.eigenvector_evaluation x hEigen]
    simp [Set.indicator_of_not_mem hNotMem]

/-- The abstract Borel functional calculus therefore yields off-energy indicator
annihilation. -/
theorem explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_borelFunctionalCalculus
    (M : ExplicitWightmanOSReconstructedModel)
    (F : ExplicitWightmanOSRealBorelFunctionalCalculus M) :
    ExplicitWightmanOSAmbientEigenvectorOffEnergyIndicatorAnnihilationLaw M := by
  exact explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_evaluation
    M (explicit_wightman_os_ambient_indicator_evaluation_of_borelFunctionalCalculus M F)

/-- The Borel functional calculus and exact ENNReal quadratic realization imply
canonical singleton eigenprojection compatibility. -/
theorem explicit_wightman_os_canonical_eigenprojection_law_of_borelFunctionalCalculus
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (F : ExplicitWightmanOSRealBorelFunctionalCalculus M) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M := by
  exact explicit_wightman_os_canonical_eigenprojection_law_of_indicator_evaluation
    M P hQuadratic
      (explicit_wightman_os_ambient_indicator_evaluation_of_borelFunctionalCalculus M F)

end

end MathlibAnalytic
end MGAP4D

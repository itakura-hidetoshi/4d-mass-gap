import MGAP4D.MathlibAnalytic.WightmanOSEigenvectorIndicatorAnnihilationScalarVanishing

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Indicator functional-calculus evaluation on ambient Hamiltonian eigenvectors:
for an eigenvector at energy `E`, the spectral projection of a measurable set is
the vector itself when `E` belongs to the set and zero otherwise. -/
def ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw
    (M : ExplicitWightmanOSReconstructedModel) : Prop :=
  ∀ {E : ℝ} (x : M.hamiltonian.domain),
    M.hamiltonian x = E • (x : M.H) →
      ∀ (s : Set ℝ), MeasurableSet s →
        M.spectralPVM.projection s (x : M.H) =
          if E ∈ s then (x : M.H) else 0

/-- Indicator evaluation immediately gives annihilation on every measurable set
disjoint from the eigenvalue singleton. -/
theorem explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_evaluation
    (M : ExplicitWightmanOSReconstructedModel)
    (hEvaluation : ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M) :
    ExplicitWightmanOSAmbientEigenvectorOffEnergyIndicatorAnnihilationLaw M := by
  intro E x hEigen s hs hDisjoint
  have hNotMem : E ∉ s := by
    intro hMem
    exact Set.disjoint_left.1 hDisjoint hMem (by simp)
  rw [hEvaluation x hEigen s hs, if_neg hNotMem]

/-- Indicator evaluation and exact ENNReal quadratic realization imply off-energy
scalar spectral vanishing. -/
theorem explicit_wightman_os_ambient_offEnergy_scalar_vanishing_of_indicator_evaluation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hEvaluation : ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M) :
    ExplicitWightmanOSAmbientEigenvectorOffEnergyScalarVanishingLaw M P := by
  exact
    explicit_wightman_os_ambient_offEnergy_scalar_vanishing_of_indicator_annihilation
      M P hQuadratic
        (explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_evaluation
          M hEvaluation)

/-- Indicator evaluation and exact ENNReal quadratic realization imply zero scalar
spectral-measure restriction away from every eigenvalue. -/
theorem explicit_wightman_os_ambient_scalarMeasure_restriction_of_indicator_evaluation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hEvaluation : ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M) :
    ExplicitWightmanOSAmbientEigenvectorScalarMeasureRestrictionLaw M P := by
  exact
    explicit_wightman_os_ambient_scalarMeasure_restriction_of_indicator_annihilation
      M P hQuadratic
        (explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_evaluation
          M hEvaluation)

/-- Indicator evaluation and exact ENNReal quadratic realization imply ambient
complement annihilation. -/
theorem explicit_wightman_os_ambient_complement_annihilation_of_indicator_evaluation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hEvaluation : ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M) :
    ExplicitWightmanOSAmbientEigenvectorComplementAnnihilationLaw M := by
  exact
    explicit_wightman_os_ambient_complement_annihilation_of_indicator_annihilation
      M P hQuadratic
        (explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_evaluation
          M hEvaluation)

/-- Indicator evaluation and exact ENNReal quadratic realization imply the ambient
singleton eigenprojection law. -/
theorem explicit_wightman_os_ambient_eigenprojection_law_of_indicator_evaluation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hEvaluation : ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M) :
    ExplicitWightmanOSAmbientEigenprojectionLaw M := by
  exact
    explicit_wightman_os_ambient_eigenprojection_law_of_indicator_annihilation
      M P hQuadratic
        (explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_evaluation
          M hEvaluation)

/-- Indicator evaluation and exact ENNReal quadratic realization also imply the
canonical vacuum-orthogonal singleton eigenprojection law. -/
theorem explicit_wightman_os_canonical_eigenprojection_law_of_indicator_evaluation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hEvaluation : ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M := by
  exact
    explicit_wightman_os_canonical_eigenprojection_law_of_indicator_annihilation
      M P hQuadratic
        (explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_evaluation
          M hEvaluation)

end

end MathlibAnalytic
end MGAP4D

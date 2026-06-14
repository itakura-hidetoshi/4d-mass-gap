import MGAP4D.MathlibAnalytic.EuclideanYangMillsSpectralMeasureLaplaceRepresentation

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A coherent scalar spectral-measure realization of the reconstructed
Hamiltonian PVM.

For every Hilbert vector `ψ`, `scalarMeasure ψ` is a genuine countably additive
Mathlib measure on the energy line.  Its singleton masses agree with the squared
norms of the corresponding PVM projections. -/
structure ExplicitWightmanOSScalarSpectralMeasureRealization
    (M : ExplicitWightmanOSReconstructedModel) where
  scalarMeasure : M.H → Measure ℝ
  singletonMass_eq_squaredProjectionNorm :
    ∀ (ψ : M.H) (E : ℝ),
      (scalarMeasure ψ).real ({E} : Set ℝ) =
        ‖M.spectralPVM.projection ({E} : Set ℝ) ψ‖ ^ 2

/-- A singleton PVM projection is nonzero exactly when the corresponding scalar
spectral measure has positive real mass at that energy. -/
theorem scalar_spectral_measure_singleton_mass_pos_of_projection_ne_zero
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (ψ : M.H) (E : ℝ)
    (hProjection : M.spectralPVM.projection ({E} : Set ℝ) ψ ≠ 0) :
    0 < (R.scalarMeasure ψ).real ({E} : Set ℝ) := by
  rw [R.singletonMass_eq_squaredProjectionNorm ψ E]
  exact sq_pos_of_pos (norm_pos_iff.mpr hProjection)

/-- OS reconstruction identifies each Euclidean connected correlation with the
Laplace transform of the scalar Hamiltonian spectral measure of its source
vector.  This is the remaining semigroup/spectral-theorem identification after
the countably additive scalar measures themselves have been constructed. -/
structure EuclideanYangMillsOSLaplaceSemigroupIdentification
    (C : EuclideanYangMillsConnectedObservableCore)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization C.explicitModel) where
  laplaceIntegrable :
    ∀ e : C.explicitModel.NonVacuumEnergy,
      ∀ t : ℝ,
        0 ≤ t →
          Integrable
            (fun λ : ℝ => Real.exp (-λ * t))
            (R.scalarMeasure (C.sourceVector e))
  correlation_eq_laplaceIntegral :
    ∀ e : C.explicitModel.NonVacuumEnergy,
      ∀ t : ℝ,
        0 ≤ t →
          C.connectedCorrelation e t =
            ∫ λ : ℝ, Real.exp (-λ * t)
              ∂R.scalarMeasure (C.sourceVector e)

/-- The coherent vector-indexed scalar spectral measure and the OS semigroup
identification induce the positive per-observable spectral-measure package. -/
def EuclideanYangMillsOSLaplaceSemigroupIdentification.toPositiveSpectralMeasure
    {C : EuclideanYangMillsConnectedObservableCore}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization C.explicitModel}
    (L : EuclideanYangMillsOSLaplaceSemigroupIdentification C R) :
    EuclideanYangMillsPositiveSpectralMeasureRepresentation C :=
  { spectralMeasure := fun e => R.scalarMeasure (C.sourceVector e)
    laplaceIntegrable := L.laplaceIntegrable
    correlation_eq_laplaceIntegral := L.correlation_eq_laplaceIntegral
    singletonMass_eq_squaredProjectionNorm := by
      intro e
      exact R.singletonMass_eq_squaredProjectionNorm
        (C.sourceVector e) (e : ℝ) }

/-- The coherent scalar spectral realization automatically discharges the
previous OS Laplace lower-bound certificate once the semigroup identification is
known. -/
def EuclideanYangMillsOSLaplaceSemigroupIdentification.toOSSpectralLaplace
    {C : EuclideanYangMillsConnectedObservableCore}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization C.explicitModel}
    (L : EuclideanYangMillsOSLaplaceSemigroupIdentification C R) :
    EuclideanYangMillsOSSpectralLaplaceRepresentation C :=
  L.toPositiveSpectralMeasure.toOSSpectralLaplace

/-- End-to-end Hamiltonian gap from a coherent scalar spectral measure,
OS semigroup identification, and exponential clustering. -/
theorem euclidean_scalar_spectral_measure_semigroup_clustering_mass_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization C.explicitModel)
    (L : EuclideanYangMillsOSLaplaceSemigroupIdentification C R)
    (X : EuclideanYangMillsExponentialClusteringEstimate C) :
    HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  exact euclidean_connected_correlation_analytic_inputs_hasHamiltonianMassGap
    C L.toOSSpectralLaplace X

/-- Exact physical vacuum-sector gap from the coherent scalar spectral measure,
OS semigroup identification, exponential clustering, and threshold attainment. -/
theorem euclidean_scalar_spectral_measure_semigroup_clustering_exact_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization C.explicitModel)
    (L : EuclideanYangMillsOSLaplaceSemigroupIdentification C R)
    (X : EuclideanYangMillsExponentialClusteringEstimate C)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
        ((C.assemble L.toOSSpectralLaplace X).exactEnergy
          hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
          ((C.assemble L.toOSSpectralLaplace X).exactEnergy
            hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  exact euclidean_connected_correlation_analytic_inputs_exact_gap
    C L.toOSSpectralLaplace X hExactSpectrum

end

end MathlibAnalytic
end MGAP4D

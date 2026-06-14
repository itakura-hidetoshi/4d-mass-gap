import MGAP4D.MathlibAnalytic.WightmanOSScalarSpectralMeasureRealization

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Countably additive scalar-measure upgrade of the reconstructed bounded
projection family.

For every Hilbert vector `ψ`, the quadratic projection weights
`‖P(S) ψ‖²` on measurable energy sets are represented by a genuine Mathlib
measure.  Since `Measure ℝ` is countably additive by construction, this packages
the precise measure-theoretic strengthening missing from the original finite
set-function interface. -/
structure ExplicitWightmanOSCountablyAdditivePVMScalarMeasure
    (M : ExplicitWightmanOSReconstructedModel) where
  scalarMeasure : M.H → Measure ℝ
  scalarMeasure_real_eq_projectionNormSq :
    ∀ (ψ : M.H) (s : Set ℝ), MeasurableSet s →
      (scalarMeasure ψ).real s =
        ‖M.spectralPVM.projection s ψ‖ ^ 2

/-- The measurable-set identity specializes to singleton spectral atoms. -/
theorem countably_additive_pvm_scalarMeasure_singleton
    {M : ExplicitWightmanOSReconstructedModel}
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (ψ : M.H) (E : ℝ) :
    (P.scalarMeasure ψ).real ({E} : Set ℝ) =
      ‖M.spectralPVM.projection ({E} : Set ℝ) ψ‖ ^ 2 := by
  exact P.scalarMeasure_real_eq_projectionNormSq
    ψ ({E} : Set ℝ) (MeasurableSet.singleton E)

/-- The countably additive scalar-measure upgrade induces the coherent spectral
measure realization used by the OS Laplace route. -/
def ExplicitWightmanOSCountablyAdditivePVMScalarMeasure.toScalarSpectralRealization
    {M : ExplicitWightmanOSReconstructedModel}
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M) :
    ExplicitWightmanOSScalarSpectralMeasureRealization M :=
  { scalarMeasure := P.scalarMeasure
    singletonMass_eq_squaredProjectionNorm := by
      intro ψ E
      exact countably_additive_pvm_scalarMeasure_singleton P ψ E }

/-- Zero projection on a measurable set forces zero scalar spectral mass. -/
theorem countably_additive_pvm_scalarMeasure_zero_of_projection_zero
    {M : ExplicitWightmanOSReconstructedModel}
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (ψ : M.H) (s : Set ℝ) (hs : MeasurableSet s)
    (hProjection : M.spectralPVM.projection s ψ = 0) :
    (P.scalarMeasure ψ).real s = 0 := by
  rw [P.scalarMeasure_real_eq_projectionNormSq ψ s hs, hProjection]
  simp

/-- A nonzero projected vector on a measurable set gives strictly positive scalar
spectral mass. -/
theorem countably_additive_pvm_scalarMeasure_pos_of_projection_ne_zero
    {M : ExplicitWightmanOSReconstructedModel}
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (ψ : M.H) (s : Set ℝ) (hs : MeasurableSet s)
    (hProjection : M.spectralPVM.projection s ψ ≠ 0) :
    0 < (P.scalarMeasure ψ).real s := by
  rw [P.scalarMeasure_real_eq_projectionNormSq ψ s hs]
  exact sq_pos_of_pos (norm_pos_iff.mpr hProjection)

/-- End-to-end Hamiltonian gap from the countably additive scalar PVM upgrade,
OS semigroup/Laplace identification, and Euclidean exponential clustering. -/
theorem euclidean_countably_additive_pvm_semigroup_clustering_mass_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure C.explicitModel)
    (L : EuclideanYangMillsOSLaplaceSemigroupIdentification
      C P.toScalarSpectralRealization)
    (X : EuclideanYangMillsExponentialClusteringEstimate C) :
    HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  exact euclidean_scalar_spectral_measure_semigroup_clustering_mass_gap
    C P.toScalarSpectralRealization L X

/-- Exact physical gap under the same countably additive PVM and Euclidean
analytic inputs, together with spectral attainment of the threshold. -/
theorem euclidean_countably_additive_pvm_semigroup_clustering_exact_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure C.explicitModel)
    (L : EuclideanYangMillsOSLaplaceSemigroupIdentification
      C P.toScalarSpectralRealization)
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
  exact euclidean_scalar_spectral_measure_semigroup_clustering_exact_gap
    C P.toScalarSpectralRealization L X hExactSpectrum

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.WightmanOSScalarToOSSpectralLaplace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Compatibility aggregation for the scalar spectral-measure OS/Laplace route.

The carrier, singleton positivity theorem, semigroup identification, and
conversion maps now live in the split modules imported above.  This file retains
the two public gap endpoints used by downstream countably-additive PVM modules.
-/

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

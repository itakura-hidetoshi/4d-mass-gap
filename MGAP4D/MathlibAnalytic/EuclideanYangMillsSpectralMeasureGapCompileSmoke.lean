import MGAP4D.MathlibAnalytic.EuclideanYangMillsSpectralMeasureLaplaceRepresentation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile-level exposure of strict positivity of the selected singleton
spectral mass. -/
theorem euclidean_yang_mills_positive_spectral_measure_singleton_mass_compile_smoke
    {C : EuclideanYangMillsConnectedObservableCore}
    (S : EuclideanYangMillsPositiveSpectralMeasureRepresentation C)
    (e : C.explicitModel.NonVacuumEnergy) :
    0 < (S.spectralMeasure e).real ({(e : ℝ)} : Set ℝ) := by
  exact positive_spectral_measure_singleton_mass_pos S e

/-- Compile-level exposure of the Hamiltonian mass-gap route obtained from a
positive scalar spectral measure and exponential clustering. -/
theorem euclidean_yang_mills_spectral_measure_mass_gap_compile_smoke
    (C : EuclideanYangMillsConnectedObservableCore)
    (S : EuclideanYangMillsPositiveSpectralMeasureRepresentation C)
    (X : EuclideanYangMillsExponentialClusteringEstimate C) :
    HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  exact euclidean_spectral_measure_and_clustering_hasHamiltonianMassGap C S X

/-- Compile-level exposure of the exact physical gap once the threshold belongs
to the Hamiltonian energy spectrum. -/
theorem euclidean_yang_mills_spectral_measure_exact_gap_compile_smoke
    (C : EuclideanYangMillsConnectedObservableCore)
    (S : EuclideanYangMillsPositiveSpectralMeasureRepresentation C)
    (X : EuclideanYangMillsExponentialClusteringEstimate C)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      ((C.assemble S.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
        ((C.assemble S.toOSSpectralLaplace X).exactEnergy
          hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        ((C.assemble S.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
          ((C.assemble S.toOSSpectralLaplace X).exactEnergy
            hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  exact euclidean_spectral_measure_and_clustering_exact_gap
    C S X hExactSpectrum

end

end MathlibAnalytic
end MGAP4D

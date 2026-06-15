import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapClusterRate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapClusterData W)

/-- Compile gate for the exact-gap geometric adapter. -/
noncomputable def finite_wilson_exact_gap_cluster_data_compile_smoke :
    FiniteWilsonOSAutomaticUniformGeometricClusterData W :=
  D.toUniformGeometricClusterData

/-- Compile gate for continuum clustering at the exact-gap rate. -/
theorem finite_wilson_exact_gap_cluster_compile_smoke :
    D.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.
      ContinuumClusterProperty :=
  finite_wilson_exact_gap_cluster_passes_to_limit D

/-- Compile gate for the inherited exact-gap continuum bound. -/
theorem finite_wilson_exact_gap_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_cluster_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D

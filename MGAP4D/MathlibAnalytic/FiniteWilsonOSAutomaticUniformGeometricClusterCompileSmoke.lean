import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticUniformGeometricCluster

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticUniformGeometricClusterData W)

/-- Compile gate for automatic construction of the general cluster package. -/
noncomputable def finite_wilson_uniform_geometric_cluster_data_compile_smoke :
    FiniteWilsonOSAutomaticClusterLimitData W :=
  D.toClusterLimitData

/-- Compile gate for continuum clustering. -/
theorem finite_wilson_uniform_geometric_cluster_compile_smoke :
    D.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_uniform_geometric_cluster_passes_to_limit D

/-- Compile gate for the inherited continuum geometric bound. -/
theorem finite_wilson_uniform_geometric_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * D.contractionRatio ^ r :=
  finite_wilson_uniform_geometric_cluster_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D

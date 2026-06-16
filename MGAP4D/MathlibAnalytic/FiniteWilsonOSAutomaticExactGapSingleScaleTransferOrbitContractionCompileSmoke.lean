import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapSingleScaleTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapSingleScaleTransferOrbitContractionData W)

noncomputable def finite_wilson_single_scale_transfer_orbit_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W :=
  D.toConstructedTransferOrbitData

theorem finite_wilson_single_scale_pointwise_compile_smoke
    (O : D.Observable) (r : ℕ) :
    Tendsto
      (fun _ : ℕ =>
        (W.system D.sourceScale).gibbsConnectedCorrelation
          (D.leftObservable O) (D.rightObservable O r))
      atTop (nhds (D.continuumConnectedCorrelation O r)) :=
  finite_wilson_single_scale_pointwise_convergence D O r

theorem finite_wilson_single_scale_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_single_scale_continuum_bound D O r

theorem finite_wilson_single_scale_cluster_compile_smoke :
    D.toConstructedTransferOrbitData.toConstructedHamiltonianTransferData.toHamiltonianEigenactionData.toFiniteDimensionalHamiltonianData.toOrthonormalEigenbasisData.toFiniteSpectralData.toPositiveRayleighData.toSymmetricRayleighData.toHilbertMatrixData.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_single_scale_passes_to_limit D

end

end MathlibAnalytic
end MGAP4D

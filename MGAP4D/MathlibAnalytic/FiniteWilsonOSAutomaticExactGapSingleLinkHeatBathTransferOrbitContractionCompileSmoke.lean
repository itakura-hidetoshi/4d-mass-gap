import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapSingleLinkHeatBathTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapSingleLinkHeatBathTransferOrbitContractionData W)

noncomputable def finite_wilson_single_link_heat_bath_transfer_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData W :=
  D.toVacuumPoincareData

theorem finite_wilson_single_link_heat_bath_finite_bound_compile_smoke
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.bridgeData.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_single_link_heat_bath D n O r

theorem finite_wilson_single_link_heat_bath_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_single_link_heat_bath_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D

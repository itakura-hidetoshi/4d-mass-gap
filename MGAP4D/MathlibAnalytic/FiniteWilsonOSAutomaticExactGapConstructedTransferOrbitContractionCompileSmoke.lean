import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)

noncomputable def finite_wilson_constructed_transfer_orbit_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapConstructedHamiltonianTransferContractionData W :=
  D.toConstructedHamiltonianTransferData

theorem finite_wilson_constructed_transfer_orbit_succ_compile_smoke
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    D.correlationState n O (Nat.succ r) =
      D.transferOperator n (D.correlationState n O r) :=
  finite_wilson_constructed_transfer_orbit_succ D n O r

theorem finite_wilson_constructed_transfer_orbit_bound_compile_smoke
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_constructed_transfer_orbit D n O r

theorem finite_wilson_constructed_transfer_orbit_continuum_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_constructed_transfer_orbit_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D

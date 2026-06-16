import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapTransferOperator

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapTransferOperatorData W)

/-- Compile gate for the state-space geometric norm bound. -/
theorem finite_wilson_exact_gap_transfer_state_compile_smoke
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖D.correlationState n O r‖ ≤
      exactGapClusterContractionRatio ^ r * ‖D.correlationState n O 0‖ :=
  finite_wilson_exact_gap_transfer_state_norm_bound D n O r

/-- Compile gate for the generated finite Wilson correlation bound. -/
theorem finite_wilson_exact_gap_transfer_bound_compile_smoke
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_transfer_operator D n O r

/-- Compile gate for continuum clustering from operator-norm contraction. -/
theorem finite_wilson_exact_gap_transfer_cluster_compile_smoke :
    D.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_transfer_operator_passes_to_limit D

end

end MathlibAnalytic
end MGAP4D

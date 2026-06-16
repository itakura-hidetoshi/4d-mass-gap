import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapStepContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapStepContractionData W)

/-- Compile gate for the inductively generated all-distance bound. -/
theorem finite_wilson_exact_gap_step_bound_compile_smoke
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_step_contraction D n O r

/-- Compile gate for the exact-gap cluster adapter. -/
noncomputable def finite_wilson_exact_gap_step_adapter_compile_smoke :
    FiniteWilsonOSAutomaticExactGapClusterData W :=
  D.toExactGapClusterData

/-- Compile gate for continuum clustering from one-step contraction. -/
theorem finite_wilson_exact_gap_step_cluster_compile_smoke :
    D.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_step_contraction_passes_to_limit D

end

end MathlibAnalytic
end MGAP4D

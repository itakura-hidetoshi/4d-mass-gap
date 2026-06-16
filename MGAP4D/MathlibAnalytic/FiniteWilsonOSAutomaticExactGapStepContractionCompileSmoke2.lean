import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapStepContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapStepContractionData W)

/-- Compile gate for the inherited continuum exact-gap estimate. -/
theorem finite_wilson_exact_gap_step_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_step_contraction_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D

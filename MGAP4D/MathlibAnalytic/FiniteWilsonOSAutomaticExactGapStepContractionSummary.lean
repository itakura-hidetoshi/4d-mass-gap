import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapStepContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Public summary: one initial estimate plus one-step exact-gap contraction generates
all-distance finite-volume decay and continuum clustering. -/
theorem finite_wilson_exact_gap_step_contraction_summary
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapStepContractionData W) :
    D.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_step_contraction_passes_to_limit D

end

end MathlibAnalytic
end MGAP4D

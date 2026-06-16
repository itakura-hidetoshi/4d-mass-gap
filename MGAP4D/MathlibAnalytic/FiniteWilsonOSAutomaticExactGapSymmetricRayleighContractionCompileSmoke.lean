import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapSymmetricRayleighContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W)

/-- Compile gate for the global Rayleigh bound generated from unit vectors. -/
theorem finite_wilson_symmetric_rayleigh_global_bound_compile_smoke
    (n : ℕ) (x : D.StateSpace) :
    |(D.transferOperator n).rayleighQuotient x| ≤
      exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_rayleigh_abs_bound D n x

/-- Compile gate for the operator norm bound. -/
theorem finite_wilson_symmetric_rayleigh_operator_norm_compile_smoke
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_symmetric_rayleigh D n

/-- Compile gate for the generated transfer-operator package. -/
noncomputable def finite_wilson_symmetric_rayleigh_transfer_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapTransferOperatorData W :=
  D.toTransferOperatorData

/-- Compile gate for continuum clustering. -/
theorem finite_wilson_symmetric_rayleigh_cluster_compile_smoke :
    D.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_symmetric_rayleigh_passes_to_limit D

end

end MathlibAnalytic
end MGAP4D

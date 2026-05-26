import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2TailIteSubPrefixTarget

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

theorem concrete_l2_prefix_deficit_comparison_of_tail_ite_sub_prefix_target
    (h : concreteL2TargetTailIteTsumLeSubPrefixTarget) :
    concreteL2RawTruncationGraphErrorEnergyLeTargetPrefixDeficit := by
  intro x N
  rw [concrete_l2_completed_truncation_error_energy_eq_tail_ite_tsum x N]
  exact h x N

theorem concrete_l2_energy_epsilon_of_tail_ite_sub_prefix_target
    (h : concreteL2TargetTailIteTsumLeSubPrefixTarget) :
    concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget := by
  exact concrete_l2_raw_truncation_energy_epsilon_of_error_le_prefix_deficit
    (concrete_l2_prefix_deficit_comparison_of_tail_ite_sub_prefix_target h)

theorem concrete_l2_precise_density_of_tail_ite_sub_prefix_target
    (h : concreteL2TargetTailIteTsumLeSubPrefixTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_graph_norm_precise_density_target_of_energy_epsilon
    (concrete_l2_energy_epsilon_of_tail_ite_sub_prefix_target h)

end

end MathlibAnalytic
end MGAP4D

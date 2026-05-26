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

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2SubPrefixClosureChain

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

def concreteL2PrefixPlusTailLeCompletedTarget : Prop :=
  forall x : ConcreteL2DiagonalDomainCarrier,
  forall N : Nat,
    Finset.sum (Finset.range N)
        (fun n : Nat =>
          concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n) +
      tsum (fun n : Nat => concreteL2TargetGraphEnergyTailIte x N n) <=
        concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x)

theorem concrete_l2_sub_prefix_target_of_prefix_plus_tail
    (h : concreteL2PrefixPlusTailLeCompletedTarget) :
    concreteL2TargetTailIteTsumLeSubPrefixTarget := by
  intro x N
  have hx := h x N
  linarith

theorem concrete_l2_precise_density_of_prefix_plus_tail
    (h : concreteL2PrefixPlusTailLeCompletedTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_precise_density_of_tail_ite_sub_prefix_target
    (concrete_l2_sub_prefix_target_of_prefix_plus_tail h)

end

end MathlibAnalytic
end MGAP4D

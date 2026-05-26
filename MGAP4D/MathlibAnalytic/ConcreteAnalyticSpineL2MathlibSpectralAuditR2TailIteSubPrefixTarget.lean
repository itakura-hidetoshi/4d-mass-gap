import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2TailIteTsumLeCompleted

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

def concreteL2TargetTailIteTsumLeSubPrefixTarget : Prop :=
  forall x : ConcreteL2DiagonalDomainCarrier,
  forall N : Nat,
    tsum (fun n : Nat => concreteL2TargetGraphEnergyTailIte x N n) <=
      concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x) -
        Finset.sum (Finset.range N)
          (fun n : Nat =>
            concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n)

def concreteAnalyticSpineL2MathlibSpectralAuditR2TailIteSubPrefixTargetSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2TailIteTsumLeCompletedSurfaceReady

theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_ite_sub_prefix_target_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TailIteSubPrefixTargetSurfaceReady := by
  exact concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_ite_tsum_le_completed_surface_ready

end

end MathlibAnalytic
end MGAP4D

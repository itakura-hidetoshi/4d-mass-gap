import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteSupportCore
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityClosedSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

structure ConcreteL2R2GraphNormFiniteSupportDensitySurface where
  finiteSupportCoreReady : concreteL2R2FiniteSupportCoreReady
  inheritedGraphNormDensityClosedSurfaceReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityClosedSurfaceReady
  preciseGraphNormFiniteSupportDensityClosed :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityClosed
  closedDensityPacket :
    concreteL2MathlibSpectralAuditR2GraphNormDensityClosedPacket
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotEssentialSelfAdjointness : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotExactAtomThirtyThreeTwentieth : Prop
  boundaryNotPositiveSpectralWeight : Prop
  boundaryNotPhysicalYangMillsHamiltonian : Prop

def concreteL2R2GraphNormFiniteSupportDensitySurface :
    ConcreteL2R2GraphNormFiniteSupportDensitySurface :=
  { finiteSupportCoreReady :=
      concrete_analytic_spine_l2_r2_finite_support_core_ready
    inheritedGraphNormDensityClosedSurfaceReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_closed_surface_ready
    preciseGraphNormFiniteSupportDensityClosed :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_density_closed
    closedDensityPacket :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_closed_packet_ready
    boundaryNotClosedOperatorTheorem := True
    boundaryNotEssentialSelfAdjointness := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotExactAtomThirtyThreeTwentieth := True
    boundaryNotPositiveSpectralWeight := True
    boundaryNotPhysicalYangMillsHamiltonian := True }

def concreteL2R2GraphNormFiniteSupportDensityReady : Prop :=
  concreteL2R2FiniteSupportCoreReady ∧
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityClosedSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityClosed ∧
  concreteL2MathlibSpectralAuditR2GraphNormDensityClosedPacket ∧
  True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True

theorem concrete_analytic_spine_l2_r2_graph_norm_finite_support_density_ready :
    concreteL2R2GraphNormFiniteSupportDensityReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_finite_support_core_ready,
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_closed_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_density_closed,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_closed_packet_ready,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D

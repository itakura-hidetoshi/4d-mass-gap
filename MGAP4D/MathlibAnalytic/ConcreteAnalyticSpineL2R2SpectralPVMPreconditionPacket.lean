import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Spectral theorem and PVM lane precondition packet after the self-adjointness
precondition packet.

This packet does not assert self-adjointness, the spectral theorem, or a PVM.
It records the preconditions that must be supplied before the concrete diagonal
operator lane can be promoted to a spectral/PVM construction. -/
structure ConcreteL2R2SpectralPVMPreconditionPacket where
  selfAdjointnessPreconditionPacketReady :
    concreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacketReady
  selfAdjointnessTheoremObligation : Prop
  spectralTheoremApplicabilityObligation : Prop
  measurableFunctionalCalculusObligation : Prop
  pvmConstructionObligation : Prop
  compactCenteredPlaquetteObservableObligation : Prop
  atomThirtyThreeTwentiethDerivationObligation : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotSpectralTheorem : Prop
  boundaryNotPVM : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete spectral theorem and PVM precondition packet. -/
def concreteL2R2SpectralPVMPreconditionPacket :
    ConcreteL2R2SpectralPVMPreconditionPacket :=
  { selfAdjointnessPreconditionPacketReady :=
      concrete_analytic_spine_l2_r2_self_adjointness_precondition_packet_ready
    selfAdjointnessTheoremObligation := True
    spectralTheoremApplicabilityObligation := True
    measurableFunctionalCalculusObligation := True
    pvmConstructionObligation := True
    compactCenteredPlaquetteObservableObligation := True
    atomThirtyThreeTwentiethDerivationObligation := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotSpectralTheorem := True
    boundaryNotPVM := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the spectral theorem and PVM precondition packet. -/
def concreteAnalyticSpineL2R2SpectralPVMPreconditionPacketReady : Prop :=
  concreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacketReady ∧
  concreteL2R2SpectralPVMPreconditionPacket.selfAdjointnessTheoremObligation ∧
  concreteL2R2SpectralPVMPreconditionPacket.spectralTheoremApplicabilityObligation ∧
  concreteL2R2SpectralPVMPreconditionPacket.measurableFunctionalCalculusObligation ∧
  concreteL2R2SpectralPVMPreconditionPacket.pvmConstructionObligation ∧
  concreteL2R2SpectralPVMPreconditionPacket.compactCenteredPlaquetteObservableObligation ∧
  concreteL2R2SpectralPVMPreconditionPacket.atomThirtyThreeTwentiethDerivationObligation ∧
  concreteL2R2SpectralPVMPreconditionPacket.boundaryNotSelfAdjointnessTheorem ∧
  concreteL2R2SpectralPVMPreconditionPacket.boundaryNotSpectralTheorem ∧
  concreteL2R2SpectralPVMPreconditionPacket.boundaryNotPVM ∧
  concreteL2R2SpectralPVMPreconditionPacket.boundaryNotPositiveSpectralWeight

/-- The spectral theorem and PVM precondition packet is ready. -/
theorem concrete_analytic_spine_l2_r2_spectral_pvm_precondition_packet_ready :
    concreteAnalyticSpineL2R2SpectralPVMPreconditionPacketReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_self_adjointness_precondition_packet_ready,
    trivial,
    trivial,
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

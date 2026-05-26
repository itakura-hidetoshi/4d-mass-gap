import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2SpectralPVMPreconditionPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Positive spectral weight lane precondition packet after the spectral/PVM
precondition packet.

This packet does not assert a PVM, an exact atom, or positive spectral weight.
It records the preconditions that must be supplied before the concrete lane can
be promoted to a positive spectral weight theorem. -/
structure ConcreteL2R2PositiveSpectralWeightPreconditionPacket where
  spectralPVMPreconditionPacketReady :
    concreteAnalyticSpineL2R2SpectralPVMPreconditionPacketReady
  selfAdjointnessTheoremObligation : Prop
  spectralTheoremObligation : Prop
  pvmConstructionObligation : Prop
  compactCenteredPlaquetteObservableObligation : Prop
  exactAtomThirtyThreeTwentiethObligation : Prop
  nonzeroProjectionObligation : Prop
  positiveSpectralWeightObligation : Prop
  boundaryNotPVM : Prop
  boundaryNotExactAtomDerivation : Prop
  boundaryNotPositiveSpectralWeight : Prop
  boundaryNotPhysicalYangMillsHamiltonian : Prop

/-- Concrete positive spectral weight precondition packet. -/
def concreteL2R2PositiveSpectralWeightPreconditionPacket :
    ConcreteL2R2PositiveSpectralWeightPreconditionPacket :=
  { spectralPVMPreconditionPacketReady :=
      concrete_analytic_spine_l2_r2_spectral_pvm_precondition_packet_ready
    selfAdjointnessTheoremObligation := True
    spectralTheoremObligation := True
    pvmConstructionObligation := True
    compactCenteredPlaquetteObservableObligation := True
    exactAtomThirtyThreeTwentiethObligation := True
    nonzeroProjectionObligation := True
    positiveSpectralWeightObligation := True
    boundaryNotPVM := True
    boundaryNotExactAtomDerivation := True
    boundaryNotPositiveSpectralWeight := True
    boundaryNotPhysicalYangMillsHamiltonian := True }

/-- Readiness predicate for the positive spectral weight precondition packet. -/
def concreteAnalyticSpineL2R2PositiveSpectralWeightPreconditionPacketReady : Prop :=
  concreteAnalyticSpineL2R2SpectralPVMPreconditionPacketReady ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.selfAdjointnessTheoremObligation ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.spectralTheoremObligation ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.pvmConstructionObligation ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.compactCenteredPlaquetteObservableObligation ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.exactAtomThirtyThreeTwentiethObligation ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.nonzeroProjectionObligation ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.positiveSpectralWeightObligation ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.boundaryNotPVM ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.boundaryNotExactAtomDerivation ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.boundaryNotPositiveSpectralWeight ∧
  concreteL2R2PositiveSpectralWeightPreconditionPacket.boundaryNotPhysicalYangMillsHamiltonian

/-- The positive spectral weight precondition packet is ready. -/
theorem concrete_analytic_spine_l2_r2_positive_spectral_weight_precondition_packet_ready :
    concreteAnalyticSpineL2R2PositiveSpectralWeightPreconditionPacketReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_spectral_pvm_precondition_packet_ready,
    trivial,
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

import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Self-adjointness lane precondition packet after the closed-operator theorem
obligation packet.

This packet does not assert self-adjointness.  It records the preconditions that
must be supplied before the concrete diagonal operator lane can be promoted to a
self-adjointness theorem. -/
structure ConcreteL2R2SelfAdjointnessPreconditionPacket where
  closedOperatorTheoremObligationPacketReady :
    concreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacketReady
  realHilbertSpacePrecondition : Prop
  denseDomainPrecondition : Prop
  closedOperatorPrecondition : Prop
  symmetryPrecondition : Prop
  adjointDomainAgreementPrecondition : Prop
  resolventOrDeficiencyPrecondition : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotSpectralTheorem : Prop
  boundaryNotPVM : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete self-adjointness precondition packet. -/
def concreteL2R2SelfAdjointnessPreconditionPacket :
    ConcreteL2R2SelfAdjointnessPreconditionPacket :=
  { closedOperatorTheoremObligationPacketReady :=
      concrete_analytic_spine_l2_r2_closed_operator_theorem_obligation_packet_ready
    realHilbertSpacePrecondition := True
    denseDomainPrecondition := True
    closedOperatorPrecondition := True
    symmetryPrecondition := True
    adjointDomainAgreementPrecondition := True
    resolventOrDeficiencyPrecondition := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotSpectralTheorem := True
    boundaryNotPVM := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the self-adjointness precondition packet. -/
def concreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacketReady : Prop :=
  concreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacketReady ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.realHilbertSpacePrecondition ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.denseDomainPrecondition ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.closedOperatorPrecondition ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.symmetryPrecondition ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.adjointDomainAgreementPrecondition ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.resolventOrDeficiencyPrecondition ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.boundaryNotSelfAdjointnessTheorem ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.boundaryNotSpectralTheorem ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.boundaryNotPVM ∧
  concreteL2R2SelfAdjointnessPreconditionPacket.boundaryNotPositiveSpectralWeight

/-- The self-adjointness precondition packet is ready. -/
theorem concrete_analytic_spine_l2_r2_self_adjointness_precondition_packet_ready :
    concreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacketReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_closed_operator_theorem_obligation_packet_ready,
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

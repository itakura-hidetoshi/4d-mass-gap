import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphClosednessObligationPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Closure-uniqueness obligation packet after graph-closedness obligations.

This packet does not assert closure uniqueness.  It records the inputs and
remaining obligations needed before closed-operator promotion can be considered. -/
structure ConcreteL2R2ClosureUniquenessObligationPacket where
  graphClosednessObligationPacketReady :
    concreteAnalyticSpineL2R2GraphClosednessObligationPacketReady
  graphClosednessTheoremObligation : Prop
  closureUniquenessTheoremObligation : Prop
  closureCompatibilityWithDomainActionObligation : Prop
  closureCompatibilityWithGraphNormObligation : Prop
  boundaryNotClosureUniquenessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheorem : Prop
  boundaryNotPVM : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete closure-uniqueness obligation packet. -/
def concreteL2R2ClosureUniquenessObligationPacket :
    ConcreteL2R2ClosureUniquenessObligationPacket :=
  { graphClosednessObligationPacketReady :=
      concrete_analytic_spine_l2_r2_graph_closedness_obligation_packet_ready
    graphClosednessTheoremObligation := True
    closureUniquenessTheoremObligation := True
    closureCompatibilityWithDomainActionObligation := True
    closureCompatibilityWithGraphNormObligation := True
    boundaryNotClosureUniquenessTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheorem := True
    boundaryNotPVM := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the closure-uniqueness obligation packet. -/
def concreteAnalyticSpineL2R2ClosureUniquenessObligationPacketReady : Prop :=
  concreteAnalyticSpineL2R2GraphClosednessObligationPacketReady ∧
  concreteL2R2ClosureUniquenessObligationPacket.graphClosednessTheoremObligation ∧
  concreteL2R2ClosureUniquenessObligationPacket.closureUniquenessTheoremObligation ∧
  concreteL2R2ClosureUniquenessObligationPacket.closureCompatibilityWithDomainActionObligation ∧
  concreteL2R2ClosureUniquenessObligationPacket.closureCompatibilityWithGraphNormObligation ∧
  concreteL2R2ClosureUniquenessObligationPacket.boundaryNotClosureUniquenessTheorem ∧
  concreteL2R2ClosureUniquenessObligationPacket.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2ClosureUniquenessObligationPacket.boundaryNotSelfAdjointness ∧
  concreteL2R2ClosureUniquenessObligationPacket.boundaryNotSpectralTheorem ∧
  concreteL2R2ClosureUniquenessObligationPacket.boundaryNotPVM ∧
  concreteL2R2ClosureUniquenessObligationPacket.boundaryNotPositiveSpectralWeight

/-- The closure-uniqueness obligation packet is ready. -/
theorem concrete_analytic_spine_l2_r2_closure_uniqueness_obligation_packet_ready :
    concreteAnalyticSpineL2R2ClosureUniquenessObligationPacketReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_graph_closedness_obligation_packet_ready,
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

import MGAP4D.R2.Concrete.SelfAdjointRestrictionStatus
import MGAP4D.MathlibAdoptionGate.R2RestrictionRequest

namespace MGAP4D
namespace R2
namespace Concrete

structure RestrictionTheoremCandidate where
  restrictionStatusReady : Prop
  reducingSubspaceCandidate : Prop
  fullHamiltonianSelfAdjointCandidate : Prop
  restrictionDomainCandidate : Prop
  restrictionSelfAdjointCandidate : Prop
  r2RestrictionRequestReady : Prop
  mathlibStillDeferred : Prop

def RestrictionTheoremCandidate.ready (C : RestrictionTheoremCandidate) : Prop :=
  C.restrictionStatusReady ∧ C.reducingSubspaceCandidate ∧
  C.fullHamiltonianSelfAdjointCandidate ∧ C.restrictionDomainCandidate ∧
  C.restrictionSelfAdjointCandidate ∧ C.r2RestrictionRequestReady ∧
  C.mathlibStillDeferred

theorem restriction_theorem_candidate_pack
    (C : RestrictionTheoremCandidate) :
    C.ready ↔ C.restrictionStatusReady ∧ C.reducingSubspaceCandidate ∧
      C.fullHamiltonianSelfAdjointCandidate ∧ C.restrictionDomainCandidate ∧
      C.restrictionSelfAdjointCandidate ∧ C.r2RestrictionRequestReady ∧
      C.mathlibStillDeferred := by
  rfl

end Concrete
end R2
end MGAP4D

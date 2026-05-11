import MGAP4D.R5.Concrete.InfimumStatus
import MGAP4D.MathlibAdoptionGate.R5SpectrumRequest

namespace MGAP4D
namespace R5
namespace Concrete

structure SpectrumTheoremCandidate where
  infimumStatusReady : Prop
  spectrumSetCandidate : Prop
  bottomCandidate : Prop
  membershipWitnessCandidate : Prop
  comparisonSurfaceCandidate : Prop
  r5SpectrumRequestReady : Prop
  mathlibStillDeferred : Prop

def SpectrumTheoremCandidate.ready (C : SpectrumTheoremCandidate) : Prop :=
  C.infimumStatusReady ∧ C.spectrumSetCandidate ∧ C.bottomCandidate ∧
  C.membershipWitnessCandidate ∧ C.comparisonSurfaceCandidate ∧
  C.r5SpectrumRequestReady ∧ C.mathlibStillDeferred

theorem spectrum_theorem_candidate_pack
    (C : SpectrumTheoremCandidate) :
    C.ready ↔ C.infimumStatusReady ∧ C.spectrumSetCandidate ∧ C.bottomCandidate ∧
      C.membershipWitnessCandidate ∧ C.comparisonSurfaceCandidate ∧
      C.r5SpectrumRequestReady ∧ C.mathlibStillDeferred := by
  rfl

end Concrete
end R5
end MGAP4D

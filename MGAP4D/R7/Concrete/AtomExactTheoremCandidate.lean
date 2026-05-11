import MGAP4D.R7.Concrete.ExactGapStatus
import MGAP4D.MathlibAdoptionGate.R7AtomExactRequest

namespace MGAP4D
namespace R7
namespace Concrete

structure AtomExactTheoremCandidate where
  exactGapStatusReady : Prop
  atomPersistenceCandidate : Prop
  eigenstateSurfaceCandidate : Prop
  exactGapCandidate : Prop
  globalExportCandidate : Prop
  r7AtomExactRequestReady : Prop
  mathlibStillDeferred : Prop

def AtomExactTheoremCandidate.ready (C : AtomExactTheoremCandidate) : Prop :=
  C.exactGapStatusReady ∧ C.atomPersistenceCandidate ∧ C.eigenstateSurfaceCandidate ∧
  C.exactGapCandidate ∧ C.globalExportCandidate ∧ C.r7AtomExactRequestReady ∧
  C.mathlibStillDeferred

theorem atom_exact_theorem_candidate_pack
    (C : AtomExactTheoremCandidate) :
    C.ready ↔ C.exactGapStatusReady ∧ C.atomPersistenceCandidate ∧ C.eigenstateSurfaceCandidate ∧
      C.exactGapCandidate ∧ C.globalExportCandidate ∧ C.r7AtomExactRequestReady ∧
      C.mathlibStillDeferred := by
  rfl

end Concrete
end R7
end MGAP4D

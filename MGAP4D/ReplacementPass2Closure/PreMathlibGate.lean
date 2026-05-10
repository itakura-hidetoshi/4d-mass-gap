import MGAP4D.ReplacementPass2Closure.Pass2

namespace MGAP4D
namespace ReplacementPass2Closure

structure PreMathlibGate where
  pass2Closed : Prop
  ciGreen : Prop
  auditGreen : Prop
  concreteTheoremNeedRecorded : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def PreMathlibGate.ready (G : PreMathlibGate) : Prop :=
  G.pass2Closed ∧ G.ciGreen ∧ G.auditGreen ∧ G.concreteTheoremNeedRecorded ∧
  G.statusSurfacesPreserved ∧ G.publicBoundaryHeld

theorem pre_mathlib_gate_pack
    (G : PreMathlibGate) :
    G.ready ↔ G.pass2Closed ∧ G.ciGreen ∧ G.auditGreen ∧ G.concreteTheoremNeedRecorded ∧
      G.statusSurfacesPreserved ∧ G.publicBoundaryHeld := by
  rfl

end ReplacementPass2Closure
end MGAP4D

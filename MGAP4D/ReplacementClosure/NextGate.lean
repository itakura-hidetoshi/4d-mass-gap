import MGAP4D.ReplacementClosure.Pass1

namespace MGAP4D
namespace ReplacementClosure

structure NextReplacementGate where
  pass1Closed : Prop
  ciGreen : Prop
  auditGreen : Prop
  statusSurfacesPreserved : Prop
  mathlibStillDeferred : Prop
  nextPassRecorded : Prop

def NextReplacementGate.ready (G : NextReplacementGate) : Prop :=
  G.pass1Closed ∧ G.ciGreen ∧ G.auditGreen ∧ G.statusSurfacesPreserved ∧
  G.mathlibStillDeferred ∧ G.nextPassRecorded

theorem next_replacement_gate_pack
    (G : NextReplacementGate) :
    G.ready ↔ G.pass1Closed ∧ G.ciGreen ∧ G.auditGreen ∧ G.statusSurfacesPreserved ∧
      G.mathlibStillDeferred ∧ G.nextPassRecorded := by
  rfl

end ReplacementClosure
end MGAP4D

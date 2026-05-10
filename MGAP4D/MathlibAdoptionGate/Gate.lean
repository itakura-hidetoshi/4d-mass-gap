import MGAP4D.MathlibAdoptionGate.Requester
import MGAP4D.ReplacementPass2Closure

namespace MGAP4D
namespace MathlibAdoptionGate

structure MathlibGate where
  pass2Closed : Prop
  ciGreen : Prop
  auditGreen : Prop
  requestRecorded : Prop
  importGroupScoped : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def MathlibGate.ready (G : MathlibGate) : Prop :=
  G.pass2Closed ∧ G.ciGreen ∧ G.auditGreen ∧ G.requestRecorded ∧
  G.importGroupScoped ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld

theorem mathlib_gate_pack
    (G : MathlibGate) :
    G.ready ↔ G.pass2Closed ∧ G.ciGreen ∧ G.auditGreen ∧ G.requestRecorded ∧
      G.importGroupScoped ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D

import MGAP4D.MathlibAdoptionGate

namespace MGAP4D
namespace MathlibAdoptionGate

/--
A scoped request record for future R6 interval-exclusion theorem modules.
This does not import Mathlib and does not change lake dependencies.
-/
def r6IntervalRequest : MathlibRequest := {
  requester := MathlibRequester.r6Interval,
  requestedImportGroup := "Real.Basic; Order.Interval.Set.Basic; Set.Basic; Order.Bounds.Basic; Topology.Basic",
  reason := "future R6 interval-exclusion theorem modules may require real intervals, set intersections, emptiness lemmas, and ordered comparison infrastructure",
  scoped := true
}

theorem r6_interval_request_scoped : r6IntervalRequest.scoped = true := by
  rfl

structure R6IntervalRequestGate where
  requestRecorded : Prop
  scopedRequest : Prop
  mathlibGateReady : Prop
  statusPreserved : Prop

def R6IntervalRequestGate.ready (G : R6IntervalRequestGate) : Prop :=
  G.requestRecorded ∧ G.scopedRequest ∧ G.mathlibGateReady ∧ G.statusPreserved

theorem r6_interval_request_gate_pack
    (G : R6IntervalRequestGate) :
    G.ready ↔ G.requestRecorded ∧ G.scopedRequest ∧ G.mathlibGateReady ∧ G.statusPreserved := by
  rfl

end MathlibAdoptionGate
end MGAP4D

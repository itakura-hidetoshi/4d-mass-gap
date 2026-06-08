import MGAP4D.MathlibAdoptionGate.Requester

namespace MGAP4D
namespace MathlibAdoptionGate

/--
A scoped request record for future R5 spectrum / infimum theorem modules.
This does not import Mathlib and does not change lake dependencies.
-/
def r5SpectrumRequest : MathlibRequest := {
  requester := MathlibRequester.r5Spectrum,
  requestedImportGroup := "Set.Basic; Order.Bounds.Basic; ConditionallyCompleteLattice.Basic; Real.Basic; Topology.Basic",
  reason := "future R5 spectrum theorem modules may require sets, infimum/lower-bound constructions, real comparisons, and spectral-bottom witnesses",
  isScoped := true
}

theorem r5_spectrum_request_scoped : r5SpectrumRequest.isScoped = true := by
  rfl

structure R5SpectrumRequestGate where
  requestRecorded : Prop
  scopedRequest : Prop
  mathlibGateReady : Prop
  statusPreserved : Prop

def R5SpectrumRequestGate.ready (G : R5SpectrumRequestGate) : Prop :=
  G.requestRecorded ∧ G.scopedRequest ∧ G.mathlibGateReady ∧ G.statusPreserved

theorem r5_spectrum_request_gate_pack
    (G : R5SpectrumRequestGate) :
    G.ready ↔ G.requestRecorded ∧ G.scopedRequest ∧ G.mathlibGateReady ∧ G.statusPreserved := by
  rfl

end MathlibAdoptionGate
end MGAP4D

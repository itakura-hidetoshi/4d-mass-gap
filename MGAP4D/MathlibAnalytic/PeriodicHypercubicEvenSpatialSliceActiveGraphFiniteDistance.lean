import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveGraphConnectivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance spatialSliceActiveGraphFiniteDistanceLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Natural-number shortest-path distance in the intrinsic spatial-link active
graph. Connectedness makes this distance non-junk for every even periodic
volume. -/
noncomputable def periodicHypercubicEvenSpatialSliceActiveGraphDistance
    (H : Nat)
    (selected p : PeriodicHypercubicEvenSpatialSliceLink H) : Nat :=
  (periodicHypercubicEvenSpatialSliceActiveGraph H).dist selected p

/-- The spatial active-graph distance from a link to itself is zero. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceActiveGraphDistance_self
    (H : Nat)
    (selected : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpatialSliceActiveGraphDistance H selected selected = 0 := by
  simp [periodicHypercubicEvenSpatialSliceActiveGraphDistance]

/-- In the connected finite spatial active graph, every distance is strictly
smaller than the number of spatial links. This is only a finite-volume cutoff,
not a volume-independent metric estimate. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraphDistance_lt_card
    (H : Nat)
    (selected p : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpatialSliceActiveGraphDistance H selected p <
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
  let hConnected := periodicHypercubicEvenSpatialSliceActiveGraph_connected H
  obtain ⟨w, hw⟩ := (hConnected selected p).exists_isPath
  calc
    periodicHypercubicEvenSpatialSliceActiveGraphDistance H selected p ≤
        w.length := by
      exact SimpleGraph.dist_le w
    _ < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := hw.length_lt

/-- The finite graph-distance shell around a selected spatial link. -/
noncomputable def periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell
    (H : Nat)
    (selected : PeriodicHypercubicEvenSpatialSliceLink H)
    (m : Nat) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.filter fun p =>
    periodicHypercubicEvenSpatialSliceActiveGraphDistance H selected p = m

/-- Membership in the graph-distance shell is exactly equality of the natural
spatial active-graph distance with the shell index. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceActiveGraph_mem_distanceShell_iff
    (H : Nat)
    (selected p : PeriodicHypercubicEvenSpatialSliceLink H)
    (m : Nat) :
    p ∈ periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell H selected m ↔
      periodicHypercubicEvenSpatialSliceActiveGraphDistance H selected p = m := by
  classical
  simp [periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell]

end

end MathlibAnalytic
end MGAP4D

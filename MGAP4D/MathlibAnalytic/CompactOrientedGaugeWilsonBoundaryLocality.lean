import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonPlaquetteSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem compact_oriented_replaceLink_boundary_eq_of_not_plaquetteNeighbor
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (g : L.Gauge)
    (p : L.geometry.Plaquette)
    (hTarget : L.PlaquetteTouchesEdge p target)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source)
    (k : Fin 4) :
    L.replaceLink A target g (L.geometry.boundary p k).edge =
      L.replaceLink B target g (L.geometry.boundary p k).edge := by
  classical
  have hNotSource : ¬ L.PlaquetteTouchesEdge p source := by
    intro hSource
    apply hNotNeighbor
    exact (compact_oriented_mem_plaquetteNeighbors_iff
      L target source).mpr ⟨p, hTarget, hSource⟩
  by_cases hBoundaryTarget : (L.geometry.boundary p k).edge = target
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, hBoundaryTarget]
  · have hBoundarySource : (L.geometry.boundary p k).edge ≠ source := by
      intro hSource
      exact hNotSource ⟨k, hSource⟩
    simp [CompactOrientedGaugeWilsonSystem.replaceLink,
      hBoundaryTarget, hAgree _ hBoundarySource]

end
end MathlibAnalytic
end MGAP4D

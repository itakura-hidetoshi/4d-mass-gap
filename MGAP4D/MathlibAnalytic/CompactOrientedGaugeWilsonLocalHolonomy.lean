import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonBoundaryLocality

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem compact_oriented_local_holonomy_eq
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (e s : L.geometry.Edge)
    (g : L.Gauge)
    (p : L.geometry.Plaquette)
    (hp : L.PlaquetteTouchesEdge p e)
    (hs : s ∉ L.plaquetteNeighbors e)
    (hAB : L.AgreeOffLink A B s) :
    L.plaquetteHolonomy (L.replaceLink A e g) p =
      L.plaquetteHolonomy (L.replaceLink B e g) p := by
  apply compact_oriented_plaquetteHolonomy_congr
  intro k
  exact compact_oriented_replaceLink_boundary_eq_of_not_plaquetteNeighbor
    L A B e s g p hp hs hAB k

end
end MathlibAnalytic
end MGAP4D

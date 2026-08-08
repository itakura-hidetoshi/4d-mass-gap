import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonLocalAction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Boundary values of a plaquette not touching `source` are unchanged by a
source update followed by the same target replacement. -/
theorem compact_oriented_targetReplace_sourceReplace_boundary_eq_of_not_touches_source
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target source : L.geometry.Edge)
    (u g : L.Gauge)
    (p : L.geometry.Plaquette)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source)
    (k : Fin 4) :
    L.replaceLink A target u (L.geometry.boundary p k).edge =
      L.replaceLink (L.replaceLink A source g) target u
        (L.geometry.boundary p k).edge := by
  classical
  by_cases hTarget : (L.geometry.boundary p k).edge = target
  · rw [hTarget]
    simp [CompactOrientedGaugeWilsonSystem.replaceLink]
  · have hSource : (L.geometry.boundary p k).edge ≠ source := by
      intro hk
      exact hNotSource ⟨k, hk⟩
    simp [CompactOrientedGaugeWilsonSystem.replaceLink, hTarget, hSource]

/-- A compact oriented plaquette not touching the updated source has identical
holonomy after a common target replacement. -/
theorem compact_oriented_targetReplace_sourceReplace_holonomy_eq_of_not_touches_source
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target source : L.geometry.Edge)
    (u g : L.Gauge)
    (p : L.geometry.Plaquette)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source) :
    L.plaquetteHolonomy (L.replaceLink A target u) p =
      L.plaquetteHolonomy
        (L.replaceLink (L.replaceLink A source g) target u) p := by
  apply compact_oriented_plaquetteHolonomy_congr
  intro k
  exact
    compact_oriented_targetReplace_sourceReplace_boundary_eq_of_not_touches_source
      L A target source u g p hNotSource k

/-- The corresponding compact plaquette-energy terms are identical. -/
theorem compact_oriented_targetReplace_sourceReplace_energy_eq_of_not_touches_source
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target source : L.geometry.Edge)
    (u g : L.Gauge)
    (p : L.geometry.Plaquette)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source) :
    L.plaquetteEnergy
        (L.plaquetteHolonomy (L.replaceLink A target u) p) =
      L.plaquetteEnergy
        (L.plaquetteHolonomy
          (L.replaceLink (L.replaceLink A source g) target u) p) := by
  rw [compact_oriented_targetReplace_sourceReplace_holonomy_eq_of_not_touches_source
    L A target source u g p hNotSource]

end
end MathlibAnalytic
end MGAP4D

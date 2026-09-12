import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalInfluenceBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Boundary values of a plaquette not touching `source` are unchanged by a
source update followed by the same target replacement. -/
theorem finite_oriented_targetReplace_sourceReplace_boundary_eq_of_not_touches_source
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge)
    (p : L.Plaquette)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source)
    (k : Fin 4) :
    L.replaceLink A target u (L.boundary p k).edge =
      L.replaceLink (L.replaceLink A source g) target u
        (L.boundary p k).edge := by
  classical
  by_cases hTarget : (L.boundary p k).edge = target
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, hTarget]
  · have hSource : (L.boundary p k).edge ≠ source := by
      intro hk
      exact hNotSource ⟨k, hk⟩
    simp [FiniteOrientedLatticeWilsonSystem.replaceLink,
      hTarget, hSource]

/-- A plaquette not touching the updated source has identical oriented
holonomy after a common target replacement. -/
theorem finite_oriented_targetReplace_sourceReplace_holonomy_eq_of_not_touches_source
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge)
    (p : L.Plaquette)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source) :
    L.plaquetteHolonomy (L.replaceLink A target u) p =
      L.plaquetteHolonomy
        (L.replaceLink (L.replaceLink A source g) target u) p := by
  apply finite_oriented_plaquetteHolonomy_congr
  intro k
  exact
    finite_oriented_targetReplace_sourceReplace_boundary_eq_of_not_touches_source
      L A target source u g p hNotSource k

/-- The corresponding oriented plaquette-energy terms are identical. -/
theorem finite_oriented_targetReplace_sourceReplace_energy_eq_of_not_touches_source
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge)
    (p : L.Plaquette)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source) :
    L.plaquetteEnergy
        (L.plaquetteHolonomy (L.replaceLink A target u) p) =
      L.plaquetteEnergy
        (L.plaquetteHolonomy
          (L.replaceLink (L.replaceLink A source g) target u) p) := by
  rw [finite_oriented_targetReplace_sourceReplace_holonomy_eq_of_not_touches_source
    L A target source u g p hNotSource]

end

end MathlibAnalytic
end MGAP4D

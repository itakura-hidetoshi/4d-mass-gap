import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedSharedPlaquetteOscillation

/-!
# Plaquette-neighbor support for compact oriented Wilson systems

The current compact Wilson stack already contains the primitive signed plaquette incidence,
shared-plaquette set, and exact holonomy locality lemmas.  What was still missing on the
continuous compact carrier was the finite edge-neighbor API used to state Dobrushin row geometry.

This file adds only that missing layer: all links sharing a plaquette with a target link, the
zero-diagonal active-neighbor set, and exact membership characterizations.  The construction is
purely finite incidence geometry and is independent of gauge-group cardinality, so it applies
directly to the actual compact periodic `SU(N)` Wilson source.

No conditional total-variation estimate, Dobrushin contraction, covariance clustering, decay
rate, spectral gap, or numerical mass value is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Physical positive links sharing at least one plaquette with a target link. -/
noncomputable def CompactOrientedGaugeWilsonSystem.plaquetteNeighbors
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) : Finset L.geometry.Edge := by
  classical
  exact Finset.univ.filter fun source =>
    ∃ p : L.geometry.Plaquette,
      L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source

/-- Geometrically active plaquette neighbors, with the target link removed. -/
noncomputable def CompactOrientedGaugeWilsonSystem.activePlaquetteNeighbors
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) : Finset L.geometry.Edge := by
  classical
  exact (L.plaquetteNeighbors target).erase target

@[simp] theorem compact_oriented_mem_plaquetteNeighbors_iff
    (L : CompactOrientedGaugeWilsonSystem)
    (target source : L.geometry.Edge) :
    source ∈ L.plaquetteNeighbors target ↔
      ∃ p : L.geometry.Plaquette,
        L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source := by
  classical
  simp [CompactOrientedGaugeWilsonSystem.plaquetteNeighbors]

@[simp] theorem compact_oriented_mem_activePlaquetteNeighbors_iff
    (L : CompactOrientedGaugeWilsonSystem)
    (target source : L.geometry.Edge) :
    source ∈ L.activePlaquetteNeighbors target ↔
      (∃ p : L.geometry.Plaquette,
        L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source) ∧
        source ≠ target := by
  classical
  simp [CompactOrientedGaugeWilsonSystem.activePlaquetteNeighbors,
    compact_oriented_mem_plaquetteNeighbors_iff, and_comm]

/-- Active-neighbor membership can equivalently be read from the already-canonical
shared-plaquette set. -/
theorem compact_oriented_mem_activePlaquetteNeighbors_iff_sharedPlaquettes_nonempty
    (L : CompactOrientedGaugeWilsonSystem)
    (target source : L.geometry.Edge) :
    source ∈ L.activePlaquetteNeighbors target ↔
      (L.sharedPlaquettes target source).Nonempty ∧ source ≠ target := by
  rw [compact_oriented_mem_activePlaquetteNeighbors_iff]
  constructor
  · rintro ⟨⟨p, hpTarget, hpSource⟩, hne⟩
    exact ⟨⟨p, (compact_oriented_mem_sharedPlaquettes_iff
      L target source p).2 ⟨hpTarget, hpSource⟩⟩, hne⟩
  · rintro ⟨⟨p, hp⟩, hne⟩
    have hp' := (compact_oriented_mem_sharedPlaquettes_iff
      L target source p).1 hp
    exact ⟨⟨p, hp'.1, hp'.2⟩, hne⟩

end

end MathlibAnalytic
end MGAP4D

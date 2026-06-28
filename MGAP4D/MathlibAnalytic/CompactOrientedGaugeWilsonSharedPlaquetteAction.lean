import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSourceLocality

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The change of a compact target-local action under one source update is
exactly the sum over plaquettes shared by the target and source. -/
theorem compact_oriented_targetLocalAction_sub_sourceReplace_eq_sum_shared
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target source : L.geometry.Edge)
    (u g : L.Gauge) :
    L.targetLocalPlaquetteAction (L.replaceLink A target u) target -
        L.targetLocalPlaquetteAction
          (L.replaceLink (L.replaceLink A source g) target u) target =
      ∑ p ∈ L.sharedPlaquettes target source,
        (L.plaquetteEnergy
            (L.plaquetteHolonomy (L.replaceLink A target u) p) -
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (L.replaceLink (L.replaceLink A source g) target u) p)) := by
  classical
  unfold CompactOrientedGaugeWilsonSystem.targetLocalPlaquetteAction
  rw [← Finset.sum_sub_distrib]
  have hSupport :
      (∑ p ∈ L.sharedPlaquettes target source,
          ((if L.PlaquetteTouchesEdge p target then
              L.plaquetteEnergy
                (L.plaquetteHolonomy (L.replaceLink A target u) p)
            else 0) -
            (if L.PlaquetteTouchesEdge p target then
              L.plaquetteEnergy
                (L.plaquetteHolonomy
                  (L.replaceLink (L.replaceLink A source g) target u) p)
            else 0))) =
        ∑ p : L.geometry.Plaquette,
          ((if L.PlaquetteTouchesEdge p target then
              L.plaquetteEnergy
                (L.plaquetteHolonomy (L.replaceLink A target u) p)
            else 0) -
            (if L.PlaquetteTouchesEdge p target then
              L.plaquetteEnergy
                (L.plaquetteHolonomy
                  (L.replaceLink (L.replaceLink A source g) target u) p)
            else 0)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _hp hNotShared
    have hNotBoth :
        ¬ (L.PlaquetteTouchesEdge p target ∧
          L.PlaquetteTouchesEdge p source) := by
      intro hBoth
      exact hNotShared
        ((compact_oriented_mem_sharedPlaquettes_iff
          L target source p).2 hBoth)
    by_cases hTarget : L.PlaquetteTouchesEdge p target
    · have hNotSource : ¬ L.PlaquetteTouchesEdge p source := by
        intro hSource
        exact hNotBoth ⟨hTarget, hSource⟩
      have hEnergy :=
        compact_oriented_targetReplace_sourceReplace_energy_eq_of_not_touches_source
          L A target source u g p hNotSource
      simp [hTarget, hEnergy]
    · simp [hTarget]
  rw [← hSupport]
  apply Finset.sum_congr rfl
  intro p hp
  have hTarget :=
    ((compact_oriented_mem_sharedPlaquettes_iff
      L target source p).1 hp).1
  simp [hTarget]

end
end MathlibAnalytic
end MGAP4D

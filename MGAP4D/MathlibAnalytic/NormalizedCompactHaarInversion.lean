import MGAP4D.MathlibAnalytic.CompactGaugeWilsonGaugeInvariance

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Inversion preserves normalized Haar probability on every compact topological
group.  The inverse pushforward is again a Haar probability measure, hence is
equal to the original normalized Haar measure by uniqueness. -/
theorem normalizedCompactHaar_measurePreserving_inv
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    MeasurePreserving Inv.inv
      (normalizedCompactHaar G) (normalizedCompactHaar G) := by
  let μ : Measure G := normalizedCompactHaar G
  letI : Measure.IsHaarMeasure μ := by
    dsimp [μ, normalizedCompactHaar]
    infer_instance
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  letI : Measure.IsMulRightInvariant μ := by
    dsimp [μ]
    infer_instance
  let μinv : Measure G := Measure.map Inv.inv μ
  letI : Measure.IsHaarMeasure μinv := by
    dsimp [μinv]
    change Measure.IsHaarMeasure μ.inv
    infer_instance
  letI : IsProbabilityMeasure μinv := by
    dsimp [μinv]
    exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  have hμ : μinv = μ :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure μinv μ
  exact ⟨measurable_inv, hμ⟩

end

end MathlibAnalytic
end MGAP4D

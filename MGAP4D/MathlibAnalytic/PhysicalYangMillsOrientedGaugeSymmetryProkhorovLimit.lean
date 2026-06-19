import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryLimit

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

noncomputable def toSymmetryLimit
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :
    PhysicalFourDimensionalYangMillsSymmetryLimit :=
  { L.toWeakLimit with
    Symmetry := G.Symmetry
    action := G.action
    action_continuous := G.action_continuous
    approximatingInvariant := fun n g =>
      G.embeddedMeasure_map_eq_self (L.subsequence n) g }

theorem continuumMeasure_map_eq_self
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (g : G.Symmetry) :
    (G.toSymmetryLimit L).continuumMeasure.map
        (G.action_continuous g).measurable.aemeasurable =
      (G.toSymmetryLimit L).continuumMeasure :=
  physical_yang_mills_symmetry_passes_to_weak_limit
    (G.toSymmetryLimit L) g

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

end

end MathlibAnalytic
end MGAP4D

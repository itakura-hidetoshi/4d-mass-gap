import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

noncomputable def toSymmetryLimit_of_tight
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (hTight : E.toLatticeEmbedding.IsTight) :
    PhysicalFourDimensionalYangMillsSymmetryLimit :=
  G.toSymmetryLimit
    (physical_yang_mills_prokhorov_subsequence_exists
      E.toLatticeEmbedding hTight).some

theorem continuumMeasure_map_eq_self_of_tight
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (hTight : E.toLatticeEmbedding.IsTight)
    (g : G.Symmetry) :
    (G.toSymmetryLimit_of_tight hTight).continuumMeasure.map
        (G.action_continuous g).measurable.aemeasurable =
      (G.toSymmetryLimit_of_tight hTight).continuumMeasure :=
  physical_yang_mills_symmetry_passes_to_weak_limit
    (G.toSymmetryLimit_of_tight hTight) g

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

end

end MathlibAnalytic
end MGAP4D

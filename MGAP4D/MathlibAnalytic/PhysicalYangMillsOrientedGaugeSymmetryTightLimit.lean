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

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v

variable {Edge : Type} [Fintype Edge]

/-- A finite product on the reflection-fixed boundary sector is `SFinite`
whenever the one-link measure is sigma-finite. -/
instance boundaryPiMeasure_sfinite
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] :
    SFinite (P.boundaryPiMeasure μ) := by
  unfold boundaryPiMeasure
  infer_instance

/-- A finite product on the selected open half-lattice is `SFinite` whenever
the one-link measure is sigma-finite. -/
instance openHalfPiMeasure_sfinite
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] :
    SFinite (P.openHalfPiMeasure μ) := by
  unfold openHalfPiMeasure
  infer_instance

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D

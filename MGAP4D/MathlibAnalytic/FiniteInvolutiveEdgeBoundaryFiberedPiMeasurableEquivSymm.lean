import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasure

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v

variable {Edge : Type} [Fintype Edge]

/-- The inverse of the canonical measurable boundary/open-half/open-half
coordinate equivalence is pointwise the geometric boundary-fibered assembly.

This is the inverse counterpart of
`boundaryFiberedPiMeasurableEquiv_apply` and allows transported densities to be
rewritten directly on explicit boundary and open-half configurations. -/
@[simp]
theorem boundaryFiberedPiMeasurableEquiv_symm_apply
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [MeasurableSpace Value]
    (z : P.BoundaryConfiguration Value ×
      (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value)) :
    (P.boundaryFiberedPiMeasurableEquiv Value).symm z =
      P.boundaryFiberedAssemble z.1 z.2.1 z.2.2 := by
  apply (P.boundaryFiberedCoordinates Value).injective
  calc
    P.boundaryFiberedCoordinates Value
        ((P.boundaryFiberedPiMeasurableEquiv Value).symm z) =
      P.boundaryFiberedPiMeasurableEquiv Value
        ((P.boundaryFiberedPiMeasurableEquiv Value).symm z) := by
      symm
      exact P.boundaryFiberedPiMeasurableEquiv_apply Value _
    _ = z :=
      (P.boundaryFiberedPiMeasurableEquiv Value).apply_symm_apply z
    _ = P.boundaryFiberedCoordinates Value
        (P.boundaryFiberedAssemble z.1 z.2.1 z.2.2) := by
      symm
      exact (P.boundaryFiberedCoordinates Value).apply_symm_apply z

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D

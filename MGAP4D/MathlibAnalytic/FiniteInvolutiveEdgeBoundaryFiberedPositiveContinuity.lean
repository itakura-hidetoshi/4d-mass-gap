import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundarySectionWeightContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe v

/-- With the shared boundary and the negative open-half coordinate fixed,
boundary-fibered assembly is continuous in the positive open-half coordinate.
The proof is coordinatewise: positive edges evaluate the varying `Pi`-coordinate,
while negative and fixed edges are constant. -/
theorem FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_continuous_positive
    {Edge : Type} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [TopologicalSpace Value]
    (b : P.BoundaryConfiguration Value)
    (y : P.OpenHalfConfiguration Value) :
    Continuous
      (fun x : P.OpenHalfConfiguration Value =>
        P.boundaryFiberedAssemble b x y) := by
  apply continuous_pi
  intro e
  by_cases hpos : P.side e = ReflectionEdgeSide.positive
  · simpa [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble, hpos] using
      (continuous_apply (⟨e, hpos⟩ : P.PositiveEdge) :
        Continuous (fun x : P.OpenHalfConfiguration Value => x ⟨e, hpos⟩))
  · by_cases hneg : P.side e = ReflectionEdgeSide.negative
    · simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble, hpos, hneg]
      exact continuous_const
    · have hfixed : P.side e = ReflectionEdgeSide.fixed := by
        cases hside : P.side e <;> simp_all
      simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
        hpos, hneg, hfixed]
      exact continuous_const

end

end MathlibAnalytic
end MGAP4D

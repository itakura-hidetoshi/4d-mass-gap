import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v

variable {Edge : Type} [Fintype Edge]

/-- Restriction of a full finite-edge configuration to the reflection-fixed
boundary is continuous for the product topologies. -/
theorem continuous_boundaryRestriction
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value] :
    Continuous
      (P.boundaryRestriction :
        (Edge → Value) → P.BoundaryConfiguration Value) := by
  apply continuous_pi
  intro e
  exact continuous_apply e.1

/-- Restriction to the selected positive open half is continuous. -/
theorem continuous_positiveRestriction
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value] :
    Continuous
      (P.positiveRestriction :
        (Edge → Value) → P.OpenHalfConfiguration Value) := by
  apply continuous_pi
  intro e
  exact continuous_apply e.1

/-- Restriction to the reflected negative open half is continuous. -/
theorem continuous_negativeRestriction
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value] :
    Continuous
      (P.negativeRestriction :
        (Edge → Value) → P.OpenHalfConfiguration Value) := by
  apply continuous_pi
  intro e
  exact continuous_apply (P.reflection e.1)

/-- Reassembling shared boundary data and the two open halves is continuous.

The reflection-side classification is finite and independent of the input
configuration, so each output coordinate is simply one continuous evaluation
from one of the three input factors. -/
theorem continuous_boundaryFiberedAssemble
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value] :
    Continuous
      (fun z : P.BoundaryConfiguration Value ×
          (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) =>
        P.boundaryFiberedAssemble z.1 z.2.1 z.2.2) := by
  apply continuous_pi
  intro e
  by_cases hpos : P.side e = ReflectionEdgeSide.positive
  · have hx : Continuous
        (fun z : P.BoundaryConfiguration Value ×
            (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) =>
          z.2.1) :=
      continuous_fst.comp continuous_snd
    simpa [boundaryFiberedAssemble, hpos] using
      (continuous_apply (⟨e, hpos⟩ : P.PositiveEdge)).comp hx
  · by_cases hneg : P.side e = ReflectionEdgeSide.negative
    · have hy : Continuous
          (fun z : P.BoundaryConfiguration Value ×
              (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) =>
            z.2.2) :=
        continuous_snd.comp continuous_snd
      have href : P.side (P.reflection e) = ReflectionEdgeSide.positive := by
        simpa [hneg] using P.side_reflection e
      simpa [boundaryFiberedAssemble, hpos, hneg] using
        (continuous_apply
          (⟨P.reflection e, href⟩ : P.PositiveEdge)).comp hy
    · have hfixed : P.side e = ReflectionEdgeSide.fixed := by
        cases hside : P.side e <;> simp_all
      simpa [boundaryFiberedAssemble, hpos, hneg] using
        (continuous_apply (⟨e, hfixed⟩ : P.FixedEdge)).comp
          (continuous_fst : Continuous
            (fun z : P.BoundaryConfiguration Value ×
                (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) =>
              z.1))

/-- The exact boundary/open-half/open-half coordinate equivalence is in fact a
homeomorphism for arbitrary value spaces with their product topologies. -/
noncomputable def boundaryFiberedHomeomorph
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value] :
    (Edge → Value) ≃ₜ
      P.BoundaryConfiguration Value ×
        (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) where
  toEquiv := P.boundaryFiberedCoordinates Value
  continuous_toFun :=
    (P.continuous_boundaryRestriction Value).prodMk
      ((P.continuous_positiveRestriction Value).prodMk
        (P.continuous_negativeRestriction Value))
  continuous_invFun := P.continuous_boundaryFiberedAssemble Value

@[simp]
theorem boundaryFiberedHomeomorph_apply
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value]
    (A : Edge → Value) :
    P.boundaryFiberedHomeomorph Value A =
      P.boundaryFiberedCoordinates Value A :=
  rfl

@[simp]
theorem boundaryFiberedHomeomorph_symm_apply
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value]
    (z : P.BoundaryConfiguration Value ×
      (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value)) :
    (P.boundaryFiberedHomeomorph Value).symm z =
      P.boundaryFiberedAssemble z.1 z.2.1 z.2.2 :=
  rfl

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D

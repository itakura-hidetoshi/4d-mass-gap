import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

variable {Edge : Type} [Fintype Edge]

/-- The disjoint index carrier consisting of shared fixed edges, positive open
edges, and a second copy of the positive edges representing the negative open
half. -/
abbrev BoundaryFiberedIndex
    (P : FiniteInvolutiveEdgeOrbitPartition Edge) : Type :=
  P.FixedEdge ⊕ (P.PositiveEdge ⊕ P.PositiveEdge)

/-- Exact index equivalence underlying the boundary-fibered configuration
coordinates.  A negative edge is represented by the positive member of its
reflection orbit in the second positive-edge copy. -/
def boundaryFiberedIndexEquiv
    (P : FiniteInvolutiveEdgeOrbitPartition Edge) :
    Edge ≃ P.BoundaryFiberedIndex where
  toFun e :=
    if hpos : P.side e = ReflectionEdgeSide.positive then
      Sum.inr (Sum.inl ⟨e, hpos⟩)
    else if hneg : P.side e = ReflectionEdgeSide.negative then
      Sum.inr (Sum.inr ⟨P.reflection e, by
        simpa [hneg] using P.side_reflection e⟩)
    else
      Sum.inl ⟨e, by
        cases hside : P.side e <;> simp_all⟩
  invFun z :=
    match z with
    | Sum.inl e => e.1
    | Sum.inr (Sum.inl e) => e.1
    | Sum.inr (Sum.inr e) => P.reflection e.1
  left_inv e := by
    by_cases hpos : P.side e = ReflectionEdgeSide.positive
    · simp [hpos]
    · by_cases hneg : P.side e = ReflectionEdgeSide.negative
      · simp [hpos, hneg, P.reflection_involutive e]
      · have hfixed : P.side e = ReflectionEdgeSide.fixed := by
          cases hside : P.side e <;> simp_all
        simp [hpos, hneg, hfixed]
  right_inv z := by
    rcases z with e | e
    · simp [e.2]
    · rcases e with e | e
      · simp [e.2]
      · have hneg :
            P.side (P.reflection e.1) = ReflectionEdgeSide.negative :=
          P.side_reflection_of_positive e
        simp [hneg, P.reflection_involutive e.1]

@[simp]
theorem boundaryFiberedIndexEquiv_apply_fixed
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (e : P.FixedEdge) :
    P.boundaryFiberedIndexEquiv e.1 = Sum.inl e := by
  simp [boundaryFiberedIndexEquiv, e.2]

@[simp]
theorem boundaryFiberedIndexEquiv_apply_positive
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (e : P.PositiveEdge) :
    P.boundaryFiberedIndexEquiv e.1 = Sum.inr (Sum.inl e) := by
  simp [boundaryFiberedIndexEquiv, e.2]

@[simp]
theorem boundaryFiberedIndexEquiv_apply_reflected_positive
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (e : P.PositiveEdge) :
    P.boundaryFiberedIndexEquiv (P.reflection e.1) =
      Sum.inr (Sum.inr e) := by
  have hneg :
      P.side (P.reflection e.1) = ReflectionEdgeSide.negative :=
    P.side_reflection_of_positive e
  simp [boundaryFiberedIndexEquiv, hneg, P.reflection_involutive e.1]

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D

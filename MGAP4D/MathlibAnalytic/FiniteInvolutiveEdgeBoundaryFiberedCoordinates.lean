import MGAP4D.MathlibAnalytic.Z2FiniteInvolutiveEdgeOrbitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v

variable {Edge : Type} [Fintype Edge]

/-- Edges belonging to the reflection-fixed sector. -/
abbrev FixedEdge (P : FiniteInvolutiveEdgeOrbitPartition Edge) :=
  {e : Edge // P.side e = ReflectionEdgeSide.fixed}

/-- The selected positive representative of each non-fixed reflection orbit. -/
abbrev PositiveEdge (P : FiniteInvolutiveEdgeOrbitPartition Edge) :=
  {e : Edge // P.side e = ReflectionEdgeSide.positive}

/-- Values on the fixed edge sector. -/
abbrev BoundaryConfiguration
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) :=
  P.FixedEdge → Value

/-- Values on one open half-lattice. -/
abbrev OpenHalfConfiguration
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) :=
  P.PositiveEdge → Value

@[simp]
theorem side_reflection_of_positive
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (e : P.PositiveEdge) :
    P.side (P.reflection e.1) = ReflectionEdgeSide.negative := by
  simpa [e.2] using P.side_reflection e.1

@[simp]
theorem side_reflection_of_fixed
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (e : P.FixedEdge) :
    P.side (P.reflection e.1) = ReflectionEdgeSide.fixed := by
  simpa [e.2] using P.side_reflection e.1

/-- Restrict a full configuration to the shared reflection-fixed sector. -/
def boundaryRestriction
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (A : Edge → Value) : P.BoundaryConfiguration Value :=
  fun e => A e.1

/-- Restrict a full configuration to the selected positive open half. -/
def positiveRestriction
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (A : Edge → Value) : P.OpenHalfConfiguration Value :=
  fun e => A e.1

/-- Restrict a full configuration to the negative open half while indexing it
by the corresponding positive representatives. -/
def negativeRestriction
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (A : Edge → Value) : P.OpenHalfConfiguration Value :=
  fun e => A (P.reflection e.1)

/-- Assemble a full configuration from shared fixed-sector data and two open
half-lattice configurations. -/
def boundaryFiberedAssemble
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (b : P.BoundaryConfiguration Value)
    (x y : P.OpenHalfConfiguration Value) : Edge → Value :=
  fun e =>
    if hpos : P.side e = ReflectionEdgeSide.positive then
      x ⟨e, hpos⟩
    else if hneg : P.side e = ReflectionEdgeSide.negative then
      y ⟨P.reflection e, by
        simpa [hneg] using P.side_reflection e⟩
    else
      b ⟨e, by
        cases hside : P.side e <;> simp_all⟩

@[simp]
theorem boundaryFiberedAssemble_positive
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (b : P.BoundaryConfiguration Value)
    (x y : P.OpenHalfConfiguration Value)
    (e : P.PositiveEdge) :
    P.boundaryFiberedAssemble b x y e.1 = x e := by
  simp [boundaryFiberedAssemble, e.2]

@[simp]
theorem boundaryFiberedAssemble_fixed
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (b : P.BoundaryConfiguration Value)
    (x y : P.OpenHalfConfiguration Value)
    (e : P.FixedEdge) :
    P.boundaryFiberedAssemble b x y e.1 = b e := by
  simp [boundaryFiberedAssemble, e.2]

@[simp]
theorem boundaryFiberedAssemble_reflected_positive
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (b : P.BoundaryConfiguration Value)
    (x y : P.OpenHalfConfiguration Value)
    (e : P.PositiveEdge) :
    P.boundaryFiberedAssemble b x y (P.reflection e.1) = y e := by
  simp [boundaryFiberedAssemble, P.reflection_involutive e.1, e.2]

@[simp]
theorem boundaryRestriction_boundaryFiberedAssemble
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (b : P.BoundaryConfiguration Value)
    (x y : P.OpenHalfConfiguration Value) :
    P.boundaryRestriction (P.boundaryFiberedAssemble b x y) = b := by
  funext e
  exact P.boundaryFiberedAssemble_fixed b x y e

@[simp]
theorem positiveRestriction_boundaryFiberedAssemble
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (b : P.BoundaryConfiguration Value)
    (x y : P.OpenHalfConfiguration Value) :
    P.positiveRestriction (P.boundaryFiberedAssemble b x y) = x := by
  funext e
  exact P.boundaryFiberedAssemble_positive b x y e

@[simp]
theorem negativeRestriction_boundaryFiberedAssemble
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v}
    (b : P.BoundaryConfiguration Value)
    (x y : P.OpenHalfConfiguration Value) :
    P.negativeRestriction (P.boundaryFiberedAssemble b x y) = y := by
  funext e
  exact P.boundaryFiberedAssemble_reflected_positive b x y e

/-- Exact coordinate equivalence between full edge configurations and shared
boundary data together with the two open halves. -/
def boundaryFiberedCoordinates
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) :
    (Edge → Value) ≃
      P.BoundaryConfiguration Value ×
        (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) where
  toFun A :=
    (P.boundaryRestriction A,
      (P.positiveRestriction A, P.negativeRestriction A))
  invFun z :=
    P.boundaryFiberedAssemble z.1 z.2.1 z.2.2
  left_inv A := by
    funext e
    cases hside : P.side e with
    | positive =>
        simp [boundaryFiberedAssemble, boundaryRestriction,
          positiveRestriction, negativeRestriction, hside]
    | negative =>
        simp [boundaryFiberedAssemble, boundaryRestriction,
          positiveRestriction, negativeRestriction, hside,
          P.reflection_involutive e]
    | fixed =>
        simp [boundaryFiberedAssemble, boundaryRestriction,
          positiveRestriction, negativeRestriction, hside]
  right_inv z := by
    rcases z with ⟨b, x, y⟩
    apply Prod.ext
    · exact P.boundaryRestriction_boundaryFiberedAssemble b x y
    · apply Prod.ext
      · exact P.positiveRestriction_boundaryFiberedAssemble b x y
      · exact P.negativeRestriction_boundaryFiberedAssemble b x y

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D

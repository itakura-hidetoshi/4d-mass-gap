import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTimeReflection
import Mathlib.Data.Fintype.EquivFin

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Three sectors of a finite edge set under an involution. -/
inductive ReflectionEdgeSide
  | positive
  | negative
  | fixed
  deriving DecidableEq

/-- A finite edge carrier equipped with an involution and a noncanonical finite
ranking.  The ranking chooses one representative from every nontrivial
reflection orbit; fixed edges form the third sector. -/
structure FiniteInvolutiveEdgeOrbitPartition (Edge : Type) [Fintype Edge] where
  reflection : Edge → Edge
  reflection_involutive : Function.Involutive reflection
  rank : Edge ≃ Fin (Fintype.card Edge)

/-- Orbit-side classifier: the lower-ranked member of a two-element orbit is
positive, the higher-ranked member is negative, and fixed points are fixed. -/
def FiniteInvolutiveEdgeOrbitPartition.side
    {Edge : Type} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (e : Edge) : ReflectionEdgeSide :=
  if P.rank e < P.rank (P.reflection e) then
    .positive
  else if P.rank (P.reflection e) < P.rank e then
    .negative
  else
    .fixed

/-- Reflection swaps the positive and negative members of every two-element
orbit and preserves fixed edges. -/
@[simp]
theorem FiniteInvolutiveEdgeOrbitPartition.side_reflection
    {Edge : Type} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (e : Edge) :
    P.side (P.reflection e) =
      match P.side e with
      | .positive => .negative
      | .negative => .positive
      | .fixed => .fixed := by
  by_cases hlt : P.rank e < P.rank (P.reflection e)
  · have hnot : ¬ P.rank (P.reflection e) < P.rank e :=
      not_lt_of_ge hlt.le
    simp [FiniteInvolutiveEdgeOrbitPartition.side,
      P.reflection_involutive e, hlt, hnot]
  · by_cases hgt : P.rank (P.reflection e) < P.rank e
    · simp [FiniteInvolutiveEdgeOrbitPartition.side,
        P.reflection_involutive e, hlt, hgt]
    · have heq : P.rank e = P.rank (P.reflection e) :=
        le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      simp [FiniteInvolutiveEdgeOrbitPartition.side,
        P.reflection_involutive e, hlt, hgt, heq]

/-- Positive-half data are stored on the finite edge carrier.  The assembly
operation below reads only the selected member of each reflection orbit. -/
abbrev FiniteInvolutiveEdgeOrbitPartition.PositiveConfiguration
    {Edge : Type} [Fintype Edge]
    (_P : FiniteInvolutiveEdgeOrbitPartition Edge) : Type :=
  Edge → Z2Gauge

/-- Assemble two positive-half inputs into one full configuration.  Fixed edges
are assigned the identity element, avoiding an asymmetric boundary choice. -/
def FiniteInvolutiveEdgeOrbitPartition.assemble
    {Edge : Type} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (x y : P.PositiveConfiguration) : Edge → Z2Gauge :=
  fun e =>
    match P.side e with
    | .positive => x e
    | .negative => y (P.reflection e)
    | .fixed => 1

/-- Pullback reflection on full edge configurations. -/
def FiniteInvolutiveEdgeOrbitPartition.configurationReflection
    {Edge : Type} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (A : Edge → Z2Gauge) : Edge → Z2Gauge :=
  fun e => A (P.reflection e)

/-- Configuration reflection is involutive. -/
theorem FiniteInvolutiveEdgeOrbitPartition.configurationReflection_involutive
    {Edge : Type} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge) :
    Function.Involutive P.configurationReflection := by
  intro A
  funext e
  simp [FiniteInvolutiveEdgeOrbitPartition.configurationReflection,
    P.reflection_involutive e]

/-- Reflection exchanges the two assembled half-configurations. -/
theorem FiniteInvolutiveEdgeOrbitPartition.reflection_assemble
    {Edge : Type} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (x y : P.PositiveConfiguration) :
    P.configurationReflection (P.assemble x y) = P.assemble y x := by
  funext e
  cases hside : P.side e <;>
    simp [FiniteInvolutiveEdgeOrbitPartition.configurationReflection,
      FiniteInvolutiveEdgeOrbitPartition.assemble,
      hside, P.reflection_involutive e]

/-- The concrete even four-torus edge involution equipped with a finite orbit
ranking. -/
def finiteEvenFourTorusEdgeOrbitPartition
    (H : ℕ) :
    FiniteInvolutiveEdgeOrbitPartition (FiniteEvenFourTorusEdge H) :=
  { reflection := finiteEvenFourTorusEdgeReflection H
    reflection_involutive :=
      finiteEvenFourTorusEdgeReflection_involutive H
    rank := Fintype.equivFin (FiniteEvenFourTorusEdge H) }

/-- Concrete assembly of two half-configurations on the even four-torus. -/
def finiteEvenFourTorusAssemble
    (H : ℕ)
    (x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration) :
    FiniteEvenFourTorusConfiguration H :=
  (finiteEvenFourTorusEdgeOrbitPartition H).assemble x y

/-- Concrete configuration reflection agrees with the generic orbit
reflection. -/
theorem finiteEvenFourTorus_configurationReflection_eq_orbitReflection
    (H : ℕ) :
    finiteEvenFourTorusConfigurationReflection H =
      (finiteEvenFourTorusEdgeOrbitPartition H).configurationReflection := by
  rfl

/-- The concrete even-torus assembly satisfies the OS swap identity. -/
theorem finiteEvenFourTorus_reflection_assemble
    (H : ℕ)
    (x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration) :
    finiteEvenFourTorusConfigurationReflection H
        (finiteEvenFourTorusAssemble H x y) =
      finiteEvenFourTorusAssemble H y x := by
  exact
    (finiteEvenFourTorusEdgeOrbitPartition H).reflection_assemble x y

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTimeReflection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Three sectors of a finite edge set under an involution. -/
inductive ReflectionEdgeSide
  | positive
  | negative
  | fixed
  deriving DecidableEq

/-- A finite edge carrier equipped with an involution and an explicit
reflection-compatible side classifier.  Keeping the classifier as data avoids
silently choosing a nongeometric order on the edge carrier. -/
structure FiniteInvolutiveEdgeOrbitPartition (Edge : Type) [Fintype Edge] where
  reflection : Edge → Edge
  reflection_involutive : Function.Involutive reflection
  side : Edge → ReflectionEdgeSide
  side_reflection :
    ∀ e,
      side (reflection e) =
        match side e with
        | .positive => .negative
        | .negative => .positive
        | .fixed => .fixed

attribute [simp] FiniteInvolutiveEdgeOrbitPartition.side_reflection

/-- A reflection-compatible side classifier generated from any natural-valued
geometric rank.  Ties are treated as fixed-sector edges. -/
def finiteInvolutiveEdgeRankSide
    {Edge : Type}
    (reflection : Edge → Edge)
    (rank : Edge → ℕ)
    (e : Edge) : ReflectionEdgeSide :=
  if rank e < rank (reflection e) then
    .positive
  else if rank (reflection e) < rank e then
    .negative
  else
    .fixed

/-- Comparing a geometric rank across an involution exchanges the two strict
sides and preserves ties. -/
@[simp]
theorem finiteInvolutiveEdgeRankSide_reflection
    {Edge : Type}
    (reflection : Edge → Edge)
    (hreflection : Function.Involutive reflection)
    (rank : Edge → ℕ)
    (e : Edge) :
    finiteInvolutiveEdgeRankSide reflection rank (reflection e) =
      match finiteInvolutiveEdgeRankSide reflection rank e with
      | .positive => .negative
      | .negative => .positive
      | .fixed => .fixed := by
  by_cases hlt : rank e < rank (reflection e)
  · have hnot : ¬ rank (reflection e) < rank e :=
      not_lt_of_ge hlt.le
    simp [finiteInvolutiveEdgeRankSide, hreflection e, hlt, hnot]
  · by_cases hgt : rank (reflection e) < rank e
    · simp [finiteInvolutiveEdgeRankSide, hreflection e, hlt, hgt]
    · have heq : rank e = rank (reflection e) :=
        le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      simp [finiteInvolutiveEdgeRankSide, hreflection e, hlt, hgt, heq]

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

/-- Reflection exchanges the two assembled positive-half inputs. -/
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

/-- A geometric rank for an even-torus edge: the sum of the canonical residue
representatives of the two endpoint time coordinates. -/
def finiteEvenFourTorusEdgeTimeRank
    (H : ℕ) (e : FiniteEvenFourTorusEdge H) : ℕ :=
  (e.1 0).val + (e.2 0).val

/-- Time-geometric side of an even-torus edge.  The representative whose
endpoint-time rank is smaller is selected as positive; its reflected partner is
negative, while reflection-symmetric ties are fixed. -/
def finiteEvenFourTorusEdgeGeometricSide
    (H : ℕ) (e : FiniteEvenFourTorusEdge H) : ReflectionEdgeSide :=
  finiteInvolutiveEdgeRankSide
    (finiteEvenFourTorusEdgeReflection H)
    (finiteEvenFourTorusEdgeTimeRank H)
    e

/-- The concrete time-geometric edge classifier obeys the reflection exchange
law. -/
@[simp]
theorem finiteEvenFourTorusEdgeGeometricSide_reflection
    (H : ℕ) (e : FiniteEvenFourTorusEdge H) :
    finiteEvenFourTorusEdgeGeometricSide H
        (finiteEvenFourTorusEdgeReflection H e) =
      match finiteEvenFourTorusEdgeGeometricSide H e with
      | .positive => .negative
      | .negative => .positive
      | .fixed => .fixed := by
  exact finiteInvolutiveEdgeRankSide_reflection
    (finiteEvenFourTorusEdgeReflection H)
    (finiteEvenFourTorusEdgeReflection_involutive H)
    (finiteEvenFourTorusEdgeTimeRank H)
    e

/-- The concrete even four-torus edge involution equipped with the
endpoint-time geometric side classifier. -/
def finiteEvenFourTorusEdgeOrbitPartition
    (H : ℕ) :
    FiniteInvolutiveEdgeOrbitPartition (FiniteEvenFourTorusEdge H) :=
  { reflection := finiteEvenFourTorusEdgeReflection H
    reflection_involutive :=
      finiteEvenFourTorusEdgeReflection_involutive H
    side := finiteEvenFourTorusEdgeGeometricSide H
    side_reflection := finiteEvenFourTorusEdgeGeometricSide_reflection H }

/-- Concrete assembly of two half-configurations on the even four-torus. -/
def finiteEvenFourTorusAssemble
    (H : ℕ)
    (x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration) :
    FiniteEvenFourTorusConfiguration H :=
  (finiteEvenFourTorusEdgeOrbitPartition H).assemble x y

/-- A positive geometric edge reads the first half-configuration. -/
@[simp]
theorem finiteEvenFourTorusAssemble_positive
    (H : ℕ)
    (x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration)
    (e : FiniteEvenFourTorusEdge H)
    (hside : finiteEvenFourTorusEdgeGeometricSide H e = .positive) :
    finiteEvenFourTorusAssemble H x y e = x e := by
  simp [finiteEvenFourTorusAssemble,
    finiteEvenFourTorusEdgeOrbitPartition,
    FiniteInvolutiveEdgeOrbitPartition.assemble,
    hside]

/-- A negative geometric edge reads the reflected edge from the second
half-configuration. -/
@[simp]
theorem finiteEvenFourTorusAssemble_negative
    (H : ℕ)
    (x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration)
    (e : FiniteEvenFourTorusEdge H)
    (hside : finiteEvenFourTorusEdgeGeometricSide H e = .negative) :
    finiteEvenFourTorusAssemble H x y e =
      y (finiteEvenFourTorusEdgeReflection H e) := by
  simp [finiteEvenFourTorusAssemble,
    finiteEvenFourTorusEdgeOrbitPartition,
    FiniteInvolutiveEdgeOrbitPartition.assemble,
    hside]

/-- A fixed geometric edge is assigned the identity gauge element. -/
@[simp]
theorem finiteEvenFourTorusAssemble_fixed
    (H : ℕ)
    (x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration)
    (e : FiniteEvenFourTorusEdge H)
    (hside : finiteEvenFourTorusEdgeGeometricSide H e = .fixed) :
    finiteEvenFourTorusAssemble H x y e = 1 := by
  simp [finiteEvenFourTorusAssemble,
    finiteEvenFourTorusEdgeOrbitPartition,
    FiniteInvolutiveEdgeOrbitPartition.assemble,
    hside]

/-- The reflection partner of a positive edge reads the second
half-configuration at the original representative. -/
@[simp]
theorem finiteEvenFourTorusAssemble_reflection_of_positive
    (H : ℕ)
    (x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration)
    (e : FiniteEvenFourTorusEdge H)
    (hside : finiteEvenFourTorusEdgeGeometricSide H e = .positive) :
    finiteEvenFourTorusAssemble H x y
        (finiteEvenFourTorusEdgeReflection H e) = y e := by
  simp [finiteEvenFourTorusAssemble,
    finiteEvenFourTorusEdgeOrbitPartition,
    FiniteInvolutiveEdgeOrbitPartition.assemble,
    hside, finiteEvenFourTorusEdgeReflection_involutive H e]

/-- The reflection partner of a negative edge is positive and therefore reads
the first half-configuration at that reflected representative. -/
@[simp]
theorem finiteEvenFourTorusAssemble_reflection_of_negative
    (H : ℕ)
    (x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration)
    (e : FiniteEvenFourTorusEdge H)
    (hside : finiteEvenFourTorusEdgeGeometricSide H e = .negative) :
    finiteEvenFourTorusAssemble H x y
        (finiteEvenFourTorusEdgeReflection H e) =
      x (finiteEvenFourTorusEdgeReflection H e) := by
  simp [finiteEvenFourTorusAssemble,
    finiteEvenFourTorusEdgeOrbitPartition,
    FiniteInvolutiveEdgeOrbitPartition.assemble,
    hside]

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

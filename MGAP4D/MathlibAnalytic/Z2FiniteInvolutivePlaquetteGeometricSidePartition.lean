import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPlaquetteReflection
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPlaquetteSupportReflection
import Mathlib.Data.Fintype.EquivFin

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A finite plaquette involution together with a reflection-invariant geometric
crossing sector.  The finite rank chooses positive and negative representatives
only outside that crossing sector. -/
structure FiniteInvolutivePlaquetteGeometricSidePartition
    (Plaquette : Type) [Fintype Plaquette] where
  reflection : Plaquette → Plaquette
  reflection_involutive : Function.Involutive reflection
  crossing : Plaquette → Prop
  crossing_reflection : ∀ p, crossing (reflection p) ↔ crossing p
  fixed_crossing : ∀ p, reflection p = p → crossing p
  rank : Plaquette ≃ Fin (Fintype.card Plaquette)

/-- Geometric side classifier.  Crossing plaquettes remain crossing even when
their reflection orbit has two distinct members.  Rank is used only on the
noncrossing two-element orbits. -/
def FiniteInvolutivePlaquetteGeometricSidePartition.side
    {Plaquette : Type} [Fintype Plaquette]
    (P : FiniteInvolutivePlaquetteGeometricSidePartition Plaquette)
    (p : Plaquette) : ReflectionPlaquetteSide :=
  if P.crossing p then
    .crossing
  else if P.rank p < P.rank (P.reflection p) then
    .positive
  else
    .negative

/-- Reflection exchanges the two open sides and preserves the full geometric
crossing sector, including nonfixed crossing orbits. -/
@[simp]
theorem FiniteInvolutivePlaquetteGeometricSidePartition.side_reflection
    {Plaquette : Type} [Fintype Plaquette]
    (P : FiniteInvolutivePlaquetteGeometricSidePartition Plaquette)
    (p : Plaquette) :
    P.side (P.reflection p) =
      match P.side p with
      | .positive => .negative
      | .crossing => .crossing
      | .negative => .positive := by
  by_cases hc : P.crossing p
  · have hcr : P.crossing (P.reflection p) :=
      (P.crossing_reflection p).2 hc
    simp [FiniteInvolutivePlaquetteGeometricSidePartition.side, hc, hcr]
  · have hcr : ¬ P.crossing (P.reflection p) := by
      intro h
      exact hc ((P.crossing_reflection p).1 h)
    by_cases hlt : P.rank p < P.rank (P.reflection p)
    · have hnot : ¬ P.rank (P.reflection p) < P.rank p :=
        not_lt_of_ge hlt.le
      simp [FiniteInvolutivePlaquetteGeometricSidePartition.side,
        hc, hcr, hlt, hnot, P.reflection_involutive p]
    · have hreflection_ne : P.reflection p ≠ p := by
        intro hfix
        exact hc (P.fixed_crossing p hfix)
      have hrank_ne : P.rank (P.reflection p) ≠ P.rank p := by
        intro h
        exact hreflection_ne (P.rank.injective h)
      have hgt : P.rank (P.reflection p) < P.rank p :=
        lt_of_le_of_ne (le_of_not_gt hlt) hrank_ne
      simp [FiniteInvolutivePlaquetteGeometricSidePartition.side,
        hc, hcr, hlt, hgt, P.reflection_involutive p]

/-- Compatibility data connecting the concrete even-torus plaquette reflection
to the already established reflected vertex support.  The remaining geometric
work is isolated in the ordered-support identity and the fixed-plane lemma. -/
structure FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility
    (H : ℕ) where
  vertices_reflection :
    ∀ p : FiniteEvenFourTorusPlaquette H,
      finiteFourTorusPlaquetteVertices
          (finiteEvenFourTorusPlaquetteReflection H p) =
        finiteEvenFourTorusPlaquetteReflectedVertices p
  fixed_crossing :
    ∀ p : FiniteEvenFourTorusPlaquette H,
      finiteEvenFourTorusPlaquetteReflection H p = p →
        finiteEvenFourTorusCrossingPlaquette p

/-- Concrete reflection exchanges strict-positive and strict-negative
plaquettes once ordered support compatibility is available. -/
theorem FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility
    .strictPositive_reflection_iff_negative
    {H : ℕ}
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H)
    (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusStrictPositivePlaquette
        (finiteEvenFourTorusPlaquetteReflection H p) ↔
      finiteEvenFourTorusStrictNegativePlaquette p := by
  unfold finiteEvenFourTorusStrictPositivePlaquette
    finiteEvenFourTorusPlaquetteVertices
  rw [C.vertices_reflection p]
  exact finiteEvenFourTorusPlaquette_reflectedPositive_iff_negative p

/-- The reverse open-side exchange. -/
theorem FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility
    .strictNegative_reflection_iff_positive
    {H : ℕ}
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H)
    (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusStrictNegativePlaquette
        (finiteEvenFourTorusPlaquetteReflection H p) ↔
      finiteEvenFourTorusStrictPositivePlaquette p := by
  unfold finiteEvenFourTorusStrictNegativePlaquette
    finiteEvenFourTorusPlaquetteVertices
  rw [C.vertices_reflection p]
  exact finiteEvenFourTorusPlaquette_reflectedNegative_iff_positive p

/-- Concrete plaquette reflection preserves the geometric crossing sector. -/
theorem FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility
    .crossing_reflection_iff
    {H : ℕ}
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H)
    (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusCrossingPlaquette
        (finiteEvenFourTorusPlaquetteReflection H p) ↔
      finiteEvenFourTorusCrossingPlaquette p := by
  unfold finiteEvenFourTorusCrossingPlaquette
    finiteEvenFourTorusPlaquetteVertices
  rw [C.vertices_reflection p]
  exact finiteEvenFourTorusPlaquette_reflectedCrossing_iff p

/-- Package compatible concrete even-torus geometry as a reflection-invariant
geometric three-sector partition. -/
def finiteEvenFourTorusGeometricPlaquetteSidePartition
    (H : ℕ)
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H) :
    FiniteInvolutivePlaquetteGeometricSidePartition
      (FiniteEvenFourTorusPlaquette H) :=
  { reflection := finiteEvenFourTorusPlaquetteReflection H
    reflection_involutive :=
      finiteEvenFourTorusPlaquetteReflection_involutive H
    crossing := finiteEvenFourTorusCrossingPlaquette
    crossing_reflection := C.crossing_reflection_iff
    fixed_crossing := C.fixed_crossing
    rank := Fintype.equivFin (FiniteEvenFourTorusPlaquette H) }

/-- The concrete geometric classifier satisfies the desired side exchange law. -/
@[simp]
theorem finiteEvenFourTorusGeometricPlaquetteSidePartition_side_reflection
    (H : ℕ)
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H)
    (p : FiniteEvenFourTorusPlaquette H) :
    (finiteEvenFourTorusGeometricPlaquetteSidePartition H C).side
        (finiteEvenFourTorusPlaquetteReflection H p) =
      match (finiteEvenFourTorusGeometricPlaquetteSidePartition H C).side p with
      | .positive => .negative
      | .crossing => .crossing
      | .negative => .positive := by
  exact
    (finiteEvenFourTorusGeometricPlaquetteSidePartition H C).side_reflection p

end

end MathlibAnalytic
end MGAP4D

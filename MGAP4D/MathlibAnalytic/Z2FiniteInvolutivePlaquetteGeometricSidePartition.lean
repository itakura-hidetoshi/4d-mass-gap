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
  rank : Plaquette ≃ Fin (Fintype.card Plaquette)

/-- Geometric side classifier.  Geometric crossing plaquettes stay crossing.
Outside that sector, rank orders nontrivial reflection pairs; equal-rank fixed
orbits are classified as crossing automatically. -/
def FiniteInvolutivePlaquetteGeometricSidePartition.side
    {Plaquette : Type} [Fintype Plaquette]
    (P : FiniteInvolutivePlaquetteGeometricSidePartition Plaquette)
    (p : Plaquette) : ReflectionPlaquetteSide := by
  classical
  exact
    if P.crossing p then
      .crossing
    else if P.rank p < P.rank (P.reflection p) then
      .positive
    else if P.rank (P.reflection p) < P.rank p then
      .negative
    else
      .crossing

/-- Reflection exchanges the two open sides and preserves both the geometric
crossing sector and fixed reflection orbits. -/
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
  classical
  by_cases hc : P.crossing p
  · have hcr : P.crossing (P.reflection p) :=
      (P.crossing_reflection p).2 hc
    unfold FiniteInvolutivePlaquetteGeometricSidePartition.side
    rw [if_pos hcr, if_pos hc]
  · have hcr : ¬ P.crossing (P.reflection p) := by
      intro h
      exact hc ((P.crossing_reflection p).1 h)
    by_cases hlt : P.rank p < P.rank (P.reflection p)
    · have hnot : ¬ P.rank (P.reflection p) < P.rank p :=
        not_lt_of_ge hlt.le
      have hfirstRef :
          ¬ P.rank (P.reflection p) <
            P.rank (P.reflection (P.reflection p)) := by
        simpa only [P.reflection_involutive p] using hnot
      have hsecondRef :
          P.rank (P.reflection (P.reflection p)) <
            P.rank (P.reflection p) := by
        simpa only [P.reflection_involutive p] using hlt
      unfold FiniteInvolutivePlaquetteGeometricSidePartition.side
      rw [if_neg hcr, if_neg hfirstRef, if_pos hsecondRef,
        if_neg hc, if_pos hlt]
    · by_cases hgt : P.rank (P.reflection p) < P.rank p
      · have hfirstRef :
            P.rank (P.reflection p) <
              P.rank (P.reflection (P.reflection p)) := by
          simpa only [P.reflection_involutive p] using hgt
        unfold FiniteInvolutivePlaquetteGeometricSidePartition.side
        rw [if_neg hcr, if_pos hfirstRef,
          if_neg hc, if_neg hlt, if_pos hgt]
      · have hfirstRef :
            ¬ P.rank (P.reflection p) <
              P.rank (P.reflection (P.reflection p)) := by
          simpa only [P.reflection_involutive p] using hgt
        have hsecondRef :
            ¬ P.rank (P.reflection (P.reflection p)) <
              P.rank (P.reflection p) := by
          simpa only [P.reflection_involutive p] using hlt
        unfold FiniteInvolutivePlaquetteGeometricSidePartition.side
        rw [if_neg hcr, if_neg hfirstRef, if_neg hsecondRef,
          if_neg hc, if_neg hlt, if_neg hgt]

/-- Compatibility data connecting the concrete even-torus plaquette reflection
to the already established reflected vertex support.  Vertex order may change
under orientation correction, so compatibility is expressed by membership
rather than ordered-list equality. -/
structure FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility
    (H : ℕ) where
  vertices_reflection_mem :
    ∀ (p : FiniteEvenFourTorusPlaquette H)
      (v : FiniteEvenFourTorusVertex H),
      v ∈ finiteFourTorusPlaquetteVertices
          (finiteEvenFourTorusPlaquetteReflection H p) ↔
        v ∈ finiteEvenFourTorusPlaquetteReflectedVertices p

/-- Strict-positive support is invariant under replacing a vertex list by a
membership-equivalent one. -/
theorem FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility.strictPositiveSupport_reflection_iff
    {H : ℕ}
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H)
    (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusStrictPositiveSupport H
        (finiteFourTorusPlaquetteVertices
          (finiteEvenFourTorusPlaquetteReflection H p)) ↔
      finiteEvenFourTorusStrictPositiveSupport H
        (finiteEvenFourTorusPlaquetteReflectedVertices p) := by
  unfold finiteEvenFourTorusStrictPositiveSupport
  constructor
  · intro h v hv
    exact h v ((C.vertices_reflection_mem p v).2 hv)
  · intro h v hv
    exact h v ((C.vertices_reflection_mem p v).1 hv)

/-- The analogous membership-invariance for strict-negative support. -/
theorem FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility.strictNegativeSupport_reflection_iff
    {H : ℕ}
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H)
    (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusStrictNegativeSupport H
        (finiteFourTorusPlaquetteVertices
          (finiteEvenFourTorusPlaquetteReflection H p)) ↔
      finiteEvenFourTorusStrictNegativeSupport H
        (finiteEvenFourTorusPlaquetteReflectedVertices p) := by
  unfold finiteEvenFourTorusStrictNegativeSupport
  constructor
  · intro h v hv
    exact h v ((C.vertices_reflection_mem p v).2 hv)
  · intro h v hv
    exact h v ((C.vertices_reflection_mem p v).1 hv)

/-- Concrete reflection exchanges strict-positive and strict-negative
plaquettes once support compatibility is available. -/
theorem FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility.strictPositive_reflection_iff_negative
    {H : ℕ}
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H)
    (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusStrictPositivePlaquette
        (finiteEvenFourTorusPlaquetteReflection H p) ↔
      finiteEvenFourTorusStrictNegativePlaquette p := by
  unfold finiteEvenFourTorusStrictPositivePlaquette
    finiteEvenFourTorusPlaquetteVertices
  exact
    (C.strictPositiveSupport_reflection_iff p).trans
      (finiteEvenFourTorusPlaquette_reflectedPositive_iff_negative p)

/-- The reverse open-side exchange. -/
theorem FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility.strictNegative_reflection_iff_positive
    {H : ℕ}
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H)
    (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusStrictNegativePlaquette
        (finiteEvenFourTorusPlaquetteReflection H p) ↔
      finiteEvenFourTorusStrictPositivePlaquette p := by
  unfold finiteEvenFourTorusStrictNegativePlaquette
    finiteEvenFourTorusPlaquetteVertices
  exact
    (C.strictNegativeSupport_reflection_iff p).trans
      (finiteEvenFourTorusPlaquette_reflectedNegative_iff_positive p)

/-- Concrete plaquette reflection preserves the geometric crossing sector. -/
theorem FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility.crossing_reflection_iff
    {H : ℕ}
    (C : FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility H)
    (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusCrossingPlaquette
        (finiteEvenFourTorusPlaquetteReflection H p) ↔
      finiteEvenFourTorusCrossingPlaquette p := by
  change
    (¬ finiteEvenFourTorusStrictPositivePlaquette
        (finiteEvenFourTorusPlaquetteReflection H p) ∧
      ¬ finiteEvenFourTorusStrictNegativePlaquette
        (finiteEvenFourTorusPlaquetteReflection H p)) ↔
    (¬ finiteEvenFourTorusStrictPositivePlaquette p ∧
      ¬ finiteEvenFourTorusStrictNegativePlaquette p)
  rw [C.strictPositive_reflection_iff_negative p,
    C.strictNegative_reflection_iff_positive p]
  exact and_comm

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
    crossing_reflection :=
      FiniteEvenFourTorusPlaquetteSupportReflectionCompatibility.crossing_reflection_iff C
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

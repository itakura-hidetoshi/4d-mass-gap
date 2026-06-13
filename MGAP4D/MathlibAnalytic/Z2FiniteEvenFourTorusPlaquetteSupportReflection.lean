import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTimeReflection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Plaquettes of the even four-dimensional torus. -/
abbrev FiniteEvenFourTorusPlaquette (H : ℕ) : Type :=
  FiniteFourTorusPlaquette (2 * H + 1)

/-- Strictly positive periodic times are represented by `1, ..., H`.
The fixed slices `0` and `H+1` are deliberately excluded. -/
def finiteEvenFourTorusStrictPositiveTime
    (H : ℕ) (t : ZMod ((2 * H + 1) + 1)) : Prop :=
  ∃ k : Fin H,
    t = ((k.1 + 1 : ℕ) : ZMod ((2 * H + 1) + 1))

/-- Strictly negative periodic times are the reflected strict-positive times. -/
def finiteEvenFourTorusStrictNegativeTime
    (H : ℕ) (t : ZMod ((2 * H + 1) + 1)) : Prop :=
  finiteEvenFourTorusStrictPositiveTime H (-t)

/-- Strict vertex sectors, excluding both reflection planes. -/
def finiteEvenFourTorusStrictPositiveVertex
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) : Prop :=
  finiteEvenFourTorusStrictPositiveTime H (v 0)

def finiteEvenFourTorusStrictNegativeVertex
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) : Prop :=
  finiteEvenFourTorusStrictNegativeTime H (v 0)

/-- Time reflection exchanges the two strict vertex sectors. -/
@[simp]
theorem finiteEvenFourTorus_reflection_strictNegative_iff_strictPositive
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    finiteEvenFourTorusStrictNegativeVertex H
        (finiteEvenFourTorusTimeReflection H v) ↔
      finiteEvenFourTorusStrictPositiveVertex H v := by
  simp [finiteEvenFourTorusStrictNegativeVertex,
    finiteEvenFourTorusStrictPositiveVertex,
    finiteEvenFourTorusStrictNegativeTime]

@[simp]
theorem finiteEvenFourTorus_reflection_strictPositive_iff_strictNegative
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    finiteEvenFourTorusStrictPositiveVertex H
        (finiteEvenFourTorusTimeReflection H v) ↔
      finiteEvenFourTorusStrictNegativeVertex H v := by
  simp [finiteEvenFourTorusStrictNegativeVertex,
    finiteEvenFourTorusStrictPositiveVertex,
    finiteEvenFourTorusStrictNegativeTime]

/-- Reflect every vertex in a finite support list. -/
def finiteEvenFourTorusReflectVertexSupport
    (H : ℕ) (vertices : List (FiniteEvenFourTorusVertex H)) :
    List (FiniteEvenFourTorusVertex H) :=
  vertices.map (finiteEvenFourTorusTimeReflection H)

/-- Support reflection is involutive. -/
@[simp]
theorem finiteEvenFourTorusReflectVertexSupport_involutive
    (H : ℕ) (vertices : List (FiniteEvenFourTorusVertex H)) :
    finiteEvenFourTorusReflectVertexSupport H
        (finiteEvenFourTorusReflectVertexSupport H vertices) =
      vertices := by
  simp [finiteEvenFourTorusReflectVertexSupport,
    List.map_map, finiteEvenFourTorusTimeReflection_involutive]

/-- Every vertex of a support lies in the strict positive sector. -/
def finiteEvenFourTorusStrictPositiveSupport
    (H : ℕ) (vertices : List (FiniteEvenFourTorusVertex H)) : Prop :=
  ∀ v ∈ vertices, finiteEvenFourTorusStrictPositiveVertex H v

/-- Every vertex of a support lies in the strict negative sector. -/
def finiteEvenFourTorusStrictNegativeSupport
    (H : ℕ) (vertices : List (FiniteEvenFourTorusVertex H)) : Prop :=
  ∀ v ∈ vertices, finiteEvenFourTorusStrictNegativeVertex H v

/-- A support crosses a reflection plane when it is contained in neither open
half-torus. -/
def finiteEvenFourTorusCrossingSupport
    (H : ℕ) (vertices : List (FiniteEvenFourTorusVertex H)) : Prop :=
  ¬ finiteEvenFourTorusStrictPositiveSupport H vertices ∧
  ¬ finiteEvenFourTorusStrictNegativeSupport H vertices

/-- Reflection exchanges strict-positive and strict-negative supports. -/
@[simp]
theorem finiteEvenFourTorus_reflectSupport_strictNegative_iff_strictPositive
    (H : ℕ) (vertices : List (FiniteEvenFourTorusVertex H)) :
    finiteEvenFourTorusStrictNegativeSupport H
        (finiteEvenFourTorusReflectVertexSupport H vertices) ↔
      finiteEvenFourTorusStrictPositiveSupport H vertices := by
  simp [finiteEvenFourTorusStrictNegativeSupport,
    finiteEvenFourTorusStrictPositiveSupport,
    finiteEvenFourTorusReflectVertexSupport]

@[simp]
theorem finiteEvenFourTorus_reflectSupport_strictPositive_iff_strictNegative
    (H : ℕ) (vertices : List (FiniteEvenFourTorusVertex H)) :
    finiteEvenFourTorusStrictPositiveSupport H
        (finiteEvenFourTorusReflectVertexSupport H vertices) ↔
      finiteEvenFourTorusStrictNegativeSupport H vertices := by
  simp [finiteEvenFourTorusStrictNegativeSupport,
    finiteEvenFourTorusStrictPositiveSupport,
    finiteEvenFourTorusReflectVertexSupport]

/-- Reflection preserves the crossing-support condition. -/
@[simp]
theorem finiteEvenFourTorus_reflectSupport_crossing_iff
    (H : ℕ) (vertices : List (FiniteEvenFourTorusVertex H)) :
    finiteEvenFourTorusCrossingSupport H
        (finiteEvenFourTorusReflectVertexSupport H vertices) ↔
      finiteEvenFourTorusCrossingSupport H vertices := by
  simpa only [finiteEvenFourTorusCrossingSupport,
    finiteEvenFourTorus_reflectSupport_strictPositive_iff_strictNegative,
    finiteEvenFourTorus_reflectSupport_strictNegative_iff_strictPositive,
    and_comm]

/-- Ordered vertex support of an even-torus plaquette. -/
def finiteEvenFourTorusPlaquetteVertices
    {H : ℕ} (p : FiniteEvenFourTorusPlaquette H) :
    List (FiniteEvenFourTorusVertex H) :=
  finiteFourTorusPlaquetteVertices p

/-- Reflected ordered vertex support of an even-torus plaquette. -/
def finiteEvenFourTorusPlaquetteReflectedVertices
    {H : ℕ} (p : FiniteEvenFourTorusPlaquette H) :
    List (FiniteEvenFourTorusVertex H) :=
  finiteEvenFourTorusReflectVertexSupport H
    (finiteFourTorusPlaquetteVertices p)

/-- Reflecting the reflected support returns the original plaquette support. -/
@[simp]
theorem finiteEvenFourTorusPlaquetteReflectedVertices_involutive
    {H : ℕ} (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusReflectVertexSupport H
        (finiteEvenFourTorusPlaquetteReflectedVertices p) =
      finiteFourTorusPlaquetteVertices p := by
  simp [finiteEvenFourTorusPlaquetteReflectedVertices]

/-- Plaquette-support sector predicates. -/
def finiteEvenFourTorusStrictPositivePlaquette
    {H : ℕ} (p : FiniteEvenFourTorusPlaquette H) : Prop :=
  finiteEvenFourTorusStrictPositiveSupport H
    (finiteEvenFourTorusPlaquetteVertices p)

def finiteEvenFourTorusStrictNegativePlaquette
    {H : ℕ} (p : FiniteEvenFourTorusPlaquette H) : Prop :=
  finiteEvenFourTorusStrictNegativeSupport H
    (finiteEvenFourTorusPlaquetteVertices p)

def finiteEvenFourTorusCrossingPlaquette
    {H : ℕ} (p : FiniteEvenFourTorusPlaquette H) : Prop :=
  finiteEvenFourTorusCrossingSupport H
    (finiteEvenFourTorusPlaquetteVertices p)

/-- The reflected support of a positive plaquette is strictly negative. -/
theorem finiteEvenFourTorusPlaquette_reflectedNegative_iff_positive
    {H : ℕ} (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusStrictNegativeSupport H
        (finiteEvenFourTorusPlaquetteReflectedVertices p) ↔
      finiteEvenFourTorusStrictPositivePlaquette p := by
  simp [finiteEvenFourTorusPlaquetteReflectedVertices,
    finiteEvenFourTorusStrictPositivePlaquette]

/-- The reflected support of a negative plaquette is strictly positive. -/
theorem finiteEvenFourTorusPlaquette_reflectedPositive_iff_negative
    {H : ℕ} (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusStrictPositiveSupport H
        (finiteEvenFourTorusPlaquetteReflectedVertices p) ↔
      finiteEvenFourTorusStrictNegativePlaquette p := by
  simp [finiteEvenFourTorusPlaquetteReflectedVertices,
    finiteEvenFourTorusStrictNegativePlaquette]

/-- Crossing plaquette supports remain crossing after reflection. -/
theorem finiteEvenFourTorusPlaquette_reflectedCrossing_iff
    {H : ℕ} (p : FiniteEvenFourTorusPlaquette H) :
    finiteEvenFourTorusCrossingSupport H
        (finiteEvenFourTorusPlaquetteReflectedVertices p) ↔
      finiteEvenFourTorusCrossingPlaquette p := by
  simp [finiteEvenFourTorusPlaquetteReflectedVertices,
    finiteEvenFourTorusCrossingPlaquette]

end

end MathlibAnalytic
end MGAP4D

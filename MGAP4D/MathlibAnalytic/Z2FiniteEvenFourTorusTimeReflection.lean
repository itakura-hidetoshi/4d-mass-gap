import MGAP4D.MathlibAnalytic.Z2FiniteFourDimensionalTorusLattice

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- An even four-dimensional torus with time circumference `2(H+1)`.  The
existing torus parameter is chosen as `N = 2H+1`, so that `N+1 = 2(H+1)`. -/
abbrev FiniteEvenFourTorusVertex (H : ℕ) : Type :=
  FiniteFourTorusVertex (2 * H + 1)

abbrev FiniteEvenFourTorusEdge (H : ℕ) : Type :=
  FiniteFourTorusEdge (2 * H + 1)

abbrev FiniteEvenFourTorusConfiguration (H : ℕ) : Type :=
  FiniteEvenFourTorusEdge H → Z2Gauge

/-- Time reflection negates the periodic time coordinate and leaves all spatial
coordinates unchanged. -/
def finiteEvenFourTorusTimeReflection
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    FiniteEvenFourTorusVertex H :=
  fun i => if i = 0 then -v i else v i

@[simp]
theorem finiteEvenFourTorusTimeReflection_time
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    finiteEvenFourTorusTimeReflection H v 0 = -v 0 := by
  simp [finiteEvenFourTorusTimeReflection]

@[simp]
theorem finiteEvenFourTorusTimeReflection_space
    (H : ℕ) (v : FiniteEvenFourTorusVertex H)
    {i : Fin 4} (hi : i ≠ 0) :
    finiteEvenFourTorusTimeReflection H v i = v i := by
  simp [finiteEvenFourTorusTimeReflection, hi]

/-- Time reflection is an involution on the even torus. -/
theorem finiteEvenFourTorusTimeReflection_involutive
    (H : ℕ) :
    Function.Involutive (finiteEvenFourTorusTimeReflection H) := by
  intro v
  funext i
  by_cases hi : i = 0
  · subst i
    simp [finiteEvenFourTorusTimeReflection]
  · simp [finiteEvenFourTorusTimeReflection, hi]

/-- Positive periodic times are the residue classes represented by
`1, ..., H+1`. -/
def finiteEvenFourTorusPositiveTime
    (H : ℕ) (t : ZMod ((2 * H + 1) + 1)) : Prop :=
  ∃ k : Fin (H + 1),
    t = ((k.1 + 1 : ℕ) : ZMod ((2 * H + 1) + 1))

/-- Negative periodic times are defined as the reflection image of the positive
sector.  This avoids choosing a noncanonical integer representative. -/
def finiteEvenFourTorusNegativeTime
    (H : ℕ) (t : ZMod ((2 * H + 1) + 1)) : Prop :=
  finiteEvenFourTorusPositiveTime H (-t)

/-- The primary reflection plane is the zero-time slice. -/
def finiteEvenFourTorusOnPrimaryReflectionPlane
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) : Prop :=
  v 0 = 0

/-- The antipodal reflection plane is the half-period slice `H+1`. -/
def finiteEvenFourTorusOnAntipodalReflectionPlane
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) : Prop :=
  v 0 = ((H + 1 : ℕ) : ZMod ((2 * H + 1) + 1))

/-- Vertex-side predicates induced by the periodic time sectors. -/
def finiteEvenFourTorusPositiveVertex
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) : Prop :=
  finiteEvenFourTorusPositiveTime H (v 0)

def finiteEvenFourTorusNegativeVertex
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) : Prop :=
  finiteEvenFourTorusNegativeTime H (v 0)

/-- Reflection swaps the positive and negative vertex sectors. -/
theorem finiteEvenFourTorus_reflection_negative_iff_positive
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    finiteEvenFourTorusNegativeVertex H
        (finiteEvenFourTorusTimeReflection H v) ↔
      finiteEvenFourTorusPositiveVertex H v := by
  simp [finiteEvenFourTorusNegativeVertex,
    finiteEvenFourTorusPositiveVertex,
    finiteEvenFourTorusNegativeTime]

/-- Reflection fixes the primary time slice pointwise. -/
theorem finiteEvenFourTorus_primaryPlane_fixed
    (H : ℕ) (v : FiniteEvenFourTorusVertex H)
    (hv : finiteEvenFourTorusOnPrimaryReflectionPlane H v) :
    finiteEvenFourTorusTimeReflection H v = v := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [finiteEvenFourTorusOnPrimaryReflectionPlane] at hv
    simp [finiteEvenFourTorusTimeReflection, hv]
  · simp [finiteEvenFourTorusTimeReflection, hi]

/-- Reflection of a directed endpoint-pair edge. -/
def finiteEvenFourTorusEdgeReflection
    (H : ℕ) (e : FiniteEvenFourTorusEdge H) :
    FiniteEvenFourTorusEdge H :=
  (finiteEvenFourTorusTimeReflection H e.1,
    finiteEvenFourTorusTimeReflection H e.2)

/-- Edge reflection is involutive. -/
theorem finiteEvenFourTorusEdgeReflection_involutive
    (H : ℕ) :
    Function.Involutive (finiteEvenFourTorusEdgeReflection H) := by
  intro e
  rcases e with ⟨s, t⟩
  change
    (finiteEvenFourTorusTimeReflection H
        (finiteEvenFourTorusTimeReflection H s),
      finiteEvenFourTorusTimeReflection H
        (finiteEvenFourTorusTimeReflection H t)) = (s, t)
  rw [finiteEvenFourTorusTimeReflection_involutive H s,
    finiteEvenFourTorusTimeReflection_involutive H t]

/-- Pullback reflection on `Z₂` edge configurations. -/
def finiteEvenFourTorusConfigurationReflection
    (H : ℕ) (A : FiniteEvenFourTorusConfiguration H) :
    FiniteEvenFourTorusConfiguration H :=
  fun e => A (finiteEvenFourTorusEdgeReflection H e)

/-- Configuration reflection is involutive. -/
theorem finiteEvenFourTorusConfigurationReflection_involutive
    (H : ℕ) :
    Function.Involutive (finiteEvenFourTorusConfigurationReflection H) := by
  intro A
  funext e
  simp [finiteEvenFourTorusConfigurationReflection,
    finiteEvenFourTorusEdgeReflection_involutive H e]

end

end MathlibAnalytic
end MGAP4D

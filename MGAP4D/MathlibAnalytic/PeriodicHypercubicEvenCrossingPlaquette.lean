import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTimeReflection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The primary site-reflection plane is the zero-time slice. -/
def periodicHypercubicEvenOnPrimaryReflectionPlane
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) : Prop :=
  v 0 = 0

/-- The antipodal fixed plane is the half-period slice `H+1`. -/
def periodicHypercubicEvenOnAntipodalReflectionPlane
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) : Prop :=
  v 0 = ((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))

/-- Strictly positive periodic times are represented by `1, ..., H`; the two
fixed reflection slices are excluded. -/
def periodicHypercubicEvenStrictPositiveTime
    (H : ℕ) (t : ZMod (PeriodicHypercubicEvenSideLength H)) : Prop :=
  ∃ k : Fin H,
    t = ((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))

/-- Strictly negative periodic times are the reflection images of strictly
positive times. -/
def periodicHypercubicEvenStrictNegativeTime
    (H : ℕ) (t : ZMod (PeriodicHypercubicEvenSideLength H)) : Prop :=
  periodicHypercubicEvenStrictPositiveTime H (-t)

/-- Open positive and negative vertex sectors. -/
def periodicHypercubicEvenStrictPositiveVertex
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) : Prop :=
  periodicHypercubicEvenStrictPositiveTime H (v 0)

def periodicHypercubicEvenStrictNegativeVertex
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) : Prop :=
  periodicHypercubicEvenStrictNegativeTime H (v 0)

/-- Site reflection exchanges the two open half-tori. -/
@[simp]
theorem periodicHypercubicEven_reflection_strictNegative_iff_strictPositive
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenStrictNegativeVertex H
        (periodicHypercubicEvenTimeReflection H v) ↔
      periodicHypercubicEvenStrictPositiveVertex H v := by
  simp [periodicHypercubicEvenStrictNegativeVertex,
    periodicHypercubicEvenStrictPositiveVertex,
    periodicHypercubicEvenStrictNegativeTime]

@[simp]
theorem periodicHypercubicEven_reflection_strictPositive_iff_strictNegative
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenStrictPositiveVertex H
        (periodicHypercubicEvenTimeReflection H v) ↔
      periodicHypercubicEvenStrictNegativeVertex H v := by
  simp [periodicHypercubicEvenStrictNegativeVertex,
    periodicHypercubicEvenStrictPositiveVertex,
    periodicHypercubicEvenStrictNegativeTime]

/-- Reflect every vertex of a finite support list. -/
def periodicHypercubicEvenReflectVertexSupport
    (H : ℕ) (vertices : List (PeriodicHypercubicEvenVertex H)) :
    List (PeriodicHypercubicEvenVertex H) :=
  vertices.map (periodicHypercubicEvenTimeReflection H)

/-- Reflection of finite supports is involutive. -/
@[simp]
theorem periodicHypercubicEvenReflectVertexSupport_involutive
    (H : ℕ) (vertices : List (PeriodicHypercubicEvenVertex H)) :
    periodicHypercubicEvenReflectVertexSupport H
        (periodicHypercubicEvenReflectVertexSupport H vertices) = vertices := by
  simp [periodicHypercubicEvenReflectVertexSupport, List.map_map,
    periodicHypercubicEvenTimeReflection_involutive]

/-- Every support vertex lies in the strict positive open half-torus. -/
def periodicHypercubicEvenStrictPositiveSupport
    (H : ℕ) (vertices : List (PeriodicHypercubicEvenVertex H)) : Prop :=
  ∀ v ∈ vertices, periodicHypercubicEvenStrictPositiveVertex H v

/-- Every support vertex lies in the strict negative open half-torus. -/
def periodicHypercubicEvenStrictNegativeSupport
    (H : ℕ) (vertices : List (PeriodicHypercubicEvenVertex H)) : Prop :=
  ∀ v ∈ vertices, periodicHypercubicEvenStrictNegativeVertex H v

/-- A finite support crosses a reflection plane when it belongs to neither open
half-torus. -/
def periodicHypercubicEvenCrossingSupport
    (H : ℕ) (vertices : List (PeriodicHypercubicEvenVertex H)) : Prop :=
  ¬ periodicHypercubicEvenStrictPositiveSupport H vertices ∧
    ¬ periodicHypercubicEvenStrictNegativeSupport H vertices

/-- Reflection exchanges positive and negative finite supports. -/
@[simp]
theorem periodicHypercubicEven_reflectSupport_strictNegative_iff_strictPositive
    (H : ℕ) (vertices : List (PeriodicHypercubicEvenVertex H)) :
    periodicHypercubicEvenStrictNegativeSupport H
        (periodicHypercubicEvenReflectVertexSupport H vertices) ↔
      periodicHypercubicEvenStrictPositiveSupport H vertices := by
  simp [periodicHypercubicEvenStrictNegativeSupport,
    periodicHypercubicEvenStrictPositiveSupport,
    periodicHypercubicEvenReflectVertexSupport]

@[simp]
theorem periodicHypercubicEven_reflectSupport_strictPositive_iff_strictNegative
    (H : ℕ) (vertices : List (PeriodicHypercubicEvenVertex H)) :
    periodicHypercubicEvenStrictPositiveSupport H
        (periodicHypercubicEvenReflectVertexSupport H vertices) ↔
      periodicHypercubicEvenStrictNegativeSupport H vertices := by
  simp [periodicHypercubicEvenStrictNegativeSupport,
    periodicHypercubicEvenStrictPositiveSupport,
    periodicHypercubicEvenReflectVertexSupport]

/-- Reflection preserves the crossing-support condition. -/
@[simp]
theorem periodicHypercubicEven_reflectSupport_crossing_iff
    (H : ℕ) (vertices : List (PeriodicHypercubicEvenVertex H)) :
    periodicHypercubicEvenCrossingSupport H
        (periodicHypercubicEvenReflectVertexSupport H vertices) ↔
      periodicHypercubicEvenCrossingSupport H vertices := by
  simpa only [periodicHypercubicEvenCrossingSupport,
    periodicHypercubicEven_reflectSupport_strictPositive_iff_strictNegative,
    periodicHypercubicEven_reflectSupport_strictNegative_iff_strictPositive,
    and_comm]

/-- Four ordered vertices of a positively oriented periodic plaquette. -/
def periodicHypercubicEvenPlaquetteCorner00
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    PeriodicHypercubicEvenVertex H :=
  p.1

def periodicHypercubicEvenPlaquetteCorner10
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    PeriodicHypercubicEvenVertex H :=
  periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) p.1
    (periodicHypercubicPlaquetteFirstAxis p)

def periodicHypercubicEvenPlaquetteCorner11
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    PeriodicHypercubicEvenVertex H :=
  periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
    (periodicHypercubicEvenPlaquetteCorner10 p)
    (periodicHypercubicPlaquetteSecondAxis p)

def periodicHypercubicEvenPlaquetteCorner01
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    PeriodicHypercubicEvenVertex H :=
  periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) p.1
    (periodicHypercubicPlaquetteSecondAxis p)

/-- Ordered vertex support of a periodic plaquette. -/
def periodicHypercubicEvenPlaquetteVertices
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    List (PeriodicHypercubicEvenVertex H) :=
  [periodicHypercubicEvenPlaquetteCorner00 p,
    periodicHypercubicEvenPlaquetteCorner10 p,
    periodicHypercubicEvenPlaquetteCorner11 p,
    periodicHypercubicEvenPlaquetteCorner01 p]

/-- Plaquette support lies wholly in the positive open half-torus. -/
def periodicHypercubicEvenStrictPositivePlaquette
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenStrictPositiveSupport H
    (periodicHypercubicEvenPlaquetteVertices p)

/-- Plaquette support lies wholly in the negative open half-torus. -/
def periodicHypercubicEvenStrictNegativePlaquette
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenStrictNegativeSupport H
    (periodicHypercubicEvenPlaquetteVertices p)

/-- Plaquette support crosses one of the two site-reflection planes. -/
def periodicHypercubicEvenCrossingPlaquette
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenCrossingSupport H
    (periodicHypercubicEvenPlaquetteVertices p)

/-- Finite label type of all crossing plaquettes at side length `2(H+1)`. -/
abbrev PeriodicHypercubicEvenCrossingPlaquetteLabel (H : ℕ) : Type :=
  {p : PeriodicHypercubicEvenPlaquette H //
    periodicHypercubicEvenCrossingPlaquette p}

/-- Canonical finite enumeration of crossing plaquette labels. -/
noncomputable instance periodicHypercubicEvenCrossingPlaquetteLabelFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenCrossingPlaquetteLabel H) := by
  classical
  exact Subtype.fintype periodicHypercubicEvenCrossingPlaquette

/-- Canonical finite ordered list of all crossing plaquette labels. -/
noncomputable def periodicHypercubicEvenCrossingPlaquetteList
    (H : ℕ) : List (PeriodicHypercubicEvenCrossingPlaquetteLabel H) := by
  classical
  exact Finset.univ.toList

@[simp]
theorem periodicHypercubicEvenCrossingPlaquette_mem_list
    (H : ℕ) (p : PeriodicHypercubicEvenCrossingPlaquetteLabel H) :
    p ∈ periodicHypercubicEvenCrossingPlaquetteList H := by
  classical
  simp [periodicHypercubicEvenCrossingPlaquetteList]

end

end MathlibAnalytic
end MGAP4D
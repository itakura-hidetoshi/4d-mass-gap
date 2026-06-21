import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTimeReflection
import MGAP4D.MathlibAnalytic.Z2FiniteInvolutiveEdgeOrbitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Reflection of a physical positively oriented periodic link.

Spatial links retain their positive orientation after reflecting the initial
vertex.  A positive time link is reflected to a negatively traversed link, so
its canonical positive-link representative starts one time step behind the
reflected initial vertex. -/
def periodicHypercubicEvenEdgeReflection
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    PeriodicHypercubicEvenEdge H :=
  if e.2 = 0 then
    (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenTimeReflection H e.1) 0, e.2)
  else
    (periodicHypercubicEvenTimeReflection H e.1, e.2)

@[simp]
theorem periodicHypercubicEvenEdgeReflection_direction
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    (periodicHypercubicEvenEdgeReflection H e).2 = e.2 := by
  by_cases htime : e.2 = 0 <;>
    simp [periodicHypercubicEvenEdgeReflection, htime]

@[simp]
theorem periodicHypercubicEvenEdgeReflection_spatial
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0) :
    periodicHypercubicEvenEdgeReflection H e =
      (periodicHypercubicEvenTimeReflection H e.1, e.2) := by
  simp [periodicHypercubicEvenEdgeReflection, hspace]

@[simp]
theorem periodicHypercubicEvenEdgeReflection_time
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenEdgeReflection H (v, 0) =
      (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenTimeReflection H v) 0, 0) := by
  simp [periodicHypercubicEvenEdgeReflection]

/-- The positive-link edge reflection is involutive. -/
theorem periodicHypercubicEvenEdgeReflection_involutive
    (H : ℕ) :
    Function.Involutive (periodicHypercubicEvenEdgeReflection H) := by
  intro e
  rcases e with ⟨v, mu⟩
  by_cases htime : mu = 0
  · subst mu
    apply Prod.ext
    · simp only [periodicHypercubicEvenEdgeReflection_time]
      rw [periodicHypercubicEvenTimeReflection_unshift_time]
      rw [periodicHypercubicUnshift_shift]
      exact periodicHypercubicEvenTimeReflection_involutive H v
    · rfl
  · apply Prod.ext
    · rw [periodicHypercubicEvenEdgeReflection_spatial H (v, mu) htime]
      rw [periodicHypercubicEvenEdgeReflection_spatial H
        (periodicHypercubicEvenTimeReflection H v, mu) htime]
      exact periodicHypercubicEvenTimeReflection_involutive H v
    · simp [periodicHypercubicEvenEdgeReflection, htime]

/-- Geometric time rank of a physical positive link, given by the canonical
residue representative of its initial time coordinate. -/
def periodicHypercubicEvenEdgeTimeRank
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) : ℕ :=
  (e.1 0).val

/-- Reflection-compatible geometric side of a physical positive link.  Strict
rank comparison chooses one member of each non-fixed orbit; rank ties form the
shared reflection-fixed boundary sector. -/
def periodicHypercubicEvenEdgeSide
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) : ReflectionEdgeSide :=
  finiteInvolutiveEdgeRankSide
    (periodicHypercubicEvenEdgeReflection H)
    (periodicHypercubicEvenEdgeTimeRank H)
    e

@[simp]
theorem periodicHypercubicEvenEdgeSide_reflection
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenEdgeSide H
        (periodicHypercubicEvenEdgeReflection H e) =
      match periodicHypercubicEvenEdgeSide H e with
      | .positive => .negative
      | .negative => .positive
      | .fixed => .fixed := by
  exact finiteInvolutiveEdgeRankSide_reflection
    (periodicHypercubicEvenEdgeReflection H)
    (periodicHypercubicEvenEdgeReflection_involutive H)
    (periodicHypercubicEvenEdgeTimeRank H)
    e

/-- Concrete finite reflection-orbit partition of the physical positive links
on the even periodic four-dimensional lattice. -/
def periodicHypercubicEvenEdgeOrbitPartition
    (H : ℕ) :
    FiniteInvolutiveEdgeOrbitPartition (PeriodicHypercubicEvenEdge H) where
  reflection := periodicHypercubicEvenEdgeReflection H
  reflection_involutive := periodicHypercubicEvenEdgeReflection_involutive H
  side := periodicHypercubicEvenEdgeSide H
  side_reflection := periodicHypercubicEvenEdgeSide_reflection H

end

end MathlibAnalytic
end MGAP4D

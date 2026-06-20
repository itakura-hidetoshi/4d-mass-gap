import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingPlaquette
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A spatial shift commutes with a backward time shift on the periodic lattice. -/
theorem periodicHypercubicEven_shift_unshift_time_comm
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H) v 0) mu =
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v mu) 0 := by
  unfold periodicHypercubicShift periodicHypercubicUnshift
  abel

/- The reflected plaquette has exactly the time-reflected vertex support of the
original plaquette, up to ordering.  The local budget is used only for this
finite four-corner normalization. -/
set_option maxHeartbeats 2000000 in
theorem periodicHypercubicEvenPlaquetteReflection_vertices_mem_iff
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H)
    (v : PeriodicHypercubicEvenVertex H) :
    v ∈ periodicHypercubicEvenPlaquetteVertices
        (periodicHypercubicEvenPlaquetteReflection H p) ↔
      v ∈ periodicHypercubicEvenReflectVertexSupport H
        (periodicHypercubicEvenPlaquetteVertices p) := by
  classical
  rcases p with ⟨base, ⟨⟨mu, nu⟩, hmunu⟩⟩
  by_cases hmu : mu = 0
  · subst mu
    have hnu : nu ≠ 0 := by
      intro h
      subst nu
      exact (lt_irrefl (0 : PeriodicHypercubicAxis)) hmunu
    simp [periodicHypercubicEvenPlaquetteVertices,
      periodicHypercubicEvenPlaquetteCorner00,
      periodicHypercubicEvenPlaquetteCorner10,
      periodicHypercubicEvenPlaquetteCorner11,
      periodicHypercubicEvenPlaquetteCorner01,
      periodicHypercubicPlaquetteFirstAxis,
      periodicHypercubicPlaquetteSecondAxis,
      periodicHypercubicEvenReflectVertexSupport,
      periodicHypercubicEvenPlaquetteReflection,
      periodicHypercubicEvenReflectedPlaquetteBase,
      periodicHypercubicEvenPlaquetteHasTimeDirection,
      hnu,
      periodicHypercubicEvenTimeReflection_shift_spatial,
      periodicHypercubicEvenTimeReflection_shift_time,
      periodicHypercubicShift_unshift,
      periodicHypercubicUnshift_shift,
      periodicHypercubicEven_shift_unshift_time_comm,
      periodicHypercubicShift_comm,
      or_assoc, or_left_comm, or_comm]
  · have hnu : nu ≠ 0 := by
      intro h
      subst nu
      exact (Fin.not_lt_zero mu) hmunu
    simp [periodicHypercubicEvenPlaquetteVertices,
      periodicHypercubicEvenPlaquetteCorner00,
      periodicHypercubicEvenPlaquetteCorner10,
      periodicHypercubicEvenPlaquetteCorner11,
      periodicHypercubicEvenPlaquetteCorner01,
      periodicHypercubicPlaquetteFirstAxis,
      periodicHypercubicPlaquetteSecondAxis,
      periodicHypercubicEvenReflectVertexSupport,
      periodicHypercubicEvenPlaquetteReflection,
      periodicHypercubicEvenReflectedPlaquetteBase,
      periodicHypercubicEvenPlaquetteHasTimeDirection,
      hmu, hnu,
      periodicHypercubicEvenTimeReflection_shift_spatial,
      periodicHypercubicShift_comm,
      or_assoc, or_left_comm, or_comm]

/-- Strict-positive support is transported to strict-positive support of the
reflected vertex list. -/
theorem periodicHypercubicEvenPlaquetteReflection_strictPositiveSupport_iff
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenStrictPositiveSupport H
        (periodicHypercubicEvenPlaquetteVertices
          (periodicHypercubicEvenPlaquetteReflection H p)) ↔
      periodicHypercubicEvenStrictPositiveSupport H
        (periodicHypercubicEvenReflectVertexSupport H
          (periodicHypercubicEvenPlaquetteVertices p)) := by
  constructor
  · intro h v hv
    exact h v
      ((periodicHypercubicEvenPlaquetteReflection_vertices_mem_iff H p v).2 hv)
  · intro h v hv
    exact h v
      ((periodicHypercubicEvenPlaquetteReflection_vertices_mem_iff H p v).1 hv)

/-- Strict-negative support is transported to strict-negative support of the
reflected vertex list. -/
theorem periodicHypercubicEvenPlaquetteReflection_strictNegativeSupport_iff
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenStrictNegativeSupport H
        (periodicHypercubicEvenPlaquetteVertices
          (periodicHypercubicEvenPlaquetteReflection H p)) ↔
      periodicHypercubicEvenStrictNegativeSupport H
        (periodicHypercubicEvenReflectVertexSupport H
          (periodicHypercubicEvenPlaquetteVertices p)) := by
  constructor
  · intro h v hv
    exact h v
      ((periodicHypercubicEvenPlaquetteReflection_vertices_mem_iff H p v).2 hv)
  · intro h v hv
    exact h v
      ((periodicHypercubicEvenPlaquetteReflection_vertices_mem_iff H p v).1 hv)

/-- Orientation-corrected plaquette reflection preserves the geometric crossing
condition. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_crossing_iff
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenCrossingPlaquette
        (periodicHypercubicEvenPlaquetteReflection H p) ↔
      periodicHypercubicEvenCrossingPlaquette p := by
  unfold periodicHypercubicEvenCrossingPlaquette
  rw [show
    periodicHypercubicEvenCrossingSupport H
        (periodicHypercubicEvenPlaquetteVertices
          (periodicHypercubicEvenPlaquetteReflection H p)) ↔
      periodicHypercubicEvenCrossingSupport H
        (periodicHypercubicEvenReflectVertexSupport H
          (periodicHypercubicEvenPlaquetteVertices p)) by
    unfold periodicHypercubicEvenCrossingSupport
    rw [periodicHypercubicEvenPlaquetteReflection_strictPositiveSupport_iff,
      periodicHypercubicEvenPlaquetteReflection_strictNegativeSupport_iff]]
  exact periodicHypercubicEven_reflectSupport_crossing_iff H
    (periodicHypercubicEvenPlaquetteVertices p)

/-- Reflection on the finite subtype of crossing plaquette labels. -/
def periodicHypercubicEvenCrossingPlaquetteReflection
    (H : ℕ) (p : PeriodicHypercubicEvenCrossingPlaquetteLabel H) :
    PeriodicHypercubicEvenCrossingPlaquetteLabel H :=
  ⟨periodicHypercubicEvenPlaquetteReflection H p.1,
    (periodicHypercubicEvenPlaquetteReflection_crossing_iff H p.1).2 p.2⟩

/-- Reflection on crossing plaquette labels is involutive. -/
theorem periodicHypercubicEvenCrossingPlaquetteReflection_involutive
    (H : ℕ) :
    Function.Involutive
      (periodicHypercubicEvenCrossingPlaquetteReflection H) := by
  intro p
  apply Subtype.ext
  exact periodicHypercubicEvenPlaquetteReflection_involutive H p.1

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOpenHalfPlaquetteReflection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The strict positive and strict negative periodic-time sectors are disjoint.

If `t = k + 1` and `-t = l + 1`, then the characteristic
`2 * (H + 1)` divides `(k + 1) + (l + 1)`.  This sum is positive and strictly
smaller than the characteristic, which is impossible. -/
theorem periodicHypercubicEvenStrictPositiveTime_not_strictNegativeTime
    (H : ℕ) (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (hpos : periodicHypercubicEvenStrictPositiveTime H t) :
    ¬ periodicHypercubicEvenStrictNegativeTime H t := by
  intro hneg
  rcases hpos with ⟨k, hk⟩
  rcases hneg with ⟨l, hl⟩
  let a : ℕ := k.1 + 1
  let b : ℕ := l.1 + 1
  have hzero :
      ((a + b : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) = 0 := by
    rw [Nat.cast_add]
    change ((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) +
        ((l.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) = 0
    rw [← hk, ← hl]
    exact add_neg_cancel t
  have hdvd : PeriodicHypercubicEvenSideLength H ∣ a + b :=
    (CharP.cast_eq_zero_iff
      (ZMod (PeriodicHypercubicEvenSideLength H))
      (PeriodicHypercubicEvenSideLength H)
      (a + b)).1 hzero
  have hab_pos : 0 < a + b := by
    dsimp [a, b]
    omega
  have hside_le : PeriodicHypercubicEvenSideLength H ≤ a + b :=
    Nat.le_of_dvd hab_pos hdvd
  have hklt : k.1 < H := k.2
  have hllt : l.1 < H := l.2
  dsimp [PeriodicHypercubicEvenSideLength, a, b] at hside_le
  omega

/-- The strict positive and strict negative vertex sectors are disjoint. -/
theorem periodicHypercubicEvenStrictPositiveVertex_not_strictNegativeVertex
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    (hpos : periodicHypercubicEvenStrictPositiveVertex H v) :
    ¬ periodicHypercubicEvenStrictNegativeVertex H v :=
  periodicHypercubicEvenStrictPositiveTime_not_strictNegativeTime H (v 0) hpos

/-- A plaquette cannot lie wholly in both strict open half-tori. -/
theorem periodicHypercubicEvenStrictPositivePlaquette_not_strictNegativePlaquette
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H)
    (hpos : periodicHypercubicEvenStrictPositivePlaquette p) :
    ¬ periodicHypercubicEvenStrictNegativePlaquette p := by
  intro hneg
  have hbase_pos : periodicHypercubicEvenStrictPositiveVertex H p.1 := by
    exact hpos p.1 (by simp [periodicHypercubicEvenPlaquetteVertices,
      periodicHypercubicEvenPlaquetteCorner00])
  have hbase_neg : periodicHypercubicEvenStrictNegativeVertex H p.1 := by
    exact hneg p.1 (by simp [periodicHypercubicEvenPlaquetteVertices,
      periodicHypercubicEvenPlaquetteCorner00])
  exact periodicHypercubicEvenStrictPositiveVertex_not_strictNegativeVertex
    H p.1 hbase_pos hbase_neg

/-- Symmetric form of strict plaquette-sector disjointness. -/
theorem periodicHypercubicEvenStrictNegativePlaquette_not_strictPositivePlaquette
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H)
    (hneg : periodicHypercubicEvenStrictNegativePlaquette p) :
    ¬ periodicHypercubicEvenStrictPositivePlaquette p := by
  intro hpos
  exact periodicHypercubicEvenStrictPositivePlaquette_not_strictNegativePlaquette
    H p hpos hneg

end

end MathlibAnalytic
end MGAP4D

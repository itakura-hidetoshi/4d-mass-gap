import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteArbitraryAxisShift
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Repeated positive unit translation of one periodic vertex in a fixed
coordinate direction. -/
def periodicHypercubicShiftIterate
    (n : Nat)
    (x : PeriodicHypercubicVertex n)
    (rho : PeriodicHypercubicAxis) : Nat → PeriodicHypercubicVertex n
  | 0 => x
  | k + 1 => periodicHypercubicShift n
      (periodicHypercubicShiftIterate n x rho k) rho

@[simp] theorem periodicHypercubicShiftIterate_zero
    (n : Nat)
    (x : PeriodicHypercubicVertex n)
    (rho : PeriodicHypercubicAxis) :
    periodicHypercubicShiftIterate n x rho 0 = x :=
  rfl

@[simp] theorem periodicHypercubicShiftIterate_succ
    (n : Nat)
    (x : PeriodicHypercubicVertex n)
    (rho : PeriodicHypercubicAxis)
    (k : Nat) :
    periodicHypercubicShiftIterate n x rho (k + 1) =
      periodicHypercubicShift n
        (periodicHypercubicShiftIterate n x rho k) rho :=
  rfl

/-- Every finite repetition of a positive coordinate shift is reachable in the
periodic plaquette graph while preserving the plaquette plane. -/
theorem periodicHypercubicPlaquetteGraph_reachable_shift_iterate
    (n : Nat) (hn : 2 ≤ n)
    (p : PeriodicHypercubicPlaquette n)
    (rho : PeriodicHypercubicAxis)
    (k : Nat) :
    (periodicHypercubicPlaquetteGraph n).Reachable p
      (periodicHypercubicShiftIterate n p.1 rho k, p.2) := by
  induction k with
  | zero =>
      exact SimpleGraph.Reachable.rfl
  | succ k ih =>
      have hStep :
          (periodicHypercubicPlaquetteGraph n).Reachable
            (periodicHypercubicShiftIterate n p.1 rho k, p.2)
            (periodicHypercubicShift n
              (periodicHypercubicShiftIterate n p.1 rho k) rho, p.2) :=
        periodicHypercubicPlaquetteGraph_reachable_shift_axis n hn
          (periodicHypercubicShiftIterate n p.1 rho k, p.2) rho
      exact ih.trans hStep

/-- Coordinate formula for a repeated positive shift. The selected coordinate
increases by the natural shift count and every other coordinate is unchanged. -/
theorem periodicHypercubicShiftIterate_apply
    (n : Nat)
    (x : PeriodicHypercubicVertex n)
    (rho i : PeriodicHypercubicAxis)
    (k : Nat) :
    periodicHypercubicShiftIterate n x rho k i =
      x i + (k : ZMod n) * if i = rho then 1 else 0 := by
  induction k with
  | zero => simp [periodicHypercubicShiftIterate]
  | succ k ih =>
      rw [periodicHypercubicShiftIterate_succ,
        periodicHypercubicShift_apply, ih]
      by_cases h : i = rho
      · simp [h, Nat.cast_succ]
        ring
      · simp [h]

/-- At the shifted coordinate itself, repeated translation adds exactly the
natural shift count modulo the side length. -/
@[simp] theorem periodicHypercubicShiftIterate_apply_self
    (n : Nat)
    (x : PeriodicHypercubicVertex n)
    (rho : PeriodicHypercubicAxis)
    (k : Nat) :
    periodicHypercubicShiftIterate n x rho k rho =
      x rho + (k : ZMod n) := by
  simpa using periodicHypercubicShiftIterate_apply n x rho rho k

/-- Away from the shifted coordinate, repeated translation leaves the vertex
coordinate unchanged. -/
theorem periodicHypercubicShiftIterate_apply_of_ne
    (n : Nat)
    (x : PeriodicHypercubicVertex n)
    (rho i : PeriodicHypercubicAxis)
    (h : i ≠ rho)
    (k : Nat) :
    periodicHypercubicShiftIterate n x rho k i = x i := by
  simpa [h] using periodicHypercubicShiftIterate_apply n x rho i k

end

end MathlibAnalytic
end MGAP4D

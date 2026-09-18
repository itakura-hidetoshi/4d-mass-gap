import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveGraphGenerators
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteRepeatedAxisShift
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private def periodicHypercubicEvenSpatialDirectionOne :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨1, by decide⟩

private def periodicHypercubicEvenSpatialDirectionTwo :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨2, by decide⟩

/-- Every spatial direction has another spatial direction available.  This tiny
finite fact lets a link temporarily rotate its direction when the requested
base shift is parallel to the link itself. -/
theorem periodicHypercubicEvenSpatialDirection_exists_ne
    (mu : PeriodicHypercubicEvenSpatialDirection) :
    ∃ nu : PeriodicHypercubicEvenSpatialDirection, nu ≠ mu := by
  let one := periodicHypercubicEvenSpatialDirectionOne
  let two := periodicHypercubicEvenSpatialDirectionTwo
  by_cases h : mu = one
  · refine ⟨two, ?_⟩
    subst mu
    intro hEq
    have hVal := congrArg
      (fun z : PeriodicHypercubicEvenSpatialDirection => z.1) hEq
    have hNat := congrArg Fin.val hVal
    norm_num [one, two,
      periodicHypercubicEvenSpatialDirectionOne,
      periodicHypercubicEvenSpatialDirectionTwo] at hNat
  · exact ⟨one, Ne.symm h⟩

/-- A positive unit base shift in any spatial direction is reachable while
returning to the original link direction.

If the shift direction differs from the link direction, this is one graph
edge.  If they coincide, rotate to an auxiliary spatial direction, take the
opposite-edge plaquette shift, and rotate back. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_reachable_shiftBase
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu rho : PeriodicHypercubicEvenSpatialDirection) :
    (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
      (v, mu)
      (periodicHypercubicEvenSpatialSliceShift H v rho, mu) := by
  by_cases h : mu = rho
  · subst rho
    obtain ⟨nu, hnu⟩ :=
      periodicHypercubicEvenSpatialDirection_exists_ne mu
    have hRotate :
        (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
          (v, mu) (v, nu) :=
      periodicHypercubicEvenSpatialSliceActiveGraph_reachable_sameBase
        H v mu nu
    have hShift :
        (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
          (v, nu)
          (periodicHypercubicEvenSpatialSliceShift H v mu, nu) :=
      (periodicHypercubicEvenSpatialSliceActiveGraph_adj_shiftBase_of_direction_ne
        H v nu mu hnu).reachable
    have hRotateBack :
        (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
          (periodicHypercubicEvenSpatialSliceShift H v mu, nu)
          (periodicHypercubicEvenSpatialSliceShift H v mu, mu) :=
      periodicHypercubicEvenSpatialSliceActiveGraph_reachable_sameBase
        H (periodicHypercubicEvenSpatialSliceShift H v mu) nu mu
    exact hRotate.trans (hShift.trans hRotateBack)
  · exact
      (periodicHypercubicEvenSpatialSliceActiveGraph_adj_shiftBase_of_direction_ne
        H v mu rho h).reachable

/-- Repeated positive unit translation of a spatial-slice vertex in one fixed
spatial direction. -/
def periodicHypercubicEvenSpatialSliceShiftIterate
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (rho : PeriodicHypercubicEvenSpatialDirection) :
    Nat -> PeriodicHypercubicEvenSpatialSliceVertex H
  | 0 => v
  | k + 1 =>
      periodicHypercubicEvenSpatialSliceShift H
        (periodicHypercubicEvenSpatialSliceShiftIterate H v rho k) rho

@[simp] theorem periodicHypercubicEvenSpatialSliceShiftIterate_zero
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (rho : PeriodicHypercubicEvenSpatialDirection) :
    periodicHypercubicEvenSpatialSliceShiftIterate H v rho 0 = v :=
  rfl

@[simp] theorem periodicHypercubicEvenSpatialSliceShiftIterate_succ
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (rho : PeriodicHypercubicEvenSpatialDirection)
    (k : Nat) :
    periodicHypercubicEvenSpatialSliceShiftIterate H v rho (k + 1) =
      periodicHypercubicEvenSpatialSliceShift H
        (periodicHypercubicEvenSpatialSliceShiftIterate H v rho k) rho :=
  rfl

/-- Every finite repetition of a spatial base shift is reachable in the
intrinsic active graph while restoring the original link direction after each
step. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_reachable_shiftIterate
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu rho : PeriodicHypercubicEvenSpatialDirection)
    (k : Nat) :
    (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
      (v, mu)
      (periodicHypercubicEvenSpatialSliceShiftIterate H v rho k, mu) := by
  induction k with
  | zero =>
      exact SimpleGraph.Reachable.rfl
  | succ k ih =>
      have hStep :
          (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
            (periodicHypercubicEvenSpatialSliceShiftIterate H v rho k, mu)
            (periodicHypercubicEvenSpatialSliceShift H
              (periodicHypercubicEvenSpatialSliceShiftIterate H v rho k) rho, mu) :=
        periodicHypercubicEvenSpatialSliceActiveGraph_reachable_shiftBase
          H (periodicHypercubicEvenSpatialSliceShiftIterate H v rho k) mu rho
      exact ih.trans hStep

/-- The intrinsic repeated spatial shift is the restriction of the already
canonical full periodic vertex shift iterate. -/
theorem periodicHypercubicEvenSpatialSliceShiftIterate_coe
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (rho : PeriodicHypercubicEvenSpatialDirection)
    (k : Nat) :
    (periodicHypercubicEvenSpatialSliceShiftIterate H v rho k).1 =
      periodicHypercubicShiftIterate
        (PeriodicHypercubicEvenSideLength H) v.1 rho.1 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [periodicHypercubicEvenSpatialSliceShiftIterate_succ,
        periodicHypercubicEvenSpatialSliceShift_coe,
        periodicHypercubicShiftIterate_succ,
        ih]

/-- Coordinate formula at the repeatedly shifted spatial axis. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceShiftIterate_apply_self
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (rho : PeriodicHypercubicEvenSpatialDirection)
    (k : Nat) :
    (periodicHypercubicEvenSpatialSliceShiftIterate H v rho k).1 rho.1 =
      v.1 rho.1 + (k : ZMod (PeriodicHypercubicEvenSideLength H)) := by
  rw [periodicHypercubicEvenSpatialSliceShiftIterate_coe]
  exact
    periodicHypercubicShiftIterate_apply_self
      (PeriodicHypercubicEvenSideLength H) v.1 rho.1 k

/-- Every other full coordinate is unchanged by the repeated spatial shift. -/
theorem periodicHypercubicEvenSpatialSliceShiftIterate_apply_of_ne
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (rho : PeriodicHypercubicEvenSpatialDirection)
    (i : PeriodicHypercubicAxis)
    (h : i ≠ rho.1)
    (k : Nat) :
    (periodicHypercubicEvenSpatialSliceShiftIterate H v rho k).1 i =
      v.1 i := by
  rw [periodicHypercubicEvenSpatialSliceShiftIterate_coe]
  exact
    periodicHypercubicShiftIterate_apply_of_ne
      (PeriodicHypercubicEvenSideLength H) v.1 rho.1 i h k

end

end MathlibAnalytic
end MGAP4D

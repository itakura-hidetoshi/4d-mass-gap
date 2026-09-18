import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveGraphShiftReachability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance spatialSliceActiveGraphConnectivitySideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

private def periodicHypercubicEvenSpatialConnectivityDirectionOne :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨1, by decide⟩

private def periodicHypercubicEvenSpatialConnectivityDirectionTwo :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨2, by decide⟩

private def periodicHypercubicEvenSpatialConnectivityDirectionThree :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨3, by decide⟩

/-- Adjust one spatial coordinate of a time-zero spatial-slice vertex to its
value in a target spatial-slice vertex. -/
def periodicHypercubicEvenSpatialSliceAdjustCoordinate
    (H : ℕ)
    (x y : PeriodicHypercubicEvenSpatialSliceVertex H)
    (rho : PeriodicHypercubicEvenSpatialDirection) :
    PeriodicHypercubicEvenSpatialSliceVertex H :=
  periodicHypercubicEvenSpatialSliceShiftIterate
    H x rho (y.1 rho.1 - x.1 rho.1).val

/-- Spatial coordinate adjustment reaches the target coordinate exactly. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceAdjustCoordinate_apply_self
    (H : ℕ)
    (x y : PeriodicHypercubicEvenSpatialSliceVertex H)
    (rho : PeriodicHypercubicEvenSpatialDirection) :
    (periodicHypercubicEvenSpatialSliceAdjustCoordinate H x y rho).1 rho.1 =
      y.1 rho.1 := by
  rw [periodicHypercubicEvenSpatialSliceAdjustCoordinate,
    periodicHypercubicEvenSpatialSliceShiftIterate_apply_self]
  have hcast :
      (((y.1 rho.1 - x.1 rho.1).val : ℕ) :
        ZMod (PeriodicHypercubicEvenSideLength H)) =
          y.1 rho.1 - x.1 rho.1 := by
    simpa using
      (ZMod.natCast_val
        (R := ZMod (PeriodicHypercubicEvenSideLength H))
        (y.1 rho.1 - x.1 rho.1))
  rw [hcast]
  abel

/-- Adjusting one spatial coordinate leaves every other full coordinate
unchanged. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceAdjustCoordinate_apply_of_ne
    (H : ℕ)
    (x y : PeriodicHypercubicEvenSpatialSliceVertex H)
    (rho : PeriodicHypercubicEvenSpatialDirection)
    (i : PeriodicHypercubicAxis)
    (h : i ≠ rho.1) :
    (periodicHypercubicEvenSpatialSliceAdjustCoordinate H x y rho).1 i =
      x.1 i := by
  exact
    periodicHypercubicEvenSpatialSliceShiftIterate_apply_of_ne
      H x rho i h (y.1 rho.1 - x.1 rho.1).val

/-- One spatial-coordinate adjustment is reachable while preserving the chosen
link direction. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_reachable_adjustCoordinate
    (H : ℕ)
    (x y : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu rho : PeriodicHypercubicEvenSpatialDirection) :
    (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
      (x, mu)
      (periodicHypercubicEvenSpatialSliceAdjustCoordinate H x y rho, mu) := by
  exact
    periodicHypercubicEvenSpatialSliceActiveGraph_reachable_shiftIterate
      H x mu rho (y.1 rho.1 - x.1 rho.1).val

/-- Successively adjust the three spatial coordinates 1, 2 and 3.  The time
coordinate remains zero by construction. -/
def periodicHypercubicEvenSpatialSliceAdjustAllCoordinates
    (H : ℕ)
    (x y : PeriodicHypercubicEvenSpatialSliceVertex H) :
    PeriodicHypercubicEvenSpatialSliceVertex H :=
  let x1 :=
    periodicHypercubicEvenSpatialSliceAdjustCoordinate
      H x y periodicHypercubicEvenSpatialConnectivityDirectionOne
  let x2 :=
    periodicHypercubicEvenSpatialSliceAdjustCoordinate
      H x1 y periodicHypercubicEvenSpatialConnectivityDirectionTwo
  periodicHypercubicEvenSpatialSliceAdjustCoordinate
    H x2 y periodicHypercubicEvenSpatialConnectivityDirectionThree

/-- The three spatial-coordinate adjustments recover the target time-zero
spatial-slice vertex exactly. -/
theorem periodicHypercubicEvenSpatialSliceAdjustAllCoordinates_eq
    (H : ℕ)
    (x y : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenSpatialSliceAdjustAllCoordinates H x y = y := by
  apply Subtype.ext
  funext i
  fin_cases i
  · have hout :=
      (periodicHypercubicEvenSpatialSliceAdjustAllCoordinates H x y).2
    have hy := y.2
    unfold periodicHypercubicEvenOnPrimaryReflectionPlane at hout hy
    exact hout.trans hy.symm
  · simp [
      periodicHypercubicEvenSpatialSliceAdjustAllCoordinates,
      periodicHypercubicEvenSpatialConnectivityDirectionOne,
      periodicHypercubicEvenSpatialConnectivityDirectionTwo,
      periodicHypercubicEvenSpatialConnectivityDirectionThree]
  · simp [
      periodicHypercubicEvenSpatialSliceAdjustAllCoordinates,
      periodicHypercubicEvenSpatialConnectivityDirectionOne,
      periodicHypercubicEvenSpatialConnectivityDirectionTwo,
      periodicHypercubicEvenSpatialConnectivityDirectionThree]
  · simp [
      periodicHypercubicEvenSpatialSliceAdjustAllCoordinates,
      periodicHypercubicEvenSpatialConnectivityDirectionOne,
      periodicHypercubicEvenSpatialConnectivityDirectionTwo,
      periodicHypercubicEvenSpatialConnectivityDirectionThree]

/-- Any two spatial links with the same link direction are reachable by
successively matching the three spatial coordinates of their base vertices. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_reachable_sameDirection
    (H : ℕ)
    (x y : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu : PeriodicHypercubicEvenSpatialDirection) :
    (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
      (x, mu) (y, mu) := by
  let d1 := periodicHypercubicEvenSpatialConnectivityDirectionOne
  let d2 := periodicHypercubicEvenSpatialConnectivityDirectionTwo
  let d3 := periodicHypercubicEvenSpatialConnectivityDirectionThree
  let x1 := periodicHypercubicEvenSpatialSliceAdjustCoordinate H x y d1
  let x2 := periodicHypercubicEvenSpatialSliceAdjustCoordinate H x1 y d2
  let x3 := periodicHypercubicEvenSpatialSliceAdjustCoordinate H x2 y d3
  have h1 :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
        (x, mu) (x1, mu) :=
    periodicHypercubicEvenSpatialSliceActiveGraph_reachable_adjustCoordinate
      H x y mu d1
  have h2 :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
        (x1, mu) (x2, mu) :=
    periodicHypercubicEvenSpatialSliceActiveGraph_reachable_adjustCoordinate
      H x1 y mu d2
  have h3 :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
        (x2, mu) (x3, mu) :=
    periodicHypercubicEvenSpatialSliceActiveGraph_reachable_adjustCoordinate
      H x2 y mu d3
  have hx3 : x3 = y := by
    simpa [x1, x2, x3, d1, d2, d3,
      periodicHypercubicEvenSpatialSliceAdjustAllCoordinates] using
      periodicHypercubicEvenSpatialSliceAdjustAllCoordinates_eq H x y
  simpa [hx3] using h1.trans (h2.trans h3)

/-- The intrinsic spatial active graph is connected at every even periodic
side length. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_connected
    (H : ℕ) :
    (periodicHypercubicEvenSpatialSliceActiveGraph H).Connected := by
  refine
    { preconnected := ?_
      nonempty := ⟨
        (⟨(0 : PeriodicHypercubicEvenVertex H), by
            simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
          ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩ }
  intro p q
  rcases p with ⟨x, mu⟩
  rcases q with ⟨y, nu⟩
  have hBase :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
        (x, mu) (y, mu) :=
    periodicHypercubicEvenSpatialSliceActiveGraph_reachable_sameDirection
      H x y mu
  have hDirection :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
        (y, mu) (y, nu) :=
    periodicHypercubicEvenSpatialSliceActiveGraph_reachable_sameBase
      H y mu nu
  exact hBase.trans hDirection

end

end MathlibAnalytic
end MGAP4D

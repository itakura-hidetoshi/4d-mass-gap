import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumSwap12
import Mathlib.Tactic

/-!
# Spatial axis swap `(2 3)` on the even periodic lattice

The all-spatial zero-momentum plaquette observable is now proved invariant under the first adjacent
spatial transposition `(1 2)`.  To generate all permutations of the three spatial axes we next
construct the second adjacent transposition `(2 3)`, again fixing Euclidean time axis `0`.

This file is geometry only.  It lifts the axis swap to vertices, positive links, configurations,
time-zero spatial displacements, and the three spatial-plane labels, and proves exact compatibility
with positive unit shifts.  The induced plane action exchanges `(1,2)` and `(1,3)` while fixing the
geometric `(2,3)` plane; the latter will reverse canonical orientation in the later holonomy layer.
No continuum-spin, parity, charge-conjugation, or spectral claim is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Swap spatial coordinate axes `2` and `3`, fixing time axis `0` and spatial axis `1`. -/
def periodicHypercubicSpatialAxisSwap23 :
    PeriodicHypercubicAxis ≃ PeriodicHypercubicAxis :=
  Equiv.swap (2 : PeriodicHypercubicAxis) (3 : PeriodicHypercubicAxis)

@[simp]
theorem periodicHypercubicSpatialAxisSwap23_zero :
    periodicHypercubicSpatialAxisSwap23 (0 : PeriodicHypercubicAxis) = 0 := by
  native_decide

@[simp]
theorem periodicHypercubicSpatialAxisSwap23_one :
    periodicHypercubicSpatialAxisSwap23 (1 : PeriodicHypercubicAxis) = 1 := by
  native_decide

@[simp]
theorem periodicHypercubicSpatialAxisSwap23_two :
    periodicHypercubicSpatialAxisSwap23 (2 : PeriodicHypercubicAxis) = 3 := by
  native_decide

@[simp]
theorem periodicHypercubicSpatialAxisSwap23_three :
    periodicHypercubicSpatialAxisSwap23 (3 : PeriodicHypercubicAxis) = 2 := by
  native_decide

@[simp]
theorem periodicHypercubicSpatialAxisSwap23_symm_apply
    (i : PeriodicHypercubicAxis) :
    periodicHypercubicSpatialAxisSwap23.symm i =
      periodicHypercubicSpatialAxisSwap23 i := by
  fin_cases i <;> native_decide

@[simp]
theorem periodicHypercubicSpatialAxisSwap23_involutive
    (i : PeriodicHypercubicAxis) :
    periodicHypercubicSpatialAxisSwap23
        (periodicHypercubicSpatialAxisSwap23 i) = i := by
  fin_cases i <;> native_decide

/-- Coordinate reindexing of periodic vertices induced by the spatial axis swap. -/
def periodicHypercubicVertexSpatialAxisSwap23Equiv
    (n : ℕ) : PeriodicHypercubicVertex n ≃ PeriodicHypercubicVertex n where
  toFun x := fun i => x (periodicHypercubicSpatialAxisSwap23.symm i)
  invFun x := fun i => x (periodicHypercubicSpatialAxisSwap23 i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

@[simp]
theorem periodicHypercubicVertexSpatialAxisSwap23Equiv_apply
    (n : ℕ) (x : PeriodicHypercubicVertex n) (i : PeriodicHypercubicAxis) :
    periodicHypercubicVertexSpatialAxisSwap23Equiv n x i =
      x (periodicHypercubicSpatialAxisSwap23.symm i) :=
  rfl

@[simp]
theorem periodicHypercubicVertexSpatialAxisSwap23Equiv_symm_apply
    (n : ℕ) (x : PeriodicHypercubicVertex n) (i : PeriodicHypercubicAxis) :
    (periodicHypercubicVertexSpatialAxisSwap23Equiv n).symm x i =
      x (periodicHypercubicSpatialAxisSwap23 i) :=
  rfl

/-- The spatial axis swap commutes exactly with positive unit translation, with the direction
relabelled by the same axis permutation. -/
theorem periodicHypercubicVertexSpatialAxisSwap23Equiv_shift
    (n : ℕ) (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicVertexSpatialAxisSwap23Equiv n
        (periodicHypercubicShift n x mu) =
      periodicHypercubicShift n
        (periodicHypercubicVertexSpatialAxisSwap23Equiv n x)
        (periodicHypercubicSpatialAxisSwap23 mu) := by
  funext i
  fin_cases mu <;> fin_cases i <;>
    simp [periodicHypercubicShift_apply]

/-- Reindex physical positive edges by the same vertex and axis permutation. -/
def periodicHypercubicEdgeSpatialAxisSwap23Equiv
    (n : ℕ) : PeriodicHypercubicEdge n ≃ PeriodicHypercubicEdge n :=
  Equiv.prodCongr
    (periodicHypercubicVertexSpatialAxisSwap23Equiv n)
    periodicHypercubicSpatialAxisSwap23

@[simp]
theorem periodicHypercubicEdgeSpatialAxisSwap23Equiv_apply
    (n : ℕ) (e : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeSpatialAxisSwap23Equiv n e =
      (periodicHypercubicVertexSpatialAxisSwap23Equiv n e.1,
        periodicHypercubicSpatialAxisSwap23 e.2) :=
  rfl

@[simp]
theorem periodicHypercubicEdgeSpatialAxisSwap23Equiv_symm_apply
    (n : ℕ) (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicEdgeSpatialAxisSwap23Equiv n).symm e =
      ((periodicHypercubicVertexSpatialAxisSwap23Equiv n).symm e.1,
        periodicHypercubicSpatialAxisSwap23.symm e.2) :=
  rfl

/-- Pull a physical-link configuration through the spatial axis swap. -/
def periodicHypercubicConfigurationSpatialAxisSwap23
    {n : ℕ} {Gauge : Type}
    (A : PeriodicHypercubicEdge n → Gauge) :
    PeriodicHypercubicEdge n → Gauge :=
  fun e => A ((periodicHypercubicEdgeSpatialAxisSwap23Equiv n).symm e)

@[simp]
theorem periodicHypercubicConfigurationSpatialAxisSwap23_apply_swappedEdge
    {n : ℕ} {Gauge : Type}
    (A : PeriodicHypercubicEdge n → Gauge)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicConfigurationSpatialAxisSwap23 A
        (periodicHypercubicEdgeSpatialAxisSwap23Equiv n e) =
      A e := by
  simp [periodicHypercubicConfigurationSpatialAxisSwap23]

/-- The axis swap preserves the time-zero spatial-displacement carrier. -/
def periodicHypercubicEvenSpatialDisplacementSwap23Equiv
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialDisplacement H ≃
      PeriodicHypercubicEvenSpatialDisplacement H where
  toFun a :=
    ⟨periodicHypercubicVertexSpatialAxisSwap23Equiv
        (PeriodicHypercubicEvenSideLength H) a.1,
      by simpa using a.2⟩
  invFun a :=
    ⟨(periodicHypercubicVertexSpatialAxisSwap23Equiv
        (PeriodicHypercubicEvenSideLength H)).symm a.1,
      by simpa using a.2⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv a := by
    apply Subtype.ext
    simp

@[simp]
theorem periodicHypercubicEvenSpatialDisplacementSwap23Equiv_apply_val
    (H : ℕ) (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialDisplacementSwap23Equiv H a).1 =
      periodicHypercubicVertexSpatialAxisSwap23Equiv
        (PeriodicHypercubicEvenSideLength H) a.1 :=
  rfl

/-- Induced action of the `(2 3)` axis swap on the three purely spatial coordinate planes.
The `(2,3)` geometric plane is fixed but its canonical boundary orientation reverses; the `(1,2)`
and `(1,3)` planes are exchanged. -/
def periodicHypercubicSpatialPlaneSwap23Equiv :
    PeriodicHypercubicSpatialPlane ≃ PeriodicHypercubicSpatialPlane where
  toFun
    | .plane12 => .plane13
    | .plane13 => .plane12
    | .plane23 => .plane23
  invFun
    | .plane12 => .plane13
    | .plane13 => .plane12
    | .plane23 => .plane23
  left_inv p := by cases p <;> rfl
  right_inv p := by cases p <;> rfl

@[simp]
theorem periodicHypercubicSpatialPlaneSwap23Equiv_plane12 :
    periodicHypercubicSpatialPlaneSwap23Equiv .plane12 = .plane13 :=
  rfl

@[simp]
theorem periodicHypercubicSpatialPlaneSwap23Equiv_plane13 :
    periodicHypercubicSpatialPlaneSwap23Equiv .plane13 = .plane12 :=
  rfl

@[simp]
theorem periodicHypercubicSpatialPlaneSwap23Equiv_plane23 :
    periodicHypercubicSpatialPlaneSwap23Equiv .plane23 = .plane23 :=
  rfl

end

end MathlibAnalytic
end MGAP4D

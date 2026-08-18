import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentum
import Mathlib.Tactic

/-!
# Spatial axis swap `(1 2)` on the even periodic lattice

The all-spatial zero-momentum plaquette operator is an equal-weight sum over the three purely
spatial coordinate planes.  To turn that precursor into a theorem-generated cubic scalar channel,
we first construct explicit lattice reindexing for one generator of the spatial permutation group:
the transposition of axes `1` and `2`, with Euclidean time axis `0` fixed.

This file is geometry only.  It constructs the induced equivalences on axes, vertices, physical
positive edges, time-zero spatial displacements, and the three spatial-plane labels, together with
exact compatibility with positive unit shifts.  A later layer will use these receipts to transport
plaquette holonomies and normalized traces.  No spectral or continuum claim is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Swap spatial coordinate axes `1` and `2`, fixing time axis `0` and spatial axis `3`. -/
def periodicHypercubicSpatialAxisSwap12 :
    PeriodicHypercubicAxis ≃ PeriodicHypercubicAxis :=
  Equiv.swap (1 : PeriodicHypercubicAxis) (2 : PeriodicHypercubicAxis)

@[simp]
theorem periodicHypercubicSpatialAxisSwap12_zero :
    periodicHypercubicSpatialAxisSwap12 (0 : PeriodicHypercubicAxis) = 0 := by
  native_decide

@[simp]
theorem periodicHypercubicSpatialAxisSwap12_one :
    periodicHypercubicSpatialAxisSwap12 (1 : PeriodicHypercubicAxis) = 2 := by
  native_decide

@[simp]
theorem periodicHypercubicSpatialAxisSwap12_two :
    periodicHypercubicSpatialAxisSwap12 (2 : PeriodicHypercubicAxis) = 1 := by
  native_decide

@[simp]
theorem periodicHypercubicSpatialAxisSwap12_three :
    periodicHypercubicSpatialAxisSwap12 (3 : PeriodicHypercubicAxis) = 3 := by
  native_decide

@[simp]
theorem periodicHypercubicSpatialAxisSwap12_symm_apply
    (i : PeriodicHypercubicAxis) :
    periodicHypercubicSpatialAxisSwap12.symm i =
      periodicHypercubicSpatialAxisSwap12 i := by
  fin_cases i <;> native_decide

/-- Coordinate reindexing of periodic vertices induced by the spatial axis swap. -/
def periodicHypercubicVertexSpatialAxisSwap12Equiv
    (n : ℕ) : PeriodicHypercubicVertex n ≃ PeriodicHypercubicVertex n where
  toFun x := fun i => x (periodicHypercubicSpatialAxisSwap12.symm i)
  invFun x := fun i => x (periodicHypercubicSpatialAxisSwap12 i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

@[simp]
theorem periodicHypercubicVertexSpatialAxisSwap12Equiv_apply
    (n : ℕ) (x : PeriodicHypercubicVertex n) (i : PeriodicHypercubicAxis) :
    periodicHypercubicVertexSpatialAxisSwap12Equiv n x i =
      x (periodicHypercubicSpatialAxisSwap12.symm i) :=
  rfl

@[simp]
theorem periodicHypercubicVertexSpatialAxisSwap12Equiv_symm_apply
    (n : ℕ) (x : PeriodicHypercubicVertex n) (i : PeriodicHypercubicAxis) :
    (periodicHypercubicVertexSpatialAxisSwap12Equiv n).symm x i =
      x (periodicHypercubicSpatialAxisSwap12 i) :=
  rfl

/-- The spatial axis swap commutes exactly with positive unit translation, with the direction
relabelled by the same axis permutation. -/
theorem periodicHypercubicVertexSpatialAxisSwap12Equiv_shift
    (n : ℕ) (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicVertexSpatialAxisSwap12Equiv n
        (periodicHypercubicShift n x mu) =
      periodicHypercubicShift n
        (periodicHypercubicVertexSpatialAxisSwap12Equiv n x)
        (periodicHypercubicSpatialAxisSwap12 mu) := by
  funext i
  simp [periodicHypercubicShift_apply]

/-- Reindex physical positive edges by the same vertex and axis permutation. -/
def periodicHypercubicEdgeSpatialAxisSwap12Equiv
    (n : ℕ) : PeriodicHypercubicEdge n ≃ PeriodicHypercubicEdge n :=
  Equiv.prodCongr
    (periodicHypercubicVertexSpatialAxisSwap12Equiv n)
    periodicHypercubicSpatialAxisSwap12

@[simp]
theorem periodicHypercubicEdgeSpatialAxisSwap12Equiv_apply
    (n : ℕ) (e : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeSpatialAxisSwap12Equiv n e =
      (periodicHypercubicVertexSpatialAxisSwap12Equiv n e.1,
        periodicHypercubicSpatialAxisSwap12 e.2) :=
  rfl

@[simp]
theorem periodicHypercubicEdgeSpatialAxisSwap12Equiv_symm_apply
    (n : ℕ) (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicEdgeSpatialAxisSwap12Equiv n).symm e =
      ((periodicHypercubicVertexSpatialAxisSwap12Equiv n).symm e.1,
        periodicHypercubicSpatialAxisSwap12.symm e.2) :=
  rfl

/-- Pull a physical-link configuration through the spatial axis swap. -/
def periodicHypercubicConfigurationSpatialAxisSwap12
    {n : ℕ} {Gauge : Type}
    (A : PeriodicHypercubicEdge n → Gauge) :
    PeriodicHypercubicEdge n → Gauge :=
  fun e => A ((periodicHypercubicEdgeSpatialAxisSwap12Equiv n).symm e)

@[simp]
theorem periodicHypercubicConfigurationSpatialAxisSwap12_apply_swappedEdge
    {n : ℕ} {Gauge : Type}
    (A : PeriodicHypercubicEdge n → Gauge)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicConfigurationSpatialAxisSwap12 A
        (periodicHypercubicEdgeSpatialAxisSwap12Equiv n e) =
      A e := by
  simp [periodicHypercubicConfigurationSpatialAxisSwap12]

/-- The axis swap preserves the time-zero spatial-displacement carrier. -/
def periodicHypercubicEvenSpatialDisplacementSwap12Equiv
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialDisplacement H ≃
      PeriodicHypercubicEvenSpatialDisplacement H where
  toFun a :=
    ⟨periodicHypercubicVertexSpatialAxisSwap12Equiv
        (PeriodicHypercubicEvenSideLength H) a.1,
      by simpa using a.2⟩
  invFun a :=
    ⟨(periodicHypercubicVertexSpatialAxisSwap12Equiv
        (PeriodicHypercubicEvenSideLength H)).symm a.1,
      by simpa using a.2⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv a := by
    apply Subtype.ext
    simp

@[simp]
theorem periodicHypercubicEvenSpatialDisplacementSwap12Equiv_apply_val
    (H : ℕ) (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialDisplacementSwap12Equiv H a).1 =
      periodicHypercubicVertexSpatialAxisSwap12Equiv
        (PeriodicHypercubicEvenSideLength H) a.1 :=
  rfl

/-- Induced action of the `(1 2)` axis swap on the three purely spatial coordinate planes.
The `(1,2)` geometric plane is fixed but its canonical boundary orientation reverses; the other two
planes are exchanged. -/
def periodicHypercubicSpatialPlaneSwap12Equiv :
    PeriodicHypercubicSpatialPlane ≃ PeriodicHypercubicSpatialPlane where
  toFun
    | .plane12 => .plane12
    | .plane13 => .plane23
    | .plane23 => .plane13
  invFun
    | .plane12 => .plane12
    | .plane13 => .plane23
    | .plane23 => .plane13
  left_inv p := by cases p <;> rfl
  right_inv p := by cases p <;> rfl

@[simp]
theorem periodicHypercubicSpatialPlaneSwap12Equiv_plane12 :
    periodicHypercubicSpatialPlaneSwap12Equiv .plane12 = .plane12 :=
  rfl

@[simp]
theorem periodicHypercubicSpatialPlaneSwap12Equiv_plane13 :
    periodicHypercubicSpatialPlaneSwap12Equiv .plane13 = .plane23 :=
  rfl

@[simp]
theorem periodicHypercubicSpatialPlaneSwap12Equiv_plane23 :
    periodicHypercubicSpatialPlaneSwap12Equiv .plane23 = .plane13 :=
  rfl

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventNewtonHermiteCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Append one final entry to a finite vector. -/
def continuousLinearMapFinAppend
    {X : Type*} {n : ℕ} (xs : Fin n → X) (x : X) : Fin (n + 1) → X :=
  Fin.lastCases x xs

@[simp]
theorem continuousLinearMapFinAppend_last
    {X : Type*} {n : ℕ} (xs : Fin n → X) (x : X) :
    continuousLinearMapFinAppend xs x (Fin.last n) = x := by
  simp [continuousLinearMapFinAppend]

@[simp]
theorem continuousLinearMapFinAppend_castSucc
    {X : Type*} {n : ℕ} (xs : Fin n → X) (x : X) (i : Fin n) :
    continuousLinearMapFinAppend xs x i.castSucc = xs i := by
  simp [continuousLinearMapFinAppend]

@[simp]
theorem Fin.init_continuousLinearMapFinAppend
    {X : Type*} {n : ℕ} (xs : Fin n → X) (x : X) :
    Fin.init (continuousLinearMapFinAppend xs x) = xs := by
  funext i
  simp [Fin.init]

@[simp]
theorem continuousLinearMapFinAppend_init_last
    {X : Type*} {n : ℕ} (xs : Fin (n + 1) → X) :
    continuousLinearMapFinAppend (Fin.init xs) (xs (Fin.last n)) = xs := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.init]

/-- Ordered operator products respect final-entry append. -/
theorem continuousLinearMapOrderedProduct_finAppend
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : Fin n → (V →L[ℝ] V)) (A : V →L[ℝ] V) :
    continuousLinearMapOrderedProduct (n + 1)
        (continuousLinearMapFinAppend R A) =
      continuousLinearMapOrderedProduct n R * A := by
  simpa using
    continuousLinearMapOrderedProduct_snoc n
      (continuousLinearMapFinAppend R A)

/-- Scalar Newton products respect final-node append. -/
theorem continuousLinearMapRealResolventNewtonNodeProduct_finAppend
    (n : ℕ) (nodes : Fin n → ℝ) (w z : ℝ) :
    continuousLinearMapRealResolventNewtonNodeProduct (n + 1)
        (continuousLinearMapFinAppend nodes w) z =
      continuousLinearMapRealResolventNewtonNodeProduct n nodes z * (z - w) := by
  rw [continuousLinearMapRealResolventNewtonNodeProduct_succ]
  simp

/-- A normalized Hermite coefficient with one final node is an ordered prefix
product followed by the final resolvent. -/
theorem continuousLinearMapRealResolventHermiteCoefficient_finAppend
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n : ℕ) (A : V →L[ℝ] V) (nodes : Fin n → ℝ) (z : ℝ) :
    continuousLinearMapRealResolventHermiteCoefficient n A
        (continuousLinearMapFinAppend nodes z) =
      (-1 : ℝ) ^ n •
        (continuousLinearMapOrderedProduct n
            (fun i => continuousLinearMapRealResolvent A (nodes i)) *
          continuousLinearMapRealResolvent A z) := by
  unfold continuousLinearMapRealResolventHermiteCoefficient
  unfold continuousLinearMapRealResolventHermiteObservable
  rw [continuousLinearMapOrderedProduct_finAppend]
  rfl

/-- Replacing the final spectral node gives the exact next-order confluent
divided difference.  Repeated prefix nodes and equal endpoints are allowed. -/
theorem continuousLinearMapRealResolventHermiteCoefficient_finAppend_sub
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n : ℕ) (A : V →L[ℝ] V) (nodes : Fin n → ℝ) (z w : ℝ)
    (hz : IsUnit (continuousLinearMapRealShift A z))
    (hw : IsUnit (continuousLinearMapRealShift A w)) :
    continuousLinearMapRealResolventHermiteCoefficient n A
          (continuousLinearMapFinAppend nodes z) -
        continuousLinearMapRealResolventHermiteCoefficient n A
          (continuousLinearMapFinAppend nodes w) =
      (z - w) •
        continuousLinearMapRealResolventHermiteCoefficient (n + 1) A
          (continuousLinearMapFinAppend
            (continuousLinearMapFinAppend nodes w) z) := by
  let P : V →L[ℝ] V :=
    continuousLinearMapOrderedProduct n
      (fun i => continuousLinearMapRealResolvent A (nodes i))
  let Rz : V →L[ℝ] V := continuousLinearMapRealResolvent A z
  let Rw : V →L[ℝ] V := continuousLinearMapRealResolvent A w
  have hres : Rz - Rw = (w - z) • (Rz * Rw) := by
    simpa [Rz, Rw] using
      continuousLinearMapRealResolvent_sub_eq_smul_mul A hz hw
  have hcomm : Rz * Rw = Rw * Rz := by
    simpa [Rz, Rw] using continuousLinearMapRealResolvent_commute A hz hw
  have hprod : P * (Rz * Rw) = (P * Rw) * Rz := by
    rw [hcomm, mul_assoc]
  rw [continuousLinearMapRealResolventHermiteCoefficient_finAppend,
    continuousLinearMapRealResolventHermiteCoefficient_finAppend]
  rw [continuousLinearMapRealResolventHermiteCoefficient_finAppend]
  change
    (-1 : ℝ) ^ n • (P * Rz) - (-1 : ℝ) ^ n • (P * Rw) =
      (z - w) • ((-1 : ℝ) ^ (n + 1) • ((P * Rw) * Rz))
  calc
    (-1 : ℝ) ^ n • (P * Rz) - (-1 : ℝ) ^ n • (P * Rw) =
        (-1 : ℝ) ^ n • (P * (Rz - Rw)) := by
      rw [smul_sub, mul_sub]
    _ = (-1 : ℝ) ^ n • ((w - z) • (P * (Rz * Rw))) := by
      rw [hres, mul_smul_comm]
    _ = ((-1 : ℝ) ^ n * (w - z)) • (P * (Rz * Rw)) := by
      rw [smul_smul]
    _ = ((z - w) * (-1 : ℝ) ^ (n + 1)) • ((P * Rw) * Rz) := by
      rw [hprod]
      congr 1
      rw [pow_succ]
      ring
    _ = (z - w) • ((-1 : ℝ) ^ (n + 1) • ((P * Rw) * Rz)) := by
      rw [smul_smul]

/-- Exact Newton-Hermite remainder observable for a true finite-dimensional
real resolvent. -/
def continuousLinearMapRealResolventNewtonHermiteRemainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z : ℝ) : V →L[ℝ] V :=
  continuousLinearMapRealResolventNewtonNodeProduct (degree + 1) nodes z •
    continuousLinearMapRealResolventHermiteCoefficient (degree + 1) A
      (continuousLinearMapFinAppend nodes z)

/-- A Newton node product vanishes whenever the evaluation point is one of
its nodes. -/
theorem continuousLinearMapRealResolventNewtonNodeProduct_eq_zero_of_eq
    (n : ℕ) (nodes : Fin n → ℝ) (z : ℝ) (i : Fin n)
    (hi : z = nodes i) :
    continuousLinearMapRealResolventNewtonNodeProduct n nodes z = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases
        (motive := fun i : Fin (n + 1) => z = nodes i →
          continuousLinearMapRealResolventNewtonNodeProduct (n + 1) nodes z = 0)
        ?_ (fun j => ?_) i hi
      · intro hlast
        rw [continuousLinearMapRealResolventNewtonNodeProduct_succ]
        simp [hlast]
      · intro hcast
        rw [continuousLinearMapRealResolventNewtonNodeProduct_succ]
        rw [ih (Fin.init nodes) z j (by simpa [Fin.init] using hcast)]
        simp

/-- The exact Newton-Hermite remainder vanishes at every interpolation node. -/
theorem continuousLinearMapRealResolventNewtonHermiteRemainder_eq_zero_at_node
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (i : Fin (degree + 1)) :
    continuousLinearMapRealResolventNewtonHermiteRemainder
      degree A nodes (nodes i) = 0 := by
  unfold continuousLinearMapRealResolventNewtonHermiteRemainder
  rw [continuousLinearMapRealResolventNewtonNodeProduct_eq_zero_of_eq
    (degree + 1) nodes (nodes i) i rfl]
  simp

/-- Explicit operator-norm bound for the exact Newton-Hermite remainder. -/
theorem continuousLinearMapRealResolventNewtonHermiteRemainder_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z M D : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hnodesDist : ∀ i, |z - nodes i| ≤ D)
    (hnodesNorm : ∀ i, ‖continuousLinearMapRealResolvent A (nodes i)‖ ≤ M)
    (hzNorm : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    ‖continuousLinearMapRealResolventNewtonHermiteRemainder
        degree A nodes z‖ ≤
      D ^ (degree + 1) * M ^ (degree + 2) := by
  unfold continuousLinearMapRealResolventNewtonHermiteRemainder
  rw [norm_smul, Real.norm_eq_abs]
  apply mul_le_mul
  · exact abs_continuousLinearMapRealResolventNewtonNodeProduct_le
      (degree + 1) nodes z D hD hnodesDist
  · unfold continuousLinearMapRealResolventHermiteCoefficient
    apply continuousLinearMapRealResolventHermiteObservable_norm_le
      (degree + 1) _ hM
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hzNorm
    · simpa using hnodesNorm j
  · exact norm_nonneg _
  · exact pow_nonneg hD (degree + 1)

end MathlibAnalytic
end MGAP4D

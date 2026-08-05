import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit adjugate-over-determinant inverse for a finite real matrix.
Unlike the global matrix `Inv` instance, this uses the ordinary real inverse
and is therefore directly compatible with topological-field continuity. -/
noncomputable def finiteRealNonsingularMatrixInverse
    {n : Type}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A.det⁻¹ • A.adjugate

/-- The explicit inverse is a left inverse whenever the determinant is
nonzero. -/
theorem finiteRealNonsingularMatrixInverse_mul
    {n : Type}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n ℝ)
    (hdet : A.det ≠ 0) :
    finiteRealNonsingularMatrixInverse A * A = 1 := by
  unfold finiteRealNonsingularMatrixInverse
  rw [Matrix.mul_mul_left, Matrix.adjugate_mul]
  ext i j
  simp [hdet]

/-- The explicit inverse is a right inverse whenever the determinant is
nonzero. -/
theorem mul_finiteRealNonsingularMatrixInverse
    {n : Type}
    [Fintype n]
    [DecidableEq n]
    (A : Matrix n n ℝ)
    (hdet : A.det ≠ 0) :
    A * finiteRealNonsingularMatrixInverse A = 1 := by
  unfold finiteRealNonsingularMatrixInverse
  rw [Matrix.mul_mul_right, Matrix.mul_adjugate]
  ext i j
  simp [hdet]

/-- A continuous finite real matrix family with everywhere nonzero determinant
has a continuous explicit nonsingular inverse. -/
theorem continuous_finiteRealNonsingularMatrixInverse
    {X n : Type}
    [TopologicalSpace X]
    [Fintype n]
    [DecidableEq n]
    (A : X → Matrix n n ℝ)
    (hA : Continuous A)
    (hdet : ∀ x, (A x).det ≠ 0) :
    Continuous (fun x => finiteRealNonsingularMatrixInverse (A x)) := by
  unfold finiteRealNonsingularMatrixInverse
  exact (hA.matrix_det.inv₀ hdet).smul hA.matrix_adjugate

/-- Applying a continuous explicit nonsingular inverse matrix family to a
continuous finite vector family remains continuous. -/
theorem continuous_finiteRealNonsingularMatrixInverse_mulVec
    {X n : Type}
    [TopologicalSpace X]
    [Fintype n]
    [DecidableEq n]
    (A : X → Matrix n n ℝ)
    (v : X → n → ℝ)
    (hA : Continuous A)
    (hv : Continuous v)
    (hdet : ∀ x, (A x).det ≠ 0) :
    Continuous (fun x =>
      Matrix.mulVec (finiteRealNonsingularMatrixInverse (A x)) (v x)) :=
  (continuous_finiteRealNonsingularMatrixInverse A hA hdet).matrix_mulVec hv

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLIntegralPhysicalD3DeterminantV5_PZ37X
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# P4-Q2-PZ37Y — sharp Loewner determinant comparison

The exact original two-interacting-Wilson-posterior GL integral Gram B
is bounded below by c times the genuine normalized physical Gauss-law
Krylov Hankel Gram P in quadratic form, by PZ37W.

The new finite-dimensional lemma proves the stronger, SHARP determinant
comparison for any real 3x3 positive definite P and positive semidefinite B:

    (forall a, c * (a^T P a) <= a^T B a) && 0 <= c
    implies c^3 * det P <= det B.

It proceeds by true invertible square-root congruence of P,
not simultaneous diagonalization of P and B, and applies PZ37X's
already verified three-eigenvalue floor/product lemmas. This is
a theorem about the actual GL matrix and original Wilson D3, not
a surrogate statistic or a new posterior assumption.

The coefficients are finite-volume-dependent. No U0, volume-uniform
fine radius, endpoint E, arbitrary-depth F or H1-H4 is inferred.
No new axioms/sorry/admit/native_decide.
-/

namespace MGAP4D.MathlibAnalytic
open Matrix MeasureTheory
open scoped MatrixOrder InnerProductSpace BigOperators ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

private theorem p4Q2PZ37Y_finThree_conjugate_quadratic
    (S A : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    star a ⬝ᵥ ((star S * A * S) *ᵥ a) =
      star (S *ᵥ a) ⬝ᵥ (A *ᵥ (S *ᵥ a)) := by
  calc
    star a ⬝ᵥ ((star S * A * S) *ᵥ a) =
        (star a ᵥ* (star S)) ⬝ᵥ (A *ᵥ (S *ᵥ a)) := by
      simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_mul]
    _ = star (S *ᵥ a) ⬝ᵥ (A *ᵥ (S *ᵥ a)) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.vecMul_conjTranspose]
      simp

/-- A genuinely sharp 3x3 Loewner-order determinant comparison:
c P <= B for all real coefficient vectors, with P positive definite
and B positive semidefinite, entails c^3 det(P) <= det(B).
The proof uses an actual unit square-root factor of P and its inverse;
no comparison of eigenvectors of different matrices is assumed. -/
theorem p4Q2PZ37Y_finThree_posDef_quadratic_det_mono
    (P B : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : P.PosDef) (hB : B.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c)
    (hCmp : ∀ a : Fin 3 → ℝ,
      c * (star a ⬝ᵥ (P *ᵥ a)) ≤
        star a ⬝ᵥ (B *ᵥ a)) :
    c ^ 3 * P.det ≤ B.det := by
  obtain ⟨S, hSUnit, hFactor⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
      hP.isStrictlyPositive
  have hSDet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSUnit
  let T : Matrix (Fin 3) (Fin 3) ℝ := S⁻¹
  let M : Matrix (Fin 3) (Fin 3) ℝ := star T * B * T
  have hST : S * T = 1 := by
    simpa only [T] using Matrix.mul_nonsing_inv S hSDet
  have hTS : T * S = 1 := by
    simpa only [T] using Matrix.nonsing_inv_mul S hSDet
  have hStarTS : star T * star S = 1 := by
    rw [← Matrix.star_mul, hST, star_one]
  have hStarST : star S * star T = 1 := by
    rw [← Matrix.star_mul, hTS, star_one]
  have hPconj : star T * P * T = 1 := by
    calc
      star T * P * T = (star T * star S) * (S * T) := by
        rw [hFactor]
        simp only [mul_assoc]
      _ = 1 := by rw [hStarTS, hST, one_mul]
  have hMPSD : M.PosSemidef := by
    simpa only [M, Matrix.star_eq_conjTranspose] using
      hB.conjTranspose_mul_mul_same T
  have hFloor (a : Fin 3 → ℝ) :
      c * (∑ j : Fin 3, (a j) ^ 2) ≤
        star a ⬝ᵥ (M *ᵥ a) := by
    have h := hCmp (T *ᵥ a)
    rw [← p4Q2PZ37Y_finThree_conjugate_quadratic T P a,
      ← p4Q2PZ37Y_finThree_conjugate_quadratic T B a,
      hPconj, Matrix.one_mulVec] at h
    simpa only [M, dotProduct, star_trivial, pow_two] using h
  have hMdet : c ^ 3 ≤ M.det :=
    p4Q2PZ37X_finThree_eigenvalues_floor_det M hMPSD c hc
      (p4Q2PZ37X_finThree_quadratic_floor_eigenvalues M hMPSD c hFloor)
  have hStarDet : (star S).det = S.det := by
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
    simp
  have hPdet : P.det = S.det ^ 2 := by
    rw [hFactor, Matrix.det_mul, hStarDet]
    ring
  have hBfactor : B = star S * M * S := by
    calc
      B = (1 : Matrix (Fin 3) (Fin 3) ℝ) * B * 1 := by simp
      _ = (star S * star T) * B * (T * S) := by
        rw [hStarST, hTS]
      _ = star S * M * S := by
        simp only [M, mul_assoc]
  have hBdet : B.det = S.det ^ 2 * M.det := by
    rw [hBfactor, Matrix.det_mul, Matrix.det_mul, hStarDet]
    ring
  calc
    c ^ 3 * P.det = (S.det ^ 2) * c ^ 3 := by rw [hPdet]; ring
    _ ≤ S.det ^ 2 * M.det :=
      mul_le_mul_of_nonneg_left hMdet (sq_nonneg S.det)
    _ = B.det := hBdet.symm

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Y_finThree_posDef_quadratic_det_mono

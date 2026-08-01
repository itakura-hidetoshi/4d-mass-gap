import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationDirectionalDerivative
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The symmetric mixed-direction Dyson coefficient.  At order `n + 1` it is
obtained by choosing the last perturbation direction and summing over all
choices.  Thus every ordering of the directions occurs exactly once. -/
def continuousLinearMapRealResolventOperatorMixedDysonCoefficient :
    (n : ℕ) → {V : Type*} → [NormedAddCommGroup V] → [NormedSpace ℝ V] →
      [FiniteDimensional ℝ V] →
      (V →L[ℝ] V) → (Fin n → (V →L[ℝ] V)) → ℝ → (V →L[ℝ] V)
  | 0, V, _, _, _, A, _, z => continuousLinearMapRealResolvent A z
  | n + 1, V, _, _, _, A, H, z =>
      ∑ i : Fin (n + 1),
        continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A
            (fun j => H (i.succAbove j)) z *
          H i * continuousLinearMapRealResolvent A z

@[simp]
theorem continuousLinearMapRealResolventOperatorMixedDysonCoefficient_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (H : Fin 0 → (V →L[ℝ] V)) (z : ℝ) :
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient 0 A H z =
      continuousLinearMapRealResolvent A z :=
  rfl

@[simp]
theorem continuousLinearMapRealResolventOperatorMixedDysonCoefficient_succ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V)
    (H : Fin (n + 1) → (V →L[ℝ] V)) (z : ℝ) :
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient (n + 1) A H z =
      ∑ i : Fin (n + 1),
        continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A
            (fun j => H (i.succAbove j)) z *
          H i * continuousLinearMapRealResolvent A z :=
  rfl

@[simp]
theorem continuousLinearMapRealResolventOperatorMixedDysonCoefficient_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V)
    (H : Fin 1 → (V →L[ℝ] V)) (z : ℝ) :
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient 1 A H z =
      continuousLinearMapRealResolvent A z * H 0 *
        continuousLinearMapRealResolvent A z := by
  simp [continuousLinearMapRealResolventOperatorMixedDysonCoefficient]

/-- Constant direction tuples recover the ordinary one-direction Dyson
coefficient, multiplied by the factorial counting all orderings. -/
theorem continuousLinearMapRealResolventOperatorMixedDysonCoefficient_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A
        (fun _ => H) z =
      (n.factorial : ℝ) •
        continuousLinearMapRealResolventOperatorDysonCoefficient n A H z := by
  induction n with
  | zero =>
      simp [continuousLinearMapRealResolventOperatorMixedDysonCoefficient,
        continuousLinearMapRealResolventOperatorDysonCoefficient]
  | succ n ih =>
      rw [continuousLinearMapRealResolventOperatorMixedDysonCoefficient_succ]
      have hremove : ∀ i : Fin (n + 1),
          continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A
              (fun j => (fun _ : Fin (n + 1) => H) (i.succAbove j)) z =
            (n.factorial : ℝ) •
              continuousLinearMapRealResolventOperatorDysonCoefficient n A H z := by
        intro i
        simpa using ih
      simp_rw [hremove]
      have hterm :
          (((n.factorial : ℝ) •
              continuousLinearMapRealResolventOperatorDysonCoefficient n A H z) * H) *
              continuousLinearMapRealResolvent A z =
            (n.factorial : ℝ) •
              continuousLinearMapRealResolventOperatorDysonCoefficient (n + 1) A H z := by
        rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,
          ← continuousLinearMapRealResolventOperatorDysonCoefficient_succ]
      rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, smul_smul]
      congr 1
      ring

/-- The finite mixed-direction polarization jet through order `N - 1`. -/
def continuousLinearMapRealResolventOperatorMixedDysonJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A : V →L[ℝ] V)
    (H : ∀ n : Fin N, Fin n.1 → (V →L[ℝ] V)) (z : ℝ) :
    ∀ n : Fin N, V →L[ℝ] V :=
  fun n => continuousLinearMapRealResolventOperatorMixedDysonCoefficient n.1 A (H n) z

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventHermiteCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Ordered scalar Newton basis product over a finite node vector.  The
recursive definition exposes the final factor and therefore supports exact
Newton remainder induction without any distinct-node hypothesis. -/
def continuousLinearMapRealResolventNewtonNodeProduct :
    (n : ℕ) → (Fin n → ℝ) → ℝ → ℝ
  | 0, _, _ => 1
  | n + 1, nodes, z =>
      continuousLinearMapRealResolventNewtonNodeProduct n (Fin.init nodes) z *
        (z - nodes (Fin.last n))

@[simp]
theorem continuousLinearMapRealResolventNewtonNodeProduct_zero
    (nodes : Fin 0 → ℝ) (z : ℝ) :
    continuousLinearMapRealResolventNewtonNodeProduct 0 nodes z = 1 := rfl

@[simp]
theorem continuousLinearMapRealResolventNewtonNodeProduct_succ
    (n : ℕ) (nodes : Fin (n + 1) → ℝ) (z : ℝ) :
    continuousLinearMapRealResolventNewtonNodeProduct (n + 1) nodes z =
      continuousLinearMapRealResolventNewtonNodeProduct n (Fin.init nodes) z *
        (z - nodes (Fin.last n)) := rfl

/-- Absolute-value control for the finite Newton basis product. -/
theorem abs_continuousLinearMapRealResolventNewtonNodeProduct_le
    (n : ℕ) (nodes : Fin n → ℝ) (z D : ℝ) (hD : 0 ≤ D)
    (hnodes : ∀ i, |z - nodes i| ≤ D) :
    |continuousLinearMapRealResolventNewtonNodeProduct n nodes z| ≤ D ^ n := by
  induction n with
  | zero => simp [continuousLinearMapRealResolventNewtonNodeProduct]
  | succ n ih =>
      rw [continuousLinearMapRealResolventNewtonNodeProduct_succ, abs_mul, pow_succ']
      exact mul_le_mul
        (ih (Fin.init nodes) (fun i => hnodes i.castSucc))
        (hnodes (Fin.last n)) (abs_nonneg _) (pow_nonneg hD n)

/-- Recursive Newton-Hermite interpolant observable built from a finite vector
of bounded operators.  Its coefficient of order `k` is the normalized
Hermite observable on the first `k+1` operators. -/
def continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (degree : ℕ) → (Fin (degree + 1) → ℝ) → ℝ →
      (Fin (degree + 1) → (V →L[ℝ] V)) → (V →L[ℝ] V)
  | 0, _, _, R => R 0
  | n + 1, nodes, z, R =>
      continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
        n (Fin.init nodes) z (Fin.init R) +
      continuousLinearMapRealResolventNewtonNodeProduct
          (n + 1) (Fin.init nodes) z •
        continuousLinearMapRealResolventHermiteObservable (n + 1) R

@[simp]
theorem continuousLinearMapRealResolventNewtonHermiteInterpolantObservable_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (nodes : Fin 1 → ℝ) (z : ℝ) (R : Fin 1 → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
      0 nodes z R = R 0 := rfl

@[simp]
theorem continuousLinearMapRealResolventNewtonHermiteInterpolantObservable_succ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (nodes : Fin (n + 2) → ℝ) (z : ℝ)
    (R : Fin (n + 2) → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
        (n + 1) nodes z R =
      continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
          n (Fin.init nodes) z (Fin.init R) +
        continuousLinearMapRealResolventNewtonNodeProduct
            (n + 1) (Fin.init nodes) z •
          continuousLinearMapRealResolventHermiteObservable (n + 1) R := rfl

/-- The Newton-Hermite interpolant observable is continuous in the complete
finite operator tuple for every fixed node vector and evaluation point. -/
theorem continuous_continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∀ degree : ℕ, ∀ nodes : Fin (degree + 1) → ℝ, ∀ z : ℝ,
      Continuous
        (continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
          (V := V) degree nodes z)
  | 0, nodes, z => by
      simpa only [continuousLinearMapRealResolventNewtonHermiteInterpolantObservable]
        using (continuous_apply (0 : Fin 1) :
          Continuous (fun R : Fin 1 → (V →L[ℝ] V) => R 0))
  | n + 1, nodes, z => by
      have hinit : Continuous
          (fun R : Fin (n + 2) → (V →L[ℝ] V) => Fin.init R) := by
        apply continuous_pi
        intro i
        exact continuous_apply i.castSucc
      exact
        ((continuous_continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
            n (Fin.init nodes) z).comp hinit).add
          ((continuous_const_smul
              (continuousLinearMapRealResolventNewtonNodeProduct
                (n + 1) (Fin.init nodes) z)).comp
            (continuous_continuousLinearMapRealResolventHermiteObservable (n + 1)))

/-- Explicit recursive envelope for a Newton-Hermite interpolant when every
operator has norm at most `M` and every node displacement has size at most
`D`. -/
def continuousLinearMapRealResolventNewtonHermiteEnvelope :
    ℕ → ℝ → ℝ → ℝ
  | 0, M, _ => M
  | n + 1, M, D =>
      continuousLinearMapRealResolventNewtonHermiteEnvelope n M D +
        D ^ (n + 1) * M ^ (n + 2)

@[simp]
theorem continuousLinearMapRealResolventNewtonHermiteEnvelope_zero
    (M D : ℝ) :
    continuousLinearMapRealResolventNewtonHermiteEnvelope 0 M D = M := rfl

@[simp]
theorem continuousLinearMapRealResolventNewtonHermiteEnvelope_succ
    (n : ℕ) (M D : ℝ) :
    continuousLinearMapRealResolventNewtonHermiteEnvelope (n + 1) M D =
      continuousLinearMapRealResolventNewtonHermiteEnvelope n M D +
        D ^ (n + 1) * M ^ (n + 2) := rfl

/-- Operator-norm control for the complete Newton-Hermite interpolant. -/
theorem continuousLinearMapRealResolventNewtonHermiteInterpolantObservable_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z M D : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (R : Fin (degree + 1) → (V →L[ℝ] V))
    (hR : ∀ i, ‖R i‖ ≤ M) (hnodes : ∀ i, |z - nodes i| ≤ D) :
    ‖continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
        degree nodes z R‖ ≤
      continuousLinearMapRealResolventNewtonHermiteEnvelope degree M D := by
  induction degree with
  | zero =>
      simpa [continuousLinearMapRealResolventNewtonHermiteInterpolantObservable,
        continuousLinearMapRealResolventNewtonHermiteEnvelope] using hR 0
  | succ n ih =>
      rw [continuousLinearMapRealResolventNewtonHermiteInterpolantObservable_succ,
        continuousLinearMapRealResolventNewtonHermiteEnvelope_succ]
      apply le_trans (norm_add_le _ _)
      apply add_le_add
      · exact ih (Fin.init nodes) z M D hM hD (Fin.init R)
          (fun i => hR i.castSucc) (fun i => hnodes i.castSucc)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul
          (abs_continuousLinearMapRealResolventNewtonNodeProduct_le
            (n + 1) (Fin.init nodes) z D hD (fun i => hnodes i.castSucc))
          (continuousLinearMapRealResolventHermiteObservable_norm_le
            (n + 1) R hM hR)
          (norm_nonneg _) (pow_nonneg hD (n + 1))

/-- Newton-Hermite interpolant of the true finite-dimensional real resolvent. -/
def continuousLinearMapRealResolventNewtonHermiteInterpolant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z : ℝ) : V →L[ℝ] V :=
  continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
    degree nodes z (fun i => continuousLinearMapRealResolvent A (nodes i))

end MathlibAnalytic
end MGAP4D

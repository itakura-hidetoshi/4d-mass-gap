import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# Source-fixed leakage and source-residual forcing

Write P for the target and Q for the source orthogonal projection. For
z = Q x, r = z - P z, y = x - Q x, and ell = P z - Q (P z), orthogonality gives

  ||r||^2 = <r, x - P x> + <ell, y>.

Thus a bound ||ell|| <= k * ||r|| implies

  ||Q x - P (Q x)|| <= ||x - P x|| + k * ||x - Q x||.

This retains the signed cancellation before applying Cauchy--Schwarz. It does
not replace an operator-norm commutator bound by a source-residual bound.
The leakage estimate is a separate analytic input, evaluated only at Q x.
No factor two, cardinality constant, division, or commutativity is required.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Exact signed pairing identity. Both residuals stay on the same Hilbert carrier. -/
theorem realHilbertProjection_targetResidual_sq_eq_inner_residual_add_sourceLeakage
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →L[ℝ] E)
    (hPIdem : P.comp P = P) (hQIdem : Q.comp Q = Q)
    (hPSymm : ∀ u v : E, inner ℝ (P u) v = inner ℝ u (P v))
    (hQSymm : ∀ u v : E, inner ℝ (Q u) v = inner ℝ u (Q v))
    (x : E) :
    ‖Q x - P (Q x)‖ ^ 2 =
      inner ℝ (Q x - P (Q x)) (x - P x) +
        inner ℝ (P (Q x) - Q (P (Q x))) (x - Q x) := by
  have hPApply (u : E) : P (P u) = P u := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T u) hPIdem
  have hQApply (u : E) : Q (Q u) = Q u := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T u) hQIdem
  let z := Q x
  let r := z - P z
  let y := x - z
  let leakage := P z - Q (P z)
  have hPr : P r = 0 := by
    simp only [r, map_sub, hPApply, sub_self]
  have hQy : Q y = 0 := by
    simp only [y, z, map_sub, hQApply, sub_self]
  have hrP (u : E) : inner ℝ r (P u) = 0 := by
    rw [← hPSymm r u, hPr, inner_zero_left]
  have hQOrth (u : E) : inner ℝ (Q u) y = 0 := by
    rw [hQSymm u y, hQy, inner_zero_right]
  have hzY : inner ℝ z y = 0 := hQOrth x
  have hRy : inner ℝ r y = -inner ℝ leakage y := by
    dsimp only [r, leakage]
    rw [inner_sub_left, inner_sub_left, hQOrth (P z), hzY]
    ring
  have hRz : inner ℝ r z = ‖r‖ ^ 2 := by
    have hz : z = r + P z := by
      dsimp only [r]
      abel
    calc
      inner ℝ r z = inner ℝ r (r + P z) := congrArg (inner ℝ r) hz
      _ = ‖r‖ ^ 2 := by
        rw [inner_add_right, hrP z, add_zero, real_inner_self_eq_norm_sq]
  have hBefore :
      inner ℝ r (x - P x) = inner ℝ r z + inner ℝ r y := by
    rw [inner_sub_right, hrP x, sub_zero]
    have hx : x = z + y := by
      dsimp only [y]
      abel
    calc
      inner ℝ r x = inner ℝ r (z + y) := congrArg (inner ℝ r) hx
      _ = inner ℝ r z + inner ℝ r y := inner_add_right _ _ _
  change ‖r‖ ^ 2 = inner ℝ r (x - P x) + inner ℝ leakage y
  rw [hBefore, hRy, hRz]
  ring

/-- A source-fixed leakage bound yields the actual source-residual one-step cost.
The premise concerns the single updated input Q x, not all projected inputs. -/
theorem realHilbertProjection_targetResidual_norm_le_add_sourceResidual_of_leakage
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →L[ℝ] E)
    (hPIdem : P.comp P = P) (hQIdem : Q.comp Q = Q)
    (hPSymm : ∀ u v : E, inner ℝ (P u) v = inner ℝ u (P v))
    (hQSymm : ∀ u v : E, inner ℝ (Q u) v = inner ℝ u (Q v))
    (k : ℝ) (hk : 0 ≤ k) (x : E)
    (hLeakage : ‖P (Q x) - Q (P (Q x))‖ ≤ k * ‖Q x - P (Q x)‖) :
    ‖Q x - P (Q x)‖ ≤ ‖x - P x‖ + k * ‖x - Q x‖ := by
  let r := Q x - P (Q x)
  let leakage := P (Q x) - Q (P (Q x))
  have hPair :=
    realHilbertProjection_targetResidual_sq_eq_inner_residual_add_sourceLeakage
      P Q hPIdem hQIdem hPSymm hQSymm x
  have hSquared :
      ‖r‖ ^ 2 ≤ ‖r‖ * (‖x - P x‖ + k * ‖x - Q x‖) := by
    calc
      ‖r‖ ^ 2 = inner ℝ r (x - P x) + inner ℝ leakage (x - Q x) := hPair
      _ ≤ ‖r‖ * ‖x - P x‖ + ‖leakage‖ * ‖x - Q x‖ :=
        _root_.add_le_add
          ((le_abs_self _).trans (abs_real_inner_le_norm _ _))
          ((le_abs_self _).trans (abs_real_inner_le_norm _ _))
      _ ≤ ‖r‖ * ‖x - P x‖ + (k * ‖r‖) * ‖x - Q x‖ :=
        _root_.add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hLeakage (norm_nonneg _))
      _ = ‖r‖ * (‖x - P x‖ + k * ‖x - Q x‖) := by ring
  change ‖r‖ ≤ ‖x - P x‖ + k * ‖x - Q x‖
  by_cases hr : ‖r‖ = 0
  · rw [hr]
    exact add_nonneg (norm_nonneg _) (mul_nonneg hk (norm_nonneg _))
  · have hrpos : 0 < ‖r‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr)
    exact (mul_le_mul_left hrpos).mp (by simpa only [pow_two] using hSquared)

end

end MGAP4D.MathlibAnalytic

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace

noncomputable section

/-- A real-Hilbert orbit satisfying the bounded-generator equation

`u'(s) = -(1/2) A (u(s))`

and a pointwise coercivity bound with constant `gap` decays at the square-root
exponential rate.  The proof uses the antitonicity of the weighted energy
`exp (gap * s) * ‖u(s)‖²`; no spectral theorem is required. -/
theorem realHilbert_boundedGenerator_halfTime_norm_decay
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (gap t : ℝ)
    (ht : 0 ≤ t)
    (f : E)
    (u : ℝ → E)
    (hu0 : u 0 = f)
    (hu' : ∀ s,
      HasDerivAt u ((-(1 / 2 : ℝ)) • A (u s)) s)
    (hcoercive : ∀ s,
      gap * ‖u s‖ ^ 2 ≤ inner ℝ (A (u s)) (u s)) :
    ‖u t‖ ≤ Real.sqrt (Real.exp (-gap * t)) * ‖f‖ := by
  let energy : ℝ → ℝ := fun s => Real.exp (gap * s) * ‖u s‖ ^ 2
  let energy' : ℝ → ℝ := fun s =>
    Real.exp (gap * s) *
      (gap * ‖u s‖ ^ 2 - inner ℝ (A (u s)) (u s))
  have hnorm_sq : ∀ s,
      HasDerivAt (fun r => ‖u r‖ ^ 2)
        (-inner ℝ (A (u s)) (u s)) s := by
    intro s
    convert (hu' s).norm_sq using 1
    rw [real_inner_smul_right, real_inner_comm]
    ring
  have henergy : ∀ s, HasDerivAt energy (energy' s) s := by
    intro s
    have hexp :
        HasDerivAt (fun r => Real.exp (gap * r))
          (Real.exp (gap * s) * gap) s :=
      ((hasDerivAt_id s).const_mul gap).exp
    convert hexp.mul (hnorm_sq s) using 1 <;>
      simp only [energy, energy'] <;> ring
  have henergy_nonpos : energy' ≤ 0 := by
    intro s
    exact mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_nonneg _)
      (sub_nonpos.mpr (hcoercive s))
  have hanti : Antitone energy :=
    antitone_of_hasDerivAt_nonpos henergy henergy_nonpos
  have hweighted :
      Real.exp (gap * t) * ‖u t‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    simpa [energy, hu0] using hanti ht
  have hsquare :
      ‖u t‖ ^ 2 ≤ Real.exp (-gap * t) * ‖f‖ ^ 2 := by
    have hexp_pos : 0 < Real.exp (gap * t) := Real.exp_pos _
    have hdiv : ‖u t‖ ^ 2 ≤ ‖f‖ ^ 2 / Real.exp (gap * t) :=
      (le_div_iff₀ hexp_pos).2 (by simpa [mul_comm] using hweighted)
    calc
      ‖u t‖ ^ 2 ≤ ‖f‖ ^ 2 / Real.exp (gap * t) := hdiv
      _ = Real.exp (-gap * t) * ‖f‖ ^ 2 := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        ring
  calc
    ‖u t‖ = Real.sqrt (‖u t‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (Real.exp (-gap * t) * ‖f‖ ^ 2) :=
      Real.sqrt_le_sqrt hsquare
    _ = Real.sqrt (Real.exp (-gap * t)) * ‖f‖ := by
      rw [Real.sqrt_mul (Real.exp_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end

end MathlibAnalytic
end MGAP4D

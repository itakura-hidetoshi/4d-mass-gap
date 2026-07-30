import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventDerivativeBundle
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1000000

/-- The first operator-norm derivative of the real resolvent has the expected
within-derivative obtained from the noncommutative product rule. -/
theorem orthonormalDiagonalHamiltonianResolvent_deriv_hasDerivWithinAt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) :
    HasDerivWithinAt
      (deriv (orthonormalDiagonalHamiltonianResolvent b a))
      (((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
          (orthonormalDiagonalHamiltonianResolvent b a lambda)).comp
            (orthonormalDiagonalHamiltonianResolvent b a lambda) +
        (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
          ((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
            (orthonormalDiagonalHamiltonianResolvent b a lambda)))
      (Set.Iio delta) lambda := by
  let R := orthonormalDiagonalHamiltonianResolvent b a
  let Rlambda := R lambda
  have hR :
      HasDerivWithinAt R (Rlambda.comp Rlambda) (Set.Iio delta) lambda := by
    simpa [R, Rlambda] using
      (orthonormalDiagonalHamiltonianResolvent_hasDerivWithinAt
        b a delta hdelta hlambda)
  have hsquare :
      HasDerivWithinAt
        (fun mu => (R mu).comp (R mu))
        ((Rlambda.comp Rlambda).comp Rlambda +
          Rlambda.comp (Rlambda.comp Rlambda))
        (Set.Iio delta) lambda := by
    simpa using hR.clm_comp hR
  have hderivSquare :
      ∀ mu ∈ Set.Iio delta, deriv R mu = (R mu).comp (R mu) := by
    intro mu hmu
    simpa [R] using
      (orthonormalDiagonalHamiltonianResolvent_deriv
        b a delta hdelta hmu)
  have hcongr := hsquare.congr_of_mem hderivSquare hlambda
  simpa [R, Rlambda] using hcongr

/-- Since the open sub-gap interval is a neighborhood of each of its points,
the first derivative has the corresponding ordinary derivative. -/
theorem orthonormalDiagonalHamiltonianResolvent_deriv_hasDerivAt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) :
    HasDerivAt
      (deriv (orthonormalDiagonalHamiltonianResolvent b a))
      (((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
          (orthonormalDiagonalHamiltonianResolvent b a lambda)).comp
            (orthonormalDiagonalHamiltonianResolvent b a lambda) +
        (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
          ((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
            (orthonormalDiagonalHamiltonianResolvent b a lambda)))
      lambda := by
  exact
    (orthonormalDiagonalHamiltonianResolvent_deriv_hasDerivWithinAt
      b a delta hdelta hlambda).hasDerivAt (Iio_mem_nhds hlambda)

/-- Explicit second operator-norm derivative formula.  The two cubic terms are
kept in product-rule order, so no commutativity assumption is introduced. -/
theorem orthonormalDiagonalHamiltonianResolvent_secondDeriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) :
    deriv (deriv (orthonormalDiagonalHamiltonianResolvent b a)) lambda =
      ((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
          (orthonormalDiagonalHamiltonianResolvent b a lambda)).comp
            (orthonormalDiagonalHamiltonianResolvent b a lambda) +
        (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
          ((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
            (orthonormalDiagonalHamiltonianResolvent b a lambda)) :=
  (orthonormalDiagonalHamiltonianResolvent_deriv_hasDerivAt
    b a delta hdelta hlambda).deriv

/-- The first derivative is differentiable throughout the open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_deriv_differentiableOn
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    DifferentiableOn ℝ
      (deriv (orthonormalDiagonalHamiltonianResolvent b a))
      (Set.Iio delta) := by
  intro lambda hlambda
  exact
    (orthonormalDiagonalHamiltonianResolvent_deriv_hasDerivWithinAt
      b a delta hdelta hlambda).differentiableWithinAt

/-- The second operator-norm derivative is continuous throughout the open
sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_continuousOn_secondDeriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContinuousOn
      (deriv (deriv (orthonormalDiagonalHamiltonianResolvent b a)))
      (Set.Iio delta) := by
  let R := orthonormalDiagonalHamiltonianResolvent b a
  have hRdiff : DifferentiableOn ℝ R (Set.Iio delta) := by
    simpa [R] using
      (orthonormalDiagonalHamiltonianResolvent_differentiableOn
        b a delta hdelta)
  have hsquareDiff :
      DifferentiableOn ℝ (fun lambda => (R lambda).comp (R lambda))
        (Set.Iio delta) :=
    hRdiff.clm_comp hRdiff
  have hcubicLeft :
      DifferentiableOn ℝ
        (fun lambda => ((R lambda).comp (R lambda)).comp (R lambda))
        (Set.Iio delta) :=
    hsquareDiff.clm_comp hRdiff
  have hcubicRight :
      DifferentiableOn ℝ
        (fun lambda => (R lambda).comp ((R lambda).comp (R lambda)))
        (Set.Iio delta) :=
    hRdiff.clm_comp hsquareDiff
  have hsum :
      ContinuousOn
        (fun lambda =>
          ((R lambda).comp (R lambda)).comp (R lambda) +
            (R lambda).comp ((R lambda).comp (R lambda)))
        (Set.Iio delta) :=
    (hcubicLeft.add hcubicRight).continuousOn
  apply hsum.congr
  intro lambda hlambda
  simpa [R] using
    (orthonormalDiagonalHamiltonianResolvent_secondDeriv
      b a delta hdelta hlambda)

/-- The first derivative is `C¹` in operator norm on the full open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_deriv_contDiffOn_one
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContDiffOn ℝ 1
      (deriv (orthonormalDiagonalHamiltonianResolvent b a))
      (Set.Iio delta) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
  refine ⟨orthonormalDiagonalHamiltonianResolvent_deriv_differentiableOn
      b a delta hdelta, ?_, ?_⟩
  · simp
  · simpa only [contDiffOn_zero] using
      orthonormalDiagonalHamiltonianResolvent_continuousOn_secondDeriv
        b a delta hdelta

/-- The real resolvent is `C²` in operator norm on the full open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_contDiffOn_two
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContDiffOn ℝ 2
      (orthonormalDiagonalHamiltonianResolvent b a)
      (Set.Iio delta) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
  refine ⟨orthonormalDiagonalHamiltonianResolvent_differentiableOn
      b a delta hdelta, ?_, ?_⟩
  · norm_num
  · exact orthonormalDiagonalHamiltonianResolvent_deriv_contDiffOn_one
      b a delta hdelta

/-- Exact reciprocal-cube distance-to-gap bound for the second resolvent derivative. -/
theorem orthonormalDiagonalHamiltonianResolvent_secondDeriv_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) :
    ‖deriv (deriv (orthonormalDiagonalHamiltonianResolvent b a)) lambda‖ ≤
      2 * (((delta - lambda)⁻¹ * (delta - lambda)⁻¹) *
        (delta - lambda)⁻¹) := by
  rw [orthonormalDiagonalHamiltonianResolvent_secondDeriv
    b a delta hdelta hlambda]
  let R := orthonormalDiagonalHamiltonianResolvent b a lambda
  let q := (delta - lambda)⁻¹
  change ‖(R * R) * R + R * (R * R)‖ ≤ 2 * ((q * q) * q)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)
  have hR : ‖R‖ ≤ q := by
    simpa [R, q] using
      (orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
        b a delta lambda hdelta hlambda)
  have hRR : ‖R * R‖ ≤ q * q := by
    exact (norm_mul_le R R).trans
      (mul_le_mul hR hR (norm_nonneg R) hq)
  have hleft : ‖(R * R) * R‖ ≤ (q * q) * q := by
    exact (norm_mul_le (R * R) R).trans
      (mul_le_mul hRR hR (norm_nonneg R) (mul_nonneg hq hq))
  have hright : ‖R * (R * R)‖ ≤ q * (q * q) := by
    exact (norm_mul_le R (R * R)).trans
      (mul_le_mul hR hRR (norm_nonneg (R * R)) hq)
  calc
    ‖(R * R) * R + R * (R * R)‖ ≤
        ‖(R * R) * R‖ + ‖R * (R * R)‖ := norm_add_le _ _
    _ ≤ (q * q) * q + q * (q * q) := add_le_add hleft hright
    _ = 2 * ((q * q) * q) := by ring

/-- Pointwise reciprocal-cube control for the second derivative acting on a state. -/
theorem orthonormalDiagonalHamiltonianResolvent_secondDeriv_apply_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) (x : E) :
    ‖deriv (deriv (orthonormalDiagonalHamiltonianResolvent b a)) lambda x‖ ≤
      (2 * (((delta - lambda)⁻¹ * (delta - lambda)⁻¹) *
        (delta - lambda)⁻¹)) * ‖x‖ := by
  calc
    ‖deriv (deriv (orthonormalDiagonalHamiltonianResolvent b a)) lambda x‖ ≤
        ‖deriv (deriv (orthonormalDiagonalHamiltonianResolvent b a)) lambda‖ * ‖x‖ :=
      (deriv (deriv (orthonormalDiagonalHamiltonianResolvent b a)) lambda).le_opNorm x
    _ ≤ (2 * (((delta - lambda)⁻¹ * (delta - lambda)⁻¹) *
          (delta - lambda)⁻¹)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (orthonormalDiagonalHamiltonianResolvent_secondDeriv_norm_le
          b a delta hdelta hlambda) (norm_nonneg x)

/-- `C²`, exact second derivative formula, and reciprocal-cube control as one package. -/
theorem orthonormalDiagonalHamiltonianResolventSecondDerivative_package
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContDiffOn ℝ 2
        (orthonormalDiagonalHamiltonianResolvent b a)
        (Set.Iio delta) ∧
      DifferentiableOn ℝ
        (deriv (orthonormalDiagonalHamiltonianResolvent b a))
        (Set.Iio delta) ∧
      ∀ {lambda : ℝ} (hlambda : lambda < delta),
        deriv (deriv (orthonormalDiagonalHamiltonianResolvent b a)) lambda =
            ((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
                (orthonormalDiagonalHamiltonianResolvent b a lambda)).comp
              (orthonormalDiagonalHamiltonianResolvent b a lambda) +
            (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
              ((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
                (orthonormalDiagonalHamiltonianResolvent b a lambda)) ∧
          ‖deriv (deriv (orthonormalDiagonalHamiltonianResolvent b a)) lambda‖ ≤
            2 * (((delta - lambda)⁻¹ * (delta - lambda)⁻¹) *
              (delta - lambda)⁻¹) :=
  ⟨orthonormalDiagonalHamiltonianResolvent_contDiffOn_two
      b a delta hdelta,
    orthonormalDiagonalHamiltonianResolvent_deriv_differentiableOn
      b a delta hdelta,
    fun hlambda =>
      ⟨orthonormalDiagonalHamiltonianResolvent_secondDeriv
          b a delta hdelta hlambda,
        orthonormalDiagonalHamiltonianResolvent_secondDeriv_norm_le
          b a delta hdelta hlambda⟩⟩

end MathlibAnalytic
end MGAP4D

end

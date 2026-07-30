import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventIdentityContinuityBundle
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 800000

/-- The total real resolvent is continuous in operator norm on the open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_continuousOn
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContinuousOn
      (orthonormalDiagonalHamiltonianResolvent b a)
      (Set.Iio delta) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq :
      (Set.Iio delta).restrict
          (orthonormalDiagonalHamiltonianResolvent b a) =
        orthonormalDiagonalHamiltonianResolventFamily b a delta := by
    rfl
  rw [heq]
  exact orthonormalDiagonalHamiltonianResolventFamily_continuous
    b a delta hdelta

/-- Below the spectral gap, the operator-norm derivative of the real resolvent is
its square. -/
theorem orthonormalDiagonalHamiltonianResolvent_hasDerivWithinAt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) :
    HasDerivWithinAt
      (orthonormalDiagonalHamiltonianResolvent b a)
      ((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
        (orthonormalDiagonalHamiltonianResolvent b a lambda))
      (Set.Iio delta) lambda := by
  refine (hasDerivWithinAt_iff_tendsto_slope
    (𝕜 := ℝ)
    (f := orthonormalDiagonalHamiltonianResolvent b a)
    (f' := (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
      (orthonormalDiagonalHamiltonianResolvent b a lambda))
    (s := Set.Iio delta)
    (x := lambda)).2 ?_
  let Rlambda := orthonormalDiagonalHamiltonianResolvent b a lambda
  have hres0 :
      Tendsto
        (orthonormalDiagonalHamiltonianResolvent b a)
        (𝓝[Set.Iio delta] lambda)
        (𝓝 (orthonormalDiagonalHamiltonianResolvent b a lambda)) :=
    orthonormalDiagonalHamiltonianResolvent_continuousOn
      b a delta hdelta lambda hlambda
  have hres :
      Tendsto
        (orthonormalDiagonalHamiltonianResolvent b a)
        (𝓝[Set.Iio delta] lambda) (𝓝 Rlambda) := by
    simpa [Rlambda] using hres0
  have hres' :
      Tendsto
        (orthonormalDiagonalHamiltonianResolvent b a)
        (𝓝[Set.Iio delta \ {lambda}] lambda) (𝓝 Rlambda) :=
    hres.mono_left <| nhdsWithin_mono _ <| by
      intro mu hmu
      exact hmu.1
  have hcomp :
      Tendsto
        (fun mu =>
          (orthonormalDiagonalHamiltonianResolvent b a mu).comp Rlambda)
        (𝓝[Set.Iio delta \ {lambda}] lambda)
        (𝓝 (Rlambda.comp Rlambda)) := by
    exact
      (continuous_id.clm_comp_const Rlambda).continuousAt.tendsto.comp hres'
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with mu hmu
  rcases hmu with ⟨hmuDelta, hmuNe⟩
  have hne : mu - lambda ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [mem_singleton_iff] using hmuNe
  rw [slope_def_module,
    orthonormalDiagonalHamiltonianResolvent_sub_eq_smul_mul
      b a delta hdelta hmuDelta hlambda,
    inv_smul_smul₀ hne]

/-- Since the sub-gap interval is open, the within-derivative is the ordinary
operator-norm derivative. -/
theorem orthonormalDiagonalHamiltonianResolvent_hasDerivAt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) :
    HasDerivAt
      (orthonormalDiagonalHamiltonianResolvent b a)
      ((orthonormalDiagonalHamiltonianResolvent b a lambda).comp
        (orthonormalDiagonalHamiltonianResolvent b a lambda))
      lambda := by
  let d :=
    (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
      (orthonormalDiagonalHamiltonianResolvent b a lambda)
  have hwithin :
      HasDerivWithinAt
        (orthonormalDiagonalHamiltonianResolvent b a)
        d (Set.Iio delta) lambda := by
    simpa [d] using
      orthonormalDiagonalHamiltonianResolvent_hasDerivWithinAt
        b a delta hdelta hlambda
  have hfwithin :
      HasFDerivWithinAt
        (orthonormalDiagonalHamiltonianResolvent b a)
        (toSpanSingleton ℝ d) (Set.Iio delta) lambda :=
    hwithin.hasFDerivWithinAt
  have hfat :
      HasFDerivAt
        (orthonormalDiagonalHamiltonianResolvent b a)
        (toSpanSingleton ℝ d) lambda :=
    hfwithin.hasFDerivAt (Iio_mem_nhds hlambda)
  have hd :
      HasDerivAt
        (orthonormalDiagonalHamiltonianResolvent b a)
        ((toSpanSingleton ℝ d) 1) lambda :=
    (hasFDerivAt_iff_hasDerivAt).1 hfat
  simpa [d] using hd

/-- Explicit operator-norm derivative formula for the real resolvent. -/
theorem orthonormalDiagonalHamiltonianResolvent_deriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) :
    deriv (orthonormalDiagonalHamiltonianResolvent b a) lambda =
      (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
        (orthonormalDiagonalHamiltonianResolvent b a lambda) := by
  let d :=
    (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
      (orthonormalDiagonalHamiltonianResolvent b a lambda)
  have hd :
      HasDerivAt
        (orthonormalDiagonalHamiltonianResolvent b a)
        d lambda := by
    simpa [d] using
      orthonormalDiagonalHamiltonianResolvent_hasDerivAt
        b a delta hdelta hlambda
  have hf :
      HasFDerivAt
        (orthonormalDiagonalHamiltonianResolvent b a)
        (toSpanSingleton ℝ d) lambda :=
    hd.hasFDerivAt
  have hfd :
      fderiv ℝ (orthonormalDiagonalHamiltonianResolvent b a) lambda =
        toSpanSingleton ℝ d :=
    hf.fderiv
  unfold deriv
  rw [hfd]
  simp [d]

/-- The real resolvent is differentiable in operator norm throughout the open
sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_differentiableOn
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    DifferentiableOn ℝ
      (orthonormalDiagonalHamiltonianResolvent b a)
      (Set.Iio delta) := by
  intro lambda hlambda
  let d :=
    (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
      (orthonormalDiagonalHamiltonianResolvent b a lambda)
  have hwithin :
      HasDerivWithinAt
        (orthonormalDiagonalHamiltonianResolvent b a)
        d (Set.Iio delta) lambda := by
    simpa [d] using
      orthonormalDiagonalHamiltonianResolvent_hasDerivWithinAt
        b a delta hdelta hlambda
  exact ⟨toSpanSingleton ℝ d, hwithin.hasFDerivWithinAt⟩

/-- The operator-norm derivative of the real resolvent is continuous below the gap. -/
theorem orthonormalDiagonalHamiltonianResolvent_continuousOn_deriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContinuousOn
      (deriv (orthonormalDiagonalHamiltonianResolvent b a))
      (Set.Iio delta) := by
  have hdiff :=
    orthonormalDiagonalHamiltonianResolvent_differentiableOn
      b a delta hdelta
  have hsquare :
      ContinuousOn
        (fun lambda =>
          (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
            (orthonormalDiagonalHamiltonianResolvent b a lambda))
        (Set.Iio delta) :=
    (hdiff.clm_comp hdiff).continuousOn
  apply hsquare.congr
  intro lambda hlambda
  exact orthonormalDiagonalHamiltonianResolvent_deriv
    b a delta hdelta hlambda

/-- The real resolvent is `C¹` in operator norm on the complete open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_contDiffOn_one
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContDiffOn ℝ 1
      (orthonormalDiagonalHamiltonianResolvent b a)
      (Set.Iio delta) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
  refine ⟨orthonormalDiagonalHamiltonianResolvent_differentiableOn
      b a delta hdelta, ?_, ?_⟩
  · simp
  · simpa only [contDiffOn_zero] using
      orthonormalDiagonalHamiltonianResolvent_continuousOn_deriv
        b a delta hdelta

/-- Exact reciprocal-square distance-to-gap bound for the resolvent derivative. -/
theorem orthonormalDiagonalHamiltonianResolvent_deriv_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) :
    ‖deriv (orthonormalDiagonalHamiltonianResolvent b a) lambda‖ ≤
      (delta - lambda)⁻¹ * (delta - lambda)⁻¹ := by
  rw [orthonormalDiagonalHamiltonianResolvent_deriv
    b a delta hdelta hlambda]
  change ‖orthonormalDiagonalHamiltonianResolvent b a lambda *
      orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
    (delta - lambda)⁻¹ * (delta - lambda)⁻¹
  have hR :=
    orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
      b a delta lambda hdelta hlambda
  exact (norm_mul_le _ _).trans
    (mul_le_mul hR hR (norm_nonneg _)
      (inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)))

/-- Pointwise reciprocal-square control for the derivative acting on a state. -/
theorem orthonormalDiagonalHamiltonianResolvent_deriv_apply_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) (x : E) :
    ‖deriv (orthonormalDiagonalHamiltonianResolvent b a) lambda x‖ ≤
      ((delta - lambda)⁻¹ * (delta - lambda)⁻¹) * ‖x‖ := by
  calc
    ‖deriv (orthonormalDiagonalHamiltonianResolvent b a) lambda x‖ ≤
        ‖deriv (orthonormalDiagonalHamiltonianResolvent b a) lambda‖ * ‖x‖ :=
      (deriv (orthonormalDiagonalHamiltonianResolvent b a) lambda).le_opNorm x
    _ ≤ ((delta - lambda)⁻¹ * (delta - lambda)⁻¹) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (orthonormalDiagonalHamiltonianResolvent_deriv_norm_le
          b a delta hdelta hlambda) (norm_nonneg x)

/-- `C¹`, derivative formula, and exact derivative norm control as one package. -/
theorem orthonormalDiagonalHamiltonianResolventDerivative_package
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContDiffOn ℝ 1
        (orthonormalDiagonalHamiltonianResolvent b a)
        (Set.Iio delta) ∧
      DifferentiableOn ℝ
        (orthonormalDiagonalHamiltonianResolvent b a)
        (Set.Iio delta) ∧
      ∀ {lambda : ℝ} (hlambda : lambda < delta),
        deriv (orthonormalDiagonalHamiltonianResolvent b a) lambda =
            (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
              (orthonormalDiagonalHamiltonianResolvent b a lambda) ∧
          ‖deriv (orthonormalDiagonalHamiltonianResolvent b a) lambda‖ ≤
            (delta - lambda)⁻¹ * (delta - lambda)⁻¹ :=
  ⟨orthonormalDiagonalHamiltonianResolvent_contDiffOn_one
      b a delta hdelta,
    orthonormalDiagonalHamiltonianResolvent_differentiableOn
      b a delta hdelta,
    fun hlambda =>
      ⟨orthonormalDiagonalHamiltonianResolvent_deriv
          b a delta hdelta hlambda,
        orthonormalDiagonalHamiltonianResolvent_deriv_norm_le
          b a delta hdelta hlambda⟩⟩

end MathlibAnalytic
end MGAP4D

end

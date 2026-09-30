import MGAP4D.MathlibAnalytic.ProbabilityMeasureMutualDominationBoundedTest
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# L² mean-difference control from mutual probability-measure domination

This file is the variance-sensitive replacement for applying a bounded-test
total-variation estimate to an arbitrary L² observable.

If two probability measures satisfy the mutual Harnack bounds

  μ ≤ K ν,   ν ≤ K μ,   1 ≤ K,

then, for any integrable real function g,

  |μ[g] - ν[g]| ≤ t (μ[|g|] + ν[|g|]),
  t = (K - 1) / (K + 1).

The proof uses only nonnegative integral comparison and positive/negative
parts; no L∞ bound is imposed on g.

For an L² observable f, center at the midpoint of the two means.  When
K ≤ 3 (equivalently t ≤ 1/2), variance nonnegativity and the probability
normalization yield

  (μ[f] - ν[f])²
    ≤ (2 t)² (Var_μ(f) + Var_ν(f)).

Thus the coefficient is exactly the square of the repository's existing
bounded-test Harnack coefficient 2 (K - 1) / (K + 1), but the statement is
genuinely L² and variance-sensitive.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Nonnegative integral comparison in the sharp symmetric Harnack form.
This is the scalar measure-theoretic core used before splitting a general
integrable function into positive and negative parts. -/
theorem probabilityMeasure_nonnegative_integral_difference_abs_le_of_pairwise_le_smul
    {α : Type*}
    [MeasurableSpace α]
    (μ ν : Measure α)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (K : ℝ)
    (hK : 1 ≤ K)
    (hμν : μ ≤ ENNReal.ofReal K • ν)
    (hνμ : ν ≤ ENNReal.ofReal K • μ)
    (g : α → ℝ)
    (hgNonneg : ∀ x, 0 ≤ g x)
    (hgμ : Integrable g μ)
    (hgν : Integrable g ν) :
    |(∫ x, g x ∂μ) - (∫ x, g x ∂ν)| ≤
      ((K - 1) / (K + 1)) *
        ((∫ x, g x ∂μ) + (∫ x, g x ∂ν)) := by
  have hKnonneg : 0 ≤ K := by linarith
  have hKtop : ENNReal.ofReal K ≠ ∞ := ENNReal.ofReal_ne_top
  have hμνInt :
      (∫ x, g x ∂μ) ≤ K * ∫ x, g x ∂ν := by
    calc
      (∫ x, g x ∂μ) ≤ ∫ x, g x ∂(ENNReal.ofReal K • ν) := by
        exact integral_mono_measure hμν
          (Filter.Eventually.of_forall hgNonneg)
          (hgν.smul_measure hKtop)
      _ = K * ∫ x, g x ∂ν := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hνμInt :
      (∫ x, g x ∂ν) ≤ K * ∫ x, g x ∂μ := by
    calc
      (∫ x, g x ∂ν) ≤ ∫ x, g x ∂(ENNReal.ofReal K • μ) := by
        exact integral_mono_measure hνμ
          (Filter.Eventually.of_forall hgNonneg)
          (hgμ.smul_measure hKtop)
      _ = K * ∫ x, g x ∂μ := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hden : 0 < K + 1 := by linarith
  have hUpper :
      (∫ x, g x ∂μ) - (∫ x, g x ∂ν) ≤
        ((K - 1) / (K + 1)) *
          ((∫ x, g x ∂μ) + (∫ x, g x ∂ν)) := by
    rw [show
      ((K - 1) / (K + 1)) *
          ((∫ x, g x ∂μ) + (∫ x, g x ∂ν)) =
        ((K - 1) *
          ((∫ x, g x ∂μ) + (∫ x, g x ∂ν))) / (K + 1) by ring]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hLower :
      -(((K - 1) / (K + 1)) *
          ((∫ x, g x ∂μ) + (∫ x, g x ∂ν))) ≤
        (∫ x, g x ∂μ) - (∫ x, g x ∂ν) := by
    rw [neg_le_sub_iff_le_add]
    rw [show
      (∫ x, g x ∂ν) ≤
          (∫ x, g x ∂μ) +
            ((K - 1) / (K + 1)) *
              ((∫ x, g x ∂μ) + (∫ x, g x ∂ν)) ↔
        (∫ x, g x ∂ν) - (∫ x, g x ∂μ) ≤
            ((K - 1) / (K + 1)) *
              ((∫ x, g x ∂μ) + (∫ x, g x ∂ν)) by
          constructor <;> intro h <;> linarith]
    rw [show
      ((K - 1) / (K + 1)) *
          ((∫ x, g x ∂μ) + (∫ x, g x ∂ν)) =
        ((K - 1) *
          ((∫ x, g x ∂μ) + (∫ x, g x ∂ν))) / (K + 1) by ring]
    apply (le_div_iff₀ hden).2
    nlinarith
  exact abs_le.mpr ⟨hLower, hUpper⟩

/-- Mutual Harnack domination controls the difference of expectations of every
integrable real function by the sum of its two L¹ norms.  Unlike the bounded
test theorem, this statement has no pointwise boundedness hypothesis. -/
theorem probabilityMeasure_integral_difference_abs_le_integral_abs_of_pairwise_le_smul
    {α : Type*}
    [MeasurableSpace α]
    (μ ν : Measure α)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (K : ℝ)
    (hK : 1 ≤ K)
    (hμν : μ ≤ ENNReal.ofReal K • ν)
    (hνμ : ν ≤ ENNReal.ofReal K • μ)
    (f : α → ℝ)
    (hfμ : Integrable f μ)
    (hfν : Integrable f ν) :
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤
      ((K - 1) / (K + 1)) *
        ((∫ x, |f x| ∂μ) + (∫ x, |f x| ∂ν)) := by
  let fp : α → ℝ := fun x => max (f x) 0
  let fn : α → ℝ := fun x => max (-f x) 0
  have hfpμ : Integrable fp μ := by
    simpa [fp] using hfμ.pos_part
  have hfpν : Integrable fp ν := by
    simpa [fp] using hfν.pos_part
  have hfnμ : Integrable fn μ := by
    simpa [fn] using hfμ.neg_part
  have hfnν : Integrable fn ν := by
    simpa [fn] using hfν.neg_part
  have hfpNonneg : ∀ x, 0 ≤ fp x := by
    intro x
    exact le_max_right _ _
  have hfnNonneg : ∀ x, 0 ≤ fn x := by
    intro x
    exact le_max_right _ _
  have hp :=
    probabilityMeasure_nonnegative_integral_difference_abs_le_of_pairwise_le_smul
      μ ν K hK hμν hνμ fp hfpNonneg hfpμ hfpν
  have hn :=
    probabilityMeasure_nonnegative_integral_difference_abs_le_of_pairwise_le_smul
      μ ν K hK hμν hνμ fn hfnNonneg hfnμ hfnν
  have hdecomp : ∀ x, f x = fp x - fn x := by
    intro x
    dsimp [fp, fn]
    by_cases hx : 0 ≤ f x
    · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    · have hx' : f x ≤ 0 := le_of_not_ge hx
      simp [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
  have habs : ∀ x, |f x| = fp x + fn x := by
    intro x
    dsimp [fp, fn]
    by_cases hx : 0 ≤ f x
    · simp [abs_of_nonneg hx, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    · have hx' : f x ≤ 0 := le_of_not_ge hx
      simp [abs_of_nonpos hx', max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
  have hfμDecomp :
      (∫ x, f x ∂μ) = (∫ x, fp x ∂μ) - ∫ x, fn x ∂μ := by
    calc
      (∫ x, f x ∂μ) = ∫ x, fp x - fn x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hdecomp
      _ = (∫ x, fp x ∂μ) - ∫ x, fn x ∂μ :=
        integral_sub hfpμ hfnμ
  have hfνDecomp :
      (∫ x, f x ∂ν) = (∫ x, fp x ∂ν) - ∫ x, fn x ∂ν := by
    calc
      (∫ x, f x ∂ν) = ∫ x, fp x - fn x ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hdecomp
      _ = (∫ x, fp x ∂ν) - ∫ x, fn x ∂ν :=
        integral_sub hfpν hfnν
  have habsμ :
      (∫ x, |f x| ∂μ) =
        (∫ x, fp x ∂μ) + ∫ x, fn x ∂μ := by
    calc
      (∫ x, |f x| ∂μ) = ∫ x, fp x + fn x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall habs
      _ = (∫ x, fp x ∂μ) + ∫ x, fn x ∂μ :=
        integral_add hfpμ hfnμ
  have habsν :
      (∫ x, |f x| ∂ν) =
        (∫ x, fp x ∂ν) + ∫ x, fn x ∂ν := by
    calc
      (∫ x, |f x| ∂ν) = ∫ x, fp x + fn x ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall habs
      _ = (∫ x, fp x ∂ν) + ∫ x, fn x ∂ν :=
        integral_add hfpν hfnν
  rw [hfμDecomp, hfνDecomp, habsμ, habsν]
  have htriangle :
      |((∫ x, fp x ∂μ) - (∫ x, fp x ∂ν)) -
          ((∫ x, fn x ∂μ) - (∫ x, fn x ∂ν))| ≤
        |(∫ x, fp x ∂μ) - (∫ x, fp x ∂ν)| +
          |(∫ x, fn x ∂μ) - (∫ x, fn x ∂ν)| := by
    exact abs_sub _ _
  calc
    |((∫ x, fp x ∂μ) - ∫ x, fn x ∂μ) -
        ((∫ x, fp x ∂ν) - ∫ x, fn x ∂ν)| =
      |((∫ x, fp x ∂μ) - (∫ x, fp x ∂ν)) -
        ((∫ x, fn x ∂μ) - (∫ x, fn x ∂ν))| := by
          congr 1
          ring
    _ ≤
        |(∫ x, fp x ∂μ) - (∫ x, fp x ∂ν)| +
          |(∫ x, fn x ∂μ) - (∫ x, fn x ∂ν)| := htriangle
    _ ≤
        ((K - 1) / (K + 1)) *
          ((∫ x, fp x ∂μ) + (∫ x, fp x ∂ν)) +
        ((K - 1) / (K + 1)) *
          ((∫ x, fn x ∂μ) + (∫ x, fn x ∂ν)) :=
      _root_.add_le_add hp hn
    _ =
        ((K - 1) / (K + 1)) *
          (((∫ x, fp x ∂μ) + ∫ x, fn x ∂μ) +
            ((∫ x, fp x ∂ν) + ∫ x, fn x ∂ν)) := by
      ring

/-- On a probability space, the square of the L¹ norm of a real L² function
is bounded by its second moment.  This is Cauchy--Schwarz recovered from
nonnegativity of the variance of |g|. -/
theorem probabilityMeasure_integral_abs_sq_le_integral_sq
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    [IsProbabilityMeasure μ]
    (g : α → ℝ)
    (hg : MemLp g 2 μ) :
    (∫ x, |g x| ∂μ) ^ 2 ≤ ∫ x, (g x) ^ 2 ∂μ := by
  have habs : MemLp (fun x => |g x|) 2 μ := by
    simpa [Real.norm_eq_abs] using hg.abs
  have hvar := variance_nonneg (fun x => |g x|) μ
  rw [variance_eq_sub habs] at hvar
  have hvar' :
      0 ≤ (∫ x, |g x| ^ 2 ∂μ) - (∫ x, |g x| ∂μ) ^ 2 := by
    simpa only [Pi.pow_apply] using hvar
  have hsq :
      (∫ x, |g x| ^ 2 ∂μ) = ∫ x, (g x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    exact sq_abs (g x)
  rw [hsq] at hvar'
  nlinarith

/-- Exact second-moment decomposition around an arbitrary constant center:
squared residual = variance + squared displacement of the mean. -/
theorem probabilityMeasure_integral_sq_sub_const_eq_variance_add_mean_sub_sq
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    [IsProbabilityMeasure μ]
    (f : α → ℝ)
    (hf : MemLp f 2 μ)
    (c : ℝ) :
    (∫ x, (f x - c) ^ 2 ∂μ) =
      variance f μ + ((∫ x, f x ∂μ) - c) ^ 2 := by
  let g : α → ℝ := fun x => f x - c
  have hg : MemLp g 2 μ := by
    exact hf.sub (memLp_const c)
  have hmean :
      (∫ x, g x ∂μ) = (∫ x, f x ∂μ) - c := by
    dsimp [g]
    rw [integral_sub (hf.integrable one_le_two) (integrable_const c)]
    simp
  have hshift : variance g μ = variance f μ := by
    dsimp [g]
    exact variance_sub_const hf.aestronglyMeasurable c
  have hvar :
      variance g μ =
        (∫ x, (g x) ^ 2 ∂μ) - (∫ x, g x ∂μ) ^ 2 := by
    simpa only [Pi.pow_apply] using (variance_eq_sub hg)
  change
    (∫ x, (g x) ^ 2 ∂μ) =
      variance f μ + ((∫ x, f x ∂μ) - c) ^ 2
  rw [← hshift, ← hmean]
  linarith

/-- Variance-sensitive mean-difference estimate under mutual Harnack
domination.  The coefficient is the square of the sharp bounded-test
coefficient.  The restriction K ≤ 3 is sufficient for the elementary
absorption step and matches the existing cross-boundary high-temperature
threshold. -/
theorem probabilityMeasure_integral_difference_sq_le_variance_sum_of_pairwise_le_smul
    {α : Type*}
    [MeasurableSpace α]
    (μ ν : Measure α)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (K : ℝ)
    (hK : 1 ≤ K)
    (hK3 : K ≤ 3)
    (hμν : μ ≤ ENNReal.ofReal K • ν)
    (hνμ : ν ≤ ENNReal.ofReal K • μ)
    (f : α → ℝ)
    (hfμ : MemLp f 2 μ)
    (hfν : MemLp f 2 ν) :
    ((∫ x, f x ∂μ) - (∫ x, f x ∂ν)) ^ 2 ≤
      (2 * ((K - 1) / (K + 1))) ^ 2 *
        (variance f μ + variance f ν) := by
  let mμ : ℝ := ∫ x, f x ∂μ
  let mν : ℝ := ∫ x, f x ∂ν
  let d : ℝ := mμ - mν
  let c : ℝ := (mμ + mν) / 2
  let t : ℝ := (K - 1) / (K + 1)
  let g : α → ℝ := fun x => f x - c
  have hden : 0 < K + 1 := by linarith
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (sub_nonneg.mpr hK) hden.le
  have htHalf : t ≤ (1 : ℝ) / 2 := by
    dsimp [t]
    apply (div_le_iff₀ hden).2
    nlinarith
  have htSqHalf : t ^ 2 ≤ (1 : ℝ) / 2 := by
    have hprod : 0 ≤ t * ((1 : ℝ) / 2 - t) :=
      mul_nonneg ht0 (sub_nonneg.mpr htHalf)
    nlinarith
  have hgμ : MemLp g 2 μ := by
    exact hfμ.sub (memLp_const c)
  have hgν : MemLp g 2 ν := by
    exact hfν.sub (memLp_const c)
  have hgIntμ : Integrable g μ := hgμ.integrable one_le_two
  have hgIntν : Integrable g ν := hgν.integrable one_le_two
  have hmeanμ : (∫ x, g x ∂μ) = mμ - c := by
    dsimp [g]
    rw [integral_sub (hfμ.integrable one_le_two) (integrable_const c)]
    simp [mμ]
  have hmeanν : (∫ x, g x ∂ν) = mν - c := by
    dsimp [g]
    rw [integral_sub (hfν.integrable one_le_two) (integrable_const c)]
    simp [mν]
  have hdiff : (∫ x, g x ∂μ) - (∫ x, g x ∂ν) = d := by
    rw [hmeanμ, hmeanν]
    dsimp [d]
    ring
  have hL1 :=
    probabilityMeasure_integral_difference_abs_le_integral_abs_of_pairwise_le_smul
      μ ν K hK hμν hνμ g hgIntμ hgIntν
  rw [hdiff] at hL1
  change
    |d| ≤ t * ((∫ x, |g x| ∂μ) + ∫ x, |g x| ∂ν)
    at hL1
  let a : ℝ := ∫ x, |g x| ∂μ
  let b : ℝ := ∫ x, |g x| ∂ν
  let A : ℝ := ∫ x, (g x) ^ 2 ∂μ
  let B : ℝ := ∫ x, (g x) ^ 2 ∂ν
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact integral_nonneg fun x => abs_nonneg _
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact integral_nonneg fun x => abs_nonneg _
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x => sq_nonneg _
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun x => sq_nonneg _
  have haSq : a ^ 2 ≤ A := by
    dsimp [a, A]
    exact probabilityMeasure_integral_abs_sq_le_integral_sq μ g hgμ
  have hbSq : b ^ 2 ≤ B := by
    dsimp [b, B]
    exact probabilityMeasure_integral_abs_sq_le_integral_sq ν g hgν
  have habSq : (a + b) ^ 2 ≤ 2 * (A + B) := by
    nlinarith [sq_nonneg (a - b)]
  have hL1' : |d| ≤ t * (a + b) := by
    simpa [a, b] using hL1
  have hright0 : 0 ≤ t * (a + b) :=
    mul_nonneg ht0 (add_nonneg ha0 hb0)
  have hsq :
      d ^ 2 ≤ t ^ 2 * (a + b) ^ 2 := by
    have hsq' :=
      (sq_le_sq₀ (abs_nonneg d) hright0).2 hL1'
    simpa only [sq_abs, mul_pow] using hsq'
  have hscaled :
      t ^ 2 * (a + b) ^ 2 ≤ t ^ 2 * (2 * (A + B)) :=
    mul_le_mul_of_nonneg_left habSq (sq_nonneg t)
  have hcore : d ^ 2 ≤ 2 * t ^ 2 * (A + B) := by
    calc
      d ^ 2 ≤ t ^ 2 * (a + b) ^ 2 := hsq
      _ ≤ t ^ 2 * (2 * (A + B)) := hscaled
      _ = 2 * t ^ 2 * (A + B) := by ring
  have hAeq :
      A = variance f μ + (d / 2) ^ 2 := by
    calc
      A = ∫ x, (f x - c) ^ 2 ∂μ := by
        rfl
      _ = variance f μ + ((∫ x, f x ∂μ) - c) ^ 2 :=
        probabilityMeasure_integral_sq_sub_const_eq_variance_add_mean_sub_sq
          μ f hfμ c
      _ = variance f μ + (d / 2) ^ 2 := by
        have hmid : (∫ x, f x ∂μ) - c = d / 2 := by
          dsimp [c, d, mμ, mν]
          ring
        rw [hmid]
  have hBeq :
      B = variance f ν + (d / 2) ^ 2 := by
    calc
      B = ∫ x, (f x - c) ^ 2 ∂ν := by
        rfl
      _ = variance f ν + ((∫ x, f x ∂ν) - c) ^ 2 :=
        probabilityMeasure_integral_sq_sub_const_eq_variance_add_mean_sub_sq
          ν f hfν c
      _ = variance f ν + (d / 2) ^ 2 := by
        have hmid : (∫ x, f x ∂ν) - c = -(d / 2) := by
          dsimp [c, d, mμ, mν]
          ring
        rw [hmid, neg_sq]
  rw [hAeq, hBeq] at hcore
  have hV :
      0 ≤ variance f μ + variance f ν :=
    add_nonneg (variance_nonneg f μ) (variance_nonneg f ν)
  have hrearr :
      (1 - t ^ 2) * d ^ 2 ≤
        2 * t ^ 2 * (variance f μ + variance f ν) := by
    nlinarith
  have hcoef : (1 : ℝ) / 2 ≤ 1 - t ^ 2 := by
    linarith
  have hleft :
      ((1 : ℝ) / 2) * d ^ 2 ≤ (1 - t ^ 2) * d ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef (sq_nonneg d)
  have hfinal :
      d ^ 2 ≤ 4 * t ^ 2 * (variance f μ + variance f ν) := by
    nlinarith [hleft.trans hrearr]
  change d ^ 2 ≤ (2 * t) ^ 2 * (variance f μ + variance f ν)
  nlinarith

end

end MathlibAnalytic
end MGAP4D

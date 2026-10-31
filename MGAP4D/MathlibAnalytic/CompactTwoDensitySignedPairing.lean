import MGAP4D.MathlibAnalytic.ContinuousNormalizedExponentialOscillation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Tactic

/-!
# Exact signed pairing of two normalized densities

The two-copy product measure is an auxiliary integration device. Neither
original density is replaced by the reference measure. Sign cancellation
is retained inside a symmetric two-point integrand, before taking bounds.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
noncomputable section
set_option autoImplicit false

/-- Symmetric response difference times the antisymmetric density determinant. -/
def twoDensitySignedPair {X : Type*} (p q f : X → ℝ) (z : X × X) : ℝ :=
  (f z.1 - f z.2) * (p z.1 * q z.2 - q z.1 * p z.2)

/-- Both differences change sign under swapping the auxiliary copies. -/
theorem twoDensitySignedPair_swap {X : Type*} (p q f : X → ℝ) (x y : X) :
    twoDensitySignedPair p q f (y, x) = twoDensitySignedPair p q f (x, y) := by
  unfold twoDensitySignedPair
  ring

/-- Continuity of the full signed pair, without an absolute-value replacement. -/
theorem twoDensitySignedPair_continuous
    {X : Type*} [TopologicalSpace X] (p q f : X → ℝ)
    (hp : Continuous p) (hq : Continuous q) (hf : Continuous f) :
    Continuous (twoDensitySignedPair p q f) :=
  ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).mul
    (((hp.comp continuous_fst).mul (hq.comp continuous_snd)).sub
      ((hq.comp continuous_fst).mul (hp.comp continuous_snd)))

/-- A cross-density response difference integrates to the difference of the
original two density-weighted expectations. -/
theorem integral_twoDensityCrossPair
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p q f : X → ℝ) (hp : Continuous p) (hq : Continuous q) (hf : Continuous f)
    (hp1 : (∫ x, p x ∂μ) = 1) (hq1 : (∫ x, q x ∂μ) = 1) :
    (∫ z : X × X, (f z.1 - f z.2) * p z.1 * q z.2 ∂μ.prod μ) =
      (∫ x, p x * f x ∂μ) - (∫ x, q x * f x ∂μ) := by
  have hA : Integrable (fun z : X × X => (p z.1 * f z.1) * q z.2) (μ.prod μ) :=
    (((hp.mul hf).comp continuous_fst).mul (hq.comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun z : X × X => p z.1 * (q z.2 * f z.2)) (μ.prod μ) :=
    ((hp.comp continuous_fst).mul ((hq.mul hf).comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ z : X × X, (p z.1 * f z.1) * q z.2 -
        p z.1 * (q z.2 * f z.2) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ = (∫ z : X × X, (p z.1 * f z.1) * q z.2 ∂μ.prod μ) -
        (∫ z : X × X, p z.1 * (q z.2 * f z.2) ∂μ.prod μ) := integral_sub hA hB
    _ = _ := by
      rw [integral_prod_mul (μ := μ) (ν := μ) (fun x : X => p x * f x) q,
        integral_prod_mul (μ := μ) (ν := μ) p (fun x : X => q x * f x),
        hq1, hp1, mul_one, one_mul]

/-- Exact antisymmetrization: twice the original signed expectation gap.
The normalization hypotheses are explicit and no sign hypothesis is added. -/
theorem integral_twoDensitySignedPair_eq_two_mul_gap
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p q f : X → ℝ) (hp : Continuous p) (hq : Continuous q) (hf : Continuous f)
    (hp1 : (∫ x, p x ∂μ) = 1) (hq1 : (∫ x, q x ∂μ) = 1) :
    (∫ z : X × X, twoDensitySignedPair p q f z ∂μ.prod μ) =
      2 * ((∫ x, p x * f x ∂μ) - (∫ x, q x * f x ∂μ)) := by
  have hd : Continuous (fun z : X × X => f z.1 - f z.2) :=
    (hf.comp continuous_fst).sub (hf.comp continuous_snd)
  have hA : Integrable (fun z : X × X => (f z.1 - f z.2) * p z.1 * q z.2)
      (μ.prod μ) :=
    ((hd.mul (hp.comp continuous_fst)).mul (hq.comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun z : X × X => (f z.1 - f z.2) * q z.1 * p z.2)
      (μ.prod μ) :=
    ((hd.mul (hq.comp continuous_fst)).mul (hp.comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ z : X × X, (f z.1 - f z.2) * p z.1 * q z.2 -
        (f z.1 - f z.2) * q z.1 * p z.2 ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with z
      unfold twoDensitySignedPair
      ring
    _ = (∫ z : X × X, (f z.1 - f z.2) * p z.1 * q z.2 ∂μ.prod μ) -
        (∫ z : X × X, (f z.1 - f z.2) * q z.1 * p z.2 ∂μ.prod μ) :=
      integral_sub hA hB
    _ = _ := by
      rw [integral_twoDensityCrossPair μ p q f hp hq hf hp1 hq1,
        integral_twoDensityCrossPair μ q p f hq hp hf hq1 hp1]
      ring

/-- Exact positive-minus-negative decomposition, with both terms integrable. -/
theorem integral_compactContinuous_eq_pos_sub_neg
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂μ) = (∫ x, max (f x) 0 ∂μ) - (∫ x, max (-f x) 0 ∂μ) := by
  have hp : Integrable (fun x => max (f x) 0) μ :=
    (hf.max continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn : Integrable (fun x => max (-f x) 0) μ :=
    (hf.neg.max continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hp hn]
  apply integral_congr_ae
  filter_upwards with x
  by_cases h : 0 ≤ f x
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · have h' : f x ≤ 0 := (lt_of_not_ge h).le
    rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
    ring

/-- Normalized exponential rows have mass one under their actual partition function. -/
theorem integral_compactNormalizedExp_eq_one
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (L : X → ℝ) (hL : Continuous L) :
    (∫ x, continuousNormalizedExp μ L x ∂μ) = 1 := by
  unfold continuousNormalizedExp
  rw [integral_div]
  exact div_self (continuousExpPartition_pos μ L hL).ne'

/-- Exact cross determinant, retaining the genuine common positive weight.
Only the log-odds difference enters the sign-carrying exponential difference. -/
theorem compactNormalizedExp_crossDet_eq
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (L0 L1 : X → ℝ) (x y : X) :
    continuousNormalizedExp μ L0 x * continuousNormalizedExp μ L1 y -
      continuousNormalizedExp μ L1 x * continuousNormalizedExp μ L0 y =
    (Real.exp (L1 x) * Real.exp (L1 y) /
      (continuousExpPartition μ L0 * continuousExpPartition μ L1)) *
        (Real.exp (L0 x - L1 x) - Real.exp (L0 y - L1 y)) := by
  have hx : Real.exp (L0 x) = Real.exp (L1 x) * Real.exp (L0 x - L1 x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hy : Real.exp (L0 y) = Real.exp (L1 y) * Real.exp (L0 y - L1 y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold continuousNormalizedExp
  rw [hx, hy]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual normalized density determinant has precisely the log-odds order.
Positive partition functions are proved from compactness and continuity. -/
theorem compactNormalizedExp_crossDet_nonneg_iff
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (L0 L1 : X → ℝ)
    (hL0 : Continuous L0) (hL1 : Continuous L1) (x y : X) :
    0 ≤ continuousNormalizedExp μ L0 x * continuousNormalizedExp μ L1 y -
      continuousNormalizedExp μ L1 x * continuousNormalizedExp μ L0 y ↔
        L0 y - L1 y ≤ L0 x - L1 x := by
  rw [compactNormalizedExp_crossDet_eq]
  have hc : 0 < Real.exp (L1 x) * Real.exp (L1 y) /
      (continuousExpPartition μ L0 * continuousExpPartition μ L1) :=
    div_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))
      (mul_pos (continuousExpPartition_pos μ L0 hL0) (continuousExpPartition_pos μ L1 hL1))
  constructor
  · intro h
    have he : Real.exp (L0 y - L1 y) ≤ Real.exp (L0 x - L1 x) := by nlinarith
    exact Real.exp_le_exp.mp he
  · intro h
    exact mul_nonneg hc.le (sub_nonneg.mpr (Real.exp_le_exp.mpr h))

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.twoDensitySignedPair_swap
#print axioms MGAP4D.MathlibAnalytic.twoDensitySignedPair_continuous
#print axioms MGAP4D.MathlibAnalytic.integral_twoDensityCrossPair
#print axioms MGAP4D.MathlibAnalytic.integral_twoDensitySignedPair_eq_two_mul_gap
#print axioms MGAP4D.MathlibAnalytic.integral_compactContinuous_eq_pos_sub_neg
#print axioms MGAP4D.MathlibAnalytic.integral_compactNormalizedExp_eq_one
#print axioms MGAP4D.MathlibAnalytic.compactNormalizedExp_crossDet_eq
#print axioms MGAP4D.MathlibAnalytic.compactNormalizedExp_crossDet_nonneg_iff

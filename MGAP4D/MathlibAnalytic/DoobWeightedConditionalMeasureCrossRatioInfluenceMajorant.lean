import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCrossRatioComparison
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureBoundedProbabilityNoMeasurability
import MGAP4D.MathlibAnalytic.ProbabilityMeasureMutualDominationBoundedTest
import MGAP4D.MathlibAnalytic.FinitePositiveWeightCrossRatioInfluenceTransform
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Two probability measures differ by at most two on a real test bounded by
one.  This is the endpoint branch used when a cross-ratio influence majorant is
exactly the trivial full-L1 value two. -/
theorem probabilityMeasure_boundedTest_integral_difference_abs_le_two
    {α : Type*}
    [MeasurableSpace α]
    (μ ν : Measure α)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (phi : α → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ x, |phi x| ≤ 1) :
    |(∫ x, phi x ∂μ) - (∫ x, phi x ∂ν)| ≤ 2 := by
  have hphiIntμ : Integrable phi μ := by
    apply (integrable_const (1 : ℝ)).mono hphi.aestronglyMeasurable
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hphiBound x
  have hphiIntν : Integrable phi ν := by
    apply (integrable_const (1 : ℝ)).mono hphi.aestronglyMeasurable
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hphiBound x
  have hμ :
      |∫ x, phi x ∂μ| ≤ 1 := by
    calc
      |∫ x, phi x ∂μ| ≤ ∫ x, |phi x| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _x : α, (1 : ℝ) ∂μ := by
        apply integral_mono hphiIntμ.abs (integrable_const (1 : ℝ))
        intro x
        exact hphiBound x
      _ = 1 := by simp
  have hν :
      |∫ x, phi x ∂ν| ≤ 1 := by
    calc
      |∫ x, phi x ∂ν| ≤ ∫ x, |phi x| ∂ν :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _x : α, (1 : ℝ) ∂ν := by
        apply integral_mono hphiIntν.abs (integrable_const (1 : ℝ))
        intro x
        exact hphiBound x
      _ = 1 := by simp
  calc
    |(∫ x, phi x ∂μ) - (∫ x, phi x ∂ν)| ≤
        |∫ x, phi x ∂μ| + |∫ x, phi x ∂ν| :=
      abs_sub _ _
    _ ≤ 2 := by linarith

/-- A pointwise family of nonnegative logarithmic cross-ratio radii controls
the full bounded-test difference of the corresponding normalized Doob laws as
soon as every transformed radius is bounded by one common majorant M.

The proof deliberately does not require the supremum producing M to be
attained.  If M = 2, the trivial probability bound closes the endpoint.  If
M < 2, the inverse Mobius transform K = (2 + M) / (2 - M) converts all
radius-wise bounds into one uniform multiplicative cross-ratio constant, after
which normalization cancels through the existing pairwise Doob comparison. -/
theorem doobWeightedMeasure_boundedTest_integral_difference_abs_le_crossRatioInfluenceMajorant
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (w v : α → ℝ≥0∞)
    (radius : α → α → ℝ)
    (M : ℝ)
    (hMNonneg : 0 ≤ M)
    (hMLeTwo : M ≤ 2)
    (hRadiusNonneg : ∀ x y, 0 ≤ radius x y)
    (hInfluence : ∀ x y,
      finitePositiveWeightCrossRatioInfluenceTransform (radius x y) ≤ M)
    (hwtop : ∀ x, w x ≠ ∞)
    (hvtop : ∀ x, v x ≠ ∞)
    (hMassW0 : doobWeightMass μ w ≠ 0)
    (hMassWtop : doobWeightMass μ w ≠ ∞)
    (hMassV0 : doobWeightMass μ v ≠ 0)
    (hMassVtop : doobWeightMass μ v ≠ ∞)
    (hcross : ∀ x y,
      w x * v y ≤
        ENNReal.ofReal (Real.exp (radius x y)) * v x * w y)
    (phi : α → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ x, |phi x| ≤ 1) :
    |(∫ x, phi x ∂doobWeightedMeasure μ w) -
        (∫ x, phi x ∂doobWeightedMeasure μ v)| ≤ M := by
  let μw := doobWeightedMeasure μ w
  let μv := doobWeightedMeasure μ v
  letI : IsProbabilityMeasure μw :=
    ⟨doobWeightedMeasure_measure_univ_without_measurability
      μ w hMassW0 hMassWtop⟩
  letI : IsProbabilityMeasure μv :=
    ⟨doobWeightedMeasure_measure_univ_without_measurability
      μ v hMassV0 hMassVtop⟩
  by_cases hMtwo : M = 2
  · simpa [μw, μv, hMtwo] using
      probabilityMeasure_boundedTest_integral_difference_abs_le_two
        μw μv phi hphi hphiBound
  · have hMlt : M < 2 := lt_of_le_of_ne hMLeTwo hMtwo
    have hTwoSub : 0 < 2 - M := sub_pos.mpr hMlt
    let K : ℝ := (2 + M) / (2 - M)
    have hK : 1 ≤ K := by
      dsimp [K]
      apply (le_div_iff₀ hTwoSub).2
      nlinarith
    have hExpLeK : ∀ x y, Real.exp (radius x y) ≤ K := by
      intro x y
      let z : ℝ := Real.exp (radius x y)
      have hz : 1 ≤ z := by
        dsimp [z]
        simpa using Real.exp_le_exp.mpr (hRadiusNonneg x y)
      have hzDen : 0 < z + 1 := by positivity
      have hT := hInfluence x y
      unfold finitePositiveWeightCrossRatioInfluenceTransform at hT
      change 2 * ((z - 1) / (z + 1)) ≤ M at hT
      have hAlg : 2 * (z - 1) ≤ M * (z + 1) := by
        apply (div_le_iff₀ hzDen).mp
        simpa [mul_div_assoc] using hT
      change z ≤ (2 + M) / (2 - M)
      apply (le_div_iff₀ hTwoSub).2
      nlinarith
    have hCrossUniform : ∀ x y,
        w x * v y ≤ ENNReal.ofReal K * v x * w y := by
      intro x y
      calc
        w x * v y ≤
            ENNReal.ofReal (Real.exp (radius x y)) * v x * w y :=
          hcross x y
        _ ≤ ENNReal.ofReal K * v x * w y := by
          exact mul_le_mul_right'
            (mul_le_mul_right'
              (ENNReal.ofReal_le_ofReal (hExpLeK x y))
              (v x))
            (w y)
    have hPair :=
      doobWeightedMeasure_pairwise_le_mul_of_cross_ratio
        μ w v (ENNReal.ofReal K)
        ENNReal.ofReal_ne_top hwtop hvtop
        hMassW0 hMassWtop hMassV0 hMassVtop hCrossUniform
    have hBound :=
      probabilityMeasure_boundedTest_integral_difference_abs_le_of_pairwise_le_smul
        μw μv K hK
        (by simpa [μw, μv] using hPair.1)
        (by simpa [μw, μv] using hPair.2)
        phi hphi hphiBound
    have hCoeff :
        2 * ((K - 1) / (K + 1)) = M := by
      dsimp [K]
      field_simp [ne_of_gt hTwoSub]
      <;> ring
    rw [hCoeff] at hBound
    simpa [μw, μv] using hBound

end

end MathlibAnalytic
end MGAP4D

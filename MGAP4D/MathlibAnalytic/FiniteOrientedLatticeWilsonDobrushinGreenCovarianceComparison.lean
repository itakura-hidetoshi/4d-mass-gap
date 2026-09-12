import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanGreenCovarianceTelescope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators

noncomputable section

/-- The geometric random-scan temporal covariance estimate forces every fixed
finite-volume temporal covariance to vanish at large time. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanTemporalCovarianceReal_tendsto_zero
    {L : FiniteOrientedLatticeWilsonSystem}
    {g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ) :
    Tendsto
      (fun k : ℕ => L.randomScanTemporalCovarianceReal f g k)
      atTop (nhds 0) := by
  let q : ℝ :=
    finiteOrientedConditionalAverageRandomScanContractionFactor D
  let C : ℝ :=
    L.gibbsMeanAbsoluteDeviationReal f *
      ∑ source : L.Edge, P.variation source
  have hq0 : 0 ≤ q := by
    exact
      finiteOrientedConditionalAverageRandomScanContractionFactor_nonneg
        D hEdge
  have hq1 : q < 1 := by
    exact
      finiteOrientedConditionalAverageRandomScanContractionFactor_lt_one
        D hEdge
  have hEnvelope :
      Tendsto (fun k : ℕ => C * q ^ k) atTop (nhds 0) := by
    have hPow : Tendsto (fun k : ℕ => q ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa using (tendsto_const_nhds.mul hPow)
  have hAbs : ∀ k : ℕ,
      |L.randomScanTemporalCovarianceReal f g k| ≤ C * q ^ k := by
    intro k
    have hCov :=
      P.randomScanTemporalCovarianceReal_abs_le_mad_mul_pow_sum
        D hEdge f k
    dsimp [C, q]
    calc
      |L.randomScanTemporalCovarianceReal f g k| ≤
          L.gibbsMeanAbsoluteDeviationReal f *
            ((finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k *
              ∑ source : L.Edge, P.variation source) := hCov
      _ = (L.gibbsMeanAbsoluteDeviationReal f *
            ∑ source : L.Edge, P.variation source) *
          (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k := by
        ring
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hEventually :
      ∀ᶠ k : ℕ in atTop, C * q ^ k < ε :=
    (tendsto_order.1 hEnvelope).2 ε hε
  rcases eventually_atTop.1 hEventually with ⟨N, hN⟩
  refine ⟨N, fun k hk => ?_⟩
  simpa [Real.dist_eq] using lt_of_le_of_lt (hAbs k) (hN k hk)

/-- The finite Green telescope and temporal covariance decay construct the
proof-relevant Dobrushin Green covariance comparison certificate. -/
theorem finite_oriented_dobrushinGreenCovarianceComparison
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    FiniteOrientedLatticeWilsonDobrushinGreenCovarianceComparison D := by
  refine ⟨?_⟩
  intro f g P Q
  let bound : ℝ :=
    ∑ target : L.Edge,
      ∑ source : L.Edge,
        P.variation target * D.influenceGreenTail 0 target source *
          Q.variation source
  have hTemporal :
      Tendsto
        (fun n : ℕ => L.randomScanTemporalCovarianceReal g f n)
        atTop (nhds 0) :=
    P.randomScanTemporalCovarianceReal_tendsto_zero D hEdge g
  have hDifference :
      Tendsto
        (fun n : ℕ =>
          |L.randomScanTemporalCovarianceReal g f 0 -
            L.randomScanTemporalCovarianceReal g f n|)
        atTop
        (nhds |L.randomScanTemporalCovarianceReal g f 0|) := by
    have hSub :
        Tendsto
          (fun n : ℕ =>
            L.randomScanTemporalCovarianceReal g f 0 -
              L.randomScanTemporalCovarianceReal g f n)
          atTop
          (nhds (L.randomScanTemporalCovarianceReal g f 0 - 0)) :=
      tendsto_const_nhds.sub hTemporal
    simpa using hSub.abs
  have hFinite : ∀ n : ℕ,
      |L.randomScanTemporalCovarianceReal g f 0 -
        L.randomScanTemporalCovarianceReal g f n| ≤ bound := by
    intro n
    exact P.randomScanTemporalCovarianceReal_zero_sub_abs_le_green
      Q D hEdge n
  have hLimit :
      |L.randomScanTemporalCovarianceReal g f 0| ≤ bound :=
    le_of_tendsto' hDifference hFinite
  dsimp [bound] at hLimit ⊢
  calc
    |L.gibbsCovarianceReal f g| =
        |L.gibbsCovarianceReal g f| := by
      rw [finite_oriented_gibbsCovarianceReal_symm]
    _ = |L.randomScanTemporalCovarianceReal g f 0| := by
      rw [finite_oriented_randomScanTemporalCovarianceReal_zero]
    _ ≤ ∑ target : L.Edge,
        ∑ source : L.Edge,
          P.variation target * D.influenceGreenTail 0 target source *
            Q.variation source := hLimit

end

end MathlibAnalytic
end MGAP4D

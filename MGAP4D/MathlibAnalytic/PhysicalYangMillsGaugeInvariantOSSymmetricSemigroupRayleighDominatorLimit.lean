import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupTimeAverageRayleighQuotient
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A scalar upper bound for the two-step correlation defect rate propagates
through the exact time-average Rayleigh correction without any fixed loss.

The fractional map is compared by cross multiplication.  Its mixed nonlinear
terms cancel identically, so the only genuine input is `d_h <= M`. -/
theorem timeAverageClosedRayleighQuotient_le_dominator
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) {psi : P.PhysicalHilbert}
    (hpsi : ‖psi‖ = 1) {M : ℝ}
    (hdM : T.twoStepCorrelationDefectRate h psi ≤ M)
    (hMcorrection : 2 * (h : ℝ) * M < 1) :
    T.timeAverageClosedRayleighQuotient h psi ≤
      M / (1 - 2 * (h : ℝ) * M) := by
  let d : ℝ := T.twoStepCorrelationDefectRate h psi
  have hcoef : 0 ≤ 2 * (h : ℝ) := by positivity
  have hdcorr_le : 2 * (h : ℝ) * d ≤ 2 * (h : ℝ) * M := by
    exact mul_le_mul_of_nonneg_left hdM hcoef
  have hdcorrection : 2 * (h : ℝ) * d < 1 :=
    lt_of_le_of_lt hdcorr_le hMcorrection
  have hq :=
    T.timeAverageClosedRayleighQuotient_le_twoStepDefectRate_div_one_sub_correction
      hSymmetric hh hpsi hdcorrection
  have hLdpos : 0 < 1 - 2 * (h : ℝ) * d := by linarith
  have hLMpos : 0 < 1 - 2 * (h : ℝ) * M := by linarith
  have hfrac : d / (1 - 2 * (h : ℝ) * d) ≤
      M / (1 - 2 * (h : ℝ) * M) := by
    apply (div_le_div_iff₀ hLdpos hLMpos).2
    calc
      d * (1 - 2 * (h : ℝ) * M) =
          d - 2 * (h : ℝ) * d * M := by ring
      _ ≤ M - 2 * (h : ℝ) * d * M :=
        sub_le_sub_right hdM _
      _ = M * (1 - 2 * (h : ℝ) * d) := by ring
  exact hq.trans hfrac

/-- The same scalar dominator supplies nonvanishing of the actual graph-domain
time average.  This is the form needed when the continuum defect itself is
known only through a finite Wilson upper estimate. -/
theorem timeAverageClosedRightHamiltonianDomain_ne_zero_of_unit_and_dominatorCorrection_lt_one
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) {psi : P.PhysicalHilbert}
    (hpsi : ‖psi‖ = 1) {M : ℝ}
    (hdM : T.twoStepCorrelationDefectRate h psi ≤ M)
    (hMcorrection : 2 * (h : ℝ) * M < 1) :
    (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert) ≠ 0 := by
  have hcoef : 0 ≤ 2 * (h : ℝ) := by positivity
  have hdcorr_le :
      2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi ≤
        2 * (h : ℝ) * M :=
    mul_le_mul_of_nonneg_left hdM hcoef
  have hdcorrection :
      2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi < 1 :=
    lt_of_le_of_lt hdcorr_le hMcorrection
  exact
    T.timeAverageClosedRightHamiltonianDomain_ne_zero_of_unit_and_defectCorrection_lt_one
      hSymmetric hh hpsi hdcorrection

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- If the averaging widths vanish and scalar dominators converge, then their
Rayleigh correction factors converge to the same limit.

This is the pure real-analysis tail of moving-state Mosco/Gamma-limsup recovery:
`M_n / (1 - 2 h_n M_n) -> L` whenever `h_n -> 0` and `M_n -> L`. -/
theorem tendsto_dominator_div_one_sub_two_mul_width_mul_dominator
    {h : ℕ → NNReal} {M : ℕ → ℝ} {L : ℝ}
    (hh : Tendsto (fun n => (h n : ℝ)) atTop (nhds 0))
    (hM : Tendsto M atTop (nhds L)) :
    Tendsto
      (fun n => M n / (1 - 2 * (h n : ℝ) * M n))
      atTop (nhds L) := by
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hcorr :
      Tendsto (fun n => 2 * (h n : ℝ) * M n) atTop (nhds 0) := by
    simpa using (htwo.mul hh).mul hM
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hden :
      Tendsto (fun n => 1 - 2 * (h n : ℝ) * M n) atTop (nhds 1) := by
    simpa using hone.sub hcorr
  simpa using hM.div hden (by norm_num : (1 : ℝ) ≠ 0)

/-- Under the same hypotheses the correction denominator is eventually
positive, equivalently `2 h_n M_n < 1`.  No separate boundedness hypothesis is
needed because it follows automatically from convergence of `M_n`. -/
theorem eventually_two_mul_width_mul_dominator_lt_one
    {h : ℕ → NNReal} {M : ℕ → ℝ} {L : ℝ}
    (hh : Tendsto (fun n => (h n : ℝ)) atTop (nhds 0))
    (hM : Tendsto M atTop (nhds L)) :
    ∀ᶠ n in atTop, 2 * (h n : ℝ) * M n < 1 := by
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hcorr :
      Tendsto (fun n => 2 * (h n : ℝ) * M n) atTop (nhds 0) := by
    simpa using (htwo.mul hh).mul hM
  exact hcorr.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))

end

end MathlibAnalytic
end MGAP4D

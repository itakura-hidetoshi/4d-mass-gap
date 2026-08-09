import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupTimeAverageRayleigh
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The actual graph-closed Hamiltonian Rayleigh quotient of the positive-time
average.  The denominator is written on the ambient Hilbert vector so this
quantity can be compared directly with the scalar two-step defect rate. -/
def timeAverageClosedRayleighQuotient
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) : ℝ :=
  inner ℝ
      (T.closedRightHamiltonian
        (T.timeAverageClosedRightHamiltonianDomain h psi))
      (T.timeAverage h psi) /
    ‖T.timeAverage h psi‖ ^ 2

/-- Quantitative nonvanishing lifted from the ambient time average to the
actual graph-closed Hamiltonian-domain state. -/
theorem timeAverageClosedRightHamiltonianDomain_ne_zero_of_unit_and_defectCorrection_lt_one
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) {psi : P.PhysicalHilbert}
    (hpsi : ‖psi‖ = 1)
    (hcorrection :
      2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi < 1) :
    (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert) ≠ 0 := by
  change T.timeAverage h psi ≠ 0
  exact T.timeAverage_ne_zero_of_unit_and_defectCorrection_lt_one
    hSymmetric hh hpsi hcorrection

/-- Exact moving-state Rayleigh estimate.  The only price for passing from the
unnormalized time-average energy to the actual Rayleigh quotient is the
quantitative denominator correction `1 - 2 h d_h`.

In particular there is no fixed coefficient loss: whenever `h d_h -> 0`, the
multiplicative correction tends to one. -/
theorem timeAverageClosedRayleighQuotient_le_twoStepDefectRate_div_one_sub_correction
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) {psi : P.PhysicalHilbert}
    (hpsi : ‖psi‖ = 1)
    (hcorrection :
      2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi < 1) :
    T.timeAverageClosedRayleighQuotient h psi ≤
      T.twoStepCorrelationDefectRate h psi /
        (1 - 2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi) := by
  have hnum := T.inner_closedRightHamiltonian_timeAverage_le_twoStepDefectRate
    hSymmetric hh psi
  have hden := T.norm_sq_sub_two_mul_defectRate_le_timeAverage_norm_sq
    hSymmetric hh psi
  rw [hpsi] at hden
  norm_num at hden
  have hLpos :
      0 < 1 - 2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi := by
    linarith
  have hDpos : 0 < ‖T.timeAverage h psi‖ ^ 2 :=
    lt_of_lt_of_le hLpos hden
  have hd : 0 ≤ T.twoStepCorrelationDefectRate h psi :=
    T.twoStepCorrelationDefectRate_nonneg hSymmetric hh psi
  unfold timeAverageClosedRayleighQuotient
  calc
    inner ℝ
          (T.closedRightHamiltonian
            (T.timeAverageClosedRightHamiltonianDomain h psi))
          (T.timeAverage h psi) /
        ‖T.timeAverage h psi‖ ^ 2 ≤
      T.twoStepCorrelationDefectRate h psi /
        ‖T.timeAverage h psi‖ ^ 2 := by
          exact (div_le_div_iff_of_pos_right hDpos).2 hnum
    _ ≤ T.twoStepCorrelationDefectRate h psi /
        (1 - 2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi) := by
          apply (div_le_div_iff₀ hDpos hLpos).2
          exact mul_le_mul_of_nonneg_left hden hd

/-- Algebraic form of the moving-state correction error.  This identity is the
bridge from the exact quotient estimate to a Mosco/Gamma-limsup statement. -/
theorem defectRate_div_one_sub_correction_sub_defectRate_eq
    (h : NNReal) (d : ℝ)
    (hcorrection : 2 * (h : ℝ) * d < 1) :
    d / (1 - 2 * (h : ℝ) * d) - d =
      (2 * (h : ℝ) * d ^ 2) / (1 - 2 * (h : ℝ) * d) := by
  have hdenpos : 0 < 1 - 2 * (h : ℝ) * d := by linarith
  have hdenne : 1 - 2 * (h : ℝ) * d ≠ 0 := ne_of_gt hdenpos
  field_simp [hdenne]
  ring

/-- For a nonnegative two-step rate the correction can only increase the
comparison value. -/
theorem defectRate_le_defectRate_div_one_sub_correction
    (h : NNReal) {d : ℝ} (hd : 0 ≤ d)
    (hcorrection : 2 * (h : ℝ) * d < 1) :
    d ≤ d / (1 - 2 * (h : ℝ) * d) := by
  have herr := defectRate_div_one_sub_correction_sub_defectRate_eq
    h d hcorrection
  have hdenpos : 0 < 1 - 2 * (h : ℝ) * d := by linarith
  have herror_nonneg :
      0 ≤ (2 * (h : ℝ) * d ^ 2) / (1 - 2 * (h : ℝ) * d) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) h.coe_nonneg) (sq_nonneg d))
      hdenpos.le
  linarith

/-- Additive form of the exact Rayleigh correction.  This is the form consumed
by one-sided recovery: the Rayleigh excess above `d_h` is bounded by an
explicit quantity that vanishes as soon as `h d_h^2 -> 0` and the correction
denominator stays away from zero. -/
theorem timeAverageClosedRayleighQuotient_sub_twoStepDefectRate_le_correctionError
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) {psi : P.PhysicalHilbert}
    (hpsi : ‖psi‖ = 1)
    (hcorrection :
      2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi < 1) :
    T.timeAverageClosedRayleighQuotient h psi -
        T.twoStepCorrelationDefectRate h psi ≤
      (2 * (h : ℝ) * (T.twoStepCorrelationDefectRate h psi) ^ 2) /
        (1 - 2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi) := by
  have hq :=
    T.timeAverageClosedRayleighQuotient_le_twoStepDefectRate_div_one_sub_correction
      hSymmetric hh hpsi hcorrection
  have herr := defectRate_div_one_sub_correction_sub_defectRate_eq
    h (T.twoStepCorrelationDefectRate h psi) hcorrection
  linarith

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D

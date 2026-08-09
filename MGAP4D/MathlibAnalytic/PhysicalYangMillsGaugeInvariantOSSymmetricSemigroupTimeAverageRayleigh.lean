import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupTrapezoidDefect
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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

/-- The real-time integrand appearing in the time-average Hamiltonian numerator:
`C(s) - C(s+h)` on the positive interval `[0,h]`. -/
def physicalCorrelationDefectIntegrand
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) (s : ℝ) : ℝ :=
  inner ℝ psi (T.realPhysicalOrbit psi s) -
    inner ℝ psi (T.realPhysicalOrbit psi (s + (h : ℝ)))

/-- The correlation-defect integrand is continuous on the full real line. -/
theorem physicalCorrelationDefectIntegrand_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    Continuous (T.physicalCorrelationDefectIntegrand h psi) := by
  unfold physicalCorrelationDefectIntegrand
  have h0 : Continuous (fun s : ℝ => inner ℝ psi (T.realPhysicalOrbit psi s)) :=
    continuous_const.inner (T.realPhysicalOrbit_continuous psi)
  have hshift : Continuous
      (fun s : ℝ => T.realPhysicalOrbit psi (s + (h : ℝ))) :=
    (T.realPhysicalOrbit_continuous psi).comp
      (continuous_id.add continuous_const)
  exact h0.sub (continuous_const.inner hshift)

/-- On nonnegative real times the real integrand is exactly the NNReal scalar
correlation defect. -/
theorem physicalCorrelationDefectIntegrand_eq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert)
    (s : ℝ) (hs : 0 ≤ s) :
    T.physicalCorrelationDefectIntegrand h psi s =
      T.physicalCorrelation psi s.toNNReal -
        T.physicalCorrelation psi (s.toNNReal + h) := by
  unfold physicalCorrelationDefectIntegrand physicalCorrelation realPhysicalOrbit
  have hsum : (s + (h : ℝ)).toNNReal = s.toNNReal + h := by
    apply NNReal.eq
    simp [Real.toNNReal_of_nonneg hs, add_nonneg hs h.coe_nonneg]
  rw [hsum]

/-- The pairwise trapezoid inequality from the triple defect, rewritten on a
real interval as `g(s) + g(h-s) <= C(0)-C(2h)`. -/
theorem physicalCorrelationDefectIntegrand_add_reflected_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (h : NNReal) (psi : P.PhysicalHilbert)
    {s : ℝ} (hs0 : 0 ≤ s) (hsh : s ≤ (h : ℝ)) :
    T.physicalCorrelationDefectIntegrand h psi s +
        T.physicalCorrelationDefectIntegrand h psi ((h : ℝ) - s) ≤
      T.physicalCorrelation psi 0 - T.physicalCorrelation psi (h + h) := by
  let r : NNReal := NNReal.mk s hs0
  have hrh : r ≤ h := by
    exact_mod_cast hsh
  let t : NNReal := h - r
  have hrt : r + t = h := by
    dsimp [t]
    simpa [add_comm] using tsub_add_cancel_of_le hrh
  have href_nonneg : 0 ≤ (h : ℝ) - s := sub_nonneg.mpr hsh
  have hrcoe : (r : ℝ) = s := rfl
  have hrto : s.toNNReal = r := by
    apply NNReal.eq
    simp [Real.toNNReal_of_nonneg hs0, hrcoe]
  have htcoe : (t : ℝ) = (h : ℝ) - s := by
    dsimp [t]
    rw [NNReal.coe_sub hrh, hrcoe]
  have href : ((h : ℝ) - s).toNNReal = t := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ href_nonneg, htcoe]
  have hfirst := T.physicalCorrelationDefectIntegrand_eq h psi s hs0
  have hsecond := T.physicalCorrelationDefectIntegrand_eq
    h psi ((h : ℝ) - s) href_nonneg
  rw [href] at hsecond
  have hpair := T.physicalCorrelation_pair_trapezoid_le
    hSymmetric r t psi
  rw [hrt] at hpair
  rw [hfirst, hsecond, hrto]
  linarith

/-- Reflection of the defect integrand about the midpoint preserves its interval
integral. -/
theorem integral_physicalCorrelationDefectIntegrand_reflected
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    (∫ s in (0 : ℝ)..(h : ℝ),
      T.physicalCorrelationDefectIntegrand h psi ((h : ℝ) - s)) =
    ∫ s in (0 : ℝ)..(h : ℝ),
      T.physicalCorrelationDefectIntegrand h psi s := by
  rw [intervalIntegral.integral_comp_sub_left
    (T.physicalCorrelationDefectIntegrand h psi) (h : ℝ)]
  simp

/-- Integrated no-loss trapezoid inequality.  The reflection identity turns the
paired pointwise estimate into the exact factor two required downstream. -/
theorem two_mul_integral_physicalCorrelationDefectIntegrand_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) (psi : P.PhysicalHilbert) :
    2 * (∫ s in (0 : ℝ)..(h : ℝ),
      T.physicalCorrelationDefectIntegrand h psi s) ≤
      (h : ℝ) *
        (T.physicalCorrelation psi 0 - T.physicalCorrelation psi (h + h)) := by
  have hhreal : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  let g := T.physicalCorrelationDefectIntegrand h psi
  have hgcont : Continuous g :=
    T.physicalCorrelationDefectIntegrand_continuous h psi
  have hgint : IntervalIntegrable g volume 0 (h : ℝ) :=
    hgcont.intervalIntegrable 0 (h : ℝ)
  have hrefcont : Continuous (fun s : ℝ => g ((h : ℝ) - s)) :=
    hgcont.comp (continuous_const.sub continuous_id)
  have hrefint : IntervalIntegrable (fun s : ℝ => g ((h : ℝ) - s))
      volume 0 (h : ℝ) :=
    hrefcont.intervalIntegrable 0 (h : ℝ)
  have hsumint : IntervalIntegrable
      (fun s : ℝ => g s + g ((h : ℝ) - s)) volume 0 (h : ℝ) :=
    hgint.add hrefint
  have hconstint : IntervalIntegrable
      (fun _ : ℝ => T.physicalCorrelation psi 0 -
        T.physicalCorrelation psi (h + h)) volume 0 (h : ℝ) :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on
    (a := (0 : ℝ)) (b := (h : ℝ))
    (f := fun s : ℝ => g s + g ((h : ℝ) - s))
    (g := fun _ : ℝ => T.physicalCorrelation psi 0 -
      T.physicalCorrelation psi (h + h))
    hhreal.le hsumint hconstint ?_
  · rw [intervalIntegral.integral_add hgint hrefint] at hmono
    rw [T.integral_physicalCorrelationDefectIntegrand_reflected h psi] at hmono
    simpa [g, two_mul, mul_sub] using hmono
  · intro s hs
    exact T.physicalCorrelationDefectIntegrand_add_reflected_le
      hSymmetric h psi hs.1 hs.2

/-- Pairing the initial vector with its time average is the normalized integral
of the unshifted scalar correlation. -/
theorem inner_timeAverage_left_eq_correlationIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    inner ℝ psi (T.timeAverage h psi) =
      (h : ℝ)⁻¹ *
        (∫ s in (0 : ℝ)..(h : ℝ), inner ℝ psi (T.realPhysicalOrbit psi s)) := by
  unfold timeAverage
  rw [real_inner_smul_right]
  congr 1
  unfold timeIntegral
  change
    (innerSL ℝ psi)
        (∫ s in (0 : ℝ)..(h : ℝ), T.realPhysicalOrbit psi s) =
      ∫ s in (0 : ℝ)..(h : ℝ),
        (innerSL ℝ psi) (T.realPhysicalOrbit psi s)
  rw [ContinuousLinearMap.intervalIntegral_comp_comm
    (innerSL ℝ psi)
    (T.realPhysicalOrbit_intervalIntegrable psi 0 (h : ℝ))]

/-- The endpoint defect paired with its time average is exactly the normalized
integral of the correlation-defect integrand. -/
theorem inner_physicalDefect_timeAverage_eq_integral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    inner ℝ (T.physicalDefect h psi) (T.timeAverage h psi) =
      (h : ℝ)⁻¹ *
        (∫ s in (0 : ℝ)..(h : ℝ),
          T.physicalCorrelationDefectIntegrand h psi s) := by
  have h0cont : Continuous
      (fun s : ℝ => inner ℝ psi (T.realPhysicalOrbit psi s)) :=
    continuous_const.inner (T.realPhysicalOrbit_continuous psi)
  have hshift : Continuous
      (fun s : ℝ => inner ℝ psi
        (T.realPhysicalOrbit psi (s + (h : ℝ)))) := by
    apply continuous_const.inner
    exact (T.realPhysicalOrbit_continuous psi).comp
      (continuous_id.add continuous_const)
  have h0int : IntervalIntegrable
      (fun s : ℝ => inner ℝ psi (T.realPhysicalOrbit psi s)) volume 0 (h : ℝ) :=
    h0cont.intervalIntegrable 0 (h : ℝ)
  have hshiftint : IntervalIntegrable
      (fun s : ℝ => inner ℝ psi
        (T.realPhysicalOrbit psi (s + (h : ℝ)))) volume 0 (h : ℝ) :=
    hshift.intervalIntegrable 0 (h : ℝ)
  have hendpoint :
      inner ℝ (T.toPhysicalSemigroup.operator h psi) (T.timeAverage h psi) =
        (h : ℝ)⁻¹ *
          (∫ s in (0 : ℝ)..(h : ℝ),
            inner ℝ psi (T.realPhysicalOrbit psi (s + (h : ℝ)))) := by
    rw [real_inner_comm]
    exact T.inner_timeAverage_operator_eq_shiftedCorrelationIntegral
      hSymmetric h psi
  unfold physicalDefect
  rw [inner_sub_left, T.inner_timeAverage_left_eq_correlationIntegral h psi,
    hendpoint]
  rw [← mul_sub]
  rw [← intervalIntegral.integral_sub h0int hshiftint]
  rfl

/-- Exact integral representation of the graph-closed Hamiltonian energy on a
time average. -/
theorem inner_closedRightHamiltonian_timeAverage_eq_integral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    inner ℝ
        (T.closedRightHamiltonian
          (T.timeAverageClosedRightHamiltonianDomain h psi))
        (T.timeAverage h psi) =
      (h : ℝ)⁻¹ ^ 2 *
        (∫ s in (0 : ℝ)..(h : ℝ),
          T.physicalCorrelationDefectIntegrand h psi s) := by
  rw [T.inner_closedRightHamiltonian_timeAverage_eq_endpointPairing h psi]
  change
    (h : ℝ)⁻¹ * inner ℝ (T.physicalDefect h psi) (T.timeAverage h psi) = _
  rw [T.inner_physicalDefect_timeAverage_eq_integral hSymmetric h psi]
  ring

/-- The graph-closed Hamiltonian numerator of a time average is bounded by the
same two-step scalar defect rate, with no coefficient loss. -/
theorem inner_closedRightHamiltonian_timeAverage_le_twoStepDefectRate
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) (psi : P.PhysicalHilbert) :
    inner ℝ
        (T.closedRightHamiltonian
          (T.timeAverageClosedRightHamiltonianDomain h psi))
        (T.timeAverage h psi) ≤
      T.twoStepCorrelationDefectRate h psi := by
  have hhreal : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  let I : ℝ := ∫ s in (0 : ℝ)..(h : ℝ),
    T.physicalCorrelationDefectIntegrand h psi s
  let delta : ℝ := T.physicalCorrelation psi 0 -
    T.physicalCorrelation psi (h + h)
  have hI : 2 * I ≤ (h : ℝ) * delta := by
    exact T.two_mul_integral_physicalCorrelationDefectIntegrand_le
      hSymmetric hh psi
  have hIhalf : I ≤ (h : ℝ) * delta / 2 := by linarith
  have hdelta : delta = ‖psi‖ ^ 2 - T.physicalCorrelation psi (h + h) := by
    dsimp [delta]
    rw [T.physicalCorrelation_zero]
  rw [hdelta] at hIhalf
  rw [T.inner_closedRightHamiltonian_timeAverage_eq_integral
    hSymmetric h psi]
  unfold twoStepCorrelationDefectRate
  change (h : ℝ)⁻¹ ^ 2 * I ≤
    (‖psi‖ ^ 2 - T.physicalCorrelation psi (h + h)) /
      (2 * (h : ℝ))
  calc
    (h : ℝ)⁻¹ ^ 2 * I = I / ((h : ℝ) ^ 2) := by
      field_simp [hhreal.ne']
    _ ≤ ((h : ℝ) * (‖psi‖ ^ 2 - T.physicalCorrelation psi (h + h)) / 2) /
        ((h : ℝ) ^ 2) := by
      exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hhreal)).2 hIhalf
    _ = (‖psi‖ ^ 2 - T.physicalCorrelation psi (h + h)) /
        (2 * (h : ℝ)) := by
      field_simp [hhreal.ne']
      ring

/-- The two-step correlation defect rate is nonnegative for positive width. -/
theorem twoStepCorrelationDefectRate_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) (psi : P.PhysicalHilbert) :
    0 ≤ T.twoStepCorrelationDefectRate h psi := by
  have hhreal : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hnorm := T.physicalOperator_norm_le h psi
  have hcorr := T.physicalCorrelation_add_self_eq_norm_sq hSymmetric h psi
  unfold twoStepCorrelationDefectRate
  rw [hcorr]
  exact div_nonneg (by
    nlinarith [norm_nonneg psi,
      norm_nonneg (T.toPhysicalSemigroup.operator h psi)])
    (by positivity)

/-- A unit moving state cannot vanish under time averaging whenever its
quantitative defect correction remains strictly below one.  This is the exact
nonvanishing criterion needed before forming a moving Rayleigh quotient. -/
theorem timeAverage_ne_zero_of_unit_and_defectCorrection_lt_one
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) {psi : P.PhysicalHilbert}
    (hpsi : ‖psi‖ = 1)
    (hcorrection : 2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi < 1) :
    T.timeAverage h psi ≠ 0 := by
  have hden := T.norm_sq_sub_two_mul_defectRate_le_timeAverage_norm_sq
    hSymmetric hh psi
  rw [hpsi] at hden
  norm_num at hden
  have hpos : 0 < ‖T.timeAverage h psi‖ ^ 2 := by linarith
  intro hzero
  rw [hzero, norm_zero] at hpos
  norm_num at hpos

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D

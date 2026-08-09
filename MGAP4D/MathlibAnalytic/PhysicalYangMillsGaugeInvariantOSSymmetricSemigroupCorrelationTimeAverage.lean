import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverageExcitationGraphRegularization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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

/-- The scalar Euclidean-time correlation of a completed physical state. -/
def physicalCorrelation
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : NNReal) : ℝ :=
  inner ℝ psi (T.toPhysicalSemigroup.operator t psi)

@[simp] theorem physicalCorrelation_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    T.physicalCorrelation psi 0 = ‖psi‖ ^ 2 := by
  simp [physicalCorrelation, T.toPhysicalSemigroup.operator_zero,
    real_inner_self_eq_norm_sq]

/-- For a symmetric Euclidean semigroup, the correlation at twice a time is
exactly the squared norm of the half-time evolved vector.  This is the basic
positive-type identity behind the moving-state estimates below. -/
theorem physicalCorrelation_add_self_eq_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    T.physicalCorrelation psi (t + t) =
      ‖T.toPhysicalSemigroup.operator t psi‖ ^ 2 := by
  unfold physicalCorrelation
  rw [T.toPhysicalSemigroup.operator_add]
  change
    inner ℝ psi
        (T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator t psi)) =
      ‖T.toPhysicalSemigroup.operator t psi‖ ^ 2
  rw [← hSymmetric t psi (T.toPhysicalSemigroup.operator t psi)]
  exact real_inner_self_eq_norm_sq _

/-- Correlations at doubled times decrease under additional Euclidean-time
contraction. -/
theorem physicalCorrelation_add_self_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {s t : NNReal} (hst : s ≤ t) (psi : P.PhysicalHilbert) :
    T.physicalCorrelation psi (t + t) ≤
      T.physicalCorrelation psi (s + s) := by
  rw [T.physicalCorrelation_add_self_eq_norm_sq hSymmetric,
    T.physicalCorrelation_add_self_eq_norm_sq hSymmetric]
  have ht : t = (t - s) + s := by
    simpa [add_comm] using (tsub_add_cancel_of_le hst).symm
  have hop :
      T.toPhysicalSemigroup.operator t psi =
        T.toPhysicalSemigroup.operator (t - s)
          (T.toPhysicalSemigroup.operator s psi) := by
    rw [ht, T.toPhysicalSemigroup.operator_add]
    rfl
  rw [hop]
  have hnorm := T.physicalOperator_norm_le (t - s)
    (T.toPhysicalSemigroup.operator s psi)
  nlinarith [norm_nonneg (T.toPhysicalSemigroup.operator (t - s)
    (T.toPhysicalSemigroup.operator s psi)),
    norm_nonneg (T.toPhysicalSemigroup.operator s psi)]

/-- The scalar correlation is antitone on nonnegative Euclidean time. -/
theorem physicalCorrelation_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) :
    Antitone (T.physicalCorrelation psi) := by
  intro s t hst
  have hhalf : s / 2 ≤ t / 2 := by gcongr
  have h := T.physicalCorrelation_add_self_antitone
    hSymmetric hhalf psi
  have hs : s / 2 + s / 2 = s := by
    apply NNReal.eq
    norm_num
  have ht : t / 2 + t / 2 = t := by
    apply NNReal.eq
    norm_num
  simpa only [hs, ht] using h

/-- In particular, every symmetric-semigroup correlation is nonnegative. -/
theorem physicalCorrelation_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    0 ≤ T.physicalCorrelation psi t := by
  have hhalf := T.physicalCorrelation_add_self_eq_norm_sq
    hSymmetric (t / 2) psi
  have ht : t / 2 + t / 2 = t := by
    apply NNReal.eq
    norm_num
  rw [ht] at hhalf
  rw [hhalf]
  positivity

/-- Exact midpoint-convexity defect of a symmetric-semigroup correlation.
The defect is a squared Hilbert norm, so no spectral theorem is needed. -/
theorem physicalCorrelation_midpoint_defect_eq_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (a d : NNReal) (psi : P.PhysicalHilbert) :
    T.physicalCorrelation psi (a + a) +
        T.physicalCorrelation psi ((a + d) + (a + d)) -
        2 * T.physicalCorrelation psi ((a + a) + d) =
      ‖T.toPhysicalSemigroup.operator a psi -
        T.toPhysicalSemigroup.operator (a + d) psi‖ ^ 2 := by
  have hmiddle :
      T.physicalCorrelation psi ((a + a) + d) =
        inner ℝ (T.toPhysicalSemigroup.operator a psi)
          (T.toPhysicalSemigroup.operator (a + d) psi) := by
    unfold physicalCorrelation
    have hs := hSymmetric a psi
      (T.toPhysicalSemigroup.operator (a + d) psi)
    rw [T.toPhysicalSemigroup.operator_add] at hs
    simpa [add_assoc] using hs.symm
  rw [T.physicalCorrelation_add_self_eq_norm_sq hSymmetric,
    T.physicalCorrelation_add_self_eq_norm_sq hSymmetric, hmiddle,
    norm_sub_sq_real]

/-- The graph-closed Hamiltonian energy of a positive-width time average is
exactly the endpoint generator pairing.  This identity is valid for moving
states and is the numerator interface for the later two-step defect estimate. -/
theorem inner_closedRightHamiltonian_timeAverage_eq_endpointPairing
    (T : P.StronglyContinuousPhysicalSemigroup)
    {h : NNReal} (hh : 0 < h) (psi : P.PhysicalHilbert) :
    inner ℝ
        (T.closedRightHamiltonian
          (T.timeAverageClosedRightHamiltonianDomain h psi))
        (T.timeAverage h psi) =
      (h : ℝ)⁻¹ *
        inner ℝ
          (psi - T.toPhysicalSemigroup.operator h psi)
          (T.timeAverage h psi) := by
  rw [T.closedRightHamiltonian_timeAverage]
  simp only [real_inner_smul_left]

/-- Pairing a time average with its endpoint evolution is the normalized
integral of the shifted correlation over the second half-interval. -/
theorem inner_timeAverage_operator_eq_shiftedCorrelationIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) (psi : P.PhysicalHilbert) :
    inner ℝ (T.timeAverage h psi)
        (T.toPhysicalSemigroup.operator h psi) =
      (h : ℝ)⁻¹ *
        (∫ s in (0 : ℝ)..(h : ℝ),
          inner ℝ psi (T.realPhysicalOrbit psi (s + (h : ℝ)))) := by
  unfold timeAverage
  rw [real_inner_smul_left]
  congr 1
  unfold timeIntegral
  calc
    inner ℝ
        (∫ s in (0 : ℝ)..(h : ℝ), T.realPhysicalOrbit psi s)
        (T.toPhysicalSemigroup.operator h psi) =
      inner ℝ (T.toPhysicalSemigroup.operator h psi)
        (∫ s in (0 : ℝ)..(h : ℝ), T.realPhysicalOrbit psi s) :=
      real_inner_comm _ _
    _ = ∫ s in (0 : ℝ)..(h : ℝ),
        inner ℝ (T.toPhysicalSemigroup.operator h psi)
          (T.realPhysicalOrbit psi s) := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (innerSL ℝ (T.toPhysicalSemigroup.operator h psi))
        (T.realPhysicalOrbit_intervalIntegrable psi 0 (h : ℝ))]
      rfl
    _ = ∫ s in (0 : ℝ)..(h : ℝ),
        inner ℝ psi (T.realPhysicalOrbit psi (s + (h : ℝ))) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hhreal : (0 : ℝ) ≤ (h : ℝ) := h.coe_nonneg
      rw [uIcc_of_le hhreal] at hs
      calc
        inner ℝ (T.toPhysicalSemigroup.operator h psi)
            (T.realPhysicalOrbit psi s) =
          inner ℝ psi
            (T.toPhysicalSemigroup.operator h
              (T.realPhysicalOrbit psi s)) :=
          hSymmetric h psi (T.realPhysicalOrbit psi s)
        _ = inner ℝ psi
            (T.realPhysicalOrbit
              (T.toPhysicalSemigroup.operator h psi) s) := by
          rw [T.physicalOperator_realPhysicalOrbit]
        _ = inner ℝ psi
            (T.realPhysicalOrbit psi (s + (h : ℝ))) := by
          rw [T.realPhysicalOrbit_operator_eq_add_of_nonneg h psi s hs.1]

/-- A positive-width time average of a symmetric contraction semigroup cannot
have smaller norm than the endpoint vector `T_h psi`.

This estimate is uniform in `psi`; consequently it remains useful for moving
finite-to-continuum candidate sequences, unlike fixed-vector strong
continuity. -/
theorem physicalOperator_norm_le_timeAverage_norm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) (psi : P.PhysicalHilbert) :
    ‖T.toPhysicalSemigroup.operator h psi‖ ≤ ‖T.timeAverage h psi‖ := by
  have hhreal : 0 < (h : ℝ) := by exact_mod_cast hh
  let q := T.toPhysicalSemigroup.operator h psi
  have hcorr2 :
      T.physicalCorrelation psi (h + h) = ‖q‖ ^ 2 := by
    exact T.physicalCorrelation_add_self_eq_norm_sq hSymmetric h psi
  have hintegral :
      (h : ℝ) * T.physicalCorrelation psi (h + h) ≤
        ∫ s in (0 : ℝ)..(h : ℝ),
          inner ℝ psi (T.realPhysicalOrbit psi (s + (h : ℝ))) := by
    have hfunInt : IntervalIntegrable
        (fun s : ℝ => inner ℝ psi
          (T.realPhysicalOrbit psi (s + (h : ℝ)))) volume 0 (h : ℝ) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hmono := intervalIntegral.integral_mono_on
      (a := (0 : ℝ)) (b := (h : ℝ))
      (f := fun _ : ℝ => T.physicalCorrelation psi (h + h))
      (g := fun s : ℝ => inner ℝ psi
        (T.realPhysicalOrbit psi (s + (h : ℝ))))
      hhreal.le (by simp) hfunInt ?_
    · simpa using hmono
    · intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hsh : s ≤ (h : ℝ) := hs.2
      let r : NNReal := ⟨s, hs0⟩
      have hrh : r ≤ h := by
        exact_mod_cast hsh
      have hrt : r + h ≤ h + h := by gcongr
      have hc := T.physicalCorrelation_antitone hSymmetric psi hrt
      have hrs : (r : ℝ) = s := rfl
      have hsum : (s + (h : ℝ)).toNNReal = r + h := by
        apply NNReal.eq
        simp [Real.toNNReal_of_nonneg (add_nonneg hs0 h.coe_nonneg), r]
      simpa [physicalCorrelation, realPhysicalOrbit, hsum] using hc
  have hpair : ‖q‖ ^ 2 ≤ inner ℝ (T.timeAverage h psi) q := by
    rw [T.inner_timeAverage_operator_eq_shiftedCorrelationIntegral
      hSymmetric hh psi, ← hcorr2]
    have hinv : 0 ≤ (h : ℝ)⁻¹ := inv_nonneg.mpr hhreal.le
    calc
      T.physicalCorrelation psi (h + h) =
          (h : ℝ)⁻¹ * ((h : ℝ) * T.physicalCorrelation psi (h + h)) := by
        field_simp
      _ ≤ (h : ℝ)⁻¹ *
          (∫ s in (0 : ℝ)..(h : ℝ),
            inner ℝ psi (T.realPhysicalOrbit psi (s + (h : ℝ)))) :=
        mul_le_mul_of_nonneg_left hintegral hinv
  have hcauchy :
      inner ℝ (T.timeAverage h psi) q ≤
        ‖T.timeAverage h psi‖ * ‖q‖ :=
    real_inner_le_norm _ _
  by_cases hq : ‖q‖ = 0
  · simp [hq]
  · have hqpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) (Ne.symm hq)
    have hmul : ‖q‖ * ‖q‖ ≤ ‖T.timeAverage h psi‖ * ‖q‖ := by
      rw [← pow_two]
      exact hpair.trans hcauchy
    exact (mul_le_mul_right hqpos).mp hmul

/-- Uniform squared-norm lower bound by the two-step scalar correlation. -/
theorem physicalCorrelation_twoStep_le_timeAverage_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) (psi : P.PhysicalHilbert) :
    T.physicalCorrelation psi (h + h) ≤ ‖T.timeAverage h psi‖ ^ 2 := by
  rw [T.physicalCorrelation_add_self_eq_norm_sq hSymmetric]
  have hnorm := T.physicalOperator_norm_le_timeAverage_norm
    hSymmetric hh psi
  nlinarith [norm_nonneg (T.toPhysicalSemigroup.operator h psi),
    norm_nonneg (T.timeAverage h psi)]

/-- The two-step scalar defect rate attached to a physical vector.  For a unit
vector this is exactly `(1 - <psi,T_{2h}psi>)/(2h)`. -/
def twoStepCorrelationDefectRate
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) : ℝ :=
  (‖psi‖ ^ 2 - T.physicalCorrelation psi (h + h)) /
    (2 * (h : ℝ))

/-- The moving-state denominator estimate in defect-rate form.  No uniform
strong-continuity hypothesis appears: a bounded two-step defect at a vanishing
width automatically prevents time-average norm loss. -/
theorem norm_sq_sub_two_mul_defectRate_le_timeAverage_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {h : NNReal} (hh : 0 < h) (psi : P.PhysicalHilbert) :
    ‖psi‖ ^ 2 - 2 * (h : ℝ) * T.twoStepCorrelationDefectRate h psi ≤
      ‖T.timeAverage h psi‖ ^ 2 := by
  have hhreal : (2 : ℝ) * (h : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    positivity
  have hcorr := T.physicalCorrelation_twoStep_le_timeAverage_norm_sq
    hSymmetric hh psi
  unfold twoStepCorrelationDefectRate
  convert hcorr using 1 <;> field_simp [hhreal]

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D

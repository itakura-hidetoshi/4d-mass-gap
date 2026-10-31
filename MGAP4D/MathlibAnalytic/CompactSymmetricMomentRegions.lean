import MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Quantitative sign regions from an actual symmetric second moment

A measure-preserving sign reversal balances the two strict sign tails.
If a continuous real function satisfies f^2 <= R and its actual second
moment S is positive, each tail beyond sqrt(S/2) has probability at least
S/(4*R-2*S).  The denominator is proved positive from S <= R.
The proof integrates an indicator envelope; no measure-zero boundary
assumption, atom-free hypothesis or unspecified positive-mass witness is used.
-/

namespace MGAP4D.MathlibAnalytic.CompactSymmetricMomentRegions

open MeasureTheory
open scoped Topology
noncomputable section
set_option autoImplicit false

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [CompactSpace α] [BorelSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

/-- The actual second moment under the same probability measure. -/
def secondMoment (f : α → ℝ) : ℝ := ∫ x, (f x) ^ 2 ∂μ

private theorem csmr_integrable {f : α → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [CompactSpace α] [IsProbabilityMeasure μ] in
/-- A genuine measure-preserving sign reversal forces the actual mean to vanish. -/
theorem mean_eq_zero (f : α → ℝ) (T : α → α) (hf : Continuous f)
    (hT : MeasurePreserving T μ μ) (hFlip : ∀ x, f (T x) = -f x) :
    (∫ x, f x ∂μ) = 0 := by
  have h : (∫ x, f x ∂Measure.map T μ) = ∫ x, f (T x) ∂μ :=
    integral_map_of_stronglyMeasurable hT.measurable hf.stronglyMeasurable
  rw [hT.map_eq] at h
  simp_rw [hFlip] at h
  rw [integral_neg] at h
  linarith

omit [CompactSpace α] [IsProbabilityMeasure μ] in
/-- Strict positive and negative tails have equal real mass, at every threshold. -/
theorem positive_negative_tail_mass_eq
    (f : α → ℝ) (T : α → α) (hf : Continuous f)
    (hT : MeasurePreserving T μ μ) (hFlip : ∀ x, f (T x) = -f x) (c : ℝ) :
    Measure.real μ {x | c < f x} = Measure.real μ {x | f x < -c} := by
  have hp : MeasurableSet {x | c < f x} :=
    (isOpen_lt continuous_const hf).measurableSet
  have hpre : T ⁻¹' {x | c < f x} = {x | f x < -c} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hFlip]
    constructor <;> intro h <;> linarith
  have hm := hT.measure_preimage hp.nullMeasurableSet
  rw [hpre] at hm
  exact congrArg ENNReal.toReal hm.symm

/-- Integrating a proved pointwise square cap bounds the actual second moment. -/
theorem secondMoment_le (f : α → ℝ) (hf : Continuous f)
    (R : ℝ) (hBound : ∀ x, (f x) ^ 2 ≤ R) : secondMoment μ f ≤ R := by
  calc
    secondMoment μ f ≤ ∫ _x : α, R ∂μ :=
      integral_mono (csmr_integrable μ (hf.pow 2)) (integrable_const _) hBound
    _ = R := by simp

/-- Explicit balanced strict-tail mass floors obtained from the actual positive
second moment. The same S controls both the threshold and the denominator. -/
theorem half_moment_tail_bounds
    (f : α → ℝ) (T : α → α) (hf : Continuous f)
    (hT : MeasurePreserving T μ μ) (hFlip : ∀ x, f (T x) = -f x)
    (R : ℝ) (hBound : ∀ x, (f x) ^ 2 ≤ R)
    (hM : 0 < secondMoment μ f) :
    0 < Real.sqrt (secondMoment μ f / 2) ∧
      0 < 4 * R - 2 * secondMoment μ f ∧
      secondMoment μ f / (4 * R - 2 * secondMoment μ f) ≤
        Measure.real μ {x | Real.sqrt (secondMoment μ f / 2) < f x} ∧
      secondMoment μ f / (4 * R - 2 * secondMoment μ f) ≤
        Measure.real μ {x | f x < -Real.sqrt (secondMoment μ f / 2)} := by
  classical
  let M : ℝ := secondMoment μ f
  let c : ℝ := Real.sqrt (M / 2)
  let P : Set α := {x | c < f x}
  let N : Set α := {x | f x < -c}
  have hMR : M ≤ R := secondMoment_le μ f hf R hBound
  have hc : 0 < c := Real.sqrt_pos.mpr (half_pos hM)
  have hcSq : c ^ 2 = M / 2 := Real.sq_sqrt (div_nonneg hM.le (by norm_num))
  have hd : 0 < 4 * R - 2 * M := by change 0 < M at hM; linarith
  have hP : MeasurableSet P := (isOpen_lt continuous_const hf).measurableSet
  have hN : MeasurableSet N := (isOpen_lt hf continuous_const).measurableSet
  have hPI : Integrable (P.indicator (fun _ : α => (1 : ℝ))) μ :=
    (integrable_const _).indicator hP
  have hNI : Integrable (N.indicator (fun _ : α => (1 : ℝ))) μ :=
    (integrable_const _).indicator hN
  have hSumI : Integrable (fun x : α =>
      P.indicator (fun _ => (1 : ℝ)) x + N.indicator (fun _ => (1 : ℝ)) x) μ :=
    hPI.add hNI
  have hMulI : Integrable (fun x : α => (R - c ^ 2) *
      (P.indicator (fun _ => (1 : ℝ)) x + N.indicator (fun _ => (1 : ℝ)) x)) μ :=
    hSumI.const_mul _
  have hConstI : Integrable (fun _x : α => c ^ 2) μ := integrable_const _
  have hUpperI : Integrable (fun x : α => c ^ 2 + (R - c ^ 2) *
      (P.indicator (fun _ => (1 : ℝ)) x + N.indicator (fun _ => (1 : ℝ)) x)) μ :=
    hConstI.add hMulI
  have hPoint (x : α) : (f x) ^ 2 ≤ c ^ 2 + (R - c ^ 2) *
      (P.indicator (fun _ => (1 : ℝ)) x + N.indicator (fun _ => (1 : ℝ)) x) := by
    by_cases hp : x ∈ P
    · have hpx : c < f x := hp
      have hn : x ∉ N := by change ¬f x < -c; linarith
      rw [Set.indicator_of_mem hp, Set.indicator_of_notMem hn]
      nlinarith [hBound x]
    · by_cases hn : x ∈ N
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_mem hn]
        nlinarith [hBound x]
      · have hLower : -c ≤ f x := le_of_not_gt hn
        have hUpper : f x ≤ c := le_of_not_gt hp
        have hAbs : |f x| ≤ c := abs_le.mpr ⟨hLower, hUpper⟩
        have hSq : (f x) ^ 2 ≤ c ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f x)) hAbs 2
        rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hn]
        simpa using hSq
  have hIntegral :
      (∫ x : α, c ^ 2 + (R - c ^ 2) *
        (P.indicator (fun _ => (1 : ℝ)) x + N.indicator (fun _ => (1 : ℝ)) x) ∂μ) =
      c ^ 2 + (R - c ^ 2) * (Measure.real μ P + Measure.real μ N) := by
    rw [integral_add hConstI hMulI, integral_const_mul,
      integral_add hPI hNI, integral_indicator_const (1 : ℝ) hP,
      integral_indicator_const (1 : ℝ) hN]
    simp
  have hBudget : M ≤ c ^ 2 + (R - c ^ 2) * (Measure.real μ P + Measure.real μ N) := by
    have h := integral_mono (csmr_integrable μ (hf.pow 2)) hUpperI hPoint
    rw [hIntegral] at h
    exact h
  have hMass : Measure.real μ P = Measure.real μ N :=
    positive_negative_tail_mass_eq μ f T hf hT hFlip c
  have hPos : M / (4 * R - 2 * M) ≤ Measure.real μ P := by
    apply (div_le_iff₀ hd).mpr
    rw [← hMass, hcSq] at hBudget
    nlinarith
  have hNeg : M / (4 * R - 2 * M) ≤ Measure.real μ N := by
    rw [← hMass]
    exact hPos
  exact ⟨hc, hd, hPos, hNeg⟩

end
end MGAP4D.MathlibAnalytic.CompactSymmetricMomentRegions

#print axioms MGAP4D.MathlibAnalytic.CompactSymmetricMomentRegions.mean_eq_zero
#print axioms MGAP4D.MathlibAnalytic.CompactSymmetricMomentRegions.positive_negative_tail_mass_eq
#print axioms MGAP4D.MathlibAnalytic.CompactSymmetricMomentRegions.secondMoment_le
#print axioms MGAP4D.MathlibAnalytic.CompactSymmetricMomentRegions.half_moment_tail_bounds

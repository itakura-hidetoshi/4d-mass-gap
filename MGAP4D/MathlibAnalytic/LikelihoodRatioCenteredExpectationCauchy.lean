import MGAP4D.MathlibAnalytic.LikelihoodRatioQuadraticInfluenceIntegratedReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Centered expectation transport from quadratic likelihood-ratio influence

This file turns the integrated quadratic density defect into the linear
influence estimate needed by the observable-specific L2 profile.

For normalized nonnegative densities p and q satisfying a mutual
likelihood-ratio bound, and for a strongly measurable observable X with finite
centered energy against p+q, weighted Cauchy--Schwarz gives

  |integral (X-c)(p-q)|
    <= (2*c(K)) * sqrt (integral (X-c)^2 (p+q)),

where c(K)=(K-1)/(K+1).

The coefficient therefore remains linear after the L2 square root.  This is the
reason for introducing the quadratic defect in the preceding theorem units.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HaarLikelihoodRatioInfluence

/-- Weighted Cauchy--Schwarz transport for a centered observable under two
likelihood-ratio-comparable probability densities. -/
theorem centered_density_difference_integral_abs_le_fullL1_coefficient_mul_sqrt_energy
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (p q : α → ℝ)
    (hpMeas : Measurable p)
    (hqMeas : Measurable q)
    (hpInt : Integrable p μ)
    (hqInt : Integrable q μ)
    (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x)
    (hpOne : ∫ x, p x ∂μ = 1)
    (hqOne : ∫ x, q x ∂μ = 1)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ x, p x ≤ K * q x ∧ q x ≤ K * p x)
    (X : α → ℝ)
    (hX : StronglyMeasurable X)
    (center : ℝ)
    (hEnergy :
      Integrable
        (fun x => (X x - center) ^ 2 * (p x + q x)) μ) :
    |∫ x, (X x - center) * (p x - q x) ∂μ| ≤
      (2 * coefficient K) *
        Real.sqrt
          (∫ x, (X x - center) ^ 2 * (p x + q x) ∂μ) := by
  let s : α → ℝ := fun x => p x + q x
  let F : α → ℝ := fun x => (X x - center) * Real.sqrt (s x)
  let G : α → ℝ := fun x => (p x - q x) / Real.sqrt (s x)
  let E : ℝ := ∫ x, (X x - center) ^ 2 * s x ∂μ
  let D : ℝ := ∫ x, ((p x - q x) ^ 2) / s x ∂μ
  let influence : ℝ := 2 * coefficient K
  have hs0 : ∀ x, 0 ≤ s x := by
    intro x
    exact add_nonneg (hp0 x) (hq0 x)
  have hsMeas : Measurable s := by
    exact hpMeas.add hqMeas
  have hsqrtMeas : Measurable (fun x => Real.sqrt (s x)) :=
    Real.continuous_sqrt.measurable.comp hsMeas
  have hFMeas : Measurable F := by
    dsimp [F]
    exact (hX.measurable.sub measurable_const).mul hsqrtMeas
  have hGMeas : Measurable G := by
    dsimp [G]
    exact (hpMeas.sub hqMeas).div hsqrtMeas
  have hFSq (x : α) :
      F x ^ 2 = (X x - center) ^ 2 * s x := by
    dsimp [F]
    rw [mul_pow, Real.sq_sqrt (hs0 x)]
  have hGSq (x : α) :
      G x ^ 2 = ((p x - q x) ^ 2) / s x := by
    dsimp [G]
    rw [div_pow, Real.sq_sqrt (hs0 x)]
  have hFMem : MemLp F 2 μ := by
    apply (memLp_two_iff_integrable_sq hFMeas.aestronglyMeasurable).2
    exact Integrable.congr hEnergy
      (Filter.Eventually.of_forall fun x => (hFSq x).symm)
  have hDefectInt :
      Integrable (fun x => ((p x - q x) ^ 2) / (p x + q x)) μ :=
    quadratic_defect_integrable
      μ p q hpMeas hqMeas hpInt hqInt hp0 hq0 hpOne hqOne
      K hK hRatio
  have hGMem : MemLp G 2 μ := by
    apply (memLp_two_iff_integrable_sq hGMeas.aestronglyMeasurable).2
    exact Integrable.congr hDefectInt
      (Filter.Eventually.of_forall fun x => by
        simpa [s] using (hGSq x).symm)
  have hProd (x : α) :
      F x * G x = (X x - center) * (p x - q x) := by
    by_cases hz : s x = 0
    · have hpz : p x = 0 := by
        have := hs0 x
        dsimp [s] at hz
        nlinarith [hp0 x, hq0 x]
      have hqz : q x = 0 := by
        dsimp [s] at hz
        nlinarith [hp0 x, hq0 x]
      simp [F, G, s, hpz, hqz]
    · have hspos : 0 < s x :=
        lt_of_le_of_ne (hs0 x) (Ne.symm hz)
      have hsqrtNe : Real.sqrt (s x) ≠ 0 :=
        (Real.sqrt_pos.2 hspos).ne'
      dsimp [F, G]
      field_simp [hsqrtNe]
  have hFNormSq :
      (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) = E := by
    dsimp [E]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, hFSq]
  have hGNormSq :
      (∫ x, ‖G x‖ ^ (2 : ℝ) ∂μ) = D := by
    dsimp [D]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, hGSq]
  have hHolderRaw :=
    integral_mul_norm_le_Lp_mul_Lq
      Real.HolderConjugate.two_two hFMem hGMem
  have hHolder :
      (∫ x, |F x| * |G x| ∂μ) ≤
        Real.sqrt E * Real.sqrt D := by
    rw [hFNormSq, hGNormSq] at hHolderRaw
    simpa [Real.norm_eq_abs, ← Real.sqrt_eq_rpow] using hHolderRaw
  have hE0 : 0 ≤ E := by
    dsimp [E, s]
    exact integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (add_nonneg (hp0 x) (hq0 x))
  have hD0 : 0 ≤ D := by
    dsimp [D, s]
    exact integral_nonneg fun x =>
      quadratic_defect_nonneg_of_density_nonneg p q hp0 hq0 x
  have hInfluence0 : 0 ≤ influence := by
    dsimp [influence, coefficient]
    exact mul_nonneg (by norm_num)
      (div_nonneg (sub_nonneg.mpr hK) (by linarith))
  have hDBound : D ≤ influence ^ 2 := by
    dsimp [D, s, influence]
    exact
      quadratic_defect_integral_le_fullL1_coefficient_sq
        μ p q hpMeas hqMeas hpInt hqInt hp0 hq0 hpOne hqOne
        K hK hRatio
  have hSqrtDLe : Real.sqrt D ≤ influence := by
    have hsqrt0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
    have hsqrtSq : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD0
    nlinarith
  have hIntegralEq :
      (∫ x, (X x - center) * (p x - q x) ∂μ) =
        ∫ x, F x * G x ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => (hProd x).symm
  calc
    |∫ x, (X x - center) * (p x - q x) ∂μ| =
        |∫ x, F x * G x ∂μ| := by rw [hIntegralEq]
    _ ≤ ∫ x, |F x * G x| ∂μ :=
      abs_integral_le_integral_abs
    _ = ∫ x, |F x| * |G x| ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => abs_mul (F x) (G x)
    _ ≤ Real.sqrt E * Real.sqrt D := hHolder
    _ ≤ Real.sqrt E * influence :=
      mul_le_mul_of_nonneg_left hSqrtDLe (Real.sqrt_nonneg E)
    _ = influence * Real.sqrt E := by ring
    _ =
        (2 * coefficient K) *
          Real.sqrt
            (∫ x, (X x - center) ^ 2 * (p x + q x) ∂μ) := by
      rfl

end HaarLikelihoodRatioInfluence

end

end MGAP4D.MathlibAnalytic

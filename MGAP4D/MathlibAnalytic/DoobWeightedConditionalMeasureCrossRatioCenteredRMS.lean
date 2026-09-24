import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCrossRatioInfluenceMajorant
import MGAP4D.MathlibAnalytic.LikelihoodRatioCenteredExpectationCauchy
import Mathlib.Tactic

/-!
# Centered RMS transport for normalized Doob laws under cross-ratio control

The existing Doob cross-ratio theorem turns an all-pairs multiplicative
cross-ratio estimate into sharp bounded-test transport with coefficient

  M = 2 * (K - 1) / (K + 1).

The likelihood-ratio quadratic-defect/Cauchy spine proves that the same
normalized-density domination controls centered expectations by the identical
linear coefficient times the square root of the two centered energies.

This file connects those two theorem spines.  In particular, no square-root
loss in the influence coefficient and no additional normalization factor is
introduced.  This is the generic interface needed for the remote part of the
physical influence envelope.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HaarLikelihoodRatioInfluence

/-- Two finite ENNReal densities of probability measures, mutually dominated
by the same real likelihood-ratio constant, satisfy the centered RMS
expectation comparison from the real-density Cauchy theorem.

The first- and second-moment integrability receipts are kept explicit so that
bounded physical sections can discharge them without evaluating an arbitrary
L2 quotient representative pointwise. -/
theorem withDensity_centered_integral_sub_abs_le_fullL1_coefficient_mul_sqrt_energy
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (rho sigma : α → ℝ≥0∞)
    (hrhoMeas : Measurable rho)
    (hsigmaMeas : Measurable sigma)
    (hrhoTop : ∀ x, rho x ≠ ∞)
    (hsigmaTop : ∀ x, sigma x ≠ ∞)
    (hrhoOne : μ.withDensity rho Set.univ = 1)
    (hsigmaOne : μ.withDensity sigma Set.univ = 1)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ x,
      rho x ≤ ENNReal.ofReal K * sigma x ∧
        sigma x ≤ ENNReal.ofReal K * rho x)
    (X : α → ℝ)
    (hX : StronglyMeasurable X)
    (center : ℝ)
    (hFirstRho : Integrable (fun x => X x - center) (μ.withDensity rho))
    (hFirstSigma : Integrable (fun x => X x - center) (μ.withDensity sigma))
    (hEnergyRho :
      Integrable (fun x => (X x - center) ^ 2) (μ.withDensity rho))
    (hEnergySigma :
      Integrable (fun x => (X x - center) ^ 2) (μ.withDensity sigma)) :
    |(∫ x, X x - center ∂μ.withDensity rho) -
        (∫ x, X x - center ∂μ.withDensity sigma)| ≤
      (2 * coefficient K) *
        Real.sqrt
          ((∫ x, (X x - center) ^ 2 ∂μ.withDensity rho) +
            ∫ x, (X x - center) ^ 2 ∂μ.withDensity sigma) := by
  let p : α → ℝ := fun x => (rho x).toReal
  let q : α → ℝ := fun x => (sigma x).toReal
  have hrhoLtTop : ∀ᵐ x ∂μ, rho x < (∞ : ℝ≥0∞) :=
    Filter.Eventually.of_forall fun x => lt_top_iff_ne_top.mpr (hrhoTop x)
  have hsigmaLtTop : ∀ᵐ x ∂μ, sigma x < (∞ : ℝ≥0∞) :=
    Filter.Eventually.of_forall fun x => lt_top_iff_ne_top.mpr (hsigmaTop x)
  letI : IsProbabilityMeasure (μ.withDensity rho) := ⟨hrhoOne⟩
  letI : IsProbabilityMeasure (μ.withDensity sigma) := ⟨hsigmaOne⟩

  have hpMeas : Measurable p :=
    ENNReal.measurable_toReal.comp hrhoMeas
  have hqMeas : Measurable q :=
    ENNReal.measurable_toReal.comp hsigmaMeas

  have hpIntRaw :
      Integrable (fun x => (rho x).toReal • (1 : ℝ)) μ := by
    apply
      (integrable_withDensity_iff_integrable_smul₀'
        hrhoMeas.aemeasurable hrhoLtTop).mp
    exact integrable_const (1 : ℝ)
  have hqIntRaw :
      Integrable (fun x => (sigma x).toReal • (1 : ℝ)) μ := by
    apply
      (integrable_withDensity_iff_integrable_smul₀'
        hsigmaMeas.aemeasurable hsigmaLtTop).mp
    exact integrable_const (1 : ℝ)
  have hpInt : Integrable p μ := by
    simpa [p, smul_eq_mul] using hpIntRaw
  have hqInt : Integrable q μ := by
    simpa [q, smul_eq_mul] using hqIntRaw

  have hp0 : ∀ x, 0 ≤ p x := fun x => ENNReal.toReal_nonneg
  have hq0 : ∀ x, 0 ≤ q x := fun x => ENNReal.toReal_nonneg

  have hpOne : ∫ x, p x ∂μ = 1 := by
    have h :=
      integral_withDensity_eq_integral_toReal_smul₀
        hrhoMeas.aemeasurable hrhoLtTop (fun _ : α => (1 : ℝ))
    calc
      (∫ x, p x ∂μ) =
          ∫ x, (rho x).toReal • (1 : ℝ) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            simp [p, smul_eq_mul]
      _ = ∫ _x : α, (1 : ℝ) ∂μ.withDensity rho := h.symm
      _ = 1 := by simp
  have hqOne : ∫ x, q x ∂μ = 1 := by
    have h :=
      integral_withDensity_eq_integral_toReal_smul₀
        hsigmaMeas.aemeasurable hsigmaLtTop (fun _ : α => (1 : ℝ))
    calc
      (∫ x, q x ∂μ) =
          ∫ x, (sigma x).toReal • (1 : ℝ) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            simp [q, smul_eq_mul]
      _ = ∫ _x : α, (1 : ℝ) ∂μ.withDensity sigma := h.symm
      _ = 1 := by simp

  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hpq : ∀ x, p x ≤ K * q x := by
    intro x
    have hTop :
        ENNReal.ofReal K * sigma x ≠ (∞ : ℝ≥0∞) :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hsigmaTop x)
    have h :=
      ENNReal.toReal_mono hTop (hRatio x).1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at h
    simpa [p, q] using h
  have hqp : ∀ x, q x ≤ K * p x := by
    intro x
    have hTop :
        ENNReal.ofReal K * rho x ≠ (∞ : ℝ≥0∞) :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hrhoTop x)
    have h :=
      ENNReal.toReal_mono hTop (hRatio x).2
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at h
    simpa [p, q] using h

  have hFirstP0 :
      Integrable (fun x => (rho x).toReal • (X x - center)) μ :=
    (integrable_withDensity_iff_integrable_smul₀'
      hrhoMeas.aemeasurable hrhoLtTop).mp hFirstRho
  have hFirstQ0 :
      Integrable (fun x => (sigma x).toReal • (X x - center)) μ :=
    (integrable_withDensity_iff_integrable_smul₀'
      hsigmaMeas.aemeasurable hsigmaLtTop).mp hFirstSigma
  have hFirstP :
      Integrable (fun x => (X x - center) * p x) μ := by
    apply hFirstP0.congr
    filter_upwards with x
    simp [p, smul_eq_mul]
    ring
  have hFirstQ :
      Integrable (fun x => (X x - center) * q x) μ := by
    apply hFirstQ0.congr
    filter_upwards with x
    simp [q, smul_eq_mul]
    ring

  have hEnergyP0 :
      Integrable (fun x => (rho x).toReal • (X x - center) ^ 2) μ :=
    (integrable_withDensity_iff_integrable_smul₀'
      hrhoMeas.aemeasurable hrhoLtTop).mp hEnergyRho
  have hEnergyQ0 :
      Integrable (fun x => (sigma x).toReal • (X x - center) ^ 2) μ :=
    (integrable_withDensity_iff_integrable_smul₀'
      hsigmaMeas.aemeasurable hsigmaLtTop).mp hEnergySigma
  have hEnergyP :
      Integrable (fun x => (X x - center) ^ 2 * p x) μ := by
    apply hEnergyP0.congr
    filter_upwards with x
    simp [p, smul_eq_mul]
    ring
  have hEnergyQ :
      Integrable (fun x => (X x - center) ^ 2 * q x) μ := by
    apply hEnergyQ0.congr
    filter_upwards with x
    simp [q, smul_eq_mul]
    ring
  have hEnergy :
      Integrable
        (fun x => (X x - center) ^ 2 * (p x + q x)) μ := by
    simpa only [Pi.add_apply, mul_add] using hEnergyP.add hEnergyQ

  have hCore :=
    centered_density_difference_integral_abs_le_fullL1_coefficient_mul_sqrt_energy
      μ p q hpMeas hqMeas hpInt hqInt hp0 hq0 hpOne hqOne
      K hK (fun x => ⟨hpq x, hqp x⟩)
      X hX center hEnergy

  have hCenteredRho :
      (∫ x, X x - center ∂μ.withDensity rho) =
        ∫ x, (X x - center) * p x ∂μ := by
    rw [
      integral_withDensity_eq_integral_toReal_smul₀
        hrhoMeas.aemeasurable hrhoLtTop]
    apply integral_congr_ae
    filter_upwards with x
    simp [p, smul_eq_mul]
    ring
  have hCenteredSigma :
      (∫ x, X x - center ∂μ.withDensity sigma) =
        ∫ x, (X x - center) * q x ∂μ := by
    rw [
      integral_withDensity_eq_integral_toReal_smul₀
        hsigmaMeas.aemeasurable hsigmaLtTop]
    apply integral_congr_ae
    filter_upwards with x
    simp [q, smul_eq_mul]
    ring
  have hCenteredDifference :
      (∫ x, (X x - center) * p x ∂μ) -
          (∫ x, (X x - center) * q x ∂μ) =
        ∫ x, (X x - center) * (p x - q x) ∂μ := by
    rw [← integral_sub hFirstP hFirstQ]
    apply integral_congr_ae
    filter_upwards with x
    ring

  have hEnergyRhoEq :
      (∫ x, (X x - center) ^ 2 ∂μ.withDensity rho) =
        ∫ x, (X x - center) ^ 2 * p x ∂μ := by
    rw [
      integral_withDensity_eq_integral_toReal_smul₀
        hrhoMeas.aemeasurable hrhoLtTop]
    apply integral_congr_ae
    filter_upwards with x
    simp [p, smul_eq_mul]
    ring
  have hEnergySigmaEq :
      (∫ x, (X x - center) ^ 2 ∂μ.withDensity sigma) =
        ∫ x, (X x - center) ^ 2 * q x ∂μ := by
    rw [
      integral_withDensity_eq_integral_toReal_smul₀
        hsigmaMeas.aemeasurable hsigmaLtTop]
    apply integral_congr_ae
    filter_upwards with x
    simp [q, smul_eq_mul]
    ring
  have hEnergyEq :
      (∫ x, (X x - center) ^ 2 * (p x + q x) ∂μ) =
        (∫ x, (X x - center) ^ 2 ∂μ.withDensity rho) +
          ∫ x, (X x - center) ^ 2 ∂μ.withDensity sigma := by
    calc
      (∫ x, (X x - center) ^ 2 * (p x + q x) ∂μ) =
          (∫ x, (X x - center) ^ 2 * p x ∂μ) +
            ∫ x, (X x - center) ^ 2 * q x ∂μ := by
              rw [← integral_add hEnergyP hEnergyQ]
              apply integral_congr_ae
              filter_upwards with x
              ring
      _ =
          (∫ x, (X x - center) ^ 2 ∂μ.withDensity rho) +
            ∫ x, (X x - center) ^ 2 ∂μ.withDensity sigma := by
              rw [hEnergyRhoEq, hEnergySigmaEq]

  rw [hCenteredRho, hCenteredSigma, hCenteredDifference]
  rw [hEnergyEq] at hCore
  exact hCore

/-- All-pairs cross-ratio control of two normalized Doob laws yields centered
RMS expectation transport with exactly the same full-L1 influence majorant
used by the bounded-test theorem.

The strict M < 2 branch is the one needed by the positive high-temperature
physical remote residual.  The inverse Mobius constant
K = (2+M)/(2-M) is used only internally; the conclusion is expressed with M,
so no new external coefficient is introduced. -/
theorem doobWeightedMeasure_centered_integral_sub_abs_le_crossRatioInfluenceMajorant_mul_sqrt_energy
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w v : α → ℝ≥0∞)
    (hwMeas : Measurable w) (hvMeas : Measurable v)
    (radius : α → α → ℝ) (M : ℝ) (hMNonneg : 0 ≤ M) (hMltTwo : M < 2)
    (hRadiusNonneg : ∀ x y, 0 ≤ radius x y)
    (hInfluence : ∀ x y, finitePositiveWeightCrossRatioInfluenceTransform (radius x y) ≤ M)
    (hwtop : ∀ x, w x ≠ ∞) (hvtop : ∀ x, v x ≠ ∞)
    (hMassW0 : doobWeightMass μ w ≠ 0) (hMassWtop : doobWeightMass μ w ≠ ∞)
    (hMassV0 : doobWeightMass μ v ≠ 0) (hMassVtop : doobWeightMass μ v ≠ ∞)
    (hcross : ∀ x y, w x * v y ≤ ENNReal.ofReal (Real.exp (radius x y)) * v x * w y)
    (X : α → ℝ) (hX : StronglyMeasurable X) (center : ℝ)
    (hFirstW : Integrable (fun x => X x - center) (doobWeightedMeasure μ w))
    (hFirstV : Integrable (fun x => X x - center) (doobWeightedMeasure μ v))
    (hEnergyW : Integrable (fun x => (X x - center) ^ 2) (doobWeightedMeasure μ w))
    (hEnergyV : Integrable (fun x => (X x - center) ^ 2) (doobWeightedMeasure μ v)) :
    |(∫ x, X x - center ∂doobWeightedMeasure μ w) -
        (∫ x, X x - center ∂doobWeightedMeasure μ v)| ≤
      M * Real.sqrt
        ((∫ x, (X x - center) ^ 2 ∂doobWeightedMeasure μ w) +
          ∫ x, (X x - center) ^ 2 ∂doobWeightedMeasure μ v) := by
  let K : ℝ := (2 + M) / (2 - M)
  have hTwoSub : 0 < 2 - M := sub_pos.mpr hMltTwo
  have hK : 1 ≤ K := by
    dsimp [K]
    apply (le_div_iff₀ hTwoSub).2
    nlinarith
  have hK0 : 0 ≤ K := le_trans zero_le_one hK

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
        exact
          mul_le_mul_right'
            (mul_le_mul_right'
              (ENNReal.ofReal_le_ofReal (hExpLeK x y))
              (v x))
            (w y)

  let rho : α → ℝ≥0∞ := doobWeightedDensity μ w
  let sigma : α → ℝ≥0∞ := doobWeightedDensity μ v
  have hrhoMeas : Measurable rho := by
    dsimp [rho, doobWeightedDensity]
    exact hwMeas.div_const _
  have hsigmaMeas : Measurable sigma := by
    dsimp [sigma, doobWeightedDensity]
    exact hvMeas.div_const _
  have hrhoTop : ∀ x, rho x ≠ ∞ := by
    intro x
    dsimp [rho, doobWeightedDensity]
    exact ENNReal.div_ne_top (hwtop x) hMassW0
  have hsigmaTop : ∀ x, sigma x ≠ ∞ := by
    intro x
    dsimp [sigma, doobWeightedDensity]
    exact ENNReal.div_ne_top (hvtop x) hMassV0

  have hrhoOne : μ.withDensity rho Set.univ = 1 := by
    simpa [rho, doobWeightedMeasure] using
      doobWeightedMeasure_measure_univ
        μ w hwMeas.aemeasurable hMassW0 hMassWtop
  have hsigmaOne : μ.withDensity sigma Set.univ = 1 := by
    simpa [sigma, doobWeightedMeasure] using
      doobWeightedMeasure_measure_univ
        μ v hvMeas.aemeasurable hMassV0 hMassVtop

  have hrhoSigma : ∀ x,
      rho x ≤ ENNReal.ofReal K * sigma x := by
    intro x
    simpa [rho, sigma] using
      doobWeightedDensity_le_mul_of_cross_ratio
        μ w v (ENNReal.ofReal K) ENNReal.ofReal_ne_top
        hwtop hvtop hMassW0 hMassWtop hMassV0 hMassVtop
        hCrossUniform x
  have hCrossUniformSwap : ∀ x y,
      v x * w y ≤ ENNReal.ofReal K * w x * v y := by
    intro x y
    simpa [mul_comm, mul_left_comm, mul_assoc] using hCrossUniform y x
  have hsigmaRho : ∀ x,
      sigma x ≤ ENNReal.ofReal K * rho x := by
    intro x
    simpa [rho, sigma] using
      doobWeightedDensity_le_mul_of_cross_ratio
        μ v w (ENNReal.ofReal K) ENNReal.ofReal_ne_top
        hvtop hwtop hMassV0 hMassVtop hMassW0 hMassWtop
        hCrossUniformSwap x

  have hCore :=
    withDensity_centered_integral_sub_abs_le_fullL1_coefficient_mul_sqrt_energy
      μ rho sigma hrhoMeas hsigmaMeas hrhoTop hsigmaTop
      hrhoOne hsigmaOne K hK
      (fun x => ⟨hrhoSigma x, hsigmaRho x⟩)
      X hX center
      (by simpa [rho, doobWeightedMeasure] using hFirstW)
      (by simpa [sigma, doobWeightedMeasure] using hFirstV)
      (by simpa [rho, doobWeightedMeasure] using hEnergyW)
      (by simpa [sigma, doobWeightedMeasure] using hEnergyV)

  have hCoeff :
      2 * coefficient K = M := by
    dsimp [K, coefficient]
    field_simp [ne_of_gt hTwoSub]
    <;> ring

  simpa [rho, sigma, doobWeightedMeasure, hCoeff] using hCore

end HaarLikelihoodRatioInfluence

end

end MGAP4D.MathlibAnalytic

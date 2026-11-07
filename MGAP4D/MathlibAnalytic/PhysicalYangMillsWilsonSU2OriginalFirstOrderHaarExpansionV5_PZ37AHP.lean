import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullKernelBetaStabilityV5_PZ37AHO
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHP — first-order expansion of the ORIGINAL signed Haar transfer

Keep the original full Wilson slab action S(A,B), both spatial halfweights,
ZW centered physical source f=(W-p_H)/2, and original product Haar mu_H.
For every beta >= 0, with the proved original global action budget C_H,

  T_beta(B) = -beta * (V_H + X_H(B)) + R_beta(B),
  |R_beta(B)| <= (beta*C_H)^2 * Msrc_H / 2,
  V_H = integral f^2 dmu_H,
  X_H(B) = integral f(A)*S_cross(A,B) dmu_H(A).

The source mean is PROVED zero; the right spatial halfweight term therefore
cancels exactly. The left spatial halfweight yields exactly V_H, not 2*V_H.
The global scalar bound 0 <= exp(-x)-1+x <= x^2/2 for x>=0 requires no
smallness hypothesis beta*C_H<=1 and is proved with pinned mathlib calculus.
The signed source is never replaced by a positive source.

AHN's explicit V_H floor is transported into a genuine transfer upper bound
and a conditional negative-sign criterion with the ACTUAL named crossing
correlation and quadratic remainder. X_H(B) is NOT assumed to vanish or to
have any sign. The criterion is not asserted satisfied at fixed beta0.
No evaluated AGP sign table, both-sign shell, H-uniform coercivity,
Hamiltonian spectral gap or continuum Yang--Mills mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Global one-sided exponential Taylor remainder, including x=0.
The quadratic coefficient 1/2 comes from the derivative comparison,
not an assumed convergent finite-volume smallness regime. -/
theorem p4Q2PZ37AHP_exp_neg_quadraticRemainder
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ Real.exp (-x) - 1 + x ∧
      Real.exp (-x) - 1 + x ≤ x ^ 2 / 2 := by
  have hLow : 0 ≤ Real.exp (-x) - 1 + x := by
    have h := Real.add_one_le_exp (-x)
    linarith only [h]
  have hDeriv (t : ℝ) :
      HasDerivAt (fun y : ℝ => Real.exp (-y) - 1 + y)
        (1 - Real.exp (-t)) t := by
    convert (((hasDerivAt_id t).neg.exp).sub_const 1).add
      (hasDerivAt_id t) using 1 <;> ring
  have hPoly (t : ℝ) :
      HasDerivAt (fun y : ℝ => y ^ 2 / 2) t t := by
    convert ((hasDerivAt_id t).pow 2).div_const (2 : ℝ) using 1 <;> ring
  have hCont : Continuous (fun y : ℝ => Real.exp (-y) - 1 + y) :=
    ((Real.continuous_exp.comp continuous_id.neg).sub continuous_const).add
      continuous_id
  have hUpper : Real.exp (-x) - 1 + x ≤ x ^ 2 / 2 := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (a := (0 : ℝ)) (b := x)
      (B := fun y : ℝ => y ^ 2 / 2) (B' := fun y : ℝ => y)
      hCont.continuousOn
      (fun t _ => (hDeriv t).hasDerivWithinAt)
      (by norm_num)
      (by fun_prop)
      (fun t _ => (hPoly t).hasDerivWithinAt)
      (fun t _ => ?_)
      ⟨hx, le_rfl⟩
    have h := Real.add_one_le_exp (-t)
    linarith only [h]
  exact ⟨hLow, hUpper⟩

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHP_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHP_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHP_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHP_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHP_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Cslab" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H

local instance p4Q2PZ37AHP_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHP_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Continuity of the literal temporal crossing ACTION at fixed right B,
proved on the original link list, not postulated for a new kernel. -/
theorem p4Q2PZ37AHP_originalCrossing_continuous (B : Cfg) :
    Continuous (fun A : Cfg => Cross A B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil => simpa using (continuous_const : Continuous (fun _ : Cfg => (0 : ℝ)))
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      have hLink : Continuous (fun A : Cfg => (A e)⁻¹ * B e) :=
        (continuous_apply e).inv.mul continuous_const
      exact ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp hLink).add ih

/-- The original COMPLETE action includes both original spatial halfweights. -/
theorem p4Q2PZ37AHP_originalFullAction_continuous (B : Cfg) :
    Continuous (fun A : Cfg => S A B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  exact ((continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)).add
    (p4Q2PZ37AHP_originalCrossing_continuous H B)).add continuous_const

/-- True original Haar centering, not a pointwise claim about an arbitrary
physical L2 representative. -/
theorem p4Q2PZ37AHP_originalSource_mean_zero :
    (∫ A : Cfg, fCont A ∂muH) = 0 := by
  have hW : Integrable W muH :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2).
      integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hMean : (∫ A : Cfg, W A ∂muH) = pH := by
    calc
      (∫ A : Cfg, W A ∂muH) = p4Q2PZ37AFZ_originalWilsonMean H :=
        (p4Q2PZ37AFZ_originalWilsonMean_eq_integral H).symm
      _ = pH := p4Q2PZ37AGN_originalWilsonMean_exact H
  calc
    (∫ A : Cfg, fCont A ∂muH) = ((∫ A : Cfg, W A ∂muH) - pH) / 2 := by
      simp_rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H]
      rw [integral_div, integral_sub hW (integrable_const _)]
      simp
    _ = 0 := by rw [hMean]; ring

/-- Physical L2 transfer and continuous-source integral agree for EVERY
coupling by the proven original Haar-a.e. representative equality. -/
theorem p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral
    (beta : ℝ) (B : Cfg) :
    T beta f0 B = ∫ A : Cfg, fCont A * K beta A B ∂muH := by
  have hRep : (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) =ᵐ[muH] fCont := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := muH) fCont
  rw [p4Q2LJ_originalPhysicalTransfer_eq_continuousWilsonKernelIntegral
    H beta f0 fCont hRep B]
  apply integral_congr_ae
  filter_upwards with A
  ring

/-- The constant term of the actual original transfer vanishes exactly. -/
theorem p4Q2PZ37AHP_originalTransfer_zeroCoupling (B : Cfg) :
    T 0 f0 B = 0 := by
  rw [p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H]
  simp_rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    neg_zero, zero_mul, Real.exp_zero, mul_one]
  exact p4Q2PZ37AHP_originalSource_mean_zero H

/-- Exact first action moment determining the first-order transfer term. -/
def p4Q2PZ37AHP_originalFirstActionMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, fCont A * S A B ∂muH

/-- Actual temporal crossing/source correlation. Its sign and vanishing
are intentionally NOT built into the definition or assumed. -/
def p4Q2PZ37AHP_originalCrossingCorrelation (B : Cfg) : ℝ :=
  ∫ A : Cfg, fCont A * Cross A B ∂muH

/-- The true first action moment is exactly the AHN source second moment
plus the genuine temporal crossing correlation. Right spatial terms cancel
by mean zero; the left halfweight contributes V, not 2*V. -/
theorem p4Q2PZ37AHP_originalFirstMoment_eq_variance_add_crossing (B : Cfg) :
    p4Q2PZ37AHP_originalFirstActionMoment H B =
      Vsrc + p4Q2PZ37AHP_originalCrossingCorrelation H B := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hSq : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCross : Integrable (fun A : Cfg => fCont A * Cross A B) muH :=
    (hf.mul (p4Q2PZ37AHP_originalCrossing_continuous H B)).
      integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let c : ℝ := (pH + W B) / 2
  have hConst : Integrable (fun A : Cfg => c * fCont A) muH :=
    (continuous_const.mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (A : Cfg) :
      fCont A * S A B =
        ((fCont A) ^ 2 + fCont A * Cross A B) + c * fCont A := by
    have hSource := p4Q2PZ37AGN_originalCenteredContinuous_eq H A
    have hW : W A = 2 * fCont A + pH := by linarith only [hSource]
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    rw [hW]
    dsimp [c]
    ring
  unfold p4Q2PZ37AHP_originalFirstActionMoment
  simp_rw [hPoint]
  rw [integral_add (hSq.add hCross) hConst, integral_add hSq hCross,
    integral_const_mul, p4Q2PZ37AHP_originalSource_mean_zero H]
  simp only [mul_zero, add_zero]
  rfl

/-- Uniform kernel Taylor remainder for ALL nonnegative couplings.
No new action budget and no beta*Cslab <= 1 assumption. -/
theorem p4Q2PZ37AHP_originalKernel_firstOrder_bound
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    |K beta A B - (1 - beta * S A B)| ≤ (beta * Cslab) ^ 2 / 2 := by
  have hS : 0 ≤ S A B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B
  have hCap : S A B ≤ Cslab :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by norm_num) A B
  have hx : 0 ≤ beta * S A B := mul_nonneg hbeta hS
  have hxc : beta * S A B ≤ beta * Cslab :=
    mul_le_mul_of_nonneg_left hCap hbeta
  have hc : 0 ≤ beta * Cslab := hx.trans hxc
  have hSq : (beta * S A B) ^ 2 ≤ (beta * Cslab) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hxc) (add_nonneg hc hx)]
  obtain ⟨hLo, hHi⟩ := p4Q2PZ37AHP_exp_neg_quadraticRemainder (beta * S A B) hx
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  have hEq : Real.exp (-beta * S A B) - (1 - beta * S A B) =
      Real.exp (-(beta * S A B)) - 1 + beta * S A B := by
    rw [neg_mul]
    ring
  rw [hEq, abs_of_nonneg hLo]
  linarith only [hHi, hSq]

/-- Actual finite-H error budget using the same true original source L1 mass. -/
def p4Q2PZ37AHP_originalQuadraticBudget (beta : ℝ) : ℝ :=
  ((beta * Cslab) ^ 2 / 2) * Msrc

theorem p4Q2PZ37AHP_originalQuadraticBudget_nonneg (beta : ℝ) :
    0 ≤ p4Q2PZ37AHP_originalQuadraticBudget H beta := by
  exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)

/-- Integrate the true full-kernel Taylor remainder against the SIGNED
original physical source, using its true Haar L1 mass only as an upper bound. -/
theorem p4Q2PZ37AHP_originalTransfer_firstOrder_bound
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |T beta f0 B + beta * p4Q2PZ37AHP_originalFirstActionMoment H B| ≤
      p4Q2PZ37AHP_originalQuadraticBudget H beta := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hfInt : Integrable (fun A : Cfg => fCont A) muH :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS := p4Q2PZ37AHP_originalFullAction_continuous H B
  have hK : Continuous (fun A : Cfg => K beta A B) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp (continuous_id.prodMk continuous_const)
  have hKernelInt : Integrable (fun A : Cfg => fCont A * K beta A B) muH :=
    (hf.mul hK).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLinearInt : Integrable (fun A : Cfg => fCont A * (1 - beta * S A B)) muH :=
    (hf.mul (continuous_const.sub (continuous_const.mul hS))).
      integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hActionInt : Integrable (fun A : Cfg => fCont A * S A B) muH :=
    (hf.mul hS).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLinear : (∫ A : Cfg, fCont A * (1 - beta * S A B) ∂muH) =
      -(beta * p4Q2PZ37AHP_originalFirstActionMoment H B) := by
    calc
      (∫ A : Cfg, fCont A * (1 - beta * S A B) ∂muH) =
          ∫ A : Cfg, fCont A - beta * (fCont A * S A B) ∂muH := by
        apply integral_congr_ae
        filter_upwards with A
        ring
      _ = -(beta * p4Q2PZ37AHP_originalFirstActionMoment H B) := by
        rw [integral_sub hfInt (hActionInt.const_mul beta), integral_const_mul,
          p4Q2PZ37AHP_originalSource_mean_zero H]
        simp only [zero_sub, p4Q2PZ37AHP_originalFirstActionMoment]
  have hBound := p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
    muH (fun A : Cfg => fCont A) (fun A : Cfg => K beta A B)
    (fun A : Cfg => 1 - beta * S A B) ((beta * Cslab) ^ 2 / 2)
    hfInt hKernelInt hLinearInt
    (fun A => p4Q2PZ37AHP_originalKernel_firstOrder_bound H beta hbeta A B)
  rw [hLinear, sub_neg_eq_add,
    ← p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta B,
    ← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H] at hBound
  exact hBound

/-- Explicit source/crossing decomposition inside the true transfer error. -/
theorem p4Q2PZ37AHP_originalTransfer_varianceCrossing_bound
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |T beta f0 B + beta *
        (Vsrc + p4Q2PZ37AHP_originalCrossingCorrelation H B)| ≤
      p4Q2PZ37AHP_originalQuadraticBudget H beta := by
  rw [← p4Q2PZ37AHP_originalFirstMoment_eq_variance_add_crossing H B]
  exact p4Q2PZ37AHP_originalTransfer_firstOrder_bound H beta hbeta B

/-- Two-sided signed enclosure, retaining all cancellation information. -/
theorem p4Q2PZ37AHP_originalTransfer_signedInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    -(beta * (Vsrc + p4Q2PZ37AHP_originalCrossingCorrelation H B)) -
        p4Q2PZ37AHP_originalQuadraticBudget H beta ≤ T beta f0 B ∧
      T beta f0 B ≤
        -(beta * (Vsrc + p4Q2PZ37AHP_originalCrossingCorrelation H B)) +
          p4Q2PZ37AHP_originalQuadraticBudget H beta := by
  have h := abs_le.mp
    (p4Q2PZ37AHP_originalTransfer_varianceCrossing_bound H beta hbeta B)
  constructor <;> linarith only [h.1, h.2]

/-- The ORIGINAL AHN source floor, not a newly postulated transfer floor. -/
def p4Q2PZ37AHP_originalVarianceFloor : ℝ :=
  (3 * pH / 8) ^ 2 *
    p4Q2PZ37ADQ_sphereRadiusFraction (1 / 96) ^ Fintype.card Link

/-- AHN's source second-moment floor now enters an actual original TRANSFER
upper bound. The actual crossing correlation is retained, not silently zeroed. -/
theorem p4Q2PZ37AHP_originalTransfer_upper_from_AHN
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    T beta f0 B ≤
      -(beta * (p4Q2PZ37AHP_originalVarianceFloor H +
        p4Q2PZ37AHP_originalCrossingCorrelation H B)) +
      p4Q2PZ37AHP_originalQuadraticBudget H beta := by
  have hFloor : p4Q2PZ37AHP_originalVarianceFloor H ≤ Vsrc :=
    p4Q2PZ37AHN_originalSource_HaarSecondMoment_explicitFloor H
  have hScaled := mul_le_mul_of_nonneg_left
    (add_le_add_right hFloor (p4Q2PZ37AHP_originalCrossingCorrelation H B)) hbeta
  have hUpper := (p4Q2PZ37AHP_originalTransfer_signedInterval H beta hbeta B).2
  linarith only [hScaled, hUpper]

/-- Exact conditional negative-sign certificate from actual original data.
No assertion that this budget is satisfied at the original fixed beta0. -/
theorem p4Q2PZ37AHP_originalTransfer_negative_of_budget
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hBudget : p4Q2PZ37AHP_originalQuadraticBudget H beta <
      beta * (p4Q2PZ37AHP_originalVarianceFloor H +
        p4Q2PZ37AHP_originalCrossingCorrelation H B)) :
    T beta f0 B < 0 := by
  have hUpper := p4Q2PZ37AHP_originalTransfer_upper_from_AHN H beta hbeta B
  linarith only [hBudget, hUpper]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHP_exp_neg_quadraticRemainder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalCrossing_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalFullAction_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalSource_mean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalTransfer_zeroCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalFirstMoment_eq_variance_add_crossing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalKernel_firstOrder_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalQuadraticBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalTransfer_firstOrder_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalTransfer_varianceCrossing_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalTransfer_signedInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalTransfer_upper_from_AHN
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHP_originalTransfer_negative_of_budget

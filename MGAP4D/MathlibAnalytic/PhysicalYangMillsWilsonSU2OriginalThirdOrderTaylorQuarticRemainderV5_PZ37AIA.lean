import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUniformCenterCubicActionMomentV5_PZ37AHZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIA — genuine cubic transfer expansion and quartic remainder

Keep the complete original Wilson action S, both spatial halfweights, the
original signed ZW source f, the original product Haar and physical transfer.
AHX's exact quadratic center and AHZ's true cubic moment define P3. The new
R4 is the actual signed integral of the original kernel minus its cubic
Taylor polynomial; T=P3+R4 and R4=R3+(beta^3/6)*M3full for every real beta.

For every beta>=0 the scalar kernel remainder is nonnegative and at most
(beta*S)^4/24. Its signed-source interval therefore uses the NEGATIVE part
on the lower side and the POSITIVE part on the upper side:
  -(beta^4/24)*J4minus <= R4 <= (beta^4/24)*J4plus.
The quartic source/action moments remain genuine correlated Haar integrals.
AHY's exact half-masses and right-boundary cap C_B give
  |R4| <= E4_B := ((beta*C_B)^4/48)*Msrc.
No smallness assumption or exponential loss is used in this error bound.

AHZ's positive variance floor also gives a completed-square inequality:
  P3 <= -beta*V/2 - (beta*V/8)*(beta*(3*p_H+W(B))-2)^2.
Hence P3 is strictly negative for every beta>0. This is a statement about
the cubic approximation, not an unconditional sign for the actual transfer.
Actual negative-transfer certificates retain explicit quartic margins,
including at the original fixed beta0. The cubic interval's lower endpoint
is nonpositive and cannot certify a positive transfer by itself.

No actual fixed-beta sign shell, volume-uniform coercivity, Hamiltonian gap
or continuum Yang-Mills mass gap is asserted. All previous definitions,
files, typed histories, roots, toolchain pins and workflows are preserved.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Fourth-order remainder of the genuine negative exponential,
valid globally for x >= 0. -/
theorem p4Q2PZ37AIA_exp_neg_quarticRemainder
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ Real.exp (-x) - (1 - x + x ^ 2 / 2 - x ^ 3 / 6) ∧
      Real.exp (-x) - (1 - x + x ^ 2 / 2 - x ^ 3 / 6) ≤ x ^ 4 / 24 := by
  have hLow : 0 ≤ Real.exp (-x) - (1 - x + x ^ 2 / 2 - x ^ 3 / 6) := by
    have h := (p4Q2PZ37AHX_exp_neg_cubicRemainder x hx).2
    linarith only [h]
  have hDeriv (t : ℝ) :
      HasDerivAt
        (fun y : ℝ => Real.exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6))
        (1 - t + t ^ 2 / 2 - Real.exp (-t)) t := by
    convert ((hasDerivAt_id t).neg.exp).sub
      ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        (((hasDerivAt_id t).pow 2).div_const (2 : ℝ))).sub
          (((hasDerivAt_id t).pow 3).div_const (6 : ℝ))) using 1
    simp
    ring
  have hPoly (t : ℝ) :
      HasDerivAt (fun y : ℝ => y ^ 4 / 24) (t ^ 3 / 6) t := by
    convert ((hasDerivAt_id t).pow 4).div_const (24 : ℝ) using 1
    simp
    ring
  have hCont : Continuous
      (fun y : ℝ => Real.exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6)) := by
    fun_prop
  have hUpper :
      Real.exp (-x) - (1 - x + x ^ 2 / 2 - x ^ 3 / 6) ≤ x ^ 4 / 24 := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (a := (0 : ℝ)) (b := x)
      (B := fun y : ℝ => y ^ 4 / 24) (B' := fun y : ℝ => y ^ 3 / 6)
      hCont.continuousOn
      (fun t _ => (hDeriv t).hasDerivWithinAt)
      (by norm_num)
      (by fun_prop)
      (fun t _ => (hPoly t).hasDerivWithinAt)
      (fun t ht => ?_)
      ⟨hx, le_rfl⟩
    exact (p4Q2PZ37AHX_exp_neg_cubicRemainder t ht.1).2
  exact ⟨hLow, hUpper⟩


/-- A nonnegative error couples to the original signed source with the
negative part below and the positive part above. -/
theorem p4Q2PZ37AIA_real_signedNonnegativeError_interval
    (f r d : ℝ) (hr : 0 ≤ r ∧ r ≤ d) :
    -((|f| - f) / 2) * d ≤ f * r ∧
      f * r ≤ ((|f| + f) / 2) * d := by
  have hNeg : -d ≤ -r ∧ -r ≤ 0 :=
    ⟨neg_le_neg hr.2, neg_nonpos.mpr hr.1⟩
  have h := p4Q2PZ37AHY_real_signedNonpositiveError_interval f (-r) d hNeg
  constructor <;> nlinarith only [h.1, h.2]

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIA_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIA_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIA_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIA_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIA_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Q2" => p4Q2PZ37AHX_originalQuadraticApproximation H
local notation "R3" => p4Q2PZ37AHX_originalThirdOrderRemainder H
local notation "M3full" => p4Q2PZ37AHZ_originalThirdFullActionHaarMoment H
local notation "Q4" => p4Q2PZ37AHZ_originalSourceFourthHaarMoment H
local notation "D" => p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment H

local instance p4Q2PZ37AIA_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The exact integrated cubic polynomial retains the actual full-action moment. -/
def p4Q2PZ37AIA_originalCubicApproximation (beta : ℝ) (B : Cfg) : ℝ :=
  Q2 beta B - (beta ^ 3 / 6) * M3full B

local notation "P3" => p4Q2PZ37AIA_originalCubicApproximation H

/-- A genuine integral of the ORIGINAL kernel minus its cubic polynomial. -/
def p4Q2PZ37AIA_originalFourthOrderRemainder (beta : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, fCont A *
    (K beta A B -
      (1 - beta * S A B + (beta * S A B) ^ 2 / 2 -
        (beta * S A B) ^ 3 / 6)) ∂muH

local notation "R4" => p4Q2PZ37AIA_originalFourthOrderRemainder H

/-- Integrability uses AHY's real R3 integrand and AHZ's full cubic integrand. -/
theorem p4Q2PZ37AIA_originalFourthOrderRemainder_integrable
    (beta : ℝ) (B : Cfg) :
    Integrable (fun A : Cfg => fCont A *
      (K beta A B -
        (1 - beta * S A B + (beta * S A B) ^ 2 / 2 -
          (beta * S A B) ^ 3 / 6))) muH := by
  have hR3 := p4Q2PZ37AHY_originalThirdOrderRemainder_integrable H beta B
  have hCube := p4Q2PZ37AHZ_originalThirdFullAction_integrable H B
  have hPoint (A : Cfg) :
      fCont A *
        (K beta A B -
          (1 - beta * S A B + (beta * S A B) ^ 2 / 2 -
            (beta * S A B) ^ 3 / 6)) =
      fCont A * (K beta A B -
        (1 - beta * S A B + (beta * S A B) ^ 2 / 2)) +
        (beta ^ 3 / 6) * (fCont A * (S A B) ^ 3) := by
    ring
  refine (hR3.add (hCube.const_mul (beta ^ 3 / 6))).congr ?_
  filter_upwards with A
  exact (hPoint A).symm

/-- Exact remainder bridge; no coupling sign or scalar error bound is required. -/
theorem p4Q2PZ37AIA_originalFourthOrderRemainder_eq_third_add
    (beta : ℝ) (B : Cfg) :
    R4 beta B = R3 beta B + (beta ^ 3 / 6) * M3full B := by
  have hR3 := p4Q2PZ37AHY_originalThirdOrderRemainder_integrable H beta B
  have hCube := p4Q2PZ37AHZ_originalThirdFullAction_integrable H B
  calc
    R4 beta B =
        ∫ A : Cfg,
          fCont A * (K beta A B -
            (1 - beta * S A B + (beta * S A B) ^ 2 / 2)) +
            (beta ^ 3 / 6) * (fCont A * (S A B) ^ 3) ∂muH := by
      unfold p4Q2PZ37AIA_originalFourthOrderRemainder
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ =
        (∫ A : Cfg, fCont A * (K beta A B -
          (1 - beta * S A B + (beta * S A B) ^ 2 / 2)) ∂muH) +
        (beta ^ 3 / 6) * (∫ A : Cfg, fCont A * (S A B) ^ 3 ∂muH) := by
      rw [integral_add hR3 (hCube.const_mul (beta ^ 3 / 6)), integral_const_mul]
    _ = R3 beta B + (beta ^ 3 / 6) * M3full B := rfl

/-- The remainder is the error of the same physical L2 transfer as AHX. -/
theorem p4Q2PZ37AIA_originalFourthOrderRemainder_eq_sub
    (beta : ℝ) (B : Cfg) :
    R4 beta B = T beta f0 B - P3 beta B := by
  rw [p4Q2PZ37AIA_originalFourthOrderRemainder_eq_third_add H beta B,
    p4Q2PZ37AHX_originalThirdOrderRemainder_eq_sub H beta B]
  unfold p4Q2PZ37AIA_originalCubicApproximation
  ring

/-- Exact third-order expansion of the original complete Boltzmann transfer. -/
theorem p4Q2PZ37AIA_originalTransfer_thirdOrder_expansion
    (beta : ℝ) (B : Cfg) :
    T beta f0 B =
      -(beta * Vsrc) +
        (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc) -
        (beta ^ 3 / 6) * M3full B + R4 beta B := by
  rw [p4Q2PZ37AIA_originalFourthOrderRemainder_eq_sub H beta B]
  unfold p4Q2PZ37AIA_originalCubicApproximation
    p4Q2PZ37AHX_originalQuadraticApproximation
  ring

/-- AHZ's exact positive full-action coefficient is retained in the cubic term. -/
theorem p4Q2PZ37AIA_originalTransfer_thirdOrder_expansion_exactCubic
    (beta : ℝ) (B : Cfg) :
    T beta f0 B =
      -(beta * Vsrc) +
        (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc) -
        (beta ^ 3 / 6) *
          (Q4 + (3 / 4 : ℝ) * (3 * pH + W B) ^ 2 * Vsrc + 3 * D B) +
        R4 beta B := by
  rw [p4Q2PZ37AIA_originalTransfer_thirdOrder_expansion H beta B,
    p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_exact H B]


local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "Cslab" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "CB" => p4Q2PZ37AHY_originalBoundaryActionBudget H
local notation "fp" => p4Q2PZ37AHY_originalSourcePositivePart H
local notation "fm" => p4Q2PZ37AHY_originalSourceNegativePart H
local notation "E3B" => p4Q2PZ37AHY_originalBoundaryHalfCubicBudget H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

/-- The true original cubic kernel remainder is nonnegative and of fourth
order at every nonnegative coupling; the full action is retained. -/
theorem p4Q2PZ37AIA_originalKernel_thirdOrder_signedInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    0 ≤ K beta A B -
        (1 - beta * S A B + (beta * S A B) ^ 2 / 2 -
          (beta * S A B) ^ 3 / 6) ∧
      K beta A B -
        (1 - beta * S A B + (beta * S A B) ^ 2 / 2 -
          (beta * S A B) ^ 3 / 6) ≤ (beta * S A B) ^ 4 / 24 := by
  have hS : 0 ≤ S A B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B
  have h := p4Q2PZ37AIA_exp_neg_quarticRemainder
    (beta * S A B) (mul_nonneg hbeta hS)
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  simpa only [neg_mul] using h

/-- Any continuous original-boundary weight times the full-action fourth power
is integrable under the unchanged finite product Haar measure. -/
theorem p4Q2PZ37AIA_originalWeightedActionFourth_integrable
    (g : Cfg → ℝ) (hg : Continuous g) (B : Cfg) :
    Integrable (fun A : Cfg => g A * (S A B) ^ 4) muH :=
  (hg.mul ((p4Q2PZ37AHP_originalFullAction_continuous H B).pow 4)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Genuine absolute-source/full-action quartic correlation. -/
def p4Q2PZ37AIA_originalAbsoluteActionFourthMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, |fCont A| * (S A B) ^ 4 ∂muH

/-- Genuine positive-source/full-action quartic correlation. -/
def p4Q2PZ37AIA_originalPositiveActionFourthMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, fp A * (S A B) ^ 4 ∂muH

/-- Genuine negative-source/full-action quartic correlation. -/
def p4Q2PZ37AIA_originalNegativeActionFourthMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, fm A * (S A B) ^ 4 ∂muH

local notation "J4abs" => p4Q2PZ37AIA_originalAbsoluteActionFourthMoment H
local notation "J4p" => p4Q2PZ37AIA_originalPositiveActionFourthMoment H
local notation "J4m" => p4Q2PZ37AIA_originalNegativeActionFourthMoment H

theorem p4Q2PZ37AIA_originalActionFourthMoments_nonneg (B : Cfg) :
    0 ≤ J4abs B ∧ 0 ≤ J4p B ∧ 0 ≤ J4m B := by
  have hS (A : Cfg) : 0 ≤ (S A B) ^ 4 :=
    pow_nonneg
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
        H 2 (by norm_num) A B) 4
  refine ⟨?_, ?_, ?_⟩
  · exact integral_nonneg (fun A => mul_nonneg (abs_nonneg _) (hS A))
  · exact integral_nonneg (fun A =>
      mul_nonneg (p4Q2PZ37AHY_originalSourceParts_nonneg H A).1 (hS A))
  · exact integral_nonneg (fun A =>
      mul_nonneg (p4Q2PZ37AHY_originalSourceParts_nonneg H A).2 (hS A))

/-- Absolute weighting is the SUM, not generally twice either signed part. -/
theorem p4Q2PZ37AIA_originalActionFourthMoments_sum (B : Cfg) :
    J4p B + J4m B = J4abs B := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  unfold p4Q2PZ37AIA_originalPositiveActionFourthMoment
    p4Q2PZ37AIA_originalNegativeActionFourthMoment
    p4Q2PZ37AIA_originalAbsoluteActionFourthMoment
  rw [← integral_add
    (p4Q2PZ37AIA_originalWeightedActionFourth_integrable H fp hp B)
    (p4Q2PZ37AIA_originalWeightedActionFourth_integrable H fm hm B)]
  apply integral_congr_ae
  filter_upwards with A
  change ((|fCont A| + fCont A) / 2) * (S A B) ^ 4 +
    ((|fCont A| - fCont A) / 2) * (S A B) ^ 4 =
      |fCont A| * (S A B) ^ 4
  ring

/-- A continuous nonnegative weight retains the right boundary in the cap. -/
theorem p4Q2PZ37AIA_originalWeightedActionFourth_le_boundaryBudget
    (g : Cfg → ℝ) (hg : Continuous g) (hg0 : ∀ A, 0 ≤ g A) (B : Cfg) :
    (∫ A : Cfg, g A * (S A B) ^ 4 ∂muH) ≤
      (CB B) ^ 4 * (∫ A : Cfg, g A ∂muH) := by
  have hgInt : Integrable g muH :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, g A * (S A B) ^ 4 ∂muH) ≤
        ∫ A : Cfg, (CB B) ^ 4 * g A ∂muH := by
      apply integral_mono
        (p4Q2PZ37AIA_originalWeightedActionFourth_integrable H g hg B)
        (hgInt.const_mul _)
      intro A
      have hPow : (S A B) ^ 4 ≤ (CB B) ^ 4 :=
        pow_le_pow_left₀
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
            H 2 (by norm_num) A B)
          (p4Q2PZ37AHY_originalFullAction_le_boundaryBudget H A B) 4
      calc
        g A * (S A B) ^ 4 ≤ g A * (CB B) ^ 4 :=
          mul_le_mul_of_nonneg_left hPow (hg0 A)
        _ = (CB B) ^ 4 * g A := mul_comm _ _
    _ = (CB B) ^ 4 * (∫ A : Cfg, g A ∂muH) := by
      rw [integral_const_mul]

/-- Each genuine source-part quartic moment uses only half the source L1 mass. -/
theorem p4Q2PZ37AIA_originalSourcePartFourthMoments_le_halfMass
    (B : Cfg) :
    J4p B ≤ (CB B) ^ 4 * (Msrc / 2) ∧
      J4m B ≤ (CB B) ^ 4 * (Msrc / 2) := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  have hP := p4Q2PZ37AIA_originalWeightedActionFourth_le_boundaryBudget H fp hp
    (fun A => (p4Q2PZ37AHY_originalSourceParts_nonneg H A).1) B
  have hM := p4Q2PZ37AIA_originalWeightedActionFourth_le_boundaryBudget H fm hm
    (fun A => (p4Q2PZ37AHY_originalSourceParts_nonneg H A).2) B
  rw [(p4Q2PZ37AHY_originalSourceParts_HaarMass H).1] at hP
  rw [(p4Q2PZ37AHY_originalSourceParts_HaarMass H).2] at hM
  exact ⟨hP, hM⟩

/-- The absolute weighted moment also has the genuine boundary-dependent cap. -/
theorem p4Q2PZ37AIA_originalAbsoluteActionFourthMoment_le_mass
    (B : Cfg) : J4abs B ≤ (CB B) ^ 4 * Msrc := by
  have h := p4Q2PZ37AIA_originalWeightedActionFourth_le_boundaryBudget H
    (fun A : Cfg => |fCont A|) (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.abs (fun A => abs_nonneg _) B
  rw [← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H] at h
  exact h


/-- Nonnegative kernel error reverses AHY's cubic source-side orientation.
Both bounds retain the actual quartic source/action correlations. -/
theorem p4Q2PZ37AIA_originalFourthOrderRemainder_weightedInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    -((beta ^ 4 / 24) * J4m B) ≤ R4 beta B ∧
      R4 beta B ≤ (beta ^ 4 / 24) * J4p B := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  have hpInt := p4Q2PZ37AIA_originalWeightedActionFourth_integrable H fp hp B
  have hmInt := p4Q2PZ37AIA_originalWeightedActionFourth_integrable H fm hm B
  have hrInt := p4Q2PZ37AIA_originalFourthOrderRemainder_integrable H beta B
  have hPoint (A : Cfg) := p4Q2PZ37AIA_real_signedNonnegativeError_interval
    (fCont A)
    (K beta A B -
      (1 - beta * S A B + (beta * S A B) ^ 2 / 2 - (beta * S A B) ^ 3 / 6))
    ((beta * S A B) ^ 4 / 24)
    (p4Q2PZ37AIA_originalKernel_thirdOrder_signedInterval H beta hbeta A B)
  constructor
  · calc
      -((beta ^ 4 / 24) * J4m B) =
          ∫ A : Cfg, -(beta ^ 4 / 24) * (fm A * (S A B) ^ 4) ∂muH := by
        rw [integral_const_mul]
        unfold p4Q2PZ37AIA_originalNegativeActionFourthMoment
        ring
      _ ≤ R4 beta B := by
        unfold p4Q2PZ37AIA_originalFourthOrderRemainder
        apply integral_mono (hmInt.const_mul _) hrInt
        intro A
        calc
          -(beta ^ 4 / 24) * (fm A * (S A B) ^ 4) =
              -((|fCont A| - fCont A) / 2) * ((beta * S A B) ^ 4 / 24) := by
            unfold p4Q2PZ37AHY_originalSourceNegativePart
            ring
          _ ≤ fCont A *
              (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2 -
                (beta * S A B) ^ 3 / 6)) := (hPoint A).1
  · calc
      R4 beta B ≤
          ∫ A : Cfg, (beta ^ 4 / 24) * (fp A * (S A B) ^ 4) ∂muH := by
        unfold p4Q2PZ37AIA_originalFourthOrderRemainder
        apply integral_mono hrInt (hpInt.const_mul _)
        intro A
        calc
          fCont A *
              (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2 -
                (beta * S A B) ^ 3 / 6)) ≤
              ((|fCont A| + fCont A) / 2) * ((beta * S A B) ^ 4 / 24) :=
            (hPoint A).2
          _ = (beta ^ 4 / 24) * (fp A * (S A B) ^ 4) := by
            unfold p4Q2PZ37AHY_originalSourcePositivePart
            ring
      _ = (beta ^ 4 / 24) * J4p B := integral_const_mul _ _

/-- An absolute-source fourth moment also bounds the actual signed error.
The sharper half-mass bound below uses each source part separately. -/
theorem p4Q2PZ37AIA_originalFourthOrderRemainder_abs_weightedBound
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |R4 beta B| ≤ (beta ^ 4 / 24) * J4abs B := by
  have h := p4Q2PZ37AIA_originalFourthOrderRemainder_weightedInterval H beta hbeta B
  have hNonneg := p4Q2PZ37AIA_originalActionFourthMoments_nonneg H B
  have hSum := p4Q2PZ37AIA_originalActionFourthMoments_sum H B
  have hc : 0 ≤ beta ^ 4 / 24 := by positivity
  have hP : (beta ^ 4 / 24) * J4p B ≤ (beta ^ 4 / 24) * J4abs B :=
    mul_le_mul_of_nonneg_left (by linarith only [hSum, hNonneg.2.2]) hc
  have hM : (beta ^ 4 / 24) * J4m B ≤ (beta ^ 4 / 24) * J4abs B :=
    mul_le_mul_of_nonneg_left (by linarith only [hSum, hNonneg.2.1]) hc
  exact abs_le.mpr ⟨by linarith only [h.1, hM], h.2.trans hP⟩

/-- Actual right-boundary quartic budget using the equal UNWEIGHTED
source-part masses. The original signed source is unchanged. -/
def p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget (beta : ℝ) (B : Cfg) : ℝ :=
  ((beta * CB B) ^ 4 / 48) * Msrc

local notation "E4B" => p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget H

theorem p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_nonneg
    (beta : ℝ) (B : Cfg) : 0 ≤ E4B beta B := by
  have hPow : 0 ≤ (beta * CB B) ^ 4 := by positivity
  exact mul_nonneg (div_nonneg hPow (by norm_num))
    (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)

theorem p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_zero
    (B : Cfg) : E4B 0 B = 0 := by
  simp [p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget]

/-- Exact budget relation. The centers differ, and no unconditional
decrease of the error width is inferred when beta*C_B exceeds four. -/
theorem p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_eq_scaledCubic
    (beta : ℝ) (B : Cfg) :
    E4B beta B = (beta * CB B / 4) * E3B beta B := by
  unfold p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget
    p4Q2PZ37AHY_originalBoundaryHalfCubicBudget
  ring

theorem p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_le_global
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    E4B beta B ≤ ((beta * Cslab) ^ 4 / 48) * Msrc := by
  have hPow : (beta * CB B) ^ 4 ≤ (beta * Cslab) ^ 4 :=
    pow_le_pow_left₀
      (mul_nonneg hbeta (p4Q2PZ37AHY_originalBoundaryActionBudget_nonneg H B))
      (mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHY_originalBoundaryActionBudget_le_global H B) hbeta) 4
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hPow (by norm_num))
    (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)

/-- Both source-part estimates use half the mass, with the correct
opposite sides of the signed fourth-order remainder. -/
theorem p4Q2PZ37AIA_originalFourthOrderRemainder_abs_boundaryHalfBound
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |R4 beta B| ≤ E4B beta B := by
  have h := p4Q2PZ37AIA_originalFourthOrderRemainder_weightedInterval H beta hbeta B
  have hParts := p4Q2PZ37AIA_originalSourcePartFourthMoments_le_halfMass H B
  have hc : 0 ≤ beta ^ 4 / 24 := by positivity
  have hP : (beta ^ 4 / 24) * J4p B ≤ E4B beta B := by
    calc
      (beta ^ 4 / 24) * J4p B ≤
          (beta ^ 4 / 24) * ((CB B) ^ 4 * (Msrc / 2)) :=
        mul_le_mul_of_nonneg_left hParts.1 hc
      _ = E4B beta B := by
        unfold p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget
        ring
  have hM : (beta ^ 4 / 24) * J4m B ≤ E4B beta B := by
    calc
      (beta ^ 4 / 24) * J4m B ≤
          (beta ^ 4 / 24) * ((CB B) ^ 4 * (Msrc / 2)) :=
        mul_le_mul_of_nonneg_left hParts.2 hc
      _ = E4B beta B := by
        unfold p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget
        ring
  exact abs_le.mpr ⟨by linarith only [h.1, hM], h.2.trans hP⟩

/-- Count-only error bound, preserving AHY's original boundary cap. -/
theorem p4Q2PZ37AIA_originalFourthOrderRemainder_abs_halfCount
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |R4 beta B| ≤ ((beta * CB B) ^ 4 / 96) * pH := by
  have hCoef : 0 ≤ (beta * CB B) ^ 4 / 48 := by positivity
  calc
    |R4 beta B| ≤ E4B beta B :=
      p4Q2PZ37AIA_originalFourthOrderRemainder_abs_boundaryHalfBound H beta hbeta B
    _ ≤ ((beta * CB B) ^ 4 / 48) * (pH / 2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H) hCoef
    _ = ((beta * CB B) ^ 4 / 96) * pH := by ring

/-- Asymmetric enclosure around the exact cubic center, retaining both
different quartic Haar correlations. -/
theorem p4Q2PZ37AIA_originalTransfer_weightedQuarticInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    P3 beta B - (beta ^ 4 / 24) * J4m B ≤ T beta f0 B ∧
      T beta f0 B ≤ P3 beta B + (beta ^ 4 / 24) * J4p B := by
  have h := p4Q2PZ37AIA_originalFourthOrderRemainder_weightedInterval H beta hbeta B
  rw [p4Q2PZ37AIA_originalFourthOrderRemainder_eq_sub H beta B] at h
  constructor <;> linarith only [h.1, h.2]

theorem p4Q2PZ37AIA_originalTransfer_boundaryHalfQuarticInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    P3 beta B - E4B beta B ≤ T beta f0 B ∧
      T beta f0 B ≤ P3 beta B + E4B beta B := by
  have h := abs_le.mp
    (p4Q2PZ37AIA_originalFourthOrderRemainder_abs_boundaryHalfBound H beta hbeta B)
  rw [p4Q2PZ37AIA_originalFourthOrderRemainder_eq_sub H beta B] at h
  constructor <;> linarith only [h.1, h.2]

/-- Completing the square retains an additional nonpositive correction.
The AHZ lower bound is scaled only by a nonnegative coefficient. -/
theorem p4Q2PZ37AIA_originalCubicApproximation_le_completedSquare
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    P3 beta B ≤ -(beta * Vsrc) / 2 -
      (beta * Vsrc / 8) * (beta * (3 * pH + W B) - 2) ^ 2 := by
  have hFloor := p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_varianceFloor H B
  have hCoef : 0 ≤ beta ^ 3 / 6 :=
    div_nonneg (pow_nonneg hbeta 3) (by norm_num)
  have hScaled := mul_le_mul_of_nonneg_left hFloor hCoef
  unfold p4Q2PZ37AIA_originalCubicApproximation
  calc
    Q2 beta B - (beta ^ 3 / 6) * M3full B ≤
        Q2 beta B - (beta ^ 3 / 6) *
          ((3 / 4 : ℝ) * (3 * pH + W B) ^ 2 * Vsrc) :=
      sub_le_sub_left hScaled (Q2 beta B)
    _ = -(beta * Vsrc) / 2 -
        (beta * Vsrc / 8) * (beta * (3 * pH + W B) - 2) ^ 2 := by
      unfold p4Q2PZ37AHX_originalQuadraticApproximation
      ring

/-- A negative half-variance bound for the cubic approximation, valid for
all nonnegative couplings, with no coupling-budget smallness condition. -/
theorem p4Q2PZ37AIA_originalCubicApproximation_le_negativeHalfVariance
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    P3 beta B ≤ -(beta * Vsrc) / 2 := by
  have hv : 0 ≤ Vsrc :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le
  have hCorrection :
      0 ≤ (beta * Vsrc / 8) * (beta * (3 * pH + W B) - 2) ^ 2 :=
    mul_nonneg
      (div_nonneg (mul_nonneg hbeta hv) (by norm_num))
      (sq_nonneg _)
  exact
    (p4Q2PZ37AIA_originalCubicApproximation_le_completedSquare H beta hbeta B).trans
      (sub_le_self _ hCorrection)

/-- The cubic approximation is strictly negative at every positive beta.
An actual transfer sign still requires control of the quartic remainder. -/
theorem p4Q2PZ37AIA_originalCubicApproximation_neg
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) : P3 beta B < 0 := by
  have hv : 0 < Vsrc :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hProduct : 0 < beta * Vsrc := mul_pos hbeta hv
  have hHalf : -(beta * Vsrc) / 2 < 0 := by
    linarith only [hProduct]
  exact
    (p4Q2PZ37AIA_originalCubicApproximation_le_negativeHalfVariance
      H beta hbeta.le B).trans_lt hHalf

/-- This particular cubic enclosure has no positive lower endpoint.
It does not assert that the actual transfer itself cannot be positive. -/
theorem p4Q2PZ37AIA_originalCubicQuarticLowerEndpoint_nonpos
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    P3 beta B - (beta ^ 4 / 24) * J4m B ≤ 0 := by
  have hCenter :=
    p4Q2PZ37AIA_originalCubicApproximation_le_negativeHalfVariance H beta hbeta B
  have hProduct : 0 ≤ beta * Vsrc :=
    mul_nonneg hbeta (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le
  have hError : 0 ≤ (beta ^ 4 / 24) * J4m B :=
    mul_nonneg (by positivity) (p4Q2PZ37AIA_originalActionFourthMoments_nonneg H B).2.2
  linarith only [hCenter, hProduct, hError]

/-- Actual negative-transfer certificate with the full cubic coefficient
and the genuine positive-source quartic correlation retained. -/
theorem p4Q2PZ37AIA_originalTransfer_negative_of_weightedQuarticMargin
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hMargin : (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc) +
      (beta ^ 4 / 24) * J4p B <
        beta * Vsrc + (beta ^ 3 / 6) * M3full B) :
    T beta f0 B < 0 := by
  have h := (p4Q2PZ37AIA_originalTransfer_weightedQuarticInterval H beta hbeta B).2
  unfold p4Q2PZ37AIA_originalCubicApproximation
    p4Q2PZ37AHX_originalQuadraticApproximation at h
  linarith only [h, hMargin]

/-- The completed-square bound reduces an actual negative-transfer
certificate to a quartic error smaller than half the original variance term. -/
theorem p4Q2PZ37AIA_originalTransfer_negative_of_halfVarianceQuarticMargin
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hMargin : E4B beta B < beta * Vsrc / 2) :
    T beta f0 B < 0 := by
  have hInterval :=
    (p4Q2PZ37AIA_originalTransfer_boundaryHalfQuarticInterval H beta hbeta B).2
  have hCenter :=
    p4Q2PZ37AIA_originalCubicApproximation_le_negativeHalfVariance H beta hbeta B
  linarith only [hInterval, hCenter, hMargin]

/-- Explicit finite-lattice scaled margin. Positivity of beta is used to
multiply a genuine quantitative inequality, not to assume a transfer sign. -/
theorem p4Q2PZ37AIA_originalTransfer_negative_of_scaledQuarticMargin
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg)
    (hMargin : beta ^ 3 * (CB B) ^ 4 * Msrc < 24 * Vsrc) :
    T beta f0 B < 0 := by
  have hScaled := mul_lt_mul_of_pos_left hMargin hbeta
  have hBudget : E4B beta B < beta * Vsrc / 2 := by
    unfold p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget
    nlinarith only [hScaled]
  exact p4Q2PZ37AIA_originalTransfer_negative_of_halfVarianceQuarticMargin
    H beta hbeta.le B hBudget

/-- Genuine fixed-coupling enclosure; no smallness assumption is imposed
on beta0 to state the interval. Its numerical endpoints remain unevaluated. -/
theorem p4Q2PZ37AIA_originalFixedTransfer_boundaryHalfQuarticInterval
    (B : Cfg) :
    P3 beta0 B - E4B beta0 B ≤ T beta0 f0 B ∧
      T beta0 f0 B ≤ P3 beta0 B + E4B beta0 B :=
  p4Q2PZ37AIA_originalTransfer_boundaryHalfQuarticInterval
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B

theorem p4Q2PZ37AIA_originalFixedTransfer_negative_of_weightedQuarticMargin
    (B : Cfg)
    (hMargin : (beta0 ^ 2 / 2) * ((3 * pH + W B) * Vsrc) +
      (beta0 ^ 4 / 24) * J4p B <
        beta0 * Vsrc + (beta0 ^ 3 / 6) * M3full B) :
    T beta0 f0 B < 0 :=
  p4Q2PZ37AIA_originalTransfer_negative_of_weightedQuarticMargin
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B hMargin

/-- Fixed beta0 still requires the displayed quantitative margin; the
present theorem does not provide or assume a numerical witness for it. -/
theorem p4Q2PZ37AIA_originalFixedTransfer_negative_of_scaledQuarticMargin
    (B : Cfg)
    (hMargin : beta0 ^ 3 * (CB B) ^ 4 * Msrc < 24 * Vsrc) :
    T beta0 f0 B < 0 :=
  p4Q2PZ37AIA_originalTransfer_negative_of_scaledQuarticMargin
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos B hMargin

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIA_exp_neg_quarticRemainder
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIA_real_signedNonnegativeError_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFourthOrderRemainder_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFourthOrderRemainder_eq_third_add
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFourthOrderRemainder_eq_sub
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalTransfer_thirdOrder_expansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalTransfer_thirdOrder_expansion_exactCubic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalKernel_thirdOrder_signedInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalWeightedActionFourth_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalActionFourthMoments_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalActionFourthMoments_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalWeightedActionFourth_le_boundaryBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalSourcePartFourthMoments_le_halfMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalAbsoluteActionFourthMoment_le_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFourthOrderRemainder_weightedInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFourthOrderRemainder_abs_weightedBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_eq_scaledCubic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_le_global
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFourthOrderRemainder_abs_boundaryHalfBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFourthOrderRemainder_abs_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalTransfer_weightedQuarticInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalTransfer_boundaryHalfQuarticInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalCubicApproximation_le_completedSquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalCubicApproximation_le_negativeHalfVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalCubicApproximation_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalCubicQuarticLowerEndpoint_nonpos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalTransfer_negative_of_weightedQuarticMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalTransfer_negative_of_halfVarianceQuarticMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalTransfer_negative_of_scaledQuarticMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFixedTransfer_boundaryHalfQuarticInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFixedTransfer_negative_of_weightedQuarticMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIA_originalFixedTransfer_negative_of_scaledQuarticMargin


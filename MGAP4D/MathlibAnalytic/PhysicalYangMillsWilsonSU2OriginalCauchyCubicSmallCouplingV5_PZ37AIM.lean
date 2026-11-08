import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExplicitSmallCouplingFullNegativeRegionV5_PZ37AIL
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalWeightedCubicRemainderV5_PZ37AHY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuarticBudgetObstructionV5_PZ37AIB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIM — actual Haar Cauchy bound and larger cubic small-coupling interval

Keep the ORIGINAL complete Wilson slab action, both spatial halfweights,
signed ZW physical L2 source, actual continuous representative, normalized
spatial product Haar, and the SAME AIG negative margin and region.

On that probability Haar, M_H^2 <= V_H. Put u_H=(1/384)^n_H. AIK's
variance floor is v_H=(3*p_H/8)^2*u_H^4, so Cauchy implies
  (3*p_H/8)*u_H^2*M_H <= V_H.
Define theta_H=u_H/(16*p_H+1)>0. AHX's exact quadratic correction
and AHY's actual half cubic error are then bounded by 5*beta*V_H/32
and beta*V_H/18. Their sum is less than beta*V_H/4. Thus the ORIGINAL
transfer satisfies T_beta f0(B)<-3*beta*V_H/4 for EVERY boundary B
and EVERY 0<beta<=theta_H, including the explicit endpoint.

The SAME full-margin negative region is the whole original space with
true Haar mass one. The original identity is a specified negative boundary.
The old AIL cutoff is STRICTLY smaller. The actual count p_H>=24 gives
theta_H<=1/385<beta0: exclusion from this certificate's interval, not
a claim about the transfer sign at beta0 or outside the interval.

No source/partition integral remains in theta_H; no plaquette independence
is assumed. No volume-uniform interval, coercivity, Hamiltonian gap or
continuum gap is inferred. Existing files, hypotheses, roots and pins remain.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIM_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIM_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIM_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIM_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIM_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nH" => Nat.card Link
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "v" => p4Q2PZ37AIK_elementarySourceVarianceFloor H
local notation "tau" => p4Q2PZ37AIL_elementarySmallCoupling H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cslab" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "EB" => p4Q2PZ37AHY_originalBoundaryHalfCubicBudget H
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H
local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H
local notation "T" => decomposableOneSliceTransferIntegral H 2

local instance p4Q2PZ37AIM_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Cauchy's inequality on the ORIGINAL normalized Haar probability.
Use the authentic continuous representative and the integral of a square;
no pointwise representative of an L2 equivalence class is invented. -/
theorem p4Q2PZ37AIM_originalSource_L1_sq_le_secondMoment :
    Msrc ^ 2 ≤ Vsrc := by
  have hf : Continuous (fun A : Cfg => fCont A) := fCont.continuous
  have hAbs : Integrable (fun A : Cfg => |fCont A|) muH :=
    hf.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSq : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNonneg : 0 ≤ ∫ A : Cfg, (|fCont A| - Msrc) ^ 2 ∂muH :=
    integral_nonneg (fun A => sq_nonneg (|fCont A| - Msrc))
  have hExpand :
      (∫ A : Cfg, (|fCont A| - Msrc) ^ 2 ∂muH) = Vsrc - Msrc ^ 2 := by
    calc
      (∫ A : Cfg, (|fCont A| - Msrc) ^ 2 ∂muH) =
          ∫ A : Cfg, (fCont A) ^ 2 - (2 * Msrc) * |fCont A| + Msrc ^ 2 ∂muH := by
        apply integral_congr_ae
        filter_upwards with A
        nlinarith only [sq_abs (fCont A)]
      _ = (∫ A : Cfg, (fCont A) ^ 2 ∂muH) -
          (2 * Msrc) * (∫ A : Cfg, |fCont A| ∂muH) + Msrc ^ 2 := by
        rw [integral_add (hSq.sub (hAbs.const_mul _)) (integrable_const _),
          integral_sub hSq (hAbs.const_mul _), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      _ = Vsrc - Msrc ^ 2 := by
        rw [← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H]
        change Vsrc - (2 * Msrc) * Msrc + Msrc ^ 2 = Vsrc - Msrc ^ 2
        ring
  linarith only [hNonneg, hExpand]

/-- The elementary factor comes from the SAME original identity-box Haar floor. -/
def p4Q2PZ37AIM_identityHaarRoot : ℝ :=
  (1 / 384 : ℝ) ^ nH

local notation "u" => p4Q2PZ37AIM_identityHaarRoot H

theorem p4Q2PZ37AIM_identityHaarRoot_pos : 0 < u := by
  unfold p4Q2PZ37AIM_identityHaarRoot
  positivity

theorem p4Q2PZ37AIM_identityHaarRoot_le_one : u ≤ 1 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 384)
    (by norm_num : (1 / 384 : ℝ) ≤ 1) nH
  simpa only [p4Q2PZ37AIM_identityHaarRoot, one_pow] using h

/-- Exact evaluation of the old AIK floor, not a replacement variance. -/
theorem p4Q2PZ37AIM_elementaryVariance_eq_root :
    v = (3 * pH / 8) ^ 2 * u ^ 4 := by
  unfold p4Q2PZ37AIK_elementarySourceVarianceFloor p4Q2PZ37AIM_identityHaarRoot
  rw [← pow_mul, Nat.mul_comm nH 4]

/-- Cauchy combines the original actual L1 mass and actual second moment
with the existing elementary lower floor. No unproved covariance is used. -/
theorem p4Q2PZ37AIM_originalSource_rootScaledMass_le_variance :
    (3 * pH / 8) * u ^ 2 * Msrc ≤ Vsrc := by
  have hCauchy := p4Q2PZ37AIM_originalSource_L1_sq_le_secondMoment H
  have hFloor := p4Q2PZ37AIK_elementarySourceVarianceFloor_le_original H
  rw [p4Q2PZ37AIM_elementaryVariance_eq_root] at hFloor
  nlinarith only [hCauchy, hFloor, sq_nonneg ((3 * pH / 8) * u ^ 2 - Msrc)]

/-- A larger entirely elementary finite-volume cutoff. -/
def p4Q2PZ37AIM_elementaryCubicSmallCoupling : ℝ :=
  u / (16 * pH + 1)

local notation "theta" => p4Q2PZ37AIM_elementaryCubicSmallCoupling H

theorem p4Q2PZ37AIM_elementaryCubicSmallCoupling_pos : 0 < theta := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hu := p4Q2PZ37AIM_identityHaarRoot_pos H
  unfold p4Q2PZ37AIM_elementaryCubicSmallCoupling
  positivity

/-- This includes the minimal original spatial period H=0. -/
theorem p4Q2PZ37AIM_plaquetteCount_ge_twentyFour : (24 : ℝ) ≤ pH := by
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  have hh : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hPow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : (1 : ℝ) ≤ (H : ℝ) + 1) 3
  rw [one_pow] at hPow
  nlinarith only [hPow]

/-- Strict enlargement preserves every old AIL instance and certifies
additional positive couplings; it does not change the old definition. -/
theorem p4Q2PZ37AIM_oldSmallCoupling_lt_cubic : tau < theta := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hp24 := p4Q2PZ37AIM_plaquetteCount_ge_twentyFour H
  have hp1 : (1 : ℝ) ≤ pH := by linarith only [hp24]
  have hu := p4Q2PZ37AIM_identityHaarRoot_pos H
  have hu1 := p4Q2PZ37AIM_identityHaarRoot_le_one H
  have hu3 : u ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hu.le hu1 3
  have hu4 : u ^ 4 ≤ u := by
    have h := mul_le_mul_of_nonneg_left hu3 hu.le
    nlinarith only [h]
  have hp23 : pH ^ 2 ≤ pH ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hp1 (sq_nonneg pH)
    nlinarith only [h]
  have hCoeff : (3 * pH / 8) ^ 2 * (16 * pH + 1) < 16 * pH ^ 3 + 1 := by
    nlinarith only [hp23, sq_nonneg pH]
  have hScaled := mul_lt_mul_of_pos_right hCoeff hu
  have hFloor : v ≤ (3 * pH / 8) ^ 2 * u := by
    rw [p4Q2PZ37AIM_elementaryVariance_eq_root]
    exact mul_le_mul_of_nonneg_left hu4 (sq_nonneg _)
  have hDenOld : 0 < 16 * pH ^ 3 + 1 := by positivity
  have hDenNew : 0 < 16 * pH + 1 := by positivity
  calc
    tau = v / (16 * pH ^ 3 + 1) := rfl
    _ ≤ ((3 * pH / 8) ^ 2 * u) / (16 * pH ^ 3 + 1) :=
      div_le_div_of_nonneg_right hFloor hDenOld.le
    _ < u / (16 * pH + 1) := (div_lt_div_iff₀ hDenOld hDenNew).mpr (by
      nlinarith only [hScaled])
    _ = theta := rfl

/-- An upper bound on this certificate's endpoint, not on actual signs. -/
theorem p4Q2PZ37AIM_elementaryCubicSmallCoupling_le_oneDiv385 :
    theta ≤ (1 / 385 : ℝ) := by
  have hp := p4Q2PZ37AIM_plaquetteCount_ge_twentyFour H
  have hDen : 0 < 16 * pH + 1 := by linarith only [hp]
  unfold p4Q2PZ37AIM_elementaryCubicSmallCoupling
  calc
    u / (16 * pH + 1) ≤ 1 / (16 * pH + 1) :=
      div_le_div_of_nonneg_right
        (p4Q2PZ37AIM_identityHaarRoot_le_one H) hDen.le
    _ ≤ (1 / 385 : ℝ) := (div_le_div_iff₀ hDen (by norm_num)).mpr (by
      nlinarith only [hp])

/-- The ORIGINAL fixed beta0 lies strictly outside the new interval
for EVERY H. Nothing here determines its transfer sign. -/
theorem p4Q2PZ37AIM_elementaryCubicSmallCoupling_lt_fixedCoupling :
    theta < p4Q2PZ37ADC_fixedCoupling := by
  calc
    theta ≤ (1 / 385 : ℝ) :=
      p4Q2PZ37AIM_elementaryCubicSmallCoupling_le_oneDiv385 H
    _ < (1 / 192 : ℝ) := by norm_num
    _ ≤ p4Q2PZ37ADC_fixedCoupling := p4Q2PZ37AIB_fixedCoupling_ge_oneDiv192

/-- The denominator's +1 retains strict slack at the CLOSED endpoint. -/
theorem p4Q2PZ37AIM_scaledCoupling_lt_root
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) :
    16 * beta * pH < u := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hDen : 0 < 16 * pH + 1 := by positivity
  have hProduct : beta * (16 * pH + 1) ≤ u :=
    (le_div_iff₀ hDen).mp hSmall
  nlinarith only [hProduct, hbeta]

/-- Bound AHX's exact second-order correction uniformly in every original
boundary, retaining the original spatial Wilson contribution W(B). -/
theorem p4Q2PZ37AIM_originalQuadraticCorrection_lt_fiveThirtySeconds
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) (B : Cfg) :
    (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc) < 5 * beta * Vsrc / 32 := by
  have hV := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hW : W B ≤ 2 * pH :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H 2 (by norm_num) B
  have hWScaled := mul_le_mul_of_nonneg_right hW
    (mul_nonneg (sq_nonneg beta) hV.le)
  have hBP : 16 * beta * pH < 1 :=
    (p4Q2PZ37AIM_scaledCoupling_lt_root H beta hbeta hSmall).trans_le
      (p4Q2PZ37AIM_identityHaarRoot_le_one H)
  have hScaled := mul_lt_mul_of_pos_right hBP (mul_pos hbeta hV)
  nlinarith only [hWScaled, hScaled]

/-- The cubic remainder is controlled by the SAME genuine source moments.
Cauchy removes the L1 integral from the cutoff, not from the actual model. -/
theorem p4Q2PZ37AIM_originalHalfCubicBudget_le_eighteenthVariance
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) (B : Cfg) :
    EB beta B ≤ beta * Vsrc / 18 := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hM := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).1
  have hRoot := p4Q2PZ37AIM_scaledCoupling_lt_root H beta hbeta hSmall
  have hSquare : (16 * beta * pH) ^ 2 ≤ u ^ 2 :=
    pow_le_pow_left₀ (by positivity) hRoot.le 2
  have hSquareScaled := mul_le_mul_of_nonneg_right hSquare
    (show 0 ≤ beta * pH * Msrc by positivity)
  have hVarianceScaled := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIM_originalSource_rootScaledMass_le_variance H) hbeta.le
  have hBudget : EB beta B ≤ (16 / 3 : ℝ) * beta ^ 3 * pH ^ 3 * Msrc := by
    calc
      EB beta B ≤ p4Q2PZ37AHX_originalCubicBudget H beta / 2 :=
        p4Q2PZ37AHY_originalBoundaryHalfCubicBudget_le_halfAHX H beta hbeta.le B
      _ = (16 / 3 : ℝ) * beta ^ 3 * pH ^ 3 * Msrc := by
        unfold p4Q2PZ37AHX_originalCubicBudget
        rw [p4Q2PZ37AIL_originalGlobalActionBudget_eq_fourCount]
        ring
  nlinarith only [hSquareScaled, hVarianceScaled, hBudget]

/-- Bound the actual ORIGINAL physical transfer, after controlling the
difference from the exact quadratic approximation on true Haar. -/
theorem p4Q2PZ37AIM_originalTransfer_lt_negThreeQuarterVariance
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) (B : Cfg) :
    T beta f0 B < -(3 * beta * Vsrc / 4) := by
  have hUpper :=
    (p4Q2PZ37AHY_originalTransfer_boundaryHalfCubicInterval H beta hbeta.le B).2
  rw [p4Q2PZ37AHX_originalQuadraticApproximation] at hUpper
  have hQuadratic :=
    p4Q2PZ37AIM_originalQuadraticCorrection_lt_fiveThirtySeconds H beta hbeta hSmall B
  have hCubic :=
    p4Q2PZ37AIM_originalHalfCubicBudget_le_eighteenthVariance H beta hbeta hSmall B
  have hPositive : 0 < beta * Vsrc :=
    mul_pos hbeta (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  linarith only [hUpper, hQuadratic, hCubic, hPositive]

theorem p4Q2PZ37AIM_originalTransfer_lt_negThreeQuarterElementary
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) (B : Cfg) :
    T beta f0 B < -(3 * beta * v / 4) := by
  have h := p4Q2PZ37AIM_originalTransfer_lt_negThreeQuarterVariance
    H beta hbeta hSmall B
  have hFloor := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIK_elementarySourceVarianceFloor_le_original H) hbeta.le
  linarith only [h, hFloor]

/-- Keep the ORIGINAL AIG margin; it is not replaced by the new cutoff. -/
theorem p4Q2PZ37AIM_originalTransfer_below_threeHalfMargin
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) (B : Cfg) :
    T beta f0 B < -(3 * margin beta / 2) := by
  have h := p4Q2PZ37AIM_originalTransfer_lt_negThreeQuarterVariance
    H beta hbeta hSmall B
  have hm := p4Q2PZ37AIL_originalNegativeMargin_le_halfVariance H beta hbeta.le
  linarith only [h, hm]

theorem p4Q2PZ37AIM_originalFullNegativeRegion_eq_univ
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) :
    Region beta = Set.univ := by
  ext B
  simp only [p4Q2PZ37AIG_originalNegativeTransferRegion, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  have h := p4Q2PZ37AIM_originalTransfer_below_threeHalfMargin H beta hbeta hSmall B
  have hm := p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta
  linarith only [h, hm]

theorem p4Q2PZ37AIM_originalFullNegativeRegion_measure_one
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) :
    muH (Region beta) = 1 := by
  rw [p4Q2PZ37AIM_originalFullNegativeRegion_eq_univ H beta hbeta hSmall]
  exact measure_univ

theorem p4Q2PZ37AIM_originalFullNegativeRegion_realMeasure_one
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) :
    Measure.real muH (Region beta) = 1 := by
  rw [p4Q2PZ37AIM_originalFullNegativeRegion_eq_univ H beta hbeta hSmall]
  exact probReal_univ

/-- The already defined actual identity is a specified negative boundary
throughout the strictly enlarged elementary interval. -/
theorem p4Q2PZ37AIM_originalIdentityTransfer_below_threeHalfMargin
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) :
    T beta f0 (p4Q2PZ37AHN_identity H) < -(3 * margin beta / 2) :=
  p4Q2PZ37AIM_originalTransfer_below_threeHalfMargin
    H beta hbeta hSmall (p4Q2PZ37AHN_identity H)

theorem p4Q2PZ37AIM_originalTransfer_negative
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) (B : Cfg) :
    T beta f0 B < 0 := by
  have h := p4Q2PZ37AIM_originalTransfer_lt_negThreeQuarterElementary
    H beta hbeta hSmall B
  have hv := p4Q2PZ37AIK_elementarySourceVarianceFloor_pos H
  have hPos : 0 < 3 * beta * v / 4 := by positivity
  linarith only [h, hPos]

/-- Positive or zero boundaries are excluded on this certified interval;
the theorem makes no assertion about its complement. -/
theorem p4Q2PZ37AIM_originalNonnegativeRegion_eq_empty
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ theta) :
    {B : Cfg | 0 ≤ T beta f0 B} = ∅ := by
  ext B
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact not_le.mpr (p4Q2PZ37AIM_originalTransfer_negative H beta hbeta hSmall B)

/-- A concrete endpoint beyond AIL, below beta0, with every original
boundary strictly negative and the original full-margin Haar mass one. -/
theorem p4Q2PZ37AIM_explicitEndpoint_certificate :
    0 < theta ∧ tau < theta ∧ theta < p4Q2PZ37ADC_fixedCoupling ∧
      (∀ B : Cfg, T theta f0 B < -(3 * margin theta / 2)) ∧
      Measure.real muH (Region theta) = 1 := by
  have hTheta := p4Q2PZ37AIM_elementaryCubicSmallCoupling_pos H
  exact ⟨hTheta, p4Q2PZ37AIM_oldSmallCoupling_lt_cubic H,
    p4Q2PZ37AIM_elementaryCubicSmallCoupling_lt_fixedCoupling H,
    fun B => p4Q2PZ37AIM_originalTransfer_below_threeHalfMargin
      H theta hTheta le_rfl B,
    p4Q2PZ37AIM_originalFullNegativeRegion_realMeasure_one H theta hTheta le_rfl⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalSource_L1_sq_le_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_identityHaarRoot
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_identityHaarRoot_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_identityHaarRoot_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_elementaryVariance_eq_root
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalSource_rootScaledMass_le_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_elementaryCubicSmallCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_elementaryCubicSmallCoupling_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_plaquetteCount_ge_twentyFour
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_oldSmallCoupling_lt_cubic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_elementaryCubicSmallCoupling_le_oneDiv385
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_elementaryCubicSmallCoupling_lt_fixedCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_scaledCoupling_lt_root
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalQuadraticCorrection_lt_fiveThirtySeconds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalHalfCubicBudget_le_eighteenthVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalTransfer_lt_negThreeQuarterVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalTransfer_lt_negThreeQuarterElementary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalTransfer_below_threeHalfMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalFullNegativeRegion_eq_univ
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalFullNegativeRegion_measure_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalFullNegativeRegion_realMeasure_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalIdentityTransfer_below_threeHalfMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalTransfer_negative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_originalNonnegativeRegion_eq_empty
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIM_explicitEndpoint_certificate

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCauchyCubicSmallCouplingV5_PZ37AIM
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllLinkTemporalHaarRestrictionV5_PZ37ABP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalEvenTorusCenterSourceOddV5_PZ37AHW2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIN — specified negative boundary at every positive coupling

Keep the ORIGINAL complete SU(2) Wilson slab action, both spatial
halfweights, signed ZW physical L2 source, existing continuous representative,
and genuine normalized spatial product Haar. All existing assumptions,
theorems, roots, fixed Lean/mathlib pins, and resource budgets remain.

Sum ABP's exact actual-plaquette temporal convolution over the original
plaquettes. The crossing integral of the full centered source is exactly
Zcross(beta)*r(beta)^4*f_H(B). Restore the original LEFT halfweight by the
identity W_H/2=f_H+p_H/2, and retain AIE's signed scalar quadratic bound.
AIF's existing representative bridge and RIGHT halfweight cancellation
then give an upper envelope for the original physical transfer.

The actual identity on every original spatial link has negative transfer
for EVERY beta>0, including the unchanged beta0, with the elementary floor
  eta_H(beta) = (p_H/2)*exp(-beta*p_H/2)*exp(-2*beta*n_H)
               *(beta*exp(-2*beta)/4)^4 > 0.
No unevaluated integral occurs in this floor. There is no small-coupling
assumption and no independence assumption about overlapping plaquettes.

The retained quadratic term also gives strict transfer negativity wherever
the original continuous source is nonpositive, including its zero set.
AHW/AHW2's actual Haar-preserving source-odd cochain twist shows that this
source-nonpositive set has Haar mass at least 1/2. Hence the ZERO-threshold
transfer-negative set has true Haar mass at least 1/2 for every beta>0.
AIG's original full-margin negative region and its earlier bounds remain
unchanged; no comparison with that older margin is inserted.

No positive transfer boundary, both-sign transfer shell, volume-uniform
positive amplitude, coercivity, Hamiltonian gap, or continuum mass gap is
inferred. This appended leaf does not alter any earlier artifact.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIN_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIN_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIN_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIN_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIN_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nH" => Nat.card Link
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "KC" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "r" => p4Q2PZ37ABN_originalTemporalWilsonCoefficient
local notation "identityH" => p4Q2PZ37AHN_identity H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AIN_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

local instance p4Q2PZ37AIN_linkFintype : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AIN_plaquetteFintype : Fintype Plaq :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

/-- The two existing one-link partition names denote the same original
SU(2) Wilson Boltzmann integral on the same normalized Haar measure. -/
theorem p4Q2PZ37AIN_originalSingleLinkPartition_eq_temporalMass
    (beta : ℝ) :
    p4Q2PZ37AIF_originalSingleLinkPartition beta =
      p4Q2PZ37ABN_originalTemporalWilsonMass beta := rfl

theorem p4Q2PZ37AIN_originalCrossingPartition_eq_temporalMassPower
    (beta : ℝ) :
    Zcross beta = (p4Q2PZ37ABN_originalTemporalWilsonMass beta) ^ Fintype.card Link := by
  simp only [p4Q2PZ37AIF_originalCrossingPartition,
    p4Q2PZ37AIN_originalSingleLinkPartition_eq_temporalMass,
    Fintype.card_eq_nat_card]

/-- Sum of the centered half-energy of every actual original plaquette. -/
theorem p4Q2PZ37AIN_originalSource_eq_centeredPlaquetteSum
    (A : Cfg) :
    fCont A = ∑ p : Plaq, (p4Q2LO_originalLocalPlaquetteContinuous H p A - 1) / 2 := by
  rw [p4Q2PZ37AHR_originalSource_eq_negHalfTrace H A]
  unfold p4Q2PW2_originalAllPlaquetteRealTrace
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_univ]
  · intro p _hp
    rw [p4Q2LO_originalLocalPlaquetteContinuous_apply]
    unfold p4Q2PV_originalPlaquetteRealCharacter
    ring

/-- Undo only the positive temporal normalizer in ABP's already proved
actual all-link plaquette convolution. No physical transfer is normalized. -/
theorem p4Q2PZ37AIN_originalCrossingPlaquette_convolution
    (beta : ℝ) (p : Plaq) (B : Cfg) :
    (∫ A : Cfg, KC beta A B *
      ((p4Q2LO_originalLocalPlaquetteContinuous H p A - 1) / 2) ∂muH) =
        Zcross beta * r beta ^ 4 *
          ((p4Q2LO_originalLocalPlaquetteContinuous H p B - 1) / 2) := by
  have h := p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_eq_coefficient_pow_mul
    H beta p B
  unfold p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer at h
  have hMass :
      (p4Q2PZ37ABN_originalTemporalWilsonMass beta) ^ Fintype.card Link ≠ 0 :=
    ne_of_gt (pow_pos (p4Q2PZ37ABN_originalTemporalWilsonMass_pos beta) _)
  have hIntegral := (div_eq_iff hMass).mp h
  rw [p4Q2PZ37AIN_originalCrossingPartition_eq_temporalMassPower H beta]
  nlinarith only [hIntegral]

/-- Exact full-source convolution follows from a finite SUM of the actual
plaquette formulas, without any joint independence premise. -/
theorem p4Q2PZ37AIN_originalCrossingSource_convolution
    (beta : ℝ) (B : Cfg) :
    (∫ A : Cfg, KC beta A B * fCont A ∂muH) =
      Zcross beta * r beta ^ 4 * fCont B := by
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    (continuous_id : Continuous (fun A : Cfg => A)).prodMk
      (continuous_const : Continuous (fun _ : Cfg => B))
  have hJoint : Continuous (fun q : Cfg × Cfg => KC beta q.1 q.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous H 2 beta
  have hk := Continuous.comp'
    (f := fun A : Cfg => (A, B))
    (g := fun q : Cfg × Cfg => KC beta q.1 q.2) hJoint hPair
  change Continuous (fun A : Cfg => KC beta A B) at hk
  have hEach (p : Plaq) : Integrable (fun A : Cfg => KC beta A B *
      ((p4Q2LO_originalLocalPlaquetteContinuous H p A - 1) / 2)) muH := by
    have hp : Continuous (fun A : Cfg =>
        (p4Q2LO_originalLocalPlaquetteContinuous H p A - 1) / 2) :=
      ((p4Q2LO_originalLocalPlaquetteContinuous H p).continuous.sub continuous_const).div_const 2
    exact (hk.mul hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, KC beta A B * fCont A ∂muH) =
        ∫ A : Cfg, ∑ p : Plaq, KC beta A B *
          ((p4Q2LO_originalLocalPlaquetteContinuous H p A - 1) / 2) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37AIN_originalSource_eq_centeredPlaquetteSum H A, Finset.mul_sum]
    _ = ∑ p : Plaq, (∫ A : Cfg, KC beta A B *
          ((p4Q2LO_originalLocalPlaquetteContinuous H p A - 1) / 2) ∂muH) := by
      rw [integral_finset_sum _ (fun p _hp => hEach p)]
    _ = ∑ p : Plaq, Zcross beta * r beta ^ 4 *
          ((p4Q2LO_originalLocalPlaquetteContinuous H p B - 1) / 2) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact p4Q2PZ37AIN_originalCrossingPlaquette_convolution H beta p B
    _ = Zcross beta * r beta ^ 4 * fCont B := by
      rw [← Finset.mul_sum, ← p4Q2PZ37AIN_originalSource_eq_centeredPlaquetteSum H B]

/-- Compact continuity of the actual all-link crossing kernel at a fixed
right boundary. -/
theorem p4Q2PZ37AIN_originalCrossingKernel_leftContinuous
    (beta : ℝ) (B : Cfg) :
    Continuous (fun A : Cfg => KC beta A B) := by
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    (continuous_id : Continuous (fun A : Cfg => A)).prodMk
      (continuous_const : Continuous (fun _ : Cfg => B))
  have hJoint : Continuous (fun q : Cfg × Cfg => KC beta q.1 q.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous H 2 beta
  have hKernel := Continuous.comp'
    (f := fun A : Cfg => (A, B))
    (g := fun q : Cfg × Cfg => KC beta q.1 q.2) hJoint hPair
  change Continuous (fun A : Cfg => KC beta A B) at hKernel
  exact hKernel

theorem p4Q2PZ37AIN_originalCrossingKernel_pos
    (beta : ℝ) (A B : Cfg) : 0 < KC beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
  exact Real.exp_pos _

/-- The lower bound uses the ORIGINAL complete crossing action. -/
theorem p4Q2PZ37AIN_originalCrossingKernel_lower
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    Real.exp (-(2 * beta * pH)) ≤ KC beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
  apply Real.exp_le_exp.mpr
  have hBound := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AHQ_originalCrossing_le_twoCount H A B) hbeta
  linarith only [hBound]

/-- Genuine crossing-weighted source variance has a strictly positive
finite-volume floor at positive coupling. -/
theorem p4Q2PZ37AIN_originalCrossingSecondMoment_lower
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Real.exp (-(2 * beta * pH)) * Vsrc ≤
      ∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hSq : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKSq : Integrable (fun A : Cfg => KC beta A B * (fCont A) ^ 2) muH :=
    ((p4Q2PZ37AIN_originalCrossingKernel_leftContinuous H beta B).mul
      (hf.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    Real.exp (-(2 * beta * pH)) * Vsrc =
        ∫ A : Cfg, Real.exp (-(2 * beta * pH)) * (fCont A) ^ 2 ∂muH := by
      rw [integral_const_mul]
      rfl
    _ ≤ ∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH := by
      apply integral_mono (hSq.const_mul _) hKSq
      intro A
      exact mul_le_mul_of_nonneg_right
        (p4Q2PZ37AIN_originalCrossingKernel_lower H beta hbeta A B)
        (sq_nonneg (fCont A))

/-- This is an exact identity for the original LEFT halfweight. -/
theorem p4Q2PZ37AIN_originalLeftHalfweight_factor
    (beta : ℝ) (A : Cfg) :
    Real.exp (-(beta / 2) * W A) =
      Real.exp (-(beta * (pH / 2))) *
        Real.exp (-(beta * fCont A)) := by
  rw [← Real.exp_add]
  congr 1
  rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H A]
  ring

/-- Restore both ORIGINAL spatial halfweights. The quantitative scalar
inequality holds for BOTH signs of the original signed source. -/
theorem p4Q2PZ37AIN_originalRightWeightedTransfer_quadraticUpper
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Real.exp ((beta / 2) * W B) * T beta f0 B ≤
      Real.exp (-(beta * (pH / 2))) *
        (Zcross beta * r beta ^ 4 * fCont B -
          (beta * Real.exp (-(beta * (pH / 2)))) *
            (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hk := p4Q2PZ37AIN_originalCrossingKernel_leftContinuous H beta B
  have hSource : Integrable (fun A : Cfg => KC beta A B * fCont A) muH :=
    (hk.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSq : Integrable (fun A : Cfg => KC beta A B * (fCont A) ^ 2) muH :=
    (hk.mul (hf.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hExp : Integrable
      (fun A : Cfg => KC beta A B * (fCont A * Real.exp (-(beta * fCont A)))) muH := by
    have hArg : Continuous (fun A : Cfg => -(beta * fCont A)) :=
      (continuous_const.mul hf).neg
    exact (hk.mul (hf.mul (Real.continuous_exp.comp hArg))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCorrection : Integrable
      (fun A : Cfg => (beta * Real.exp (-(beta * (pH / 2)))) *
        (KC beta A B * (fCont A) ^ 2)) muH := hSq.const_mul _
  have hPoint (A : Cfg) :
      KC beta A B * (fCont A * Real.exp (-(beta * fCont A))) ≤
        KC beta A B * fCont A -
          (beta * Real.exp (-(beta * (pH / 2)))) *
            (KC beta A B * (fCont A) ^ 2) := by
    have hScalar := p4Q2PZ37AIE_real_centeredLaplace_quadraticUpper
      beta (pH / 2) (fCont A) hbeta
      (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num))
      (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A)
    have hScalar' : fCont A * Real.exp (-(beta * fCont A)) ≤
        fCont A - (beta * Real.exp (-(beta * (pH / 2)))) * (fCont A) ^ 2 := by
      nlinarith only [hScalar]
    have hScaled := mul_le_mul_of_nonneg_left hScalar'
      (p4Q2PZ37AIN_originalCrossingKernel_pos H beta A B).le
    nlinarith only [hScaled]
  rw [p4Q2PZ37AIF_originalRightWeightedTransfer_eq_crossingIntegral H beta B]
  calc
    (∫ A : Cfg, (fCont A * Real.exp (-(beta / 2) * W A)) * KC beta A B ∂muH) =
        Real.exp (-(beta * (pH / 2))) *
          (∫ A : Cfg, KC beta A B * (fCont A * Real.exp (-(beta * fCont A))) ∂muH) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37AIN_originalLeftHalfweight_factor H beta A]
      ring
    _ ≤ Real.exp (-(beta * (pH / 2))) *
          (∫ A : Cfg, KC beta A B * fCont A -
            (beta * Real.exp (-(beta * (pH / 2)))) *
              (KC beta A B * (fCont A) ^ 2) ∂muH) :=
      mul_le_mul_of_nonneg_left
        (integral_mono hExp (hSource.sub hCorrection) hPoint) (Real.exp_pos _).le
    _ = Real.exp (-(beta * (pH / 2))) *
        (Zcross beta * r beta ^ 4 * fCont B -
          (beta * Real.exp (-(beta * (pH / 2)))) *
            (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) := by
      rw [integral_sub hSource hCorrection, integral_const_mul,
        p4Q2PZ37AIN_originalCrossingSource_convolution H beta B]

/-- A useful upper envelope for every boundary, without any assumption on
the sign of the signed source at that boundary. -/
theorem p4Q2PZ37AIN_originalRightWeightedTransfer_upper
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Real.exp ((beta / 2) * W B) * T beta f0 B ≤
      Real.exp (-(beta * (pH / 2))) * (Zcross beta * r beta ^ 4 * fCont B) := by
  have hSq : 0 ≤ ∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH :=
    integral_nonneg (fun A => mul_nonneg
      (p4Q2PZ37AIN_originalCrossingKernel_pos H beta A B).le (sq_nonneg _))
  have hCorrection : 0 ≤ (beta * Real.exp (-(beta * (pH / 2)))) *
      (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH) :=
    mul_nonneg (mul_nonneg hbeta (Real.exp_pos _).le) hSq
  exact (p4Q2PZ37AIN_originalRightWeightedTransfer_quadraticUpper H beta hbeta B).trans
    (mul_le_mul_of_nonneg_left (sub_le_self _ hCorrection) (Real.exp_pos _).le)

/-- Equivalent pointwise upper bound for the unchanged physical transfer,
with the original RIGHT halfweight explicitly restored. -/
theorem p4Q2PZ37AIN_originalTransfer_upper
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    T beta f0 B ≤ Real.exp (-(beta / 2) * W B) *
      (Real.exp (-(beta * (pH / 2))) * (Zcross beta * r beta ^ 4 * fCont B)) := by
  have hCancel : Real.exp (-(beta / 2) * W B) *
      Real.exp ((beta / 2) * W B) = 1 := by
    have hArg : -(beta / 2) * W B + (beta / 2) * W B = 0 := by ring
    rw [← Real.exp_add, hArg, Real.exp_zero]
  calc
    T beta f0 B = Real.exp (-(beta / 2) * W B) *
        (Real.exp ((beta / 2) * W B) * T beta f0 B) := by
      rw [← mul_assoc, hCancel, one_mul]
    _ ≤ Real.exp (-(beta / 2) * W B) *
        (Real.exp (-(beta * (pH / 2))) * (Zcross beta * r beta ^ 4 * fCont B)) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AIN_originalRightWeightedTransfer_upper H beta hbeta B) (Real.exp_pos _).le

/-- Strictness, including fCont(B)=0, comes from the actual positive Haar
variance and the complete crossing-kernel lower bound. -/
theorem p4Q2PZ37AIN_originalTransfer_neg_of_source_nonpos
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) (hB : fCont B ≤ 0) :
    T beta f0 B < 0 := by
  have hSq : 0 < ∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH :=
    (mul_pos (Real.exp_pos _)
      (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2).trans_le
        (p4Q2PZ37AIN_originalCrossingSecondMoment_lower H beta hbeta.le B)
  have hCorrection : 0 < (beta * Real.exp (-(beta * (pH / 2)))) *
      (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH) :=
    mul_pos (mul_pos hbeta (Real.exp_pos _)) hSq
  have hSource : Zcross beta * r beta ^ 4 * fCont B ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (p4Q2PZ37AIF_originalCrossingPartition_pos H beta)
        (pow_pos (p4Q2PZ37ABN_originalTemporalWilsonCoefficient_pos beta hbeta) 4)).le hB
  have hUpper : Real.exp (-(beta * (pH / 2))) *
      (Zcross beta * r beta ^ 4 * fCont B -
        (beta * Real.exp (-(beta * (pH / 2)))) *
          (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) < 0 :=
    mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith only [hSource, hCorrection])
  have hWeighted :=
    (p4Q2PZ37AIN_originalRightWeightedTransfer_quadraticUpper H beta hbeta.le B).trans_lt hUpper
  by_contra hNot
  have hNonneg : 0 ≤ T beta f0 B := le_of_not_gt hNot
  have hProduct : 0 ≤ Real.exp ((beta / 2) * W B) * T beta f0 B :=
    mul_nonneg (Real.exp_pos _).le hNonneg
  exact (not_lt_of_ge hProduct) hWeighted

/-- The specified boundary is the actual identity on EVERY original
spatial link. -/
theorem p4Q2PZ37AIN_originalIdentity_action_zero : W identityH = 0 := by
  have hSource : fCont identityH = -pH / 2 := p4Q2PZ37AHH_originalSource_identity H
  rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H identityH] at hSource
  linarith only [hSource]

/-- Exact-normalizer quantitative identity certificate for ALL beta>=0. -/
theorem p4Q2PZ37AIN_originalIdentityTransfer_le_negativeCoefficient
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    T beta f0 identityH ≤
      -((pH / 2) * Real.exp (-(beta * (pH / 2))) * Zcross beta * r beta ^ 4) := by
  have hUpper := p4Q2PZ37AIN_originalRightWeightedTransfer_upper H beta hbeta identityH
  have hSource : fCont identityH = -pH / 2 := p4Q2PZ37AHH_originalSource_identity H
  rw [p4Q2PZ37AIN_originalIdentity_action_zero H, hSource] at hUpper
  simp only [mul_zero, Real.exp_zero, one_mul] at hUpper
  nlinarith only [hUpper]

/-- No unevaluated source, partition, or character integral occurs in this
finite-volume identity-boundary amplitude. -/
def p4Q2PZ37AIN_elementaryIdentityNegativeFloor (beta : ℝ) : ℝ :=
  (pH / 2) * Real.exp (-(beta * (pH / 2))) *
    Real.exp (-(2 * beta * (nH : ℝ))) * (beta * Real.exp (-2 * beta) / 4) ^ 4

local notation "eta" => p4Q2PZ37AIN_elementaryIdentityNegativeFloor H

theorem p4Q2PZ37AIN_elementaryIdentityNegativeFloor_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < eta beta := by
  unfold p4Q2PZ37AIN_elementaryIdentityNegativeFloor
  exact mul_pos
    (mul_pos (mul_pos (div_pos (p4Q2PZ37AHN_count_pos H) (by norm_num))
      (Real.exp_pos _)) (Real.exp_pos _))
    (pow_pos (div_pos (mul_pos hbeta (Real.exp_pos _)) (by norm_num)) 4)

theorem p4Q2PZ37AIN_elementaryIdentityNegativeFloor_zero : eta 0 = 0 := by
  simp [p4Q2PZ37AIN_elementaryIdentityNegativeFloor]

/-- ABN's actual temporal coefficient and AIJ's actual partition lower
bounds produce the fully elementary identity amplitude. -/
theorem p4Q2PZ37AIN_originalIdentityTransfer_le_negativeElementaryFloor
    (beta : ℝ) (hbeta : 0 ≤ beta) : T beta f0 identityH ≤ -(eta beta) := by
  have hZ := p4Q2PZ37AIJ_originalCrossingPartition_ge_expCount H beta hbeta
  have hBase : 0 ≤ beta * Real.exp (-2 * beta) / 4 :=
    div_nonneg (mul_nonneg hbeta (Real.exp_pos _).le) (by norm_num)
  have hPow := pow_le_pow_left₀ hBase
    (p4Q2PZ37ABN_originalTemporalWilsonCoefficient_ge_explicit beta hbeta) 4
  have hLeft : 0 ≤ (pH / 2) * Real.exp (-(beta * (pH / 2))) :=
    mul_nonneg (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num)) (Real.exp_pos _).le
  have hFloor : eta beta ≤
      (pH / 2) * Real.exp (-(beta * (pH / 2))) * Zcross beta * r beta ^ 4 := by
    unfold p4Q2PZ37AIN_elementaryIdentityNegativeFloor
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hZ hLeft) hPow
      (pow_nonneg hBase 4)
      (mul_nonneg hLeft (p4Q2PZ37AIF_originalCrossingPartition_pos H beta).le)
  exact (p4Q2PZ37AIN_originalIdentityTransfer_le_negativeCoefficient H beta hbeta).trans
    (neg_le_neg hFloor)

/-- A SPECIFIED actual negative boundary at EVERY positive coupling,
without a small-coupling assumption. -/
theorem p4Q2PZ37AIN_originalIdentityTransfer_neg
    (beta : ℝ) (hbeta : 0 < beta) : T beta f0 identityH < 0 :=
  (p4Q2PZ37AIN_originalIdentityTransfer_le_negativeElementaryFloor H beta hbeta.le).trans_lt
    (neg_neg_of_pos (p4Q2PZ37AIN_elementaryIdentityNegativeFloor_pos H beta hbeta))

theorem p4Q2PZ37AIN_originalFixedIdentityTransfer_neg :
    T beta0 f0 identityH < 0 :=
  p4Q2PZ37AIN_originalIdentityTransfer_neg H beta0 p4Q2PZ37ADC_fixedCoupling_pos

theorem p4Q2PZ37AIN_originalFixedIdentityTransfer_elementaryCertificate :
    0 < eta beta0 ∧ T beta0 f0 identityH ≤ -(eta beta0) :=
  ⟨p4Q2PZ37AIN_elementaryIdentityNegativeFloor_pos H beta0 p4Q2PZ37ADC_fixedCoupling_pos,
    p4Q2PZ37AIN_originalIdentityTransfer_le_negativeElementaryFloor
      H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le⟩

/-- The actual source is nonpositive on at least half of ORIGINAL Haar
space. The explicit cochain twist is source-odd and Haar preserving. -/
theorem p4Q2PZ37AIN_originalSource_nonpos_Haar_half :
    (1 / 2 : ℝ≥0∞) ≤ muH {B : Cfg | fCont B ≤ 0} := by
  let N : Set Cfg := {B | fCont B ≤ 0}
  let P : Set Cfg := {B | 0 ≤ fCont B}
  let τ : Cfg → Cfg := p4Q2PZ37AHW_originalCenterTwist H
  have hτ : MeasurePreserving τ muH muH :=
    p4Q2PZ37AHW_originalCenterTwist_Haar_measurePreserving H
  have hN : MeasurableSet N :=
    (isClosed_le (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
      continuous_const).measurableSet
  have hpreimage : τ ⁻¹' N = P := by
    ext B
    change fCont (p4Q2PZ37AHW_originalCenterTwist H B) ≤ 0 ↔
      0 ≤ fCont B
    rw [p4Q2PZ37AHW2_originalSource_centerTwist_odd H B]
    constructor <;> intro h <;> linarith only [h]
  have heq : muH P = muH N := by
    rw [← hpreimage, ← Measure.map_apply hτ.measurable hN, hτ.map_eq]
  have hcover : N ∪ P = Set.univ := by
    ext B
    change (fCont B ≤ 0 ∨ 0 ≤ fCont B) ↔ True
    exact iff_true_intro (le_total _ _)
  have hsum : (1 : ℝ≥0∞) ≤ muH N + muH N := by
    calc
      1 = muH (N ∪ P) := by rw [hcover, measure_univ]
      _ ≤ muH N + muH P := measure_union_le N P
      _ = muH N + muH N := by rw [heq]
  exact ENNReal.div_le_of_le_mul (by simpa only [mul_two] using hsum)

/-- A half-Haar bound for the ZERO-threshold negative set at every
positive coupling. This does not replace AIG's full-margin negative set. -/
theorem p4Q2PZ37AIN_originalTransfer_negative_Haar_half
    (beta : ℝ) (hbeta : 0 < beta) :
    (1 / 2 : ℝ≥0∞) ≤ muH {B : Cfg | T beta f0 B < 0} := by
  refine (p4Q2PZ37AIN_originalSource_nonpos_Haar_half H).trans ?_
  apply measure_mono
  intro B hB
  exact p4Q2PZ37AIN_originalTransfer_neg_of_source_nonpos H beta hbeta B hB

/-- The same genuine normalized Haar bound in the real-valued notation
used by the existing finite-volume certificates. -/
theorem p4Q2PZ37AIN_originalTransfer_negative_realHaar_half
    (beta : ℝ) (hbeta : 0 < beta) :
    (1 / 2 : ℝ) ≤ Measure.real muH {B : Cfg | T beta f0 B < 0} := by
  have h := ENNReal.toReal_mono
    (measure_ne_top muH {B : Cfg | T beta f0 B < 0})
    (p4Q2PZ37AIN_originalTransfer_negative_Haar_half H beta hbeta)
  simpa [Measure.real] using h

theorem p4Q2PZ37AIN_originalFixedTransfer_negative_realHaar_half :
    (1 / 2 : ℝ) ≤ Measure.real muH {B : Cfg | T beta0 f0 B < 0} :=
  p4Q2PZ37AIN_originalTransfer_negative_realHaar_half
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalSingleLinkPartition_eq_temporalMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalCrossingPartition_eq_temporalMassPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalSource_eq_centeredPlaquetteSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalCrossingPlaquette_convolution
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalCrossingSource_convolution
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalCrossingKernel_leftContinuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalCrossingKernel_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalCrossingKernel_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalCrossingSecondMoment_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalLeftHalfweight_factor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalRightWeightedTransfer_quadraticUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalRightWeightedTransfer_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalTransfer_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalTransfer_neg_of_source_nonpos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalIdentity_action_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalIdentityTransfer_le_negativeCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_elementaryIdentityNegativeFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_elementaryIdentityNegativeFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_elementaryIdentityNegativeFloor_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalIdentityTransfer_le_negativeElementaryFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalIdentityTransfer_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalFixedIdentityTransfer_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalFixedIdentityTransfer_elementaryCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalSource_nonpos_Haar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalTransfer_negative_Haar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalTransfer_negative_realHaar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIN_originalFixedTransfer_negative_realHaar_half

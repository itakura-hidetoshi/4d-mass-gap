import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstOrderHaarExpansionV5_PZ37AHP
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHQ — original crossing correlation centered Haar budget

AHP isolated the TRUE original temporal crossing/source Haar correlation

  X_H(B) = ∫ f_H(A) * Cross_H(A,B) dμ_H(A).

The crossing action is the sum of the SAME original SU(2) Wilson energies
of the genuine spatial links, with each genuine Wilson energy in [0,2].
The original AHI count identity says card(Link_H)=p_H exactly.
Therefore the actual crossing action belongs to [0,2*p_H].

The ORIGINAL source has exact Haar mean zero by AHP. Subtracting p_H
from the crossing action inside the original signed Haar integral is
therefore an equality, not a replacement source or independent
probability law:

  X_H(B) = ∫ f_H(A) * (Cross_H(A,B)-p_H) dμ_H(A).

The centered crossing oscillation has pointwise bound p_H rather than
2*p_H. AEV's genuine signed weighted-integral estimate gives

  |X_H(B)| ≤ p_H*Msrc_H ≤ p_H²/2,

uniformly for every original physical right boundary B.
This improves the naïve uncentered 2*p_H*Msrc_H by a factor of two.

AHP's genuine first-order expansion then yields an explicit, original,
boundary-independent signed transfer approximation:

  |T_{H,beta}(B)+beta*V_H|
      ≤ E_H(beta)+beta*p_H*Msrc_H
      ≤ E_H(beta)+beta*p_H²/2.

At the actual fixed coupling beta0 ≤ 1/128, the second correction has
an entirely rational envelope p_H²/256. The exact AHN source variance
floor F_H is preserved in a separate signed upper bound.

This does NOT claim exact Haar orthogonality X_H(B)=0, sign of X_H(B),
an actually satisfied transfer sign threshold, any evaluated AGP table,
H-uniform coercivity or the 4D continuum mass gap. The next task is
the TRUE one-link/plaquette Haar independence proof, which is NOT
silently assumed in this leaf. All original source/kernel/Haar objects
and theorem assumptions remain unchanged. Append-only new Lean file.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHQ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHQ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHQ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHQ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHQ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "X" => p4Q2PZ37AHP_originalCrossingCorrelation H
local notation "E" => p4Q2PZ37AHP_originalQuadraticBudget H
local notation "F" => p4Q2PZ37AHP_originalVarianceFloor H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AHQ_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHQ_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The literal original crossing-link list has EXACTLY the genuine
spatial plaquette count, not an independently inserted cardinal bound. -/
theorem p4Q2PZ37AHQ_crossingLinkCount_exact :
    ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) = pH := by
  calc
    ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) =
        (Fintype.card Link : ℝ) := by
      simp only [periodicHypercubicEvenSpatialSliceLinkList,
        Finset.length_toList, Finset.card_univ, Fintype.card_eq_nat_card]
    _ = pH := p4Q2PZ37AHI_cardLinks_eq_plaquettes H

/-- Actual original temporal crossing action is nonnegative. -/
theorem p4Q2PZ37AHQ_originalCrossing_nonneg (A B : Cfg) :
    0 ≤ Cross A B :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_nonneg
    H 2 (by norm_num) A B

/-- No surrogate crossing model: each original one-link Wilson energy is ≤2. -/
theorem p4Q2PZ37AHQ_originalCrossing_le_twoCount (A B : Cfg) :
    Cross A B ≤ 2 * pH := by
  calc
    Cross A B ≤ 2 *
        ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_le_two_mul_length
        H 2 (by norm_num) A B
    _ = 2 * pH := by
      rw [p4Q2PZ37AHQ_crossingLinkCount_exact H]

/-- Exact centered crossing amplitude certificate, using the proved
0≤Cross≤2p_H original one-slab bounds. -/
theorem p4Q2PZ37AHQ_originalCrossing_centered_abs_le_count (A B : Cfg) :
    |Cross A B - pH| ≤ pH := by
  have hLo := p4Q2PZ37AHQ_originalCrossing_nonneg H A B
  have hHi := p4Q2PZ37AHQ_originalCrossing_le_twoCount H A B
  apply abs_le.mpr
  constructor <;> linarith only [hLo, hHi]

/-- Integrable original signed source times the literal crossing
action, under the ORIGINAL spatial product Haar measure. -/
theorem p4Q2PZ37AHQ_originalCrossingWeightedSource_integrable (B : Cfg) :
    Integrable (fun A : Cfg => fCont A * Cross A B) muH := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hCross : Continuous (fun A : Cfg => Cross A B) :=
    p4Q2PZ37AHP_originalCrossing_continuous H B
  exact (hf.mul hCross).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The comparison product uses the genuine source multiplied by
the EXACT original p_H, not a new source or Haar measure. -/
theorem p4Q2PZ37AHQ_originalCrossingConstantWeightedSource_integrable :
    Integrable (fun A : Cfg => fCont A * pH) muH := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  exact (hf.mul continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Source exact Haar mean zero makes constant crossing background
vanish, not merely small: ∫ f_H(A)*p_H dμ_H(A)=0. -/
theorem p4Q2PZ37AHQ_originalConstantCrossing_integral_zero :
    (∫ A : Cfg, fCont A * pH ∂muH) = 0 := by
  calc
    (∫ A : Cfg, fCont A * pH ∂muH) =
        (∫ A : Cfg, pH * fCont A ∂muH) := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = pH * (∫ A : Cfg, fCont A ∂muH) :=
      integral_const_mul pH _
    _ = 0 := by rw [p4Q2PZ37AHP_originalSource_mean_zero H]; ring

/-- The ORIGINAL crossing correlation is the centered crossing
oscillation integral, using only the already PROVED zero source mean. -/
theorem p4Q2PZ37AHQ_originalCrossingCorrelation_eq_centered (B : Cfg) :
    X B = ∫ A : Cfg, fCont A * (Cross A B - pH) ∂muH := by
  have hfCross : Integrable (fun A : Cfg => fCont A * Cross A B) muH :=
    p4Q2PZ37AHQ_originalCrossingWeightedSource_integrable H B
  have hfConst : Integrable (fun A : Cfg => fCont A * pH) muH :=
    p4Q2PZ37AHQ_originalCrossingConstantWeightedSource_integrable H
  calc
    X B = (∫ A : Cfg, fCont A * Cross A B ∂muH) -
        (∫ A : Cfg, fCont A * pH ∂muH) := by
      rw [p4Q2PZ37AHQ_originalConstantCrossing_integral_zero H]
      simp [p4Q2PZ37AHP_originalCrossingCorrelation]
    _ = ∫ A : Cfg, fCont A * (Cross A B - pH) ∂muH := by
      rw [← integral_sub hfCross hfConst]
      apply integral_congr_ae
      filter_upwards with A
      ring

/-- A non-assumed, genuine signed Haar correlation amplitude certificate.
Centering the crossing action improves the 2p_H envelope to p_H. -/
theorem p4Q2PZ37AHQ_originalCrossingCorrelation_abs_le_sourceMass (B : Cfg) :
    |X B| ≤ pH * Msrc := by
  have hf : Integrable (fun A : Cfg => fCont A) muH :=
    p4Q2PZ37AHP_originalContinuousSource_integrable H
  have hu : Integrable (fun A : Cfg => fCont A * Cross A B) muH :=
    p4Q2PZ37AHQ_originalCrossingWeightedSource_integrable H B
  have hv : Integrable (fun A : Cfg => fCont A * pH) muH :=
    p4Q2PZ37AHQ_originalCrossingConstantWeightedSource_integrable H
  have hVariation :
      |(∫ A : Cfg, fCont A * Cross A B ∂muH) -
        (∫ A : Cfg, fCont A * pH ∂muH)| ≤
        pH * (∫ A : Cfg, |fCont A| ∂muH) :=
    p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
      muH (fun A : Cfg => fCont A)
      (fun A : Cfg => Cross A B) (fun _A : Cfg => pH) pH
      hf hu hv
      (fun A => p4Q2PZ37AHQ_originalCrossing_centered_abs_le_count H A B)
  rw [p4Q2PZ37AHQ_originalConstantCrossing_integral_zero H, sub_zero,
    ← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H] at hVariation
  exact hVariation

/-- The original AHJ source-Haar upper bound yields a fully explicit
plaquette-count scalar for the original crossing/source correlation. -/
theorem p4Q2PZ37AHQ_originalCrossingCorrelation_abs_le_halfSquare (B : Cfg) :
    |X B| ≤ pH ^ 2 / 2 := by
  have hp : 0 ≤ pH := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  calc
    |X B| ≤ pH * Msrc :=
      p4Q2PZ37AHQ_originalCrossingCorrelation_abs_le_sourceMass H B
    _ ≤ pH * (pH / 2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H) hp
    _ = pH ^ 2 / 2 := by ring

/-- The AHP true Wilson beta-expansion becomes a B-independent
unconditional original signed transfer enclosure, with no unknown
crossing correlation on the RIGHT side. -/
theorem p4Q2PZ37AHQ_originalTransfer_centeredVarianceError
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |T beta f0 B + beta * Vsrc| ≤
      E beta + beta * (pH * Msrc) := by
  have hAHP :=
    p4Q2PZ37AHP_originalTransfer_varianceCrossing_bound H beta hbeta B
  have hX : |X B| ≤ pH * Msrc :=
    p4Q2PZ37AHQ_originalCrossingCorrelation_abs_le_sourceMass H B
  have hScaled : |beta * X B| ≤ beta * (pH * Msrc) := by
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left hX hbeta
  calc
    |T beta f0 B + beta * Vsrc| =
        |(T beta f0 B + beta * (Vsrc + X B)) - beta * X B| := by
      congr 1
      ring
    _ ≤ |T beta f0 B + beta * (Vsrc + X B)| + |beta * X B| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (T beta f0 B + beta * (Vsrc + X B))
          (0 : ℝ) (beta * X B))
    _ ≤ E beta + beta * (pH * Msrc) :=
      add_le_add hAHP hScaled

/-- Truly unconditional original-source, original-Haar transfer
enclosure with only the actual p_H, original slab action budget and beta. -/
theorem p4Q2PZ37AHQ_originalTransfer_centeredVarianceError_halfCount
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |T beta f0 B + beta * Vsrc| ≤
      E beta + beta * pH ^ 2 / 2 := by
  have hp : 0 ≤ pH := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  have hM : Msrc ≤ pH / 2 :=
    p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H
  have hScale : beta * (pH * Msrc) ≤
      beta * (pH * (pH / 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM hp) hbeta
  calc
    |T beta f0 B + beta * Vsrc| ≤
        E beta + beta * (pH * Msrc) :=
      p4Q2PZ37AHQ_originalTransfer_centeredVarianceError H beta hbeta B
    _ ≤ E beta + beta * (pH * (pH / 2)) :=
      add_le_add_right hScale (E beta)
    _ = E beta + beta * pH ^ 2 / 2 := by ring

/-- At the ORIGINAL fixed positive beta0, the crossing uncertainty
is bounded by the explicit rational p_H²/256; the original quadratic
remainder E_H(beta0) remains separate and retains its exact definition. -/
theorem p4Q2PZ37AHQ_fixedCoupling_originalTransfer_rationalCrossingBudget
    (B : Cfg) :
    |T beta0 f0 B + beta0 * Vsrc| ≤
      E beta0 + pH ^ 2 / 256 := by
  have hb : 0 ≤ beta0 := p4Q2PZ37ADC_fixedCoupling_pos.le
  have hBeta : beta0 ≤ (1 / 128 : ℝ) :=
    p4Q2PZ37AHI_fixedCoupling_le_one128
  have hSq : 0 ≤ pH ^ 2 := sq_nonneg _
  have hScale : beta0 * pH ^ 2 / 2 ≤ pH ^ 2 / 256 := by
    have h := mul_le_mul_of_nonneg_right hBeta hSq
    nlinarith only [h]
  calc
    |T beta0 f0 B + beta0 * Vsrc| ≤
        E beta0 + beta0 * pH ^ 2 / 2 :=
      p4Q2PZ37AHQ_originalTransfer_centeredVarianceError_halfCount
        H beta0 hb B
    _ ≤ E beta0 + pH ^ 2 / 256 :=
      add_le_add_right hScale (E beta0)

/-- Retain the ORIGINAL AHN positive variance floor, but remove the
unresolved crossing correlation from the right side of the upper bound
by its true-Haar amplitude certificate. No sign is presumed. -/
theorem p4Q2PZ37AHQ_originalTransfer_upper_from_AHN_uniform
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    T beta f0 B ≤
      -(beta * F) + beta * (pH * Msrc) + E beta := by
  have hAHP := p4Q2PZ37AHP_originalTransfer_upper_from_AHN H beta hbeta B
  have hX : |X B| ≤ pH * Msrc :=
    p4Q2PZ37AHQ_originalCrossingCorrelation_abs_le_sourceMass H B
  have hScaled : -(beta * X B) ≤ beta * (pH * Msrc) := by
    calc
      -(beta * X B) = beta * (-(X B)) := by ring
      _ ≤ beta * |X B| :=
        mul_le_mul_of_nonneg_left (neg_le_abs _) hbeta
      _ ≤ beta * (pH * Msrc) :=
        mul_le_mul_of_nonneg_left hX hbeta
  calc
    T beta f0 B ≤ -(beta * (F + X B)) + E beta := hAHP
    _ = -(beta * F) + (-(beta * X B)) + E beta := by ring
    _ ≤ -(beta * F) + beta * (pH * Msrc) + E beta := by
      linarith only [hScaled]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_crossingLinkCount_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalCrossing_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalCrossing_le_twoCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalCrossing_centered_abs_le_count
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalCrossingWeightedSource_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalCrossingConstantWeightedSource_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalConstantCrossing_integral_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalCrossingCorrelation_eq_centered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalCrossingCorrelation_abs_le_sourceMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalCrossingCorrelation_abs_le_halfSquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalTransfer_centeredVarianceError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalTransfer_centeredVarianceError_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_fixedCoupling_originalTransfer_rationalCrossingBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHQ_originalTransfer_upper_from_AHN_uniform

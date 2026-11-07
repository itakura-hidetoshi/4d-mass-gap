import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredCrossingHaarBudgetV5_PZ37AHQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCenteredFirstPlaquetteSumV5_PW2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalThreeCrossingFreeLinkV5_PY3
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHR — genuine original one-crossing Haar orthogonality

AHP isolated the original full one-slab transfer's FIRST beta coefficient
as V_H+X_H(B), with V_H the genuine nonzero Gauss-law source Haar second
moment and X_H(B)=∫ f_H(A) Cross_H(A,B) dμ_H(A). AHQ bounded |X_H(B)|
but did NOT assert the cancellation X_H(B)=0.

AHR proves that cancellation without any new independence assumption.
The existing genuine PY3 geometry proves that each original four-edge
spatial plaquette has a free edge other than any designated temporal
crossing edge, EVEN at the minimal spatial period. PU/PV/PY3 prove
the SU(2) central -I flip is true product-Haar measure preserving
and the spatial plaquette character is odd on that free link.
PU2 proves the designated one-link crossing energy is unchanged.
Therefore the actual character × one-crossing Haar integral vanishes.

PW proves the ORIGINAL complete crossing is the exact finite link sum.
PW2 proves the ORIGINAL complete spatial action is the plaquette count
minus the exact finite plaquette-character sum. AGN identifies the
centered physical source as (W_H-p_H)/2. Consequently its continuous
representative is MINUS ONE HALF of the true character sum, and the
original AHP correlation X_H(B) is EXACTLY ZERO at every actual B.

The original full Wilson kernel (both spatial halfweights INCLUDED)
therefore obeys the sharpened first-order estimate

          |T_beta(B)+beta*V_H| <= E_H(beta)

without AHQ's positive crossing uncertainty. Using AHN's proven
V_H>0, at each fixed finite H this yields an EXISTENTIAL sufficiently
small beta>0 with T_beta(B)<0 for EVERY true right boundary B.

This finite-volume small-coupling result does NOT evaluate the original
preselected beta0, a volume-uniform coercivity constant, physical
positive/negative transfer sign shells at beta0, Hamiltonian spectral
gap, or continuum Yang--Mills mass gap. Nothing is overwritten,
and no original source/kernel/Haar/type evidence is replaced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHR_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHR_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHR_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHR_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHR_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "E1" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "X" => p4Q2PZ37AHP_originalCrossingCorrelation H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Eerr" => p4Q2PZ37AHP_originalQuadraticBudget H
local notation "F" => p4Q2PZ37AHP_originalVarianceFloor H
local notation "Cslab" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H

local instance p4Q2PZ37AHR_linkFintype : Fintype Link :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ37AHR_plaquetteFintype : Fintype Plaq :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair
local instance p4Q2PZ37AHR_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Every genuine original spatial plaquette character is Haar
orthogonal to EVERY actual SINGLE temporal crossing Wilson energy.
The proof uses PY3's genuine free edge and PU's true center-flip Haar
symmetry, not an assumed conditional independence premise. -/
theorem p4Q2PZ37AHR_originalPlaquette_oneCrossingHaar_zero
    (p : Plaq) (e : Link) (B : Cfg) :
    (∫ A : Cfg, χ p A * E1 ((A e)⁻¹ * B e) ∂muH) = 0 := by
  obtain ⟨target, hMember, ht, _, _⟩ :=
    p4Q2PY3_originalPlaquette_freeLink_for_threeCrossings H p e e e
  let obs : Cfg → ℝ :=
    fun A => χ p A * E1 ((A e)⁻¹ * B e)
  have hχ : Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hE : Continuous (fun A : Cfg => E1 ((A e)⁻¹ * B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hObs : Continuous obs := hχ.mul hE
  have hOdd (A : Cfg) : obs (Flip target A) = -obs A := by
    dsimp [obs]
    rw [p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
        H p target hMember A,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target e ht.symm A B]
    ring
  change (∫ A : Cfg, obs A ∂muH) = 0
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target obs hObs hOdd

/-- Exact integration over the ORIGINAL complete crossing LINK sum,
without discarding any link or substituting a new product probability. -/
theorem p4Q2PZ37AHR_originalPlaquette_fullCrossingHaar_zero
    (p : Plaq) (B : Cfg) :
    (∫ A : Cfg, χ p A * Cross A B ∂muH) = 0 := by
  classical
  let weight : Link → Cfg → ℝ :=
    fun e A => E1 ((A e)⁻¹ * B e)
  have hχ : Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hWeight (e : Link) : Continuous (weight e) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hEach (e : Link) :
      Integrable (fun A : Cfg => χ p A * weight e A) muH :=
    (hχ.mul (hWeight e)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, χ p A * Cross A B ∂muH) =
        ∫ A : Cfg, ∑ e : Link, χ p A * weight e A ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW_originalCrossing_eq_finsetSum H A B]
      simp only [weight]
      rw [Finset.mul_sum]
      apply Finset.sum_congr
      · ext e
        simp
      · intro e _he
        rfl
    _ = ∑ e : Link, (∫ A : Cfg, χ p A * weight e A ∂muH) := by
      rw [integral_finset_sum _ (fun e _ => hEach e)]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro e _he
      exact p4Q2PZ37AHR_originalPlaquette_oneCrossingHaar_zero H p e B

/-- Original complete finite spatial plaquette trace sum is
Haar-orthogonal to the entire original temporal crossing action. -/
theorem p4Q2PZ37AHR_originalTraceSum_fullCrossingHaar_zero
    (B : Cfg) :
    (∫ A : Cfg, Φ A * Cross A B ∂muH) = 0 := by
  classical
  have hCross : Continuous (fun A : Cfg => Cross A B) :=
    p4Q2PZ37AHP_originalCrossing_continuous H B
  have hEach (p : Plaq) :
      Integrable (fun A : Cfg => χ p A * Cross A B) muH :=
    ((p4Q2PV_originalPlaquetteRealCharacter_continuous H p).mul hCross).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, Φ A * Cross A B ∂muH) =
        ∫ A : Cfg, ∑ p : Plaq, χ p A * Cross A B ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      unfold p4Q2PW2_originalAllPlaquetteRealTrace
      rw [Finset.sum_mul]
      apply Finset.sum_congr
      · ext p
        simp
      · intro p _hp
        rfl
    _ = ∑ p : Plaq, (∫ A : Cfg, χ p A * Cross A B ∂muH) := by
      rw [integral_finset_sum _ (fun p _ => hEach p)]
    _ = 0 := by
      simp [p4Q2PZ37AHR_originalPlaquette_fullCrossingHaar_zero H]

/-- The authentic continuous representative of the original
Gauss-law ZW centered source is MINUS half the actual finite
spatial Wilson trace sum. No scalar was postulated or altered. -/
theorem p4Q2PZ37AHR_originalSource_eq_negHalfTrace (A : Cfg) :
    fCont A = -((1 / 2 : ℝ) * Φ A) := by
  have hCard : (Fintype.card Plaq : ℝ) = pH := by
    simp only [p4Q2PZ37AFZ_plaquetteCount,
      periodicHypercubicEvenSpatialSlicePlaquetteList,
      Finset.length_toList, Finset.card_univ,
      Fintype.card_eq_nat_card]
  have hPW :=
    p4Q2PW2_originalSpatialWilsonAction_eq_card_sub_traceSum H A
  simp only [Fintype.card_eq_nat_card] at hPW hCard
  rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H A, hPW, hCard]
  ring

/-- The former AHQ amplitude-obstruction X_H(B) vanishes EXACTLY
for every original SU(2) right boundary at EVERY finite H.
No independence assertion for the interacting Wilson posterior
or Gauss-law physical transfer has been introduced. -/
theorem p4Q2PZ37AHR_originalCrossingCorrelation_zero (B : Cfg) :
    X B = 0 := by
  change (∫ A : Cfg, fCont A * Cross A B ∂muH) = 0
  calc
    (∫ A : Cfg, fCont A * Cross A B ∂muH) =
        ∫ A : Cfg, -((1 / 2 : ℝ) * (Φ A * Cross A B)) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37AHR_originalSource_eq_negHalfTrace H A]
      ring
    _ = -((1 / 2 : ℝ) *
        (∫ A : Cfg, Φ A * Cross A B ∂muH)) := by
      rw [integral_neg, integral_const_mul]
    _ = 0 := by
      rw [p4Q2PZ37AHR_originalTraceSum_fullCrossingHaar_zero H B]
      ring

/-- AHP's actual first beta coefficient for the original complete
Wilson one-slab transfer equals the genuine AHN SOURCE variance
without any crossing correction. -/
theorem p4Q2PZ37AHR_originalFirstActionMoment_eq_variance (B : Cfg) :
    p4Q2PZ37AHP_originalFirstActionMoment H B = Vsrc := by
  rw [p4Q2PZ37AHP_originalFirstMoment_eq_variance_add_crossing H B,
    p4Q2PZ37AHR_originalCrossingCorrelation_zero H B, add_zero]

/-- Improved original signed transfer expansion with NO first-order
crossing uncertainty. Works for every beta >= 0 and genuine right B. -/
theorem p4Q2PZ37AHR_originalTransfer_varianceOnly_bound
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |T beta f0 B + beta * Vsrc| ≤ Eerr beta := by
  simpa only [p4Q2PZ37AHR_originalCrossingCorrelation_zero H B, add_zero] using
    p4Q2PZ37AHP_originalTransfer_varianceCrossing_bound H beta hbeta B

/-- The improved true complete original Wilson transfer upper bound
uses AHN's positive source variance floor, not an invented gap. -/
theorem p4Q2PZ37AHR_originalTransfer_upper_sharpFromAHN
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    T beta f0 B ≤ -(beta * F) + Eerr beta := by
  simpa only [p4Q2PZ37AHR_originalCrossingCorrelation_zero H B, add_zero] using
    p4Q2PZ37AHP_originalTransfer_upper_from_AHN H beta hbeta B

/-- Concrete TRUE signed-transfer negative branch whenever beta
is positive and the authentic quadratic remainder lies below the
genuine beta times AHN source variance. -/
theorem p4Q2PZ37AHR_originalTransfer_negative_of_varianceBudget
    (beta : ℝ) (hbeta : 0 < beta)
    (hSmall : beta * (Cslab ^ 2 * Msrc) < 2 * Vsrc)
    (B : Cfg) :
    T beta f0 B < 0 := by
  have hErr : Eerr beta = beta * (beta * (Cslab ^ 2 * Msrc)) / 2 := by
    unfold p4Q2PZ37AHP_originalQuadraticBudget
    ring
  have hMult := mul_lt_mul_of_pos_left hSmall hbeta
  have hErrLt : Eerr beta < beta * Vsrc := by
    rw [hErr]
    nlinarith only [hMult]
  have hBound :=
    (abs_le.mp
      (p4Q2PZ37AHR_originalTransfer_varianceOnly_bound
        H beta hbeta.le B)).2
  linarith only [hErrLt, hBound]

/-- Entirely genuine finite-volume SMALL-COUPLING negative-transfer
existence: one positive beta works for EVERY original right boundary.
This beta is chosen from the TRUE source variance and the proved
original slab budget; it is not the preselected physical beta0 and
is not uniform in H. -/
theorem p4Q2PZ37AHR_exists_uniform_negative_smallCoupling :
    ∃ beta : ℝ, 0 < beta ∧ ∀ B : Cfg, T beta f0 B < 0 := by
  let a : ℝ := Cslab ^ 2 * Msrc
  have ha : 0 ≤ a := by
    exact mul_nonneg (sq_nonneg _)
      (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)
  have hV : 0 < Vsrc :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  let beta : ℝ := Vsrc / (a + 1)
  have hDen : 0 < a + 1 := by linarith only [ha]
  have hbeta : 0 < beta := div_pos hV hDen
  have hEq : beta * (a + 1) = Vsrc := by
    dsimp [beta]
    field_simp
  have hSmall : beta * a < 2 * Vsrc := by
    nlinarith only [hEq, hbeta, hV]
  refine ⟨beta, hbeta, ?_⟩
  intro B
  exact p4Q2PZ37AHR_originalTransfer_negative_of_varianceBudget
    H beta hbeta (by simpa only [a] using hSmall) B

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_originalPlaquette_oneCrossingHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_originalPlaquette_fullCrossingHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_originalTraceSum_fullCrossingHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_originalSource_eq_negHalfTrace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_originalCrossingCorrelation_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_originalFirstActionMoment_eq_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_originalTransfer_varianceOnly_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_originalTransfer_upper_sharpFromAHN
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_originalTransfer_negative_of_varianceBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHR_exists_uniform_negative_smallCoupling

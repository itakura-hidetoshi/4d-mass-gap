import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalElementaryNegativeHaarFloorV5_PZ37AIK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIL — explicit small-coupling full negative region

Keep the ORIGINAL full Wilson slab action, both spatial halfweights, the
signed ZW physical L2 source, its existing continuous representative, and
the original normalized spatial product Haar measure.

The original exact link/plaquette count identifies the existing global
action budget as C_H=4*p_H. With AIK's elementary variance floor v_H set
  tau_H = v_H / (16*p_H^3+1) > 0.
For EVERY 0<beta<=tau_H and EVERY original right boundary B, AHR's
variance-only Taylor estimate and AHJ's source L1 bound give
  T_beta f0(B) < -3*beta*V_H/4.
The +1 in the explicit denominator supplies strict slack even at beta=tau_H.

The actual single-link Wilson energy is nonnegative, so Zcross<=1.
Thus the ORIGINAL AIG margin epsilon_H(beta)<=beta*V_H/2, and every
boundary is below -3*epsilon_H(beta)/2. The SAME original full-margin
negative region equals the whole configuration space and has true Haar
mass exactly one on this explicitly specified finite-volume interval.
The already defined original identity configuration is a specified
negative boundary here. Nonnegative boundaries are impossible here.

No claim places the original fixed beta0 in this interval. The interval
depends on H, and no arbitrary-coupling evaluated center, positive boundary,
volume-uniform coercivity, Hamiltonian gap, or continuum gap is inferred.
All existing statements, assumptions, roots, pins and workflows are retained.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIL_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIL_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIL_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIL_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIL_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "nu" => normalizedCompactHaar G

/-- Integrate the actual nonnegative-energy Wilson factor against the
original normalized Haar probability. No surrogate partition is used. -/
theorem p4Q2PZ37AIL_originalSingleLinkPartition_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    p4Q2PZ37AIF_originalSingleLinkPartition beta ≤ 1 := by
  have hPoint (g : G) :
      Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 g) ≤ (1 : ℝ) := by
    calc
      Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 g) ≤
          Real.exp 0 := Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta)
          (specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) g))
      _ = 1 := Real.exp_zero
  have hInt := integral_mono
    (p4Q2PZ37AIF_originalSingleLinkPartition_integrable beta)
    (integrable_const (μ := nu) (1 : ℝ)) hPoint
  simpa only [p4Q2PZ37AIF_originalSingleLinkPartition,
    integral_const, probReal_univ, one_smul] using hInt

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "v" => p4Q2PZ37AIK_elementarySourceVarianceFloor H
local notation "Cslab" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "Eerr" => p4Q2PZ37AHP_originalQuadraticBudget H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H
local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "identityH" => p4Q2PZ37AHN_identity H

local instance p4Q2PZ37AIL_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The old global action budget uses the actual plaquette and link lists.
Their already proved equal counts give exactly four times p_H. -/
theorem p4Q2PZ37AIL_originalGlobalActionBudget_eq_fourCount :
    Cslab = 4 * pH := by
  have hLinks :
      ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) = pH := by
    simpa only [periodicHypercubicEvenSpatialSliceLinkList,
      Finset.length_toList, Finset.card_univ, Fintype.card_eq_nat_card] using
      p4Q2PZ37AHI_cardLinks_eq_plaquettes H
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume
  rw [Nat.cast_add]
  change 2 * (pH + ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ)) =
    4 * pH
  rw [hLinks]
  ring

/-- A specified positive cutoff with no source, L1, or partition integrals.
All finite-volume dependence remains in the ORIGINAL counts and AIK floor. -/
def p4Q2PZ37AIL_elementarySmallCoupling : ℝ :=
  v / (16 * pH ^ 3 + 1)

local notation "tau" => p4Q2PZ37AIL_elementarySmallCoupling H

theorem p4Q2PZ37AIL_elementarySmallCoupling_pos : 0 < tau := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hv := p4Q2PZ37AIK_elementarySourceVarianceFloor_pos H
  unfold p4Q2PZ37AIL_elementarySmallCoupling
  positivity

/-- Exact connection to the old action budget; the +1 is strict slack. -/
theorem p4Q2PZ37AIL_elementarySmallCoupling_eq_actionBudget :
    tau = v / (Cslab ^ 2 * pH + 1) := by
  unfold p4Q2PZ37AIL_elementarySmallCoupling
  rw [p4Q2PZ37AIL_originalGlobalActionBudget_eq_fourCount]
  congr 1
  ring

/-- The unchanged true source L1 bound removes its unevaluated integral
from the genuine quadratic Taylor error budget. -/
theorem p4Q2PZ37AIL_originalQuadraticBudget_le_elementary (beta : ℝ) :
    Eerr beta ≤ beta ^ 2 * Cslab ^ 2 * pH / 4 := by
  calc
    Eerr beta ≤ ((beta * Cslab) ^ 2 / 2) * (pH / 2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H)
        (div_nonneg (sq_nonneg _) (by norm_num))
    _ = beta ^ 2 * Cslab ^ 2 * pH / 4 := by ring

/-- Strict error control holds on the CLOSED upper endpoint beta=tau.
The argument uses the actual positive beta and the denominator's +1. -/
theorem p4Q2PZ37AIL_originalQuadraticBudget_lt_quarterVarianceFloor
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) :
    Eerr beta < beta * v / 4 := by
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have hDen : 0 < Cslab ^ 2 * pH + 1 := by positivity
  rw [p4Q2PZ37AIL_elementarySmallCoupling_eq_actionBudget] at hSmall
  have hProduct : beta * (Cslab ^ 2 * pH + 1) ≤ v :=
    (le_div_iff₀ hDen).mp hSmall
  have hStrict : beta * (Cslab ^ 2 * pH) < v := by
    nlinarith only [hProduct, hbeta]
  have hScaled := mul_lt_mul_of_pos_left hStrict hbeta
  have hBudget := p4Q2PZ37AIL_originalQuadraticBudget_le_elementary H beta
  nlinarith only [hBudget, hScaled]

/-- AHR's genuine first-order expansion is uniform in the right boundary.
The bound is on the original physical transfer, not a Taylor polynomial. -/
theorem p4Q2PZ37AIL_originalTransfer_lt_negThreeQuarterVariance
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) (B : Cfg) :
    T beta f0 B < -(3 * beta * Vsrc / 4) := by
  have hError :=
    p4Q2PZ37AIL_originalQuadraticBudget_lt_quarterVarianceFloor H beta hbeta hSmall
  have hFloor := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIK_elementarySourceVarianceFloor_le_original H) hbeta.le
  have hUpper := (abs_le.mp
    (p4Q2PZ37AHR_originalTransfer_varianceOnly_bound H beta hbeta.le B)).2
  linarith only [hError, hFloor, hUpper]

/-- Every boundary has a fully elementary strict negative amplitude. -/
theorem p4Q2PZ37AIL_originalTransfer_lt_negThreeQuarterElementary
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) (B : Cfg) :
    T beta f0 B < -(3 * beta * v / 4) := by
  have h := p4Q2PZ37AIL_originalTransfer_lt_negThreeQuarterVariance
    H beta hbeta hSmall B
  have hFloor := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIK_elementarySourceVarianceFloor_le_original H) hbeta.le
  linarith only [h, hFloor]

/-- The actual product crossing partition is at most one for beta>=0. -/
theorem p4Q2PZ37AIL_originalCrossingPartition_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) : Zcross beta ≤ 1 := by
  have hPow := pow_le_pow_left₀
    (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta).le
    (p4Q2PZ37AIL_originalSingleLinkPartition_le_one beta hbeta)
    (Fintype.card Link)
  simpa only [p4Q2PZ37AIF_originalCrossingPartition, one_pow] using hPow

/-- Compare to the ORIGINAL AIG margin, including its actual partition.
This upper bound complements AIK's preserved lower bound. -/
theorem p4Q2PZ37AIL_originalNegativeMargin_le_halfVariance
    (beta : ℝ) (hbeta : 0 ≤ beta) : margin beta ≤ beta * Vsrc / 2 := by
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have hV : 0 ≤ Vsrc := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le
  have hZ0 := (p4Q2PZ37AIF_originalCrossingPartition_pos H beta).le
  have hZ1 := p4Q2PZ37AIL_originalCrossingPartition_le_one H beta hbeta
  have hExp : Real.exp (-(2 * beta * pH)) ≤ 1 := by
    calc
      Real.exp (-(2 * beta * pH)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr (by positivity))
      _ = 1 := Real.exp_zero
  have hCoeff : Zcross beta * Real.exp (-(2 * beta * pH)) ≤ 1 := by
    calc
      Zcross beta * Real.exp (-(2 * beta * pH)) ≤ Zcross beta * 1 :=
        mul_le_mul_of_nonneg_left hExp hZ0
      _ ≤ 1 := by simpa only [mul_one] using hZ1
  have hScaled := mul_le_mul_of_nonneg_left hCoeff (mul_nonneg hbeta hV)
  unfold p4Q2PZ37AIG_originalNegativeTransferMargin
  nlinarith only [hScaled]

/-- EVERY original boundary meets AII's stronger three-half-margin center
criterion on the specified interval. The original margin is unchanged. -/
theorem p4Q2PZ37AIL_originalTransfer_below_threeHalfMargin
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) (B : Cfg) :
    T beta f0 B < -(3 * margin beta / 2) := by
  have h := p4Q2PZ37AIL_originalTransfer_lt_negThreeQuarterVariance
    H beta hbeta hSmall B
  have hm := p4Q2PZ37AIL_originalNegativeMargin_le_halfVariance H beta hbeta.le
  linarith only [h, hm]

/-- All configurations belong to the SAME original full-margin region. -/
theorem p4Q2PZ37AIL_originalFullNegativeRegion_eq_univ
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) :
    Region beta = Set.univ := by
  ext B
  simp only [p4Q2PZ37AIG_originalNegativeTransferRegion, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  have h := p4Q2PZ37AIL_originalTransfer_below_threeHalfMargin H beta hbeta hSmall B
  have hm := p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta
  linarith only [h, hm]

theorem p4Q2PZ37AIL_originalFullNegativeRegion_measure_one
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) :
    muH (Region beta) = 1 := by
  rw [p4Q2PZ37AIL_originalFullNegativeRegion_eq_univ H beta hbeta hSmall]
  exact measure_univ

theorem p4Q2PZ37AIL_originalFullNegativeRegion_realMeasure_one
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) :
    Measure.real muH (Region beta) = 1 := by
  rw [p4Q2PZ37AIL_originalFullNegativeRegion_eq_univ H beta hbeta hSmall]
  exact probReal_univ

/-- Use the ALREADY DEFINED original identity configuration explicitly.
No compactness choice or unknown negative center occurs in this statement. -/
theorem p4Q2PZ37AIL_originalIdentityTransfer_below_threeHalfMargin
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) :
    T beta f0 identityH < -(3 * margin beta / 2) :=
  p4Q2PZ37AIL_originalTransfer_below_threeHalfMargin H beta hbeta hSmall identityH

theorem p4Q2PZ37AIL_originalIdentityTransfer_lt_elementary
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) :
    T beta f0 identityH < -(3 * beta * v / 4) :=
  p4Q2PZ37AIL_originalTransfer_lt_negThreeQuarterElementary
    H beta hbeta hSmall identityH

theorem p4Q2PZ37AIL_originalTransfer_negative
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) (B : Cfg) :
    T beta f0 B < 0 := by
  have h := p4Q2PZ37AIL_originalTransfer_lt_negThreeQuarterElementary
    H beta hbeta hSmall B
  have hv := p4Q2PZ37AIK_elementarySourceVarianceFloor_pos H
  have hPos : 0 < 3 * beta * v / 4 := by positivity
  linarith only [h, hPos]

/-- An actual obstruction to positive or zero transfer boundaries on this
interval, rather than an unresolved sign search. Outside it nothing follows. -/
theorem p4Q2PZ37AIL_originalNonnegativeRegion_eq_empty
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tau) :
    {B : Cfg | 0 ≤ T beta f0 B} = ∅ := by
  ext B
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact not_le.mpr (p4Q2PZ37AIL_originalTransfer_negative H beta hbeta hSmall B)

/-- The explicitly supplied endpoint itself is a genuine positive coupling
with all-boundary negativity and original full-margin Haar mass one. -/
theorem p4Q2PZ37AIL_explicitEndpoint_certificate :
    0 < tau ∧
      (∀ B : Cfg, T tau f0 B < -(3 * margin tau / 2)) ∧
      Measure.real muH (Region tau) = 1 := by
  have hTau := p4Q2PZ37AIL_elementarySmallCoupling_pos H
  exact ⟨hTau,
    fun B => p4Q2PZ37AIL_originalTransfer_below_threeHalfMargin H tau hTau le_rfl B,
    p4Q2PZ37AIL_originalFullNegativeRegion_realMeasure_one H tau hTau le_rfl⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalSingleLinkPartition_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalGlobalActionBudget_eq_fourCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_elementarySmallCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_elementarySmallCoupling_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_elementarySmallCoupling_eq_actionBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalQuadraticBudget_le_elementary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalQuadraticBudget_lt_quarterVarianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalTransfer_lt_negThreeQuarterVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalTransfer_lt_negThreeQuarterElementary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalCrossingPartition_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalNegativeMargin_le_halfVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalTransfer_below_threeHalfMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalFullNegativeRegion_eq_univ
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalFullNegativeRegion_measure_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalFullNegativeRegion_realMeasure_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalIdentityTransfer_below_threeHalfMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalIdentityTransfer_lt_elementary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalTransfer_negative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_originalNonnegativeRegion_eq_empty
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIL_explicitEndpoint_certificate

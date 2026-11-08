import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHalfHaarFullMarginCouplingV5_PZ37AIO
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIP — strict original partition and a larger closed half-Haar interval

Keep the ORIGINAL complete SU(2) Wilson slab action, both spatial halfweights,
signed ZW physical L2 source and its continuous representative, genuine Haar,
and AIG's original epsilon and strict full-margin negative region.

The original single-link energy has genuine Haar mean one. Its actual range
0<=E<=2 and add_one_le_exp prove the quantitative partition deficit
  z(beta) <= 1-beta*exp(-2*beta) < 1  (beta>0).
For 0<beta<1/4 this strengthens to z(beta)<exp(-beta/2). The exact positive
original link count equals p_H, so the actual product partition satisfies
  Zcross_H(beta)<exp(-beta*p_H/2).
Thus AIO's unchanged exact margin comparison is strict on the CLOSED interval
  0<beta<=log(2)/p_H.
The new endpoint is exactly three halves of AIO's old endpoint. Both the old
endpoint and the strictly larger new endpoint have original full-margin Haar
mass at least 1/2. The old definitions and all previous stronger conclusions
on their own smaller intervals are retained.

No convex-chord surrogate, replacement measure, independent-plaquette
assumption, or source normalization is introduced. There is no claim of an
optimal interval, arbitrary-coupling full negativity, volume-uniform positive
amplitude/coercivity, Hamiltonian gap, or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIP_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIP_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIP_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIP_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIP_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "nu" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "z" => p4Q2PZ37AIF_originalSingleLinkPartition

local instance p4Q2PZ37AIP_singleLinkProbability : IsProbabilityMeasure nu :=
  normalizedCompactHaar_isProbabilityMeasure G

theorem p4Q2PZ37AIP_originalSingleLinkEnergy_integrable : Integrable E nu :=
  (continuous_specialUnitaryWilsonPlaquetteEnergy 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The mean is a theorem about the original normalized compact SU(2) Haar,
obtained from the existing exact character-zero identity. -/
theorem p4Q2PZ37AIP_originalSingleLinkEnergy_Haar_mean :
    (∫ g : G, E g ∂nu) = 1 := by
  have hChi := p4Q2PZ35D4_originalOneLinkHaar_characterZero
  change (∫ g : G, (1 : ℝ) - E g ∂nu) = 0 at hChi
  rw [integral_sub (integrable_const (μ := nu) (1 : ℝ))
    p4Q2PZ37AIP_originalSingleLinkEnergy_integrable] at hChi
  simp only [integral_const, probReal_univ, one_smul] at hChi
  linarith only [hChi]

/-- An elementary deficit on the full original energy range, valid at every
nonnegative coupling. Its integration below uses the actual energy mean. -/
theorem p4Q2PZ37AIP_real_exp_deficit
    (beta x : ℝ) (hbeta : 0 ≤ beta) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    beta * Real.exp (-2 * beta) * x ≤ 1 - Real.exp (-beta * x) := by
  have hLower : Real.exp (-2 * beta) ≤ Real.exp (-beta * x) := by
    apply Real.exp_le_exp.mpr
    have hMul := mul_le_mul_of_nonneg_left hx2 hbeta
    nlinarith only [hMul]
  have hExponential := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp (beta * x)) (Real.exp_pos (-beta * x)).le
  have hCancel : Real.exp (-beta * x) * Real.exp (beta * x) = 1 := by
    have hArg : -beta * x + beta * x = 0 := by ring
    rw [← Real.exp_add, hArg, Real.exp_zero]
  rw [hCancel] at hExponential
  have hScaled := mul_le_mul_of_nonneg_left hLower (mul_nonneg hbeta hx)
  nlinarith only [hExponential, hScaled]

/-- A quantitative strictness budget for the actual AIF partition.
No integral or measure in its definition is changed. -/
theorem p4Q2PZ37AIP_originalSingleLinkPartition_le_deficit
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    z beta ≤ 1 - beta * Real.exp (-2 * beta) := by
  have hE := p4Q2PZ37AIP_originalSingleLinkEnergy_integrable
  have hPoint (g : G) : Real.exp (-beta * E g) ≤
      1 - (beta * Real.exp (-2 * beta)) * E g := by
    have h := p4Q2PZ37AIP_real_exp_deficit beta (E g) hbeta
      (specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num : 0 < (2 : ℕ)) g)
      (specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num : 0 < (2 : ℕ)) g)
    linarith only [h]
  calc
    z beta = ∫ g : G, Real.exp (-beta * E g) ∂nu := rfl
    _ ≤ ∫ g : G, (1 : ℝ) - (beta * Real.exp (-2 * beta)) * E g ∂nu :=
      integral_mono (p4Q2PZ37AIF_originalSingleLinkPartition_integrable beta)
        ((integrable_const (μ := nu) (1 : ℝ)).sub (hE.const_mul _)) hPoint
    _ = 1 - beta * Real.exp (-2 * beta) := by
      rw [integral_sub (integrable_const (μ := nu) (1 : ℝ)) (hE.const_mul _),
        integral_const_mul, p4Q2PZ37AIP_originalSingleLinkEnergy_Haar_mean]
      simp only [integral_const, probReal_univ, one_smul, mul_one]

theorem p4Q2PZ37AIP_originalSingleLinkPartition_lt_one
    (beta : ℝ) (hbeta : 0 < beta) : z beta < 1 := by
  have hBound := p4Q2PZ37AIP_originalSingleLinkPartition_le_deficit beta hbeta.le
  have hDeficit : 0 < beta * Real.exp (-2 * beta) := mul_pos hbeta (Real.exp_pos _)
  linarith only [hBound, hDeficit]

/-- Strict exponential decay on a specified scalar interval. Strictness
comes from the proved positive partition deficit, not an assumed endpoint. -/
theorem p4Q2PZ37AIP_originalSingleLinkPartition_lt_expHalf
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta < 1 / 4) :
    z beta < Real.exp (-(beta / 2)) := by
  have hLower := Real.add_one_le_exp (-2 * beta)
  have hHalf : (1 / 2 : ℝ) < Real.exp (-2 * beta) := by
    linarith only [hLower, hSmall]
  have hProduct := mul_lt_mul_of_pos_left hHalf hbeta
  have hBound := p4Q2PZ37AIP_originalSingleLinkPartition_le_deficit beta hbeta.le
  have hExp := Real.add_one_le_exp (-(beta / 2))
  linarith only [hProduct, hBound, hExp]

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nH" => Nat.card Link
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H
local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H
local notation "oldCutoff" => p4Q2PZ37AIO_halfHaarCouplingCutoff H

local instance p4Q2PZ37AIP_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Nat.card avoids dependence on a choice of finite enumeration. -/
theorem p4Q2PZ37AIP_originalLinkCount_eq_plaquettes : (nH : ℝ) = pH := by
  simpa only [Fintype.card_eq_nat_card] using p4Q2PZ37AHI_cardLinks_eq_plaquettes H

theorem p4Q2PZ37AIP_originalLinkCount_pos : 0 < nH := by
  have hReal : (0 : ℝ) < (nH : ℝ) := by
    rw [p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H]
    exact p4Q2PZ37AHN_count_pos H
  exact_mod_cast hReal

/-- The actual finite product partition is strictly below one at EVERY
positive coupling; positivity of the actual link count is proved above. -/
theorem p4Q2PZ37AIP_originalCrossingPartition_lt_one
    (beta : ℝ) (hbeta : 0 < beta) : Zcross beta < 1 := by
  have hPow := pow_lt_pow_left₀
    (p4Q2PZ37AIP_originalSingleLinkPartition_lt_one beta hbeta)
    (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta).le
    (ne_of_gt (p4Q2PZ37AIP_originalLinkCount_pos H))
  simpa only [p4Q2PZ37AIF_originalCrossingPartition,
    Fintype.card_eq_nat_card, one_pow] using hPow

/-- Quantitative improvement uses the actual original partition power and
the exact original count identity, not a new normalized physical transfer. -/
theorem p4Q2PZ37AIP_originalCrossingPartition_lt_expHalfCount
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta < 1 / 4) :
    Zcross beta < Real.exp (-(beta * pH / 2)) := by
  have hPow := pow_lt_pow_left₀
    (p4Q2PZ37AIP_originalSingleLinkPartition_lt_expHalf beta hbeta hSmall)
    (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta).le
    (ne_of_gt (p4Q2PZ37AIP_originalLinkCount_pos H))
  have hExp : Real.exp (-(beta / 2)) ^ nH = Real.exp (-(beta * pH / 2)) := by
    rw [← Real.exp_nat_mul, p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H]
    congr 1
    ring
  rw [hExp] at hPow
  simpa only [p4Q2PZ37AIF_originalCrossingPartition,
    Fintype.card_eq_nat_card] using hPow

/-- A larger elementary endpoint, INCLUDED in the half-Haar theorem. -/
def p4Q2PZ37AIP_closedHalfHaarCouplingCutoff : ℝ := Real.log 2 / pH

local notation "cutoff" => p4Q2PZ37AIP_closedHalfHaarCouplingCutoff H

theorem p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos : 0 < cutoff :=
  div_pos (Real.log_pos (by norm_num)) (p4Q2PZ37AHN_count_pos H)

/-- The previous endpoint is retained; the new endpoint is exactly 3/2
times as large, with no comparison involving an unevaluated Haar integral. -/
theorem p4Q2PZ37AIP_closedCutoff_eq_threeHalf_old :
    cutoff = (3 / 2 : ℝ) * oldCutoff := by
  have hp : pH ≠ 0 := ne_of_gt (p4Q2PZ37AHN_count_pos H)
  unfold p4Q2PZ37AIP_closedHalfHaarCouplingCutoff p4Q2PZ37AIO_halfHaarCouplingCutoff
  field_simp [hp] <;> ring

theorem p4Q2PZ37AIP_oldCutoff_lt_closedCutoff : oldCutoff < cutoff := by
  rw [p4Q2PZ37AIP_closedCutoff_eq_threeHalf_old H]
  have hOld := p4Q2PZ37AIO_halfHaarCouplingCutoff_pos H
  linarith only [hOld]

/-- The original minimal volume is included. This bound makes the scalar
smallness used for strict partition decay a proved consequence of the cutoff. -/
theorem p4Q2PZ37AIP_closedCutoff_le_oneDiv24 : cutoff ≤ (1 / 24 : ℝ) := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hp24 := p4Q2PZ37AIM_plaquetteCount_ge_twentyFour H
  have hLog : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith only [h]
  calc
    cutoff ≤ 1 / pH := div_le_div_of_nonneg_right hLog hp.le
    _ ≤ 1 / 24 := (div_le_div_iff₀ hp (by norm_num)).mpr (by nlinarith only [hp24])

theorem p4Q2PZ37AIP_coupling_lt_quarter_of_le_closedCutoff
    (beta : ℝ) (hSmall : beta ≤ cutoff) : beta < 1 / 4 := by
  have hCap := p4Q2PZ37AIP_closedCutoff_le_oneDiv24 H
  linarith only [hSmall, hCap]

/-- The actual AIO partition condition is STRICT even at the NEW endpoint.
Only the final exponential comparison is non-strict at that endpoint. -/
theorem p4Q2PZ37AIP_originalPartitionCondition_of_le_closedCutoff
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    Zcross beta * Real.exp (3 * beta * pH / 2) < 2 := by
  have hPartition := p4Q2PZ37AIP_originalCrossingPartition_lt_expHalfCount H beta hbeta
    (p4Q2PZ37AIP_coupling_lt_quarter_of_le_closedCutoff H beta hSmall)
  have hProduct : beta * pH ≤ Real.log 2 :=
    (le_div_iff₀ (p4Q2PZ37AHN_count_pos H)).mp hSmall
  have hExp : Real.exp (-(beta * pH / 2)) * Real.exp (3 * beta * pH / 2) =
      Real.exp (beta * pH) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ < Real.exp (-(beta * pH / 2)) * Real.exp (3 * beta * pH / 2) :=
      mul_lt_mul_of_pos_right hPartition (Real.exp_pos _)
    _ = Real.exp (beta * pH) := hExp
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hProduct
    _ = 2 := Real.exp_log (by norm_num)

/-- This still compares the SAME original AIG epsilon to AIO's actual
source-nonpositive amplitude; the old margin is not reduced. -/
theorem p4Q2PZ37AIP_originalNegativeMargin_lt_varianceFloor
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    margin beta < p4Q2PZ37AIO_sourceNonpositiveVarianceFloor H beta :=
  p4Q2PZ37AIO_originalNegativeMargin_lt_varianceFloor H beta hbeta
    (p4Q2PZ37AIP_originalPartitionCondition_of_le_closedCutoff H beta hbeta hSmall)

theorem p4Q2PZ37AIP_originalSource_nonpos_subset_fullNegativeRegion
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    {B : Cfg | fCont B ≤ 0} ⊆ Region beta :=
  p4Q2PZ37AIO_originalSource_nonpos_subset_fullNegativeRegion H beta hbeta
    (p4Q2PZ37AIP_originalPartitionCondition_of_le_closedCutoff H beta hbeta hSmall)

theorem p4Q2PZ37AIP_originalFullNegativeRegion_Haar_half
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    (1 / 2 : ℝ≥0∞) ≤ muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_Haar_half_of_partition H beta hbeta
    (p4Q2PZ37AIP_originalPartitionCondition_of_le_closedCutoff H beta hbeta hSmall)

theorem p4Q2PZ37AIP_originalFullNegativeRegion_realHaar_half
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half_of_partition H beta hbeta
    (p4Q2PZ37AIP_originalPartitionCondition_of_le_closedCutoff H beta hbeta hSmall)

/-- The formerly excluded AIO endpoint now has the OLD full-margin bound. -/
theorem p4Q2PZ37AIP_oldEndpoint_fullNegativeRegion_realHaar_half :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region oldCutoff) :=
  p4Q2PZ37AIP_originalFullNegativeRegion_realHaar_half H oldCutoff
    (p4Q2PZ37AIO_halfHaarCouplingCutoff_pos H)
    (p4Q2PZ37AIP_oldCutoff_lt_closedCutoff H).le

/-- A specified new endpoint strictly beyond AIO's old endpoint, certified
with the SAME epsilon and genuine normalized product Haar. -/
theorem p4Q2PZ37AIP_expandedEndpoint_certificate :
    oldCutoff < cutoff ∧ 0 < cutoff ∧
      Zcross cutoff * Real.exp (3 * cutoff * pH / 2) < 2 ∧
      (1 / 2 : ℝ) ≤ Measure.real muH (Region cutoff) :=
  ⟨p4Q2PZ37AIP_oldCutoff_lt_closedCutoff H,
    p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos H,
    p4Q2PZ37AIP_originalPartitionCondition_of_le_closedCutoff H cutoff
      (p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos H) le_rfl,
    p4Q2PZ37AIP_originalFullNegativeRegion_realHaar_half H cutoff
      (p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos H) le_rfl⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalSingleLinkEnergy_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalSingleLinkEnergy_Haar_mean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_real_exp_deficit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalSingleLinkPartition_le_deficit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalSingleLinkPartition_lt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalSingleLinkPartition_lt_expHalf
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalLinkCount_eq_plaquettes
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalLinkCount_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalCrossingPartition_lt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalCrossingPartition_lt_expHalfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_closedHalfHaarCouplingCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_closedCutoff_eq_threeHalf_old
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_oldCutoff_lt_closedCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_closedCutoff_le_oneDiv24
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_coupling_lt_quarter_of_le_closedCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalPartitionCondition_of_le_closedCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalNegativeMargin_lt_varianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalSource_nonpos_subset_fullNegativeRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalFullNegativeRegion_Haar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_originalFullNegativeRegion_realHaar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_oldEndpoint_fullNegativeRegion_realHaar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIP_expandedEndpoint_certificate

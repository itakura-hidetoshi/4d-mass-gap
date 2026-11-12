import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH16ExactCharacterMomentAJANoGoV5_PZ37AKT
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKU — exact original Haar-budget vs. full-top residual through H16

The existing AKQ physical comparison, together with the now-certified
AKT original crossing partition estimate, implies MORE than the absence
of an original AJA finite-power strict witness for every original H<=16:
it gives the direct non-strict comparison of the original Haar-negative
budget B_H=m_H^2 * mu_H{u_H<-m_H} to the actual full-top energy
||Q f0_H||^2, preserving the original finite SU(2) Wilson operator,
normalized S, full-top orthogonal projection, original centered ZW
source, original normalized transfer representative, margin and Haar
probability, with unchanged beta0=log(3/2)/64 and pinned mathlib.

This is NOT a proof that the difference is strictly negative or equal
to zero; only the exact nonpositive inequality Delta_H<=0 follows,
and r_H itself remains unknown. No claim of finite AJA witness at any
volume, H>=17 comparison, H-uniform coercivity, Hamiltonian gap,
or continuum 4D Yang--Mills mass gap is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "GU" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKU_group : IsTopologicalGroup GU :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKU_compact : CompactSpace GU :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKU_countable : SecondCountableTopology GU :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKU_measurable : MeasurableSpace GU :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKU_borel : BorelSpace GU :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKU_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgU" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muU" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pU" => p4Q2PZ37AFZ_plaquetteCount H
local notation "ZU" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "PU" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num)
local notation "uU" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mU" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "EU" =>
  (fun A : CfgU =>
    uU beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
      -(mU beta0 p4Q2PZ37ADC_fixedCoupling_pos.le))

local instance p4Q2PZ37AKU_probability : IsProbabilityMeasure muU := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Exact descent from AKQ's original partition-Haar criterion
to the actual original Haar budget vs. genuine full-top projection.
The original Haar mass, source and margin are preserved literally. -/
theorem p4Q2PZ37AKU_originalBudget_le_fullTop_of_partitionHaarMass
    (beta : ℝ) (hbeta : 0 < beta)
    (hMass :
      Measure.real muU
        {A : CfgU |
          uU beta hbeta.le A < -(mU beta hbeta.le)} *
          ZU beta ≤ 4 * Real.exp (-(beta * pU))) :
    (mU beta hbeta.le) ^ 2 *
      Measure.real muU
        {A : CfgU |
          uU beta hbeta.le A < -(mU beta hbeta.le)} ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 := by
  have hZ : 0 ≤ ZU beta :=
    (p4Q2PZ37AIF_originalCrossingPartition_pos H beta).le
  have hMult := mul_le_mul_of_nonneg_right hMass hZ
  have hNorm :=
    p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean H beta hbeta.le
  have hWeighted :
      Measure.real muU
        {A : CfgU |
          uU beta hbeta.le A < -(mU beta hbeta.le)} *
          (ZU beta) ^ 2 ≤ 4 * ‖PU beta hbeta.le‖ := by
    calc
      _ = (Measure.real muU
            {A : CfgU |
              uU beta hbeta.le A < -(mU beta hbeta.le)} * ZU beta) *
            ZU beta := by ring
      _ ≤ (4 * Real.exp (-(beta * pU))) * ZU beta := hMult
      _ = 4 * (Real.exp (-(beta * pU)) * ZU beta) := by ring
      _ ≤ 4 * ‖PU beta hbeta.le‖ :=
        mul_le_mul_of_nonneg_left hNorm (by norm_num)
  exact p4Q2PZ37AKQ_originalBudget_le_fullTop_of_weightedHaarMass
    H beta hbeta hWeighted

/-- An unconditional ORIGINAL-model physical budget/top comparison for
every H<=16 at unchanged beta0. This does not assume a numerical r_H. -/
theorem p4Q2PZ37AKU_originalFixedCoupling_budget_le_fullTop_of_le_sixteen
    (hH : H ≤ 16) :
    (mU beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real muU EU ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 := by
  exact p4Q2PZ37AKU_originalBudget_le_fullTop_of_partitionHaarMass
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKT_originalFixedCoupling_partitionHaarMass_of_le_sixteen H hH)

/-- The ACTUAL original top-minus-Haar obstruction has nonpositive
Haar-minus-top residual for every H<=16. No strict sign is claimed. -/
theorem p4Q2PZ37AKU_originalFixedCoupling_topHaarResidual_nonpos_of_le_sixteen
    (hH : H ≤ 16) :
    (mU beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real muU EU -
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 ≤ 0 := by
  exact sub_nonpos.mpr
    (p4Q2PZ37AKU_originalFixedCoupling_budget_le_fullTop_of_le_sixteen H hH)

/-- H=16 specialization of the original strictness-unresolved but
certified nonpositive Haar-budget minus full-top residual. -/
theorem p4Q2PZ37AKU_originalH16_topHaarResidual_nonpos :
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin 16 beta0
      p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 16 2)
        {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 16 2 |
          p4Q2PZ37AIW_originalNormalizedSourceTransfer 16 beta0
            p4Q2PZ37ADC_fixedCoupling_pos.le A <
            -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 16 beta0
              p4Q2PZ37ADC_fixedCoupling_pos.le)} -
      ‖p4Q2PZ37AJD_originalSourceTopComponent 16 beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 ≤ 0 := by
  exact p4Q2PZ37AKU_originalFixedCoupling_topHaarResidual_nonpos_of_le_sixteen
    16 (by omega)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKU_originalBudget_le_fullTop_of_partitionHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKU_originalFixedCoupling_budget_le_fullTop_of_le_sixteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKU_originalFixedCoupling_topHaarResidual_nonpos_of_le_sixteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKU_originalH16_topHaarResidual_nonpos

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPairHaarQuadraticMomentV5_PZ37ALC
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALD — true original full Wilson one-slab / pair-Laplace physical norm

The previously certified AGN identity f_H(A)=(W_H(A)-p_H)/2
holds pointwise for the ORIGINAL continuous Gauss-law ZW source.
The original full Wilson one-slab kernel retains both ORIGINAL spatial
halfweights. Its product-Haar integral therefore coincides EXACTLY with
  exp(-beta*p_H) * Lpair_H(beta,-beta),
where Lpair is the true original crossing-weighted pair-Haar Laplace
integral certified by ALB, and not an alternative physical transfer.

AIW's existing true physical constant-vector matrix coefficient and
operator-norm bound then descend this equality to the ACTUAL physical
one-slab transfer operator norm. ALC's true measured second-moment
quadratic lower bound gives
  exp(-beta*p_H) * (Zcross_H(beta)+beta²*M2pair_H(beta)/4)
     <= ||P_H(beta)||
for all finite H and nonnegative beta. An exact H22 fixed beta0
specialization retains the original p22=292008.

A strict improvement over AIW is proved only conditionally on
M2pair_H(beta)>0 at beta>0. This leaf does NOT infer such strict
positivity from mere M2>=0; it does not certify an r22 Haar-mass
upper bound, AJA no-witness, H-uniform coercivity, Hamiltonian gap,
or the continuum Yang--Mills mass gap.

All original Wilson, Haar, source, transfer, projections, margins,
pinning, canonical roots and existing Lean files are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALD_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALD_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALD_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALD_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALD_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALD_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "pairH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "KC" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "KW" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "PW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num)
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "Lpair" => p4Q2PZ37ALB_originalPairCrossingLaplace H
local notation "M2pair" => p4Q2PZ37ALC_originalPairCrossingSecondMoment H

/-- The unchanged genuine Wilson spatial action is precisely p_H
plus twice the original centered continuous ZW source. -/
theorem p4Q2PZ37ALD_originalWilsonAction_eq_centeredSource (A : Cfg) :
    W A = pH + 2 * fCont A := by
  rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H A]
  ring

/-- Exact pointwise identity for the ORIGINAL full one-slab Wilson kernel.
Both original endpoint spatial halfweights are present. -/
theorem p4Q2PZ37ALD_originalFullKernel_eq_pairLaplaceIntegrand
    (beta : ℝ) (A B : Cfg) :
    KW beta A B =
      Real.exp (-(beta * pH)) *
        (KC beta A B * Real.exp (-beta * (fCont A + fCont B))) := by
  have hWA := p4Q2PZ37ALD_originalWilsonAction_eq_centeredSource H A
  have hWB := p4Q2PZ37ALD_originalWilsonAction_eq_centeredSource H B
  change
    Real.exp (-(beta / 2) * W A) * KC beta A B *
        Real.exp (-(beta / 2) * W B) =
      Real.exp (-(beta * pH)) *
        (KC beta A B * Real.exp (-beta * (fCont A + fCont B)))
  calc
    _ = KC beta A B *
        (Real.exp (-(beta / 2) * W A) *
          Real.exp (-(beta / 2) * W B)) := by ring
    _ = KC beta A B *
        Real.exp (-(beta / 2) * W A + -(beta / 2) * W B) := by
          rw [← Real.exp_add]
    _ = KC beta A B *
        (Real.exp (-(beta * pH)) *
          Real.exp (-beta * (fCont A + fCont B))) := by
          rw [← Real.exp_add]
          congr 1
          rw [hWA, hWB]
          ring
    _ = Real.exp (-(beta * pH)) *
        (KC beta A B * Real.exp (-beta * (fCont A + fCont B))) := by ring

/-- Genuine identity of full original Wilson one-slab pair-Haar integral
with the true ALC source Laplace, not an assumed norm equality. -/
theorem p4Q2PZ37ALD_originalFullKernel_pairHaar_eq_originalLaplace
    (beta : ℝ) :
    (∫ P : Cfg × Cfg, KW beta P.1 P.2 ∂pairH) =
      Real.exp (-(beta * pH)) * Lpair beta (-beta) := by
  calc
    _ = ∫ P : Cfg × Cfg,
      Real.exp (-(beta * pH)) *
        (KC beta P.1 P.2 *
          Real.exp (-beta * (fCont P.1 + fCont P.2))) ∂pairH := by
            apply integral_congr_ae
            filter_upwards with P
            exact p4Q2PZ37ALD_originalFullKernel_eq_pairLaplaceIntegrand
              H beta P.1 P.2
    _ = Real.exp (-(beta * pH)) *
        (∫ P : Cfg × Cfg,
          KC beta P.1 P.2 *
            Real.exp (-beta * (fCont P.1 + fCont P.2)) ∂pairH) := by
              rw [integral_const_mul]
    _ = _ := rfl

/-- TRUE physical constant unit-vector expectation is equal to the
original pair-Haar Laplace only after retaining exact Wilson halfweights. -/
theorem p4Q2PZ37ALD_originalPhysicalConstantExpectation_eq_laplace
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) * Lpair beta (-beta) =
      inner ℝ
        (PW beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) := by
  rw [← p4Q2PZ37ALD_originalFullKernel_pairHaar_eq_originalLaplace H beta]
  exact p4Q2PZ37AIW_originalFullKernel_pair_integral_eq_constantExpectation
    H beta hbeta

/-- The ACTUAL original physical one-slab transfer norm dominates
the true pair-Haar Laplace, without identifying the two quantities. -/
theorem p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_pairLaplace
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) * Lpair beta (-beta) ≤
      ‖PW beta hbeta‖ := by
  rw [← p4Q2PZ37ALD_originalFullKernel_pairHaar_eq_originalLaplace H beta]
  exact p4Q2PZ37AIW_originalFullKernel_pair_integral_le_physicalTransferNorm
    H beta hbeta

/-- Strengthened unconditional finite-volume ORIGINAL physical norm floor
using the actual non-Gaussian crossing-weighted pair Haar second moment. -/
theorem p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_quadraticMoment
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta + (beta ^ 2 / 4) * M2pair beta) ≤
        ‖PW beta hbeta‖ := by
  have hLaplace :=
    p4Q2PZ37ALC_originalPairLaplace_quadraticMoment_lower H beta (-beta)
  have hScale :=
    mul_le_mul_of_nonneg_left hLaplace (Real.exp_pos (-(beta * pH))).le
  have hPhysical :=
    p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_pairLaplace
      H beta hbeta
  have hCombine := hScale.trans hPhysical
  simpa only [neg_sq] using hCombine

/-- The same quantitative improvement at the EXACT original H22 volume. -/
theorem p4Q2PZ37ALD_originalH22_physicalNorm_ge_quadraticMoment
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * p4Q2PZ37AFZ_plaquetteCount 22)) *
      (p4Q2PZ37AIF_originalCrossingPartition 22 beta +
        (beta ^ 2 / 4) *
          p4Q2PZ37ALC_originalPairCrossingSecondMoment 22 beta) ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          22 2 (by norm_num) beta hbeta‖ :=
  p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_quadraticMoment
    22 beta hbeta

/-- At the true unchanged beta0 and p22=292008, all original-model
quantities retain their exact meanings and no numerical r22 is used. -/
theorem p4Q2PZ37ALD_originalH22_fixedCoupling_physicalNorm_floor :
    Real.exp (-(p4Q2PZ37ADC_fixedCoupling * (292008 : ℝ))) *
      (p4Q2PZ37AIF_originalCrossingPartition 22
          p4Q2PZ37ADC_fixedCoupling +
        (p4Q2PZ37ADC_fixedCoupling ^ 2 / 4) *
          p4Q2PZ37ALC_originalPairCrossingSecondMoment 22
            p4Q2PZ37ADC_fixedCoupling) ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          22 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
            p4Q2PZ37ADC_fixedCoupling_pos.le‖ := by
  have hNorm :=
    p4Q2PZ37ALD_originalH22_physicalNorm_ge_quadraticMoment
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
  rw [p4Q2PZ37AKX_originalH22_plaquetteCount_exact] at hNorm
  exact hNorm

/-- A STRICT gain over the previous AIW spatial-mean floor follows
ONLY when positivity of the true original pair-Haar moment is supplied.
No such positivity is assumed silently or read from a Gaussian model. -/
theorem p4Q2PZ37ALD_originalPhysicalNorm_strictly_gt_spatialMean_of_M2_pos
    (beta : ℝ) (hbeta : 0 < beta) (hM2 : 0 < M2pair beta) :
    Real.exp (-(beta * pH)) * Zcross beta <
      ‖PW beta hbeta.le‖ := by
  have hPos : 0 < (beta ^ 2 / 4) * M2pair beta :=
    mul_pos (by positivity) hM2
  have hAdd :
      Zcross beta < Zcross beta + (beta ^ 2 / 4) * M2pair beta :=
    lt_add_of_pos_right _ hPos
  have hMul := mul_lt_mul_of_pos_left hAdd (Real.exp_pos (-(beta * pH)))
  exact hMul.trans_le
    (p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_quadraticMoment
      H beta hbeta.le)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALD_originalWilsonAction_eq_centeredSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALD_originalFullKernel_eq_pairLaplaceIntegrand
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALD_originalFullKernel_pairHaar_eq_originalLaplace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALD_originalPhysicalConstantExpectation_eq_laplace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_pairLaplace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_quadraticMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALD_originalH22_physicalNorm_ge_quadraticMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALD_originalH22_fixedCoupling_physicalNorm_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALD_originalPhysicalNorm_strictly_gt_spatialMean_of_M2_pos

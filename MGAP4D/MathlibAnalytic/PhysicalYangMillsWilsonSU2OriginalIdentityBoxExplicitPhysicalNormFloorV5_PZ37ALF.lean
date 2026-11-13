import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPairHaarSecondMomentPositiveFloorV5_PZ37ALE
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALF — explicit true identity-box Haar floor for the Wilson norm

ALE certifies M2pair_H(beta) >= 2*exp(-2*beta*ell_H)*V_H > 0 for
every original finite SU(2) Wilson slab, where V_H is the exact
original centered ZW source Haar second moment. AHN has independently
certified the original Haar identity-box geometric floor
  V_H >= (3*p_H/8)^2 * kappa(1/96)^card(original spatial links).

This append-only proof substitutes the actual AHN lower bound in the
actual ALE crossing-weighted moment estimate and then in ALD's
authentic original physical one-slab operator-norm bound:
 ||P_H(beta)|| >= exp(-beta*p_H) *
   [Zcross_H(beta) + beta^2/2 * exp(-2*beta*ell_H) *
    (3*p_H/8)^2 * kappa(1/96)^card(links)].

The added term is strictly positive for every finite H and beta>0.
The explicit H22/beta0/p22=292008 specialization has no oracle mass,
Gaussian substitution, new kernel, source, transfer or gauge measure.

The severe volume decay is retained as an obstruction: this does
not show any H-uniform coercivity, exact negative-region Haar upper
mass r22, AJA verdict, Hamiltonian or 4D continuum mass gap.
No original definitions, prior Lean files, pins or canonical root changed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALF_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALF_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALF_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALF_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALF_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALF_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "M2pair" => p4Q2PZ37ALC_originalPairCrossingSecondMoment H
local notation "kFloor" => p4Q2PZ37ALE_originalCrossingKernelFloor H
local notation "PW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2
    (by norm_num)

/-- A new NAME for the already-proved AHN original identity-box lower
bound. The radius and all true original links are unchanged. -/
def p4Q2PZ37ALF_originalIdentityBoxVarianceFloor : ℝ :=
  (3 * pH / 8) ^ 2 *
    p4Q2PZ37ADQ_sphereRadiusFraction (1 / 96) ^
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)

local notation "vBox" => p4Q2PZ37ALF_originalIdentityBoxVarianceFloor H

/-- AHN's explicit true-Haar identity box supplies strictly positive
finite-H geometric source variance without any numerical mass oracle. -/
theorem p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos :
    0 < vBox := by
  unfold p4Q2PZ37ALF_originalIdentityBoxVarianceFloor
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have hk : 0 < p4Q2PZ37ADQ_sphereRadiusFraction (1 / 96) :=
    p4Q2PZ37ADQ_sphereRadiusFraction_pos _
  have hCoeff : 0 < (3 * pH / 8) ^ 2 := by positivity
  have hPower :
      0 < p4Q2PZ37ADQ_sphereRadiusFraction (1 / 96) ^
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    pow_pos hk _
  exact mul_pos hCoeff hPower

/-- Directly reuse the original AHN true-Haar variance certificate. -/
theorem p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_le_sourceVariance :
    vBox ≤ Vsrc := by
  unfold p4Q2PZ37ALF_originalIdentityBoxVarianceFloor
  exact p4Q2PZ37AHN_originalSource_HaarSecondMoment_explicitFloor H

/-- A completely explicit original crossing-weighted source-square
bound; no unproved factorization of the crossed Wilson kernel. -/
theorem p4Q2PZ37ALF_originalPairSecondMoment_ge_identityBoxFloor
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    2 * kFloor beta * vBox ≤ M2pair beta := by
  have hVar :=
    p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_le_sourceVariance H
  have hKF := (p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta).le
  have hProd :=
    mul_le_mul_of_nonneg_left hVar
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hKF)
  have hTrue :=
    p4Q2PZ37ALE_originalPairSecondMoment_ge_explicitPositiveFloor
      H beta hbeta
  calc
    2 * kFloor beta * vBox =
        (2 * kFloor beta) * vBox := by ring
    _ ≤ (2 * kFloor beta) * Vsrc := hProd
    _ = 2 * kFloor beta * Vsrc := by ring
    _ ≤ M2pair beta := hTrue

/-- The actual original Wilson one-slab physical transfer norm now
has an explicit geometric positive correction from the AHN Haar box. -/
theorem p4Q2PZ37ALF_originalPhysicalNorm_ge_identityBoxFloor
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta +
        (beta ^ 2 / 4) * (2 * kFloor beta * vBox)) ≤
      ‖PW beta hbeta‖ := by
  have hMoment :=
    p4Q2PZ37ALF_originalPairSecondMoment_ge_identityBoxFloor H beta hbeta
  have hBeta : 0 ≤ (beta ^ 2 / 4 : ℝ) := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hMoment hBeta
  have hInner :
      Zcross beta + (beta ^ 2 / 4) * (2 * kFloor beta * vBox) ≤
      Zcross beta + (beta ^ 2 / 4) * M2pair beta :=
    add_le_add_left hScaled _
  have hExp : 0 ≤ Real.exp (-(beta * pH)) := (Real.exp_pos _).le
  exact (mul_le_mul_of_nonneg_left hInner hExp).trans
    (p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_quadraticMoment
      H beta hbeta)

/-- AHN's independent true-Haar identity-box bound makes the gain
over the previous AIW physical norm floor EXPLICITLY strict, not just
a qualitative appeal to M2pair positivity, for every beta>0. -/
theorem p4Q2PZ37ALF_originalPhysicalNorm_strictly_gt_spatialMean_viaBox
    (beta : ℝ) (hbeta : 0 < beta) :
    Real.exp (-(beta * pH)) * Zcross beta <
      ‖PW beta hbeta.le‖ := by
  have hKF := p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta
  have hBox := p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos H
  have hCorrection :
      0 < (beta ^ 2 / 4) * (2 * kFloor beta * vBox) := by
    have hβ : 0 < (beta ^ 2 / 4 : ℝ) := by positivity
    exact mul_pos hβ (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hKF) hBox)
  have hInner :
      Zcross beta <
        Zcross beta + (beta ^ 2 / 4) * (2 * kFloor beta * vBox) :=
    lt_add_of_pos_right _ hCorrection
  have hScale :=
    mul_lt_mul_of_pos_left hInner (Real.exp_pos (-(beta * pH)))
  exact hScale.trans_le
    (p4Q2PZ37ALF_originalPhysicalNorm_ge_identityBoxFloor
      H beta hbeta.le)

/-- Explicit identity-box finite-H22 fixed-beta0 norm lower bound
with EXACT original 292008 spatial plaquettes. The geometric link
power is retained in its genuine original dependent finite type. -/
theorem p4Q2PZ37ALF_originalH22_fixedCoupling_physicalNorm_ge_box :
    Real.exp (-(p4Q2PZ37ADC_fixedCoupling * (292008 : ℝ))) *
      (p4Q2PZ37AIF_originalCrossingPartition 22
          p4Q2PZ37ADC_fixedCoupling +
        (p4Q2PZ37ADC_fixedCoupling ^ 2 / 4) *
          (2 * p4Q2PZ37ALE_originalCrossingKernelFloor 22
            p4Q2PZ37ADC_fixedCoupling *
            p4Q2PZ37ALF_originalIdentityBoxVarianceFloor 22)) ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          22 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
            p4Q2PZ37ADC_fixedCoupling_pos.le‖ := by
  have h :=
    p4Q2PZ37ALF_originalPhysicalNorm_ge_identityBoxFloor
      22 p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
  rw [p4Q2PZ37AKX_originalH22_plaquetteCount_exact] at h
  exact h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALF_originalIdentityBoxVarianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_le_sourceVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALF_originalPairSecondMoment_ge_identityBoxFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALF_originalPhysicalNorm_ge_identityBoxFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALF_originalPhysicalNorm_strictly_gt_spatialMean_viaBox
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALF_originalH22_fixedCoupling_physicalNorm_ge_box

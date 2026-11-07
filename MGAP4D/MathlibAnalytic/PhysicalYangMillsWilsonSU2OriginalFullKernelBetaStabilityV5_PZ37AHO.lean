import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalIdentitySourceHaarMomentV5_PZ37AHN
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabKernelBetaLipschitz
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHO — original full-Wilson transfer stability near fixed coupling

AHN proved a positive explicit genuine spatial-Haar source L1 floor and
physical source second-moment floor at the actual identity configuration.
AHK separately proved strictly positive ORIGINAL signed source-transfer
Haar correlation for the FULL Wilson one-slab kernel at the original
positive fixed coupling beta0 = log(3/2)/64.

Here the complete (spatial halfweights INCLUDED) original Wilson kernel
K_beta(A,B) = exp(-beta*S_slab(A,B)) is varied in beta, without changing
the original ZW physical centered source or original spatial Haar law.
The existing exact action-budget mean-value theorem proves

 |T_gamma(B)-T_beta(B)|
   <= C_H * |gamma-beta| * Msrc_H
   <= C_H * |gamma-beta| * (p_H/2)

for beta,gamma >= 0, where C_H is the PROVED ORIGINAL finite one-slab
global action budget, not a new external numerical oracle. In particular
the genuine source L1 mass Msrc_H is also explicitly strictly positive,
by AHN.

Combining this genuinely quantitative beta modulus with AHK's existing
UNCONDITIONAL strictly positive action-transfer product at some real B,
there are B, q>0, delta>0 such that for EVERY nonnegative gamma with
|gamma-beta0|<delta, the SAME original physical B has

                 f_H(B) * T_gamma(B) > q.

A chosen q, delta, B remain existential: the fixed-beta original signed
correlation's numerical lower bound and the sign of T_gamma(B) alone
are NOT evaluated. No numerical AGP true-Haar table, both-sign shell,
volume-uniform coercivity, spectral gap or continuum mass gap is claimed.
The original kernel, original source, and all prior formal files are
unchanged; this leaf is append-only.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHO_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHO_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHO_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHO_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHO_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "Cslab" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "T" =>
  decomposableOneSliceTransferIntegral H 2

local instance p4Q2PZ37AHO_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The original FULL Wilson one-slab transfer is Lipschitz in the
positive coupling parameter, with the independently proven ORIGINAL
slab action budget C_H and genuine source Haar L1 mass Msrc_H. -/
theorem p4Q2PZ37AHO_originalFullTransfer_betaLipschitz
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (B : Cfg) :
    |T gamma f0 B - T beta f0 B| ≤
      (Cslab * |gamma - beta|) * Msrc := by
  let f : Cfg → ℝ := fun A => (f0 : Lp ℝ 2 muH) A
  have hf : Integrable f muH :=
    (Lp.memLp (f0 : Lp ℝ 2 muH)).integrable (by norm_num)
  have hgammaInt :
      Integrable (fun A : Cfg => f A * K gamma A B) muH :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
      H 2 (by norm_num) gamma hgamma (f0 : Lp ℝ 2 muH) B
  have hbetaInt :
      Integrable (fun A : Cfg => f A * K beta A B) muH :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
      H 2 (by norm_num) beta hbeta (f0 : Lp ℝ 2 muH) B
  have hKernel (A : Cfg) :
      |K gamma A B - K beta A B| ≤ Cslab * |gamma - beta| := by
    simpa only [Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_norm_sub_le
        H 2 (by norm_num) beta gamma hbeta hgamma A B
  have hBound :=
    p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
      muH f (fun A : Cfg => K gamma A B)
      (fun A : Cfg => K beta A B) (Cslab * |gamma - beta|)
      hf hgammaInt hbetaInt hKernel
  have hEq (b : ℝ) :
      T b f0 B = ∫ A : Cfg, f A * K b A B ∂muH := by
    unfold decomposableOneSliceTransferIntegral
    apply integral_congr_ae
    filter_upwards with A
    dsimp [f]
    ring
  calc
    |T gamma f0 B - T beta f0 B| =
        |(∫ A : Cfg, f A * K gamma A B ∂muH) -
          (∫ A : Cfg, f A * K beta A B ∂muH)| := by
      rw [hEq gamma, hEq beta]
    _ ≤ (Cslab * |gamma - beta|) * Msrc := hBound

/-- The SAME beta perturbation bound has an explicit original
plaquette-count scalar, via AHJ's true physical Haar source estimate. -/
theorem p4Q2PZ37AHO_originalFullTransfer_betaLipschitz_halfCount
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (B : Cfg) :
    |T gamma f0 B - T beta f0 B| ≤
      (Cslab * |gamma - beta|) * (pH / 2) := by
  have hC : 0 ≤ Cslab :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hCoef : 0 ≤ Cslab * |gamma - beta| :=
    mul_nonneg hC (abs_nonneg _)
  calc
    |T gamma f0 B - T beta f0 B| ≤
        (Cslab * |gamma - beta|) * Msrc :=
      p4Q2PZ37AHO_originalFullTransfer_betaLipschitz
        H beta gamma hbeta hgamma B
    _ ≤ (Cslab * |gamma - beta|) * (pH / 2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H) hCoef

/-- Exact finite-H perturbation control on the SIGNED product of
the original centered spatial Wilson action with the original FULL
transfer. No positive-part replacement or new Borel measure. -/
theorem p4Q2PZ37AHO_originalSignedProduct_betaLipschitz
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (B : Cfg) :
    |fCont B * T gamma f0 B - fCont B * T beta f0 B| ≤
      ((pH / 2) * (Cslab * Msrc)) * |gamma - beta| := by
  have hT :
      |T gamma f0 B - T beta f0 B| ≤
        (Cslab * |gamma - beta|) * Msrc :=
    p4Q2PZ37AHO_originalFullTransfer_betaLipschitz
      H beta gamma hbeta hgamma B
  have hF : |fCont B| ≤ pH / 2 :=
    p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H B
  have hp : 0 ≤ pH / 2 := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  calc
    |fCont B * T gamma f0 B - fCont B * T beta f0 B| =
        |fCont B| * |T gamma f0 B - T beta f0 B| := by
      rw [← mul_sub, abs_mul]
    _ ≤ (pH / 2) * |T gamma f0 B - T beta f0 B| :=
      mul_le_mul_of_nonneg_right hF (abs_nonneg _)
    _ ≤ (pH / 2) * ((Cslab * |gamma - beta|) * Msrc) :=
      mul_le_mul_of_nonneg_left hT hp
    _ = ((pH / 2) * (Cslab * Msrc)) * |gamma - beta| := by ring

/-- Unconditional persistence of a TRUE original full-Wilson
source-transfer SIGN ALIGNMENT in a positive coupling neighborhood of
the ORIGINAL fixed beta0. Same actual right boundary B throughout the
coupling interval. The margin and radius are existential, not evaluated
numeric transfer-sign certificates or an H-uniform coercivity bound. -/
theorem p4Q2PZ37AHO_exists_originalAlignedCouplingNeighborhood :
    ∃ B : Cfg, ∃ q delta : ℝ,
      0 < q ∧ 0 < delta ∧
      ∀ gamma : ℝ, 0 ≤ gamma → |gamma - beta0| < delta →
        q < fCont B * T gamma f0 B := by
  obtain ⟨B, hB⟩ :=
    p4Q2PZ37AHK_exists_originalActionAlignedBoundary H
  let L : ℝ := (pH / 2) * (Cslab * Msrc)
  have hp : 0 ≤ pH / 2 := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  have hC : 0 ≤ Cslab :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hM : 0 ≤ Msrc :=
    p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H
  have hL : 0 ≤ L := mul_nonneg hp (mul_nonneg hC hM)
  let q : ℝ := (fCont B * T beta0 f0 B) / 2
  let delta : ℝ := q / (L + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hDen : 0 < L + 1 := by linarith only [hL]
  have hdelta : 0 < delta := div_pos hq hDen
  have hScaleEq : delta * (L + 1) = q := by
    dsimp [delta]
    field_simp
  have hScale : L * delta < q := by
    nlinarith only [hScaleEq, hdelta]
  refine ⟨B, q, delta, hq, hdelta, ?_⟩
  intro gamma hgamma hNear
  have hVariation :
      |fCont B * T gamma f0 B - fCont B * T beta0 f0 B| ≤
        L * |gamma - beta0| := by
    exact p4Q2PZ37AHO_originalSignedProduct_betaLipschitz
      H beta0 gamma p4Q2PZ37ADC_fixedCoupling_pos.le hgamma B
  have hSmall : L * |gamma - beta0| < q :=
    (mul_le_mul_of_nonneg_left (le_of_lt hNear) hL).trans_lt hScale
  have hLower := (abs_le.mp hVariation).1
  have hDouble : fCont B * T beta0 f0 B = 2 * q := by
    dsimp [q]
    ring
  linarith only [hLower, hSmall, hDouble]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHO_originalFullTransfer_betaLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHO_originalFullTransfer_betaLipschitz_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHO_originalSignedProduct_betaLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHO_exists_originalAlignedCouplingNeighborhood

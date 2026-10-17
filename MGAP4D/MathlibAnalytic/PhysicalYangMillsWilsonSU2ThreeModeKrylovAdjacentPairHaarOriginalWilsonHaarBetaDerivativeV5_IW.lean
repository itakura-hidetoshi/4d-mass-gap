import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalUnitWilsonHaarKernelSectionV5_IV
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabKernelBetaLipschitz
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-!
# P4-Q2-IW: parameter derivative of the literal original Wilson Haar row

This file differentiates the actual temporal-gauge SU(2) Wilson one-slab
kernel, integrated over the genuine normalized physical left-boundary Haar
measure, **at beta=0** (and throughout beta > -1).

The derivative is the negative Haar mean of the ACTUAL one-slab Wilson
action, not a substituted independent-posterior conditional action.
For beta near zero a finite-volume action budget dominates the derivative;
the parameterized Bochner integral differentiation is therefore legitimate.

This alone does not establish nonconstancy in the right boundary: one
must still prove crossing-energy Haar invariance, spatial plaquette
nonconstancy, and the small-positive-beta witness. Likewise this does
not prove any original GI two-context minor or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section RawWilsonBeta

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H

/-- The true temporal crossing Wilson **action**, rather than merely its
exponentiated kernel, is jointly continuous in both actual SU(2) boundaries. -/
theorem p4Q2IW_originalWilsonCrossingAction_continuous :
    Continuous (fun p : Cfg × Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
        H 2 p.1 p.2) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil =>
      simpa using
        (continuous_const : Continuous (fun _ : Cfg × Cfg => (0 : ℝ)))
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      have hl : Continuous (fun p : Cfg × Cfg => p.1 e) :=
        (continuous_apply e).comp continuous_fst
      have hr : Continuous (fun p : Cfg × Cfg => p.2 e) :=
        (continuous_apply e).comp continuous_snd
      have hc : Continuous (fun p : Cfg × Cfg =>
          specialUnitaryWilsonPlaquetteEnergy 2 ((p.1 e)⁻¹ * p.2 e)) :=
        (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
          (hl.inv.mul hr)
      exact hc.add ih

/-- Joint continuity of the complete original, symmetrized one-slab action. -/
theorem p4Q2IW_originalWilsonOneSlabAction_continuous :
    Continuous (fun p : Cfg × Cfg => S p.1 p.2) := by
  have hw := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hc := p4Q2IW_originalWilsonCrossingAction_continuous H
  change Continuous (fun p : Cfg × Cfg =>
    (1 / 2 : ℝ) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 p.1 +
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 p.1 p.2 +
    (1 / 2 : ℝ) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 p.2)
  exact ((continuous_const.mul (hw.comp continuous_fst)).add hc).add
    (continuous_const.mul (hw.comp continuous_snd))

/-- Legitimate differentiation under the **literal physical Haar integral**
of the original Wilson kernel for beta > -1, including beta = 0.
The finite-volume action budget supplies a common integrable majorant
M * exp M on this whole parameter neighborhood. -/
theorem p4Q2IW_originalWilsonHaarRow_hasDerivAt_beta
    (beta : ℝ) (hbeta : -1 < beta) (B : Cfg) :
    HasDerivAt
      (fun t : ℝ => p4Q2IV_originalWilsonUnitHaarKernelSection H t B)
      (∫ A : Cfg, -(S A B) * K beta A B ∂haar)
      beta := by
  let F : ℝ → Cfg → ℝ := fun t A => K t A B
  let DF : ℝ → Cfg → ℝ := fun t A => -(S A B) * K t A B
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hFcont (t : ℝ) : Continuous (F t) := by
    have h :=
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H 2 t).comp hPair
    simpa only [F, Function.comp_def] using h
  have hScont : Continuous (fun A : Cfg => S A B) := by
    have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
    simpa only [Function.comp_def] using h
  have hDFcont (t : ℝ) : Continuous (DF t) := by
    simpa only [DF] using hScont.neg.mul (hFcont t)
  have hFmeas :
      ∀ᶠ t in 𝓝 beta, AEStronglyMeasurable (F t) haar := by
    filter_upwards with t
    exact (hFcont t).measurable.aestronglyMeasurable
  have hFint : Integrable (F beta) haar :=
    (hFcont beta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDFmeas : AEStronglyMeasurable (DF beta) haar :=
    (hDFcont beta).measurable.aestronglyMeasurable
  have hMnonneg : 0 ≤ M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hSrange (A : Cfg) : 0 ≤ S A B ∧ S A B ≤ M := by
    constructor
    · exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
        H 2 (by decide) A B
    · exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
        H 2 (by decide) A B
  have hBoundInt :
      Integrable (fun _ : Cfg => M * Real.exp M) haar :=
    integrable_const _
  have hBound :
      ∀ᵐ A ∂haar, ∀ t ∈ Ioi (-1 : ℝ),
        ‖DF t A‖ ≤ M * Real.exp M := by
    filter_upwards with A
    intro t ht
    have ht' : 0 ≤ t + 1 := by
      have ht0 : (-1 : ℝ) < t := ht
      linarith
    have hupper : -t * S A B ≤ M := by
      have hmul := mul_nonneg ht' (hSrange A).1
      nlinarith [(hSrange A).2]
    have hexp : Real.exp (-t * S A B) ≤ Real.exp M :=
      Real.exp_le_exp.mpr hupper
    have hnorm : ‖DF t A‖ = S A B * Real.exp (-t * S A B) := by
      dsimp [DF]
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
      simp only [norm_mul, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (hSrange A).1,
        abs_of_pos (Real.exp_pos _)]
    rw [hnorm]
    exact mul_le_mul (hSrange A).2 hexp
      (Real.exp_pos _).le hMnonneg
  have hdiff :
      ∀ᵐ A ∂haar, ∀ t ∈ Ioi (-1 : ℝ),
        HasDerivAt (F · A) (DF t A) t := by
    filter_upwards with A
    intro t _ht
    simpa only [F, DF] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_hasDerivAt_beta
        H 2 t A B)
  have hparam :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (x₀ := beta)
      (bound := fun _ : Cfg => M * Real.exp M) (μ := haar)
      (s := Ioi (-1 : ℝ)) (Ioi_mem_nhds hbeta)
      hFmeas hFint hDFmeas hBound hBoundInt hdiff
  change HasDerivAt
    (fun t : ℝ => ∫ A : Cfg, F t A ∂haar)
    (∫ A : Cfg, DF beta A ∂haar) beta
  exact hparam.2

/-- At beta = 0 the original kernel is exactly 1, and the Haar fiber has
total mass 1. No normalizing Wilson-posterior surrogate is used. -/
theorem p4Q2IW_originalWilsonHaarRow_beta_zero (B : Cfg) :
    p4Q2IV_originalWilsonUnitHaarKernelSection H 0 B = 1 := by
  unfold p4Q2IV_originalWilsonUnitHaarKernelSection
  simp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]

/-- The beta-zero derivative is the negative genuine left-Haar mean of
the full actual one-slab Wilson action, for any real right boundary B. -/
theorem p4Q2IW_originalWilsonHaarRow_hasDerivAt_zero (B : Cfg) :
    HasDerivAt
      (fun t : ℝ => p4Q2IV_originalWilsonUnitHaarKernelSection H t B)
      (-(∫ A : Cfg, S A B ∂haar)) 0 := by
  have hd := p4Q2IW_originalWilsonHaarRow_hasDerivAt_beta H 0
    (by norm_num) B
  have hInt :
      (∫ A : Cfg, -(S A B) * K 0 A B ∂haar) =
        -(∫ A : Cfg, S A B ∂haar) := by
    simp only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
      zero_mul, neg_zero, Real.exp_zero, mul_one]
    rw [integral_neg]
  simpa only [hInt] using hd

end RawWilsonBeta
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IW_originalWilsonCrossingAction_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IW_originalWilsonOneSlabAction_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IW_originalWilsonHaarRow_hasDerivAt_beta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IW_originalWilsonHaarRow_beta_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IW_originalWilsonHaarRow_hasDerivAt_zero

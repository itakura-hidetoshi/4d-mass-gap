import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedSourceAllPositiveCouplingV5_PZ37AIZ
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJA — quantitative original positive-Haar L² source-image floor

This append-only leaf keeps the genuine complete SU(2) Wilson one-slab
physical operator P, existing norm-normalized N, its original signed ZW
Gauss-law L² source, both spatial halfweights, and the ORIGINAL product-Haar
measure. No new operator, source, normalization, axiom, or volume-uniform
amplitude floor is introduced.

AIZ shows the original negative-margin sublevel set has positive genuine
Haar measure for every finite H and beta>0 and that its prescribed continuous
integral representative agrees Haar-a.e. with the existing physical L² image.

This file first proves a general quantitative measure-to-L² descent with an
explicit a.e. representative condition, then applies it to the UNCHANGED
original AIG/AIW negative set and margin:

  m_H(beta)^2 * mu_H(R_H,beta).toReal <= ||N_H,beta f0,H||^2.

The right-hand side is the actual physical Hilbert norm, not a pointwise
certificate. The lower bound depends on H and beta. It is neither a common
positive floor nor a proof of top-eigenspace orthogonality or spectral gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A genuine finite-measure real L² lower bound from a positive-measure
strict negative region of a SPECIFIED a.e. representative. No value of an
arbitrary L² representative is claimed to be pointwise canonical. -/
theorem realL2_norm_sq_ge_margin_sq_mul_realMeasure
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : Lp ℝ 2 μ) (u : α → ℝ)
    (s : Set α) (hs : MeasurableSet s) (m : ℝ) (hm : 0 ≤ m)
    (hBridge : (fun x : α => f x) =ᵐ[μ] u)
    (hRegion : ∀ x ∈ s, u x < -m) :
    m ^ 2 * Measure.real μ s ≤ ‖f‖ ^ 2 := by
  have hSqInt : Integrable (fun x : α => ‖f x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) f f)
  have hIndInt :
      Integrable (s.indicator (fun _ : α => m ^ 2)) μ :=
    (integrable_const (μ := μ) (m ^ 2)).indicator hs
  have hAE : ∀ᵐ x : α ∂μ,
      s.indicator (fun _ : α => m ^ 2) x ≤ ‖f x‖ ^ 2 := by
    filter_upwards [hBridge] with x hx
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]
      have huNeg : u x < 0 := lt_of_lt_of_le (hRegion x hxs) (neg_nonpos.mpr hm)
      have huAbs : m ≤ |u x| := by
        rw [abs_of_neg huNeg]
        linarith [hRegion x hxs]
      have hfNorm : m ≤ ‖f x‖ := by
        rw [hx, Real.norm_eq_abs]
        exact huAbs
      nlinarith [sq_nonneg (‖f x‖ - m)]
    · rw [Set.indicator_of_notMem hxs]
      exact sq_nonneg _
  calc
    m ^ 2 * Measure.real μ s =
        ∫ x : α, s.indicator (fun _ : α => m ^ 2) x ∂μ := by
      rw [integral_indicator hs, setIntegral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ ∫ x : α, ‖f x‖ ^ 2 ∂μ :=
      integral_mono_ae hIndInt hSqInt hAE
    _ = ‖f‖ ^ 2 := (realL2_norm_sq_eq_integral_norm_sq f).symm

local notation "GJA" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AJA_group : IsTopologicalGroup GJA :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AJA_compact : CompactSpace GJA :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AJA_countable : SecondCountableTopology GJA :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AJA_measurable : MeasurableSpace GJA :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AJA_borel : BorelSpace GJA :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgZ" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muZ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "PhysZ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fZ" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "NZ" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "uZ" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mZ" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJA_probability : IsProbabilityMeasure muZ := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The true original normalized physical source-image norm squared bounds
the explicit original squared margin times the REAL genuine Haar mass of
the unchanged strict negative region, for all finite H and beta>0. -/
theorem p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
    (beta : ℝ) (hbeta : 0 < beta) :
    (mZ beta hbeta.le) ^ 2 *
      Measure.real muZ
        {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)} ≤
      ‖NZ beta hbeta.le fZ‖ ^ 2 := by
  let s : Set CfgZ := {B | uZ beta hbeta.le B < -(mZ beta hbeta.le)}
  let f : Lp ℝ 2 muZ := ((NZ beta hbeta.le fZ : PhysZ) : Lp ℝ 2 muZ)
  have hs : MeasurableSet s := by
    change MeasurableSet
      {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)}
    rw [p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original H beta hbeta.le]
    exact p4Q2PZ37AIG_originalNegativeTransferRegion_measurable H beta
  have hBridge : (fun B : CfgZ => f B) =ᵐ[muZ] uZ beta hbeta.le := by
    simpa only [f] using
      (p4Q2PZ37AIW_originalNormalizedSourceTransfer_coeFn H beta hbeta.le)
  have hm : 0 ≤ mZ beta hbeta.le :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta).le
  have hBound :=
    realL2_norm_sq_ge_margin_sq_mul_realMeasure
      muZ f (uZ beta hbeta.le) s hs (mZ beta hbeta.le) hm
      hBridge (fun B hB => hB)
  simpa only [s, f] using hBound

/-- Both factors in the lower certificate are strictly positive at every
finite H and every positive coupling. No H-uniform estimate is inferred. -/
theorem p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 <
      (mZ beta hbeta.le) ^ 2 *
        Measure.real muZ
          {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)} := by
  have hm := p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta
  have hMass :
      0 < Measure.real muZ
        {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)} := by
    exact ENNReal.toReal_pos
      (p4Q2PZ37AIZ_originalNormalizedNegativeRegion_HaarMeasure_pos
        H beta hbeta).ne' (measure_ne_top muZ _)
  exact mul_pos (pow_pos hm 2) hMass

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Actual axiom audit for all new results; no surrogate proof axioms. -/
#print axioms MGAP4D.MathlibAnalytic.realL2_norm_sq_ge_margin_sq_mul_realMeasure
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos

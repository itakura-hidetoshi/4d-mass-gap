import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferOperatorNormVolumeDecayV5_PZ37AIV
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration

/-!
# P4-Q2-PZ37AIW — original spatial-mean normalization and negative margin

Preserve the ORIGINAL complete SU(2) Wilson action, both endpoint spatial
halfweights, genuine normalized Haar, signed ZW physical source, its original
continuous transfer representative, and all previous results, roots and pins.

The exact crossing-weighted first moment of each endpoint spatial action is
p_H * Zcross_H(beta). Integrating the elementary exponential tangent around
that exact mean gives
  exp(-beta*p_H) * Zcross_H(beta)
    <= integral K_beta d(pair Haar) <= ||P_beta|| <= Zcross_H(beta).
The middle integral is the literal complete ONE-SLAB FREE-BOUNDARY pair-Haar
partition and physical constant-unit-vector matrix coefficient. It is not the
periodic temporal trace partition, and it is not identified with ||P_beta||.
No new probability law or physical operator is introduced.

This strengthens AIV's lower exponent from 2*beta+rho to beta+rho and gives
  1 <= Zcross_H(beta)/||P_beta|| <= exp(beta*p_H).
The source integral divided by ||P_beta|| is proved to represent the EXISTING
normalized physical transfer almost everywhere; continuity and pointwise
inequalities refer to this explicitly chosen integral representative.

For the UNCHANGED original AIG certificate delta_H(beta), set only its scalar
normalized value m_H(beta)=delta_H(beta)/||P_beta||. Its exact relative factor
and the improved physical norm floor yield
  (beta/2)*V_H*exp(-2*beta*p_H) <= m_H(beta)
    <= (beta/2)*V_H*exp(-beta*p_H)
    <= (beta/8)*p_H^2*exp(-beta*p_H).
Thus m_H(beta)>0 for finite H and beta>0, while m_H(beta) tends to zero at
fixed positive beta as H grows. At the unchanged beta0=log(3/2)/64,
  m_H(beta0) <= 72*beta0*(H+1)^6*exp(-(H+1)^3/8).

The normalized strict negative sublevel at m_H is EXACTLY AIG's original set.
AIT's half-Haar statement, small positive normalized margin, and norm one of
the existing normalized physical operator therefore hold at a common cutoff.
The all-boundary normalized-source upper envelope is explicitly retained;
it can grow and is not used to infer decay of the normalized source image.

The certificate's limit does not establish vanishing of actual normalized
source amplitudes, absence of deeper negative regions, normalized coercivity,
a common-Hilbert-space limit, excitation/spectral bounds, a Hamiltonian gap,
or a continuum four-dimensional Yang--Mills mass gap. Different H keep their
original different boundary spaces and physical Hilbert spaces.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIW_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIW_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIW_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIW_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIW_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgW" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muW" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pairW" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "pW" => p4Q2PZ37AFZ_plaquetteCount H
local notation "WW" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "KCW" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "KW" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "PW" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
  H 2 (by norm_num)

local instance p4Q2PZ37AIW_probability : IsProbabilityMeasure muW := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

local instance p4Q2PZ37AIW_pair_probability : IsProbabilityMeasure pairW := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure]
  infer_instance

/-- The literal original spatial action has the already proved exact Haar
mean. The equality of the continuous representative and the action is
definitional; the physical Hilbert centering is explicitly bridged by AFZ. -/
theorem p4Q2PZ37AIW_originalSpatialWilsonAction_haarMean :
    (∫ A : CfgW, WW A ∂muW) = pW := by
  have hMean := p4Q2PZ37AGN_originalWilsonMean_exact H
  rw [p4Q2PZ37AFZ_originalWilsonMean_eq_integral H] at hMean
  exact hMean

/-- Compact continuity supplies joint integrability before the right Haar
variable is integrated out. -/
theorem p4Q2PZ37AIW_originalCrossing_leftAction_pair_integrable (beta : ℝ) :
    Integrable (fun P : CfgW × CfgW =>
      WW P.1 * KCW beta P.1 P.2) pairW := by
  have hW : Continuous (fun P : CfgW × CfgW => WW P.1) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2).comp
      continuous_fst
  have hKC : Continuous (fun P : CfgW × CfgW => KCW beta P.1 P.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous H 2 beta
  exact (hW.mul hKC).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The corresponding joint integrability for the unchanged right endpoint
spatial action. -/
theorem p4Q2PZ37AIW_originalCrossing_rightAction_pair_integrable (beta : ℝ) :
    Integrable (fun P : CfgW × CfgW =>
      WW P.2 * KCW beta P.1 P.2) pairW := by
  have hW : Continuous (fun P : CfgW × CfgW => WW P.2) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2).comp
      continuous_snd
  have hKC : Continuous (fun P : CfgW × CfgW => KCW beta P.1 P.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous H 2 beta
  exact (hW.mul hKC).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- AIF's right Haar identity shows that the crossing-weighted left action
has exactly its original Haar first moment times the genuine partition. -/
theorem p4Q2PZ37AIW_originalCrossing_leftAction_pair_integral (beta : ℝ) :
    (∫ P : CfgW × CfgW, WW P.1 * KCW beta P.1 P.2 ∂pairW) =
      pW * p4Q2PZ37AIF_originalCrossingPartition H beta := by
  change (∫ P : CfgW × CfgW,
    WW P.1 * KCW beta P.1 P.2 ∂(Measure.prod muW muW)) = _
  rw [integral_prod _
    (p4Q2PZ37AIW_originalCrossing_leftAction_pair_integrable H beta)]
  simp_rw [integral_const_mul, p4Q2PZ37AIF_originalCrossingKernel_haarIntegral H beta]
  rw [integral_mul_const, p4Q2PZ37AIW_originalSpatialWilsonAction_haarMean H]

/-- AIU's explicit symmetry bridge gives the other original Haar marginal.
Both endpoint first moments are obtained from the actual crossing kernel. -/
theorem p4Q2PZ37AIW_originalCrossing_rightAction_pair_integral
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ P : CfgW × CfgW, WW P.2 * KCW beta P.1 P.2 ∂pairW) =
      pW * p4Q2PZ37AIF_originalCrossingPartition H beta := by
  change (∫ P : CfgW × CfgW,
    WW P.2 * KCW beta P.1 P.2 ∂(Measure.prod muW muW)) = _
  rw [integral_prod_symm _
    (p4Q2PZ37AIW_originalCrossing_rightAction_pair_integrable H beta)]
  simp_rw [integral_const_mul,
    p4Q2PZ37AIU_originalCrossingKernel_leftHaarIntegral H beta hbeta]
  rw [integral_mul_const, p4Q2PZ37AIW_originalSpatialWilsonAction_haarMean H]

/-- The exponential tangent is centered at the exact pair crossing-weighted
spatial mean. Both original endpoint halfweights remain in the full kernel. -/
theorem p4Q2PZ37AIW_originalFullKernel_ge_spatialMeanTangent
    (beta : ℝ) (A B : CfgW) :
    Real.exp (-(beta * pW)) *
        ((1 + beta * pW) * KCW beta A B -
          (beta / 2) * (WW A * KCW beta A B + WW B * KCW beta A B)) ≤
      KW beta A B := by
  have hTangent := Real.add_one_le_exp
    (beta * pW - (beta / 2) * (WW A + WW B))
  have hKC : 0 ≤ KCW beta A B :=
    (p4Q2PZ37AIN_originalCrossingKernel_pos H beta A B).le
  have hExp :
      Real.exp (-(beta * pW)) *
          Real.exp (beta * pW - (beta / 2) * (WW A + WW B)) =
        Real.exp (-(beta / 2) * WW A) * Real.exp (-(beta / 2) * WW B) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-(beta * pW)) * KCW beta A B) *
        ((beta * pW - (beta / 2) * (WW A + WW B)) + 1) := by ring
    _ ≤ (Real.exp (-(beta * pW)) * KCW beta A B) *
        Real.exp (beta * pW - (beta / 2) * (WW A + WW B)) :=
      mul_le_mul_of_nonneg_left hTangent
        (mul_nonneg (Real.exp_pos _).le hKC)
    _ = KCW beta A B *
        (Real.exp (-(beta * pW)) *
          Real.exp (beta * pW - (beta / 2) * (WW A + WW B))) := by ring
    _ = KCW beta A B *
        (Real.exp (-(beta / 2) * WW A) * Real.exp (-(beta / 2) * WW B)) := by
      rw [hExp]
    _ = KW beta A B := by
      change KCW beta A B *
          (Real.exp (-(beta / 2) * WW A) * Real.exp (-(beta / 2) * WW B)) =
        Real.exp (-(beta / 2) * WW A) * KCW beta A B *
          Real.exp (-(beta / 2) * WW B)
      ring

/-- Integrating the tangent uses the two exact crossing-weighted first
moments. This is the literal pair-Haar partition of the original full kernel. -/
theorem p4Q2PZ37AIW_originalFullKernel_pair_integral_ge_spatialMean
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pW)) * p4Q2PZ37AIF_originalCrossingPartition H beta ≤
      ∫ P : CfgW × CfgW, KW beta P.1 P.2 ∂pairW := by
  have hKC := p4Q2PZ37AIV_originalCrossingKernel_pair_integrable H beta
  have hLeft := p4Q2PZ37AIW_originalCrossing_leftAction_pair_integrable H beta
  have hRight := p4Q2PZ37AIW_originalCrossing_rightAction_pair_integrable H beta
  have hSum : Integrable (fun P : CfgW × CfgW =>
      WW P.1 * KCW beta P.1 P.2 +
        WW P.2 * KCW beta P.1 P.2) pairW :=
    hLeft.fun_add hRight
  have hTangent : Integrable (fun P : CfgW × CfgW =>
      Real.exp (-(beta * pW)) *
        ((1 + beta * pW) * KCW beta P.1 P.2 -
          (beta / 2) *
            (WW P.1 * KCW beta P.1 P.2 + WW P.2 * KCW beta P.1 P.2))) pairW :=
    ((hKC.const_mul (1 + beta * pW)).sub
      (hSum.const_mul (beta / 2))).const_mul
        (Real.exp (-(beta * pW)))
  have hIntegral :
      (∫ P : CfgW × CfgW,
        Real.exp (-(beta * pW)) *
          ((1 + beta * pW) * KCW beta P.1 P.2 -
            (beta / 2) *
              (WW P.1 * KCW beta P.1 P.2 + WW P.2 * KCW beta P.1 P.2))
        ∂pairW) =
      Real.exp (-(beta * pW)) * p4Q2PZ37AIF_originalCrossingPartition H beta := by
    rw [integral_const_mul]
    rw [integral_sub (hKC.const_mul (1 + beta * pW))
      (hSum.const_mul (beta / 2))]
    rw [integral_const_mul, integral_const_mul, integral_add hLeft hRight,
      p4Q2PZ37AIV_originalCrossingKernel_pair_integral H beta,
      p4Q2PZ37AIW_originalCrossing_leftAction_pair_integral H beta,
      p4Q2PZ37AIW_originalCrossing_rightAction_pair_integral H beta hbeta]
    ring
  calc
    _ = _ := hIntegral.symm
    _ ≤ _ := integral_mono hTangent
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_integrable
        H 2 (by norm_num) beta hbeta)
      (fun P => p4Q2PZ37AIW_originalFullKernel_ge_spatialMeanTangent H beta P.1 P.2)

/-- The already-existing physical constant unit vector identifies the literal
original pair-Haar kernel integral as an actual physical matrix coefficient. -/
theorem p4Q2PZ37AIW_originalFullKernel_pair_integral_eq_constantExpectation
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ P : CfgW × CfgW, KW beta P.1 P.2 ∂pairW) =
      inner ℝ
        (PW beta hbeta (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) := by
  symm
  change inner ℝ
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta (Lp.const 2 muW (1 : ℝ)))
    (Lp.const 2 muW (1 : ℝ)) = _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_const_one_eq_integral]

/-- Cauchy--Schwarz and the operator norm applied to the same physical unit
vector give the Rayleigh lower estimate without a new spectral assumption. -/
theorem p4Q2PZ37AIW_originalFullKernel_pair_integral_le_physicalTransferNorm
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ P : CfgW × CfgW, KW beta P.1 P.2 ∂pairW) ≤ ‖PW beta hbeta‖ := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hu : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  rw [p4Q2PZ37AIW_originalFullKernel_pair_integral_eq_constantExpectation H beta hbeta]
  change inner ℝ (PW beta hbeta u) u ≤ ‖PW beta hbeta‖
  calc
    _ ≤ ‖PW beta hbeta u‖ * ‖u‖ := real_inner_le_norm _ _
    _ ≤ (‖PW beta hbeta‖ * ‖u‖) * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm (PW beta hbeta) u) (norm_nonneg u)
    _ = ‖PW beta hbeta‖ := by rw [hu]; ring

/-- Sharper unconditional finite-volume norm floor for the existing original
physical transfer, retaining both original spatial halfweights and genuine
Haar. The exponent beta*p_H uses their exact combined first moment. -/
theorem p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pW)) * p4Q2PZ37AIF_originalCrossingPartition H beta ≤
      ‖PW beta hbeta‖ :=
  (p4Q2PZ37AIW_originalFullKernel_pair_integral_ge_spatialMean H beta hbeta).trans
    (p4Q2PZ37AIW_originalFullKernel_pair_integral_le_physicalTransferNorm H beta hbeta)

/-- The original literal source transfer divided by the already-existing
positive physical norm. Its relation to the existing normalized operator is
proved below, rather than assumed from the scalar notation. -/
def p4Q2PZ37AIW_originalNormalizedSourceTransfer
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : CfgW) : ℝ :=
  decomposableOneSliceTransferIntegral H 2 beta
    (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B / ‖PW beta hbeta‖

/-- The unchanged original AIG certificate scaled by exactly the same
existing physical norm as the normalized source image. -/
def p4Q2PZ37AIW_originalNormalizedNegativeMargin
    (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  p4Q2PZ37AIG_originalNegativeTransferMargin H beta / ‖PW beta hbeta‖

section PZ37AIWNormalizedSourceBridge

variable (H : ℕ)

local notation "CfgAIWBridge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muAIWBridge" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "PhysAIWBridge" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "PAIWBridge" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2
local notation "NAIWBridge" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2

/-- The unchanged Gauss-law physical transfer has the original literal
Wilson integral as an actual Haar-a.e. representative. The multiplication
order in the pre-existing ambient integral API is reconciled explicitly. -/
theorem p4Q2PZ37AIW_originalPhysicalTransfer_coeFn
    (beta : ℝ) (hbeta : 0 ≤ beta) (f : PhysAIWBridge) :
    (fun B : CfgAIWBridge =>
      ((PAIWBridge (by norm_num) beta hbeta f : PhysAIWBridge) :
        Lp ℝ 2 muAIWBridge) B) =ᵐ[muAIWBridge]
      decomposableOneSliceTransferIntegral H 2 beta f := by
  change
    (fun B : CfgAIWBridge =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta (f : Lp ℝ 2 muAIWBridge) B) =ᵐ[muAIWBridge]
      decomposableOneSliceTransferIntegral H 2 beta f
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
      H 2 (by norm_num) beta hbeta (f : Lp ℝ 2 muAIWBridge)] with B hB
  simpa only
    [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative,
      decomposableOneSliceTransferIntegral, mul_comm] using hB

/-- For every genuine physical input, divide the original integral by the
existing positive physical top norm. The result represents the ALREADY
DEFINED normalized physical operator; no new operator is substituted. -/
theorem p4Q2PZ37AIW_existingNormalizedPhysicalTransfer_coeFn
    (beta : ℝ) (hbeta : 0 ≤ beta) (f : PhysAIWBridge) :
    (fun B : CfgAIWBridge =>
      ((NAIWBridge (by norm_num) beta hbeta f : PhysAIWBridge) :
        Lp ℝ 2 muAIWBridge) B) =ᵐ[muAIWBridge]
      (fun B : CfgAIWBridge =>
        decomposableOneSliceTransferIntegral H 2 beta f B /
          ‖PAIWBridge (by norm_num) beta hbeta‖) := by
  let P := PAIWBridge (by norm_num) beta hbeta
  have hRaw := p4Q2PZ37AIW_originalPhysicalTransfer_coeFn H beta hbeta f
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply]
  change
    (fun B : CfgAIWBridge =>
      (‖P‖⁻¹ • ((P f : PhysAIWBridge) : Lp ℝ 2 muAIWBridge)) B) =ᵐ[muAIWBridge]
      (fun B : CfgAIWBridge =>
        decomposableOneSliceTransferIntegral H 2 beta f B / ‖P‖)
  filter_upwards
    [Lp.coeFn_smul ‖P‖⁻¹ ((P f : PhysAIWBridge) : Lp ℝ 2 muAIWBridge), hRaw]
    with B hSmul hRawB
  calc
    (‖P‖⁻¹ • ((P f : PhysAIWBridge) : Lp ℝ 2 muAIWBridge)) B =
        ‖P‖⁻¹ * (((P f : PhysAIWBridge) : Lp ℝ 2 muAIWBridge) B) := by
          simpa only [Pi.smul_apply, smul_eq_mul] using hSmul
    _ = ‖P‖⁻¹ * decomposableOneSliceTransferIntegral H 2 beta f B := by
      rw [hRawB]
    _ = decomposableOneSliceTransferIntegral H 2 beta f B / ‖P‖ := by
      rw [div_eq_mul_inv, mul_comm]

/-- Specialize the exact operator/representative bridge to the SAME original
ZW centered Gauss-law physical source used throughout AIG--AIV. -/
theorem p4Q2PZ37AIW_originalNormalizedSourceTransfer_coeFn
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun B : CfgAIWBridge =>
      ((NAIWBridge (by norm_num) beta hbeta
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) : PhysAIWBridge) :
        Lp ℝ 2 muAIWBridge) B) =ᵐ[muAIWBridge]
      p4Q2PZ37AIW_originalNormalizedSourceTransfer H beta hbeta := by
  simpa only [p4Q2PZ37AIW_originalNormalizedSourceTransfer] using
    p4Q2PZ37AIW_existingNormalizedPhysicalTransfer_coeFn H beta hbeta
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

/-- Continuity is for the specified integral representative. It does not
assert continuity of an arbitrary representative of the output L2 class. -/
theorem p4Q2PZ37AIW_originalNormalizedSourceTransfer_continuous
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Continuous (p4Q2PZ37AIW_originalNormalizedSourceTransfer H beta hbeta) := by
  exact (p4Q2PZ37AIG_originalTransfer_continuous H beta).div_const _

/-- A positive scalar normalization preserves the sign at every original
right boundary of the specified continuous integral representative. -/
theorem p4Q2PZ37AIW_originalNormalizedSourceTransfer_neg_iff
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : CfgAIWBridge) :
    p4Q2PZ37AIW_originalNormalizedSourceTransfer H beta hbeta B < 0 ↔
      decomposableOneSliceTransferIntegral H 2 beta
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B < 0 := by
  have hNorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  change
    decomposableOneSliceTransferIntegral H 2 beta
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B /
        ‖PAIWBridge (by norm_num) beta hbeta‖ < 0 ↔ _
  rw [div_lt_iff₀ hNorm, zero_mul]

/-- Normalize the original margin by exactly the same physical top norm.
The strict inequality is equivalent to the unchanged original inequality. -/
theorem p4Q2PZ37AIW_originalNormalizedSourceTransfer_lt_negativeMargin_iff
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : CfgAIWBridge) :
    p4Q2PZ37AIW_originalNormalizedSourceTransfer H beta hbeta B <
        -(p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta) ↔
      decomposableOneSliceTransferIntegral H 2 beta
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B <
        -(p4Q2PZ37AIG_originalNegativeTransferMargin H beta) := by
  have hNorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  change
    decomposableOneSliceTransferIntegral H 2 beta
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B /
      ‖PAIWBridge (by norm_num) beta hbeta‖ <
        -(p4Q2PZ37AIG_originalNegativeTransferMargin H beta /
          ‖PAIWBridge (by norm_num) beta hbeta‖) ↔ _
  rw [← neg_div, div_lt_div_iff_of_pos_right hNorm]

/-- The normalized strict negative region is literally AIG's ORIGINAL
region. No shrinking of the original margin or change of Haar measure occurs. -/
theorem p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    {B : CfgAIWBridge |
      p4Q2PZ37AIW_originalNormalizedSourceTransfer H beta hbeta B <
        -(p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta)} =
      p4Q2PZ37AIG_originalNegativeTransferRegion H beta := by
  ext B
  exact p4Q2PZ37AIW_originalNormalizedSourceTransfer_lt_negativeMargin_iff
    H beta hbeta B

end PZ37AIWNormalizedSourceBridge

section PZ37AIWRelativeEstimates

local notation "pAIW" => p4Q2PZ37AFZ_plaquetteCount
local notation "ZAIW" => p4Q2PZ37AIF_originalCrossingPartition
local notation "VAIW" => p4Q2PZ37AHN_originalSource_HaarSecondMoment
local notation "rhoAIW" => p4Q2PZ37AIU_originalPartitionDecayRate
local notation "PAIW" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
local notation "NAIW" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator

/-- The existing physical norm divided by the genuine crossing partition
retains the spatial mean floor. This ratio does not replace either operator. -/
theorem p4Q2PZ37AIW_originalNorm_div_crossingPartition_bounds
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pAIW H)) ≤
        ‖PAIW H 2 (by norm_num) beta hbeta‖ / ZAIW H beta ∧
      ‖PAIW H 2 (by norm_num) beta hbeta‖ / ZAIW H beta ≤ 1 := by
  have hZ := p4Q2PZ37AIF_originalCrossingPartition_pos H beta
  constructor
  · exact (le_div_iff₀ hZ).2
      (p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean H beta hbeta)
  · apply (div_le_iff₀ hZ).2
    simpa only [one_mul] using
      p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_crossingPartition H beta hbeta

/-- The factor remaining after cancellation of the genuine crossing
partition lies between one and exp(beta*pH). Both endpoint halfweights
remain in the physical norm in the denominator. -/
theorem p4Q2PZ37AIW_originalCrossingPartition_div_norm_bounds
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    1 ≤ ZAIW H beta / ‖PAIW H 2 (by norm_num) beta hbeta‖ ∧
      ZAIW H beta / ‖PAIW H 2 (by norm_num) beta hbeta‖ ≤
        Real.exp (beta * pAIW H) := by
  have hNorm := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    H 2 (by norm_num) beta hbeta
  constructor
  · apply (le_div_iff₀ hNorm).2
    simpa only [one_mul] using
      p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_crossingPartition H beta hbeta
  · apply (div_le_iff₀ hNorm).2
    have hCancel : Real.exp (beta * pAIW H) * Real.exp (-(beta * pAIW H)) = 1 := by
      rw [← Real.exp_add]
      simp only [add_neg_cancel, Real.exp_zero]
    calc
      ZAIW H beta = Real.exp (beta * pAIW H) *
          (Real.exp (-(beta * pAIW H)) * ZAIW H beta) := by
        rw [← mul_assoc, hCancel, one_mul]
      _ ≤ Real.exp (beta * pAIW H) *
          ‖PAIW H 2 (by norm_num) beta hbeta‖ :=
        mul_le_mul_of_nonneg_left
          (p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean H beta hbeta)
          (Real.exp_pos _).le

/-- The spatial mean improves the lower exponent from AIV's 2*beta+rho
to beta+rho, for the same original physical transfer at every finite volume. -/
theorem p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_improvedRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-((beta + rhoAIW beta) * pAIW H)) ≤
      ‖PAIW H 2 (by norm_num) beta hbeta‖ := by
  have h := p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean H beta hbeta
  rw [p4Q2PZ37AIU_originalCrossingPartition_eq_exp_rate H beta, ← Real.exp_add] at h
  have hShape : -(beta * pAIW H) + -(rhoAIW beta * pAIW H) =
      -((beta + rhoAIW beta) * pAIW H) := by ring
  rwa [hShape] at h

/-- A tighter upper bound on the inverse norm used by the already-existing
normalized physical transfer. The original lower bound is retained. -/
theorem p4Q2PZ37AIW_originalInverseNormalization_bounds
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (rhoAIW beta * pAIW H) ≤
        ‖PAIW H 2 (by norm_num) beta hbeta‖⁻¹ ∧
      ‖PAIW H 2 (by norm_num) beta hbeta‖⁻¹ ≤
        Real.exp ((beta + rhoAIW beta) * pAIW H) := by
  refine ⟨p4Q2PZ37AIV_originalPhysicalTransfer_inverseNorm_ge_exactRate H beta hbeta, ?_⟩
  have hNorm := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    H 2 (by norm_num) beta hbeta
  have h := (inv_le_inv₀ hNorm
    (Real.exp_pos (-((beta + rhoAIW beta) * pAIW H)))).2
    (p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_improvedRate H beta hbeta)
  simpa only [Real.exp_neg, inv_inv] using h

/-- Exact factorization of the unchanged AIG margin under the existing
physical norm normalization. The genuine crossing partition is retained
inside the relative factor rather than silently discarded. -/
theorem p4Q2PZ37AIW_originalNormalizedNegativeMargin_eq_relativeFactor
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta =
      (beta * Real.exp (-(2 * beta * pAIW H)) * VAIW H / 2) *
        (ZAIW H beta / ‖PAIW H 2 (by norm_num) beta hbeta‖) := by
  unfold p4Q2PZ37AIW_originalNormalizedNegativeMargin
    p4Q2PZ37AIG_originalNegativeTransferMargin
  ring

/-- Strict positivity is finite-volume positivity of the original margin
divided by the original positive physical norm. -/
theorem p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    0 < p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta.le := by
  exact div_pos (p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le)

/-- The partition-cancelled original margin has explicit two-sided
spatial-weight bounds. Neither bound is asserted to be volume uniform. -/
theorem p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    beta * Real.exp (-(2 * beta * pAIW H)) * VAIW H / 2 ≤
        p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta ∧
      p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta ≤
        beta * Real.exp (-(beta * pAIW H)) * VAIW H / 2 := by
  have hRatio := p4Q2PZ37AIW_originalCrossingPartition_div_norm_bounds H beta hbeta
  have hV : 0 ≤ VAIW H := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le
  have hFactor : 0 ≤ beta * Real.exp (-(2 * beta * pAIW H)) * VAIW H / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hbeta (Real.exp_pos _).le) hV) (by norm_num)
  rw [p4Q2PZ37AIW_originalNormalizedNegativeMargin_eq_relativeFactor H beta hbeta]
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hRatio.1 hFactor
  · have hExp : Real.exp (-(2 * beta * pAIW H)) * Real.exp (beta * pAIW H) =
        Real.exp (-(beta * pAIW H)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (beta * Real.exp (-(2 * beta * pAIW H)) * VAIW H / 2) *
          Real.exp (beta * pAIW H) := mul_le_mul_of_nonneg_left hRatio.2 hFactor
      _ = beta *
          (Real.exp (-(2 * beta * pAIW H)) * Real.exp (beta * pAIW H)) * VAIW H / 2 := by ring
      _ = _ := by rw [hExp]

/-- A count-only upper envelope survives the existing physical norm
normalization, with a positive exponential rate at every fixed beta>0. -/
theorem p4Q2PZ37AIW_originalNormalizedNegativeMargin_le_countEnvelope
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta ≤
      (beta / 8) * ((pAIW H) ^ 2 * Real.exp (-(beta * pAIW H))) := by
  have hVariance := p4Q2PZ37AIS_originalSourceSecondMoment_le_countSquare H
  calc
    _ ≤ beta * Real.exp (-(beta * pAIW H)) * VAIW H / 2 :=
      (p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds H beta hbeta).2
    _ ≤ beta * Real.exp (-(beta * pAIW H)) * ((pAIW H) ^ 2 / 4) / 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hVariance
          (mul_nonneg hbeta (Real.exp_pos _).le)) (by norm_num)
    _ = _ := by ring

/-- An honest all-boundary estimate for the actual norm-normalized source
image. This upper envelope can grow with volume and is not a decay claim. -/
theorem p4Q2PZ37AIW_originalNormalizedSourceTransfer_abs_le_relativeEnvelope
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |p4Q2PZ37AIW_originalNormalizedSourceTransfer H beta hbeta B| ≤
      (pAIW H / 2) *
        (ZAIW H beta / ‖PAIW H 2 (by norm_num) beta hbeta‖) := by
  have hNorm := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    H 2 (by norm_num) beta hbeta
  unfold p4Q2PZ37AIW_originalNormalizedSourceTransfer
  rw [abs_div, abs_of_pos hNorm]
  calc
    _ ≤ ((pAIW H / 2) * ZAIW H beta) /
        ‖PAIW H 2 (by norm_num) beta hbeta‖ :=
      div_le_div_of_nonneg_right
        (p4Q2PZ37AIU_originalTransfer_abs_le_crossingEnvelope H beta hbeta B) hNorm.le
    _ = _ := by ring

theorem p4Q2PZ37AIW_originalNormalizedSourceTransfer_abs_le_spatialEnvelope
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |p4Q2PZ37AIW_originalNormalizedSourceTransfer H beta hbeta B| ≤
      (pAIW H / 2) * Real.exp (beta * pAIW H) :=
  (p4Q2PZ37AIW_originalNormalizedSourceTransfer_abs_le_relativeEnvelope H beta hbeta B).trans
    (mul_le_mul_of_nonneg_left
      (p4Q2PZ37AIW_originalCrossingPartition_div_norm_bounds H beta hbeta).2
      (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num)))

section PZ37AIWVolume

open Filter
open scoped Topology

/-- The ORIGINAL AIG certificate divided by the EXISTING physical norm
tends to zero at fixed positive coupling. This concerns the certificate;
it does not imply that the normalized source image tends to zero. -/
theorem p4Q2PZ37AIW_originalNormalizedNegativeMargin_tendsto_zero
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun H : ℕ => p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta.le)
      atTop (𝓝 0) := by
  have hEnvelope : Tendsto (fun H : ℕ =>
      (beta / 8) * ((pAIW H) ^ 2 * Real.exp (-(beta * pAIW H)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (p4Q2PZ37AIT_originalCountSquareExp_tendsto_zero beta hbeta).const_mul (beta / 8)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hEnvelope
    (fun H => (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta).le)
    (fun H => p4Q2PZ37AIW_originalNormalizedNegativeMargin_le_countEnvelope H beta hbeta.le)

/-- At one common cutoff, the SAME original negative region retains at
least half the genuine Haar mass, its normalized original certificate is
positive and arbitrarily small, and the existing normalized operator has
norm exactly one. No source-image or spectral asymptotic is substituted. -/
theorem p4Q2PZ37AIW_originalNormalizedHalfHaar_with_smallMargin
    (beta : ℝ) (hbeta : 0 < beta) (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ H : ℕ, N ≤ H →
      (1 / 2 : ℝ) ≤ Measure.real
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
        {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 |
          p4Q2PZ37AIW_originalNormalizedSourceTransfer H beta hbeta.le B <
            -(p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta.le)} ∧
      0 < p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta.le ∧
      p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta.le < eta ∧
      ‖NAIW H 2 (by norm_num) beta hbeta.le‖ = 1 := by
  obtain ⟨N₁, hN₁⟩ :=
    p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_eventually beta hbeta
  have hMargin : ∀ᶠ H : ℕ in atTop,
      p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta hbeta.le < eta :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_tendsto_zero beta hbeta).eventually
      (gt_mem_nhds heta)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hMargin
  refine ⟨max N₁ N₂, fun H hH => ?_⟩
  have hSet := p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original H beta hbeta.le
  rw [hSet]
  exact ⟨hN₁ H ((le_max_left _ _).trans hH),
    p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta,
    hN₂ H ((le_max_right _ _).trans hH),
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
      H 2 (by norm_num) beta hbeta.le⟩

end PZ37AIWVolume

/-- At the unchanged beta0 the normalized original certificate has an
explicit cubic exponential bound, retaining the polynomial variance factor. -/
theorem p4Q2PZ37AIW_originalFixedNormalizedMargin_le_explicitVolumeBound
    (H : ℕ) :
    p4Q2PZ37AIW_originalNormalizedNegativeMargin H p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos.le ≤
      72 * p4Q2PZ37ADC_fixedCoupling * ((H : ℝ) + 1) ^ 6 *
        Real.exp (-(((H : ℝ) + 1) ^ 3 / 8)) := by
  have hRate : ((H : ℝ) + 1) ^ 3 / 8 ≤ p4Q2PZ37ADC_fixedCoupling * pAIW H := by
    calc
      ((H : ℝ) + 1) ^ 3 / 8 = (1 / 192 : ℝ) * pAIW H := by
        rw [p4Q2PZ37AIB_plaquetteCount_exact H]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right p4Q2PZ37AIB_fixedCoupling_rationalInterval.1
        (p4Q2PZ37AHN_count_pos H).le
  calc
    _ ≤ (p4Q2PZ37ADC_fixedCoupling / 8) *
        ((pAIW H) ^ 2 * Real.exp (-(p4Q2PZ37ADC_fixedCoupling * pAIW H))) :=
      p4Q2PZ37AIW_originalNormalizedNegativeMargin_le_countEnvelope H
        p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
    _ ≤ (p4Q2PZ37ADC_fixedCoupling / 8) *
        ((pAIW H) ^ 2 * Real.exp (-(((H : ℝ) + 1) ^ 3 / 8))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hRate)) (sq_nonneg _))
        (div_nonneg p4Q2PZ37ADC_fixedCoupling_pos.le (by norm_num))
    _ = _ := by
      rw [p4Q2PZ37AIB_plaquetteCount_exact H]
      ring

end PZ37AIWRelativeEstimates

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Every new theorem and scalar definition has an explicit axiom audit. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalSpatialWilsonAction_haarMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossing_leftAction_pair_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossing_rightAction_pair_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossing_leftAction_pair_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossing_rightAction_pair_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFullKernel_ge_spatialMeanTangent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFullKernel_pair_integral_ge_spatialMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFullKernel_pair_integral_eq_constantExpectation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFullKernel_pair_integral_le_physicalTransferNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalPhysicalTransfer_coeFn
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_existingNormalizedPhysicalTransfer_coeFn
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_coeFn
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_neg_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_lt_negativeMargin_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNorm_div_crossingPartition_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossingPartition_div_norm_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_improvedRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalInverseNormalization_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_eq_relativeFactor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_le_countEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_abs_le_relativeEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_abs_le_spatialEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedHalfHaar_with_smallMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFixedNormalizedMargin_le_explicitVolumeBound

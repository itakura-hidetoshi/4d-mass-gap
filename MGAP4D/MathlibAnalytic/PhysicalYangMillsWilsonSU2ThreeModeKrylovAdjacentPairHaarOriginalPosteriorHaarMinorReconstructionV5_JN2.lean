import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDensityMinorTaylorV5_JN
import Mathlib.Tactic

/-!
# P4-Q2-JN2: actual interacting Wilson density difference recovered by SU(2) Haar integration

The JN genuine UNLOGGED two-posterior SU(2) density determinant has an
exact first-order temporal Wilson expansion. To transport it from a
two-point minor to the original physical density DIFFERENCE, we first
prove that EACH genuine normalized interacting Wilson posterior density
integrates to exactly one with respect to its legitimate normalized
SU(2) Haar REFERENCE measure.

This is an identity for the ORIGINAL Wilson posteriors (including the
Perron vacuum and full partition factors); the conditional laws are
not substituted by independent Haar laws.

Consequently integrating the original two-context density 2x2 minor
in its second physical inserted SU(2) variable EXACTLY recovers the
original density contrast p0_b(g)-p1_b(g). An abstract compact
probability argument transfers any UNIFORM minor Taylor error into
the same error bound for the reconstructed actual density contrast
against the centered temporal Wilson action.

The remaining work for the strong derivative is to supply JN's
explicit O(b²) minor error to the norm-integral bound uniformly, and
then pass to C(SU2,R) / Haar-L2. No unproved vacuum differentiability,
Dobrushin, continuum YM construction or 4D mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JN2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JN2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JN2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JN2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JN2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The original compact normalized-exponential posterior integrates to ONE
against the reference probability, including its actual partition mass.
The reference measure is NOT the conditional law itself. -/
theorem p4Q2JN2_continuousNormalizedExp_integral_eq_one
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (logWeight : X → ℝ) (hcont : Continuous logWeight) :
    (∫ x, continuousNormalizedExp μ logWeight x ∂μ) = 1 := by
  have hZ : 0 < continuousExpPartition μ logWeight :=
    continuousExpPartition_pos μ logWeight hcont
  change (∫ x, Real.exp (logWeight x) /
    continuousExpPartition μ logWeight ∂μ) = 1
  simp only [div_eq_mul_inv]
  rw [integral_mul_const]
  change continuousExpPartition μ logWeight *
    (continuousExpPartition μ logWeight)⁻¹ = 1
  exact mul_inv_cancel₀ hZ.ne'

section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast

/-- Actual ORIGINAL identity-left posterior as a compact continuous
SU(2) Haar-integrable density function. -/
noncomputable def p4Q2JN2_originalPosteriorIdentityContinuous
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) : C(Gauge, ℝ) := by
  refine ⟨p4Q2JN_originalPosteriorIdentityDensity H b hb right e, ?_⟩
  change Continuous (continuousNormalizedExp nu
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) b hb
      (originalWilsonExplicitIdentityBoundary H) right e))
  exact continuous_continuousNormalizedExp nu _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) b hb
      (originalWilsonExplicitIdentityBoundary H) right e)

/-- Actual ORIGINAL pi-left posterior as a compact continuous
SU(2) Haar-integrable density function. -/
noncomputable def p4Q2JN2_originalPosteriorPiContinuous
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) : C(Gauge, ℝ) := by
  refine ⟨p4Q2JN_originalPosteriorPiDensity H b hb right e, ?_⟩
  change Continuous (continuousNormalizedExp nu
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) b hb
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e))
  exact continuous_continuousNormalizedExp nu _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) b hb
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e)

/-- Each of the TWO genuine physical interacting SU(2) Wilson
conditional posterior densities integrates to precisely ONE. -/
theorem p4Q2JN2_bothOriginalPosteriorHaarIntegrals_one
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    (∫ g : Gauge,
      p4Q2JN_originalPosteriorIdentityDensity H b hb right e g ∂nu) = 1 ∧
    (∫ g : Gauge,
      p4Q2JN_originalPosteriorPiDensity H b hb right e g ∂nu) = 1 := by
  let l0 : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) b hb
      (originalWilsonExplicitIdentityBoundary H) right e
  let l1 : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) b hb
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  have h0 : Continuous l0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) b hb
      (originalWilsonExplicitIdentityBoundary H) right e
  have h1 : Continuous l1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) b hb
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  constructor
  · have hi := p4Q2JN2_continuousNormalizedExp_integral_eq_one nu l0 h0
    exact hi
  · have hi := p4Q2JN2_continuousNormalizedExp_integral_eq_one nu l1 h1
    exact hi

/-- Fundamental non-perturbative Haar reconstruction: the integral of
the genuine ORIGINAL SU(2) two-posterior density minor at fixed first
right-link value g equals the actual original density contrast at g.
The physical posteriors themselves remain interacting Wilson laws. -/
theorem p4Q2JN2_originalDensityContrast_eq_minorHaarIntegral
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) (g : Gauge) :
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g =
      ∫ h : Gauge,
        p4Q2JN_originalPosteriorTwoPointMinor H b hb right e g h ∂nu := by
  let P0 := p4Q2JN2_originalPosteriorIdentityContinuous H b hb right e
  let P1 := p4Q2JN2_originalPosteriorPiContinuous H b hb right e
  have hI0 : Integrable (fun h : Gauge => P0 h) nu :=
    P0.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hI1 : Integrable (fun h : Gauge => P1 h) nu :=
    P1.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOne := p4Q2JN2_bothOriginalPosteriorHaarIntegrals_one
    H b hb right e
  have h0 : (∫ h : Gauge, P0 h ∂nu) = 1 := hOne.1
  have h1 : (∫ h : Gauge, P1 h ∂nu) = 1 := hOne.2
  change P0 g - P1 g =
    ∫ h : Gauge, P0 g * P1 h - P0 h * P1 g ∂nu
  symm
  calc
    (∫ h : Gauge, P0 g * P1 h - P0 h * P1 g ∂nu) =
        (∫ h : Gauge, P0 g * P1 h ∂nu) -
        (∫ h : Gauge, P0 h * P1 g ∂nu) := by
      exact integral_sub (hI1.const_mul _) (hI0.mul_const _)
    _ = P0 g * (∫ h : Gauge, P1 h ∂nu) -
        (∫ h : Gauge, P0 h ∂nu) * P1 g := by
      rw [integral_const_mul, integral_mul_const]
    _ = P0 g - P1 g := by rw [h0, h1]; ring

/-- A precise SU(2) Haar integral for the original temporal Wilson
energy difference at a fixed first physical right-link insertion g. -/
theorem p4Q2JN2_originalTemporalDifferenceHaarIntegral
    (g : Gauge) :
    (∫ h : Gauge, (D g - D h) ∂nu) =
      D g - (∫ h : Gauge, D h ∂nu) := by
  have hDInt : Integrable D nu :=
    p4Q2FZ_originalSU2TemporalWilsonContrast_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (integrable_const _) hDInt]
  simp

/-- Uniform control of any minor approximation transfers to the
ORIGINAL interacting Wilson density difference by its exact Haar
reconstruction, and the true Haar-centering of the temporal action.
The assumed bound is a genuinely pointwise estimate and is supplied
by JN's verified quadratic physical minor expansion in the next step. -/
theorem p4Q2JN2_densityContrast_error_le_of_minor_error
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (C : ℝ)
    (hMinorErr : ∀ g h : Gauge,
      ‖p4Q2JN_originalPosteriorTwoPointMinor H b hb right e g h +
        b * (D g - D h)‖ ≤ C)
    (g : Gauge) :
    ‖p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g +
      b * (D g - ∫ h : Gauge, D h ∂nu)‖ ≤ C := by
  let P0 := p4Q2JN2_originalPosteriorIdentityContinuous H b hb right e
  let P1 := p4Q2JN2_originalPosteriorPiContinuous H b hb right e
  let M : Gauge → ℝ := fun h => P0 g * P1 h - P0 h * P1 g
  let E : Gauge → ℝ := fun h => M h + b * (D g - D h)
  have hMCont : Continuous M :=
    (continuous_const.mul P1.continuous).sub
      (P0.continuous.mul continuous_const)
  have hECont : Continuous E := by
    exact hMCont.add (continuous_const.mul
      (continuous_const.sub
        p4Q2FZ_originalSU2TemporalWilsonContrast_continuous))
  have hMInt : Integrable M nu :=
    hMCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hTInt : Integrable (fun h : Gauge => b * (D g - D h)) nu :=
    (continuous_const.mul
      (continuous_const.sub
        p4Q2FZ_originalSU2TemporalWilsonContrast_continuous))
      .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRecon := p4Q2JN2_originalDensityContrast_eq_minorHaarIntegral
    H b hb right e g
  have hT :=
    p4Q2JN2_originalTemporalDifferenceHaarIntegral g
  have hEIntegral :
      (∫ h : Gauge, E h ∂nu) =
        p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g +
          b * (D g - ∫ h : Gauge, D h ∂nu) := by
    change (∫ h : Gauge, M h + b * (D g - D h) ∂nu) = _
    rw [integral_add hMInt hTInt, integral_const_mul, hT]
    rw [hRecon]
    rfl
  have hBound (h : Gauge) : ‖E h‖ ≤ C := by
    exact hMinorErr g h
  have hIntegralBound : ‖∫ h : Gauge, E h ∂nu‖ ≤ C := by
    have h := norm_integral_le_of_norm_le_const
      (μ := nu) (Filter.Eventually.of_forall hBound)
    simpa using h
  rw [hEIntegral] at hIntegralBound
  exact hIntegralBound


/-- The exact unlogged physical Wilson two-context minor estimate
from JN gives a UNIFORM source-free first-order bound on the ORIGINAL
interacting posterior density contrast itself. At finite b no
conditional Wilson law is replaced, and no vacuum derivative is used. -/
theorem p4Q2JN2_actualDensityContrast_centeredTaylor_explicit
    (b : ℝ) (hb : 0 ≤ b) (hsmall : b ≤ 1 / 4)
    (right : Cfg) (e : Link) (g : Gauge) :
    ‖p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g +
      b * (D g - ∫ h : Gauge, D h ∂nu)‖ ≤
      (16 * b ^ 2) * Real.exp (32 * b) +
        (4 * b) * (Real.exp (32 * b) - Real.exp (-32 * b)) := by
  apply p4Q2JN2_densityContrast_error_le_of_minor_error H b hb right e
    ((16 * b ^ 2) * Real.exp (32 * b) +
      (4 * b) * (Real.exp (32 * b) - Real.exp (-32 * b))) ?_ g
  intro g h
  have hTaylor := p4Q2JN_originalPosteriorMinor_unweightedTaylor_uniform
    H b hb hsmall right e g h
  have hD := p4Q2JN_temporalWilsonDifference_abs_le_four g h
  have hAbs : |b * (D g - D h)| ≤ 4 * b := by
    rw [abs_mul, abs_of_nonneg hb]
    calc
      b * |D g - D h| ≤ b * 4 :=
        mul_le_mul_of_nonneg_left hD hb
      _ = 4 * b := by ring
  have hPow : (b * (D g - D h)) ^ 2 ≤ 16 * b ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hAbs 2
    have h' : (b * (D g - D h)) ^ 2 ≤ (4 * b) ^ 2 := by
      simpa only [sq_abs] using h
    nlinarith
  have hGap : 0 ≤ Real.exp (32 * b) - Real.exp (-32 * b) := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hA :
      (b * (D g - D h)) ^ 2 * Real.exp (32 * b) ≤
      (16 * b ^ 2) * Real.exp (32 * b) :=
    mul_le_mul_of_nonneg_right hPow (Real.exp_pos _).le
  have hB :
      |b * (D g - D h)| *
        (Real.exp (32 * b) - Real.exp (-32 * b)) ≤
      (4 * b) * (Real.exp (32 * b) - Real.exp (-32 * b)) :=
    mul_le_mul_of_nonneg_right hAbs hGap
  have hEq :
      p4Q2JN_originalPosteriorTwoPointMinor H b hb right e g h +
        b * (D g - D h) =
      p4Q2JN_originalPosteriorTwoPointMinor H b hb right e g h -
        (-b * (D g - D h)) := by ring
  rw [hEq]
  exact hTaylor.trans (add_le_add hA hB)


/-- A pure real-exponential inequality turning the genuine Wilson
posterior density-crossing envelope into a quadratic weak-coupling
bound, without any lattice-volume or physical-vacuum hypothesis. -/
theorem p4Q2JN2_trueWilsonExpGap_le
    (b : ℝ) (hb : 0 ≤ b) :
    Real.exp (32 * b) - Real.exp (-32 * b) ≤
      (64 * b) * Real.exp (32 * b) := by
  have hExp := Real.add_one_le_exp (-64 * b)
  have hOne : (1 : ℝ) - Real.exp (-64 * b) ≤ 64 * b := by
    linarith
  have hFactor :
      Real.exp (32 * b) - Real.exp (-32 * b) =
      Real.exp (32 * b) * (1 - Real.exp (-64 * b)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  rw [hFactor]
  calc
    Real.exp (32 * b) * (1 - Real.exp (-64 * b)) ≤
      Real.exp (32 * b) * (64 * b) :=
      mul_le_mul_of_nonneg_left hOne (Real.exp_pos _).le
    _ = (64 * b) * Real.exp (32 * b) := by ring

/-- TRUE UNLOGGED ORIGINAL interacting posterior density difference,
at every physical finite SU(2) right background and link, has a
uniformly quadratic first-order remainder with explicit constant
272 exp(8). Crucially the first-order vector is the centered
temporal SU(2) Wilson action, and no differentiability of either
original normalized posterior or Perron vacuum is assumed. -/
theorem p4Q2JN2_actualDensityContrast_centeredTaylor_quadratic
    (b : ℝ) (hb : 0 ≤ b) (hsmall : b ≤ 1 / 4)
    (right : Cfg) (e : Link) (g : Gauge) :
    ‖p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g +
      b * (D g - ∫ h : Gauge, D h ∂nu)‖ ≤
      (272 * Real.exp 8) * b ^ 2 := by
  have hTaylor := p4Q2JN2_actualDensityContrast_centeredTaylor_explicit
    H b hb hsmall right e g
  have hGap := p4Q2JN2_trueWilsonExpGap_le b hb
  have hExp : Real.exp (32 * b) ≤ Real.exp 8 :=
    Real.exp_le_exp.mpr (by linarith)
  have hTerm1 :
      (16 * b ^ 2) * Real.exp (32 * b) ≤
      (16 * b ^ 2) * Real.exp 8 :=
    mul_le_mul_of_nonneg_left hExp
      (mul_nonneg (by norm_num) (sq_nonneg b))
  have hTerm2 :
      (4 * b) * (Real.exp (32 * b) - Real.exp (-32 * b)) ≤
      (4 * b) * ((64 * b) * Real.exp (32 * b)) :=
    mul_le_mul_of_nonneg_left hGap
      (mul_nonneg (by norm_num) hb)
  have hTerm3 :
      (4 * b) * ((64 * b) * Real.exp (32 * b)) ≤
      (4 * b) * ((64 * b) * Real.exp 8) :=
    mul_le_mul_of_nonneg_left hExp
      (mul_nonneg (mul_nonneg (by norm_num) hb)
        (mul_nonneg (by norm_num) hb))
  calc
    ‖p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g +
        b * (D g - ∫ h : Gauge, D h ∂nu)‖ ≤
      (16 * b ^ 2) * Real.exp (32 * b) +
        (4 * b) * (Real.exp (32 * b) - Real.exp (-32 * b)) := hTaylor
    _ ≤ (16 * b ^ 2) * Real.exp 8 +
        (4 * b) * ((64 * b) * Real.exp 8) :=
      add_le_add hTerm1 (hTerm2.trans hTerm3)
    _ = (272 * Real.exp 8) * b ^ 2 := by ring


/-- The true ORIGINAL interacting posterior density contrast as a
continuous function of the actual SU(2) right-link value. -/
noncomputable def p4Q2JN2_originalPosteriorDensityContrastContinuous
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) : C(Gauge, ℝ) :=
  p4Q2JN2_originalPosteriorIdentityContinuous H b hb right e -
    p4Q2JN2_originalPosteriorPiContinuous H b hb right e

/-- STRONG SUP-NORM first-order asymptotic of the genuine original
UNLOGGED Wilson posterior density contrast, at every finite lattice
volume and every physical link/context, uniformly with a universal
rate. This is the analytic weak-coupling right derivative on the
actual SU(2) Haar reference carrier, NOT a derivative of either
individual interacting Wilson posterior or physical Perron vacuum. -/
theorem p4Q2JN2_originalPosteriorDensityContrast_strongSupQuotient_le
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ 1 / 4)
    (right : Cfg) (e : Link) :
    ‖b⁻¹ • p4Q2JN2_originalPosteriorDensityContrastContinuous H b hb.le right e +
      p4Q2JM_temporalWilsonCentered‖ ≤
      (272 * Real.exp 8) * b := by
  let F := p4Q2JN2_originalPosteriorDensityContrastContinuous
    H b hb.le right e
  let T := p4Q2JM_temporalWilsonCentered
  have hPoint (g : Gauge) :
      ‖F g + b * T g‖ ≤ (272 * Real.exp 8) * b ^ 2 := by
    change
      ‖p4Q2GB_originalWilsonPosteriorLeftDensityContrast
          H b hb.le right e g +
        b * (D g - ∫ h : Gauge, D h ∂nu)‖ ≤
        (272 * Real.exp 8) * b ^ 2
    exact p4Q2JN2_actualDensityContrast_centeredTaylor_quadratic
      H b hb.le hsmall right e g
  have hSup : ‖F + b • T‖ ≤ (272 * Real.exp 8) * b ^ 2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro g
    simpa only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
      smul_eq_mul] using hPoint g
  have hRewrite : b⁻¹ • F + T = b⁻¹ • (F + b • T) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]
  change ‖b⁻¹ • F + T‖ ≤ (272 * Real.exp 8) * b
  rw [hRewrite, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hb)]
  calc
    b⁻¹ * ‖F + b • T‖ ≤
        b⁻¹ * ((272 * Real.exp 8) * b ^ 2) :=
      mul_le_mul_of_nonneg_left hSup (inv_nonneg.mpr hb.le)
    _ = (272 * Real.exp 8) * b := by
      field_simp [hb.ne']
      ring

/-- The SAME actual genuine unlogged original interacting posterior
first-order contrast converges strongly through mathlib's bounded
continuous-function-to-Haar-L² map. The right-hand coefficient is
nonzero by JM, and the explicit norm bound makes this statement
quantitatively stronger than pointwise differentiation. -/
theorem p4Q2JN2_originalPosteriorDensityContrast_strongHaarL2Quotient_le
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ 1 / 4)
    (right : Cfg) (e : Link) :
    ‖b⁻¹ •
        ContinuousMap.toLp 2 nu ℝ
          (p4Q2JN2_originalPosteriorDensityContrastContinuous H b hb.le right e) +
      ContinuousMap.toLp 2 nu ℝ p4Q2JM_temporalWilsonCentered‖ ≤
      ‖(ContinuousMap.toLp 2 nu ℝ :
          C(Gauge, ℝ) →L[ℝ] Lp ℝ 2 nu)‖ *
        ((272 * Real.exp 8) * b) := by
  let L : C(Gauge, ℝ) →L[ℝ] Lp ℝ 2 nu :=
    ContinuousMap.toLp 2 nu ℝ
  let F := p4Q2JN2_originalPosteriorDensityContrastContinuous
    H b hb.le right e
  let T := p4Q2JM_temporalWilsonCentered
  have hSup :=
    p4Q2JN2_originalPosteriorDensityContrast_strongSupQuotient_le
      H b hb hsmall right e
  change ‖b⁻¹ • L F + L T‖ ≤ ‖L‖ * ((272 * Real.exp 8) * b)
  rw [← map_smul, ← map_add]
  exact (L.le_opNorm (b⁻¹ • F + T)).trans
    (mul_le_mul_of_nonneg_left hSup (norm_nonneg L))

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_continuousNormalizedExp_integral_eq_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_bothOriginalPosteriorHaarIntegrals_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_originalDensityContrast_eq_minorHaarIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_originalTemporalDifferenceHaarIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_densityContrast_error_le_of_minor_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_actualDensityContrast_centeredTaylor_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_trueWilsonExpGap_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_actualDensityContrast_centeredTaylor_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_originalPosteriorDensityContrast_strongSupQuotient_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN2_originalPosteriorDensityContrast_strongHaarL2Quotient_le

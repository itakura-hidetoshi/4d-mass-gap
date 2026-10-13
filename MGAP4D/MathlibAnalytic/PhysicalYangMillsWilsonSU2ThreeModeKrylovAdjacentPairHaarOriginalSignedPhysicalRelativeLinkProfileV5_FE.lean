import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalLinkLocalizedTwoRegimeV5_FD
import Mathlib.Tactic

/-!
# P4-Q2-FE: construct genuine nonuniform original Wilson physical-source link profile

FC proves true ORIGINAL signed Wilson posterior link differences pointwise,
with the exact positive half-density/inverse-vacuum factor W(z)/Omega(B)
left INSIDE the Wilson probability integration. FD proves a restricted-link
comparison but leaves the spatially nonuniform physical profile conditional.

Here build the actual continuous *relative* signed link response, not an
arbitrarily chosen coefficient:

     R_{beta,e,f}(z,g)
       = [O_f(z) - O_f(z.1, update z.2 e g)]
            / [W_beta(z) Omega_beta(z.2)^(-1)].

The denominator is the actual strictly positive original Wilson joint
half-density times actual inverse continuous vacuum, for every
configuration. The numerator retains the COMPLETE signed Wilson physical
receiver and the real right-link update, including output drift.

By FC's physical Harnack proof, ||R_{beta,e,f}||_sup is bounded by the
genuine original source L2 norm times the original transfer/Harnack
coefficient. This is a constructed e- and f-dependent, nonnegative finite
quantity, with no hypothesis asserting localization.

The original Wilson posterior resampling energy can then be integrated
with b_e(z)=||R_{beta,e,f}||_sup W_beta(z)/Omega_beta(z.2).
FC's EXACT original Wilson squared joint moment cancels the density,
yielding an explicit e-dependent and f-dependent profile strictly at
least as sharp as the earlier uniform Harnack estimate.

This does NOT assert spatial decay, finite support, volume-uniform
summability, independent Haar posterior, Dobrushin, or a continuum
Yang-Mills gap. The genuine beta(n+1) physical orbit remains distinct
from the beta(n) frozen joint law wherever later specialized.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 900000

local instance p4Q2FE_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FE_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FE_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FE_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FE_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
private noncomputable instance p4Q2FE_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Strict positivity of the ACTUAL original Wilson half-density and
inverse-vacuum multiplier; no uniform lower bound is asserted. -/
theorem p4Q2FE_originalWilsonDensityCancellationWeight_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 <
      normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta z *
      normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta z.2 := by
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  have hL : 0 < L :=
    inv_pos.mpr (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta)
  have hΩ : 0 < Ω z.2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta z.2
  have hW : 0 < W z := by
    change 0 < (L * Ω z.2) / continuousJointSqrtDensity H N hN beta hbeta z
    exact div_pos (mul_pos hL hΩ)
      (continuousJointSqrtDensity_pos H N hN beta hbeta z)
  have hV : 0 < V z.2 := by
    change 0 < (Ω z.2)⁻¹
    exact inv_pos.mpr hΩ
  exact mul_pos hW hV

/-- The ACTUAL original signed Wilson physical-source relative right-link
response as a globally bounded continuous function on the compact
configuration x SU(N) update carrier. The denominator is everywhere
strictly positive, not a chosen bounded-below substitute. -/
noncomputable def p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    BoundedContinuousFunction
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ := by
  classical
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let Delta := physicalJointBCFRightLinkDifference H N O e
  let q : Pair × Gauge → ℝ := fun t => W t.1 * V t.1.2
  have hqContinuous : Continuous q :=
    (W.continuous.comp continuous_fst).mul
      (V.continuous.comp (continuous_snd.comp continuous_fst))
  have hqNonzero : ∀ t : Pair × Gauge, q t ≠ 0 := by
    intro t
    exact (p4Q2FE_originalWilsonDensityCancellationWeight_pos
      H N hN beta hbeta t.1).ne'
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun t : Pair × Gauge => Delta t / q t,
      Delta.continuous.div hqContinuous hqNonzero⟩

@[simp] theorem p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF H N hN beta hbeta f e (z,g) =
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f z -
       normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
         (z.1, Function.update z.2 e g)) /
      (normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta z *
       normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta z.2) := by
  rfl

/-- The constructed nonuniform physical-source link response is
ALREADY bounded by the proved universal FC coefficient; it is not a
hypothetical finite physical profile. At beta=0 the bound vanishes. -/
theorem p4Q2FE_originalWilsonRelativeSignedLinkResponse_norm_le_FC
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF
       H N hN beta hbeta f e‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
      (Real.exp (8 * beta) ^ 3 - 1) * ‖f‖ := by
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  let R : ℝ := Real.exp (8 * beta)
  let C : ℝ := L * (R ^ 3 - 1) * ‖f‖
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  have hL : 0 ≤ L :=
    (inv_pos.mpr (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta)).le
  have hR : 1 ≤ R := by
    have hb : (0 : ℝ) ≤ 8 * beta := by positivity
    simpa [R] using (Real.exp_le_exp.mpr hb :
      Real.exp (0 : ℝ) ≤ Real.exp (8 * beta))
  have hR3 : 1 ≤ R ^ 3 := by
    calc
      (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ R ^ 3 := pow_le_pow_left₀ (by norm_num) hR 3
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hL (sub_nonneg.mpr hR3)) (norm_nonneg f)
  apply (BoundedContinuousFunction.norm_le hC).2
  intro t
  rcases t with ⟨z,g⟩
  have hWeight := p4Q2FE_originalWilsonDensityCancellationWeight_pos
    H N hN beta hbeta z
  have hDelta := p4Q2FC_originalJointReceiver_linkDifference_abs_le_weightedSource
    H N hN beta hbeta f e z g
  change |O z - O (z.1, Function.update z.2 e g)| ≤
    C * (W z * V z.2) at hDelta
  rw [Real.norm_eq_abs,
    p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF_apply,
    abs_div, abs_of_pos hWeight]
  exact (div_le_iff₀ hWeight).2 hDelta

/-- The true source-dependent and link-dependent profile is a FINITE
BCF norm computed from the original signed Wilson physical receiver
and real right-link update. No physical localization is postulated. -/
noncomputable def p4Q2FE_originalWilsonSignedSourceLinkProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (1 / 2 : ℝ) *
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹) ^ 2 *
    ‖p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF
       H N hN beta hbeta f e‖ ^ 2

theorem p4Q2FE_originalWilsonSignedSourceLinkProfile_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ p4Q2FE_originalWilsonSignedSourceLinkProfile
      H N hN beta hbeta f e := by
  unfold p4Q2FE_originalWilsonSignedSourceLinkProfile
  positivity

/-- The actual link profile is at most the FC small-coupling
density-cancelled bound, with no artificial link independence. -/
theorem p4Q2FE_originalWilsonSignedSourceLinkProfile_le_FC
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FE_originalWilsonSignedSourceLinkProfile H N hN beta hbeta f e ≤
      (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹) ^ 4 *
      (Real.exp (8 * beta) ^ 3 - 1) ^ 2 * ‖f‖ ^ 2 := by
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  let R : ℝ := Real.exp (8 * beta)
  let B := p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF
    H N hN beta hbeta f e
  have hBound := p4Q2FE_originalWilsonRelativeSignedLinkResponse_norm_le_FC
    H N hN beta hbeta f e
  change ‖B‖ ≤ L * (R ^ 3 - 1) * ‖f‖ at hBound
  have hSq : ‖B‖ ^ 2 ≤ (L * (R ^ 3 - 1) * ‖f‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hBound 2
  have hMul := mul_le_mul_of_nonneg_left hSq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (sq_nonneg L))
  calc
    p4Q2FE_originalWilsonSignedSourceLinkProfile H N hN beta hbeta f e =
        ((1 / 2 : ℝ) * L ^ 2) * ‖B‖ ^ 2 := by rfl
    _ ≤ ((1 / 2 : ℝ) * L ^ 2) * (L * (R ^ 3 - 1) * ‖f‖) ^ 2 :=
      hMul
    _ = (1 / 2 : ℝ) * L ^ 4 * (R ^ 3 - 1) ^ 2 * ‖f‖ ^ 2 := by ring


/-- Certified pointwise ACTUAL signed Wilson link update in terms of
its CONSTRUCTED, truly link/source-dependent normalized BCF norm.
The original positive Wilson joint weight remains inside the
bound and hence inside the upcoming original joint integral. -/
theorem p4Q2FE_originalJointReceiver_linkDifference_abs_le_actualSourceResponse
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let O := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
    let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
    let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
    let B := p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF
      H N hN beta hbeta f e
    |O z - O (z.1, Function.update z.2 e g)| ≤
      ‖B‖ * (W z * V z.2) := by
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let B := p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF
    H N hN beta hbeta f e
  let zp := (z.1, Function.update z.2 e g)
  have hWeight : 0 < W z * V z.2 :=
    p4Q2FE_originalWilsonDensityCancellationWeight_pos H N hN beta hbeta z
  have hNorm : |(O z - O zp) / (W z * V z.2)| ≤ ‖B‖ := by
    simpa only [B, O, W, V,
      p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF_apply,
      Real.norm_eq_abs] using B.norm_coe_le_norm (z,g)
  rw [abs_div, abs_of_pos hWeight] at hNorm
  calc
    |O z - O zp| = (|O z - O zp| / (W z * V z.2)) *
          (W z * V z.2) := by field_simp [ne_of_gt hWeight]
    _ ≤ ‖B‖ * (W z * V z.2) :=
      mul_le_mul_of_nonneg_right hNorm hWeight.le

/-- GENUINE ORIGINAL WILSON signed two-copy posterior resampling
is controlled by the constructed relative physical-source response
of this exact spatial link, not a fictional independent Haar law.
The old physical exact joint moment cancels W and Omega^-1 in L². -/
theorem p4Q2FE_originalPosteriorResampling_le_actualSourceResponse
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹) ^ 2 *
      ‖p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF
        H N hN beta hbeta f e‖ ^ 2 := by
  classical
  let μJ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let B := p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF
    H N hN beta hbeta f e
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  let C : ℝ := ‖B‖
  let b (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
    C * (W z * V z.2)
  have hbContinuity :
      Continuous (fun z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => b z ^ 2) := by
    dsimp [b]
    exact (continuous_const.mul
      (W.continuous.mul (V.continuous.comp continuous_snd))).pow 2
  have hbIntegrable : Integrable (fun z => b z ^ 2) μJ :=
    hbContinuity.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbPoint : ∀ z (g : Matrix.specialUnitaryGroup (Fin N) ℂ),
      |O z - O (z.1, Function.update z.2 e g)| ≤ b z := by
    intro z g
    exact p4Q2FE_originalJointReceiver_linkDifference_abs_le_actualSourceResponse
      H N hN beta hbeta f e z g
  have hPosterior :
      posteriorResamplingEnergy H N hN beta hbeta e O ≤
        ∫ z, b z ^ 2 ∂μJ :=
    originalWilsonPosteriorResamplingEnergy_le_pointwiseLinkOscillation
      H N hN beta hbeta e O b hbIntegrable hbPoint
  have hMoment :
      (∫ z, (W z * V z.2) ^ 2 ∂μJ) = L ^ 2 := by
    exact normalizedPhysicalOneSlabJointHalfDensityWeightBCF_mul_vacuumInverse_sq_integral_joint_eq
      H N hN beta hbeta
  calc
    posteriorResamplingEnergy H N hN beta hbeta e O ≤
        ∫ z, b z ^ 2 ∂μJ := hPosterior
    _ = C ^ 2 * (∫ z, (W z * V z.2) ^ 2 ∂μJ) := by
      calc
        (∫ z, b z ^ 2 ∂μJ) =
            ∫ z, C ^ 2 * (W z * V z.2) ^ 2 ∂μJ := by
              apply integral_congr_ae
              filter_upwards with z
              dsimp [b]
              ring
        _ = C ^ 2 * (∫ z, (W z * V z.2) ^ 2 ∂μJ) :=
          integral_const_mul _ _
    _ = C ^ 2 * L ^ 2 := by rw [hMoment]
    _ = L ^ 2 * C ^ 2 := mul_comm _ _

/-- NONUNIFORM PHYSICAL LINK CERTIFICATE built from the signed source
and the exact original Wilson right-link kernel: its actual
transported physical CondExpL2 squared defect is bounded by
the explicitly constructed profile. This closes FD's missing
pointwise source-specific coefficient without assuming decay. -/
theorem p4Q2FE_originalPhysicalLinkDefect_le_constructedSourceLinkProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e ≤
      p4Q2FE_originalWilsonSignedSourceLinkProfile H N hN beta hbeta f e := by
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  let B := p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF
    H N hN beta hbeta f e
  have hExact := p4Q2FD_originalPhysicalLinkDefect_eq_half_posterior
    H N hN beta hbeta f e
  have hEnergy := p4Q2FE_originalPosteriorResampling_le_actualSourceResponse
    H N hN beta hbeta f e
  calc
    p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e =
        (1 / 2 : ℝ) * posteriorResamplingEnergy H N hN beta hbeta e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) :=
      hExact
    _ ≤ (1 / 2 : ℝ) * (L ^ 2 * ‖B‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hEnergy (by norm_num)
    _ = p4Q2FE_originalWilsonSignedSourceLinkProfile H N hN beta hbeta f e := by
      rfl

/-- FINITE PATCH source-adapted profile: the full physical signed
Wilson right-link energies can be bounded without first replacing
every link response by FC's universal worst-case coefficient. -/
noncomputable def p4Q2FE_originalWilsonSignedSourcePatchProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  S.sum (fun e => p4Q2FE_originalWilsonSignedSourceLinkProfile H N hN beta hbeta f e)

theorem p4Q2FE_originalPhysicalRestrictedLinkEnergy_le_constructedSourcePatchProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta f S ≤
      p4Q2FE_originalWilsonSignedSourcePatchProfile H N hN beta hbeta f S := by
  unfold p4Q2FD_originalPhysicalRestrictedLinkEnergy
    p4Q2FE_originalWilsonSignedSourcePatchProfile
  exact Finset.sum_le_sum (fun e _he =>
    p4Q2FE_originalPhysicalLinkDefect_le_constructedSourceLinkProfile
      H N hN beta hbeta f e)

/-- An authentic physical source's link-dependent profile is no
larger than FC's worst-case |S| bound; no fictitious decay rate. -/
theorem p4Q2FE_originalSignedSourcePatchProfile_le_FC_count
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FE_originalWilsonSignedSourcePatchProfile H N hN beta hbeta f S ≤
      (S.card : ℝ) * (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹) ^ 4 *
      (Real.exp (8 * beta) ^ 3 - 1) ^ 2 * ‖f‖ ^ 2 := by
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  let R : ℝ := Real.exp (8 * beta)
  let C : ℝ := (1 / 2 : ℝ) * L ^ 4 * (R ^ 3 - 1) ^ 2 * ‖f‖ ^ 2
  have hEach (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      p4Q2FE_originalWilsonSignedSourceLinkProfile H N hN beta hbeta f e ≤ C :=
    p4Q2FE_originalWilsonSignedSourceLinkProfile_le_FC H N hN beta hbeta f e
  calc
    p4Q2FE_originalWilsonSignedSourcePatchProfile H N hN beta hbeta f S =
        S.sum (fun e => p4Q2FE_originalWilsonSignedSourceLinkProfile H N hN beta hbeta f e) :=
      rfl
    _ ≤ S.sum (fun _e => C) :=
      Finset.sum_le_sum (fun e _he => hEach e)
    _ = (S.card : ℝ) * C := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = (S.card : ℝ) * (1 / 2 : ℝ) * L ^ 4 *
          (R ^ 3 - 1) ^ 2 * ‖f‖ ^ 2 := by ring

/-- The whole arbitrary physical input-family signed Gram now has
a CONSTRUCTED source-dependent profile, with no input orthogonality
or fake spatial independence. -/
theorem p4Q2FE_originalWilsonPhysicalGram_rayleigh_le_sourceProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H N hN beta hbeta
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) ≤
      p4Q2FE_originalWilsonSignedSourcePatchProfile H N hN beta hbeta
        (∑ i : ι, a i • f i)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  classical
  let F := ∑ i : ι, a i • f i
  let L := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hEq := pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
    H N hN beta hbeta f a
  have hPatch := p4Q2FE_originalPhysicalRestrictedLinkEnergy_le_constructedSourcePatchProfile
    H N hN beta hbeta F L
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H N hN beta hbeta
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) =
      p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta F L := by
        simpa only [p4Q2FD_originalPhysicalRestrictedLinkEnergy, F, L] using hEq
    _ ≤ p4Q2FE_originalWilsonSignedSourcePatchProfile H N hN beta hbeta F L :=
      hPatch

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonDensityCancellationWeight_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonRelativeSignedLinkResponse_norm_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonSignedSourceLinkProfile_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonSignedSourceLinkProfile_le_FC

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalJointReceiver_linkDifference_abs_le_actualSourceResponse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalPosteriorResampling_le_actualSourceResponse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalPhysicalLinkDefect_le_constructedSourceLinkProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalPhysicalRestrictedLinkEnergy_le_constructedSourcePatchProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalSignedSourcePatchProfile_le_FC_count
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonPhysicalGram_rayleigh_le_sourceProfile

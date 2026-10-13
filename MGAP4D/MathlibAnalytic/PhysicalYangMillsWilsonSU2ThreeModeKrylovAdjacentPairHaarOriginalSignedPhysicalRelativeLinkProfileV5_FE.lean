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
  have hN := p4Q2FE_originalWilsonRelativeSignedLinkResponse_norm_le_FC
    H N hN beta hbeta f e
  change ‖B‖ ≤ L * (R ^ 3 - 1) * ‖f‖ at hN
  have hSq : ‖B‖ ^ 2 ≤ (L * (R ^ 3 - 1) * ‖f‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hN 2
  have hMul := mul_le_mul_of_nonneg_left hSq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (sq_nonneg L))
  calc
    p4Q2FE_originalWilsonSignedSourceLinkProfile H N hN beta hbeta f e =
        ((1 / 2 : ℝ) * L ^ 2) * ‖B‖ ^ 2 := by rfl
    _ ≤ ((1 / 2 : ℝ) * L ^ 2) * (L * (R ^ 3 - 1) * ‖f‖) ^ 2 :=
      hMul
    _ = (1 / 2 : ℝ) * L ^ 4 * (R ^ 3 - 1) ^ 2 * ‖f‖ ^ 2 := by ring

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonDensityCancellationWeight_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonRelativeSignedLinkResponseBCF_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonRelativeSignedLinkResponse_norm_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonSignedSourceLinkProfile_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonSignedSourceLinkProfile_le_FC

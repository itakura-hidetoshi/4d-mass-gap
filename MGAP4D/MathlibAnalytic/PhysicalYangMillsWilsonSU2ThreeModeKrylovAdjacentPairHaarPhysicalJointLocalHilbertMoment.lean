import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalPosteriorHilbertRayleighNoVacuumSup
import Mathlib.Tactic

/-!
# P4-Q2-D: original Wilson pointwise half-density cancellation in posterior energy

The genuine half-density W obeys a two-sided local Wilson Harnack comparison.
Rather than bounding W and the signed physical mean M by independent global
suprema, retain the positive W at the ORIGINAL joint configuration z.

For every genuine right-link update z' of z, the original signed receiver
F = W * M satisfies

  |F(z) - F(z')|
    ≤ (R * W(z)) * (C * Omega(z.2)^{-1}) + (R-1) * |F(z)|,

where R=exp(8*beta) and
C=||physical one-slab transfer||^{-1} (R^2-1) ||f||_HaarL2.

The genuine posterior energy is bounded by the joint integral of the SQUARE
of this local expression. In particular neither ||W||_sup nor ||M||_sup
appears, and no modified conditional law is used. The two true joint moments,
physical normalization and full spatial-link sum require further estimates
before an H-uniform Rayleigh theorem. No Dobrushin or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4LocalMomentTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4LocalMomentCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4LocalMomentSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4LocalMomentMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4LocalMomentBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4LocalMomentLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Positivity of the actual original Wilson joint half-density. -/
theorem normalizedPhysicalOneSlabJointHalfDensityWeightBCF_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 ≤ normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta z := by
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  have hl : 0 ≤ l :=
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)).le
  have hOmega : 0 ≤ Omega z.2 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta z.2).le
  change 0 ≤ (l * Omega z.2) /
    Real.sqrt (l * (Omega z.1 * K z.1 z.2 * Omega z.2))
  exact div_nonneg (mul_nonneg hl hOmega) (Real.sqrt_nonneg _)

/-- The genuine two-sided Harnack comparison yields a LOCAL bound, with
W(z), not its global norm. The absence of a global sup is essential. -/
theorem normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightLinkDifference_abs_le_local
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
    |W z - W (z.1, Function.update z.2 e g)| ≤
      (Real.exp (8 * beta) - 1) * W z := by
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let R := Real.exp (8 * beta)
  let z' := (z.1, Function.update z.2 e g)
  have hR : 1 ≤ R := by
    have hmul : (0 : ℝ) ≤ 8 * beta := by nlinarith [hbeta]
    simpa [R] using
      (Real.exp_le_exp.mpr hmul :
        Real.exp (0 : ℝ) ≤ Real.exp (8 * beta))
  have hW : 0 ≤ W z :=
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF_nonneg
      H N hN beta hbeta z
  have hForward : W z' ≤ R * W z :=
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightUpdate_le_exp_eight_mul
      H N hN beta hbeta e z g
  have hRest :
      Function.update (Function.update z.2 e g) e (z.2 e) = z.2 := by
    simp
  have hBackward : W z ≤ R * W z' := by
    have h :=
      normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightUpdate_le_exp_eight_mul
        H N hN beta hbeta e z' (z.2 e)
    change W (z.1, Function.update (Function.update z.2 e g) e (z.2 e)) ≤
      R * W z' at h
    rw [hRest] at h
    exact h
  have hUpper : W z' - W z ≤ (R - 1) * W z := by
    nlinarith [hForward]
  have hLower : W z - W z' ≤ (R - 1) * W z := by
    by_cases hh : W z' ≤ W z
    · have ht : W z - W z' ≤ (R - 1) * W z' := by
        nlinarith [hBackward]
      exact ht.trans (mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hR))
    · have ht : W z - W z' ≤ 0 := sub_nonpos.mpr (le_of_not_ge hh)
      exact ht.trans (mul_nonneg (sub_nonneg.mpr hR) hW)
  change |W z - W z'| ≤ (R - 1) * W z
  exact abs_le.mpr ⟨by linarith, hLower⟩

/-- Original signed joint receiver: genuinely local variation with NO
global W or M supremum norm, and no positive-kernel comparison applied
to a signed source integral. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_rightLinkVariation_le_localHilbert
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
    let F := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
    let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
    let C := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ * ((Real.exp (8 * beta)) ^ 2 - 1) * ‖f‖
    |F z - F (z.1, Function.update z.2 e g)| ≤
      (Real.exp (8 * beta) * W z) * (C * V z.2) +
        (Real.exp (8 * beta) - 1) * |F z| := by
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let M := normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f
  let F := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let R := Real.exp (8 * beta)
  let D := R ^ 2 - 1
  let C := l * D * ‖f‖
  let z' := (z.1, Function.update z.2 e g)
  have hR : 1 ≤ R := by
    have hmul : (0 : ℝ) ≤ 8 * beta := by nlinarith [hbeta]
    simpa [R] using
      (Real.exp_le_exp.mpr hmul :
        Real.exp (0 : ℝ) ≤ Real.exp (8 * beta))
  have hL : 0 ≤ l :=
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)).le
  have hD : 0 ≤ D := by dsimp [D]; nlinarith [hR]
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hL hD) (norm_nonneg f)
  have hOmega : 0 < Omega z.2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta z.2
  have hV : 0 ≤ V z.2 := by
    change 0 ≤ (Omega z.2)⁻¹
    exact (inv_pos.mpr hOmega).le
  have hW : 0 ≤ W z :=
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF_nonneg
      H N hN beta hbeta z
  have hW' : 0 ≤ W z' :=
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF_nonneg
      H N hN beta hbeta z'
  have hForward : |W z'| ≤ R * W z := by
    rw [abs_of_nonneg hW']
    exact normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightUpdate_le_exp_eight_mul
      H N hN beta hbeta e z g
  have hLocalW : |W z - W z'| ≤ (R - 1) * W z :=
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightLinkDifference_abs_le_local
      H N hN beta hbeta e z g
  have hMean : |M z - M z'| ≤ C * V z.2 := by
    have hm :=
      normalizedPhysicalOneSlabVacuumReceiverBCF_rightLinkDifference_abs_le_signedSourceL2
        H N hN beta hbeta f z.2 e g
    change |M z' - M z| ≤ l * (D / Omega z.2) * ‖f‖ at hm
    calc
      |M z - M z'| = |M z' - M z| := abs_sub_comm _ _
      _ ≤ l * (D / Omega z.2) * ‖f‖ := hm
      _ = C * V z.2 := by
        change l * (D / Omega z.2) * ‖f‖ =
          (l * D * ‖f‖) * (Omega z.2)⁻¹
        ring
  have hSplit : F z - F z' =
      W z' * (M z - M z') + (W z - W z') * M z := by
    change W z * M z - W z' * M z' =
      W z' * (M z - M z') + (W z - W z') * M z
    ring
  have hFirst :
      |W z'| * |M z - M z'| ≤ (R * W z) * (C * V z.2) := by
    calc
      |W z'| * |M z - M z'| ≤
          (R * W z) * |M z - M z'| :=
        mul_le_mul_of_nonneg_right hForward (abs_nonneg _)
      _ ≤ (R * W z) * (C * V z.2) :=
        mul_le_mul_of_nonneg_left hMean
          (mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hR) hW)
  have hFAbs : |F z| = W z * |M z| := by
    change |W z * M z| = W z * |M z|
    rw [abs_mul, abs_of_nonneg hW]
  have hSecond :
      |W z - W z'| * |M z| ≤ (R - 1) * |F z| := by
    calc
      |W z - W z'| * |M z| ≤ ((R - 1) * W z) * |M z| :=
        mul_le_mul_of_nonneg_right hLocalW (abs_nonneg _)
      _ = (R - 1) * |F z| := by rw [hFAbs]; ring
  change |F z - F z'| ≤
    (R * W z) * (C * V z.2) + (R - 1) * |F z|
  calc
    |F z - F z'| =
        |W z' * (M z - M z') + (W z - W z') * M z| :=
      congrArg abs hSplit
    _ ≤ |W z'| * |M z - M z'| + |W z - W z'| * |M z| := by
      simpa only [abs_mul] using
        (abs_add_le (W z' * (M z - M z')) ((W z - W z') * M z))
    _ ≤ (R * W z) * (C * V z.2) + (R - 1) * |F z| :=
      add_le_add hFirst hSecond

/-- Actual Wilson posterior link energy bounded by JOINT LOCAL MOMENTS.
Unlike the preceding global-sup envelope, neither ||W|| nor ||M|| enters.
This is not yet a uniform bound on the moments or their sum over links. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_posteriorEnergy_le_jointLocalHilbertMoment
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
    let F := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
    let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
    let C := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ * ((Real.exp (8 * beta)) ^ 2 - 1) * ‖f‖
    posteriorResamplingEnergy H N hN beta hbeta e F ≤
      ∫ z, ((Real.exp (8 * beta) * W z) * (C * V z.2) +
        (Real.exp (8 * beta) - 1) * |F z|) ^ 2
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let F := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let R := Real.exp (8 * beta)
  let C : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ * (R ^ 2 - 1) * ‖f‖
  let B : BoundedContinuousFunction (Cfg × Cfg) ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun z => (R * W z) * (C * V z.2) + (R - 1) * |F z|,
        ((continuous_const.mul W.continuous).mul
          (continuous_const.mul (V.continuous.comp continuous_snd))).add
          (continuous_const.mul F.continuous.abs)⟩
  have hInt : Integrable (fun z => (B z) ^ 2) ν := by
    apply Integrable.of_bound
      ((B.continuous.pow 2).aestronglyMeasurable)
      (‖B‖ ^ 2)
    filter_upwards with z
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (B.norm_coe_le_norm z) 2
  have hOsc (z : Cfg × Cfg) (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      |F z - F (z.1, Function.update z.2 e g)| ≤ B z := by
    change |F z - F (z.1, Function.update z.2 e g)| ≤
      (R * W z) * (C * V z.2) + (R - 1) * |F z|
    exact normalizedPhysicalOneSlabJointReceiverProductBCF_rightLinkVariation_le_localHilbert
      H N hN beta hbeta f e z g
  have hEnergy := originalWilsonPosteriorResamplingEnergy_le_pointwiseLinkOscillation
    H N hN beta hbeta e F (fun z => B z) hInt hOsc
  change posteriorResamplingEnergy H N hN beta hbeta e F ≤
    ∫ z, (B z) ^ 2 ∂ν
  exact hEnergy

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

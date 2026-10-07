import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFrozenVacuumReceiverJointHalfDensity
import Mathlib.Tactic

/-!
# Exact Leibniz splitting of the signed joint receiver and its resampling energy

The actual frozen adjacent receiver from PR #5256 is the genuine product

  R(C,B) = W(C,B) * M(B),

where W = lambda^(-1) * Omega(B) / sqrt(rho_joint(C,B)) retains the output
joint half-density, and M is the normalized physical one-slab transfer
receiver from PR #5255.

This file proves the exact discrete Leibniz rule for the original right-link
update and a corresponding coefficient-two posterior resampling energy bound:

  E_e(W*M) <= 2 * ||W||_infty^2 * E_e(M)
              + 2 * ||M||_infty^2 * E_e(W).

Both E_e are computed under the original joint law and the original
posterior single-link conditional law, not a product approximation.
The first term is the posterior-mean response; the second retains the
full half-density/output drift.

The infinity norms are exposed honestly and may depend on spatial volume.
This is an exact structural Dirichlet reduction, not a volume-uniform
gap, a new Dobrushin estimate or an identification of a covariance
with an L2 coordinate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3JointLeibnizTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3JointLeibnizCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3JointLeibnizSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3JointLeibnizMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3JointLeibnizBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3JointLeibnizSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Continuous joint half-density weight of the actual normalized transfer.
The fixed-right vacuum representative is evaluated at the updated boundary;
the left boundary is retained in the genuine joint square-root density. -/
noncomputable def normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z =>
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta z.2) /
          continuousJointSqrtDensity H N hN beta hbeta z,
      by
        have hOmega :
            Continuous (fun z :
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                H N hN beta hbeta z.2) :=
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
            H N hN beta hbeta).comp continuous_snd
        exact
          (continuous_const.mul hOmega).div
            (continuousJointSqrtDensity_continuous H N hN beta hbeta)
            (fun z => (continuousJointSqrtDensity_pos H N hN beta hbeta z).ne')⟩

/-- Lift the actual frozen posterior-mean receiver to the joint boundary by
the right-coordinate projection. -/
noncomputable def normalizedPhysicalOneSlabVacuumMeanJointBCF
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => normalizedPhysicalOneSlabVacuumReceiverBCF
        H N hN beta hbeta f z.2,
      (normalizedPhysicalOneSlabVacuumReceiverBCF
        H N hN beta hbeta f).continuous.comp continuous_snd⟩

/-- The bounded continuous product carrier for the exact joint receiver. -/
noncomputable def normalizedPhysicalOneSlabJointReceiverProductBCF
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta *
    normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f

/-- Exactly the pre-existing signed-transfer receiver, including its joint
half-density, not a new independently normalized observable. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f z =
      normalizedPhysicalOneSlabJointHalfDensityReceiver H N hN beta hbeta f z := by
  unfold normalizedPhysicalOneSlabJointReceiverProductBCF
  change
    ((‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta z.2) /
        continuousJointSqrtDensity H N hN beta hbeta z) *
      normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f z.2 =
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta z.2 *
        normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f z.2) /
        continuousJointSqrtDensity H N hN beta hbeta z
  ring

/-- Discrete Leibniz rule on precisely the right-coordinate link update
used by the genuine posterior resampling Dirichlet energy. -/
theorem jointBCF_mul_sub_right_update
    {H N : ℕ}
    (A B : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (A * B) z - (A * B) (z.1, Function.update z.2 e g) =
      A z * (B z - B (z.1, Function.update z.2 e g)) +
        (A z - A (z.1, Function.update z.2 e g)) *
          B (z.1, Function.update z.2 e g) := by
  change A z * B z -
      A (z.1, Function.update z.2 e g) * B (z.1, Function.update z.2 e g) = _
  ring

/-- The exact half-density/right-mean splitting of the ORIGINAL signed right
link defect; neither endpoint nor output drift has been discarded. -/
theorem decomposableRightLinkDifferenceFactor_eq_halfDensity_mean_leibniz
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    decomposableRightLinkDifferenceFactor H N hN beta hbeta f e z g =
      normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta z *
        (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f z -
          normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f
            (z.1, Function.update z.2 e g)) +
      (normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta z -
        normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
          (z.1, Function.update z.2 e g)) *
          normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f
            (z.1, Function.update z.2 e g) := by
  rw [decomposableRightLinkDifferenceFactor_eq_jointHalfDensityReceiver_sub_update]
  rw [← normalizedPhysicalOneSlabJointReceiverProductBCF_apply
      H N hN beta hbeta f z,
      ← normalizedPhysicalOneSlabJointReceiverProductBCF_apply
        H N hN beta hbeta f (z.1, Function.update z.2 e g)]
  exact jointBCF_mul_sub_right_update
    (normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta)
    (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f) e z g

/-- A bounded joint observable's pointwise squared value is dominated by its
squared supremum norm.  In contrast to the vacuum-L2 norm, this coefficient
is not claimed to be uniform in finite volume. -/
private theorem jointBCF_value_sq_le_norm_sq
    {α : Type*} [TopologicalSpace α]
    (F : BoundedContinuousFunction α ℝ) (x : α) :
    F x ^ 2 ≤ ‖F‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (F.norm_coe_le_norm x) 2
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- Pointwise coefficient-two product variation inequality.
The first term measures variation of the posterior mean; the second
measures the full half-density/output coefficient variation. -/
theorem jointBCF_mul_right_update_sq_le_two
    {H N : ℕ}
    (A B : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ((A * B) z - (A * B) (z.1, Function.update z.2 e g)) ^ 2 ≤
      (2 * ‖A‖ ^ 2) *
        (B z - B (z.1, Function.update z.2 e g)) ^ 2 +
      (2 * ‖B‖ ^ 2) *
        (A z - A (z.1, Function.update z.2 e g)) ^ 2 := by
  let z' := (z.1, Function.update z.2 e g)
  have hA := jointBCF_value_sq_le_norm_sq A z
  have hB := jointBCF_value_sq_le_norm_sq B z'
  have hx :
      (A z * (B z - B z')) ^ 2 ≤
        ‖A‖ ^ 2 * (B z - B z') ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hA (sq_nonneg _)
  have hy :
      ((A z - A z') * B z') ^ 2 ≤
        ‖B‖ ^ 2 * (A z - A z') ^ 2 := by
    rw [mul_pow]
    rw [mul_comm ((A z - A z') ^ 2) ((B z') ^ 2)]
    exact mul_le_mul_of_nonneg_right hB (sq_nonneg _)
  have hSq :
      ((A * B) z - (A * B) z') ^ 2 =
        (A z * (B z - B z') + (A z - A z') * B z') ^ 2 := by
    rw [jointBCF_mul_sub_right_update]
  rw [hSq]
  calc
    (A z * (B z - B z') + (A z - A z') * B z') ^ 2 ≤
        2 * (A z * (B z - B z')) ^ 2 +
          2 * ((A z - A z') * B z') ^ 2 := by
            nlinarith [sq_nonneg
              (A z * (B z - B z') - (A z - A z') * B z')]
    _ ≤ 2 * (‖A‖ ^ 2 * (B z - B z') ^ 2) +
          2 * (‖B‖ ^ 2 * (A z - A z') ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hx (by norm_num))
          (mul_le_mul_of_nonneg_left hy (by norm_num))
    _ = (2 * ‖A‖ ^ 2) * (B z - B z') ^ 2 +
          (2 * ‖B‖ ^ 2) * (A z - A z') ^ 2 := by ring

/-- Fully integrated Leibniz estimate for the ORIGINAL posterior resampling
measure and joint law, with both conditional and outer integrability discharged
by the existing BCF squared-difference theorems. -/
theorem posteriorResamplingEnergy_mul_le_two
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (A B : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    posteriorResamplingEnergy H N hN beta hbeta e (A * B) ≤
      (2 * ‖A‖ ^ 2) * posteriorResamplingEnergy H N hN beta hbeta e B +
      (2 * ‖B‖ ^ 2) * posteriorResamplingEnergy H N hN beta hbeta e A := by
  let muJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let nu := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta
  have hInner (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      posteriorResamplingSquare H N hN beta hbeta e (A * B) z ≤
        (2 * ‖A‖ ^ 2) * posteriorResamplingSquare H N hN beta hbeta e B z +
          (2 * ‖B‖ ^ 2) * posteriorResamplingSquare H N hN beta hbeta e A z := by
    have hProd := posteriorResamplingDifferenceSquare_integrable
      H N hN beta hbeta e (A * B) z
    have hA := posteriorResamplingDifferenceSquare_integrable
      H N hN beta hbeta e A z
    have hB := posteriorResamplingDifferenceSquare_integrable
      H N hN beta hbeta e B z
    have hLeft :=
      hB.const_mul (2 * ‖A‖ ^ 2)
    have hRight :=
      hA.const_mul (2 * ‖B‖ ^ 2)
    change
      (∫ g, ((A * B) z -
          (A * B) (z.1, Function.update z.2 e g)) ^ 2 ∂nu z.1 z.2 e) ≤
      (2 * ‖A‖ ^ 2) *
          (∫ g, (B z - B (z.1, Function.update z.2 e g)) ^ 2
            ∂nu z.1 z.2 e) +
        (2 * ‖B‖ ^ 2) *
          (∫ g, (A z - A (z.1, Function.update z.2 e g)) ^ 2
            ∂nu z.1 z.2 e)
    calc
      (∫ g, ((A * B) z -
          (A * B) (z.1, Function.update z.2 e g)) ^ 2 ∂nu z.1 z.2 e) ≤
        ∫ g, ((2 * ‖A‖ ^ 2) *
            (B z - B (z.1, Function.update z.2 e g)) ^ 2 +
          (2 * ‖B‖ ^ 2) *
            (A z - A (z.1, Function.update z.2 e g)) ^ 2)
            ∂nu z.1 z.2 e := by
        apply integral_mono hProd (hLeft.add hRight)
        intro g
        exact jointBCF_mul_right_update_sq_le_two A B e z g
      _ = _ := by
        rw [integral_add hLeft hRight, integral_const_mul, integral_const_mul]
  have hProd := posteriorResamplingSquare_integrable H N hN beta hbeta e (A * B)
  have hA := posteriorResamplingSquare_integrable H N hN beta hbeta e A
  have hB := posteriorResamplingSquare_integrable H N hN beta hbeta e B
  have hLeft := hB.const_mul (2 * ‖A‖ ^ 2)
  have hRight := hA.const_mul (2 * ‖B‖ ^ 2)
  change
    (∫ z, posteriorResamplingSquare H N hN beta hbeta e (A * B) z ∂muJ) ≤
      (2 * ‖A‖ ^ 2) *
        (∫ z, posteriorResamplingSquare H N hN beta hbeta e B z ∂muJ) +
      (2 * ‖B‖ ^ 2) *
        (∫ z, posteriorResamplingSquare H N hN beta hbeta e A z ∂muJ)
  calc
    (∫ z, posteriorResamplingSquare H N hN beta hbeta e (A * B) z ∂muJ) ≤
      ∫ z, ((2 * ‖A‖ ^ 2) *
          posteriorResamplingSquare H N hN beta hbeta e B z +
        (2 * ‖B‖ ^ 2) *
          posteriorResamplingSquare H N hN beta hbeta e A z) ∂muJ := by
            exact integral_mono hProd (hLeft.add hRight) hInner
    _ = _ := by
      rw [integral_add hLeft hRight, integral_const_mul, integral_const_mul]

/-- The exact half-density receiver inherits the integrated Leibniz estimate,
with the genuine posterior mean and genuine density variation separated. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
      (2 * ‖normalizedPhysicalOneSlabJointHalfDensityWeightBCF
          H N hN beta hbeta‖ ^ 2) *
        posteriorResamplingEnergy H N hN beta hbeta e
          (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f) +
      (2 * ‖normalizedPhysicalOneSlabVacuumMeanJointBCF
          H N hN beta hbeta f‖ ^ 2) *
        posteriorResamplingEnergy H N hN beta hbeta e
          (normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta) := by
  exact posteriorResamplingEnergy_mul_le_two H N hN beta hbeta e
    (normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta)
    (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f)

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

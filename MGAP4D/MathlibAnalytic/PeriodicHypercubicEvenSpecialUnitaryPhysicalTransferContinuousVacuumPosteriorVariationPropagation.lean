import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorNonstrictInfluence
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

/-!
# One-link variation propagation for continuous-vacuum posterior conditionals

PR #5162 packages the literal continuous posterior one-link conditional laws
into proof-relevant non-strict influence data.  This file proves the next
finite-volume propagation step.

For a bounded continuous configuration observable with a centered link
variation profile v and a target-link posterior update Q_t, configurations
that agree away from a source s satisfy

  |Q_t O(A) - Q_t O(C)| ≤ v_s + c_{t,s} v_t.

The proof splits the difference into:

* the direct observable change under one fixed posterior conditional law,
  bounded by v_s; and
* the change of posterior conditional law against a target-fiber centered
  test, bounded by c_{t,s} v_t.

For the diagonal source s = t, off-target invariance of the exact posterior
conditional expectation gives zero variation exactly.  Hence the packaged
one-link update profile is

  v'_s = 0                              if s = t,
  v'_s = v_s + c_{t,s} v_t             if s ≠ t.

No strict row-sum bound, finite sweep contraction, geometric decay,
Euclidean-time identification, H1-D5 exact descent, or complete
Yang--Mills mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance posteriorVariationTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorVariationCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorVariationSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorVariationMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorVariationBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A proof-relevant spatial-link variation bound for a real function on the
continuous-vacuum posterior configuration space. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
    (H N : ℕ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) where
  variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ
  variation_nonneg :
    ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e
  variation_bound :
    ∀
      (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C e →
      |F A - F C| ≤ variation e

/-- A bounded continuous posterior observable equipped with a midpoint center
on every one-link fiber. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
    (H N : ℕ)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    extends
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => O A) where
  fiberCenter :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      PeriodicHypercubicEvenSpatialSliceLink H → ℝ
  fiber_radius_bound :
    ∀
      (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (g : Matrix.specialUnitaryGroup (Fin N) ℂ),
      |O (Function.update A e g) - fiberCenter A e| ≤ variation e / 2

/-- Replacing a common target coordinate preserves agreement away from any
specified source coordinate. -/
theorem
    posterior_update_agreeOff
    {H N : ℕ}
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAgree :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C source) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
      (Function.update A target g)
      (Function.update C target g)
      source := by
  intro e he
  by_cases ht : e = target
  · subst e
    simp
  · simp [Function.update, ht, hAgree e he]

/-- Linkwise variation after one exact posterior target-link conditional
expectation. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ := by
  classical
  exact if source = target then 0
    else variation source + D.influence target source * variation target

/-- The posterior one-link updated variation profile is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation_nonneg
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariation :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
        D variation target source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
  by_cases h : source = target
  · simp [h]
  · simp only [h, if_false]
    exact add_nonneg (hVariation source)
      (mul_nonneg (D.influence_nonneg target source)
        (hVariation target))

/-- The quotient definition of the posterior bounded-continuous conditional
expectation is exactly integration against the literal posterior conditional
probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O A target =
      ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        O (Function.update A target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkNumerator
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
  rw [MeasureTheory.integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div]

/-- Under one fixed posterior conditional probability law, a uniform pointwise
difference controls the corresponding expectation difference. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorConditionalIntegral_direct_difference_abs_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hA hC : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hhA : Continuous hA)
    (hhC : Continuous hC)
    (sourceBound : ℝ)
    (hSourceBound :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |hA g - hC g| ≤ sourceBound) :
    |(∫ g, hA g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) -
      (∫ g, hC g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target)| ≤
      sourceBound := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B A target
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta B A target
  have hAInt : Integrable hA mu :=
    hhA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCInt : Integrable hC mu :=
    hhC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDiffInt : Integrable (fun g => hA g - hC g) mu :=
    hAInt.sub' hCInt
  have hAbsDiffInt : Integrable (fun g => |hA g - hC g|) mu := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hConstInt :
      Integrable (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => sourceBound) mu :=
    integrable_const sourceBound
  change
    |(∫ g, hA g ∂mu) - (∫ g, hC g ∂mu)| ≤ sourceBound
  rw [← integral_sub hAInt hCInt]
  calc
    |∫ g, hA g - hC g ∂mu| ≤ ∫ g, |hA g - hC g| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤
        ∫ _g : Matrix.specialUnitaryGroup (Fin N) ℂ, sourceBound ∂mu := by
      apply integral_mono hAbsDiffInt hConstInt
      intro g
      exact hSourceBound g
    _ = sourceBound := by simp

/-- The posterior non-strict bounded-test influence estimate scales sharply to
tests centered in a target fiber interval of radius radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_centeredTest_difference_abs_le
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hAgree :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C source)
    (h : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hh : Continuous h)
    (center radius : ℝ)
    (hRadiusNonneg : 0 ≤ radius)
    (hRadius :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |h g - center| ≤ radius) :
    |(∫ g, h g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) -
      (∫ g, h g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B C target)| ≤
      2 * D.influence target source * radius := by
  let muA :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B A target
  let muC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B C target
  letI : IsProbabilityMeasure muA :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta B A target
  letI : IsProbabilityMeasure muC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta B C target
  by_cases hRadiusZero : radius = 0
  · have hConst : h = fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => center := by
      funext g
      have hle := hRadius g
      rw [hRadiusZero] at hle
      have hz : |h g - center| = 0 :=
        le_antisymm hle (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    simp [muA, muC, hConst, hRadiusZero]
  · have hRadiusPos : 0 < radius :=
      lt_of_le_of_ne hRadiusNonneg (Ne.symm hRadiusZero)
    let phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
      fun g => (h g - center) / radius
    have hphiContinuous : Continuous phi := by
      unfold phi
      fun_prop
    have hphiBound :
        ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ, |phi g| ≤ 1 := by
      intro g
      unfold phi
      rw [abs_div, abs_of_pos hRadiusPos]
      apply (div_le_iff₀ hRadiusPos).2
      simpa only [one_mul] using hRadius g
    have hD :=
      D.conditionalIntegral_difference_abs_le
        target source A C hAgree phi hphiContinuous hphiBound
    have hphiAInt : Integrable phi muA :=
      hphiContinuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hphiCInt : Integrable phi muC :=
      hphiContinuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hAIdentity :
        (∫ g, h g ∂muA) =
          radius * (∫ g, phi g ∂muA) + center := by
      calc
        (∫ g, h g ∂muA) =
            ∫ g, radius * phi g + center ∂muA := by
          apply integral_congr_ae
          filter_upwards [] with g
          unfold phi
          field_simp [ne_of_gt hRadiusPos]
          ring
        _ = radius * (∫ g, phi g ∂muA) + center := by
          rw [
            integral_add
              (hphiAInt.const_mul radius)
              (integrable_const center),
            integral_const_mul]
          simp
    have hCIdentity :
        (∫ g, h g ∂muC) =
          radius * (∫ g, phi g ∂muC) + center := by
      calc
        (∫ g, h g ∂muC) =
            ∫ g, radius * phi g + center ∂muC := by
          apply integral_congr_ae
          filter_upwards [] with g
          unfold phi
          field_simp [ne_of_gt hRadiusPos]
          ring
        _ = radius * (∫ g, phi g ∂muC) + center := by
          rw [
            integral_add
              (hphiCInt.const_mul radius)
              (integrable_const center),
            integral_const_mul]
          simp
    change
      |(∫ g, h g ∂muA) - (∫ g, h g ∂muC)| ≤
        2 * D.influence target source * radius
    rw [hAIdentity, hCIdentity]
    have hAlgebra :
        radius * (∫ g, phi g ∂muA) + center -
            (radius * (∫ g, phi g ∂muC) + center) =
          radius *
            ((∫ g, phi g ∂muA) - ∫ g, phi g ∂muC) := by
      ring
    rw [hAlgebra, abs_mul, abs_of_pos hRadiusPos]
    calc
      radius *
          |(∫ g, phi g ∂muA) - ∫ g, phi g ∂muC| ≤
        radius * (2 * D.influence target source) :=
          mul_le_mul_of_nonneg_left hD hRadiusPos.le
      _ = 2 * D.influence target source * radius := by ring

/-- A centered posterior link-variation profile obeys the sharp non-strict
Dobrushin one-link variation propagation estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_centeredVariation_conditionalExpectationBCF_difference_abs_le
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hAgree :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C source) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O A target -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O C target| ≤
      P.variation source + D.influence target source * P.variation target := by
  let hA : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g => O (Function.update A target g)
  let hC : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g => O (Function.update C target g)
  have hUpdateA :
      Continuous
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A target g) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
        H N target).comp
        (continuous_const.prodMk continuous_id)
  have hUpdateC :
      Continuous
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update C target g) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
        H N target).comp
        (continuous_const.prodMk continuous_id)
  have hhA : Continuous hA :=
    O.continuous.comp hUpdateA
  have hhC : Continuous hC :=
    O.continuous.comp hUpdateC
  have hSourceBound :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |hA g - hC g| ≤ P.variation source := by
    intro g
    exact
      P.variation_bound source
        (Function.update A target g)
        (Function.update C target g)
        (posterior_update_agreeOff A C target source g hAgree)
  have hDirect :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorConditionalIntegral_direct_difference_abs_le
      H N hN beta hbeta B A target
      hA hC hhA hhC (P.variation source) hSourceBound
  have hLaw :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_centeredTest_difference_abs_le
      D target source A C hAgree hC hhC
      (P.fiberCenter C target) (P.variation target / 2)
      (div_nonneg (P.variation_nonneg target) (by norm_num))
      (P.fiber_radius_bound C target)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral
      H N hN beta hbeta B O A target,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral
      H N hN beta hbeta B O C target]
  change
    |(∫ g, hA g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) -
      (∫ g, hC g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B C target)| ≤
      P.variation source + D.influence target source * P.variation target
  have hSplit :
      (∫ g, hA g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B A target) -
        (∫ g, hC g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B C target) =
      ((∫ g, hA g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B A target) -
        ∫ g, hC g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B A target) +
      ((∫ g, hC g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B A target) -
        ∫ g, hC g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B C target) := by
    ring
  rw [hSplit]
  calc
    |((∫ g, hA g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) -
      ∫ g, hC g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) +
    ((∫ g, hC g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) -
      ∫ g, hC g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B C target)| ≤
      |(∫ g, hA g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) -
      ∫ g, hC g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target| +
      |(∫ g, hC g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) -
      ∫ g, hC g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B C target| :=
        abs_add_le _ _
    _ ≤ P.variation source +
        2 * D.influence target source * (P.variation target / 2) :=
      add_le_add hDirect hLaw
    _ = P.variation source +
        D.influence target source * P.variation target := by
      ring

/-- Package one exact posterior target-link conditional expectation with its
updated spatial-link variation bound.  The target coordinate has exact zero
variation; every off-target coordinate has v_s + c_{t,s} v_t. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile.conditionalExpectationVariationBound
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    {O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ}
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
      H N
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B O A target) := by
  classical
  refine
    { variation :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
          D P.variation target
      variation_nonneg :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation_nonneg
          D P.variation P.variation_nonneg target
      variation_bound := ?_ }
  intro source A C hAgree
  by_cases h : source = target
  · subst source
    have hEq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_of_agreeOffTarget
        H N hN beta hbeta B A C target O hAgree
    rw [hEq]
    simp [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation]
  · simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation,
      h] using
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_centeredVariation_conditionalExpectationBCF_difference_abs_le
        D O P target source A C hAgree)

end

end MathlibAnalytic
end MGAP4D

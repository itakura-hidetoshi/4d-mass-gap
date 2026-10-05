import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorStationarity
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkExpectationTVComparison
import Mathlib.Tactic

/-!
# Non-strict influence data for the continuous-vacuum posterior

PRs #5159--#5161 supply:

* the literal posterior one-link conditional probability law;
* its normalized continuous Haar density;
* a sharp half-L1 receiver for remote source perturbations from an ordinary
  posterior expectation-response bound;
* Feller closure and exact global posterior stationarity.

This file packages those ingredients into a continuous-state, non-strict
Dobrushin influence carrier on the spatial-slice link product.

For a source/target pair we use:

* zero on the diagonal;
* the trivial influence one for plaquette-local off-diagonal sources;
* the sharp remote coefficient
    (exp (2 * (epsilon / exp (-8 beta))) - 1) /
      (exp (2 * (epsilon / exp (-8 beta))) + 1)
  when the source is not plaquette-local to the target.

No strict row-sum bound is asserted here.  The response matrix is explicit
proof data, so no fixed-point closure is hidden.  No heat-bath-time /
Euclidean-time identification, H1-D5 exact descent, or complete
Yang--Mills mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance posteriorNonstrictInfluenceTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorNonstrictInfluenceCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorNonstrictInfluenceSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorNonstrictInfluenceMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorNonstrictInfluenceBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Two spatial-slice configurations agree away from one source coordinate. -/
def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
    {H N : ℕ}
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : Prop :=
  ∀ e, e ≠ source → A e = C e

/-- Updating the source of one configuration to the source value of another
recovers the second configuration under agree-off-source data. -/
theorem
    posteriorAgreeOff_update_source_eq
    {H N : ℕ}
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hAgree :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C source) :
    Function.update A source (C source) = C := by
  funext e
  by_cases he : e = source
  · subst e
    simp
  · simp [Function.update, he, hAgree e he]

/-- The posterior conditional density is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN beta hbeta B A target) := by
  apply Continuous.congr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_continuous
      H N hN beta hbeta B A target)
  intro g
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_eq_groundStateNormalizedDensity
      H N hN beta hbeta B A target g).symm

/-- The literal posterior conditional measure integrates a continuous gauge test
by the named normalized real density. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditional_integral_eq_densityIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (_hphi : Continuous phi) :
    (∫ g,
        phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) =
      ∫ g,
        phi g *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
            H N hN beta hbeta B A target g
        ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
  rw [MeasureTheory.integral_tilted]
  simp [continuousNormalizedExp, continuousExpPartition, smul_eq_mul, mul_comm]

/-- Posterior one-link conditional measures depend only on the off-target
environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_eq_of_agreeOffTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hAgree :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C target) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        H N hN beta hbeta B A target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        H N hN beta hbeta B C target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_eq_of_agreeOffTarget
      H N hN beta hbeta B A C target hAgree]

/-- Proof data for ordinary posterior expectation response at every genuinely
remote source/target pair. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) where
  epsilon :
    PeriodicHypercubicEvenSpatialSliceLink H →
      PeriodicHypercubicEvenSpatialSliceLink H → ℝ
  epsilon_nonneg :
    ∀ target source, 0 ≤ epsilon target source
  remote_response :
    ∀
      (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (target source : PeriodicHypercubicEvenSpatialSliceLink H),
      source ≠ target →
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source →
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C source →
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
        H N hN beta hbeta A target source (C source)
          (epsilon target source)

/-- Sharp remote influence coefficient generated by an ordinary posterior
expectation-response radius. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
    (beta epsilon : ℝ) : ℝ :=
  let R := 2 * (epsilon / Real.exp (-8 * beta))
  (Real.exp R - 1) / (Real.exp R + 1)

/-- The remote influence is nonnegative for a nonnegative response radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_nonneg
    (beta epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
        beta epsilon := by
  let R : ℝ := 2 * (epsilon / Real.exp (-8 * beta))
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (by norm_num)
      (div_nonneg hepsilon (Real.exp_pos _).le)
  have hnum : 0 ≤ Real.exp R - 1 :=
    sub_nonneg.mpr (Real.one_le_exp hR)
  have hden : 0 ≤ Real.exp R + 1 := by positivity
  simpa [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence,
    R] using div_nonneg hnum hden

/-- Nonstrict influence profile: zero diagonal, unit local fallback, and the
sharp remote response-derived coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ := by
  classical
  exact if source = target then 0
    else if periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source then 1
    else
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
        beta (epsilon target source)

/-- The nonstrict posterior influence profile is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence_nonneg
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hepsilon : ∀ target source, 0 ≤ epsilon target source)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
        H beta epsilon target source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
  by_cases hdiag : source = target
  · simp [hdiag]
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp [hlocal]
    · simp only [hlocal, if_false]
      exact
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_nonneg
          beta (epsilon target source) (hepsilon target source)

/-- The nonstrict posterior influence has exact zero diagonal. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence_diagonal_zero
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
        H beta epsilon target target = 0 := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence]

/-- Continuous-state nonstrict Dobrushin data for the literal posterior
one-link conditional laws. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) where
  influence :
    PeriodicHypercubicEvenSpatialSliceLink H →
      PeriodicHypercubicEvenSpatialSliceLink H → ℝ
  influence_nonneg :
    ∀ target source, 0 ≤ influence target source
  influence_diagonal_zero :
    ∀ target, influence target target = 0
  conditionalIntegral_difference_abs_le :
    ∀
      (target source : PeriodicHypercubicEvenSpatialSliceLink H)
      (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C source →
      ∀
        (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ),
        Continuous phi →
        (∀ g, |phi g| ≤ 1) →
        |(∫ g,
            phi g
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
              H N hN beta hbeta B A target) -
          (∫ g,
            phi g
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
              H N hN beta hbeta B C target)| ≤
          2 * influence target source

private theorem posterior_probability_integral_abs_le_one
    {X : Type*}
    [TopologicalSpace X]
    [CompactSpace X]
    [MeasurableSpace X]
    [BorelSpace X]
    (mu : Measure X)
    [IsProbabilityMeasure mu]
    (phi : X → ℝ)
    (hphi : Continuous phi)
    (hBound : ∀ x, |phi x| ≤ 1) :
    |∫ x, phi x ∂mu| ≤ 1 := by
  have hInt : Integrable phi mu :=
    hphi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAbsInt : Integrable (fun x => |phi x|) mu := by
    simpa [Real.norm_eq_abs] using hInt.norm
  calc
    |∫ x, phi x ∂mu| ≤ ∫ x, |phi x| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _x : X, (1 : ℝ) ∂mu := by
      apply integral_mono hAbsInt (integrable_const 1)
      intro x
      exact hBound x
    _ = 1 := by simp

/-- Remote expectation-response data canonically generate a complete
continuous-state nonstrict posterior influence matrix. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData.toNonstrictInfluenceData
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    (R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      H N hN beta hbeta B := by
  classical
  refine
    { influence :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
          H beta R.epsilon
      influence_nonneg :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence_nonneg
          H beta R.epsilon R.epsilon_nonneg
      influence_diagonal_zero :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence_diagonal_zero
          H beta R.epsilon
      conditionalIntegral_difference_abs_le := ?_ }
  intro target source A C hAgree phi hphi hphiBound
  by_cases hdiag : source = target
  · subst source
    have hMeasure :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B A target =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B C target :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_eq_of_agreeOffTarget
        H N hN beta hbeta B A C target hAgree
    rw [hMeasure]
    simp [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence]
  · by_cases hlocal :
      periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · let muA :=
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
      have hA :
          |∫ g, phi g ∂muA| ≤ 1 :=
        posterior_probability_integral_abs_le_one muA phi hphi hphiBound
      have hC :
          |∫ g, phi g ∂muC| ≤ 1 :=
        posterior_probability_integral_abs_le_one muC phi hphi hphiBound
      calc
        |(∫ g, phi g ∂muA) - ∫ g, phi g ∂muC| ≤
            |∫ g, phi g ∂muA| + |∫ g, phi g ∂muC| := by
              simpa [sub_eq_add_neg] using
                abs_add_le
                  (∫ g, phi g ∂muA)
                  (-(∫ g, phi g ∂muC))
        _ ≤ 1 + 1 := add_le_add hA hC
        _ = 2 *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
              H beta R.epsilon target source := by
          norm_num [
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence,
            hdiag, hlocal]
    · let p :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta B A target
      let q :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta B C target
      have hp : Continuous p := by
        simpa [p] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
            H N hN beta hbeta B A target
      have hq : Continuous q := by
        simpa [q] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
            H N hN beta hbeta B C target
      have hAeq :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditional_integral_eq_densityIntegral
          H N hN beta hbeta B A target phi hphi
      have hCeq :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditional_integral_eq_densityIntegral
          H N hN beta hbeta B C target phi hphi
      have hHalf :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalHalfL1_le_of_agreeOff_expectationResponse
          H N hN beta hbeta B A C target source
          hdiag hlocal hAgree
          (R.epsilon target source)
          (R.epsilon_nonneg target source)
          (R.remote_response A C target source hdiag hlocal hAgree)
      have hTest :=
        continuous_probabilityDensity_boundedTest_expectation_sub_abs_le_halfL1
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
          phi p q hphi hp hq
          1 (by norm_num) hphiBound
      rw [hAeq, hCeq]
      calc
        |(∫ g, phi g * p g
            ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) -
          ∫ g, phi g * q g
            ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)| ≤
            2 * 1 *
              ((2 : ℝ)⁻¹ *
                ∫ g,
                  |p g - q g|
                  ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
          hTest
        _ ≤
            2 *
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
                beta (R.epsilon target source) := by
          have hHalf' :
              (2 : ℝ)⁻¹ *
                  ∫ g,
                    |p g - q g|
                    ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
                periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
                  beta (R.epsilon target source) := by
            simpa [
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalHalfL1,
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence,
              p, q] using hHalf
          calc
            ∫ g,
                |p g - q g|
                ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) =
              2 *
                ((2 : ℝ)⁻¹ *
                  ∫ g,
                    |p g - q g|
                    ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
                ring
            _ ≤
              2 *
                periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
                  beta (R.epsilon target source) :=
              mul_le_mul_of_nonneg_left hHalf' (by norm_num)
        _ =
            2 *
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
                H beta R.epsilon target source := by
          simp [
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence,
            hdiag, hlocal]

end

end MathlibAnalytic
end MGAP4D

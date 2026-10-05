import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorVariationPropagation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredVariationFellerClosure
import Mathlib.Tactic

/-!
# Finite random-scan variation iteration for continuous-vacuum posterior conditionals

PR #5163 proves the sharp one-target posterior variation update

  v'_s = 0                              if s = t,
  v'_s = v_s + c_{t,s} v_t             if s ≠ t.

This file averages those exact one-target updates uniformly over target links,
defines the finite random-scan variation iterate

  u₀ = v,
  uₘ₊₁ = U uₘ,

and ties that abstract iterate to the actual bounded-continuous posterior
random-scan observable.

Compact midpoint recentering restores a centered variation profile after each
random-scan Feller step without enlarging the declared linkwise variation.
Thus the observable and its proof-relevant variation profile can be iterated
together, and after m steps the carried profile is exactly U^m v.

Only non-strict influence data are used.  No strict row-sum bound, geometric
decay, posterior fixed-point closure, heat-bath-time / Euclidean-time
identification, H1-D5 exact descent, or complete Yang--Mills mass-gap claim is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorRandomScanTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorRandomScanCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorRandomScanSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorRandomScanMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorRandomScanBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance posteriorRandomScanSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise uniform random-scan average of the exact posterior one-link
conditional expectations. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
    ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O A target

/-- Bounded-continuous Feller representative of the uniform posterior
random-scan conditional expectation. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ •
    ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
        H N hN beta hbeta B target O

/-- The bounded-continuous random-scan representative agrees pointwise with
the exact finite average. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
        H N hN beta hbeta B O A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF
        H N hN beta hbeta B O A := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply,
    smul_eq_mul]

/-- Exact variation profile after uniformly averaging all one-target posterior
variation updates. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
    ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
        D variation target source

/-- A nonnegative posterior variation profile remains nonnegative after
uniform random-scan averaging. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_nonneg
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
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        D variation source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun target _ =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation_nonneg
        D variation hVariation target source)

/-- A centered posterior observable profile induces a concrete variation bound
for the actual random-scan posterior expectation. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile.randomScanVariationBound
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
        H N hN beta hbeta B) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
      H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF
        H N hN beta hbeta B O) := by
  classical
  refine
    { variation :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
          D P.variation
      variation_nonneg :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_nonneg
          D P.variation P.variation_nonneg
      variation_bound := ?_ }
  intro source A C hAgree
  have hInvNonneg :
      0 ≤
        (Fintype.card
          (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hTarget (target : PeriodicHypercubicEvenSpatialSliceLink H) :
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B O A target -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B O C target| ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
          D P.variation target source :=
    (P.conditionalExpectationVariationBound D target).variation_bound
      source A C hAgree
  have hSum :
      |∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O A target -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O C target)| ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
            D P.variation target source := by
    calc
      |∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O A target -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O C target)| ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O A target -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O C target| := by
        exact Finset.abs_sum_le_sum_abs
          (fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
                H N hN beta hbeta B O A target -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
                H N hN beta hbeta B O C target)
          Finset.univ
      _ ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
            D P.variation target source := by
        apply Finset.sum_le_sum
        intro target _
        exact hTarget target
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
  calc
    |(Fintype.card
        (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O A target) -
      (Fintype.card
        (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O C target)| =
      (Fintype.card
        (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        |∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O A target -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
              H N hN beta hbeta B O C target)| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg hInvNonneg]
    _ ≤
      (Fintype.card
        (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
            D P.variation target source :=
      mul_le_mul_of_nonneg_left hSum hInvNonneg

/-- Direct pointwise posterior random-scan variation estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_randomScanConditionalExpectationBCF_difference_abs_le
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
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hAgree :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C source) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF
        H N hN beta hbeta B O A -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF
        H N hN beta hbeta B O C| ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        D P.variation source :=
  (P.randomScanVariationBound D).variation_bound source A C hAgree

/-- Exact finite random-scan iterate of a posterior spatial-link variation
profile. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    ℕ → PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
  fun m =>
    Nat.rec variation
      (fun _ previous =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
          D previous)
      m

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_zero
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
      D variation 0 = variation := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_succ
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (m : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        D variation (m + 1) =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        D
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D variation m) := by
  rfl

/-- Nonnegative initial variation remains nonnegative under every finite
posterior random-scan iterate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
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
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e) :
    ∀ m : ℕ, ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
      0 ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D variation m source := by
  intro m
  induction m with
  | zero =>
      intro source
      exact hVariation source
  | succ m ih =>
      intro source
      exact
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_nonneg
          D
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D variation m)
          ih source

/-- A posterior link-variation bound supplies a compact midpoint center on each
SU(N) one-link fiber with exactly half the same declared variation radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound_exists_fiberCenter
    {H N : ℕ}
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => O A))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∃ c : ℝ, ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
      |O (Function.update A e g) - c| ≤ P.variation e / 2 := by
  let f : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g => O (Function.update A e g)
  have hUpdate :
      Continuous
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A e g) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
        H N e).comp
        (continuous_const.prodMk continuous_id)
  have hf : Continuous f :=
    O.continuous.comp hUpdate
  have hPair :
      ∀ g h : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |f g - f h| ≤ P.variation e := by
    intro g h
    apply P.variation_bound e
    intro source hsource
    simp [Function.update, hsource]
  simpa [f] using
    (continuous_compact_exists_midpoint_center_of_pairwise_abs_sub_le
      f hf (P.variation e) hPair)

/-- Compact midpoint recentering upgrades a posterior variation bound on a
bounded-continuous observable to a centered profile without changing any
linkwise variation constant. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound.toCenteredVariationProfile
    {H N : ℕ}
    {O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ}
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => O A)) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
      H N O := by
  classical
  have hCenter :
      ∀
        (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (e : PeriodicHypercubicEvenSpatialSliceLink H),
        ∃ c : ℝ, ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          |O (Function.update A e g) - c| ≤ P.variation e / 2 :=
    fun A e =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound_exists_fiberCenter
        O P A e
  refine
    { variation := P.variation
      variation_nonneg := P.variation_nonneg
      variation_bound := P.variation_bound
      fiberCenter := fun A e => Classical.choose (hCenter A e)
      fiber_radius_bound := ?_ }
  intro A e g
  exact (Classical.choose_spec (hCenter A e)) g

/-- One exact uniform posterior random-scan Feller step is closed on the
centered variation carrier with the averaged non-strict variation profile. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile.randomScanCenteredVariationProfile
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
        H N hN beta hbeta B) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
      H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
        H N hN beta hbeta B O) := by
  let Q :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
            H N hN beta hbeta B O A) :=
    { variation :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
          D P.variation
      variation_nonneg :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_nonneg
          D P.variation P.variation_nonneg
      variation_bound := by
        intro source A C hAgree
        simpa only [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF_apply] using
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_randomScanConditionalExpectationBCF_difference_abs_le
            P D source A C hAgree }
  exact Q.toCenteredVariationProfile

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_randomScanCenteredVariationProfile_variation
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
        H N hN beta hbeta B) :
    (P.randomScanCenteredVariationProfile D).variation =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        D P.variation := by
  rfl

/-- An actual posterior bounded-continuous observable packaged with a centered
variation profile for the same observable. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
    (H N : ℕ) where
  observable :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ
  profile :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
      H N observable

/-- Package an initial centered posterior observable as a random-scan state. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile.toRandomScanCenteredState
    {H N : ℕ}
    {O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ}
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
      H N :=
  { observable := O
    profile := P }

/-- One actual posterior bounded-continuous random-scan step together with its
recentered non-strict variation profile. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState.randomScanStep
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (S :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
      H N :=
  { observable :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
        H N hN beta hbeta B S.observable
    profile := S.profile.randomScanCenteredVariationProfile D }

/-- Finite iteration of the actual posterior random-scan Feller observable and
its centered variation profile. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState.randomScanIterate
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (S :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B) :
    ℕ →
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N :=
  fun m =>
    Nat.rec S
      (fun _ previous => previous.randomScanStep D)
      m

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_zero
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (S :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B) :
    S.randomScanIterate D 0 = S := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_succ
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (S :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (m : ℕ) :
    S.randomScanIterate D (m + 1) =
      (S.randomScanIterate D m).randomScanStep D := by
  rfl

/-- The actual observable component is literally iterated by the posterior
random-scan Feller operator. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_succ_observable
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (S :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (m : ℕ) :
    (S.randomScanIterate D (m + 1)).observable =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
        H N hN beta hbeta B
        (S.randomScanIterate D m).observable := by
  rfl

/-- The profile component is updated by the posterior random-scan variation
operator at every finite step. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_succ_variation
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (S :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (m : ℕ) :
    (S.randomScanIterate D (m + 1)).profile.variation =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        D (S.randomScanIterate D m).profile.variation := by
  rfl

/-- Starting from a centered posterior observable, the variation profile
carried by the actual m-step random-scan Feller observable is exactly the
abstract finite variation iterate U^m v. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_variation_eq
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
    (m : ℕ) :
    ((P.toRandomScanCenteredState).randomScanIterate D m).profile.variation =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        D P.variation m := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      change
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D ((P.toRandomScanCenteredState).randomScanIterate D m).profile.variation =
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
              D P.variation m)
      exact congrArg
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation D)
        ih

end

end MathlibAnalytic
end MGAP4D

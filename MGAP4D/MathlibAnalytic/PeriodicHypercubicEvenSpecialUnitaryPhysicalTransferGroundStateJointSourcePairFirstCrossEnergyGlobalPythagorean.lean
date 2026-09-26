import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFirstCrossEnergyPythagorean
import Mathlib.Tactic

/-!
# Global exact Pythagorean decomposition of the ordered first cross energy

PR #4782 proves the sharp fiberwise identity

  firstCrossEnergy(C,v)
    = oldTargetVariance(C,v) + response(C,v)^2

at every ordered source/background point (C,v).

This file lifts that identity to the actual fully ordered probability law

  mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).

The only analytic bookkeeping required is to identify the ENNReal fiber
lintegral of the squared ordered residual with ENNReal.ofReal of the real
first-centered energy.  Integrability is generated from the already-proved
bounded concrete representative and the second-fiber-mean bound; no new
hypothesis is introduced.

The resulting theorem is still an exact equality.  No law-comparison
inequality, response coefficient, factor two, or finite-cardinality factor is
introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairFirstCrossEnergyGlobalPythagoreanSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairFirstCrossEnergyGlobalPythagoreanSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairFirstCrossEnergyGlobalPythagoreanSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairFirstCrossEnergyGlobalPythagoreanSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairFirstCrossEnergyGlobalPythagoreanSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairFirstCrossEnergyGlobalPythagoreanSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At one ordered outer point (C,v), the ENNReal target-fiber integral of
the ordered cross energy is exactly ofReal of the corresponding real
first-centered energy centered by the actual second-law mean. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_fiberLIntegral_eq_ofReal_firstCenteredEnergy_secondMean_of_bounded
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∫⁻ g,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left (Cv, g)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1) =
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left Cv)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
            H N source Cv)) := by
  let z :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source Cv
  let center :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
      H N hN beta hbeta B distinguishedSource source target k g₂
      F left Cv
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1
  let R : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left (Cv, g)
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1
  have hEmbed :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ => (Cv, g)) := by
    exact measurable_const.prodMk measurable_id
  have hRStrong : StronglyMeasurable R := by
    have h :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual_stronglyMeasurable
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF left).comp_measurable hEmbed
    simpa [R, Function.comp_def] using h
  have hCenterNorm : ‖center‖ ≤ |bound| := by
    simpa [center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean,
      z] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier_norm_le_of_bounded
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left z
  have hCenterAbs : |center| ≤ |bound| := by
    simpa [Real.norm_eq_abs] using hCenterNorm
  have hRBound : ∀ g, ‖R g‖ ≤ 2 * |bound| := by
    intro g
    have hSection :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection_norm_le
        H N target source F bound hbound left center (z, g)
    calc
      ‖R g‖ ≤ |bound| + |center| := by
        simpa [
          R, z, center,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual] using
          hSection
      _ ≤ |bound| + |bound| :=
        add_le_add (le_refl |bound|) hCenterAbs
      _ = 2 * |bound| := by ring
  have hRLp : MemLp R 2 μ :=
    MemLp.of_bound hRStrong.aestronglyMeasurable (2 * |bound|)
      (Filter.Eventually.of_forall hRBound)
  have hSqInt : Integrable (fun g => R g ^ 2) μ := by
    simpa only [Pi.pow_apply] using hRLp.integrable_sq
  have hOfReal :
      (∫⁻ g, ENNReal.ofReal (R g ^ 2) ∂μ) =
        ENNReal.ofReal (∫ g, R g ^ 2 ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hSqInt
      (ae_of_all μ fun g => sq_nonneg (R g))).symm
  have hKernel :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel
          H N hN beta hbeta B distinguishedSource source target k g₂ z =
        μ := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply]
    change
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update Cv.1 source (Cv.1 source)) =
        μ
    rw [Function.update_eq_self source Cv.1]
  have hReal :
      (∫ g, R g ^ 2 ∂μ) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left center z := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
    rw [hKernel]
    apply integral_congr_ae
    filter_upwards with g
    simp [
      R, z, center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual]
  calc
    (∫⁻ g,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left (Cv, g) ∂μ) =
      ∫⁻ g, ENNReal.ofReal (R g ^ 2) ∂μ := by
        apply lintegral_congr
        intro g
        rfl
    _ = ENNReal.ofReal (∫ g, R g ^ 2 ∂μ) := hOfReal
    _ =
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left center z) := by rw [hReal]
    _ = _ := by rfl

/-- Global exact ordered-law Pythagorean decomposition.

The complete ordered first-cross energy is the outer expectation of the sum of
the old-target-law variance energy and the squared concrete response. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_eq_firstVariance_add_responseSq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ Cvg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cvg
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      ∫⁻ Cv,
        (ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left Cv) +
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
                H N hN beta hbeta target source F left B distinguishedSource
                k g₂ 0
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
                  H N source Cv)) ^ 2))
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_eq_outer_targetFiber
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF left]
  apply lintegral_congr
  intro Cv
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_fiberLIntegral_eq_ofReal_firstCenteredEnergy_secondMean_of_bounded
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left Cv,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy_secondMean_eq_firstVariance_add_responseSq_of_bounded
      H N hN beta hbeta B distinguishedSource source target hne k g₂
      F hF bound hbound left Cv]
  have hVar0 :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy_nonneg
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
          H N source Cv)
  exact
    ENNReal.ofReal_add hVar0
      (sq_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
          H N hN beta hbeta target source F left B distinguishedSource
          k g₂ 0
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
            H N source Cv)))

end

end MGAP4D.MathlibAnalytic

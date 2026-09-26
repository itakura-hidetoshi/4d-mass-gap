import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFirstCrossEnergyReordered
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectFiberBridge
import Mathlib.Tactic

/-!
# Literal ordered coordinates for the first target-law cross residual

PR #4780 moves the remaining first-law cross energy exactly to the ordered law

  mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).

The remaining obstruction is now geometric rather than carrier-theoretic:
the target sample g is distributed from the law based at C, while the frozen
observable section and its centering mean are based at C[source <- v].

This file exposes that mismatch literally.

First, the existing singleton-target split reconstruction theorem is applied
to the bounded concrete section, proving

  ConcreteSection(left, offTarget(R), g)
    = F(left, R[target <- g]).

We then specialize R = C[source <- v] and prove that

* the ordered second-law center is exactly the integral of
  F(left, C[source <- v][target <- h]) under the target law based at
  C[source <- v];
* the ordered first cross residual is exactly
  F(left, C[source <- v][target <- g]) minus that second-law mean;
* the ordered cross energy is the square of this literal residual;
* its ordered-law lintegral admits a one-step disintegration whose sampling
  target law is visibly based at C.

Thus no law mismatch is hidden by a split-coordinate alias.  No inequality,
response coefficient, or finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairOrderedCrossResidualLiteralSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairOrderedCrossResidualLiteralSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairOrderedCrossResidualLiteralSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairOrderedCrossResidualLiteralSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairOrderedCrossResidualLiteralSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairOrderedCrossResidualLiteralSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A direct target-group concrete section over the off-target restriction of a
complete right configuration is literally evaluation after updating that
configuration at the target link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target right) g =
      F (left, Function.update right target g) := by
  unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
  rw [
    periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update]
  simp

/-- On ordered coordinates, the second updated background of the canonical
source-pair section is literally C[source <- v]. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground_orderedSection
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
        H N source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
          H N source Cv) =
      Function.update Cv.1 source Cv.2 := by
  rfl

/-- Literal target section frozen at C[source <- v]. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairOrderedTargetSection
    (H N : ℕ)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cvg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  F
    (left,
      Function.update
        (Function.update Cvg.1.1 source Cvg.1.2)
        target Cvg.2)

/-- The ordered concrete section used in PR #4780 is exactly the literal target
section over C[source <- v]. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairOrderedTargetSection_eq_centeredSection_zero
    (H N : ℕ)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cvg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairOrderedTargetSection
        H N source target F left Cvg =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
        H N target source F left 0
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
            H N source Cvg.1,
          Cvg.2) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairOrderedTargetSection
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground_orderedSection,
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update]
  simp

/-- The ordered second-law center is literally the target-fiber mean of the
section frozen at C[source <- v], under the target law based at that same
updated background. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean_eq_literal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cv =
      ∫ g,
        F
          (left,
            Function.update
              (Function.update Cv.1 source Cv.2)
              target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update Cv.1 source Cv.2) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondTargetFiberKernel_apply]
  simp only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground_orderedSection]
  apply integral_congr_ae
  filter_upwards with g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground_orderedSection,
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update]
  simp

/-- Literal form of the ordered first-law cross residual.

The target sample g is integrated later under the target law based at C, while
the subtracted mean is visibly the target-fiber mean based at C[source <- v]. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual_eq_literal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cvg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cvg =
      F
        (left,
          Function.update
            (Function.update Cvg.1.1 source Cvg.1.2)
            target Cvg.2) -
        ∫ h,
          F
            (left,
              Function.update
                (Function.update Cvg.1.1 source Cvg.1.2)
                target h)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂
            (Function.update Cvg.1.1 source Cvg.1.2) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground_orderedSection,
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean_eq_literal]

/-- Literal form of the ordered first-law cross energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_eq_literal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cvg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cvg =
      ENNReal.ofReal
        ((F
            (left,
              Function.update
                (Function.update Cvg.1.1 source Cvg.1.2)
                target Cvg.2) -
            ∫ h,
              F
                (left,
                  Function.update
                    (Function.update Cvg.1.1 source Cvg.1.2)
                    target h)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B source distinguishedSource target k g₂
                (Function.update Cvg.1.1 source Cvg.1.2)) ^ 2) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual_eq_literal]

/-- One-step disintegration of the ordered cross energy.

The outer ordered carrier is (C,v), while the target sample g is drawn from
the target law based at C.  The literal residual itself remains centered by the
mean based at C[source <- v], exposing the exact law mismatch. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_eq_outer_targetFiber
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ Cvg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cvg
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      ∫⁻ Cv,
        ∫⁻ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left (Cv, g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  let Phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
      H N hN beta hbeta B distinguishedSource source target k g₂ F left
  have hPhi : Measurable Phi := by
    simpa [Phi] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_measurable
        H N hN beta hbeta B distinguishedSource source target k g₂ F hF left
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
  rw [Measure.lintegral_compProd hPhi]
  apply lintegral_congr
  intro Cv
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel_apply]
  rfl

/-- Fully literal version of the one-step ordered cross-energy disintegration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_eq_literal_outer_targetFiber
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ Cvg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cvg
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      ∫⁻ Cv,
        ∫⁻ g,
          ENNReal.ofReal
            ((F
                (left,
                  Function.update
                    (Function.update Cv.1 source Cv.2)
                    target g) -
                ∫ h,
                  F
                    (left,
                      Function.update
                        (Function.update Cv.1 source Cv.2)
                        target h)
                  ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                    H N hN beta hbeta B source distinguishedSource target k g₂
                    (Function.update Cv.1 source Cv.2)) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_eq_outer_targetFiber
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF left]
  apply lintegral_congr
  intro Cv
  apply lintegral_congr
  intro g
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_eq_literal
      H N hN beta hbeta B distinguishedSource source target k g₂ F left (Cv, g)

end

end MGAP4D.MathlibAnalytic

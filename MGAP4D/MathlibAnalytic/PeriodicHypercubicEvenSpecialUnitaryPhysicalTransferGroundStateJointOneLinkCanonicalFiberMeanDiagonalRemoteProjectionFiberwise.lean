import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberMeanDiagonalRemoteProjection
import Mathlib.Tactic

/-!
# Fiberwise canonical residual equals the diagonal remote fluctuation

PR #4761 identifies the canonical genuine fiber mean with the diagonal remote
kernel-section projection at the canonical representative obtained by inserting
the identity into the target coordinate.

For the next energy-gluing step we need the same statement at every target
value over a fixed retained off-target context.  This file records the exact
coordinate invariance needed for that upgrade:

* the continuous-vacuum direct normalized one-link law depends on the right
  boundary only through its off-target restriction;
* therefore the equivalent fixed-right kernel-section one-link law has the same
  invariance;
* the diagonal remote projection is invariant under changing only the stored
  target value of the background;
* consequently the #4761 canonical-mean and residual identities hold for every
  singleton target configuration over almost every retained outer context.

No comparison constant, response estimate, or Poincare input is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

/-- The continuous-vacuum direct normalized target-link law depends on the
right boundary only through its off-target restriction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_congr_offTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right₁ right₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₁ =
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₂) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right₁ target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right₂ target := by
  classical
  have hWeight :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right₁ target =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right₂ target := by
    funext g
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
    rw [
      periodicHypercubicEvenSpatialSlice_update_eq_of_offTargetRestriction_eq
        target right₁ right₂ hoff g]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
  rw [hWeight]

/-- The equivalent normalized fixed-right kernel-section one-link law has the
same off-target invariance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_congr_offTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C right₁ right₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₁ =
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₂) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C right₁ target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C right₂ target := by
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C right₁ target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta C right₁ target :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_eq_continuousVacuumDirect
        H N hN beta hbeta C right₁ target
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta C right₂ target :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_congr_offTarget
        H N hN beta hbeta C right₁ right₂ target hoff
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C right₂ target :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_eq_continuousVacuumDirect
        H N hN beta hbeta C right₂ target).symm

/-- At diagonal current values, the remote projection is unchanged when only
the stored target value in the background configuration is changed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_congr_offTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C right₁ right₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hX : StronglyMeasurable X)
    (hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₁ =
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₂) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta C target source target
        (C source) (C target) X right₁ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta C target source target
        (C source) (C target) X right₂ := by
  classical
  have hUpdate :
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        X (Function.update right₁ target g)) =
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        X (Function.update right₂ target g)) := by
    funext g
    rw [
      periodicHypercubicEvenSpatialSlice_update_eq_of_offTargetRestriction_eq
        target right₁ right₂ hoff g]
  have hMeasure :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_congr_offTarget
      H N hN beta hbeta C right₁ right₂ target hoff
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta C target source target
        (C source) (C target) X right₁ =
      ∫ g, X (Function.update right₁ target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C right₁ target :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
        H N hN beta hbeta C right₁ target source X hX
    _ =
      ∫ g, X (Function.update right₂ target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C right₂ target := by
      rw [hUpdate, hMeasure]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta C target source target
        (C source) (C target) X right₂ :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
        H N hN beta hbeta C right₂ target source X hX).symm

/-- Almost everywhere in the retained outer context, the canonical genuine
fiber mean equals the diagonal remote projection at every target-fiber value,
not only at the canonical identity-inserted representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_diagonalRemoteKernelSectionProjection_fiberwise
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        ∀ targetCfg :
            PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
              H N hN beta hbeta target F (left, retained) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
              H N hN beta hbeta left target source target
              (left source) (left target)
              (fun D => F (left, D))
              ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                (targetCfg, retained)) := by
  classical
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_diagonalRemoteKernelSectionProjection
      H N hN beta hbeta target source F hF
  filter_upwards [hBase] with left hleft
  filter_upwards [hleft] with retained hmean
  intro targetCfg
  let split :=
    periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let right₀ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
      H N target retained
  let right := split.symm (targetCfg, retained)
  let X :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun D => F (left, D)
  have hX : StronglyMeasurable X := by
    dsimp [X]
    exact hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hOffZero :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₀ =
        retained := by
    simpa [right₀] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction_rightFromOffTarget
        H N target retained
  have hOffRight :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right =
        retained := by
    have hsnd :=
      periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_snd
        target right
    have hsplit : split right = (targetCfg, retained) := by
      exact split.apply_symm_apply _
    change (split right).2 =
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right at hsnd
    rw [hsplit] at hsnd
    exact hsnd.symm
  have hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₀ =
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right :=
    hOffZero.trans hOffRight.symm
  have hProj :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_congr_offTarget
      H N hN beta hbeta left right₀ right target source X hX hoff
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
        H N hN beta hbeta target F (left, retained) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta left target source target
        (left source) (left target) X right₀ := by
      simpa [X, right₀] using hmean
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta left target source target
        (left source) (left target) X right := hProj
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta left target source target
        (left source) (left target)
        (fun D => F (left, D))
        (split.symm (targetCfg, retained)) := by
      rfl

/-- Fiberwise form needed by the energy glue: the canonical centered residual
is exactly the diagonal remote kernel-section fluctuation for every target
value over almost every retained outer context. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation_fiberwise
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        ∀ targetCfg :
            PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ,
          F
              (left,
                (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                  (targetCfg, retained)) -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
              H N hN beta hbeta target F (left, retained) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta left target source target
            (left source) (left target)
            (fun D => F (left, D))
            ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
              (targetCfg, retained)) := by
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_diagonalRemoteKernelSectionProjection_fiberwise
      H N hN beta hbeta target source F hF
  filter_upwards [hMean] with left hleft
  filter_upwards [hleft] with retained hmean
  intro targetCfg
  rw [hmean targetCfg]
  rfl

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberMeanDiagonalRemoteProjectionFiberwise
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonVacuumL2LinearIsometry
import Mathlib.Tactic

/-!
# Descend the canonical residual identity to the physical vacuum/kernel-section laws

PR #4764 proves, Haar-almost-everywhere in the retained outer coordinates and
for every singleton target configuration, that the canonical genuine centered
residual is the diagonal remote kernel-section fluctuation.

The energy bridge now needs that identity under the actual disintegrated
physical laws:

* the outer boundary is distributed by the physical vacuum law;
* conditional on that boundary, the section point is distributed by the
  literal normalized fixed-right kernel-section law.

This file performs only that measure-theoretic descent.

The proof first transports the retained-coordinate identity back to complete
section Haar measure through the canonical target/off-target
measure-preserving equivalence.  It then uses absolute continuity of the
kernel-section law with respect to spatial Haar, and finally absolute
continuity of the physical vacuum law with respect to spatial Haar.

No new analytic estimate, comparison coefficient, response bound, or Poincare
input is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

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

/-- Every literal continuous fixed-right kernel-section probability law is
absolutely continuous with respect to the underlying spatial Haar law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_absolutelyContinuous_Haar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C ≪
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
    realIntegralWeightedProbabilityMeasure
    doobWeightedMeasure
  exact withDensity_absolutelyContinuous _ _

/-- Under the actual physical vacuum and its literal fixed-right
kernel-section law, the canonical genuine centered residual is almost
everywhere exactly the diagonal remote kernel-section fluctuation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation_vacuum_kernelSection
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    ∀ᵐ C ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta,
      ∀ᵐ A ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C,
        F (C, A) -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
              H N hN beta hbeta target F
              (C,
                periodicHypercubicEvenSpatialSliceOffTargetRestriction
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target A) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta C target source target
            (C source) (C target)
            (fun D => F (C, D)) A := by
  classical
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let μTarget :=
    Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff :=
    Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let split :=
    periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  have hSplit :
      MeasurePreserving split μ (μTarget.prod μOff) := by
    simpa [split, μ, μTarget, μOff] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceTargetOffTargetHaar_measurePreserving
        H N target
  have hFiber :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation_fiberwise
      H N hN beta hbeta target source F hF
  have hHaar :
      ∀ᵐ C ∂μ,
        ∀ᵐ A ∂μ,
          F (C, A) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                H N hN beta hbeta target F
                (C,
                  periodicHypercubicEvenSpatialSliceOffTargetRestriction
                    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target A) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta C target source target
              (C source) (C target)
              (fun D => F (C, D)) A := by
    simpa [μ, μOff] at hFiber
    filter_upwards [hFiber] with C hC
    have hProdBase :
        ∀ᵐ z ∂(μTarget.prod μOff),
          ∀ targetCfg :
              PeriodicHypercubicEvenSpatialSliceTargetLink H target →
                Matrix.specialUnitaryGroup (Fin N) ℂ,
            F (C, split.symm (targetCfg, z.2)) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                  H N hN beta hbeta target F (C, z.2) =
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta C target source target
                (C source) (C target)
                (fun D => F (C, D))
                (split.symm (targetCfg, z.2)) := by
      simpa only [Function.comp_def] using
        (Measure.quasiMeasurePreserving_snd
          (μ := μTarget) (ν := μOff)).ae hC
    have hProd :
        ∀ᵐ z ∂(μTarget.prod μOff),
          F (C, split.symm z) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                H N hN beta hbeta target F
                (C,
                  periodicHypercubicEvenSpatialSliceOffTargetRestriction
                    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
                    (split.symm z)) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta C target source target
              (C source) (C target)
              (fun D => F (C, D)) (split.symm z) := by
      filter_upwards [hProdBase] with z hz
      have hsnd :=
        periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_snd
          target (split.symm z)
      have hsplit : split (split.symm z) = z := split.apply_symm_apply z
      change
        (split (split.symm z)).2 =
          periodicHypercubicEvenSpatialSliceOffTargetRestriction
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target (split.symm z)
        at hsnd
      rw [hsplit] at hsnd
      have hoff :
          periodicHypercubicEvenSpatialSliceOffTargetRestriction
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target (split.symm z) =
            z.2 :=
        hsnd.symm
      simpa only [hoff] using hz z.1
    have hPull := hSplit.quasiMeasurePreserving.ae hProd
    filter_upwards [hPull] with A hA
    simpa only [split.apply_symm_apply] using hA
  have hKernelSection :
      ∀ᵐ C ∂μ,
        ∀ᵐ A ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C,
          F (C, A) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                H N hN beta hbeta target F
                (C,
                  periodicHypercubicEvenSpatialSliceOffTargetRestriction
                    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target A) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta C target source target
              (C source) (C target)
              (fun D => F (C, D)) A := by
    filter_upwards [hHaar] with C hC
    exact
      hC.filter_mono
        (Measure.ae_le_iff_absolutelyContinuous.mpr
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_absolutelyContinuous_Haar
            H N hN beta hbeta C))
  have hVacuumHaar : ν ≪ μ := by
    simpa [ν, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_absolutelyContinuous_Haar
        H N hN beta hbeta
  exact
    hKernelSection.filter_mono
      (Measure.ae_le_iff_absolutelyContinuous.mpr hVacuumHaar)

end

end MathlibAnalytic
end MGAP4D

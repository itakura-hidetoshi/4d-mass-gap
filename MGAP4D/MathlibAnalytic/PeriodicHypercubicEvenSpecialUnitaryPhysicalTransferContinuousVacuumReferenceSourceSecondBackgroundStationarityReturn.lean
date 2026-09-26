import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairOldVarianceHarnackOuterIntegration
import Mathlib.Tactic

/-!
# Stationarity return from the ordered source-second-background law

The ordered source/background carrier from PR #4727 is

  mu_source(dC) kappa_source(C)(dv).

Its retained source sample v is an exact one-link heat-bath sample.  Inserting
that sample back into the source coordinate therefore returns the original
source reference law exactly.

This file packages that existing one-link stationarity as both an ENNReal
lintegral identity and a measure-level pushforward identity on the ordered
carrier.  It introduces no comparison constant and no new analytic estimate.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourceSecondBackgroundStationaritySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourceSecondBackgroundStationaritySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourceSecondBackgroundStationaritySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourceSecondBackgroundStationaritySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourceSecondBackgroundStationaritySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourceSecondBackgroundStationaritySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Insert the retained ordered source sample into the source coordinate. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  Function.update Cv.1 source Cv.2

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration_measurable
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
        H N source) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
      H N source

/-- Exact one-link stationarity on the ordered source-second-background law.

For every measurable nonnegative observable of the updated background,
integrating after inserting the retained source sample is exactly integration
against the original source reference probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure_lintegral_updatedConfiguration
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (Phi : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ Cv,
      Phi
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
          H N source Cv)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) =
      ∫⁻ C, Phi C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource k g₂
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource k g₂
  have hUpdate :
      Measurable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
          H N source) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration_measurable
      H N source
  have hComp :
      Measurable
        (fun Cv =>
          Phi
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
              H N source Cv)) :=
    hPhi.comp hUpdate
  change
    (∫⁻ Cv,
      Phi
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
          H N source Cv) ∂(μ ⊗ₘ κ)) =
      ∫⁻ C, Phi C ∂μ
  rw [Measure.lintegral_compProd hComp]
  calc
    (∫⁻ C,
      ∫⁻ v,
        Phi
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
            H N source (C, v))
        ∂κ C
      ∂μ) =
      ∫⁻ C,
        ∫⁻ v, Phi (Function.update C source v)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource source k g₂ C
        ∂μ := by
      apply lintegral_congr
      intro C
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
      rfl
    _ = ∫⁻ C, Phi C ∂μ := by
      simpa [μ] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_lintegral_oneLinkFiber
          H N hN beta hbeta B source distinguishedSource source k g₂ Phi hPhi

/-- Measure-level pushforward form of the same ordered-source stationarity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure_map_updatedConfiguration
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
          H N source)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource k g₂ := by
  apply Measure.ext
  intro s hs
  let Phi :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    s.indicator (fun _ => 1)
  have hPhi : Measurable Phi := measurable_const.indicator hs
  have hStationary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure_lintegral_updatedConfiguration
      H N hN beta hbeta B distinguishedSource source k g₂ Phi hPhi
  have hUpdate :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration_measurable
      H N source
  rw [Measure.map_apply hUpdate hs]
  have hPre :
      MeasurableSet
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
          H N source) ⁻¹' s) :=
    hUpdate hs
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
          H N source) ⁻¹' s) =
      ∫⁻ Cv,
        Phi
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
            H N source Cv)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
      rw [← lintegral_indicator_one hPre]
      apply lintegral_congr
      intro Cv
      by_cases hCv :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundUpdatedConfiguration
            H N source Cv ∈ s
      · simp [Phi, hCv]
      · simp [Phi, hCv]
    _ = ∫⁻ C, Phi C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ :=
      hStationary
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ s := by
      simpa [Phi] using lintegral_indicator_one hs

end

end MGAP4D.MathlibAnalytic

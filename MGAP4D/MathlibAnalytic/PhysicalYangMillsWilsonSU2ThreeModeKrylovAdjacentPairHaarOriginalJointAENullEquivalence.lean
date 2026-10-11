import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalContinuousDensityFiniteVolumeSandwich
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# P4-Q2-CE: genuine Wilson joint / pair-Haar a.e. equivalence at finite volume

CD gave a strictly positive continuous density for the ORIGINAL physical
Wilson one-slab ground-state joint measure relative to genuine pair Haar.
This proves directly, WITHOUT replacing either measure, that all a.e.
predicates and a.e. function equalities are equivalent for these two
measures, with NO beta cutoff and for all finite physical volume.

This is the precise measure-theoretic bridge needed before investigating
zero Haar fiber variances. It does NOT assert zero variance on every
conditional fiber, reverse global Dirichlet/Poincare comparison, equality
of Riesz/physical operator kernels, or a continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Joint" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "μH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "μW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
local notation "w" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H N hN beta hbeta

/-- The actual Wilson density viewed as an ENNReal-valued function on
the ORIGINAL physical left/right joint configuration space. -/
private def p4Q2CE_density (z : Joint) : ENNReal := ENNReal.ofReal (w z)

/-- This original density is measurable with respect to genuine pair Haar. -/
private theorem p4Q2CE_density_measurable :
    Measurable (p4Q2CE_density H N hN beta hbeta) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_continuous
      H N hN beta hbeta).measurable.ennreal_ofReal

/-- The physical Wilson--Perron density is never zero, on ANY joint point. -/
private theorem p4Q2CE_density_ne_zero (z : Joint) :
    p4Q2CE_density H N hN beta hbeta z ≠ 0 := by
  apply ne_of_gt
  exact ENNReal.ofReal_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H N hN beta hbeta z)

/-- The ORIGINAL physical Wilson and pair-Haar joint laws have identical
almost-everywhere predicates for every property on full joint configurations.
This is genuine *two-way* a.e. equivalence, not a Dirichlet comparison. -/
theorem p4Q2CE_originalWilson_ae_iff_pairHaar (p : Joint → Prop) :
    (∀ᵐ z ∂μW, p z) ↔ (∀ᵐ z ∂μH, p z) := by
  rw [p4Q2CD_originalWilsonJointMeasure_eq_continuousPairHaar]
  change (∀ᵐ z ∂μH.withDensity (p4Q2CE_density H N hN beta hbeta), p z) ↔
    (∀ᵐ z ∂μH, p z)
  rw [ae_withDensity_iff (p4Q2CE_density_measurable H N hN beta hbeta)]
  constructor
  · intro h
    filter_upwards [h] with z hz
    exact hz (p4Q2CE_density_ne_zero H N hN beta hbeta z)
  · intro h
    filter_upwards [h] with z hz
    exact fun _ => hz

/-- In particular, arbitrary real-valued measurable (or nonmeasurable)
functions agree Wilson-joint-a.e. if and only if they agree pair-Haar-a.e. -/
theorem p4Q2CE_originalWilson_aeEq_iff_pairHaar
    (f g : Joint → ℝ) :
    f =ᵐ[μW] g ↔ f =ᵐ[μH] g :=
  p4Q2CE_originalWilson_ae_iff_pairHaar H N hN beta hbeta
    (fun z => f z = g z)

/-- Every exact joint-Haar null event is physically Wilson-null and
conversely. No integrability or uniform in-volume constant is required. -/
theorem p4Q2CE_originalWilson_null_iff_pairHaar (s : Set Joint) :
    μW s = 0 ↔ μH s = 0 := by
  rw [← ae_iff, ← ae_iff]
  exact p4Q2CE_originalWilson_ae_iff_pairHaar H N hN beta hbeta
    (fun z => z ∉ s)

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkFiberMeasure
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The literal target-fiber mass is exactly the generic Doob normalization
mass of its Haar density.  This is only an identification of two already
constructed finite-dimensional fiber objects; no conditional-probability claim
is made here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass_eq_doobWeightMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
        H N hN beta hbeta left right target =
      doobWeightMass
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right target) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure_apply
      H N hN beta hbeta left right target Set.univ MeasurableSet.univ]
  simp [doobWeightMass]

/-- Explicit receipt saying that a concrete ground-state one-link fiber may be
normalized as a probability measure.  The measurability field is intentionally
kept explicit: the physical vacuum is represented in `L²`, so pointwise
measurability of every exceptional fixed fiber is not inferred from global
a.e. information. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberNormalizationData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Prop where
  aemeasurable :
    AEMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  mass_pos :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
        H N hN beta hbeta left right target
  mass_lt_top :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
        H N hN beta hbeta left right target < ∞

/-- Normalize the literal ground-state target-link Haar fiber by the exact
fiber mass, using the already-canonical generic Doob weighted-measure
construction.  The definition exists for every context; probability status is
asserted only when an explicit normalization receipt is supplied. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  doobWeightedMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target)

/-- On measurable sets, the normalized fiber has the exact density
`fiberWeight / fiberMass` against normalized compact Haar measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hs : MeasurableSet s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right target s =
      ∫⁻ g in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
            H N hN beta hbeta left right target g /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
            H N hN beta hbeta left right target
        ∂(normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
  rw [doobWeightedMeasure, withDensity_apply _ hs]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass_eq_doobWeightMass
    H N hN beta hbeta left right target]
  rfl

/-- A normalization receipt upgrades the concrete target fiber to an actual
probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberNormalizationData
        H N hN beta hbeta left right target) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right target) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target
  have hMassZero : doobWeightMass μ w ≠ 0 := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass_eq_doobWeightMass
      H N hN beta hbeta left right target]
    exact ne_of_gt D.mass_pos
  have hMassTop : doobWeightMass μ w ≠ ∞ := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass_eq_doobWeightMass
      H N hN beta hbeta left right target]
    exact ne_of_lt D.mass_lt_top
  refine ⟨?_⟩
  change doobWeightedMeasure μ w Set.univ = 1
  exact doobWeightedMeasure_measure_univ μ w D.aemeasurable hMassZero hMassTop

/-- The normalized target-fiber measure depends on the right boundary only
through its off-target coordinates, just as the unnormalized fiber does. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure_congr_offTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right₁ right₂ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₁ =
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₂) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right₁ target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right₂ target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
  rw [show
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right₁ target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right₂ target by
      funext g
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight_congr_offTarget
          H N hN beta hbeta left right₁ right₂ target hoff g]

/-- In particular, changing the arbitrary base value stored at the target link
does not change the normalized target-fiber measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure_update_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₀ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left (Function.update right target g₀) target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right target := by
  classical
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure_congr_offTarget
      H N hN beta hbeta left (Function.update right target g₀) right target
  exact periodicHypercubicEvenSpatialSliceOffTargetRestriction_update_target target right g₀

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkConditionalExpectation
import Mathlib.MeasureTheory.Integral.Marginal
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

/-- The actual normalized ground-state joint density, with the complete left
boundary frozen and viewed only as a density in the right boundary variable. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ≥0∞ :=
  ENNReal.ofReal
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta (left, right))

/-- Literal target-link fiber density obtained from the actual ground-state
joint density by replacing only the selected right-boundary link.  No regular
conditional probability or Doob identification is assumed here. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
    H N hN beta hbeta left (Function.update right target g)

/-- The corresponding unnormalized target-link fiber measure over normalized
compact Haar measure.  Normalization is intentionally postponed: exceptional
zero-mass fibers of an `L²` representative must not be silently promoted to
probability measures before the almost-everywhere disintegration theorem. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)).withDensity
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target)

/-- The total mass of the literal target-link fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure
    H N hN beta hbeta left right target Set.univ

/-- The target-link fiber measure has the expected Haar-density formula on
measurable sets. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hs : MeasurableSet s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure
        H N hN beta hbeta left right target s =
      ∫⁻ g in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right target g
        ∂(normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure,
    withDensity_apply _ hs]

/-- The fiber mass is exactly Mathlib's singleton marginal of the actual joint
density in the selected right-boundary coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass_eq_lmarginal_singleton
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
        H N hN beta hbeta left right target =
      MeasureTheory.lmarginal
        (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        {target}
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
          H N hN beta hbeta left)
        right := by
  classical
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure_apply
      H N hN beta hbeta left right target Set.univ MeasurableSet.univ]
  rw [MeasureTheory.lmarginal_singleton]
  rfl

/-- Replacing the target coordinate does not change the retained off-target
configuration. -/
theorem periodicHypercubicEvenSpatialSliceOffTargetRestriction_update_target
    {H : ℕ}
    {Gauge : Type}
    [DecidableEq (PeriodicHypercubicEvenSpatialSliceLink H)]
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (right : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (g : Gauge) :
    periodicHypercubicEvenSpatialSliceOffTargetRestriction target
        (Function.update right target g) =
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right := by
  funext e
  simp [periodicHypercubicEvenSpatialSliceOffTargetRestriction, e.2]

/-- Equal off-target right-boundary data produce exactly the same completed
configuration after inserting the same target-link value. -/
theorem periodicHypercubicEvenSpatialSlice_update_eq_of_offTargetRestriction_eq
    {H : ℕ}
    {Gauge : Type}
    [DecidableEq (PeriodicHypercubicEvenSpatialSliceLink H)]
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (right₁ right₂ : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₁ =
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₂)
    (g : Gauge) :
    Function.update right₁ target g = Function.update right₂ target g := by
  funext e
  by_cases he : e = target
  · subst e
    simp
  · have hcoord := congrFun hoff
        (⟨e, he⟩ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target)
    simpa [periodicHypercubicEvenSpatialSliceOffTargetRestriction, he] using hcoord

/-- The literal ground-state target fiber density depends on the right boundary
only through its off-target restriction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight_congr_offTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right₁ right₂ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₁ =
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₂)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right₁ target g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right₂ target g := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
  rw [periodicHypercubicEvenSpatialSlice_update_eq_of_offTargetRestriction_eq
    target right₁ right₂ hoff g]

/-- Consequently the entire unnormalized target-link fiber measure depends only
on the complete left boundary and the right off-target configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure_congr_offTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right₁ right₂ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₁ =
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right₂) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure
        H N hN beta hbeta left right₁ target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure
        H N hN beta hbeta left right₂ target := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure
  rw [show
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right₁ target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right₂ target by
      funext g
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight_congr_offTarget
          H N hN beta hbeta left right₁ right₂ target hoff g]

/-- In particular, changing the base representative at the target itself does
not alter the target-link fiber measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure_update_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₀ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure
        H N hN beta hbeta left (Function.update right target g₀) target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure
        H N hN beta hbeta left right target := by
  classical
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure_congr_offTarget
      H N hN beta hbeta left (Function.update right target g₀) right target
  exact periodicHypercubicEvenSpatialSliceOffTargetRestriction_update_target target right g₀

end

end MathlibAnalytic
end MGAP4D

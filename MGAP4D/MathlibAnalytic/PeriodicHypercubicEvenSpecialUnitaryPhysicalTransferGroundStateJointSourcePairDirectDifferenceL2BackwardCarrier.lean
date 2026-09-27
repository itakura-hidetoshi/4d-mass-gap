import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairDirectDifferenceL2OrderedEnergy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateOrderedDirectBackwardCarrier
import Mathlib.Tactic

/-!
# Direct-difference L2 energy on the backward heat-bath carrier

PR #4865 bounds the squared norm of the actual physical direct-difference L2
vector by the exact ordered direct average with coefficient one.

PR #4735 identifies the ENNReal presentation of that ordered average exactly
with the backward source direct-fiber energy integrated against the reversible
target heat-bath joint law.

This file composes those two facts:

  ofReal ||DirectDifferenceL2(target, source)||^2
    <=
  integral_(backward target heat-bath joint law)
    BackwardDirectFiberEnergy(source).

No target sum, Cauchy estimate, response symmetry, factor two, or stage-residual
identification is introduced.  The point is only to place the physical direct
term on the same backward carrier used by the existing local/law-response
decomposition.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance directL2BackwardCarrierSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance directL2BackwardCarrierSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance directL2BackwardCarrierSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance directL2BackwardCarrierSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance directL2BackwardCarrierSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual direct-difference L2 energy is controlled, with coefficient one,
by the backward source direct-fiber energy on the reversible target heat-bath
joint carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_norm_sq_ofReal_le_backwardHeatBathJoint
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left center‖ ^ 2) ≤
      ∫⁻ CD,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectFiberEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ CD
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂ := by
  have hDirect :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_norm_sq_le_orderedDirectAverageEnergy
      H N hN beta hbeta B distinguishedSource source target hne
      k g₂ F hF bound hbound left center
  have hOfReal :
      ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
              H N hN beta hbeta B distinguishedSource source target k g₂
              F hF bound hbound left center‖ ^ 2) ≤
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
            H N hN beta hbeta target source F left B distinguishedSource k g₂) :=
    ENNReal.ofReal_le_ofReal hDirect
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy_ofReal_eq_backwardHeatBathJoint
      H N hN beta hbeta target source hne F hF bound hbound
      left B distinguishedSource k g₂] at hOfReal
  exact hOfReal

end

end MGAP4D.MathlibAnalytic

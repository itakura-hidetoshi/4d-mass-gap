import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalResponseRMSV5_FG
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# P4-Q2-FH: genuine Wilson conditional RMS — spatial masses and active links

FG gives the EXACT original physical link energy as the genuine Wilson
posterior conditional square integrated OUTSIDE against original pair-Haar.

This first FH step keeps the actual source-/link-dependent conditional
RMS means as a nonnegative measure on the finite physical spatial-link
carrier. We prove exact finite-region/complement decomposition, monotonicity,
zero-region characterization, and an intrinsic threshold-counting inequality:

  epsilon * card {e | epsilon <= mean_z M2(e,f,z)}
      <= sum_e mean_z M2(e,f,z).

The same certificate holds for the actual physical posterior defect after
multiplying by the unchanged inverse-transfer normalization squared / 2.

These are finite-volume identities, not a claim of geometric spatial decay
or an H-/scale-uniform bound. The inner conditional law is ALWAYS genuine
interacting Wilson; the outer integral alone is against pair-Haar.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

private noncomputable instance p4Q2FH_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The actual nonnegative outside pair-Haar mean of FG's ORIGINAL
Wilson conditional link response square, with physical source f retained. -/
noncomputable def p4Q2FH_originalWilsonConditionalRMSLinkMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ z, p4Q2FG_originalWilsonRelativeResponseConditionalSquare
    H N hN beta hbeta f e z
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N

theorem p4Q2FH_originalWilsonConditionalRMSLinkMean_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ p4Q2FH_originalWilsonConditionalRMSLinkMean
      H N hN beta hbeta f e := by
  unfold p4Q2FH_originalWilsonConditionalRMSLinkMean
  exact integral_nonneg (fun z =>
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare_nonneg
      H N hN beta hbeta f e z)

/-- True linkwise Wilson conditional-RMS mass on a selectable subset of
the ORIGINAL finite-volume spatial links (no arbitrary Haar posterior). -/
noncomputable def p4Q2FH_originalWilsonSpatialRMSMass
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  S.sum (p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f)

theorem p4Q2FH_originalWilsonSpatialRMSMass_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 ≤ p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S := by
  unfold p4Q2FH_originalWilsonSpatialRMSMass
  exact Finset.sum_nonneg (fun e _he =>
    p4Q2FH_originalWilsonConditionalRMSLinkMean_nonneg H N hN beta hbeta f e)

/-- No geometric loss: the genuine conditional RMS spatial mass is
monotone under inclusion of ACTUAL physical link sets. -/
theorem p4Q2FH_originalWilsonSpatialRMSMass_mono
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S T : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (hST : S ⊆ T) :
    p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S ≤
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f T := by
  classical
  unfold p4Q2FH_originalWilsonSpatialRMSMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun e _he _hnot =>
      p4Q2FH_originalWilsonConditionalRMSLinkMean_nonneg
        H N hN beta hbeta f e)

/-- A zero genuine Wilson RMS region is characterized exactly by
vanishing of EVERY constituent true conditional RMS link mean. -/
theorem p4Q2FH_originalWilsonSpatialRMSMass_eq_zero_iff
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S = 0 ↔
      ∀ e ∈ S,
        p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f e = 0 := by
  unfold p4Q2FH_originalWilsonSpatialRMSMass
  exact Finset.sum_eq_zero_iff_of_nonneg (fun e _he =>
    p4Q2FH_originalWilsonConditionalRMSLinkMean_nonneg
      H N hN beta hbeta f e)

/-- Exact disjoint spatial-region splitting; unlike a global sup count,
all original Wilson posterior means are retained. -/
theorem p4Q2FH_originalWilsonSpatialRMSMass_disjointUnion
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S T : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (hST : Disjoint S T) :
    p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f (S ∪ T) =
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S +
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f T := by
  classical
  unfold p4Q2FH_originalWilsonSpatialRMSMass
  exact Finset.sum_union hST

/-- An arbitrary actual spatial patch and its genuine finite
complement together contain EXACTLY the full conditional RMS mass. -/
theorem p4Q2FH_originalWilsonSpatialRMSMass_patch_plus_tail
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S +
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f
        ((Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) \ S) =
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  classical
  unfold p4Q2FH_originalWilsonSpatialRMSMass
  have hs : S ⊆ (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :=
    Finset.subset_univ S
  simpa only [add_comm] using
    (Finset.sum_sdiff
      (f := p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f) hs)

/-- FH is a genuine reformulation of FG's true interacting Wilson
physical energy: no new physical measure or unproved volume constant. -/
theorem p4Q2FH_originalPhysicalPatchEnergy_eq_spatialRMSMass
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta f S =
      (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹) ^ 2 *
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S := by
  simpa only [p4Q2FH_originalWilsonSpatialRMSMass,
    p4Q2FH_originalWilsonConditionalRMSLinkMean,
    p4Q2FG_originalWilsonPairHaarConditionalRMSPatchEnergy] using
    p4Q2FG_originalPhysicalRestrictedEnergy_eq_pairHaarConditionalRMSPatch
      H N hN beta hbeta f S

/-- Observable, source-dependent spatial high-response links, selected
using the actual Wilson conditional mean-square rather than a guessed
distance or artificial conditional Haar law. -/
noncomputable def p4Q2FH_originalWilsonActiveRMSLinks
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (epsilon : ℝ) : Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.filter (fun e =>
    epsilon ≤ p4Q2FH_originalWilsonConditionalRMSLinkMean
      H N hN beta hbeta f e)

/-- Rigorous finite-volume counting inequality for actual high-response
Wilson links. This does NOT provide an H-uniform tail or a decay law:
the full right-hand side is the still-uncontrolled genuine RMS mass. -/
theorem p4Q2FH_originalWilsonActiveRMSLinks_card_threshold_le_total
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (epsilon : ℝ) :
    epsilon * ((p4Q2FH_originalWilsonActiveRMSLinks
      H N hN beta hbeta f epsilon).card : ℝ) ≤
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  classical
  let A := p4Q2FH_originalWilsonActiveRMSLinks H N hN beta hbeta f epsilon
  have hLower :
      epsilon * (A.card : ℝ) ≤
        p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f A := by
    unfold p4Q2FH_originalWilsonSpatialRMSMass
    calc
      epsilon * (A.card : ℝ) = A.sum (fun _ => epsilon) := by
        simp [nsmul_eq_mul, mul_comm]
      _ ≤ A.sum (fun e =>
        p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f e) := by
          apply Finset.sum_le_sum
          intro e he
          change e ∈ (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).filter
            (fun t => epsilon ≤
              p4Q2FH_originalWilsonConditionalRMSLinkMean
                H N hN beta hbeta f t) at he
          exact (Finset.mem_filter.mp he).2
  change epsilon * (A.card : ℝ) ≤
    p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  exact le_trans hLower (p4Q2FH_originalWilsonSpatialRMSMass_mono
    H N hN beta hbeta f A Finset.univ (Finset.subset_univ A))

/-- The same intrinsic threshold-counting bound is inherited by the
genuine original Wilson physical projection energy WITH the authentic
inverse-transfer normalization unchanged. -/
theorem p4Q2FH_originalWilsonActiveRMSLinks_weighted_count_le_physicalEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (epsilon : ℝ) :
    ((1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹) ^ 2) *
      (epsilon * ((p4Q2FH_originalWilsonActiveRMSLinks
        H N hN beta hbeta f epsilon).card : ℝ)) ≤
      p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  have hAlpha : 0 ≤ (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹) ^ 2 := by
    positivity
  have hCount := p4Q2FH_originalWilsonActiveRMSLinks_card_threshold_le_total
    H N hN beta hbeta f epsilon
  have hScaled := mul_le_mul_of_nonneg_left hCount hAlpha
  rw [p4Q2FH_originalPhysicalPatchEnergy_eq_spatialRMSMass
    H N hN beta hbeta f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))]
  exact hScaled

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FH_originalWilsonConditionalRMSLinkMean_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FH_originalWilsonSpatialRMSMass_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FH_originalWilsonSpatialRMSMass_mono
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FH_originalWilsonSpatialRMSMass_eq_zero_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FH_originalWilsonSpatialRMSMass_disjointUnion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FH_originalWilsonSpatialRMSMass_patch_plus_tail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FH_originalPhysicalPatchEnergy_eq_spatialRMSMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FH_originalWilsonActiveRMSLinks_card_threshold_le_total
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FH_originalWilsonActiveRMSLinks_weighted_count_le_physicalEnergy

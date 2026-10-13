import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalRMSSpatialSupportV5_FH
import Mathlib.Tactic

/-!
# P4-Q2-FI: spatial lower-profile certificate for genuine Wilson conditional RMS

This file isolates the exact bridge needed between an analytic single-link
Wilson-kernel lower estimate and the existing FH *actual* Wilson RMS mass.
The input hLower is deliberately explicit: it is NOT proved here.

For a real q and c >= 0, assume actual m_e(f) >= c*q on a finite
physical spatial-link set S. We show:
  (card S)*c*q <= sum_{e in S} m_e(f),
and the exact physical-energy version with unchanged inverse transfer norm.
This is not a proof of a Wilson spectral bound, a volume-uniform estimate,
or a spatial-decay law. In particular the kernel-derived positivity of c
must be discharged in a later analytic file.

The physical source, frozen beta and genuine Wilson posterior are unchanged.
No new axioms, sorry or independent posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

private noncomputable instance p4Q2FI_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A proposed pointwise link-mass estimate, stated as a certificate
on the original FH function and NOT silently introduced as a theorem. -/
def p4Q2FI_originalWilsonRMSLowerCertificate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (c q : ℝ) : Prop :=
  ∀ e ∈ S, c * q ≤
    p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f e

/-- A kernel-dependent per-link lower bound forces a spatial mass
proportional to the NUMBER of physical links in the selected region. -/
theorem p4Q2FI_originalWilsonRMSMass_card_lower
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (c q : ℝ)
    (hLower : p4Q2FI_originalWilsonRMSLowerCertificate
      H N hN beta hbeta f S c q) :
    (S.card : ℝ) * (c * q) ≤
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S := by
  unfold p4Q2FH_originalWilsonSpatialRMSMass
  calc
    (S.card : ℝ) * (c * q) = ∑ _e ∈ S, c * q := by simp
    _ ≤ ∑ e ∈ S,
      p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f e := by
        apply Finset.sum_le_sum
        intro e he
        exact hLower e he

/-- Restriction to a patch and then monotonicity both preserve the genuine
Wilson mass lower bound. -/
theorem p4Q2FI_originalWilsonTotalRMSMass_card_lower
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (c q : ℝ)
    (hLower : p4Q2FI_originalWilsonRMSLowerCertificate
      H N hN beta hbeta f S c q) :
    (S.card : ℝ) * (c * q) ≤
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  exact (p4Q2FI_originalWilsonRMSMass_card_lower
    H N hN beta hbeta f S c q hLower).trans
    (p4Q2FH_originalWilsonSpatialRMSMass_mono
      H N hN beta hbeta f S Finset.univ (Finset.subset_univ S))

/-- The physical Dirichlet-energy version does not drop the extra
inverse-top-transfer normalization already present in FG/FH. -/
theorem p4Q2FI_originalPhysicalEnergy_card_lower
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (c q : ℝ)
    (hLower : p4Q2FI_originalWilsonRMSLowerCertificate
      H N hN beta hbeta f S c q) :
    ((1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹) ^ 2) *
      ((S.card : ℝ) * (c * q)) ≤
      p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta f S := by
  have hnonneg : 0 ≤ (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹) ^ 2 := by positivity
  rw [p4Q2FH_originalPhysicalPatchEnergy_eq_spatialRMSMass
    H N hN beta hbeta f S]
  exact mul_le_mul_of_nonneg_left
    (p4Q2FI_originalWilsonRMSMass_card_lower
      H N hN beta hbeta f S c q hLower) hnonneg

/-- If all actual link masses dominate a common source-dependent
threshold, every original physical link is active at that threshold. -/
theorem p4Q2FI_originalWilsonAllLinks_active_of_lower
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (c q : ℝ)
    (hLower : p4Q2FI_originalWilsonRMSLowerCertificate
      H N hN beta hbeta f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) c q) :
    p4Q2FH_originalWilsonActiveRMSLinks H N hN beta hbeta f (c * q) =
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  classical
  apply Finset.eq_univ_of_forall
  intro e
  change e ∈ (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).filter
    (fun t => c * q ≤
      p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f t)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLower e (Finset.mem_univ _)⟩

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_originalWilsonRMSMass_card_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_originalWilsonTotalRMSMass_card_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_originalPhysicalEnergy_card_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_originalWilsonAllLinks_active_of_lower

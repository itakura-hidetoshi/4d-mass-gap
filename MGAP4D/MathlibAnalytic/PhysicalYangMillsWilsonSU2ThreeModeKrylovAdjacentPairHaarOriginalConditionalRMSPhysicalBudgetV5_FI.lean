import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalRMSSpatialSupportV5_FH
import Mathlib.Tactic

/-!
# P4-Q2-FI: physical Hilbert budgets for genuine Wilson conditional link RMS

FG identifies each genuine Wilson conditional-response mean with the
physical pair-Haar link projection defect, retaining the extra inverse
physical-transfer normalization. FH makes the means a finite spatial mass.

This file proves, for EVERY actual physical Haar-L2 input and link:
* unconditional RMS link mean <= 2 * ||f||^2, independent of volume,
  without a local-supremum or independent-Haar posterior replacement;
* its exact finite-patch summation and at-beta-zero vanishing;
* an explicit theorem interface for a *future* strictly positive
  per-link Wilson kernel/frame floor, and its all-link/tail consequences.

The last certificate is CONDITIONAL: positivity of a common physical
link floor is NOT assumed to be already proved by FG/FH. Its genuine
Wilson SU(2) discharge needs the kernel-dependent, left-Haar-averaged
projection estimate. No spatial locality or C3 closure is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

private noncomputable instance p4Q2FI_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Every genuine ORIGINAL Wilson posterior-link conditional RMS
pair-Haar mean is bounded by twice the ACTUAL physical input norm
squared, uniformly in the link, volume and beta. This is the
projection-contraction regime expressed on FG's conditional carrier. -/
theorem p4Q2FI_originalWilsonConditionalRMSLinkMean_le_twice_input_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f e ≤
      2 * ‖f‖ ^ 2 := by
  let L : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let M : ℝ := p4Q2FH_originalWilsonConditionalRMSLinkMean
    H N hN beta hbeta f e
  let D : ℝ := p4Q2FD_originalPhysicalLinkDefect
    H N hN beta hbeta f e
  let C : ℝ := p4Q2FD_originalPhysicalTwoRegimeCoefficient
    H N hN beta hbeta
  have hL : 0 < L := by
    exact inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)
  have hEq : D = (1 / 2 : ℝ) * L ^ 2 * M :=
    p4Q2FG_originalPhysicalLinkDefect_eq_half_pairHaarConditionalRMS
      H N hN beta hbeta f e
  have hReg : D ≤ C * ‖f‖ ^ 2 :=
    p4Q2FD_originalPhysicalLinkDefect_le_twoRegime
      H N hN beta hbeta f e
  have hCoeff : C ≤ L ^ 2 := by
    change min (L ^ 2)
      ((1 / 2 : ℝ) * L ^ 4 * (Real.exp (8 * beta) ^ 3 - 1) ^ 2) ≤ L ^ 2
    exact min_le_left _ _
  have hUp : D ≤ L ^ 2 * ‖f‖ ^ 2 :=
    le_trans hReg (mul_le_mul_of_nonneg_right hCoeff (sq_nonneg ‖f‖))
  have hScaled : L ^ 2 * M ≤ L ^ 2 * (2 * ‖f‖ ^ 2) := by
    nlinarith [hEq, hUp]
  exact (mul_le_mul_left (pow_pos hL 2)).mp hScaled

/-- Genuine Wilson conditional RMS on a finite physical spatial patch
is controlled by its OWN cardinality and input norm, not by an
invented proxy measure or the full lattice when the patch is smaller. -/
theorem p4Q2FI_originalWilsonConditionalRMSPatch_le_card_twice_input_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S ≤
      (S.card : ℝ) * (2 * ‖f‖ ^ 2) := by
  unfold p4Q2FH_originalWilsonSpatialRMSMass
  calc
    S.sum (p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f) ≤
      S.sum (fun _e => 2 * ‖f‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro e _he
        exact p4Q2FI_originalWilsonConditionalRMSLinkMean_le_twice_input_sq
          H N hN beta hbeta f e
    _ = (S.card : ℝ) * (2 * ‖f‖ ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- At beta=0 the ORIGINAL Wilson relative-response BCF is IDENTICALLY
zero, so its actual (not surrogate) Wilson conditional RMS mean vanishes
at every finite-volume physical link, before any limiting argument. -/
theorem p4Q2FI_originalWilsonConditionalRMSLinkMean_beta_zero
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FH_originalWilsonConditionalRMSLinkMean
      H N hN 0 (le_refl 0) f e = 0 := by
  have hB := p4Q2FG_originalWilsonRelativeResponse_eq_zero_beta_zero
    H N hN f e
  simp [p4Q2FH_originalWilsonConditionalRMSLinkMean,
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare, hB]

/-- The same exact beta-zero identity holds on arbitrary genuine
finite physical spatial-link patches. -/
theorem p4Q2FI_originalWilsonConditionalRMSPatch_beta_zero
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FH_originalWilsonSpatialRMSMass H N hN 0 (le_refl 0) f S = 0 := by
  classical
  simp [p4Q2FH_originalWilsonSpatialRMSMass,
    p4Q2FI_originalWilsonConditionalRMSLinkMean_beta_zero H N hN f]

/-- A spatially UNIFORM genuine Wilson one-link RMS floor, once
proved from its actual kernel, forces extensive genuine RMS mass on
every finite patch. The floor hypothesis is explicit and is NOT
silently supplied by FH's positivity or conditional counting. -/
theorem p4Q2FI_certifiedWilsonLinkFloor_forces_patch_mass
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (kappa : ℝ)
    (hFloor : ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      kappa * ‖f‖ ^ 2 ≤
        p4Q2FH_originalWilsonConditionalRMSLinkMean
          H N hN beta hbeta f e)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    (S.card : ℝ) * (kappa * ‖f‖ ^ 2) ≤
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S := by
  unfold p4Q2FH_originalWilsonSpatialRMSMass
  calc
    (S.card : ℝ) * (kappa * ‖f‖ ^ 2) =
        S.sum (fun _e => kappa * ‖f‖ ^ 2) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ S.sum (p4Q2FH_originalWilsonConditionalRMSLinkMean H N hN beta hbeta f) := by
      apply Finset.sum_le_sum
      intro e _he
      exact hFloor e

/-- The open-positive-floor obligation would force the mass OUTSIDE
any selected finite physical patch to scale with the ACTUAL number
of remaining links. This theorem does not claim the floor exists. -/
theorem p4Q2FI_certifiedWilsonLinkFloor_forces_complement_tail
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (kappa : ℝ)
    (hFloor : ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      kappa * ‖f‖ ^ 2 ≤
        p4Q2FH_originalWilsonConditionalRMSLinkMean
          H N hN beta hbeta f e)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    (((Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) \ S).card : ℝ) *
        (kappa * ‖f‖ ^ 2) ≤
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f
        ((Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) \ S) := by
  exact p4Q2FI_certifiedWilsonLinkFloor_forces_patch_mass
    H N hN beta hbeta f kappa hFloor _

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_originalWilsonConditionalRMSLinkMean_le_twice_input_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_originalWilsonConditionalRMSPatch_le_card_twice_input_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_originalWilsonConditionalRMSLinkMean_beta_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_originalWilsonConditionalRMSPatch_beta_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_certifiedWilsonLinkFloor_forces_patch_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FI_certifiedWilsonLinkFloor_forces_complement_tail

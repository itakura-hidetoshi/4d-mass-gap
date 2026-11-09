import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedSourceHaarL2NonvanishingV5_PZ37AIY

/-!
# P4-Q2-PZ37AIZ — original normalized ZW source L² nonzero at ALL positive couplings

The ORIGINAL complete SU(2) Wilson one-slab operator, with its true
spatial halfweights, true product-Haar measure, original signed ZW Gauss-law
physical L² source and existing physical norm normalization, is unchanged.

AIY proved true physical Haar-L² nonvanishing for the AIT half-Haar coupling
interval. The actual AIG predecessor contains a stronger logically distinct
fact: at EVERY finite H and EVERY beta>0, the ORIGINAL full-margin strict
negative transfer region has positive genuine Haar measure. AIG proves this
from its original weighted negative transfer average; it does not follow
merely from a nonzero point.

AIW proves the exact set equality of the original AIG negative region and
the normalized continuous integral's negative-margin sublevel set.
AIY proves the descent from nonzero Haar mass of that strict negative set,
using the true a.e. representative of the EXISTING normalized physical
operator applied to the unchanged signed ZW source, to nonzero physical L².

Their type-correct composition removes the AIT coupling upper endpoint,
proving ||N_H,beta f_H||_(genuine physical L²)>0 for ALL finite H and beta>0.
The corresponding unnormalized physical L² image is nonzero as well, and
the source norm still bounds the normalized image from above.
In particular ANY schedule beta_H>0 is covered, with NO uniform positive
lower bound on the resulting L² amplitudes asserted.

This uses the original source, Haar measure and operators; it neither
replaces them nor postulates full support, new regularity, physical
projection orthogonality, a uniform gap, or a common volume Hilbert space.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgZ" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muZ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fZ" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "PZ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "NZ" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "uZ" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mZ" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

/-- The EXACT existing original AIG strict negative region has positive
true Haar measure for EVERY positive beta and original finite volume.
The strict normalized negative set is definitionally the same subset via
AIW, rather than a new artificially weakened margin. -/
theorem p4Q2PZ37AIZ_originalNormalizedNegativeRegion_HaarMeasure_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < muZ {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)} := by
  rw [p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original
    H beta hbeta.le]
  exact p4Q2PZ37AIG_originalNegativeTransferRegion_measure_pos
    H beta hbeta

/-- Direct descent: original AIG positive Haar mass + AIW exact region
identification + AIY true normalized-operator a.e.-to-physical-L² bridge.
There is NO coupling upper bound, and no imported pointwise claim about
an arbitrary L² representative. -/
theorem p4Q2PZ37AIZ_originalNormalizedPhysicalSource_ne_zero_allPositive
    (beta : ℝ) (hbeta : 0 < beta) :
    NZ beta hbeta.le fZ ≠ 0 :=
  p4Q2PZ37AIY_originalNormalizedPhysicalSource_ne_zero_of_regionMeasure
    H beta hbeta
    (ne_of_gt
      (p4Q2PZ37AIZ_originalNormalizedNegativeRegion_HaarMeasure_pos
        H beta hbeta))

/-- The TRUE Gauss-law physical L² norm of the ORIGINAL normalized ZW
source image is strictly positive for EVERY finite H and beta>0,
including couplings above the AIT half-Haar cutoff. -/
theorem p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_allPositive
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < ‖NZ beta hbeta.le fZ‖ :=
  norm_pos_iff.mpr
    (p4Q2PZ37AIZ_originalNormalizedPhysicalSource_ne_zero_allPositive
      H beta hbeta)

/-- Nonzero normalization cannot manufacture a source image:
the ACTUAL original unnormalized physical transfer is nonzero on the
unchanged source for every beta>0. This is an L² statement, not just
an existence of a right-boundary continuous representative. -/
theorem p4Q2PZ37AIZ_originalRawPhysicalSource_ne_zero_allPositive
    (beta : ℝ) (hbeta : 0 < beta) :
    PZ beta hbeta.le fZ ≠ 0 := by
  intro hz
  have hNorm : ‖NZ beta hbeta.le fZ‖ = 0 := by
    simpa [hz] using
      (p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_eq_ratio
        H beta hbeta.le)
  exact
    (ne_of_gt
      (p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_allPositive
        H beta hbeta)) hNorm

/-- Strict positive true L² amplitude for the ORIGINAL RAW physical
transfer on its original signed ZW physical source at every beta>0. -/
theorem p4Q2PZ37AIZ_originalRawPhysicalSource_norm_pos_allPositive
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < ‖PZ beta hbeta.le fZ‖ :=
  norm_pos_iff.mpr
    (p4Q2PZ37AIZ_originalRawPhysicalSource_ne_zero_allPositive
      H beta hbeta)

/-- Full actual physical L² amplitude interval for all positive couplings.
The upper bound is the EXISTING normalized-operator contraction; no
new source norm normalization or lower floor is inserted. -/
theorem p4Q2PZ37AIZ_originalNormalizedPhysicalSource_pos_le_input_allPositive
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < ‖NZ beta hbeta.le fZ‖ ∧
      ‖NZ beta hbeta.le fZ‖ ≤ ‖fZ‖ :=
  ⟨p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_allPositive
      H beta hbeta,
    p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_le_input
      H beta hbeta.le⟩

/-- The same exact source-image result applies pointwise to EVERY
volume-dependent positive coupling schedule, even if beta_H approaches
zero or diverges. The resulting family of Hilbert spaces is indexed by H,
so this is NOT a uniform amplitude-floor or common-space limit theorem. -/
theorem p4Q2PZ37AIZ_originalNormalizedPhysicalSource_positiveSchedule
    (beta : ℕ → ℝ) (hbeta : ∀ K : ℕ, 0 < beta K) :
    ∀ K : ℕ,
      0 < ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        K 2 (by norm_num) (beta K) (hbeta K).le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection K)‖ := by
  intro K
  exact p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_allPositive
    K (beta K) (hbeta K)

/-- Audit-visible same-configuration package: positive genuine normalized
source L² norm, norm one of the ALREADY EXISTING normalized operator and
strictly positive genuine Haar measure of the unchanged full-margin
negative region, ALL at the same positive beta and finite H. -/
theorem p4Q2PZ37AIZ_originalPositiveCoupling_physicalNormAndRegion
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < ‖NZ beta hbeta.le fZ‖ ∧
    ‖NZ beta hbeta.le‖ = 1 ∧
    0 < muZ {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)} :=
  ⟨p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_allPositive
      H beta hbeta,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
      H 2 (by norm_num) beta hbeta.le,
    p4Q2PZ37AIZ_originalNormalizedNegativeRegion_HaarMeasure_pos H beta hbeta⟩

/-- Explicitly beyond AIY's former finite-volume AIT half-Haar endpoint,
the true original normalized ZW physical source image is STILL nonzero in
the SAME original Haar-L². No half-Haar claim is transported past cutoff. -/
theorem p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_above_AIT_cutoff :
    0 < ‖NZ (p4Q2PZ37AIT_volumeGrowingCouplingCutoff H + 1)
      (by
        have hc := p4Q2PZ37AIT_volumeGrowingCouplingCutoff_pos H
        linarith) fZ‖ := by
  have hc := p4Q2PZ37AIT_volumeGrowingCouplingCutoff_pos H
  have hbeta : 0 < p4Q2PZ37AIT_volumeGrowingCouplingCutoff H + 1 := by
    linarith
  exact p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_allPositive
    H (p4Q2PZ37AIT_volumeGrowingCouplingCutoff H + 1) hbeta

/-- The same all-positive volume-dependent schedules preserve strict
nonzero true Haar-L² output of the ORIGINAL RAW Gauss-law physical transfer.
This does not assert an H-uniform lower amplitude floor. -/
theorem p4Q2PZ37AIZ_originalRawPhysicalSource_positiveSchedule
    (beta : ℕ → ℝ) (hbeta : ∀ K : ℕ, 0 < beta K) :
    ∀ K : ℕ,
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        K 2 (by norm_num) (beta K) (hbeta K).le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection K)‖ := by
  intro K
  exact p4Q2PZ37AIZ_originalRawPhysicalSource_norm_pos_allPositive
    K (beta K) (hbeta K)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Actual axioms for each new declaration, independently printed. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalNormalizedNegativeRegion_HaarMeasure_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalNormalizedPhysicalSource_ne_zero_allPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_allPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalRawPhysicalSource_ne_zero_allPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalRawPhysicalSource_norm_pos_allPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalNormalizedPhysicalSource_pos_le_input_allPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalNormalizedPhysicalSource_positiveSchedule
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalPositiveCoupling_physicalNormAndRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_above_AIT_cutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIZ_originalRawPhysicalSource_positiveSchedule

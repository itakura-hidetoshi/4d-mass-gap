import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedSourceTopOrthogonalQuantitativeV5_PZ37AJB
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceOrthogonalDecomposition
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJC — canonical full-top projection of the original normalized ZW source image

Use the SAME original finite-volume SU(2) Wilson one-slab physical Hilbert
space, genuine signed ZW Gauss-law physical source, existing positive physical
operator norm normalization, and the full normalized-transfer top eigenspace.

AJB gives a noncanonical existential top/orthogonal decomposition. This new
append-only module names the ACTUAL canonical Hilbert orthogonal projections
of the unchanged source image, and proves their exact reconstruction,
Pythagorean identity, and the original AJA strictly positive
Haar-L² certificate bounded by the sum of their squared norms.

Subtracting the actual top-projection norm gives a rigorous conditional
lower bound for the canonical orthogonal projection. Whether the actual top
overlap falls below that certificate is a separate UNPROVEN input.
No top-orthogonality of the source, volume-uniform excitation floor, transfer
coercivity, Hamiltonian gap, continuum Yang--Mills mass gap or substitute
physical source is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysC" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgC" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muC" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fC" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "NC" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "TopC" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "uC" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mC" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

/-! Local proof-only instances for the EXISTING physical Hilbert carrier
and its EXISTING closed full top eigenspace. -/
local instance p4Q2PZ37AJC_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJC_topHasProjection
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      K 2 (by norm_num) beta hbeta).HasOrthogonalProjection := by
  let F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    K 2 (by norm_num) beta hbeta
  have hFclosed : IsClosed
      (F : Set
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2)) := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
        K 2 (by norm_num) beta hbeta
  letI : CompleteSpace F := hFclosed.completeSpace_coe
  change F.HasOrthogonalProjection
  infer_instance

/-- The actual orthogonal projection of the true normalized physical ZW
source IMAGE onto the EXISTING full top eigenspace. -/
noncomputable def p4Q2PZ37AJC_originalNormalizedSourceTopComponent
    (beta : ℝ) (hbeta : 0 < beta) : PhysC :=
  (TopC beta hbeta.le).starProjection (NC beta hbeta.le fC)

/-- The actual canonical projection of the SAME source image onto the
orthogonal complement of the entire full top eigenspace. -/
noncomputable def p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent
    (beta : ℝ) (hbeta : 0 < beta) : PhysC :=
  (TopC beta hbeta.le)ᗮ.starProjection (NC beta hbeta.le fC)

/-- Canonical top projection lies in the EXISTING full top eigenspace. -/
theorem p4Q2PZ37AJC_originalNormalizedSourceTopComponent_mem
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AJC_originalNormalizedSourceTopComponent H beta hbeta ∈
      TopC beta hbeta.le := by
  unfold p4Q2PZ37AJC_originalNormalizedSourceTopComponent
  exact Submodule.starProjection_apply_mem _ _

/-- Canonical orthogonal projection lies in the orthogonal complement
of the full top eigenspace, not merely that of a selected eigenvector. -/
theorem p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent_mem
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta ∈
      (TopC beta hbeta.le)ᗮ := by
  unfold p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent
  exact Submodule.starProjection_apply_mem _ _

/-- Exact canonical reconstruction of the original normalized physical
source image inside its unchanged H-indexed physical Hilbert space. -/
theorem p4Q2PZ37AJC_originalNormalizedSource_canonicalProjection_sum
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AJC_originalNormalizedSourceTopComponent H beta hbeta +
      p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta =
    NC beta hbeta.le fC := by
  change (TopC beta hbeta.le).starProjection (NC beta hbeta.le fC) +
    (TopC beta hbeta.le)ᗮ.starProjection (NC beta hbeta.le fC) =
    NC beta hbeta.le fC
  exact (TopC beta hbeta.le).starProjection_add_starProjection_orthogonal
    (NC beta hbeta.le fC)

/-- Canonical Pythagoras equality for the actual existing physical image. -/
theorem p4Q2PZ37AJC_originalNormalizedSource_canonicalProjection_norm_sq
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖NC beta hbeta.le fC‖ ^ 2 =
      ‖p4Q2PZ37AJC_originalNormalizedSourceTopComponent H beta hbeta‖ ^ 2 +
      ‖p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta‖ ^ 2 := by
  change ‖NC beta hbeta.le fC‖ ^ 2 =
    ‖(TopC beta hbeta.le).starProjection (NC beta hbeta.le fC)‖ ^ 2 +
    ‖(TopC beta hbeta.le)ᗮ.starProjection (NC beta hbeta.le fC)‖ ^ 2
  exact (TopC beta hbeta.le).norm_sq_eq_add_norm_sq_starProjection
    (NC beta hbeta.le fC)

/-- Genuine AJA quantitative Haar-L² floor bounds the sum of the
canonical top and orthogonal image components, at every finite H,beta>0. -/
theorem p4Q2PZ37AJC_originalHaarCertificate_le_canonicalProjection_norm_sq
    (beta : ℝ) (hbeta : 0 < beta) :
    (mC beta hbeta.le) ^ 2 *
      Measure.real muC
        {B : CfgC | uC beta hbeta.le B < -(mC beta hbeta.le)}
    ≤ ‖p4Q2PZ37AJC_originalNormalizedSourceTopComponent H beta hbeta‖ ^ 2 +
      ‖p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta‖ ^ 2 :=
  (p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
    H beta hbeta).trans_eq
      (p4Q2PZ37AJC_originalNormalizedSource_canonicalProjection_norm_sq H beta hbeta)

/-- Quantitative conditional orthogonal-component floor, measuring precisely
what an UNPROVEN genuine top-overlap estimate would still have to control. -/
theorem p4Q2PZ37AJC_originalOrthogonalNorm_sq_ge_certificate_sub_top
    (beta : ℝ) (hbeta : 0 < beta) :
    (mC beta hbeta.le) ^ 2 *
      Measure.real muC
        {B : CfgC | uC beta hbeta.le B < -(mC beta hbeta.le)} -
      ‖p4Q2PZ37AJC_originalNormalizedSourceTopComponent H beta hbeta‖ ^ 2
    ≤ ‖p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta‖ ^ 2 := by
  have hBound :=
    p4Q2PZ37AJC_originalHaarCertificate_le_canonicalProjection_norm_sq
      H beta hbeta
  linarith

/-- Conditional, not unconditional: an independently established sufficiently
small actual full-top projection forces nonzero canonical orthogonal output. -/
theorem p4Q2PZ37AJC_originalOrthogonalComponent_ne_zero_of_top_small
    (beta : ℝ) (hbeta : 0 < beta)
    (hTopSmall :
      ‖p4Q2PZ37AJC_originalNormalizedSourceTopComponent H beta hbeta‖ ^ 2 <
      (mC beta hbeta.le) ^ 2 *
        Measure.real muC
          {B : CfgC | uC beta hbeta.le B < -(mC beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta ≠ 0 := by
  have hBound :=
    p4Q2PZ37AJC_originalHaarCertificate_le_canonicalProjection_norm_sq
      H beta hbeta
  intro hz
  have hzero :
      ‖p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta‖ ^ 2 = 0 := by
    simp [hz]
  rw [hzero, add_zero] at hBound
  exact (not_lt_of_ge hBound) hTopSmall

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Actual dependency inspection for every new named theorem and projection. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJC_originalNormalizedSourceTopComponent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJC_originalNormalizedSourceTopComponent_mem
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent_mem
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJC_originalNormalizedSource_canonicalProjection_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJC_originalNormalizedSource_canonicalProjection_norm_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJC_originalHaarCertificate_le_canonicalProjection_norm_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJC_originalOrthogonalNorm_sq_ge_certificate_sub_top
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJC_originalOrthogonalComponent_ne_zero_of_top_small

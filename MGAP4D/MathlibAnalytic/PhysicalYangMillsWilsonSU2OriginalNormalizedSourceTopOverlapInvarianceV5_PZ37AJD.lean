import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedSourceCanonicalTopProjectionV5_PZ37AJC
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJD — invariance of the ORIGINAL source's full-top overlap

The ORIGINAL complete SU(2) Wilson one-slab Gauss-law physical transfer,
its unchanged signed centered ZW source, both spatial halfweights, genuine
product-Haar measure and true physical norm normalization are preserved.
No new physical transfer, normalized source, measure, or top eigenspace is
introduced. The only derived quantity is the canonical orthogonal
projection of the ORIGINAL UNTRANSFERRED ZW source onto the already existing
full fixed-point/top eigenspace at the same finite H and positive beta.

The normalized transfer is symmetric and fixes every vector in its full
top eigenspace. Consequently, inner products of the normalized SOURCE IMAGE
with every actual full-top vector equal those of the UNTRANSFERRED source.
By uniqueness of Hilbert orthogonal projection, the two full-top projections
coincide exactly. This reduces AJC's missing top-overlap input to the genuine
original-source top projection; its smallness is NOT thereby established.

The AJA physical Haar-L2 certificate remains positive, but all inequalities
involving a positive orthogonal component remain CONDITIONAL on bounding
the actual source's top projection. No excitation-sector norm lower floor,
uniform-in-H coercivity, Hamiltonian gap or continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- For a real symmetric operator, any subspace on which it acts as identity
has the SAME canonical orthogonal projection before and after applying the
operator. This statement requires the ACTUAL orthogonal projection and
actual fixed-vector condition; it is not a claim that every subspace is fixed. -/
theorem realHilbert_symmetric_fixedSubspace_starProjection_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hFix : ∀ v : E, v ∈ F → S v = v)
    (x : E) :
    F.starProjection (S x) = F.starProjection x := by
  apply F.eq_starProjection_of_mem_of_inner_eq_zero
    (F.starProjection_apply_mem x)
  intro w hw
  have hIw : inner ℝ (S x) w = inner ℝ x w := by
    have h := hSymm x w
    change inner ℝ (S x) w = inner ℝ x (S w) at h
    rw [hFix w hw] at h
    exact h
  calc
    inner ℝ (S x - F.starProjection x) w =
        inner ℝ (S x) w - inner ℝ (F.starProjection x) w :=
          inner_sub_left _ _ _
    _ = inner ℝ x w - inner ℝ (F.starProjection x) w := by rw [hIw]
    _ = inner ℝ (x - F.starProjection x) w :=
      (inner_sub_left _ _ _).symm
    _ = 0 := F.starProjection_inner_eq_zero x w hw

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysD" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgD" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muD" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fD" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "ND" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "TopD" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "uD" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mD" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

/-! Proof-only typeclass instances derived from the EXISTING complete
physical Hilbert carrier and the EXISTING closed full top eigenspace. -/
local instance p4Q2PZ37AJD_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJD_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- The ORIGINAL untouched ZW source's canonical full-top projection.
Its top subspace depends on the ACTUAL H and beta, not a substituted vacuum
line or a common volume Hilbert space. -/
noncomputable def p4Q2PZ37AJD_originalSourceTopComponent
    (beta : ℝ) (hbeta : 0 < beta) : PhysD :=
  (TopD beta hbeta.le).starProjection fD

/-- The original normalized source image has exactly the same genuine
physical inner product with EVERY vector in the existing full top
eigenspace as the UNTRANSFERRED original ZW source. -/
theorem p4Q2PZ37AJD_originalNormalizedSource_topInner_eq_source
    (beta : ℝ) (hbeta : 0 < beta) (v : PhysD)
    (hv : v ∈ TopD beta hbeta.le) :
    inner ℝ (ND beta hbeta.le fD) v = inner ℝ fD v := by
  have hSymm :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hvfix : ND beta hbeta.le v = v :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
      H 2 (by norm_num) beta hbeta.le v).mp hv
  have h := hSymm fD v
  change inner ℝ (ND beta hbeta.le fD) v =
    inner ℝ fD (ND beta hbeta.le v) at h
  rw [hvfix] at h
  exact h

/-- Unlike mere nonzero source L2 norm, this precisely IDENTIFIES the
top-mode overlap of the original normalized source image with the true
source's top projection. No smallness or vanishing is inferred. -/
theorem p4Q2PZ37AJD_normalizedSourceTop_eq_originalSourceTop
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AJC_originalNormalizedSourceTopComponent H beta hbeta =
      p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta := by
  change (TopD beta hbeta.le).starProjection (ND beta hbeta.le fD) =
    (TopD beta hbeta.le).starProjection fD
  exact realHilbert_symmetric_fixedSubspace_starProjection_eq
    (TopD beta hbeta.le) (ND beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le)
    (by
      intro v hv
      exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
        H 2 (by norm_num) beta hbeta.le v).mp hv)
    fD

/-- The actual existing source image's Hilbert Pythagoras decomposition
retains its orthogonal output but uses the true ORIGINAL source's top
projection instead of the transfer output's already-equal top projection. -/
theorem p4Q2PZ37AJD_sourceImage_norm_sq_eq_sourceTop_add_orthogonal
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖ND beta hbeta.le fD‖ ^ 2 =
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
      ‖p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta‖ ^ 2 := by
  have h :=
    p4Q2PZ37AJC_originalNormalizedSource_canonicalProjection_norm_sq H beta hbeta
  rw [p4Q2PZ37AJD_normalizedSourceTop_eq_originalSourceTop H beta hbeta] at h
  exact h

/-- Quantitative genuine Haar-L2 certificate now subtracts the ORIGINAL
untransferred physical source's genuine full-top squared overlap. This
is a valid H,beta-dependent inequality but not an H-uniform floor. -/
theorem p4Q2PZ37AJD_originalOrthogonal_norm_sq_ge_certificate_sub_sourceTop
    (beta : ℝ) (hbeta : 0 < beta) :
    (mD beta hbeta.le) ^ 2 *
      Measure.real muD
        {B : CfgD | uD beta hbeta.le B < -(mD beta hbeta.le)} -
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2
    ≤ ‖p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta‖ ^ 2 := by
  have h :=
    p4Q2PZ37AJC_originalOrthogonalNorm_sq_ge_certificate_sub_top H beta hbeta
  rw [p4Q2PZ37AJD_normalizedSourceTop_eq_originalSourceTop H beta hbeta] at h
  exact h

/-- The REAL obstruction is now sourced before the physical transfer:
if the original ZW source's actual projection onto the unchanged full
top eigenspace is smaller than the original AJA Haar-L2 certificate,
the normalized source image has a nonzero orthogonal component.
The inequality in the antecedent remains unproved. -/
theorem p4Q2PZ37AJD_orthogonal_ne_zero_of_originalSourceTop_small
    (beta : ℝ) (hbeta : 0 < beta)
    (hSmall :
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
        (mD beta hbeta.le) ^ 2 *
          Measure.real muD
            {B : CfgD | uD beta hbeta.le B < -(mD beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta ≠ 0 := by
  apply p4Q2PZ37AJC_originalOrthogonalComponent_ne_zero_of_top_small H beta hbeta
  rw [p4Q2PZ37AJD_normalizedSourceTop_eq_originalSourceTop H beta hbeta]
  exact hSmall

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Independent actual axiom output for each newly declared result. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_symmetric_fixedSubspace_starProjection_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJD_originalSourceTopComponent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJD_originalNormalizedSource_topInner_eq_source
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJD_normalizedSourceTop_eq_originalSourceTop
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJD_sourceImage_norm_sq_eq_sourceTop_add_orthogonal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJD_originalOrthogonal_norm_sq_ge_certificate_sub_sourceTop
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJD_orthogonal_ne_zero_of_originalSourceTop_small

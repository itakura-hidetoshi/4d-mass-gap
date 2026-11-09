import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedSourceTopOverlapInvarianceV5_PZ37AJD
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJE — genuine original ZW full-top overlap dual bounds

Use the unchanged finite-H, positive-beta REAL Gauss-law physical Hilbert
space, original signed centered ZW source, original normalized full Wilson
transfer and its full top eigenspace. AJD proves the top projection before
and after transfer is exactly equal, but does NOT bound its size.

This leaf identifies the exact full-top source overlap bound with the
operator norm of the existing canonical top projection. It also provides
an explicit necessary test from the already existing unit top eigenvector:
one single witness can obstruct the hoped-for small-top inequality, but
one single vector is NOT asserted to span the complete top eigenspace.

The resulting certificate criterion remains existential/conditional:
the genuine numerical bound for all top directions is NOT constructed.
No new assumption, substitute source, vacuum-line identification, gap,
uniform-in-H floor, or continuum limit is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The original physical pairing with any vector IN a closed subspace
equals its pairing with the actual orthogonal projection of the source. -/
theorem realHilbert_starProjection_inner_eq_of_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (x v : E) (hv : v ∈ F) :
    inner ℝ x v = inner ℝ (F.starProjection x) v := by
  have hzero := F.starProjection_inner_eq_zero x v hv
  rw [inner_sub_left] at hzero
  linarith

/-- The genuine projected self-overlap is exactly the norm squared of
the actual full-subspace projection, not an arbitrary selected component. -/
theorem realHilbert_starProjection_source_inner_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (x : E) :
    inner ℝ x (F.starProjection x) = ‖F.starProjection x‖ ^ 2 := by
  have h := realHilbert_starProjection_inner_eq_of_mem
    F x (F.starProjection x) (F.starProjection_apply_mem x)
  simpa only [real_inner_self_eq_norm_sq] using h

/-- A true orthogonal projection is contractive in the original Hilbert
norm; this does not imply the strict AJA certificate comparison. -/
theorem realHilbert_starProjection_norm_le_source_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (x : E) :
    ‖F.starProjection x‖ ≤ ‖x‖ :=
  F.norm_starProjection_apply_le x

/-- All genuine full-top overlap functionals are controlled by the
canonical top projection, without assuming top eigenspace dimension one. -/
theorem realHilbert_starProjection_inner_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (x v : E) (hv : v ∈ F) :
    |inner ℝ x v| ≤ ‖F.starProjection x‖ * ‖v‖ := by
  rw [realHilbert_starProjection_inner_eq_of_mem F x v hv]
  exact abs_real_inner_le_norm (F.starProjection x) v

/-- Exact DUAL characterization: a quantitative upper bound on the
genuine canonical top projection is equivalent to controlling the
original source pairing against EVERY actual top vector. -/
theorem realHilbert_starProjection_norm_le_iff_uniform_inner_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (x : E) (b : ℝ) (hb : 0 ≤ b) :
    ‖F.starProjection x‖ ≤ b ↔
      ∀ v : E, v ∈ F → |inner ℝ x v| ≤ b * ‖v‖ := by
  constructor
  · intro hnorm v hv
    calc
      |inner ℝ x v| ≤ ‖F.starProjection x‖ * ‖v‖ :=
        realHilbert_starProjection_inner_bound F x v hv
      _ ≤ b * ‖v‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
  · intro hbound
    have h := hbound (F.starProjection x) (F.starProjection_apply_mem x)
    rw [realHilbert_starProjection_source_inner_self F x,
      abs_of_nonneg (sq_nonneg _)] at h
    by_cases hz : F.starProjection x = 0
    · simpa [hz] using hb
    · have hp : 0 < ‖F.starProjection x‖ := norm_pos_iff.mpr hz
      have hmul :
          ‖F.starProjection x‖ * ‖F.starProjection x‖ ≤
            b * ‖F.starProjection x‖ := by
        simpa only [pow_two] using h
      exact (mul_le_mul_right hp).mp hmul

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysE" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muE" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fE" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "TopE" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OmegaE" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "uE" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mE" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJE_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJE_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- The exact dual upper bound for the ORIGINAL ZW source against every
genuine full-top vector (not merely one chosen vacuum). -/
theorem p4Q2PZ37AJE_originalSource_fullTop_inner_bound
    (beta : ℝ) (hbeta : 0 < beta)
    (v : PhysE) (hv : v ∈ TopE beta hbeta.le) :
    |inner ℝ fE v| ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ * ‖v‖ := by
  change |inner ℝ fE v| ≤
    ‖(TopE beta hbeta.le).starProjection fE‖ * ‖v‖
  exact realHilbert_starProjection_inner_bound
    (TopE beta hbeta.le) fE v hv

/-- The physical original-source top projection is bounded by the exact
physical norm of that SAME original source, at each H,beta>0. -/
theorem p4Q2PZ37AJE_originalSourceTop_norm_le_originalSource_norm
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ≤ ‖fE‖ := by
  change ‖(TopE beta hbeta.le).starProjection fE‖ ≤ ‖fE‖
  exact realHilbert_starProjection_norm_le_source_norm (TopE beta hbeta.le) fE

/-- The already available selected unit top eigenvector gives an ACTUAL
necessary overlap test, but does not exhaust the entire top eigenspace. -/
theorem p4Q2PZ37AJE_selectedUnitTop_sourceOverlap_le_fullTop_norm
    (beta : ℝ) (hbeta : 0 < beta) :
    |inner ℝ fE (OmegaE beta hbeta.le)| ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ := by
  have hmem :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H 2 (by norm_num) beta hbeta.le
  have hunit :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H 2 (by norm_num) beta hbeta.le
  have hbound :=
    p4Q2PZ37AJE_originalSource_fullTop_inner_bound
      H beta hbeta (OmegaE beta hbeta.le) hmem
  simpa [hunit] using hbound

/-- A quantitative full-top source smallness certificate is equivalent
to the existence of a genuinely uniform bound on ALL original-source
full-top pairings that is strictly below the AJA Haar-L2 threshold.
The required witness b is NOT produced here. -/
theorem p4Q2PZ37AJE_originalSourceTop_small_iff_uniform_overlap_budget
    (beta : ℝ) (hbeta : 0 < beta) :
    (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mE beta hbeta.le) ^ 2 *
        Measure.real muE
          {B : CfgE | uE beta hbeta.le B < -(mE beta hbeta.le)}) ↔
    ∃ b : ℝ, 0 ≤ b ∧
      b ^ 2 <
        (mE beta hbeta.le) ^ 2 *
          Measure.real muE
            {B : CfgE | uE beta hbeta.le B < -(mE beta hbeta.le)} ∧
      ∀ v : PhysE, v ∈ TopE beta hbeta.le →
        |inner ℝ fE v| ≤ b * ‖v‖ := by
  constructor
  · intro hsmall
    refine ⟨‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖,
      norm_nonneg _, hsmall, ?_⟩
    intro v hv
    exact p4Q2PZ37AJE_originalSource_fullTop_inner_bound H beta hbeta v hv
  · rintro ⟨b, hb, hbsq, hbound⟩
    have hproj :
        ‖(TopE beta hbeta.le).starProjection fE‖ ≤ b :=
      (realHilbert_starProjection_norm_le_iff_uniform_inner_bound
        (TopE beta hbeta.le) fE b hb).2 hbound
    have hprojSq :
        ‖(TopE beta hbeta.le).starProjection fE‖ ^ 2 ≤ b ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hproj)
        (add_nonneg hb (norm_nonneg ((TopE beta hbeta.le).starProjection fE)))]
    change ‖(TopE beta hbeta.le).starProjection fE‖ ^ 2 <
      (mE beta hbeta.le) ^ 2 *
        Measure.real muE
          {B : CfgE | uE beta hbeta.le B < -(mE beta hbeta.le)}
    exact lt_of_le_of_lt hprojSq hbsq

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Actual dependencies of every newly named declaration. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_starProjection_inner_eq_of_mem
#print axioms MGAP4D.MathlibAnalytic.realHilbert_starProjection_source_inner_self
#print axioms MGAP4D.MathlibAnalytic.realHilbert_starProjection_norm_le_source_norm
#print axioms MGAP4D.MathlibAnalytic.realHilbert_starProjection_inner_bound
#print axioms MGAP4D.MathlibAnalytic.realHilbert_starProjection_norm_le_iff_uniform_inner_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJE_originalSource_fullTop_inner_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJE_originalSourceTop_norm_le_originalSource_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJE_selectedUnitTop_sourceOverlap_le_fullTop_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJE_originalSourceTop_small_iff_uniform_overlap_budget

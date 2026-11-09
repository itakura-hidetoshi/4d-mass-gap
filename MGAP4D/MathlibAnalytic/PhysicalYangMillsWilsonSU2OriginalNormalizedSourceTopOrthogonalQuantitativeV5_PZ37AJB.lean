import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedSourceQuantitativeHaarL2V5_PZ37AJA
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceOrthogonalDecomposition
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJB — original normalized ZW source top/orthogonal quantitative split

This new leaf DOES NOT define a replacement physical operator, source, measure,
or top eigenspace. It uses the existing genuine full SU(2) Wilson one-slab
Gauss-law physical Hilbert carrier, the already-defined normalized operator,
its original signed ZW physical source and the existing FULL top eigenspace
and orthogonal complement. The previous top/orthogonal direct-sum theorem
is reused as an authentic dependent-Hilbert-space decomposition.

AJA supplies the finite-H, all beta>0 quantitative ORIGINAL
negative-margin/Haar-mass physical L2 certificate. The result here is an
exact real Hilbert Pythagorean decomposition for that source, with
certificate <= the SUM of top and orthogonal squared components. This
does NOT imply either component separately has a positive lower bound.

A conditional obstruction exposes the missing input: only if an actual top
component squared norm is strictly smaller than the certified source-image
floor does the corresponding orthogonal component have to be nonzero.
No top orthogonality, positive volume-uniform floor, excitation gap,
Hamiltonian gap or continuum mass gap is postulated or inferred.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Real-Hilbert orthogonality gives a squared-norm equality, not a
spectral separation or an operator gap. -/
theorem realHilbert_topOrthogonal_add_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) (u v : E)
    (hu : u ∈ F) (hv : v ∈ Fᗮ) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
  norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    u v (F.inner_right_of_mem_orthogonal hu hv)

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysB" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgB" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muB" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fB" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "NB" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "TopB" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OrthB" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal H 2 (by norm_num)
local notation "uB" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mB" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

/-- The exact normalized source image admits top and full-top-orthogonal
components in its SAME original physical Hilbert space, every positive
coupling and finite volume. No component nonvanishing is inferred. -/
theorem p4Q2PZ37AJB_originalNormalizedSource_exists_top_orthogonal
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ u v : PhysB,
      u ∈ TopB beta hbeta.le ∧
      v ∈ OrthB beta hbeta.le ∧
      u + v = NB beta hbeta.le fB := by
  obtain ⟨u, hu, v, hv, hsum⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_exists_top_add_orthogonal
      H 2 (by norm_num) beta hbeta.le (NB beta hbeta.le fB)
  exact ⟨u, v, hu, hv, hsum⟩

/-- The true original quantitative Haar-L2 floor descends to the SUM
of squared top and orthogonal components. Their separate lower bounds
do NOT follow without an actual top-overlap estimate. -/
theorem p4Q2PZ37AJB_originalNormalizedSource_quantitative_top_orthogonal_split
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ u v : PhysB,
      u ∈ TopB beta hbeta.le ∧
      v ∈ OrthB beta hbeta.le ∧
      u + v = NB beta hbeta.le fB ∧
      ‖NB beta hbeta.le fB‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 ∧
      0 < (mB beta hbeta.le) ^ 2 *
        Measure.real muB
          {B : CfgB | uB beta hbeta.le B < -(mB beta hbeta.le)} ∧
      (mB beta hbeta.le) ^ 2 *
        Measure.real muB
          {B : CfgB | uB beta hbeta.le B < -(mB beta hbeta.le)}
        ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  obtain ⟨u, v, hu, hv, hsum⟩ :=
    p4Q2PZ37AJB_originalNormalizedSource_exists_top_orthogonal H beta hbeta
  have hPyth : ‖NB beta hbeta.le fB‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [← hsum]
    exact realHilbert_topOrthogonal_add_norm_sq (TopB beta hbeta.le)
      u v hu (by
        simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal]
          using hv)
  have hCert :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hBound :=
    p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure H beta hbeta
  refine ⟨u, v, hu, hv, hsum, hPyth, hCert, ?_⟩
  exact hBound.trans_eq hPyth

/-- Quantified conditional obstruction: an ACTUAL top component whose squared
norm falls below the true original Haar-L2 floor forces a nonzero orthogonal
component. The missing top-overlap upper estimate is NOT assumed globally. -/
theorem p4Q2PZ37AJB_originalNormalizedSource_orthogonal_ne_zero_of_top_small
    (beta : ℝ) (hbeta : 0 < beta)
    (u v : PhysB)
    (hu : u ∈ TopB beta hbeta.le)
    (hv : v ∈ OrthB beta hbeta.le)
    (hsum : u + v = NB beta hbeta.le fB)
    (hTopSmall :
      ‖u‖ ^ 2 <
        (mB beta hbeta.le) ^ 2 *
          Measure.real muB
            {B : CfgB | uB beta hbeta.le B < -(mB beta hbeta.le)}) :
    v ≠ 0 := by
  have hPyth : ‖NB beta hbeta.le fB‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [← hsum]
    exact realHilbert_topOrthogonal_add_norm_sq (TopB beta hbeta.le)
      u v hu (by
        simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal]
          using hv)
  have hBound :
      (mB beta hbeta.le) ^ 2 *
        Measure.real muB
          {B : CfgB | uB beta hbeta.le B < -(mB beta hbeta.le)}
      ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    exact (p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
      H beta hbeta).trans_eq hPyth
  intro hz
  subst v
  simp at hBound
  exact (not_lt_of_ge hBound) hTopSmall

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Every new declaration has an independent actual axiom output. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_topOrthogonal_add_norm_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJB_originalNormalizedSource_exists_top_orthogonal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJB_originalNormalizedSource_quantitative_top_orthogonal_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJB_originalNormalizedSource_orthogonal_ne_zero_of_top_small

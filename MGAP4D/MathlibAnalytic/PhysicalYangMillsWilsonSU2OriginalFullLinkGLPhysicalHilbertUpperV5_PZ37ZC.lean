import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullLinkFineZeroFrameV5_PZ37ZB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSharpExpectationGapConditionalRMSV5_GJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalExpectationGapSquareContrastVarianceV5_GL
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalRMSPhysicalBudgetV5_FI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZC — all-physical-source upper bound for TRUE all-link GL posterior mass

PZ37ZB showed an exact fine-zero three-mode coefficient obstruction for
the unchanged original SU(2) Wilson full-link GL posterior Gram.

Here we move directly to the full Gauss-law Hilbert SOURCE (not just the
finite-dimensional Krylov subspace). We use three previously proved
identities and inequalities:
* GL: the exact two-original-interacting-Wilson-posterior expectation
  gap squared divided by the genuine density-row Haar variance,
* GJ: exp(-16 b) times this genuine GL link mass is controlled by
  the ORIGINAL interacting Wilson conditional RMS link mean,
* FI: the SAME Wilson conditional RMS link mean is bounded by
  2 * ||f||^2 for EVERY physical Haar-L2 source f.

After a finite spatial sum, at any finite H, frozen Wilson b>0 and
arbitrary ORIGINAL Gauss-law physical Hilbert input f,

   M_GL(H,b; f, S) ≤ 2 * |S| * ||f||² / exp(-16*b).

This bound is independent of fine coupling, Krylov depth, a source-frame
constant, posterior coefficients or selected boundary contexts. Its
dependence on the TRUE physical link cardinality remains extensive.
In particular, it is an UPPER bound, not an H-uniform coercivity floor.
No independent-Haar posterior substitute, Dobrushin argument, new axiom,
sorry, admit, native_decide, U0 or continuum mass-gap claim is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZC_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Every individual TRUE Wilson GL Haar link mass, including its actual
two interacting posterior density-row variance denominator, is
dominated by the true Wilson pair-Haar conditional RMS mass. -/
theorem p4Q2PZ37ZC_originalGL_link_scaled_le_originalWilsonRMS
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Real.exp (-16 * b) *
      p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
        H b (le_of_lt hb) f e ≤
      p4Q2FH_originalWilsonConditionalRMSLinkMean
        H 2 (by norm_num) b (le_of_lt hb) f e := by
  have hGJ :=
    p4Q2GJ_originalWilsonLinkRMS_ge_sharpSignedGapProjection H b hb f e
  rw [p4Q2GL_originalWilsonSharpSignedGapLinkMean_eq_gapSquareDivVariance
    H b hb f e] at hGJ
  exact hGJ

/-- Exact patch summation, using ALL genuine Wilson links and boundary
contexts: no transfer-compensated two-context GI minor is substituted. -/
theorem p4Q2PZ37ZC_originalGL_patch_scaled_le_originalWilsonRMS
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    Real.exp (-16 * b) *
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb) f S ≤
      p4Q2FH_originalWilsonSpatialRMSMass
        H 2 (by norm_num) b (le_of_lt hb) f S := by
  unfold p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    p4Q2FH_originalWilsonSpatialRMSMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _he
  exact p4Q2PZ37ZC_originalGL_link_scaled_le_originalWilsonRMS H b hb f e

/-- Explicit TRUE Wilson GL full-physical-Hilbert source upper bound.
The two Wilson posterior laws remain genuinely interacting throughout.
The bound is independent of the fine coupling and Krylov depth, but
is extensive in the actual spatial-link cardinality. -/
theorem p4Q2PZ37ZC_originalGL_patch_le_explicit_physicalSourceNorm
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb) f S ≤
      ((S.card : ℝ) * (2 * ‖f‖ ^ 2)) / Real.exp (-16 * b) := by
  have hScaled :=
    p4Q2PZ37ZC_originalGL_patch_scaled_le_originalWilsonRMS
      H b hb f S
  have hRMS :=
    p4Q2FI_originalWilsonConditionalRMSPatch_le_card_twice_input_sq
      H 2 (by norm_num) b (le_of_lt hb) f S
  have hCombined := hScaled.trans hRMS
  apply (le_div_iff₀ (Real.exp_pos (-16 * b))).2
  calc
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb) f S * Real.exp (-16 * b) =
      Real.exp (-16 * b) *
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b (le_of_lt hb) f S := mul_comm _ _
    _ ≤ (S.card : ℝ) * (2 * ‖f‖ ^ 2) := hCombined

/-- The SAME universal source norm inequality applies to the ORIGINAL
GL integral summed over EVERY actual physical spatial link. -/
theorem p4Q2PZ37ZC_originalGL_fullLink_le_explicit_physicalSourceNorm
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb) f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (2 * ‖f‖ ^ 2)) / Real.exp (-16 * b) := by
  simpa only [Finset.card_univ] using
    p4Q2PZ37ZC_originalGL_patch_le_explicit_physicalSourceNorm
      H b hb f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))

end GroundStatePosteriorJoint
end

end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZC_originalGL_link_scaled_le_originalWilsonRMS
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZC_originalGL_patch_scaled_le_originalWilsonRMS
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZC_originalGL_patch_le_explicit_physicalSourceNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZC_originalGL_fullLink_le_explicit_physicalSourceNorm

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIPhysicalReceiverQuantitativeDistanceV5_JT
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonPhysicalSourceGIBridgeV5_JU
import Mathlib.Tactic

/-!
# P4-Q2-JV: quantitative second-context obstruction for the ACTUAL spatial Wilson source

JU constructs an ACTUAL Gauss-law Hilbert vector by applying the genuine
gauge-invariant spatial Wilson action to the genuine constant physical unit,
and subtracting JK's original frozen GI anchor ratio.

The resulting genuine spatial source is nonzero in the original Haar-L2
Hilbert space, but its original two-interacting-Wilson-posterior GI response
at its own physical anchor is EXACTLY ZERO. JT says that such a physical
source's actual link receiver at the SAME anchor stays at a positive
SU(2) sup-norm distance from the literal temporal Wilson contrast D.

At a genuine candidate second physical context, however, JT's explicit
receiver-approximation threshold forces the original GI response nonzero.
JU then turns this into a nonzero ORIGINAL spatial Wilson two-context minor.

Conversely, a vanishing original spatial minor forces the actual centered
spatial-source receiver at the second context to remain outside that
positive sup-norm approximation radius.

All statements retain the original Wilson one-slab transfer, Perron vacuum,
SU(2) Haar as DENSITY REFERENCE, two ORIGINAL interacting posteriors,
and actual physical Gauss-law sources. The existence of a close second
receiver remains OPEN: this is a proved criterion/obstruction, not a
nonzero second-context witness. No rank/frame assumption, new axiom,
sorry/admit, H1-C3 or continuum Yang-Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen

variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "D" => p4Q2JM_temporalWilsonContinuous

/-- The actual anchor-centered spatial Wilson physical Gauss-law Hilbert
source is NONZERO. This uses the genuine physical-to-Haar-L2 equality
of JU and JK's actual SU(2) spatial Wilson nonconstancy witness. -/
theorem p4Q2JV_originalAnchorCenteredSpatialPhysicalSource_ne_zero
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z ≠ 0 := by
  intro hZero
  have hL :
      ((p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z :
        Phys) : Lp ℝ 2 haar) =
          L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z) :=
    p4Q2JU_originalAnchorCenteredWilsonPhysicalSource_coe_eq_toLp
      H b hb e z
  have hPhysZero :
      ((p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z :
        Phys) : Lp ℝ 2 haar) = 0 := by
    rw [hZero]
    rfl
  exact
    (p4Q2JK_anchorCenteredSpatialWilson_HaarLp_ne_zero
      H b hb e z) (hL.symm.trans hPhysZero)

/-- By the DEFINITION of the ORIGINAL anchor slope, the unchanged
physical two-posterior GI functional annihilates the genuine,
nonzero anchor-centered spatial Wilson source AT ITS OWN CONTEXT. -/
theorem p4Q2JV_originalAnchorCenteredSpatialPhysicalGI_anchor_zero
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (hAnchor : p4Q2JH_originalGIResponseCLM H b hb e z
      (L (1 : C(Cfg, ℝ))) ≠ 0) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
      e z = 0 := by
  calc
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
        e z =
      p4Q2JH_originalGIResponseCLM H b hb e z
        (L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z)) :=
      (p4Q2JU_originalCenteredSpatialGI_eq_actualPhysicalGI
        H b hb e e z z).symm
    _ = 0 :=
      p4Q2JK_originalGI_anchor_annihilates_centeredWilson
        H b hb e z hAnchor

/-- Genuine ANCHOR NO-GO in quantitative form: although the actual
spatial Wilson physical source is nonzero, its SAME-context physical
receiver cannot approximate the temporal SU(2) Wilson action within
JT's universal positive weak-coupling tolerance. -/
theorem p4Q2JV_originalAnchorPhysicalReceiver_far_from_temporal
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (e : Link) (z : Cfg × Cfg)
    (hAnchor : p4Q2JH_originalGIResponseCLM H b hb.le e z
      (L (1 : C(Cfg, ℝ))) ≠ 0) :
    p4Q2JT_physicalReceiverApproximationRadius b ≤
      ‖D -
        p4Q2JQ_originalPhysicalSourceLinkReceiver
          H b hb.le
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
            H b hb.le e z)
          e z‖ := by
  exact p4Q2JT_actualPhysicalReceiver_distance_ge_of_GI_zero
    H b hb hwindow z.2 z.1 e
    (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
    (p4Q2JV_originalAnchorCenteredSpatialPhysicalGI_anchor_zero
      H b hb.le e z hAnchor)

/-- QUANTITATIVE ZERO-MINOR OBSTRUCTION at the genuine second context:
if the original spatial Wilson two-context determinant vanishes, then
the ORIGINAL physical receiver of its specific, nonzero centered Wilson
Gauss-law source cannot approximate D closer than epsilon(b). -/
theorem p4Q2JV_originalSpatialMinor_zero_forces_secondReceiver_far
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor : p4Q2JH_originalGIResponseCLM H b hb.le e z
      (L (1 : C(Cfg, ℝ))) ≠ 0)
    (hMinor : p4Q2JI_originalGISpatialActionMinor
      H b hb.le e e' z z' = 0) :
    p4Q2JT_physicalReceiverApproximationRadius b ≤
      ‖D -
        p4Q2JQ_originalPhysicalSourceLinkReceiver
          H b hb.le
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
            H b hb.le e z) e' z'‖ := by
  have hIff :=
    p4Q2JU_originalSpatialMinor_ne_iff_physicalGI_ne
      H b hb.le e e' z z' hAnchor
  have hGI :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
        e' z' = 0 := by
    by_contra hNot
    exact (hIff.mpr hNot) hMinor
  exact p4Q2JT_actualPhysicalReceiver_distance_ge_of_GI_zero
    H b hb hwindow z'.2 z'.1 e'
    (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
    hGI

/-- A single ACTUAL second-context physical receiver of the genuinely
nonzero anchor-centered SPATIAL Wilson source, if strictly within JT's
proved positive sup-norm radius of temporal D, forces a NONZERO ORIGINAL
spatial Wilson two-context GI minor. No existence of such a context is
assumed/proved; it is the exact remaining quantitative witness input. -/
theorem p4Q2JV_originalSpatialMinor_ne_of_close_secondReceiver
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor : p4Q2JH_originalGIResponseCLM H b hb.le e z
      (L (1 : C(Cfg, ℝ))) ≠ 0)
    (hClose :
      ‖D -
        p4Q2JQ_originalPhysicalSourceLinkReceiver
          H b hb.le
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
            H b hb.le e z) e' z'‖ <
          p4Q2JT_physicalReceiverApproximationRadius b) :
    p4Q2JI_originalGISpatialActionMinor
      H b hb.le e e' z z' ≠ 0 := by
  have hGI :=
    p4Q2JT_actualPhysicalGI_nonzero_of_receiver_close
      H b hb hwindow z'.2 z'.1 e'
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
        H b hb.le e z) hClose
  exact (p4Q2JU_originalSpatialMinor_ne_iff_physicalGI_ne
    H b hb.le e e' z z' hAnchor).2 hGI

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JV_originalAnchorCenteredSpatialPhysicalSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JV_originalAnchorCenteredSpatialPhysicalGI_anchor_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JV_originalAnchorPhysicalReceiver_far_from_temporal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JV_originalSpatialMinor_zero_forces_secondReceiver_far
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JV_originalSpatialMinor_ne_of_close_secondReceiver

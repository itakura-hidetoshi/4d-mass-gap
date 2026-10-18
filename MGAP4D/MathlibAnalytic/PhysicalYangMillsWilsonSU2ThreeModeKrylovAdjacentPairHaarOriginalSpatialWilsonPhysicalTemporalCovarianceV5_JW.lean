import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonAnchorReceiverDistanceV5_JV
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGICenteredReceiverTemporalCovarianceV5_JR
import Mathlib.Tactic

/-!
# P4-Q2-JW — actual centered spatial Wilson physical source covariance gate

JU/JV give the authentic nonzero Gauss-law anchored spatial Wilson source,
a zero original GI response at its own nonzero anchor, and an exact bridge
from original spatial Wilson two-context minors to true physical GI gaps.

JR provides the true weak-frozen-coupling error bound for the Haar-centered
physical Wilson link receiver, preserving the original Perron vacuum and
both interacting Wilson conditional posteriors.

Here we prove a source-specific quantitative covariance upper obstruction:
if the ORIGINAL physical GI expectation difference vanishes, then
  |int Fc(g) D(g) dHaar(g)| <= 272 exp(8) * b * ||Fc||_sup
for 0 < b <= 1/4. Specialize this result to
(1) the actual nonzero anchored spatial Wilson source at its OWN anchor;
(2) any genuine SECOND context when the original spatial GI minor vanishes.

Conversely a second physical link/context where the actual CENTERED
receiver's temporal Wilson covariance strictly dominates this explicit
threshold forces the original static SPATIAL Wilson two-context minor
nonzero. No existence of such a context is assumed or asserted.

This is an analytic bridge, not the missing genuine second-context
witness. No synthetic source, hypothetical rank, independent-Haar
conditional posterior, new axiom/sorry/admit, H1-C3 or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen

variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast
local notation "C" => (272 * Real.exp 8 : ℝ)

/-- ORIGINAL physical GI nullity forces the centered original Wilson
source receiver to have only order-b Haar covariance with literal D.
This does NOT require every other physical source to be GI-invisible. -/
theorem p4Q2JW_originalPhysicalGI_zero_implies_centeredCovariance_le
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ (1 / 4 : ℝ))
    (f : Phys) (e : Link) (z : Cfg × Cfg)
    (hGI : p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le f e z = 0) :
    |∫ g : Gauge,
      p4Q2JR_originalPhysicalReceiverCentered H b hb.le f e z g *
        D g ∂nu| ≤
      ‖p4Q2JR_originalPhysicalReceiverCentered H b hb.le f e z‖ *
        (C * b) := by
  let Fc := p4Q2JR_originalPhysicalReceiverCentered H b hb.le f e z
  let t : ℝ := ∫ g : Gauge, Fc g * D g ∂nu
  have hErr :=
    p4Q2JR_originalPhysicalGI_centeredTemporalCovariance_quadratic
      H b hb.le hsmall f e z
  rw [hGI] at hErr
  have hScaled : b * |t| ≤ ‖Fc‖ * (C * b ^ 2) := by
    simpa only [mul_zero, zero_sub, norm_neg, norm_mul,
      Real.norm_eq_abs, abs_of_pos hb] using hErr
  have hMult : b * |t| ≤ b * (‖Fc‖ * (C * b)) := by
    nlinarith [hScaled]
  have hCov : |t| ≤ ‖Fc‖ * (C * b) :=
    le_of_mul_le_mul_left hMult hb
  exact hCov

/-- At an actual NONZERO original GI constant-unit anchor, the
genuine anchored spatial Wilson physical source's OWN-centered receiver
cannot have covariance with D exceeding the error-order threshold. -/
theorem p4Q2JW_originalAnchorSpatialSource_covariance_le
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ (1 / 4 : ℝ))
    (e : Link) (z : Cfg × Cfg)
    (hAnchor :
      p4Q2JH_originalGIResponseCLM H b hb.le e z
        (L (1 : C(Cfg, ℝ))) ≠ 0) :
    |∫ g : Gauge,
      p4Q2JR_originalPhysicalReceiverCentered H b hb.le
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
        e z g * D g ∂nu| ≤
      ‖p4Q2JR_originalPhysicalReceiverCentered H b hb.le
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
        e z‖ * (C * b) := by
  exact p4Q2JW_originalPhysicalGI_zero_implies_centeredCovariance_le
    H b hb hsmall
    (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
    e z
    (p4Q2JV_originalAnchorCenteredSpatialPhysicalGI_anchor_zero
      H b hb.le e z hAnchor)

/-- ZERO ORIGINAL SPATIAL Wilson two-context GI minor forces the
specified genuine anchored physical spatial source's SECOND receiver
covariance with temporal D to obey the exact JR order-b obstruction. -/
theorem p4Q2JW_originalSpatialMinor_zero_implies_secondCovariance_le
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ (1 / 4 : ℝ))
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor :
      p4Q2JH_originalGIResponseCLM H b hb.le e z
        (L (1 : C(Cfg, ℝ))) ≠ 0)
    (hMinor :
      p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z' = 0) :
    |∫ g : Gauge,
      p4Q2JR_originalPhysicalReceiverCentered H b hb.le
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
        e' z' g * D g ∂nu| ≤
      ‖p4Q2JR_originalPhysicalReceiverCentered H b hb.le
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
        e' z'‖ * (C * b) := by
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
  exact p4Q2JW_originalPhysicalGI_zero_implies_centeredCovariance_le
    H b hb hsmall
    (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
    e' z' hGI

/-- ACTUAL spatial Wilson GI second-context witness criterion, now
expressed as the centered temporal covariance of one PARTICULAR
genuine nonzero gauge-invariant spatial Wilson physical Hilbert source.
The covariance dominance is still an OPEN physical Wilson input. -/
theorem p4Q2JW_originalSpatialMinor_ne_of_secondCovariance_dominates
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ (1 / 4 : ℝ))
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor :
      p4Q2JH_originalGIResponseCLM H b hb.le e z
        (L (1 : C(Cfg, ℝ))) ≠ 0)
    (hCorr :
      ‖p4Q2JR_originalPhysicalReceiverCentered H b hb.le
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
        e' z'‖ * (C * b) <
        |∫ g : Gauge,
          p4Q2JR_originalPhysicalReceiverCentered H b hb.le
            (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
              H b hb.le e z) e' z' g *
            D g ∂nu|) :
    p4Q2JI_originalGISpatialActionMinor
      H b hb.le e e' z z' ≠ 0 := by
  have hPhysicalGI :=
    p4Q2JR_originalPhysicalGI_nonzero_of_centeredTemporalCorrelation
      H b hb hsmall
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
      e' z' hCorr
  exact (p4Q2JU_originalSpatialMinor_ne_iff_physicalGI_ne
    H b hb.le e e' z z' hAnchor).2 hPhysicalGI

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JW_originalPhysicalGI_zero_implies_centeredCovariance_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JW_originalAnchorSpatialSource_covariance_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JW_originalSpatialMinor_zero_implies_secondCovariance_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JW_originalSpatialMinor_ne_of_secondCovariance_dominates

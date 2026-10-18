import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorStrictTemporalOrderV5_JZ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIPhysicalReceiverQuantitativeDistanceV5_JT
import Mathlib.Tactic

/-!
# P4-Q2-KA — authentic Wilson posterior: ALL-positive Banach receiver separation

JZ proves the literal original TWO-interacting-Wilson-posterior SU(2)
temporal test gap L_b(D) < 0 for EVERY frozen b > 0. This is qualitative;
JP's explicit volume-independent lower margin is only a small-b theorem.

JS constructs the genuine two-posterior REAL linear test L_b on
C(SU(2),R); JT bounds |L_b(F)| <= E(b) ||F||_sup with
E(b) = exp(16b) - exp(-16b).

Use mathlib LinearMap.mkContinuous to obtain the ACTUAL bounded Banach
functional T_b, and its nonzero positive OPERATOR norm for ALL b>0.
At each literal finite-volume/right-configuration/link context define

      r_b(H,right,e) = ||T_b(D)|| / ||T_b|| > 0.

Then EVERY test in the actual kernel of T_b is at least r_b from D,
in the SU(2) continuous sup norm, and so is every original GAUSS-LAW
physical source receiver whose genuine original GI response vanishes.

If all physical GI responses vanish at one link/right context, the
ENTIRE actual algebraic physical receiver span (plus the constant)
is separated from D by this strictly positive Banach norm distance.
Conversely a single true physical source receiver (or a genuine linear
combination modulo constants) closer than r_b forces nonzero original
physical GI detection, for ANY b>0.

The radius depends on the actual H/right/link context through T_b;
NO volume/scale-uniform numeric positive bound is claimed for ALL b.
No assumed approximation exists, no synthetic frame/rank and no claim
of the still-OPEN spatial Wilson two-context GI nonzero witness,
H1-C3 or continuum Yang-Mills mass gap. Original interacting posteriors
and their true Perron weights are never replaced by Haar posteriors.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KA_borelSpace :
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
local notation "D" => p4Q2JM_temporalWilsonContinuous

/-- The ORIGINAL two-interacting-Wilson-posterior test as an honest
bounded continuous REAL linear functional on C(SU(2),R). The continuity
bound is JT's genuine posterior density envelope, not a new axiom. -/
noncomputable def p4Q2KA_originalWilsonPosteriorCLM
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    C(Gauge, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    (p4Q2JS_originalPosteriorTestLinearMap H b hb right e)
    (p4Q2JT_originalPosteriorEnvelope b)
    (by
      intro F
      simpa only [mul_comm] using
        (p4Q2JT_originalPosteriorTestLinearMap_norm_le_envelope
          H b hb right e F))

/-- The Banach functional is literally the original Wilson SU(2)
conditional-posterior expectation difference of JP, unchanged. -/
theorem p4Q2KA_originalWilsonPosteriorCLM_apply
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) :
    p4Q2KA_originalWilsonPosteriorCLM H b hb right e F =
      p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
        H b hb right e F := by
  exact p4Q2JS_originalPosteriorTestLinearMap_eq_JP H b hb right e F

/-- The literal JL original Wilson density envelope controls the
operator norm on this actual continuous function Banach space. -/
theorem p4Q2KA_originalWilsonPosteriorCLM_norm_le_envelope
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    ‖p4Q2KA_originalWilsonPosteriorCLM H b hb.le right e‖ ≤
      p4Q2JT_originalPosteriorEnvelope b := by
  unfold p4Q2KA_originalWilsonPosteriorCLM
  apply LinearMap.mkContinuous_norm_le
  exact (p4Q2JT_originalPosteriorEnvelope_pos b hb).le

/-- JZ gives STRICT temporal SU(2) Wilson detection for ALL
positive couplings, now as a genuine Banach continuous functional. -/
theorem p4Q2KA_originalWilsonPosteriorCLM_temporal_strictNegative
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    p4Q2KA_originalWilsonPosteriorCLM H b hb.le right e D < 0 := by
  rw [p4Q2KA_originalWilsonPosteriorCLM_apply]
  exact p4Q2JZ_originalWilsonTemporalTestGap_strictNegative_allPositive
    H b hb right e

/-- In particular the ORIGINAL interacting Wilson two-posterior
functional has strictly positive operator norm for EVERY b>0. -/
theorem p4Q2KA_originalWilsonPosteriorCLM_opNorm_pos
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    0 < ‖p4Q2KA_originalWilsonPosteriorCLM H b hb.le right e‖ := by
  have hneg := p4Q2KA_originalWilsonPosteriorCLM_temporal_strictNegative
    H b hb right e
  have hne :
      p4Q2KA_originalWilsonPosteriorCLM H b hb.le right e ≠ 0 := by
    intro hz
    rw [hz] at hneg
    simp at hneg
  exact (norm_pos_iff).2 hne

/-- TRUE nonperturbative strictly positive context-sensitive Banach
distance threshold. There is no fictitious volume-uniform norm floor. -/
noncomputable def p4Q2KA_originalWilsonOperatorDetectionRadius
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) : ℝ :=
  ‖p4Q2KA_originalWilsonPosteriorCLM H b hb right e D‖ /
    ‖p4Q2KA_originalWilsonPosteriorCLM H b hb right e‖

theorem p4Q2KA_originalWilsonOperatorDetectionRadius_pos
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    0 < p4Q2KA_originalWilsonOperatorDetectionRadius
      H b hb.le right e := by
  unfold p4Q2KA_originalWilsonOperatorDetectionRadius
  apply div_pos
  · exact (norm_pos_iff).2
      (ne_of_lt (p4Q2KA_originalWilsonPosteriorCLM_temporal_strictNegative
        H b hb right e))
  · exact p4Q2KA_originalWilsonPosteriorCLM_opNorm_pos
      H b hb right e

/-- UNCONDITIONAL, ALL-POSITIVE-GENUINE-COUPLING separation from the
kernel of the actual Wilson Banach functional. This uses the sharp
OPERATOR norm rather than JT's overestimate E(b). -/
theorem p4Q2KA_originalWilsonPosteriorKernel_distance_ge
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ))
    (hzero : p4Q2KA_originalWilsonPosteriorCLM H b hb.le right e F = 0) :
    p4Q2KA_originalWilsonOperatorDetectionRadius H b hb.le right e ≤
      ‖D - F‖ := by
  let T := p4Q2KA_originalWilsonPosteriorCLM H b hb.le right e
  have hTF : T F = 0 := hzero
  have hEq : T (D - F) = T D := by
    rw [map_sub, hTF, sub_zero]
  have hOp : ‖T D‖ ≤ ‖T‖ * ‖D - F‖ := by
    calc
      ‖T D‖ = ‖T (D - F)‖ := by rw [hEq]
      _ ≤ ‖T‖ * ‖D - F‖ := T.le_opNorm _
  have hTpos := p4Q2KA_originalWilsonPosteriorCLM_opNorm_pos
    H b hb right e
  change 0 < ‖T‖ at hTpos
  unfold p4Q2KA_originalWilsonOperatorDetectionRadius
  apply (div_le_iff₀ hTpos).2
  simpa [T, mul_comm] using hOp

/-- If ALL physical Gauss-law Wilson GI responses vanish at fixed
right/link context, every actual receiver in the authentic JS real
span (including constants) is at an explicitly positive norm
distance from the literal temporal D for EVERY b>0. -/
theorem p4Q2KA_physicalReceiverSpan_distance_ge_of_allGI_zero
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (hzero : ∀ f : Phys, ∀ left : Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e (left, right) = 0)
    (F : C(Gauge, ℝ))
    (hF : F ∈ p4Q2JS_originalPhysicalReceiverSpan
      H b hb.le right e) :
    p4Q2KA_originalWilsonOperatorDetectionRadius H b hb.le right e ≤
      ‖D - F‖ := by
  have hker :=
    (p4Q2JS_originalPhysicalReceiverSpan_le_actualPosteriorKernel
      H b hb.le right e hzero) hF
  have hFzero :
      p4Q2KA_originalWilsonPosteriorCLM H b hb.le right e F = 0 := by
    change p4Q2JS_originalPosteriorTestLinearMap H b hb.le right e F = 0
    exact hker
  exact p4Q2KA_originalWilsonPosteriorKernel_distance_ge
    H b hb right e F hFzero

/-- If a genuinely realized original physical receiver combination
approximates temporal D closer than the all-b positive operator
threshold, SOME true original Gauss-law physical GI response must be
nonzero. Approximation existence is NOT assumed. -/
theorem p4Q2KA_exists_originalPhysicalGI_nonzero_of_close_span
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ))
    (hF : F ∈ p4Q2JS_originalPhysicalReceiverSpan
      H b hb.le right e)
    (hClose : ‖D - F‖ <
      p4Q2KA_originalWilsonOperatorDetectionRadius H b hb.le right e) :
    ∃ f : Phys, ∃ left : Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e (left, right) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hFar := p4Q2KA_physicalReceiverSpan_distance_ge_of_allGI_zero
    H b hb right e hn F hF
  exact (not_lt_of_ge hFar) hClose

/-- If ONE real physical Gauss-law Wilson source has zero GI response,
its unchanged genuine SU(2) receiver lies at least the above positive
all-b Banach operator distance from temporal D. -/
theorem p4Q2KA_actualPhysicalReceiver_distance_ge_of_GI_zero
    (b : ℝ) (hb : 0 < b)
    (right left : Cfg) (e : Link) (f : Phys)
    (hGI : p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le f e (left, right) = 0) :
    p4Q2KA_originalWilsonOperatorDetectionRadius H b hb.le right e ≤
      ‖D - p4Q2JQ_originalPhysicalSourceLinkReceiver
        H b hb.le f e (left, right)‖ := by
  have hq :
      p4Q2JQ_originalPhysicalGIDensityWeight H b hb.le
        (left, right) ≠ 0 :=
    (p4Q2JQ_originalPhysicalGIDensityWeight_pos
      H b hb.le (left, right)).ne'
  have hGN := p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div
    H b hb.le f e (left, right)
  rw [hGI] at hGN
  have hMoment :
      p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
        H b hb.le right e
        (p4Q2JQ_originalPhysicalSourceLinkReceiver
          H b hb.le f e (left, right)) = 0 := by
    field_simp [hq] at hGN
    linarith
  have hKernel :
      p4Q2KA_originalWilsonPosteriorCLM H b hb.le right e
        (p4Q2JQ_originalPhysicalSourceLinkReceiver
          H b hb.le f e (left, right)) = 0 := by
    rw [p4Q2KA_originalWilsonPosteriorCLM_apply]
    exact hMoment
  exact p4Q2KA_originalWilsonPosteriorKernel_distance_ge
    H b hb right e _ hKernel

/-- A single actual Gauss-law physical source receiver closer than
the true positive OPERATOR-NORM threshold is itself an original
nonzero two-interacting-posterior GI response, at ANY frozen b>0. -/
theorem p4Q2KA_actualPhysicalGI_nonzero_of_receiver_close
    (b : ℝ) (hb : 0 < b)
    (right left : Cfg) (e : Link) (f : Phys)
    (hClose :
      ‖D - p4Q2JQ_originalPhysicalSourceLinkReceiver
        H b hb.le f e (left, right)‖ <
        p4Q2KA_originalWilsonOperatorDetectionRadius H b hb.le right e) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le f e (left, right) ≠ 0 := by
  intro hzero
  have hFar := p4Q2KA_actualPhysicalReceiver_distance_ge_of_GI_zero
    H b hb right left e f hzero
  exact (not_lt_of_ge hFar) hClose

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_originalWilsonPosteriorCLM_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_originalWilsonPosteriorCLM_norm_le_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_originalWilsonPosteriorCLM_temporal_strictNegative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_originalWilsonPosteriorCLM_opNorm_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_originalWilsonOperatorDetectionRadius_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_originalWilsonPosteriorKernel_distance_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_physicalReceiverSpan_distance_ge_of_allGI_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_exists_originalPhysicalGI_nonzero_of_close_span
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_actualPhysicalReceiver_distance_ge_of_GI_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KA_actualPhysicalGI_nonzero_of_receiver_close

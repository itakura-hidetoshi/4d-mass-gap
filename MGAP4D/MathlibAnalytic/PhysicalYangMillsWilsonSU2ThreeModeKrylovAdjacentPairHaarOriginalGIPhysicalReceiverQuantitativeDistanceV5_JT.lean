import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIPhysicalReceiverSpanObstructionV5_JS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorWeakFrozenNoGoV5_JL
import Mathlib.Tactic

/-!
# P4-Q2-JT — quantitative distance obstruction for genuine physical Wilson receivers

At a fixed actual physical link/right Wilson context, JS proves that the
literal temporal SU(2) Wilson contrast D is not in the algebraic span of
original physical Gauss-law source receivers (plus constants) IF every
original interacting-Wilson physical GI response vanishes.

Here we strengthen the exact nonmembership to an EXPLICIT POSITIVE
SUP-NORM DISTANCE, using ONLY the original Wilson posterior density
contrast, JL's true exponential bound, and JP's strict temporal detection.

For every 0 < b < JP's universal positive Wilson detection radius, define

  E(b) = exp(16b) - exp(-16b) > 0,
  epsilon(b) = b * V_SU2 / (2 * E(b)) > 0.

The genuine original two-posterior test linear map L obeys
  |L(F)| <= E(b) * ||F||_sup.

JP proves |L(D)| >= b V_SU2 / 2. Therefore, for ANY continuous SU(2) F,
  b V_SU2 / 2 <= |L(F)| + E(b) * ||D-F||_sup.

If all original GI responses of true physical Gauss-law sources vanish,
the ORIGINAL physical receiver span belongs to ker L; hence
  forall F in actual receiver span: epsilon(b) <= ||D-F||_sup.

Contrapositively, ONE actual physical receiver-span approximation to D
closer than epsilon(b) FORCES an actual nonzero original GI response.
No representation/density/frame/nondegeneracy assumption is inserted.
The radius depends on b and literal SU(2) Haar variance, but not on
spatial lattice volume, physical link or right Wilson boundary.

This is a genuine quantitative necessary obstruction; it does NOT prove
the approximation exists, the distinct JK static spatial Wilson GI minor
is nonzero, uniform Krylov source coercivity, H1-C3, or continuum YM mass gap.
The two interacting conditional Wilson posteriors are never replaced by Haar.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JT_borelSpace :
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
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2JM_temporalWilsonContinuous
local notation "V" => p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance

/-- The TRUE interacting Wilson two-posterior density contrast's
volume/link/right-context-independent pointwise Haar envelope. -/
noncomputable def p4Q2JT_originalPosteriorEnvelope (b : ℝ) : ℝ :=
  Real.exp (16 * b) - Real.exp (-16 * b)

theorem p4Q2JT_originalPosteriorEnvelope_pos (b : ℝ) (hb : 0 < b) :
    0 < p4Q2JT_originalPosteriorEnvelope b := by
  unfold p4Q2JT_originalPosteriorEnvelope
  exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))

/-- The ORIGINAL two interacting Wilson posterior test gap is bounded
in the continuous SU(2) sup norm by JL's literal signed-density envelope.
No surrogate posterior probability or unproved physical receiver norm. -/
theorem p4Q2JT_originalPosteriorTestLinearMap_norm_le_envelope
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) :
    ‖p4Q2JS_originalPosteriorTestLinearMap H b hb right e F‖ ≤
      ‖F‖ * p4Q2JT_originalPosteriorEnvelope b := by
  let P := p4Q2JN2_originalPosteriorDensityContrastContinuous H b hb right e
  let E := p4Q2JT_originalPosteriorEnvelope b
  have hP (g : Gauge) : ‖P g‖ ≤ E := by
    have hPg :
        P g = p4Q2GB_originalWilsonPosteriorLeftDensityContrast
          H b hb right e g := rfl
    rw [hPg, Real.norm_eq_abs]
    exact p4Q2JL_originalPosteriorContrast_abs_le H b hb right e g
  have hBound (g : Gauge) : ‖F g * P g‖ ≤ ‖F‖ * E := by
    calc
      ‖F g * P g‖ = ‖F g‖ * ‖P g‖ := norm_mul _ _
      _ ≤ ‖F‖ * ‖P g‖ :=
        mul_le_mul_of_nonneg_right (F.norm_coe_le_norm g) (norm_nonneg _)
      _ ≤ ‖F‖ * E :=
        mul_le_mul_of_nonneg_left (hP g) (norm_nonneg F)
  change ‖∫ g : Gauge, F g * P g ∂nu‖ ≤ ‖F‖ * E
  exact norm_integral_le_of_norm_le_const
    (μ := nu) (Filter.Eventually.of_forall hBound)

/-- The strict ORIGINAL temporal SU(2) Wilson test gap has an
explicit positive absolute-value lower bound, not just nonzero-ness. -/
theorem p4Q2JT_originalPosteriorTemporalTest_norm_lower
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right : Cfg) (e : Link) :
    b * V / 2 ≤
      ‖p4Q2JS_originalPosteriorTestLinearMap H b hb.le right e D‖ := by
  let L := p4Q2JS_originalPosteriorTestLinearMap H b hb.le right e
  have hNegative : L D ≤ -(b * V) / 2 := by
    simpa only [L, p4Q2JS_originalPosteriorTestLinearMap_eq_JP] using
      (p4Q2JP_originalWilsonTemporalTestGap_strictNegative_uniform
        H b hb hwindow right e).1
  have hLower : b * V / 2 ≤ -L D := by linarith
  have hNorm : -(L D) ≤ ‖L D‖ := by
    simpa only [Real.norm_eq_abs] using neg_le_abs (L D)
  exact hLower.trans hNorm

/-- For EVERY continuous SU(2) test F, genuine interacting-Wilson
temporal detection persists quantitatively up to its distance from F. -/
theorem p4Q2JT_originalPosteriorTemporalDetection_stability
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right : Cfg) (e : Link) (F : C(Gauge, ℝ)) :
    b * V / 2 ≤
      ‖p4Q2JS_originalPosteriorTestLinearMap H b hb.le right e F‖ +
        ‖D - F‖ * p4Q2JT_originalPosteriorEnvelope b := by
  let L := p4Q2JS_originalPosteriorTestLinearMap H b hb.le right e
  have hSplit : L D = L F + L (D - F) := by
    rw [map_sub]
    abel
  have hErr := p4Q2JT_originalPosteriorTestLinearMap_norm_le_envelope
    H b hb.le right e (D - F)
  change ‖L (D - F)‖ ≤
    ‖D - F‖ * p4Q2JT_originalPosteriorEnvelope b at hErr
  calc
    b * V / 2 ≤ ‖L D‖ :=
      p4Q2JT_originalPosteriorTemporalTest_norm_lower H b hb hwindow right e
    _ = ‖L F + L (D - F)‖ := by rw [hSplit]
    _ ≤ ‖L F‖ + ‖L (D - F)‖ := norm_add_le _ _
    _ ≤ ‖L F‖ + ‖D - F‖ * p4Q2JT_originalPosteriorEnvelope b :=
      add_le_add_left hErr _

/-- The original physical Wilson Gauss-law receiver span cannot even
APPROXIMATE the literal temporal Wilson contrast too well if all actual
GI observations are zero. This is stronger than JS's nonmembership. -/
theorem p4Q2JT_originalPhysicalReceiverSpan_null_distance_product
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right : Cfg) (e : Link)
    (hzero : ∀ f : Phys, ∀ left : Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e (left, right) = 0)
    (F : C(Gauge, ℝ))
    (hF : F ∈ p4Q2JS_originalPhysicalReceiverSpan H b hb.le right e) :
    b * V / 2 ≤ ‖D - F‖ * p4Q2JT_originalPosteriorEnvelope b := by
  let L := p4Q2JS_originalPosteriorTestLinearMap H b hb.le right e
  have hZero : L F = 0 :=
    (p4Q2JS_originalPhysicalReceiverSpan_le_actualPosteriorKernel
      H b hb.le right e hzero) hF
  have hBound :=
    p4Q2JT_originalPosteriorTemporalDetection_stability
      H b hb hwindow right e F
  change b * V / 2 ≤ ‖L F‖ + ‖D - F‖ *
    p4Q2JT_originalPosteriorEnvelope b at hBound
  rw [hZero, norm_zero, zero_add] at hBound
  exact hBound

/-- Explicit strictly positive genuine-receiver approximation radius.
It uses JL's physical density envelope and JP's genuine Wilson variance.
No fictitious source / assumed source frame is introduced. -/
noncomputable def p4Q2JT_physicalReceiverApproximationRadius (b : ℝ) : ℝ :=
  (b * V) / (2 * p4Q2JT_originalPosteriorEnvelope b)

theorem p4Q2JT_physicalReceiverApproximationRadius_pos
    (b : ℝ) (hb : 0 < b) :
    0 < p4Q2JT_physicalReceiverApproximationRadius b := by
  unfold p4Q2JT_physicalReceiverApproximationRadius
  exact div_pos
    (mul_pos hb p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos)
    (mul_pos (by norm_num)
      (p4Q2JT_originalPosteriorEnvelope_pos b hb))

/-- An actual original GI-invisible receiver span has an explicit
positive SUP-NORM DISTANCE from temporal Wilson D at every positive
coupling in JP's volume-independent Wilson detection interval. -/
theorem p4Q2JT_originalPhysicalReceiverSpan_distance_ge
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right : Cfg) (e : Link)
    (hzero : ∀ f : Phys, ∀ left : Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e (left, right) = 0)
    (F : C(Gauge, ℝ))
    (hF : F ∈ p4Q2JS_originalPhysicalReceiverSpan H b hb.le right e) :
    p4Q2JT_physicalReceiverApproximationRadius b ≤ ‖D - F‖ := by
  have hE := p4Q2JT_originalPosteriorEnvelope_pos b hb
  have hProduct :=
    p4Q2JT_originalPhysicalReceiverSpan_null_distance_product
      H b hb hwindow right e hzero F hF
  unfold p4Q2JT_physicalReceiverApproximationRadius
  apply (div_le_iff₀ (mul_pos (by norm_num) hE)).2
  nlinarith [hProduct]

/-- STRICTLY APPROXIMATING temporal Wilson D by a LINEAR COMBINATION
of genuine original physical Gauss-law Wilson receivers (and constants)
FORCES a nonzero original two-interacting-posterior GI expectation.
No density/frame/approximation existence is asserted. -/
theorem p4Q2JT_exists_nonzeroOriginalPhysicalGI_of_close_actualSpan
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ))
    (hF : F ∈ p4Q2JS_originalPhysicalReceiverSpan H b hb.le right e)
    (hClose : ‖D - F‖ <
      p4Q2JT_physicalReceiverApproximationRadius b) :
    ∃ f : Phys, ∃ left : Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e (left, right) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hDistance :=
    p4Q2JT_originalPhysicalReceiverSpan_distance_ge
      H b hb hwindow right e hn F hF
  exact (not_lt_of_ge hDistance) hClose


/-- The UNCONDITIONAL quantitative separation from the kernel of the
TRUE original two-posterior test map, even when other physical sources
do have a nonzero GI response. Thus the result is nonvacuous without
an assumption that ALL physical sources are GI-invisible. -/
theorem p4Q2JT_originalPosteriorTestKernel_distance_ge
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ))
    (hF : p4Q2JS_originalPosteriorTestLinearMap H b hb.le right e F = 0) :
    p4Q2JT_physicalReceiverApproximationRadius b ≤ ‖D - F‖ := by
  have hStability :=
    p4Q2JT_originalPosteriorTemporalDetection_stability
      H b hb hwindow right e F
  rw [hF, norm_zero, zero_add] at hStability
  have hE := p4Q2JT_originalPosteriorEnvelope_pos b hb
  unfold p4Q2JT_physicalReceiverApproximationRadius
  apply (div_le_iff₀ (mul_pos (by norm_num) hE)).2
  nlinarith [hStability]

/-- Source-specific original physical obstruction, with no universal
GI-vanishing assumption: if ONE actual Gauss-law Hilbert source has
zero original two-interacting-Wilson-posterior GI response, its ACTUAL
physical Wilson receiver is at least epsilon(b) away from temporal D. -/
theorem p4Q2JT_actualPhysicalReceiver_distance_ge_of_GI_zero
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right left : Cfg) (e : Link) (f : Phys)
    (hGI : p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le f e (left, right) = 0) :
    p4Q2JT_physicalReceiverApproximationRadius b ≤
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
      p4Q2JS_originalPosteriorTestLinearMap H b hb.le right e
        (p4Q2JQ_originalPhysicalSourceLinkReceiver
          H b hb.le f e (left, right)) = 0 := by
    rw [p4Q2JS_originalPosteriorTestLinearMap_eq_JP]
    exact hMoment
  exact p4Q2JT_originalPosteriorTestKernel_distance_ge
    H b hb hwindow right e _ hKernel

/-- A single genuinely physical source whose unchanged actual Wilson
receiver approximates D within epsilon(b) is itself a nonzero ORIGINAL
GI source. No artificial linear combination or source-frame hypothesis. -/
theorem p4Q2JT_actualPhysicalGI_nonzero_of_receiver_close
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right left : Cfg) (e : Link) (f : Phys)
    (hClose :
      ‖D - p4Q2JQ_originalPhysicalSourceLinkReceiver
        H b hb.le f e (left, right)‖ <
        p4Q2JT_physicalReceiverApproximationRadius b) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le f e (left, right) ≠ 0 := by
  intro hZero
  have hFar :=
    p4Q2JT_actualPhysicalReceiver_distance_ge_of_GI_zero
      H b hb hwindow right left e f hZero
  exact (not_lt_of_ge hFar) hClose


end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_originalPosteriorEnvelope_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_originalPosteriorTestLinearMap_norm_le_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_originalPosteriorTemporalTest_norm_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_originalPosteriorTemporalDetection_stability
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_originalPhysicalReceiverSpan_null_distance_product
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_physicalReceiverApproximationRadius_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_originalPhysicalReceiverSpan_distance_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_exists_nonzeroOriginalPhysicalGI_of_close_actualSpan

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_originalPosteriorTestKernel_distance_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_actualPhysicalReceiver_distance_ge_of_GI_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JT_actualPhysicalGI_nonzero_of_receiver_close

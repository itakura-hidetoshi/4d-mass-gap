import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSpatialPosteriorAntisymV5_JY
import Mathlib.Tactic

/-!
# P4-Q2-JZ: genuine original interacting Wilson strict temporal detection for EVERY b > 0

JX establishes at EVERY positive frozen coupling (not only a small one)
the strictly opposite order of the literal ORIGINAL two-interacting-
posterior SU(2) density minor and the temporal Wilson contrast D.
JY establishes exact antisymmetrization of the genuinely normalized
physical posterior test over SU(2) × SU(2).

Use pinned mathlib compact Haar open-set positivity to turn a single
STRICT temporal difference and a globally order-preserving continuous
receiver into a STRICTLY NEGATIVE original posterior test gap.
This requires no differentiability of either posterior or Perron vacuum.

The special literal temporal Wilson contrast D has the actual strict
pair D(1) = -2 < +2 = D(R_pi). Thus for ALL frozen b > 0, arbitrary
finite spatial volume, actual physical link and right Wilson context,

             originalPosteriorTestGap_b(D) < 0.

This extends the positive detection window of JP qualitatively to the
ENTIRE positive frozen coupling axis, while JP's explicit uniform
numerical lower bound remains only in its stated weak-coupling window.

A genuine anchored SPATIAL Wilson Gauss-law source satisfies the same
strict original two-context GI minor criterion IF its original physical
SU(2) receiver is actually temporal-order-preserving and strictly
increasing at a specified genuine pair. Such physical receiver
alignment is NOT proved here. There is no generic rank/frame axiom,
independent-Haar conditional posterior, H1-C3 or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JZ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JZ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JZ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JZ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JZ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2JZ_haarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast
local notation "M" => p4Q2JN_originalPosteriorTwoPointMinor H

/-- A fully reusable strict signed double-Haar integral principle for
CONTINUOUS nonpositive SU(2) × SU(2) kernels with a genuine strict
witness. The ORIGINAL Haar product has positive measure on every
nonempty open set, not just abstract a.e. nonnegativity. -/
private theorem p4Q2JZ_integral_integral_strictNegative_of_pointwise
    (Q : Gauge × Gauge → ℝ) (hQ : Continuous Q)
    (hNonpos : ∀ p, Q p ≤ 0)
    (p : Gauge × Gauge) (hp : Q p < 0) :
    (∫ g : Gauge, ∫ h : Gauge, Q (g,h) ∂nu ∂nu) < 0 := by
  let R : Gauge × Gauge → ℝ := fun p => -(Q p)
  have hRCont : Continuous R := hQ.neg
  have hRI : Integrable R
      ((normalizedCompactHaar Gauge).prod (normalizedCompactHaar Gauge)) :=
    hRCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRNonneg (p : Gauge × Gauge) : 0 ≤ R p := by
    exact neg_nonneg.mpr (hNonpos p)
  have hRPos : 0 < R p := by
    exact neg_pos.mpr hp
  have hOpen : IsOpen (Function.support R) := by
    change IsOpen (R ⁻¹' ({0} : Set ℝ)ᶜ)
    exact (isClosed_singleton.isOpen_compl).preimage hRCont
  have hNonempty : (Function.support R).Nonempty :=
    ⟨p, ne_of_gt hRPos⟩
  have hIntegralPos :
      0 < ∫ p : Gauge × Gauge, R p
          ∂((normalizedCompactHaar Gauge).prod (normalizedCompactHaar Gauge)) := by
    rw [integral_pos_iff_support_of_nonneg]
    · exact hOpen.measure_pos _ hNonempty
    · exact hRNonneg
    · exact hRI
  have hFubini := integral_prod R hRI
  have hDoubleNeg :
      (∫ g : Gauge, ∫ h : Gauge, R (g,h) ∂nu ∂nu) =
      -(∫ g : Gauge, ∫ h : Gauge, Q (g,h) ∂nu ∂nu) := by
    dsimp [R]
    simp only [integral_neg]
  rw [hFubini, hDoubleNeg] at hIntegralPos
  linarith

/-- A true continuous SU(2) receiver that respects temporal Wilson
order and strictly separates at least one physically available
temporal SU(2) pair is detected with a STRICT negative sign by the
two ORIGINAL INTERACTING Wilson conditional posteriors at EVERY b>0. -/
theorem p4Q2JZ_originalPosteriorTestGap_strictNegative_of_monotoneWitness
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ))
    (hMon : ∀ g h : Gauge, D g ≤ D h → F g ≤ F h)
    (hWitness : ∃ g h : Gauge, D g < D h ∧ F g < F h) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
      H b hb.le right e F < 0 := by
  let P0 := p4Q2JN2_originalPosteriorIdentityContinuous H b hb.le right e
  let P1 := p4Q2JN2_originalPosteriorPiContinuous H b hb.le right e
  let Q : Gauge × Gauge → ℝ :=
    fun p => (F p.1 - F p.2) * M b hb.le right e p.1 p.2
  have hMCont :
      Continuous (fun p : Gauge × Gauge => M b hb.le right e p.1 p.2) := by
    change Continuous (fun p : Gauge × Gauge =>
      P0 p.1 * P1 p.2 - P0 p.2 * P1 p.1)
    exact ((P0.continuous.comp continuous_fst).mul
      (P1.continuous.comp continuous_snd)).sub
      ((P0.continuous.comp continuous_snd).mul
        (P1.continuous.comp continuous_fst))
  have hQCont : Continuous Q :=
    ((F.continuous.comp continuous_fst).sub
      (F.continuous.comp continuous_snd)).mul hMCont
  have hNonpos (p : Gauge × Gauge) : Q p ≤ 0 :=
    p4Q2JY_originalPosteriorMonotonePair_nonpos
      H b hb right e F hMon p.1 p.2
  obtain ⟨g,h,hD,hF⟩ := hWitness
  have hMinor : 0 < M b hb.le right e g h :=
    p4Q2JX_originalPosteriorMinor_pos_of_temporal_lt
      H b hb right e g h hD
  have hStrict : Q (g,h) < 0 := by
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hF) hMinor
  have hDouble :=
    p4Q2JZ_integral_integral_strictNegative_of_pointwise
      Q hQCont hNonpos (g,h) hStrict
  have hAntisym :=
    p4Q2JY_originalPosteriorTestGap_antisymmetric
      H b hb.le right e F
  change (2 : ℝ) *
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb.le right e F =
      (∫ g : Gauge, ∫ h : Gauge, Q (g,h) ∂nu ∂nu) at hAntisym
  rw [← hAntisym] at hDouble
  linarith

/-- Stronger genuine posterior TEMPORAL Wilson test detection:
strict negativity at EVERY positive coupling b, not just JP's
explicit small-coupling interval. Uniform in the QUANTIFIERS over
finite volume H, actual physical link e and right Wilson context.
This is a qualitative strict sign, NOT a b/H-uniform numerical margin. -/
theorem p4Q2JZ_originalWilsonTemporalTestGap_strictNegative_allPositive
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
      H b hb.le right e p4Q2JM_temporalWilsonContinuous < 0 := by
  have hStrict :
      D (1 : Gauge) < D (specialUnitaryTwoRotation Real.pi) := by
    rw [p4Q2FZ_originalSU2TemporalWilsonContrast_one,
      p4Q2FZ_originalSU2TemporalWilsonContrast_rotation]
    norm_num
  apply p4Q2JZ_originalPosteriorTestGap_strictNegative_of_monotoneWitness
    H b hb right e p4Q2JM_temporalWilsonContinuous
  · intro g h h
    exact h
  · exact ⟨1, specialUnitaryTwoRotation Real.pi, hStrict, hStrict⟩

/-- A precise all-positive-coupling sufficient criterion for the
AUTHENTIC anchored spatial Wilson Gauss-law source to have a nonzero
second-context static spatial GI minor: its actual source receiver
must be temporally monotone with a strict pair.
The source condition remains unproved; no synthetic detector is added. -/
theorem p4Q2JZ_originalSpatialMinor_ne_of_genuineReceiverTemporalMonotone
    (b : ℝ) (hb : 0 < b)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor :
      p4Q2JH_originalGIResponseCLM H b hb.le e z
        (ContinuousMap.toLp 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
          ℝ (1 : C(Cfg, ℝ))) ≠ 0)
    (hMon :
      ∀ g h : Gauge, D g ≤ D h →
        p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
          e' z' g ≤
        p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
          e' z' h)
    (hWitness : ∃ g h : Gauge, D g < D h ∧
        p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
          e' z' g <
        p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
          e' z' h) :
    p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z' ≠ 0 := by
  let F := p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le
    (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z) e' z'
  have hGap :
      p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
        H b hb.le z'.2 e' F < 0 :=
    p4Q2JZ_originalPosteriorTestGap_strictNegative_of_monotoneWitness
      H b hb z'.2 e' F hMon hWitness
  have hq : p4Q2JQ_originalPhysicalGIDensityWeight
      H b hb.le z' ≠ 0 :=
    (p4Q2JQ_originalPhysicalGIDensityWeight_pos
      H b hb.le z').ne'
  have hGI :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb.le
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
        e' z' ≠ 0 := by
    rw [p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div]
    exact div_ne_zero (neg_ne_zero.mpr (ne_of_lt hGap)) hq
  exact (p4Q2JU_originalSpatialMinor_ne_iff_physicalGI_ne
    H b hb.le e e' z z' hAnchor).2 hGI

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JZ_originalPosteriorTestGap_strictNegative_of_monotoneWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JZ_originalWilsonTemporalTestGap_strictNegative_allPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JZ_originalSpatialMinor_ne_of_genuineReceiverTemporalMonotone

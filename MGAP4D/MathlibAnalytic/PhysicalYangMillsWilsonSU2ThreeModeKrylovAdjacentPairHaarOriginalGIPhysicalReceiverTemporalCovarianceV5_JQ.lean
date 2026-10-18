import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTemporalPosteriorTestDetectionV5_JP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTransferFiberDetectorKernelV5_GN
import Mathlib.Tactic

/-!
# P4-Q2-JQ: TRUE original GI physical source receiver and SU(2) temporal covariance criterion

JP proves the ORIGINAL interacting two-posterior conditional law genuinely
detects the temporal SU(2) Wilson contrast D on a uniform positive-beta
window, with a quantitative O(beta²) remainder for testing against ANY
continuous SU(2) source.

Here the test source is no longer a freely selected temporal observable:
it is the ACTUAL ORIGINAL SU(2) link receiver of an arbitrary
Gauss-law gauge-invariant PHYSICAL HILBERT source f, built from the
ORIGINAL normalized physical one-slab joint receiver product BCF and
the unchanged physical right-link insertion. GN already proved the
original physical GI expectation gap is precisely minus this
receiver's genuine two-posterior density moment divided by the
original nonzero density-cancellation normalization factor.

We connect these two literal physical definitions and PROVE
 - an exact factorization of the original GI detector through the
   TRUE original interacting posterior temporal source gap;
 - for 0<=beta<=1/4, the explicit source-aware quantitative relation

  |q_beta(z) * GI_beta(f,e,z) -
      beta * integral_SU2 receiver_beta(f,e,z;g)*D(g) dHaar(g)|
     <= ||receiver_beta(f,e,z)||_sup * 272*exp(8)*beta²;

 - a mathematically sharp **source-specific** sufficient condition
   for original GI detection based on the ACTUAL receiver's correlation
   with D dominating the explicitly quantified O(beta) error.

This is a concrete connection from temporal posterior sensitivity to
the original physical GI source, not an assertion that the required
receiver-D correlation is always nonzero. The original spatial Wilson
static two-context minor, H1-C3 limit and continuum mass gap remain
open. No synthetic source, independent-Haar conditional posterior,
Dobrushin hypothesis, sorry, or new axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JQ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JQ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JQ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JQ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen

variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast
local notation "Err" => (272 * Real.exp 8 : ℝ)

/-- The literal ORIGINAL normalizing weight for the gauge-invariant
physical source detector. It is strictly positive at all couplings,
and is not discarded or replaced by a new posterior. -/
noncomputable def p4Q2JQ_originalPhysicalGIDensityWeight
    (b : ℝ) (hb : 0 ≤ b) (z : Cfg × Cfg) : ℝ :=
  normalizedPhysicalOneSlabJointHalfDensityWeightBCF H 2 (by norm_num) b hb z *
    normalizedPhysicalOneSlabContinuousVacuumInverseBCF H 2 (by norm_num) b hb z.2

theorem p4Q2JQ_originalPhysicalGIDensityWeight_pos
    (b : ℝ) (hb : 0 ≤ b) (z : Cfg × Cfg) :
    0 < p4Q2JQ_originalPhysicalGIDensityWeight H b hb z := by
  unfold p4Q2JQ_originalPhysicalGIDensityWeight
  exact p4Q2FF_originalWilsonDensityCancellationWeight_pos
    H 2 (by norm_num) b hb z

/-- EXACT physical Wilson right-link receiver as a bounded continuous
SU(2) test, obtained by inserting the original gauge-link variable
into the true source-dependent normalized one-slab joint receiver BCF.
The Gauss-law Hilbert source f is not replaced by an abstract vector. -/
noncomputable def p4Q2JQ_originalPhysicalSourceLinkReceiver
    (b : ℝ) (hb : 0 ≤ b) (f : Phys)
    (e : Link) (z : Cfg × Cfg) : C(Gauge, ℝ) := by
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF
    H 2 (by norm_num) b hb f
  have hUp :
      Continuous (fun g : Gauge => (z.1, Function.update z.2 e g)) := by
    fun_prop
  exact ⟨fun g => O (z.1, Function.update z.2 e g),
    O.continuous.comp hUp⟩

@[simp] theorem p4Q2JQ_originalPhysicalSourceLinkReceiver_apply
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (g : Gauge) :
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z g =
      normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) b hb f
        (z.1, Function.update z.2 e g) := rfl

/-- GN's already VERIFIED exact original physical expectation-gap formula
is the JP moment for the SAME genuine original interacting posterior,
tested against the ACTUAL physically normalized Gauss-law source
receiver. The weight denominator is the ORIGINAL physical one. -/
theorem p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb f e z =
      -(p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb z.2 e
        (p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z)) /
        p4Q2JQ_originalPhysicalGIDensityWeight H b hb z := by
  simpa only [p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap,
    p4Q2JQ_originalPhysicalGIDensityWeight,
    p4Q2JQ_originalPhysicalSourceLinkReceiver_apply] using
    (p4Q2GN_originalExpectationGap_eq_updatedReceiverContrast H b hb f e z)

/-- A genuinely source-dependent quantitative first-order GI bridge.
The SAME ORIGINAL Wilson physical receiver appears in both the actual
GI gap and the temporal SU(2) crossing-covariance. Its true physical
normalizing density factor is retained, not assumed constant in beta.
Uniformity is in lattice volume/link/right contexts at the level of
the explicit error coefficient; the receiver's genuine supnorm may
depend on the physical source and context. -/
theorem p4Q2JQ_originalPhysicalGI_temporalCovariance_quadratic
    (b : ℝ) (hb : 0 ≤ b) (hsmall : b ≤ (1 / 4 : ℝ))
    (f : Phys) (e : Link) (z : Cfg × Cfg) :
    ‖p4Q2JQ_originalPhysicalGIDensityWeight H b hb z *
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb f e z -
        b * (∫ g : Gauge,
          p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z g *
            D g ∂nu)‖ ≤
      ‖p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z‖ *
        (Err * b ^ 2) := by
  let q := p4Q2JQ_originalPhysicalGIDensityWeight H b hb z
  let F := p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z
  let m := p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb z.2 e F
  let t : ℝ := ∫ g : Gauge, F g * D g ∂nu
  have hq : q ≠ 0 :=
    (p4Q2JQ_originalPhysicalGIDensityWeight_pos H b hb z).ne'
  have hGN :=
    p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div
      H b hb f e z
  have hFactor :
      q * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb f e z - b * t =
        -(m + b * t) := by
    rw [hGN]
    change q * ((-m) / q) - b * t = -(m + b * t)
    field_simp [hq]; ring
  have hJP :=
    p4Q2JP_originalWilsonTemporalTestGap_quadraticError
      H b hb hsmall z.2 e F
  change ‖q * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb f e z - b * t‖ ≤ ‖F‖ * (Err * b ^ 2)
  rw [hFactor]
  simpa only [norm_neg] using hJP

/-- One explicit testable criterion for ACTUAL physical GI detection.
A genuine positive-coupling source whose true Wilson right-link
receiver has a temporal-Wilson Haar correlation that dominates the
derived finite-coupling O(beta) remainder has nonzero original GI gap.
The correlation is an EXPLICIT physical condition still needing proof
for the target spatial Wilson source, not a postulated detector frame. -/
theorem p4Q2JQ_originalPhysicalGI_nonzero_of_temporalCorrelation
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ (1 / 4 : ℝ))
    (f : Phys) (e : Link) (z : Cfg × Cfg)
    (hCorr :
      ‖p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le f e z‖ *
          (Err * b) <
        |∫ g : Gauge,
          p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le f e z g *
            D g ∂nu|) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le f e z ≠ 0 := by
  let q := p4Q2JQ_originalPhysicalGIDensityWeight H b hb.le z
  let F := p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le f e z
  let t : ℝ := ∫ g : Gauge, F g * D g ∂nu
  have hErr :=
    p4Q2JQ_originalPhysicalGI_temporalCovariance_quadratic
      H b hb.le hsmall f e z
  intro hZero
  have hMoment :
      ‖b * t‖ ≤ ‖F‖ * (Err * b ^ 2) := by
    rw [hZero] at hErr
    simpa only [mul_zero, zero_sub, norm_neg] using hErr
  have hMoment' : b * |t| ≤ ‖F‖ * (Err * b ^ 2) := by
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos hb] using hMoment
  have hStrict := mul_lt_mul_of_pos_left hCorr hb
  dsimp [F, t] at hStrict hMoment'
  nlinarith [hStrict, hMoment']

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JQ_originalPhysicalGIDensityWeight_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JQ_originalPhysicalGI_temporalCovariance_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JQ_originalPhysicalGI_nonzero_of_temporalCorrelation

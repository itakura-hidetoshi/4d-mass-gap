import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIPhysicalReceiverTemporalCovarianceV5_JQ
import Mathlib.Tactic

/-!
# P4-Q2-JR: exact centered physical GI receiver and temporal SU(2) covariance

The physical GN/JQ gauge-invariant source receiver depends on the REAL
Wilson one-slab kernel, the normalized Perron vacuum, physical left/right
boundary context and an authentic Gauss-law Hilbert source. Its
two-original-interacting-posterior signed law has normalized Haar mean
zero, as proved in GN/JP, and the actual temporal Wilson crossing
contrast also has normalized Haar mean zero, as proved in JO.

Here we QUOTIENT THE PHYSICAL RECEIVER BY THE CONSTANT DIRECTION
without altering its source, original conditional posterior laws,
Wilson kernel, or joint vacuum. An exact Haar centering of the ACTUAL
receiver gives a stronger, physically relevant error and a stricter
conditional GI source detection threshold:

  |q_b(z) GI_b(f,e,z) - b <center receiver_b,D>_Haar|
     <= ||center receiver_b||_sup * 272 exp(8) b²

for 0<=b<=1/4. Thus the sufficient nonzero condition is not
controlled by the possibly huge irrelevant constant part of the
original receiver. An exactly constant physical receiver makes the
original GI response identically ZERO. Any genuine correlation
|∫ center(receiver_b)*D| > Err*b*||center(receiver_b)|| guarantees
nonzero original physical GI response at b>0.

The nonzero spatial Wilson GI second-context witness is STILL NOT
deduced from mere temporal sensitivity. The remaining task is to
evaluate the actual centered receiver-D correlation for the ORIGINAL
spatial Wilson action/source, not postulate a nondegenerate frame.
Neither an independent-Haar CONDITIONAL posterior nor Dobrushin,
sorry/admit, new axioms or continuum mass-gap result are introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JR_borelSpace :
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

/-- The true normalized compact SU(2) Haar mean of the ACTUAL physical
Wilson Gauss-law source-dependent JQ receiver. -/
noncomputable def p4Q2JR_originalPhysicalReceiverHaarMean
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) : ℝ :=
  ∫ g : Gauge, p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z g ∂nu

/-- The original physical source receiver, minus ONLY its own actual
SU(2) Haar mean. No artificial source or substitute posterior is used. -/
noncomputable def p4Q2JR_originalPhysicalReceiverCentered
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    C(Gauge, ℝ) :=
  p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z -
    p4Q2JR_originalPhysicalReceiverHaarMean H b hb f e z •
      (1 : C(Gauge, ℝ))

/-- Genuine Haar centering annihilates the scalar mean of the physical
Wilson source receiver, without any condition on the physical vacuum. -/
theorem p4Q2JR_originalPhysicalReceiverCentered_HaarMean_zero
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    (∫ g : Gauge,
      p4Q2JR_originalPhysicalReceiverCentered H b hb f e z g ∂nu) = 0 := by
  let F := p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z
  let m : ℝ := p4Q2JR_originalPhysicalReceiverHaarMean H b hb f e z
  have hFI : Integrable (fun g : Gauge => F g) nu :=
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change ∫ g : Gauge, (F - m • (1 : C(Gauge, ℝ))) g ∂nu = 0
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one]
  rw [integral_sub hFI (integrable_const m)]
  have hConst : (∫ _g : Gauge, m ∂nu) = m := by simp
  rw [hConst]
  change (∫ g : Gauge, F g ∂nu) -
    (∫ g : Gauge, F g ∂nu) = 0
  exact sub_self _

/-- The true interacting two-posterior test gap is EXACTLY unchanged
by removing the actual physical receiver's Haar-constant part. -/
theorem p4Q2JR_originalPhysicalReceiverCenter_testGap_eq
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb z.2 e
      (p4Q2JR_originalPhysicalReceiverCentered H b hb f e z) =
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb z.2 e
      (p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z) :=
  p4Q2JP_originalPosteriorTemporalTestGap_constant_invisible H b hb z.2 e
    (p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z)
    (p4Q2JR_originalPhysicalReceiverHaarMean H b hb f e z)

/-- The physical SU(2) covariance with the LITERAL temporal Wilson
action is likewise unchanged by Haar centering the real receiver;
this uses the independently verified JO Haar-mean-zero theorem. -/
theorem p4Q2JR_originalPhysicalReceiverCentered_temporalCovariance_eq
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    (∫ g : Gauge,
      p4Q2JR_originalPhysicalReceiverCentered H b hb f e z g *
        D g ∂nu) =
    (∫ g : Gauge,
      p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z g *
        D g ∂nu) := by
  let F := p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e z
  let m : ℝ := p4Q2JR_originalPhysicalReceiverHaarMean H b hb f e z
  have hF : Integrable (fun g : Gauge => F g * D g) nu :=
    (F.continuous.mul p4Q2FZ_originalSU2TemporalWilsonContrast_continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hD : Integrable (fun g : Gauge => m * D g) nu :=
    (continuous_const.mul
      p4Q2FZ_originalSU2TemporalWilsonContrast_continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ g : Gauge, (F - m • (1 : C(Gauge, ℝ))) g * D g ∂nu) =
    ∫ g : Gauge, F g * D g ∂nu
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one]
  have hpoint (g : Gauge) : (F g - m) * D g = F g * D g - m * D g := by
    ring
  calc
    (∫ g : Gauge, (F g - m) * D g ∂nu) =
        ∫ g : Gauge, F g * D g - m * D g ∂nu := by
          exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ g : Gauge, F g * D g ∂nu) -
        (∫ g : Gauge, m * D g ∂nu) :=
      integral_sub hF hD
    _ = (∫ g : Gauge, F g * D g ∂nu) := by
      rw [integral_const_mul, p4Q2JO_temporalWilsonContrast_HaarMean_zero]
      ring

/-- The EXACT original physical GI detector only sees the Haar-centered
actual Wilson right-link source receiver, retaining its real
positive physical normalization factor q. -/
theorem p4Q2JR_originalPhysicalGI_eq_centeredReceiverGap
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb f e z =
      -(p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb z.2 e
          (p4Q2JR_originalPhysicalReceiverCentered H b hb f e z)) /
        p4Q2JQ_originalPhysicalGIDensityWeight H b hb z := by
  rw [p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div,
    p4Q2JR_originalPhysicalReceiverCenter_testGap_eq]

/-- Improved source-specific, volume-uniform-coefficient error: the
supnorm is that of the ACTUAL RECEIVER MODULO CONSTANTS, not the raw
physical receiver with its invisible constant component. -/
theorem p4Q2JR_originalPhysicalGI_centeredTemporalCovariance_quadratic
    (b : ℝ) (hb : 0 ≤ b) (hsmall : b ≤ (1 / 4 : ℝ))
    (f : Phys) (e : Link) (z : Cfg × Cfg) :
    ‖p4Q2JQ_originalPhysicalGIDensityWeight H b hb z *
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb f e z -
        b * (∫ g : Gauge,
          p4Q2JR_originalPhysicalReceiverCentered H b hb f e z g *
            D g ∂nu)‖ ≤
      ‖p4Q2JR_originalPhysicalReceiverCentered H b hb f e z‖ *
        (Err * b ^ 2) := by
  let q := p4Q2JQ_originalPhysicalGIDensityWeight H b hb z
  let Fc := p4Q2JR_originalPhysicalReceiverCentered H b hb f e z
  let m : ℝ := p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb z.2 e Fc
  let t : ℝ := ∫ g : Gauge, Fc g * D g ∂nu
  have hq : q ≠ 0 :=
    (p4Q2JQ_originalPhysicalGIDensityWeight_pos H b hb z).ne'
  have hGI := p4Q2JR_originalPhysicalGI_eq_centeredReceiverGap H b hb f e z
  have hFactor :
      q * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb f e z -
        b * t = -(m + b * t) := by
    rw [hGI]
    change q * ((-m) / q) - b * t = -(m + b * t)
    field_simp [hq]; ring
  have hJP :=
    p4Q2JP_originalWilsonTemporalTestGap_quadraticError
      H b hb hsmall z.2 e Fc
  change ‖q * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb f e z - b * t‖ ≤ ‖Fc‖ * (Err * b ^ 2)
  rw [hFactor]
  simpa only [norm_neg] using hJP

/-- If the ACTUAL physical Wilson receiver is Haar-constant, the
genuine original physical GI response is exactly ZERO, irrespective
of Wilson coupling or the unknown Perron vacuum. -/
theorem p4Q2JR_originalPhysicalGI_zero_of_centeredReceiver_zero
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (hzero : p4Q2JR_originalPhysicalReceiverCentered H b hb f e z = 0) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb f e z = 0 := by
  rw [p4Q2JR_originalPhysicalGI_eq_centeredReceiverGap, hzero]
  simp [p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap]

/-- Strict source-specific GI nonzero criterion using ONLY the genuine
Haar-centered physical receiver; it requires no artificial GI source
frame and never confuses a nonconstant receiver with an already
nonzero original static spatial Wilson determinant. -/
theorem p4Q2JR_originalPhysicalGI_nonzero_of_centeredTemporalCorrelation
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ (1 / 4 : ℝ))
    (f : Phys) (e : Link) (z : Cfg × Cfg)
    (hCorr :
      ‖p4Q2JR_originalPhysicalReceiverCentered H b hb.le f e z‖ *
          (Err * b) <
        |∫ g : Gauge,
          p4Q2JR_originalPhysicalReceiverCentered H b hb.le f e z g *
            D g ∂nu|) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le f e z ≠ 0 := by
  let Fc := p4Q2JR_originalPhysicalReceiverCentered H b hb.le f e z
  let t : ℝ := ∫ g : Gauge, Fc g * D g ∂nu
  have hErr :=
    p4Q2JR_originalPhysicalGI_centeredTemporalCovariance_quadratic
      H b hb.le hsmall f e z
  intro hzero
  have hMoment :
      ‖b * t‖ ≤ ‖Fc‖ * (Err * b ^ 2) := by
    rw [hzero] at hErr
    simpa only [mul_zero, zero_sub, norm_neg] using hErr
  have hMoment' : b * |t| ≤ ‖Fc‖ * (Err * b ^ 2) := by
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos hb] using hMoment
  have hStrict := mul_lt_mul_of_pos_left hCorr hb
  dsimp [Fc, t] at hStrict hMoment'
  nlinarith [hStrict, hMoment']

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JR_originalPhysicalReceiverCentered_HaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JR_originalPhysicalReceiverCenter_testGap_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JR_originalPhysicalReceiverCentered_temporalCovariance_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JR_originalPhysicalGI_eq_centeredReceiverGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JR_originalPhysicalGI_centeredTemporalCovariance_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JR_originalPhysicalGI_zero_of_centeredReceiver_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JR_originalPhysicalGI_nonzero_of_centeredTemporalCorrelation

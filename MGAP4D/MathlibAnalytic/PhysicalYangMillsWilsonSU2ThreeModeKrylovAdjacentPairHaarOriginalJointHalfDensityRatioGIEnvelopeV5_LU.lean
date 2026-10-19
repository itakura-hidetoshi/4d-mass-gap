import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIEnvelopeControlledPhysicalCoercivityV5_LT
import Mathlib.Tactic

/-!
# P4-Q2-LU — genuine Wilson joint half-density single-link ratio detector bound

LS bounds original JH physical-GI detector by a *global* inverse joint
half-density sup norm. LT passes that bound into finite-H local coercivity.

Instead keep the original true Perron joint half-density at the actual
context z in the same integral as its reciprocal at the right-link update:
  R(e,z,g) = s(z) / s(z.left, update z.right e g).
This exact one-link ratio uses the original interacting Wilson joint law,
not an independently resampled Haar posterior or a modified density.

The original JH fiber kernel with scalar s(z) attached is bounded by
  ||s(z) • fiberKernel|| <= ||R(e,z,.)||_∞ * (exp(16b)-exp(-16b)).
The original JH Riesz, Bochner, and Haar-L² estimates then imply
  ||GI(e,z)|| <= ||T||⁻¹ * ||R(e,z,.)||_∞ * contrast.
Since ||R||∞ <= |s(z)| * ||s⁻¹||∞, this new local ratio envelope is
no larger than LS's global inverse-density envelope.

Combining with the genuine LR/Frobenius/LP local plaquette detector:
  κ_p >= Δ_total² / [5 N_H² (B(e,z)² + B(e',z')²)],
with B the true ratio envelope; strict denominator positivity follows
from the original nonzero local GI determinant and is not an assumption.

This improves the *finite-volume* bound, but does not prove ||R||∞ or
||T||⁻¹ bounded uniformly in H; global GI minor and N_H also remain
volume-dependent. H1-C3 and the continuum Yang-Mills mass gap stay open.

No invented physical source, synthetic rank, Dobrushin, sorry/admit,
replacement posterior, or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "delta" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
local notation "G" => p4Q2JH_originalGIResponseCLM H b hb
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- The literal ORIGINAL physical joint half-density ratio under one
right spatial link update at a fixed *original* left-right context.
Unlike LS's global inverse-density supremum, only the actual SU(2)
link fiber is varied here. -/
noncomputable def p4Q2LU_originalJointHalfDensityUpdateRatio
    (e : Link) (z : Cfg × Cfg) : C(Gauge, ℝ) :=
  ⟨fun g => s z * (s (z.1, Function.update z.2 e g))⁻¹, by
    have hu : Continuous (fun g : Gauge => Function.update z.2 e g) := by
      fun_prop
    have hpair : Continuous (fun g : Gauge =>
        (z.1, Function.update z.2 e g)) :=
      continuous_const.prodMk hu
    exact continuous_const.mul
      ((p4Q2JH_originalInverseJointSqrt_continuous H b hb).comp hpair)⟩

theorem p4Q2LU_originalJointHalfDensityUpdateRatio_apply
    (e : Link) (z : Cfg × Cfg) (g : Gauge) :
    p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z g =
      s z / s (z.1, Function.update z.2 e g) := by
  simp only [p4Q2LU_originalJointHalfDensityUpdateRatio, div_eq_mul_inv]

/-- The genuine one-link density-ratio envelope is *never larger*
than LS's global pointwise inverse-half-density envelope. -/
theorem p4Q2LU_originalJointHalfDensityRatio_norm_le_global
    (e : Link) (z : Cfg × Cfg) :
    ‖p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z‖ ≤
      |s z| * ‖p4Q2LS_originalInverseJointSqrtContinuous H b hb‖ := by
  let R : C(Gauge, ℝ) := p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z
  let w : C(Cfg × Cfg, ℝ) := p4Q2LS_originalInverseJointSqrtContinuous H b hb
  change ‖R‖ ≤ |s z| * ‖w‖
  apply (ContinuousMap.norm_le R (mul_nonneg (abs_nonneg _) (norm_nonneg w))).2
  intro g
  have hInv :
      |(s (z.1, Function.update z.2 e g))⁻¹| ≤ ‖w‖ := by
    simpa only [Real.norm_eq_abs] using
      w.norm_coe_le_norm (z.1, Function.update z.2 e g)
  change ‖s z * (s (z.1, Function.update z.2 e g))⁻¹‖ ≤ |s z| * ‖w‖
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hInv (abs_nonneg _)

/-- The *scaled* exact original Wilson fiber kernel has its JH
context half-density factor s(z) cancelled against the original
joint reciprocal at the perturbed right-link context, pointwise
BEFORE taking a supremum. No independence of Wilson posteriors is used. -/
theorem p4Q2LU_originalScaledFiberKernel_norm_le_ratioContrast
    (e : Link) (z : Cfg × Cfg) :
    ‖(s z) • p4Q2JH_originalFiberKernel H b hb e z‖ ≤
      ‖p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z‖ *
        p4Q2LS_originalPosteriorContrastEnvelope b := by
  let R : C(Gauge, ℝ) := p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z
  let E : ℝ := p4Q2LS_originalPosteriorContrastEnvelope b
  let k : C(Gauge × Cfg, ℝ) := p4Q2JH_originalFiberKernel H b hb e z
  have hE : 0 ≤ E := p4Q2LS_originalPosteriorContrastEnvelope_nonneg b hb
  change ‖(s z) • k‖ ≤ ‖R‖ * E
  apply (ContinuousMap.norm_le ((s z) • k)
    (mul_nonneg (norm_nonneg R) hE)).2
  rintro ⟨g, A⟩
  have hK : |K A (Function.update z.2 e g)| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H 2 (by norm_num) b hb A (Function.update z.2 e g)
  have hR : |s z * (s (z.1, Function.update z.2 e g))⁻¹| ≤ ‖R‖ := by
    simpa only [Real.norm_eq_abs] using R.norm_coe_le_norm g
  have hd : |delta z.2 e g| ≤ E :=
    p4Q2JL_originalPosteriorContrast_abs_le H b hb z.2 e g
  have hstep :
      |K A (Function.update z.2 e g)| *
          |s z * (s (z.1, Function.update z.2 e g))⁻¹| ≤ ‖R‖ := by
    calc
      _ ≤ 1 * ‖R‖ := mul_le_mul hK hR (abs_nonneg _) (by norm_num)
      _ = ‖R‖ := one_mul _
  change ‖s z * (K A (Function.update z.2 e g) *
      (s (z.1, Function.update z.2 e g))⁻¹ * delta z.2 e g)‖ ≤ ‖R‖ * E
  have hRearrange :
      s z * (K A (Function.update z.2 e g) *
        (s (z.1, Function.update z.2 e g))⁻¹ * delta z.2 e g) =
      K A (Function.update z.2 e g) *
        (s z * (s (z.1, Function.update z.2 e g))⁻¹) * delta z.2 e g := by
    ring
  rw [hRearrange, Real.norm_eq_abs, abs_mul, abs_mul]
  exact (mul_le_mul_of_nonneg_right hstep (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hd (norm_nonneg R))

/-- The local SU(2) right-link ratio replaces LS's GLOBAL inverse
joint density norm in the genuine JH Hilbert functional norm bound. -/
theorem p4Q2LU_originalGIResponse_norm_le_ratioEnvelope
    (e : Link) (z : Cfg × Cfg) :
    ‖G e z‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖⁻¹ *
        (‖p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z‖ *
          p4Q2LS_originalPosteriorContrastEnvelope b) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb
  let r := p4Q2JH_originalFiberRepresenter H b hb e z
  let k := p4Q2JH_originalFiberKernel H b hb e z
  let R := p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z
  let E := p4Q2LS_originalPosteriorContrastEnvelope b
  have hLp : ‖L r‖ ≤ ‖r‖ :=
    p4Q2LS_originalFiberRepresenter_toLp_norm_le H b hb e z
  have hr : ‖r‖ ≤ ‖k‖ :=
    p4Q2LS_originalFiberRepresenter_norm_le_kernel H b hb e z
  have hk : ‖(s z) • k‖ ≤ ‖R‖ * E :=
    p4Q2LU_originalScaledFiberKernel_norm_le_ratioContrast H b hb e z
  have hfac : 0 ≤ ‖T‖⁻¹ * |s z| :=
    mul_nonneg (inv_nonneg.mpr (norm_nonneg T)) (abs_nonneg _)
  have hT : 0 ≤ ‖T‖⁻¹ := inv_nonneg.mpr (norm_nonneg T)
  rw [p4Q2LS_originalGIResponseCLM_norm_eq_Riesz H b hb e z]
  calc
    (‖T‖⁻¹ * |s z|) * ‖L r‖ ≤
        (‖T‖⁻¹ * |s z|) * ‖k‖ :=
      mul_le_mul_of_nonneg_left (hLp.trans hr) hfac
    _ = ‖T‖⁻¹ * ‖(s z) • k‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      ring
    _ ≤ ‖T‖⁻¹ * (‖R‖ * E) :=
      mul_le_mul_of_nonneg_left hk hT

/-- A pointwise true Wilson envelope on the actual single SU(2) fiber,
with its genuine transfer-normalization factor retained exactly. -/
noncomputable def p4Q2LU_originalGIContextRatioEnvelope
    (e : Link) (z : Cfg × Cfg) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb‖⁻¹ *
    (‖p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z‖ *
      p4Q2LS_originalPosteriorContrastEnvelope b)

local notation "B" => p4Q2LU_originalGIContextRatioEnvelope H b hb

theorem p4Q2LU_originalGIResponse_norm_le_contextRatioEnvelope
    (e : Link) (z : Cfg × Cfg) :
    ‖G e z‖ ≤ B e z :=
  p4Q2LU_originalGIResponse_norm_le_ratioEnvelope H b hb e z

theorem p4Q2LU_originalGIContextRatioEnvelope_nonneg
    (e : Link) (z : Cfg × Cfg) :
    0 ≤ B e z :=
  (norm_nonneg (G e z)).trans
    (p4Q2LU_originalGIResponse_norm_le_contextRatioEnvelope H b hb e z)

/-- LU is actually an improvement, not merely an alternative form:
the true one-link ratio bound is at most LT's LS-derived envelope,
with NO global-density normalizer added or assumed. -/
theorem p4Q2LU_originalGIContextRatioEnvelope_le_LT
    (e : Link) (z : Cfg × Cfg) :
    B e z ≤ p4Q2LT_originalGIContextEnvelope H b hb z := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb
  let R := p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z
  let w := p4Q2LS_originalInverseJointSqrtContinuous H b hb
  let E := p4Q2LS_originalPosteriorContrastEnvelope b
  have hR : ‖R‖ ≤ |s z| * ‖w‖ :=
    p4Q2LU_originalJointHalfDensityRatio_norm_le_global H b hb e z
  have hE : 0 ≤ E := p4Q2LS_originalPosteriorContrastEnvelope_nonneg b hb
  have hT : 0 ≤ ‖T‖⁻¹ := inv_nonneg.mpr (norm_nonneg T)
  change ‖T‖⁻¹ * (‖R‖ * E) ≤ (‖T‖⁻¹ * |s z|) * (‖w‖ * E)
  calc
    ‖T‖⁻¹ * (‖R‖ * E) ≤ ‖T‖⁻¹ * ((|s z| * ‖w‖) * E) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hR hE) hT
    _ = (‖T‖⁻¹ * |s z|) * (‖w‖ * E) := by ring

/-- Pairwise genuine JH operator norm is controlled by the squared
single-link ratios instead of a whole joint-volume inverse supremum. -/
theorem p4Q2LU_originalGIOpNormSq_sum_le_ratioEnvelopeSq_sum
    (e e' : Link) (z z' : Cfg × Cfg) :
    5 * (‖G e z‖^2 + ‖G e' z'‖^2) ≤
      5 * ((B e z)^2 + (B e' z')^2) := by
  have h1 := p4Q2LU_originalGIResponse_norm_le_contextRatioEnvelope H b hb e z
  have h2 := p4Q2LU_originalGIResponse_norm_le_contextRatioEnvelope H b hb e' z'
  have h1pos := p4Q2LU_originalGIContextRatioEnvelope_nonneg H b hb e z
  have h2pos := p4Q2LU_originalGIContextRatioEnvelope_nonneg H b hb e' z'
  have hs1 : ‖G e z‖^2 ≤ (B e z)^2 := by
    have hp : 0 ≤ (B e z - ‖G e z‖) * (B e z + ‖G e z‖) :=
      mul_nonneg (sub_nonneg.mpr h1)
        (add_nonneg h1pos (norm_nonneg _))
    nlinarith [hp]
  have hs2 : ‖G e' z'‖^2 ≤ (B e' z')^2 := by
    have hp : 0 ≤ (B e' z' - ‖G e' z'‖) * (B e' z' + ‖G e' z'‖) :=
      mul_nonneg (sub_nonneg.mpr h2)
        (add_nonneg h2pos (norm_nonneg _))
    nlinarith [hp]
  linarith

/-- Positivity is forced by a nonzero original GI minor; no artificial
positivity hypothesis for the one-link half-density ratio is added. -/
theorem p4Q2LU_originalGI_ratioEnvelopeSq_sum_pos_of_local_minor
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0) :
    0 < 5 * ((B e z)^2 + (B e' z')^2) := by
  exact (p4Q2LR_originalGI_opNormSq_sum_pos_of_local_minor
    H b hb e e' z z' p hminor).trans_le
      (p4Q2LU_originalGIOpNormSq_sum_le_ratioEnvelopeSq_sum
        H b hb e e' z z')

/-- Original local physical GI coercivity: the genuine one-link ratio
replaces the LS global inverse half-density estimate in the denominator.
All geometric witnesses and coefficient are original LP/LO objects. -/
theorem p4Q2LU_originalLocalGI_coercivity_ge_global_ratioEnvelope_floor
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0)
    (hcount : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ))
    (hAvg : |p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'| /
        (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ≤
      |p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p|) :
    (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
      ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
        (5 * ((B e z)^2 + (B e' z')^2))) ≤
      p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb e e' z z' p := by
  let total := p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'
  let n : ℝ := (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
  let C : ℝ := 5 * (‖G e z‖^2 + ‖G e' z'‖^2)
  let D : ℝ := 5 * ((B e z)^2 + (B e' z')^2)
  have hC : 0 < C :=
    p4Q2LR_originalGI_opNormSq_sum_pos_of_local_minor
      H b hb e e' z z' p hminor
  have hCD : C ≤ D :=
    p4Q2LU_originalGIOpNormSq_sum_le_ratioEnvelopeSq_sum H b hb e e' z z'
  have hD : 0 < D := lt_of_lt_of_le hC hCD
  have hn2 : 0 < n^2 := sq_pos_of_pos hcount
  have hCden : 0 < n^2 * C := mul_pos hn2 hC
  have hDden : 0 < n^2 * D := mul_pos hn2 hD
  have hden : n^2 * C ≤ n^2 * D :=
    mul_le_mul_of_nonneg_left hCD (sq_nonneg n)
  have hDiv : total^2 / (n^2 * D) ≤ total^2 / (n^2 * C) :=
    (div_le_div_iff₀ hDden hCden).2
      (mul_le_mul_of_nonneg_left hden (sq_nonneg total))
  have hLR :=
    p4Q2LR_originalLocalGI_coercivity_ge_global_opNorm_floor
      H b hb e e' z z' p hminor hcount hAvg
  exact hDiv.trans hLR

/-- Genuine finite-volume LP witness and physical local coercivity with
the strictly positive new one-link ratio denominator. No H-uniform
coercivity, strong-limit closure, or mass gap is asserted. -/
theorem p4Q2LU_originalPhysicalLocalGI_exists_ratioEnvelope_floor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ∧
      0 < 5 * ((B e z)^2 + (B e' z')^2) ∧
      0 < p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb e e' z z' p ∧
      (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
        ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
          (5 * ((B e z)^2 + (B e' z')^2))) ≤
        p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb e e' z z' p ∧
      ∀ x y : ℝ,
        p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hpPos, hAvg⟩ :=
    p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
      H b hpos e e' left₀ right₀
  have hlocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0 := by
    intro hz
    simp [hz] at hpPos
  have hBpos :=
    p4Q2LU_originalGI_ratioEnvelopeSq_sum_pos_of_local_minor
      H b hb e e' z z' p hlocal
  obtain ⟨hκ, hBound⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hlocal
  have hFloor :=
    p4Q2LU_originalLocalGI_coercivity_ge_global_ratioEnvelope_floor
      H b hb e e' z z' p hlocal hn hAvg
  exact ⟨z, z', p, hp, hn, hBpos, hκ, hFloor, hBound⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalJointHalfDensityUpdateRatio_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalJointHalfDensityRatio_norm_le_global
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalScaledFiberKernel_norm_le_ratioContrast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalGIResponse_norm_le_ratioEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalGIResponse_norm_le_contextRatioEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalGIContextRatioEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalGIContextRatioEnvelope_le_LT
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalGIOpNormSq_sum_le_ratioEnvelopeSq_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalGI_ratioEnvelopeSq_sum_pos_of_local_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalLocalGI_coercivity_ge_global_ratioEnvelope_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LU_originalPhysicalLocalGI_exists_ratioEnvelope_floor

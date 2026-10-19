import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalGIResponseOperatorNormBoundV5_LR
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorWeakFrozenNoGoV5_JL
import Mathlib.Tactic

/-!
# P4-Q2-LS — genuine Wilson GI detector norm: original kernel/posterior envelope

LR bounds the physical two-context GI Frobenius denominator by the
squared operator norms of the ACTUAL interacting-Wilson JH detectors.

This file now bounds the JH detector's real Hilbert operator norm by
THE ORIGINAL one-slab Wilson kernel, ORIGINAL inverse joint
half-density, and ORIGINAL two interacting-posterior density contrast.

The genuine complete one-slab Wilson kernel obeys |K| <= 1 at b >= 0.
JL proves the original two conditional Wilson posterior density
contrast |delta| <= exp(16b) - exp(-16b), independent of H, physical
link or boundary. We do not replace either interacting posterior by
independent Haar. Original compact Haar measures enter only as exact
reference measures in JH's proven integral/Riesz representation.

Quantitative chain:
  ||JH_G|| = ||T||^-1 * |s(z)| * ||toLp (JH_original_representer)||,
  ||toLp representer|| <= ||representer|| <= ||original_kernel||,
  ||original_kernel|| <=
     ||original_inverse_joint_half_density|| *
       (exp(16b)-exp(-16b)).
Thus the only remaining context/volume-dependent quantities are the
genuine physical transfer normalization and true inverse joint density.

No uniform-in-H coercivity, H1-C3, continuum Yang–Mills or mass gap is
asserted. No fake rank, Dobrushin, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "delta" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "G" => p4Q2JH_originalGIResponseCLM H b hb

/-- The ORIGINAL inverse joint physical Wilson half-density, realized
as a bounded continuous function on the ACTUAL compact two-slice space. -/
noncomputable def p4Q2LS_originalInverseJointSqrtContinuous : C(Cfg × Cfg, ℝ) :=
  ⟨fun z => (s z)⁻¹, p4Q2JH_originalInverseJointSqrt_continuous H b hb⟩

@[simp] theorem p4Q2LS_originalInverseJointSqrtContinuous_apply
    (z : Cfg × Cfg) :
    p4Q2LS_originalInverseJointSqrtContinuous H b hb z = (s z)⁻¹ := rfl

/-- The JL-proved genuinely volume-uniform contrast envelope for
TWO ACTUAL interacting Wilson conditional posterior density rows. -/
noncomputable def p4Q2LS_originalPosteriorContrastEnvelope : ℝ :=
  Real.exp (16 * b) - Real.exp (-16 * b)

theorem p4Q2LS_originalPosteriorContrastEnvelope_nonneg :
    0 ≤ p4Q2LS_originalPosteriorContrastEnvelope b := by
  unfold p4Q2LS_originalPosteriorContrastEnvelope
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith [hb]

/-- Original finite-H kernel control: the complete original one-slab
Wilson factor is at most ONE in absolute value, the actual inverse
physical half-density has the actual C(slices x slices) norm, and
JL's ORIGINAL interacting two-posterior contrast has explicit
volume-independent envelope. -/
theorem p4Q2LS_originalFiberKernel_norm_le_inverseDensity_mul_contrast
    (e : Link) (z : Cfg × Cfg) :
    ‖p4Q2JH_originalFiberKernel H b hb e z‖ ≤
      ‖p4Q2LS_originalInverseJointSqrtContinuous H b hb‖ *
        p4Q2LS_originalPosteriorContrastEnvelope b := by
  let w : C(Cfg × Cfg, ℝ) := p4Q2LS_originalInverseJointSqrtContinuous H b hb
  let E : ℝ := p4Q2LS_originalPosteriorContrastEnvelope b
  let k : C(Gauge × Cfg, ℝ) := p4Q2JH_originalFiberKernel H b hb e z
  have hE : 0 ≤ E := p4Q2LS_originalPosteriorContrastEnvelope_nonneg b hb
  change ‖k‖ ≤ ‖w‖ * E
  apply (ContinuousMap.norm_le (mul_nonneg (norm_nonneg w) hE)).2
  rintro ⟨g, A⟩
  have hK : |K A (Function.update z.2 e g)| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H 2 (by norm_num) b hb A (Function.update z.2 e g)
  have hw : |(s (z.1, Function.update z.2 e g))⁻¹| ≤ ‖w‖ := by
    simpa only [Real.norm_eq_abs] using
      w.norm_coe_le_norm (z.1, Function.update z.2 e g)
  have hd : |delta z.2 e g| ≤ E :=
    p4Q2JL_originalPosteriorContrast_abs_le H b hb z.2 e g
  have hstep :
      |K A (Function.update z.2 e g)| *
          |(s (z.1, Function.update z.2 e g))⁻¹| ≤ ‖w‖ := by
    calc
      _ ≤ 1 * ‖w‖ := mul_le_mul hK hw (abs_nonneg _) (by norm_num)
      _ = ‖w‖ := one_mul _
  change ‖K A (Function.update z.2 e g) *
      (s (z.1, Function.update z.2 e g))⁻¹ *
      delta z.2 e g‖ ≤ ‖w‖ * E
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact (mul_le_mul_of_nonneg_right hstep (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hd (norm_nonneg _))

/-- Exact JH Bochner-integrated ORIGINAL fiber representer has
supremum norm at most the genuine complete original Wilson kernel
norm on Gauge × all spatial configurations. -/
theorem p4Q2LS_originalFiberRepresenter_norm_le_kernel
    (e : Link) (z : Cfg × Cfg) :
    ‖p4Q2JH_originalFiberRepresenter H b hb e z‖ ≤
      ‖p4Q2JH_originalFiberKernel H b hb e z‖ := by
  let k : C(Gauge × Cfg, ℝ) := p4Q2JH_originalFiberKernel H b hb e z
  let r : C(Cfg, ℝ) := p4Q2JH_originalFiberRepresenter H b hb e z
  change ‖r‖ ≤ ‖k‖
  apply (ContinuousMap.norm_le (norm_nonneg k)).2
  intro A
  have hInt :
      ‖∫ g : Gauge, k (g,A) ∂nu‖ ≤
        ‖k‖ * (nu.real Set.univ) := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards with g
    exact k.norm_coe_le_norm (g,A)
  have hmu : nu.real Set.univ = 1 := by
    simp [measureReal_def]
  rw [p4Q2JH_originalFiberRepresenter_apply H b hb e z A]
  simpa only [hmu, mul_one] using hInt

/-- Reference Haar-L² norm of the EXACT physical representer is
bounded by its continuous sup norm. This uses the true normalized
product spatial Haar probability measure, not a new posterior law. -/
theorem p4Q2LS_originalFiberRepresenter_toLp_norm_le
    (e : Link) (z : Cfg × Cfg) :
    ‖L (p4Q2JH_originalFiberRepresenter H b hb e z)‖ ≤
      ‖p4Q2JH_originalFiberRepresenter H b hb e z‖ := by
  let r : C(Cfg, ℝ) := p4Q2JH_originalFiberRepresenter H b hb e z
  have hL : ‖L‖ ≤ 1 := by
    simpa [measureUnivNNReal] using
      (ContinuousMap.toLp_norm_le (p := (2 : ENNReal)) (𝕜 := ℝ) haar)
  calc
    ‖L r‖ ≤ ‖L‖ * ‖r‖ := L.le_opNorm _
    _ ≤ 1 * ‖r‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg r)
    _ = ‖r‖ := one_mul _

/-- JH's ACTUAL frozen GI bounded-linear-map norm equals the
true transfer-norm inverse, actual joint half-density and the norm
of its exact interacting-Wilson fiber Riesz representer. -/
theorem p4Q2LS_originalGIResponseCLM_norm_eq_Riesz
    (e : Link) (z : Cfg × Cfg) :
    ‖G e z‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖⁻¹ * |s z| *
          ‖L (p4Q2JH_originalFiberRepresenter H b hb e z)‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb
  let r := p4Q2JH_originalFiberRepresenter H b hb e z
  change ‖(-‖T‖⁻¹ * s z) • (innerSL ℝ (L r))‖ = _
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  simp only [abs_mul, abs_neg, abs_inv, abs_of_nonneg (norm_nonneg T)]

/-- Authentic original Wilson two-posterior JH detector norm is bounded
by transfer normalization, its true context joint half-density,
the compact original inverse density sup norm, and JL's uniform
original conditional posterior contrast envelope. -/
theorem p4Q2LS_originalGIResponseCLM_norm_le_originalEnvelope
    (e : Link) (z : Cfg × Cfg) :
    ‖G e z‖ ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖⁻¹ * |s z|) *
      (‖p4Q2LS_originalInverseJointSqrtContinuous H b hb‖ *
        p4Q2LS_originalPosteriorContrastEnvelope b) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb
  let r := p4Q2JH_originalFiberRepresenter H b hb e z
  let k := p4Q2JH_originalFiberKernel H b hb e z
  let w := p4Q2LS_originalInverseJointSqrtContinuous H b hb
  let E := p4Q2LS_originalPosteriorContrastEnvelope b
  have hLp : ‖L r‖ ≤ ‖r‖ :=
    p4Q2LS_originalFiberRepresenter_toLp_norm_le H b hb e z
  have hr : ‖r‖ ≤ ‖k‖ :=
    p4Q2LS_originalFiberRepresenter_norm_le_kernel H b hb e z
  have hk : ‖k‖ ≤ ‖w‖ * E :=
    p4Q2LS_originalFiberKernel_norm_le_inverseDensity_mul_contrast
      H b hb e z
  have hfac : 0 ≤ ‖T‖⁻¹ * |s z| :=
    mul_nonneg (inv_nonneg.mpr (norm_nonneg T)) (abs_nonneg _)
  rw [p4Q2LS_originalGIResponseCLM_norm_eq_Riesz H b hb e z]
  calc
    (‖T‖⁻¹ * |s z|) * ‖L r‖ ≤
        (‖T‖⁻¹ * |s z|) * ‖r‖ :=
          mul_le_mul_of_nonneg_left hLp hfac
    _ ≤ (‖T‖⁻¹ * |s z|) * ‖k‖ :=
      mul_le_mul_of_nonneg_left hr hfac
    _ ≤ (‖T‖⁻¹ * |s z|) * (‖w‖ * E) :=
      mul_le_mul_of_nonneg_left hk hfac

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LS_originalPosteriorContrastEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LS_originalFiberKernel_norm_le_inverseDensity_mul_contrast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LS_originalFiberRepresenter_norm_le_kernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LS_originalFiberRepresenter_toLp_norm_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LS_originalGIResponseCLM_norm_eq_Riesz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LS_originalGIResponseCLM_norm_le_originalEnvelope
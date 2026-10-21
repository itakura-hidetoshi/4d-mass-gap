import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedScoreOneLinkHaarMinorizationV5_NC
import Mathlib.Tactic

/-!
# P4-Q2-ND — authentic two-posterior signed Haar L1 mass and cancellation frontier

GA's genuine two ORIGINAL interacting Wilson conditional posterior rows are
L2 separated by an explicit SU(2) Haar estimate at positive beta.
However, NC's ACTUAL signed physical receiver score is a further
integral transform of the row difference, with genuine Wilson
one-link factor and Perron half-density; row separation alone
does NOT ensure nonconstant receiver score or nonzero GI covariance.

ND first proves that both exact original conditional density rows
integrate to one by the pinned continuousNormalizedExp construction.
The original signed density contrast D therefore has ZERO Haar
mean. GA's strictly positive L2 lower bound and JL's pointwise
upper envelope then yield a positive VOLUME-UNIFORM signed Haar
L1 lower bound:

    exp(-32*b) * b² * V_temporal ≤
      (exp(16*b)-exp(-16*b)) * ∫ |D| dHaar.

In particular both positive and negative genuine signed lobes are
present on the ACTUAL compact SU(2) group at every beta > 0,
every finite H, every original source link and right environment.
No independent-Haar posterior is introduced.

The original signed fiber integrand used in MQ is the product of the
genuine local positive Wilson factor, strictly positive reciprocal
of the Perron joint half-density, and the SAME D. Thus BOTH signs
persist POINTWISE through this exact integrand before Haar
integration. Their possible cancellation AFTER integration is the
remaining obstruction to NC's positive receiver score Haar variance.

Nothing in this module postulates a nonzero receiver moment or
extra Hilbert detection direction. H1-C3, strong limit and continuum
4D Yang–Mills mass gap remain OPEN. No Dobrushin, artificial
posterior/detector, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2ND_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2ND_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2ND_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2ND_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2ND_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2ND_openPosHaar :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint
section GenuinePosteriorRow
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "D" =>
  p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
local notation "row" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) b hb
include hb

/-- Each ORIGINAL interacting-Wilson one-link posterior density row,
without replacing its authentic left/right boundary or weights,
has SU(2)-Haar mass exactly one. -/
theorem p4Q2ND_originalPosteriorRow_haar_integral_one
    (left right : Cfg) (e : Link) :
    (∫ g : Gauge, row left right e g ∂mu) = 1 := by
  let W : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) b hb left right e
  have hW : Continuous W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) b hb left right e
  have hZ : 0 < continuousExpPartition mu W :=
    continuousExpPartition_pos mu W hW
  change (∫ g : Gauge, Real.exp (W g) / continuousExpPartition mu W ∂mu) = 1
  rw [integral_div]
  change continuousExpPartition mu W / continuousExpPartition mu W = 1
  exact div_self hZ.ne'

/-- Continuity of the exact physical signed row difference on the
actual compact SU(2) group. -/
theorem p4Q2ND_originalPosteriorContrast_continuous
    (right : Cfg) (e : Link) :
    Continuous (D right e) := by
  have h0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
      H 2 (by norm_num) b hb (originalWilsonExplicitIdentityBoundary H) right e
  have h1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
      H 2 (by norm_num) b hb (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  change Continuous (fun g : Gauge => row (originalWilsonExplicitIdentityBoundary H) right e g -
    row (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g)
  exact h0.sub h1

/-- Both ORIGINAL interacting posterior density rows have mass one,
so their genuinely signed difference has exactly ZERO SU(2) Haar mean. -/
theorem p4Q2ND_originalPosteriorContrast_Haar_integral_zero
    (right : Cfg) (e : Link) :
    (∫ g : Gauge, D right e g ∂mu) = 0 := by
  let f₀ : Gauge → ℝ :=
    row (originalWilsonExplicitIdentityBoundary H) right e
  let f₁ : Gauge → ℝ :=
    row (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  have h₀ : Continuous f₀ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
      H 2 (by norm_num) b hb (originalWilsonExplicitIdentityBoundary H) right e
  have h₁ : Continuous f₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
      H 2 (by norm_num) b hb (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  have hi₀ : Integrable f₀ mu :=
    h₀.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi₁ : Integrable f₁ mu :=
    h₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ g : Gauge, f₀ g - f₁ g ∂mu) = 0
  rw [integral_sub hi₀ hi₁,
    p4Q2ND_originalPosteriorRow_haar_integral_one H b hb
      (originalWilsonExplicitIdentityBoundary H) right e,
    p4Q2ND_originalPosteriorRow_haar_integral_one H b hb
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e]
  ring

/-- GA's lower bound implies the ACTUAL signed posterior row
difference is nonzero at a genuine point of SU(2) whenever b>0. -/
theorem p4Q2ND_originalPosteriorContrast_nonzero_witness
    (bpos : 0 < b) (right : Cfg) (e : Link) :
    ∃ g : Gauge, D right e g ≠ 0 := by
  have hGa :=
    p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_pos
      H b bpos right e
  have hPos : 0 < ∫ g : Gauge, (D right e g)^2 ∂mu := by
    exact lt_of_lt_of_le hGa.1 hGa.2
  by_contra hNone
  have hZero : ∀ g : Gauge, D right e g = 0 := by
    intro g
    by_contra hg
    exact hNone ⟨g, hg⟩
  have hIntZero : (∫ g : Gauge, (D right e g)^2 ∂mu) = 0 := by
    simp [hZero]
  rw [hIntZero] at hPos
  exact (lt_irrefl (0 : ℝ)) hPos

/-- A VOLUME-UNIFORM quantitative Haar-L1 signed mass certificate
for BOTH actual interacting-Wilson posterior density rows.
The true signed D is retained; Haar is only its reference integration
carrier, never a replacement posterior. -/
theorem p4Q2ND_originalPosteriorContrast_HaarL1_uniform_lower
    (right : Cfg) (e : Link) :
    Real.exp (-32*b) *
        (b^2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ≤
      (Real.exp (16*b) - Real.exp (-16*b)) *
        (∫ g : Gauge, |D right e g| ∂mu) := by
  let C : ℝ := Real.exp (16*b) - Real.exp (-16*b)
  have hD : Continuous (D right e) :=
    p4Q2ND_originalPosteriorContrast_continuous H b hb right e
  have hSqInt : Integrable (fun g : Gauge => (D right e g)^2) mu :=
    (hD.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAbsInt : Integrable (fun g : Gauge => |D right e g|) mu :=
    hD.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (g : Gauge) :
      (D right e g)^2 ≤ C * |D right e g| := by
    have hBd :=
      p4Q2JL_originalPosteriorContrast_abs_le H b hb right e g
    change |D right e g| ≤ C at hBd
    calc
      (D right e g)^2 = |D right e g| * |D right e g| := by
        rw [← sq_abs, pow_two]
      _ ≤ C * |D right e g| :=
        mul_le_mul_of_nonneg_right hBd (abs_nonneg _)
  have hIntegral :
      (∫ g : Gauge, (D right e g)^2 ∂mu) ≤
        C * (∫ g : Gauge, |D right e g| ∂mu) := by
    calc
      (∫ g : Gauge, (D right e g)^2 ∂mu) ≤
          ∫ g : Gauge, C * |D right e g| ∂mu :=
        integral_mono hSqInt (hAbsInt.const_mul C) hPoint
      _ = C * (∫ g : Gauge, |D right e g| ∂mu) :=
        integral_const_mul _ _
  exact le_trans
    (p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_lower
      H b hb right e)
    hIntegral

/-- At EVERY genuine positive beta, the two normalized interacting
posterior rows cross: the true signed difference has both positive
and negative values on the real compact SU(2) Haar group.
This is stronger than merely being nonzero pointwise. -/
theorem p4Q2ND_originalPosteriorContrast_has_both_signs
    (bpos : 0 < b) (right : Cfg) (e : Link) :
    (∃ g : Gauge, 0 < D right e g) ∧
      (∃ h : Gauge, D right e h < 0) := by
  obtain ⟨g₀, hg₀⟩ :=
    p4Q2ND_originalPosteriorContrast_nonzero_witness H b hb bpos right e
  have hD : Continuous (D right e) :=
    p4Q2ND_originalPosteriorContrast_continuous H b hb right e
  have hInt : Integrable (D right e) mu :=
    hD.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZero :=
    p4Q2ND_originalPosteriorContrast_Haar_integral_zero H b hb right e
  constructor
  · by_contra hn
    have hNonpos : ∀ g : Gauge, D right e g ≤ 0 := by
      intro g
      exact le_of_not_gt (by
        intro hg
        exact hn ⟨g,hg⟩)
    have hNegIntPos : 0 < ∫ g : Gauge, -(D right e g) ∂mu :=
      integral_pos_of_integrable_nonneg_nonzero hD.neg hInt.neg
        (fun g => neg_nonneg.mpr (hNonpos g))
        (neg_ne_zero.mpr hg₀)
    have hNegIntZero : (∫ g : Gauge, -(D right e g) ∂mu) = 0 := by
      rw [integral_neg, hZero]
      simp
    rw [hNegIntZero] at hNegIntPos
    exact (lt_irrefl (0 : ℝ)) hNegIntPos
  · by_contra hn
    have hNonneg : ∀ g : Gauge, 0 ≤ D right e g := by
      intro g
      exact le_of_not_gt (by
        intro hg
        exact hn ⟨g,hg⟩)
    have hIntPos : 0 < ∫ g : Gauge, D right e g ∂mu :=
      integral_pos_of_integrable_nonneg_nonzero hD hInt hNonneg hg₀
    rw [hZero] at hIntPos
    exact (lt_irrefl (0 : ℝ)) hIntPos

end GenuinePosteriorRow

section TrueSignedFiber
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "D" =>
  p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
include hb

/-- The exact ORIGINAL MQ signed interacting-Wilson fiber integrand,
with both real posterior density rows and genuine Perron half-density. -/
noncomputable def p4Q2ND_originalSignedPhysicalFiberIntegrand
    (e : Link) (z : Cfg × Cfg) (A : Cfg) (g : Gauge) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H 2 b A z.2 e g *
    ((continuousJointSqrtDensity H 2 (by norm_num) b hb
        (z.1, Function.update z.2 e g))⁻¹ *
      D z.2 e g)

/-- The physical local signed receiver score is exactly the Haar
integral of this SAME genuine original interacting-posterior fiber.
No new receiver or probability law is constructed. -/
theorem p4Q2ND_originalSignedProfile_eq_integral_truePhysicalFiber
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    p4Q2MQ_originalSignedLocalFiberProfile H b hb e z A =
      ∫ g : Gauge,
        p4Q2ND_originalSignedPhysicalFiberIntegrand H b hb e z A g
          ∂normalizedCompactHaar Gauge := by
  rfl

/-- At positive beta, even after multiplication by the exact positive
one-link Wilson factor and genuine Perron half-density reciprocal,
the original physical signed fiber has BOTH signs for every fixed
source configuration A. Any cancellation can occur only AFTER the
Haar integral defining the actual receiver score. -/
theorem p4Q2ND_originalSignedPhysicalFiber_has_both_signs
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    (∃ g : Gauge,
      0 < p4Q2ND_originalSignedPhysicalFiberIntegrand H b hb e z A g) ∧
    (∃ h : Gauge,
      p4Q2ND_originalSignedPhysicalFiberIntegrand H b hb e z A h < 0) := by
  rcases p4Q2ND_originalPosteriorContrast_has_both_signs
    H b hb bpos z.2 e with ⟨⟨g,hg⟩,⟨h,hh⟩⟩
  refine ⟨⟨g, ?_⟩, ⟨h, ?_⟩⟩
  · change 0 <
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H 2 b A z.2 e g *
        ((continuousJointSqrtDensity H 2 (by norm_num) b hb
          (z.1, Function.update z.2 e g))⁻¹ * D z.2 e g)
    exact mul_pos
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H 2 b A z.2 e g)
      (mul_pos (inv_pos.mpr
        (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
          (z.1, Function.update z.2 e g))) hg)
  · change
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H 2 b A z.2 e h *
        ((continuousJointSqrtDensity H 2 (by norm_num) b hb
          (z.1, Function.update z.2 e h))⁻¹ * D z.2 e h) < 0
    exact mul_neg_of_pos_of_neg
      (mul_pos
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
          H 2 b A z.2 e h)
        (inv_pos.mpr
          (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
            (z.1, Function.update z.2 e h))))
      hh

end TrueSignedFiber
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ND_originalPosteriorRow_haar_integral_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ND_originalPosteriorContrast_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ND_originalPosteriorContrast_Haar_integral_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ND_originalPosteriorContrast_nonzero_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ND_originalPosteriorContrast_HaarL1_uniform_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ND_originalPosteriorContrast_has_both_signs
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ND_originalSignedProfile_eq_integral_truePhysicalFiber
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ND_originalSignedPhysicalFiber_has_both_signs

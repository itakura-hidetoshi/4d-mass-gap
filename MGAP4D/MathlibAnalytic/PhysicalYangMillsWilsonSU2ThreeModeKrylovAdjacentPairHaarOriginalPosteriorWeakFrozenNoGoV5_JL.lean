import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalStaticGISpatialKernelV5_JK
import Mathlib.Tactic

/-!
# P4-Q2-JL: actual interacting Wilson posterior zero-coupling no-go
  and volume-independent Haar-L2 weak-coupling envelope

The already proved FK theorem identifies EACH actual normalized one-link
interacting Wilson posterior at frozen beta=0 with density one relative
to the normalized compact SU(2) Haar reference. This implies the genuine
two-left-boundary posterior contrast vanishes, and thus the ENTIRE actual
JH fiber Riesz kernel, its vector, and its bounded original GI detector
vanish exactly at zero frozen coupling. Consequently the JI spatial
Wilson 2-context minor vanishes for every physical pair of contexts
at beta=0. In particular, the JK nonzero GI anchor CANNOT exist there.

For arbitrary beta>=0, retain BOTH ORIGINAL interacting posterior laws.
The true FK upper/lower conditional density bounds yield a uniform
pointwise bound on their signed contrast, and after legitimate integration
a uniform upper bound on the actual squared reference-Haar norm. Combining
with GA's TRUE SU(2) temporal crossing Haar variance yields an exact
two-sided inequality:

 beta^2 * exp(-32 beta) * V_SU2 <= ||p0_beta - p1_beta||^2_{Haar L2}
                                 <= (exp(16 beta)-exp(-16 beta))^2.

The bound is independent of spatial volume, link and physical right
environment; it does NOT claim GI sensitivity to the spatial Wilson
action, nor differentiability of the original interacting posterior in
beta, nor H1-C3 closure or a continuum mass-gap proof.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JL_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JL_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JL_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JL_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JL_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- The ACTUAL difference of two ORIGINAL interacting Wilson conditional
posterior densities is identically zero at frozen coupling beta=0. -/
theorem p4Q2JL_originalPosteriorContrast_zero
    (right : Cfg) (e : Link) (g : Gauge) :
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast
      H 0 (le_refl (0 : ℝ)) right e g = 0 := by
  unfold p4Q2GB_originalWilsonPosteriorLeftDensityContrast
  rw [p4Q2FK_originalWilsonPosteriorConditionalDensity_beta_zero
      H 2 (by norm_num) (originalWilsonExplicitIdentityBoundary H) right e g,
    p4Q2FK_originalWilsonPosteriorConditionalDensity_beta_zero
      H 2 (by norm_num) (p4Q2FQ_originalSU2LeftPiRotationAtLink H e)
      right e g]
  ring

/-- At the Haar decoupled frozen endpoint, JH's literal ORIGINAL fiber
kernel is the zero continuous function, for all actual SU(2) variables. -/
theorem p4Q2JL_originalFiberKernel_zero
    (e : Link) (z : Cfg × Cfg) :
    p4Q2JH_originalFiberKernel H 0 (le_refl (0 : ℝ)) e z = 0 := by
  ext p
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 0 p.2 (Function.update z.2 e p.1) *
      (continuousJointSqrtDensity H 2 (by norm_num) 0 (le_refl (0 : ℝ))
        (z.1, Function.update z.2 e p.1))⁻¹ *
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast
        H 0 (le_refl (0 : ℝ)) z.2 e p.1 = 0
  rw [p4Q2JL_originalPosteriorContrast_zero]
  ring

/-- Exact vanishing of the actual continuous spatial Riesz representer
after genuine SU(2) Haar integration of the zero original contrast. -/
theorem p4Q2JL_originalFiberRepresenter_zero
    (e : Link) (z : Cfg × Cfg) :
    p4Q2JH_originalFiberRepresenter H 0 (le_refl (0 : ℝ)) e z = 0 := by
  ext A
  rw [p4Q2JH_originalFiberRepresenter_apply,
    p4Q2JL_originalFiberKernel_zero H e z]
  simp

/-- At frozen beta=0 the complete ORIGINAL Wilson interacting GI
functional is literally the ZERO bounded map on the full Haar-L2 space,
not merely zero on the constant unit. -/
theorem p4Q2JL_originalGIResponseCLM_zero
    (e : Link) (z : Cfg × Cfg) :
    p4Q2JH_originalGIResponseCLM H 0 (le_refl (0 : ℝ)) e z = 0 := by
  ext v
  change
    (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) 0 (le_refl (0 : ℝ))‖⁻¹ *
      continuousJointSqrtDensity H 2 (by norm_num) 0 (le_refl (0 : ℝ)) z) *
      inner ℝ
        (L (p4Q2JH_originalFiberRepresenter H 0 (le_refl (0 : ℝ)) e z)) v = 0
  rw [p4Q2JL_originalFiberRepresenter_zero H e z]
  simp

/-- The genuine original 2-context spatial Wilson GI determinant
vanishes for EVERY physical pair of contexts at beta=0, with NO
positivity/anchor assumptions. This is an exact frozen endpoint no-go. -/
theorem p4Q2JL_originalGISpatialMinor_zero_at_frozen_zero
    (e e' : Link) (z z' : Cfg × Cfg) :
    p4Q2JI_originalGISpatialActionMinor H 0 (le_refl (0 : ℝ))
      e e' z z' = 0 := by
  unfold p4Q2JI_originalGISpatialActionMinor
  rw [p4Q2JL_originalGIResponseCLM_zero H e z,
    p4Q2JL_originalGIResponseCLM_zero H e' z']
  simp

/-- A genuine JK GI constant-unit anchor is IMPOSSIBLE at frozen
beta=0, even though the original spatial Wilson vector is nonzero. -/
theorem p4Q2JL_originalGIAnchor_zero_at_frozen_zero
    (e : Link) (z : Cfg × Cfg) :
    p4Q2JH_originalGIResponseCLM H 0 (le_refl (0 : ℝ)) e z
      (L (1 : C(Cfg, ℝ))) = 0 := by
  rw [p4Q2JL_originalGIResponseCLM_zero H e z]
  simp

/-- The squared Haar-L2 posterior contrast is also exactly zero at
the genuine frozen Haar endpoint. -/
theorem p4Q2JL_originalPosteriorContrastHaarSq_zero
    (right : Cfg) (e : Link) :
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H 0 (le_refl (0 : ℝ)) right e = 0 := by
  change (∫ g : Gauge,
    (p4Q2GB_originalWilsonPosteriorLeftDensityContrast
      H 0 (le_refl (0 : ℝ)) right e g) ^ 2 ∂nu) = 0
  simp [p4Q2JL_originalPosteriorContrast_zero H right e]

/-- Quantitative SUP bound for the difference of the two ACTUAL
normalized interacting-Wilson posterior density rows. -/
theorem p4Q2JL_originalPosteriorContrast_abs_le
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : Cfg) (e : Link) (g : Gauge) :
    |p4Q2GB_originalWilsonPosteriorLeftDensityContrast
      H beta hbeta right e g| ≤
      Real.exp (16 * beta) - Real.exp (-16 * beta) := by
  have h0 := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
    H 2 (by norm_num) beta hbeta
    (originalWilsonExplicitIdentityBoundary H) right e g
  have h1 := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
    H 2 (by norm_num) beta hbeta
    (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g
  unfold p4Q2GB_originalWilsonPosteriorLeftDensityContrast
  apply abs_le.mpr
  constructor
  · linarith [h0.1, h1.2]
  · linarith [h0.2, h1.1]

/-- Uniform upper bound for the exact squared Haar-L2 norm of the
ORIGINAL interacting-Wilson two-posterior contrast. The proof
integrates the genuine smooth compact SU(2) density rows, rather
than replacing the conditional measures by independent Haar. -/
theorem p4Q2JL_originalPosteriorContrastHaarSq_le_envelope
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : Cfg) (e : Link) :
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H beta hbeta right e ≤
      (Real.exp (16 * beta) - Real.exp (-16 * beta)) ^ 2 := by
  let c : ℝ := Real.exp (16 * beta) - Real.exp (-16 * beta)
  let P0 : Gauge → ℝ := fun g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H) right e g
  let P1 : Gauge → ℝ := fun g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g
  let D : Gauge → ℝ := fun g =>
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast
      H beta hbeta right e g
  have hP0 : Continuous P0 := by
    change Continuous (continuousNormalizedExp nu
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) beta hbeta
        (originalWilsonExplicitIdentityBoundary H) right e))
    exact continuous_continuousNormalizedExp nu _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta
        (originalWilsonExplicitIdentityBoundary H) right e)
  have hP1 : Continuous P1 := by
    change Continuous (continuousNormalizedExp nu
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) beta hbeta
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e))
    exact continuous_continuousNormalizedExp nu _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e)
  have hD : Continuous D := by
    change Continuous (fun g => P0 g - P1 g)
    exact hP0.sub hP1
  have hDsq : Integrable (fun g => (D g) ^ 2) nu :=
    (hD.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : 0 ≤ c := by
    exact le_trans (abs_nonneg _) (p4Q2JL_originalPosteriorContrast_abs_le
      H beta hbeta right e (1 : Gauge))
  have hBound (g : Gauge) : (D g) ^ 2 ≤ c ^ 2 := by
    have ha := p4Q2JL_originalPosteriorContrast_abs_le
      H beta hbeta right e g
    change |D g| ≤ c at ha
    have hlo := (abs_le.mp ha).1
    have hhi := (abs_le.mp ha).2
    have hp : 0 ≤ (c - D g) * (c + D g) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  change (∫ g : Gauge, (D g) ^ 2 ∂nu) ≤ c ^ 2
  calc
    (∫ g : Gauge, (D g) ^ 2 ∂nu) ≤
        ∫ _g : Gauge, c ^ 2 ∂nu := by
      apply integral_mono hDsq (integrable_const _)
      intro g
      exact hBound g
    _ = c ^ 2 := by simp

/-- A genuinely volume/link/right-context UNIFORM TWO-SIDED positive-beta
Haar-L2 envelope, synthesizing GA's physical temporal SU(2) Wilson
crossing variance with FK's true posterior conditional density bounds. -/
theorem p4Q2JL_originalPosteriorContrastHaarSq_twoSided
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : Cfg) (e : Link) :
    Real.exp (-32 * beta) *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ≤
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta hbeta right e ∧
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta hbeta right e ≤
        (Real.exp (16 * beta) - Real.exp (-16 * beta)) ^ 2 := by
  exact ⟨p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_lower
    H beta hbeta right e,
    p4Q2JL_originalPosteriorContrastHaarSq_le_envelope
      H beta hbeta right e⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalPosteriorContrast_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalFiberKernel_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalFiberRepresenter_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalGIResponseCLM_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalGISpatialMinor_zero_at_frozen_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalGIAnchor_zero_at_frozen_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalPosteriorContrastHaarSq_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalPosteriorContrast_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalPosteriorContrastHaarSq_le_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalPosteriorContrastHaarSq_twoSided

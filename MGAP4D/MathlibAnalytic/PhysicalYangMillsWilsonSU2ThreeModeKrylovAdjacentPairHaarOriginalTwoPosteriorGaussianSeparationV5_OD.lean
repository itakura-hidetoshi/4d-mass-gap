import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianFiniteInterpolationV5_OC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedSourcePosteriorContrastProjectionV5_GB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorUniformLeftHaarL2FloorV5_GA
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

/-!
# P4-Q2-OD — actual TWO interacting Wilson posteriors separated by the true temporal Gaussian

GA/FX proved the strict positive L2 Haar squared distance between the
TWO ORIGINAL interacting SU2 one-link conditional posterior densities
at the physical identity vs pi-rotated LEFT boundary, for every beta>0.

OD turns that EXACT posterior density contrast D = p0 - p1 into its
genuine nonzero bounded real signed functional on C(SU2,R).
Its self-pairing equals the PREVIOUS true squared posterior contrast,
which has GA's explicitly positive lower floor. Then NY, not an assumed
characteristic kernel axiom, supplies strictly positive complete
Gaussian double signed energy and some ORIGINAL Wilson temporal kernel
section k_b(x,-) that distinguishes the TWO posterior density laws.

This is a rigorous original-posterior -> signed functional -> temporal
kernel bridge. It does NOT by itself identify the ORIGINAL FF/GI physical
Gauss-law source response with this posterior-contrast functional.
That remaining source-weighted intertwining, spatial GI covariance,
positive fine arbitrary Krylov depth, same endpoint physical source,
uniform Q_GI/N_H, H1-C3 and continuum mass gap stay OPEN.

Original p0,p1, genuine Wilson kernel, Perron half-density and Gauss-law
physical sources are not modified. No artificial rank/injectivity,
independent Haar posterior, Dobrushin, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OD_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OD_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OD_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OD_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OD_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalTwoPosteriorGaussian
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
local notation "k" => p4Q2NJ_originalSU2WilsonTemporalSection

/-- The ACTUAL difference p0-p1 of the two interacting normalized
Wilson posterior densities is a continuous SU(2) function. -/
noncomputable def p4Q2OD_originalTwoPosteriorContrastContinuous
    (right : Cfg) (e : Link) : C(Gauge, ℝ) := by
  let P0 : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) b hb
      (originalWilsonExplicitIdentityBoundary H) right e
  let P1 : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) b hb
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  have h0 : Continuous P0 := by
    change Continuous
      (continuousNormalizedExp mu
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) b hb
          (originalWilsonExplicitIdentityBoundary H) right e))
    exact continuous_continuousNormalizedExp mu _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) b hb
        (originalWilsonExplicitIdentityBoundary H) right e)
  have h1 : Continuous P1 := by
    change Continuous
      (continuousNormalizedExp mu
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) b hb
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e))
    exact continuous_continuousNormalizedExp mu _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) b hb
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e)
  refine ⟨D right e, ?_⟩
  change Continuous (fun g : Gauge => P0 g - P1 g)
  exact h0.sub h1

private theorem p4Q2OD_originalPosteriorPairing_integrable
    (right : Cfg) (e : Link) (f : C(Gauge, ℝ)) :
    Integrable (fun g : Gauge => f g * D right e g) mu := by
  have hCont : Continuous (fun g : Gauge => f g * D right e g) :=
    f.continuous.mul
      (p4Q2OD_originalTwoPosteriorContrastContinuous H b hb right e).continuous
  exact hCont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Literal true two-posterior density difference as a real linear
Haar-reference functional; Haar is NOT substituted for either law. -/
noncomputable def p4Q2OD_originalTwoPosteriorContrastLinear
    (right : Cfg) (e : Link) : C(Gauge, ℝ) →ₗ[ℝ] ℝ where
  toFun := fun f => ∫ g : Gauge, f g * D right e g ∂mu
  map_add' f h := by
    change
      (∫ g : Gauge, (f g + h g) * D right e g ∂mu) =
        (∫ g : Gauge, f g * D right e g ∂mu) +
          (∫ g : Gauge, h g * D right e g ∂mu)
    simp_rw [add_mul]
    exact integral_add
      (p4Q2OD_originalPosteriorPairing_integrable H b hb right e f)
      (p4Q2OD_originalPosteriorPairing_integrable H b hb right e h)
  map_smul' a f := by
    change
      (∫ g : Gauge, (a * f g) * D right e g ∂mu) =
        a * (∫ g : Gauge, f g * D right e g ∂mu)
    simp_rw [mul_assoc]
    exact integral_const_mul _ _

/-- The genuine signed difference of the two original posterior laws
defines a BOUNDED real functional with the TRUE density contrast norm. -/
noncomputable def p4Q2OD_originalTwoPosteriorContrastCLM
    (right : Cfg) (e : Link) : C(Gauge, ℝ) →L[ℝ] ℝ := by
  let dc : C(Gauge,ℝ) :=
    p4Q2OD_originalTwoPosteriorContrastContinuous H b hb right e
  apply LinearMap.mkContinuous
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := C(Gauge,ℝ)) (F := ℝ)
    (σ := RingHom.id ℝ)
    (p4Q2OD_originalTwoPosteriorContrastLinear H b hb right e)
    ‖dc‖
  intro f
  change
    ‖∫ g : Gauge, f g * D right e g ∂mu‖ ≤ ‖dc‖ * ‖f‖
  have hPoint (g : Gauge) :
      ‖f g * D right e g‖ ≤ ‖dc‖ * ‖f‖ := by
    change ‖f g * dc g‖ ≤ ‖dc‖ * ‖f‖
    rw [norm_mul]
    calc
      ‖f g‖ * ‖dc g‖ ≤ ‖f‖ * ‖dc‖ :=
        mul_le_mul (f.norm_coe_le_norm g) (dc.norm_coe_le_norm g)
          (norm_nonneg _) (norm_nonneg _)
      _ = ‖dc‖ * ‖f‖ := mul_comm _ _
  have hBd := norm_integral_le_of_norm_le_const
    (μ := mu) (C := ‖dc‖ * ‖f‖)
    (f := fun g : Gauge => f g * D right e g)
    (ae_of_all _ hPoint)
  simpa using hBd

theorem p4Q2OD_originalTwoPosteriorContrastCLM_apply
    (right : Cfg) (e : Link) (f : C(Gauge, ℝ)) :
    p4Q2OD_originalTwoPosteriorContrastCLM H b hb right e f =
      ∫ g : Gauge, f g * D right e g ∂mu := by
  simp [p4Q2OD_originalTwoPosteriorContrastCLM,
    p4Q2OD_originalTwoPosteriorContrastLinear]

/-- Crucial nondegeneracy certificate: pairing the exact two-posterior
signed functional with ITS OWN true density contrast gives PRECISELY
the previously proved positive genuine original Wilson Haar L2 energy. -/
theorem p4Q2OD_originalTwoPosteriorContrast_self_eq_actualHaarSq
    (right : Cfg) (e : Link) :
    p4Q2OD_originalTwoPosteriorContrastCLM H b hb right e
      (p4Q2OD_originalTwoPosteriorContrastContinuous H b hb right e) =
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H b hb right e := by
  rw [p4Q2OD_originalTwoPosteriorContrastCLM_apply]
  change (∫ g : Gauge, D right e g * D right e g ∂mu) =
    (∫ g : Gauge, (D right e g)^2 ∂mu)
  simp only [pow_two]

/-- The actual original two-posterior signed self-pairing has
GA's explicitly positive Haar-L2 lower coefficient at every b>0. -/
theorem p4Q2OD_originalTwoPosteriorContrast_self_ge_GA_floor
    (hbpos : 0 < b) (right : Cfg) (e : Link) :
    Real.exp (-32 * b) *
      (b ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ≤
      p4Q2OD_originalTwoPosteriorContrastCLM H b hb right e
        (p4Q2OD_originalTwoPosteriorContrastContinuous H b hb right e) := by
  rw [p4Q2OD_originalTwoPosteriorContrast_self_eq_actualHaarSq]
  exact (p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_pos
    H b hbpos right e).2

/-- TRUE original interacting Wilson posterior contrast functional
is nonzero. NO injectivity/rank of a physical source is assumed. -/
theorem p4Q2OD_originalTwoPosteriorContrastCLM_ne_zero
    (hbpos : 0 < b) (right : Cfg) (e : Link) :
    p4Q2OD_originalTwoPosteriorContrastCLM H b hb right e ≠ 0 := by
  intro hZero
  have hEval :
      p4Q2OD_originalTwoPosteriorContrastCLM H b hb right e
        (p4Q2OD_originalTwoPosteriorContrastContinuous H b hb right e) = 0 := by
    rw [hZero]
    simp
  rw [p4Q2OD_originalTwoPosteriorContrast_self_eq_actualHaarSq] at hEval
  exact (ne_of_gt (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
    H b hbpos right e)) hEval

/-- The full genuine temporal Wilson Gaussian detects the exact
SIGNED CONTRAST of the original TWO interacting posterior laws. -/
theorem p4Q2OD_originalTwoPosteriorGaussianDoubleEnergy_pos
    (hbpos : 0 < b) (right : Cfg) (e : Link) :
    0 < p4Q2NX_originalSignedDoubleCLM
      (p4Q2OD_originalTwoPosteriorContrastCLM H b hb right e)
      (NormedSpace.exp (b • p4Q2NX_originalTemporalPairCharacter)) := by
  exact p4Q2NY_originalSignedGaussianDoubleEnergy_pos
    (p4Q2OD_originalTwoPosteriorContrastCLM H b hb right e)
    (p4Q2OD_originalTwoPosteriorContrastCLM_ne_zero H b hb hbpos right e)
    b hbpos

/-- Unconditionally at b>0 there is a section of the ORIGINAL SU(2)
Wilson temporal kernel distinguishing the SAME TWO true posterior
density laws (identity vs rotated left boundary; common right side). -/
theorem p4Q2OD_originalTwoPosteriorWilsonSection_detects_contrast
    (hbpos : 0 < b) (right : Cfg) (e : Link) :
    ∃ x : Gauge,
      (∫ g : Gauge, k b x g * D right e g ∂mu) ≠ 0 := by
  obtain ⟨x, hx⟩ :=
    p4Q2NY_originalPositiveWilsonSection_detects_nonzeroSigned
      (p4Q2OD_originalTwoPosteriorContrastCLM H b hb right e)
      (p4Q2OD_originalTwoPosteriorContrastCLM_ne_zero H b hb hbpos right e)
      b hbpos
  refine ⟨x, ?_⟩
  simpa only [p4Q2OD_originalTwoPosteriorContrastCLM_apply] using hx

/-- Explicitly, the two GENUINE normalized Wilson posterior density
expectations of some actual temporal kernel section are DISTINCT.
These are the original p0,p1 density laws on the reference Haar,
not newly constructed independent-Haar posterior laws. -/
theorem p4Q2OD_originalTwoPosteriorWilsonSection_separates_density_means
    (hbpos : 0 < b) (right : Cfg) (e : Link) :
    ∃ x : Gauge,
      (∫ g : Gauge, k b x g *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H 2 (by norm_num) b hb
          (originalWilsonExplicitIdentityBoundary H) right e g ∂mu) ≠
      (∫ g : Gauge, k b x g *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H 2 (by norm_num) b hb
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g ∂mu) := by
  let P0 : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) b hb
      (originalWilsonExplicitIdentityBoundary H) right e
  let P1 : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) b hb
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  obtain ⟨x, hx⟩ :=
    p4Q2OD_originalTwoPosteriorWilsonSection_detects_contrast H b hb hbpos right e
  have hP0 : Continuous P0 := by
    change Continuous
      (continuousNormalizedExp mu
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) b hb
          (originalWilsonExplicitIdentityBoundary H) right e))
    exact continuous_continuousNormalizedExp mu _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) b hb
        (originalWilsonExplicitIdentityBoundary H) right e)
  have hP1 : Continuous P1 := by
    change Continuous
      (continuousNormalizedExp mu
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) b hb
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e))
    exact continuous_continuousNormalizedExp mu _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) b hb
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e)
  have hInt0 : Integrable (fun g : Gauge => k b x g * P0 g) mu :=
    ((k b x).continuous.mul hP0).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInt1 : Integrable (fun g : Gauge => k b x g * P1 g) mu :=
    ((k b x).continuous.mul hP1).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegral :
      (∫ g : Gauge, k b x g * D right e g ∂mu) =
        (∫ g : Gauge, k b x g * P0 g ∂mu) -
        (∫ g : Gauge, k b x g * P1 g ∂mu) := by
    calc
      (∫ g : Gauge, k b x g * D right e g ∂mu) =
        ∫ g : Gauge, (k b x g * P0 g - k b x g * P1 g) ∂mu := by
          apply integral_congr_ae
          filter_upwards with g
          change k b x g * (P0 g - P1 g) =
            k b x g * P0 g - k b x g * P1 g
          ring
      _ = (∫ g : Gauge, k b x g * P0 g ∂mu) -
            (∫ g : Gauge, k b x g * P1 g ∂mu) :=
        integral_sub hInt0 hInt1
  refine ⟨x, ?_⟩
  change (∫ g : Gauge, k b x g * P0 g ∂mu) ≠
    (∫ g : Gauge, k b x g * P1 g ∂mu)
  apply sub_ne_zero.mp
  rw [← hIntegral]
  exact hx

end OriginalTwoPosteriorGaussian
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OD_originalTwoPosteriorContrastCLM_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OD_originalTwoPosteriorContrast_self_eq_actualHaarSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OD_originalTwoPosteriorContrast_self_ge_GA_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OD_originalTwoPosteriorContrastCLM_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OD_originalTwoPosteriorGaussianDoubleEnergy_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OD_originalTwoPosteriorWilsonSection_detects_contrast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OD_originalTwoPosteriorWilsonSection_separates_density_means

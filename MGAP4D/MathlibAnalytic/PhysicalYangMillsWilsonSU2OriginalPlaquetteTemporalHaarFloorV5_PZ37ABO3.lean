import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFourLinkCharacterConvolutionV5_PZ37ABO2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteHaarVarianceUniformV5_MY
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABO3 — actual plaquette temporal transmission on spatial Haar

ABO2 proves the literal four-link temporal Wilson convolution eigenlaw.
Here MY's injective embedding selects the FOUR ACTUAL links of each
original even-periodic spatial plaquette, including H=0. The cyclic
holonomy energy equals the original oriented Wilson plaquette energy.

The original plaquette energy has spatial-Haar mean 1 and variance 1/4.
Its centered half-energy (E_p-1)/2 therefore has Haar variance 1/16.
Its actual four-link temporal convolution has exactly zero Haar mean
and squared Haar moment r_b^8/16, for every finite H and every actual p.
ABN supplies a common strictly positive floor on 0<b0<=b<=B.

This is the genuine temporal factor on the original spatial-Haar
reference carrier. It does not identify that factor with the full
interacting kernel, replace either posterior by Haar, control a remote
weight or signed Perron overlap, or prove a uniform A/G lower bound.
The normalizing one-link mass Z_b is not the physical transfer norm t.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "ν" => Measure.pi (fun _ : Fin 4 => μ)

local instance p4Q2PZ37ABO3_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABO3_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABO3_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABO3_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABO3_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABO3_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

private theorem p4Q2PZ37ABO3_character_continuous : Continuous χ :=
  continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

private theorem p4Q2PZ37ABO3_singleHaarMean_one :
    p4Q2MY_singleSU2HaarWilsonMean = 1 := by
  have hE : Integrable (specialUnitaryWilsonPlaquetteEnergy 2) μ :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hZero := p4Q2PZ35D4_originalOneLinkHaar_characterZero
  change (∫ g : G, (1 - specialUnitaryWilsonPlaquetteEnergy 2 g) ∂μ) = 0 at hZero
  rw [integral_sub (integrable_const (1 : ℝ)) hE] at hZero
  have hOne : (∫ _g : G, (1 : ℝ) ∂μ) = 1 := by simp
  rw [hOne] at hZero
  unfold p4Q2MY_singleSU2HaarWilsonMean
  linarith

private theorem p4Q2PZ37ABO3_singleHaarVariance_quarter :
    p4Q2MY_singleSU2HaarWilsonVariance = (1 / 4 : ℝ) := by
  unfold p4Q2MY_singleSU2HaarWilsonVariance
  rw [p4Q2PZ37ABO3_singleHaarMean_one]
  calc
    (∫ g : G, (specialUnitaryWilsonPlaquetteEnergy 2 g - 1)^2 ∂μ) =
        ∫ g : G, (χ g)^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      unfold p4Q2PZ35C_originalOneLinkCharacter
      ring
    _ = (1 / 4 : ℝ) := p4Q2PZ37ABN_originalTemporalCharacter_haar_secondMoment

section PhysicalPlaquette

variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2

/-- The true spatial-Haar mean of each original oriented plaquette
energy is exactly one, independent of volume and plaquette. -/
theorem p4Q2PZ37ABO3_originalSpatialWilsonEnergy_haar_mean_one
    (p : Plaq) :
    (∫ A : Cfg, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar) = 1 := by
  rw [p4Q2MY_originalSpatialWilsonEnergy_HaarMean_eq_single H p,
    p4Q2PZ37ABO3_singleHaarMean_one]

/-- The true centered spatial-Haar energy variance of every actual
plaquette is exactly one quarter. This is a reference-Haar identity. -/
theorem p4Q2PZ37ABO3_originalSpatialWilsonEnergy_haar_variance_quarter
    (p : Plaq) :
    (∫ A : Cfg, (p4Q2LO_originalLocalPlaquetteContinuous H p A - 1)^2 ∂haar) =
      (1 / 4 : ℝ) := by
  have h := p4Q2MY_originalSpatialWilsonEnergy_HaarVariance_eq_single H p
  rw [p4Q2PZ37ABO3_singleHaarMean_one,
    p4Q2PZ37ABO3_singleHaarVariance_quarter] at h
  exact h

/-- Evaluate the actual four-link normalized temporal character
convolution on the four REAL edges of the original plaquette. -/
noncomputable def p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer
    (b : ℝ) (p : Plaq) (A : Cfg) : ℝ :=
  p4Q2PZ37ABO2_originalFourLinkCharacterTransfer b
    (fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i))

/-- The literal temporal convolution, pulled back to the actual
physical plaquette geometry, has coefficient r_b^4. -/
theorem p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_eq_coefficient_pow_mul
    (b : ℝ) (p : Plaq) (A : Cfg) :
    p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer H b p A =
      (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^4 *
        (1 - p4Q2LO_originalLocalPlaquetteContinuous H p A) := by
  unfold p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer
  rw [p4Q2PZ37ABO2_originalFourLinkCharacterTransfer_eq_coefficient_pow_mul,
    p4Q2MY_originalSpatialPlaquette_energy_eq_cyclic H p A]
  rfl

private theorem p4Q2PZ37ABO3_originalPlaquetteCharacter_haar_mean_zero
    (p : Plaq) :
    (∫ A : Cfg, (1 - p4Q2LO_originalLocalPlaquetteContinuous H p A) ∂haar) = 0 := by
  let test : C(G, ℝ) := ⟨χ, p4Q2PZ37ABO3_character_continuous⟩
  have h := p4Q2MY_originalPlaquetteCyclicHaar_integral_transport H p test
  change (∫ A : Cfg, χ (p4Q2MY_originalPlaquetteCyclicHolonomy H p A) ∂haar) =
    ∫ g : G, χ g ∂μ at h
  rw [p4Q2PZ35D4_originalOneLinkHaar_characterZero] at h
  simp_rw [p4Q2MY_originalSpatialPlaquette_energy_eq_cyclic H p]
  exact h

/-- Zero mean is preserved for the actual temporal character on the
complete original spatial-Haar configuration carrier. -/
theorem p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_haar_mean_zero
    (b : ℝ) (p : Plaq) :
    (∫ A : Cfg, p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer H b p A ∂haar) = 0 := by
  simp_rw [p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_eq_coefficient_pow_mul]
  rw [integral_const_mul, p4Q2PZ37ABO3_originalPlaquetteCharacter_haar_mean_zero H p,
    mul_zero]

/-- Exact squared Haar norm r_b^8/4 for every actual physical
plaquette's transmitted original character. -/
theorem p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_haar_secondMoment
    (b : ℝ) (p : Plaq) :
    (∫ A : Cfg, (p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer H b p A)^2 ∂haar) =
      (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^8 / 4 := by
  calc
    (∫ A : Cfg, (p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer H b p A)^2 ∂haar) =
        ∫ A : Cfg, (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^8 *
          (p4Q2LO_originalLocalPlaquetteContinuous H p A - 1)^2 ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_eq_coefficient_pow_mul]
      ring
    _ = (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^8 * (1 / 4 : ℝ) := by
      rw [integral_const_mul, p4Q2PZ37ABO3_originalSpatialWilsonEnergy_haar_variance_quarter H p]
    _ = _ := by ring

/-- Literal four-link temporal convolution of the original centered
half-energy (E_p-1)/2. The centering 1 is its proved actual Haar mean. -/
noncomputable def p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer
    (b : ℝ) (p : Plaq) (A : Cfg) : ℝ :=
  (∫ x : Fin 4 → G,
    p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x
      (fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i)) *
      ((specialUnitaryWilsonPlaquetteEnergy 2 (haarFinFourCyclicPlaquetteWord x) - 1) / 2)
      ∂ν) / (p4Q2PZ37ABN_originalTemporalWilsonMass b)^4

/-- Linearity identifies the actual centered half-energy convolution
with minus one half of the actual transmitted character. -/
theorem p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_eq_neg_half_characterTransfer
    (b : ℝ) (p : Plaq) (A : Cfg) :
    p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer H b p A =
      -(1 / 2 : ℝ) * p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer H b p A := by
  unfold p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer
    p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer
    p4Q2PZ37ABO2_originalFourLinkCharacterTransfer
  have hIntegrand :
      (fun x : Fin 4 → G =>
        p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x
          (fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i)) *
          ((specialUnitaryWilsonPlaquetteEnergy 2 (haarFinFourCyclicPlaquetteWord x) - 1) / 2)) =
      (fun x : Fin 4 → G => -(1 / 2 : ℝ) *
        (p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x
          (fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i)) *
            χ (haarFinFourCyclicPlaquetteWord x))) := by
    funext x
    unfold p4Q2PZ35C_originalOneLinkCharacter
    ring
  rw [hIntegrand, integral_const_mul]
  ring

/-- The centered half-energy of each actual plaquette is an exact
temporal mode with eigenvalue r_b^4; no spectral premise is assumed. -/
theorem p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_eq_coefficient_pow_mul
    (b : ℝ) (p : Plaq) (A : Cfg) :
    p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer H b p A =
      (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^4 *
        ((p4Q2LO_originalLocalPlaquetteContinuous H p A - 1) / 2) := by
  rw [p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_eq_neg_half_characterTransfer,
    p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_eq_coefficient_pow_mul]
  ring

/-- The original centered half-energy remains centered after its
actual four-link temporal convolution, on complete spatial Haar. -/
theorem p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_haar_mean_zero
    (b : ℝ) (p : Plaq) :
    (∫ A : Cfg, p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer H b p A ∂haar) = 0 := by
  simp_rw [p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_eq_neg_half_characterTransfer]
  rw [integral_const_mul, p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_haar_mean_zero H b p,
    mul_zero]

/-- Exact transmitted Haar variance r_b^8/16 for the actual original
centered half-energy, uniform as an identity in volume and plaquette. -/
theorem p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_haar_secondMoment
    (b : ℝ) (p : Plaq) :
    (∫ A : Cfg, (p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer H b p A)^2 ∂haar) =
      (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^8 / 16 := by
  calc
    (∫ A : Cfg, (p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer H b p A)^2 ∂haar) =
        ∫ A : Cfg, (1 / 4 : ℝ) *
          (p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer H b p A)^2 ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_eq_neg_half_characterTransfer]
      ring
    _ = (1 / 4 : ℝ) * (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^8 / 4 := by
      rw [integral_const_mul, p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_haar_secondMoment H b p]
      ring
    _ = _ := by ring

/-- A common positive temporal-reference-Haar variance floor on the
prescribed interval 0<b0<=b<=B, for ALL finite H and actual plaquettes.
This is not a claim about the full interacting GI response. -/
theorem p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_positive_interval
    (b0 B b : ℝ) (hb0 : 0 < b0) (hLower : b0 ≤ b) (hUpper : b ≤ B)
    (p : Plaq) :
    0 < (b0 * Real.exp (-2 * B) / 4)^8 / 16 ∧
      (b0 * Real.exp (-2 * B) / 4)^8 / 16 ≤
        ∫ A : Cfg, (p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer H b p A)^2 ∂haar := by
  have hFloor : 0 < b0 * Real.exp (-2 * B) / 4 := by positivity
  have hCoefficient := p4Q2PZ37ABN_originalTemporalWilsonCoefficient_uniform_lower
    b0 B b hb0 hLower hUpper
  have hPower : (b0 * Real.exp (-2 * B) / 4)^8 ≤
      (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^8 := by
    gcongr
  refine ⟨by positivity, ?_⟩
  rw [p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_haar_secondMoment H b p]
  nlinarith

end PhysicalPlaquette
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalSpatialWilsonEnergy_haar_mean_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalSpatialWilsonEnergy_haar_variance_quarter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_eq_coefficient_pow_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_haar_mean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer_haar_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_eq_neg_half_characterTransfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_eq_coefficient_pow_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_haar_mean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_haar_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_positive_interval

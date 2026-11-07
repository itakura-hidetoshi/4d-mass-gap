import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalBorelPositivePartHaarMomentV5_PZ37AHM
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHN — explicit original-identity Haar source moment certificates

AHM proved the TRUE ORIGINAL centered Wilson source f_H and complete
one-slab signed transfer have a Borel positive-part correlation moment.
This append-only leaf develops an EXPLICIT SOURCE-SIDE numerical-geometric
witness without assuming a transfer sign or replacing any Haar measure.

At the actual SU(2) identity spatial configuration I_H the centered
continuous ZW source is EXACTLY -p_H/2, by AHH and AGN. Every original
link lies in the genuine SU(2) ADK chordal open ball about identity of
rational radius 1/96 in an explicitly named spatial box S_H.

On this WHOLE explicit box, the original AGG all-link source slope 12
and AHF's exact |Link_H|=p_H give

  f_H(C) <= -3*p_H/8,     |f_H(C)| >= 3*p_H/8.

The original spatial Haar product measure of S_H is at least

  kappa(1/96)^card(Link_H) > 0,

where kappa is the original ADQ/ADZ strictly positive SU(2) sphere
fraction, not an invented rational Haar mass. Hence the ORIGINAL
source Haar L1 mass and its squared Haar second moment satisfy

  (3*p_H/8) * kappa(1/96)^p_H <= ∫ |f_H| dμ_H <= p_H/2
  (3*p_H/8)^2 * kappa(1/96)^p_H <= ∫ f_H^2 dμ_H.

The second moment is exactly that of the SAME original physical
Gauss-law L² source, by the proven AFZ Haar-a.e. representative equality.

This gives a fully specified rational SPATIAL CENTER, rational radius,
and rational source threshold, plus a certified genuine Haar geometric
floor. kappa(1/96) is an exact proven but NOT here numerically evaluated
Haar bound. There is no transfer sign, numerical AGP signed table,
uniform-in-H coercivity or Yang--Mills continuum gap claim.

Strict positivity of the full Wilson kernel from LJ is a qualitative
positive-definiteness theorem; these source moment lower bounds do NOT
by themselves prove a positive numerical lower eigenvalue for K_H or
convert to a numerical lower bound on ∫ f_H*T_H dμ_H.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHN_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHN_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHN_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHN_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHN_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "haar" => normalizedCompactHaar G
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "kappa" => p4Q2PZ37ADQ_sphereRadiusFraction

local instance p4Q2PZ37AHN_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHN_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Actual identity on every original physical spatial link; not a
chosen source surrogate or an arbitrary compactness witness. -/
def p4Q2PZ37AHN_identity : Cfg := fun _ : Link => (1 : G)

/-- Explicit original ADK ALL-LINK true chordal open box at the fixed
positive RATIONAL one-link radius 1/96. -/
def p4Q2PZ37AHN_identityBox : Set Cfg :=
  p4Q2PZ37ADL_originalSliceFullChordalBox H
    (p4Q2PZ37AHN_identity H) (1 / 96)

/-- The original spatial plaquette count is strictly positive at all H. -/
theorem p4Q2PZ37AHN_count_pos : 0 < pH := by
  rw [← p4Q2PZ37AGN_countRational_exact H]
  exact_mod_cast p4Q2PZ37AHG_count_pos H

/-- The specified identity-centered box is BOREL in the ORIGINAL
spatial topology, hence measurable under the original product Haar. -/
theorem p4Q2PZ37AHN_identityBox_measurable :
    MeasurableSet (p4Q2PZ37AHN_identityBox H) :=
  (p4Q2PZ37ADL_sliceBox_isOpen H
    (p4Q2PZ37AHN_identity H) (1 / 96)).measurableSet

/-- The original spatial Haar mass of the EXPLICIT identity box has a
closed radius-only geometric floor with p_H true product coordinates. -/
theorem p4Q2PZ37AHN_identityBox_trueHaarFloor :
    kappa (1 / 96) ^ Fintype.card Link ≤
      Measure.real muH (p4Q2PZ37AHN_identityBox H) := by
  change kappa (1 / 96) ^ Fintype.card Link ≤
    Measure.real muH (p4Q2PZ37ADL_originalSliceFullChordalBox H
      (p4Q2PZ37AHN_identity H) (1 / 96))
  rw [p4Q2PZ37ADL_sliceBox_originalHaarMass_eq]
  calc
    kappa (1 / 96) ^ Fintype.card Link =
        ∏ _e : Link, kappa (1 / 96) := by simp
    _ ≤ ∏ e : Link, Measure.real haar
        (p4Q2PZ37ADK_trueChordalBall
          (p4Q2PZ37AHN_identity H e) (1 / 96)) :=
      Finset.prod_le_prod
        (fun _ _ => le_of_lt (p4Q2PZ37ADQ_sphereRadiusFraction_pos (1 / 96)))
        (fun e _ => p4Q2PZ37ADZ_originalAllCenters_ge_explicit
          (p4Q2PZ37AHN_identity H e) (1 / 96) (by norm_num))

/-- Every original link in this explicit spatial box has chordal
distance at most the rational 1/96. The TRUE total distance is at most
p_H/96 using AHF's previously established exact link-plaquette count. -/
theorem p4Q2PZ37AHN_identityBox_spatialDistance
    (C : Cfg) (hC : C ∈ p4Q2PZ37AHN_identityBox H) :
    Dsp (p4Q2PZ37AHN_identity H) C ≤ pH / 96 := by
  have hEach (e : Link) :
      dJ (p4Q2PZ37AHN_identity H e) (C e) ≤ (1 / 96 : ℝ) :=
    (hC e (Set.mem_univ e)).le
  calc
    Dsp (p4Q2PZ37AHN_identity H) C ≤
        ∑ _e : Link, (1 / 96 : ℝ) := by
      unfold p4Q2PZ37AGG_originalSpatialChordalDistance
      exact Finset.sum_le_sum (fun e _ => hEach e)
    _ = (Fintype.card Link : ℝ) * (1 / 96 : ℝ) := by simp
    _ = pH / 96 := by
      rw [p4Q2PZ37AHI_cardLinks_eq_plaquettes H]
      ring

/-- A completely explicit, RATIONAL centered-Wilson-action sign and
amplitude on EVERY actual configuration in the genuine identity box.
This has a fixed source-side sign, not a claimed transfer-side sign. -/
theorem p4Q2PZ37AHN_identityBox_source_negative
    (C : Cfg) (hC : C ∈ p4Q2PZ37AHN_identityBox H) :
    fCont C ≤ -(3 * pH / 8) := by
  let I : Cfg := p4Q2PZ37AHN_identity H
  have hIdentity : fCont I = -pH / 2 :=
    p4Q2PZ37AHH_originalSource_identity H
  have hDist : Dsp I C ≤ pH / 96 :=
    p4Q2PZ37AHN_identityBox_spatialDistance H C hC
  have hLip :
      |fCont I - fCont C| ≤ 12 * Dsp I C :=
    p4Q2PZ37AGG_originalCenteredSource_allLinkChordalSlope H I C
  have hSize : 12 * Dsp I C ≤ pH / 8 := by
    calc
      12 * Dsp I C ≤ 12 * (pH / 96) :=
        mul_le_mul_of_nonneg_left hDist (by norm_num)
      _ = pH / 8 := by ring
  have hDelta := (abs_le.mp hLip).1
  linarith only [hIdentity, hDelta, hSize]

theorem p4Q2PZ37AHN_identityBox_sourceAbs_lower
    (C : Cfg) (hC : C ∈ p4Q2PZ37AHN_identityBox H) :
    3 * pH / 8 ≤ |fCont C| := by
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have hNeg := p4Q2PZ37AHN_identityBox_source_negative H C hC
  have hNonpos : fCont C ≤ 0 := by linarith only [hNeg, hp]
  rw [abs_of_nonpos hNonpos]
  linarith only [hNeg]

theorem p4Q2PZ37AHN_identityBox_sourceSquare_lower
    (C : Cfg) (hC : C ∈ p4Q2PZ37AHN_identityBox H) :
    (3 * pH / 8) ^ 2 ≤ (fCont C) ^ 2 := by
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have h0 : 0 ≤ 3 * pH / 8 := by positivity
  apply (sq_le_sq).2
  rw [abs_of_nonneg h0]
  exact p4Q2PZ37AHN_identityBox_sourceAbs_lower H C hC

/-- The TRUE original Haar L1 scalar is the absolute-value integral
of the authentic AFZ continuous representative; L2 point values are
not fabricated. -/
theorem p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral :
    Msrc = ∫ C : Cfg, |fCont C| ∂muH := by
  have hRep :
      (fun C : Cfg => (f0 : Lp ℝ 2 muH) C) =ᵐ[muH] fCont := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := muH) fCont
  unfold p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass
  apply integral_congr_ae
  filter_upwards [hRep] with C hC
  rw [hC]

/-- First substantive numerical-geometric certificate for the
GENUINE original centered source Haar L1 mass at an actual explicit
spatial identity center. The mass floor uses unchanged true Haar. -/
theorem p4Q2PZ37AHN_originalSource_L1_explicitFloor :
    (3 * pH / 8) * kappa (1 / 96) ^ Fintype.card Link ≤ Msrc := by
  let S : Set Cfg := p4Q2PZ37AHN_identityBox H
  have hMeas : MeasurableSet S :=
    p4Q2PZ37AHN_identityBox_measurable H
  have hf : Integrable (fun C : Cfg => fCont C) muH :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbs : Integrable (fun C : Cfg => |fCont C|) muH := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hMonotone :
      (∫ _C in S, 3 * pH / 8 ∂muH) ≤
        ∫ C in S, |fCont C| ∂muH := by
    apply setIntegral_mono_on integrableOn_const hAbs.integrableOn hMeas
    intro C hC
    exact p4Q2PZ37AHN_identityBox_sourceAbs_lower H C hC
  have hMonotone' :
      (3 * pH / 8) * Measure.real muH S ≤
        ∫ C in S, |fCont C| ∂muH := by
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hMonotone
  have hWhole :
      (∫ C in S, |fCont C| ∂muH) ≤ ∫ C : Cfg, |fCont C| ∂muH :=
    setIntegral_le_integral hAbs (ae_of_all _ fun C => abs_nonneg (fCont C))
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have hCoef : 0 ≤ 3 * pH / 8 := by positivity
  calc
    (3 * pH / 8) * kappa (1 / 96) ^ Fintype.card Link ≤
        (3 * pH / 8) * Measure.real muH S :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHN_identityBox_trueHaarFloor H) hCoef
    _ ≤ ∫ C in S, |fCont C| ∂muH := hMonotone'
    _ ≤ ∫ C : Cfg, |fCont C| ∂muH := hWhole
    _ = Msrc := (p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H).symm

/-- Real second moment of the genuine original centered CONTINUOUS
source on the actual original spatial Haar probability. -/
def p4Q2PZ37AHN_originalSource_HaarSecondMoment : ℝ :=
  ∫ C : Cfg, (fCont C) ^ 2 ∂muH

/-- Proven AFZ true Haar-a.e. equality transfers the continuous source
second moment to the ORIGINAL physical Gauss-law L2 representative. -/
theorem p4Q2PZ37AHN_originalSource_HaarSecondMoment_eq_physical :
    p4Q2PZ37AHN_originalSource_HaarSecondMoment H =
      ∫ C : Cfg, ((f0 : Lp ℝ 2 muH) C) ^ 2 ∂muH := by
  have hRep :
      (fun C : Cfg => (f0 : Lp ℝ 2 muH) C) =ᵐ[muH] fCont := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := muH) fCont
  unfold p4Q2PZ37AHN_originalSource_HaarSecondMoment
  apply integral_congr_ae
  filter_upwards [hRep] with C hC
  rw [hC]

/-- Actual centered ZW SOURCE Haar variance has a certified lower
bound from the true identity box; no finite-H transfer eigenvalue or
mass gap lower bound is inserted. -/
theorem p4Q2PZ37AHN_originalSource_HaarSecondMoment_explicitFloor :
    (3 * pH / 8) ^ 2 * kappa (1 / 96) ^ Fintype.card Link ≤
      p4Q2PZ37AHN_originalSource_HaarSecondMoment H := by
  let S : Set Cfg := p4Q2PZ37AHN_identityBox H
  have hMeas : MeasurableSet S :=
    p4Q2PZ37AHN_identityBox_measurable H
  have hf : Integrable (fun C : Cfg => (fCont C) ^ 2) muH :=
    ((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMonotone :
      (∫ _C in S, (3 * pH / 8) ^ 2 ∂muH) ≤
        ∫ C in S, (fCont C) ^ 2 ∂muH := by
    apply setIntegral_mono_on integrableOn_const hf.integrableOn hMeas
    intro C hC
    exact p4Q2PZ37AHN_identityBox_sourceSquare_lower H C hC
  have hMonotone' :
      (3 * pH / 8) ^ 2 * Measure.real muH S ≤
        ∫ C in S, (fCont C) ^ 2 ∂muH := by
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hMonotone
  have hWhole :
      (∫ C in S, (fCont C) ^ 2 ∂muH) ≤
        ∫ C : Cfg, (fCont C) ^ 2 ∂muH :=
    setIntegral_le_integral hf (ae_of_all _ fun C => sq_nonneg (fCont C))
  have hCoef : 0 ≤ (3 * pH / 8) ^ 2 := sq_nonneg _
  calc
    (3 * pH / 8) ^ 2 * kappa (1 / 96) ^ Fintype.card Link ≤
        (3 * pH / 8) ^ 2 * Measure.real muH S :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHN_identityBox_trueHaarFloor H) hCoef
    _ ≤ ∫ C in S, (fCont C) ^ 2 ∂muH := hMonotone'
    _ ≤ ∫ C : Cfg, (fCont C) ^ 2 ∂muH := hWhole
    _ = p4Q2PZ37AHN_originalSource_HaarSecondMoment H := rfl

/-- The two TRUE original source Haar moments are strictly positive at
each H, with a common fully specified geometric identity-box witness. -/
theorem p4Q2PZ37AHN_originalSource_twoHaarMoments_pos :
    0 < Msrc ∧ 0 < p4Q2PZ37AHN_originalSource_HaarSecondMoment H := by
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have hκ : 0 < kappa (1 / 96) :=
    p4Q2PZ37ADQ_sphereRadiusFraction_pos _
  have hL1 : 0 < (3 * pH / 8) * kappa (1 / 96) ^ Fintype.card Link :=
    mul_pos (by positivity) (pow_pos hκ _)
  have hL2 : 0 < (3 * pH / 8) ^ 2 * kappa (1 / 96) ^ Fintype.card Link :=
    mul_pos (by positivity) (pow_pos hκ _)
  exact ⟨hL1.trans_le (p4Q2PZ37AHN_originalSource_L1_explicitFloor H),
    hL2.trans_le (p4Q2PZ37AHN_originalSource_HaarSecondMoment_explicitFloor H)⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_count_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_identityBox_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_identityBox_trueHaarFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_identityBox_spatialDistance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_identityBox_source_negative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_identityBox_sourceAbs_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_identityBox_sourceSquare_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_originalSource_L1_explicitFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_originalSource_HaarSecondMoment_eq_physical
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_originalSource_HaarSecondMoment_explicitFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHN_originalSource_twoHaarMoments_pos

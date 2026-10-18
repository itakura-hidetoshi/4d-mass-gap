import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorHaarMinorReconstructionV5_JN2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTemporalWilsonHaarCenterV5_JO
import Mathlib.Tactic

/-!
# P4-Q2-JP: actual interacting Wilson posterior detects the literal temporal SU(2) source

JN2 proves from the ORIGINAL interacting Wilson posterior densities and
their true Perron vacuum (without differentiability assumptions) that
  |p0_b(g) - p1_b(g) + b * (D(g) - HaarMean D)| <= 272 exp(8) b^2
uniformly in finite spatial volume, physical link and right environment.
JO proves the literal original temporal SU(2) Wilson action contrast D
has HaarMean D = 0 and strictly positive squared Haar norm V_SU2.

We integrate this TRUE UNLOGGED ORIGINAL Wilson density contrast against
an arbitrary genuine continuous SU(2) source and obtain a UNIFORM
operator-norm-relevant first-order bound:

  |Gap_b(F) + b * integral F(g) D(g) dHaar| <= ||F||_sup C b^2

where Gap_b(F) is the difference of the SAME test's integrals under the
TWO ORIGINAL normalized interacting-Wilson conditional posterior densities
expressed relative to their actual normalized Haar reference.

Most importantly the literal temporal Wilson test itself is GENUINELY
detected: Gap_b(D) is strictly NEGATIVE for every sufficiently small
positive b in a universal interval independent of H, link and right
physical background; more precisely
  Gap_b(D) <= -(b/2) * V_SU2 < 0.

This is a true temporal test-detection theorem, NOT the unresolved
static SPATIAL Wilson GI two-context minor. A spatial-source detector
has an additional original Wilson kernel and Perron half-density
receiver, whose temporal correlation is not assumed nonzero here.
No independent-Haar CONDITIONAL posterior, new axiom, H1-C3 closure
or continuum Yang–Mills mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast
local notation "V" => p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance
local notation "C" => (272 * Real.exp 8 : ℝ)

/-- The actual normalized-Haar moment of a continuous physical SU(2)
test against the TWO ORIGINAL interacting Wilson posterior densities'
difference. Neither conditional law is replaced by independent Haar. -/
noncomputable def p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) : ℝ :=
  ∫ g : Gauge,
    F g * p4Q2GB_originalWilsonPosteriorLeftDensityContrast
      H b hb right e g ∂nu

/-- The original interacting posterior density contrast has exactly
zero Haar mean for every positive or zero physical Wilson coupling,
since BOTH original normalized conditional densities integrate to 1. -/
theorem p4Q2JP_originalPosteriorContrast_HaarMean_zero
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    (∫ g : Gauge,
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast
        H b hb right e g ∂nu) = 0 := by
  let P0 := p4Q2JN2_originalPosteriorIdentityContinuous H b hb right e
  let P1 := p4Q2JN2_originalPosteriorPiContinuous H b hb right e
  have hI0 : Integrable (fun g : Gauge => P0 g) nu :=
    P0.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hI1 : Integrable (fun g : Gauge => P1 g) nu :=
    P1.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOnes := p4Q2JN2_bothOriginalPosteriorHaarIntegrals_one
    H b hb right e
  have h0 : (∫ g : Gauge, P0 g ∂nu) = 1 := hOnes.1
  have h1 : (∫ g : Gauge, P1 g ∂nu) = 1 := hOnes.2
  change (∫ g : Gauge, P0 g - P1 g ∂nu) = 0
  rw [integral_sub hI0 hI1, h0, h1, sub_self]

/-- Any continuous source can be shifted by a constant without changing
its TRUE original Wilson two-posterior test gap; only genuine
nonconstant SU(2) variation is visible to these normalized laws. -/
theorem p4Q2JP_originalPosteriorTemporalTestGap_constant_invisible
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) (c : ℝ) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb right e
        (F - c • (1 : C(Gauge, ℝ))) =
      p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb right e F := by
  let P := p4Q2JN2_originalPosteriorDensityContrastContinuous H b hb right e
  have hPInt : Integrable (fun g : Gauge => P g) nu :=
    P.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFPInt : Integrable (fun g : Gauge => F g * P g) nu :=
    (F.continuous.mul P.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hZero := p4Q2JP_originalPosteriorContrast_HaarMean_zero H b hb right e
  unfold p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
  have hEval (g : Gauge) :
      (F - c • (1 : C(Gauge, ℝ))) g = F g - c := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
  simp_rw [hEval]
  change (∫ g : Gauge, (F g - c) * P g ∂nu) =
    ∫ g : Gauge, F g * P g ∂nu
  calc
    (∫ g : Gauge, (F g - c) * P g ∂nu) =
        ∫ g : Gauge, F g * P g - c * P g ∂nu := by
      apply integral_congr_ae
      filter_upwards with g
      ring
    _ = (∫ g : Gauge, F g * P g ∂nu) -
        (∫ g : Gauge, c * P g ∂nu) :=
      integral_sub hFPInt (hPInt.const_mul _)
    _ = (∫ g : Gauge, F g * P g ∂nu) := by
      rw [integral_const_mul]
      change (∫ g : Gauge, F g * P g ∂nu) -
        c * (∫ g : Gauge, P g ∂nu) = _
      rw [hZero, mul_zero, sub_zero]

/-- The original SU(2) Wilson temporal crossing action D(g) is within
[-2,2] pointwise because each genuine Wilson plaquette energy is in
[0,2]. This is stronger than the 4-unit oscillation bound of JN. -/
theorem p4Q2JP_temporalWilsonContrast_abs_le_two (g : Gauge) :
    |D g| ≤ (2 : ℝ) := by
  let R : Gauge := specialUnitaryTwoRotation Real.pi
  have h0 : 0 ≤ specialUnitaryWilsonPlaquetteEnergy 2 g :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) g
  have h2 : specialUnitaryWilsonPlaquetteEnergy 2 g ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) g
  have hr0 : 0 ≤ specialUnitaryWilsonPlaquetteEnergy 2 (R⁻¹ * g) :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) (R⁻¹ * g)
  have hr2 : specialUnitaryWilsonPlaquetteEnergy 2 (R⁻¹ * g) ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) (R⁻¹ * g)
  apply abs_le.mpr
  dsimp only [p4Q2FZ_originalSU2TemporalWilsonContrast]
  constructor <;> dsimp [R] at *
  · linarith
  · linarith

theorem p4Q2JP_temporalWilsonContinuous_supNorm_le_two :
    ‖p4Q2JM_temporalWilsonContinuous‖ ≤ (2 : ℝ) := by
  apply (ContinuousMap.norm_le _ (by norm_num)).2
  intro g
  simpa only [p4Q2JM_temporalWilsonContinuous, Real.norm_eq_abs] using
    p4Q2JP_temporalWilsonContrast_abs_le_two g

/-- A UNIFORM bound for testing the TRUE physical interacting-Wilson
density contrast against ANY continuous SU(2) source F. It follows
by integrating the JN2 quadratic error for the original density
difference, and JO's actual SU(2) Haar-mean cancellation. -/
theorem p4Q2JP_originalWilsonTemporalTestGap_quadraticError
    (b : ℝ) (hb : 0 ≤ b) (hsmall : b ≤ (1 / 4 : ℝ))
    (right : Cfg) (e : Link) (F : C(Gauge, ℝ)) :
    ‖p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb right e F +
        b * (∫ g : Gauge, F g * D g ∂nu)‖ ≤
      ‖F‖ * (C * b ^ 2) := by
  let P := p4Q2JN2_originalPosteriorDensityContrastContinuous H b hb right e
  let Q : Gauge → ℝ := fun g => P g + b * D g
  let E : Gauge → ℝ := fun g => F g * Q g
  have hP : Continuous (fun g : Gauge => P g) := P.continuous
  have hD : Continuous D :=
    p4Q2FZ_originalSU2TemporalWilsonContrast_continuous
  have hQ : Continuous Q := hP.add (continuous_const.mul hD)
  have hE : Continuous E := F.continuous.mul hQ
  have hPInt : Integrable (fun g : Gauge => F g * P g) nu :=
    (F.continuous.mul hP).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDInt : Integrable (fun g : Gauge => F g * D g) nu :=
    (F.continuous.mul hD).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (g : Gauge) : ‖Q g‖ ≤ C * b ^ 2 := by
    have h := p4Q2JN2_actualDensityContrast_centeredTaylor_quadratic
      H b hb hsmall right e g
    rw [p4Q2JO_temporalWilsonContrast_HaarMean_zero] at h
    simpa [Q, P, sub_zero] using h
  have hBound (g : Gauge) : ‖E g‖ ≤ ‖F‖ * (C * b ^ 2) := by
    calc
      ‖E g‖ = ‖F g‖ * ‖Q g‖ := norm_mul _ _
      _ ≤ ‖F‖ * ‖Q g‖ :=
        mul_le_mul_of_nonneg_right (F.norm_coe_le_norm g) (norm_nonneg _)
      _ ≤ ‖F‖ * (C * b ^ 2) :=
        mul_le_mul_of_nonneg_left (hPoint g) (norm_nonneg F)
  have hIntegral :
      (∫ g : Gauge, E g ∂nu) =
        p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
            H b hb right e F +
          b * (∫ g : Gauge, F g * D g ∂nu) := by
    calc
      (∫ g : Gauge, E g ∂nu) =
          ∫ g : Gauge, (F g * P g) + b * (F g * D g) ∂nu := by
        apply integral_congr_ae
        filter_upwards with g
        dsimp [E, Q]
        ring
      _ = (∫ g : Gauge, F g * P g ∂nu) +
          (∫ g : Gauge, b * (F g * D g) ∂nu) :=
        integral_add hPInt (hDInt.const_mul b)
      _ = _ := by
        rw [integral_const_mul]
        rfl
  have hErr : ‖∫ g : Gauge, E g ∂nu‖ ≤ ‖F‖ * (C * b ^ 2) := by
    have h := norm_integral_le_of_norm_le_const
      (μ := nu) (Filter.Eventually.of_forall hBound)
    simpa using h
  rw [hIntegral] at hErr
  exact hErr

/-- For the LITERAL temporal SU(2) Wilson test D, the genuine original
two-posterior expectation gap has the strict first-order expansion
  Gap_b(D) = -b*V_SU2 + O(b²),
with a completely volume/link/background-INDEPENDENT remainder. -/
theorem p4Q2JP_originalWilsonTemporalTestGap_temporalVarianceError
    (b : ℝ) (hb : 0 ≤ b) (hsmall : b ≤ (1 / 4 : ℝ))
    (right : Cfg) (e : Link) :
    ‖p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
        H b hb right e p4Q2JM_temporalWilsonContinuous + b * V‖ ≤
      2 * (C * b ^ 2) := by
  let T := p4Q2JM_temporalWilsonContinuous
  have hDsq : (∫ g : Gauge, T g * D g ∂nu) = V := by
    change (∫ g : Gauge, D g * D g ∂nu) = V
    calc
      (∫ g : Gauge, D g * D g ∂nu) =
        (∫ g : Gauge, (D g) ^ 2 ∂nu) := by
          apply integral_congr_ae
          filter_upwards with g
          ring
      _ = V := p4Q2JO_temporalWilsonHaarSquare_eq_variance
  have hError := p4Q2JP_originalWilsonTemporalTestGap_quadraticError
    H b hb hsmall right e T
  rw [hDsq] at hError
  calc
    ‖p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb right e T +
        b * V‖ ≤ ‖T‖ * (C * b ^ 2) := hError
    _ ≤ 2 * (C * b ^ 2) :=
      mul_le_mul_of_nonneg_right
        p4Q2JP_temporalWilsonContinuous_supNorm_le_two
        (by positivity)

/-- A positive, PHYSICAL-VOLUME-UNIFORM weak-coupling interval on
which the original interacting Wilson posterior strictly separates
the original temporal SU(2) Wilson test. -/
noncomputable def p4Q2JP_originalWilsonTemporalDetectionRadius : ℝ :=
  min (1 / 4 : ℝ) (V / (4 * C))

theorem p4Q2JP_originalWilsonTemporalDetectionRadius_pos :
    0 < p4Q2JP_originalWilsonTemporalDetectionRadius := by
  unfold p4Q2JP_originalWilsonTemporalDetectionRadius
  apply lt_min
  · norm_num
  · exact div_pos p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos
      (by positivity)

/-- The actual TWO normalized interacting-Wilson posteriors genuinely
detect the actual physical temporal SU(2) Wilson action D:
  Gap_b(D) <= -(b/2) V_SU2 < 0.
This strict nonzero sign holds at EVERY spatial finite volume,
physical link and right environment for all b in one universal
positive range. Does NOT assert that JH's distinct spatial-source
GI receiver has a nonzero coupling to D. -/
theorem p4Q2JP_originalWilsonTemporalTestGap_strictNegative_uniform
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right : Cfg) (e : Link) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
        H b hb.le right e p4Q2JM_temporalWilsonContinuous ≤
      -(b * V) / 2 ∧
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
        H b hb.le right e p4Q2JM_temporalWilsonContinuous < 0 := by
  let I := p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
    H b hb.le right e p4Q2JM_temporalWilsonContinuous
  let c : ℝ := C
  have hCpos : 0 < c := by dsimp [c]; positivity
  have hVpos : 0 < V :=
    p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos
  have hSmall : b ≤ (1 / 4 : ℝ) := by
    exact (lt_of_lt_of_le hwindow (min_le_left _ _)).le
  have hRate : b ≤ V / (4 * c) := by
    exact (lt_of_lt_of_le hwindow (min_le_right _ _)).le
  have hDenom : 0 < 4 * c := mul_pos (by norm_num) hCpos
  have hProduct : b * (4 * c) ≤ V :=
    (le_div_iff₀ hDenom).mp hRate
  have hMult := mul_le_mul_of_nonneg_left hProduct hb.le
  have hHalf : 2 * (c * b ^ 2) ≤ b * V / 2 := by
    nlinarith [hMult]
  have hEstimate := p4Q2JP_originalWilsonTemporalTestGap_temporalVarianceError
    H b hb.le hSmall right e
  have hUpper : I + b * V ≤ 2 * (c * b ^ 2) := by
    exact (le_abs_self _).trans (by simpa [I, c, Real.norm_eq_abs] using hEstimate)
  have hBound : I ≤ -(b * V) / 2 := by linarith
  refine ⟨hBound, ?_⟩
  have hPositive : 0 < b * V := mul_pos hb hVpos
  exact lt_of_le_of_lt hBound (by linarith)

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JP_originalPosteriorContrast_HaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JP_originalPosteriorTemporalTestGap_constant_invisible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JP_temporalWilsonContrast_abs_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JP_temporalWilsonContinuous_supNorm_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JP_originalWilsonTemporalTestGap_quadraticError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JP_originalWilsonTemporalTestGap_temporalVarianceError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JP_originalWilsonTemporalDetectionRadius_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JP_originalWilsonTemporalTestGap_strictNegative_uniform

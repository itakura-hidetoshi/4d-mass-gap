import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionWilsonHaarContractionV5_PZ35D4
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureNorm
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyInversion
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABN — a positive coefficient of the original temporal Wilson factor

Use the actual normalized compact SU(2) Haar, the original Wilson energy E,
its original character chi=1-E, and the literal original temporal factor
  k_b(g) = specialUnitaryWilsonBoltzmannCentralFunction 2 b g.
Define Z_b=integral k_b, N_b=integral k_b*chi and r_b=N_b/Z_b.

The genuine Haar identities integral chi=0 and integral chi^2=1/4,
together with an elementary pointwise exponential inequality, prove
  b*exp(-2*b)/4 <= N_b and b*exp(-2*b)/4 <= r_b <= 1  (b>=0).
Thus r_b>0 for every b>0, and b0*exp(-2*B)/4 is a common positive
coefficient floor whenever 0<b0<=b<=B.  The coefficient is continuous
on the whole real line and vanishes at b=0.

These are unconditional facts about the original temporal Wilson factor.
They do not assert the four-link exponential eigenlaw, a remote marginal
bound, signed Wilson/Perron source alignment, a uniform absolute cross
moment, a mass gap, or an alteration of either original posterior.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "k" => specialUnitaryWilsonBoltzmannCentralFunction 2

local instance p4Q2PZ37ABN_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABN_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABN_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABN_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABN_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABN_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

private theorem p4Q2PZ37ABN_character_continuous : Continuous χ :=
  continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

private theorem p4Q2PZ37ABN_temporalFactor_continuous (b : ℝ) :
    Continuous (k b) := by
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2))

private theorem p4Q2PZ37ABN_temporalFactor_integrable (b : ℝ) :
    Integrable (k b) μ :=
  (p4Q2PZ37ABN_temporalFactor_continuous b).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact genuine Haar second moment of the normalized real fundamental
Wilson character; the normalization is 1/4, not 1. -/
theorem p4Q2PZ37ABN_originalTemporalCharacter_haar_secondMoment :
    (∫ g : G, (χ g)^2 ∂μ) = (1 / 4 : ℝ) := by
  have h := p4Q2PZ35D4_originalOneLinkHaar_characterQuarter (1 : G)
  change (∫ g : G, (1 - specialUnitaryWilsonPlaquetteEnergy 2 g)^2 ∂μ) =
    (1 / 4 : ℝ)
  simpa only [p4Q2PZ35C_originalOneLinkCharacter, mul_one,
    specialUnitaryWilsonPlaquetteEnergy_inv,
    specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num), sub_zero, pow_two] using h

/-- The actual temporal Wilson partition coefficient on normalized SU(2)
Haar.  No physical transfer operator or posterior is renormalized here. -/
noncomputable def p4Q2PZ37ABN_originalTemporalWilsonMass (b : ℝ) : ℝ :=
  ∫ g : G, k b g ∂μ

/-- The actual temporal Wilson factor tested on its original normalized
fundamental real character. -/
noncomputable def p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment (b : ℝ) : ℝ :=
  ∫ g : G, k b g * χ g ∂μ

/-- The genuine normalized one-link temporal Wilson character coefficient.
Its strict positivity below is proved from the actual Haar integrals. -/
noncomputable def p4Q2PZ37ABN_originalTemporalWilsonCoefficient (b : ℝ) : ℝ :=
  p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b /
    p4Q2PZ37ABN_originalTemporalWilsonMass b

/-- The actual temporal partition coefficient is positive at every real
coupling.  An explicit uniform-in-g lower exponential makes integrability
and strict positivity independent of any point-evaluation argument. -/
theorem p4Q2PZ37ABN_originalTemporalWilsonMass_pos (b : ℝ) :
    0 < p4Q2PZ37ABN_originalTemporalWilsonMass b := by
  have hPoint (g : G) : Real.exp (-2 * |b|) ≤ k b g := by
    change Real.exp (-2 * |b|) ≤
      Real.exp (-b * specialUnitaryWilsonPlaquetteEnergy 2 g)
    apply Real.exp_le_exp.mpr
    have hE0 := specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num : 0 < 2) g
    have hE2 := specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num : 0 < 2) g
    have h₁ := mul_le_mul_of_nonneg_right (le_abs_self b) hE0
    have h₂ := mul_le_mul_of_nonneg_left hE2 (abs_nonneg b)
    nlinarith only [h₁, h₂]
  have hIntegral := integral_mono
    (integrable_const (Real.exp (-2 * |b|)))
    (p4Q2PZ37ABN_temporalFactor_integrable b) hPoint
  have hLower : Real.exp (-2 * |b|) ≤
      p4Q2PZ37ABN_originalTemporalWilsonMass b := by
    simpa [p4Q2PZ37ABN_originalTemporalWilsonMass] using hIntegral
  exact lt_of_lt_of_le (Real.exp_pos _) hLower

/-- The genuine temporal partition coefficient is at most one at
nonnegative coupling, because the original Wilson energy is nonnegative. -/
theorem p4Q2PZ37ABN_originalTemporalWilsonMass_le_one
    (b : ℝ) (hb : 0 ≤ b) :
    p4Q2PZ37ABN_originalTemporalWilsonMass b ≤ 1 := by
  have hPoint (g : G) : k b g ≤ 1 := by
    have h := specialUnitaryWilsonRelativeKernel_mem_Icc
      (by norm_num : 0 < 2) hb (1 : G) g
    simpa only [specialUnitaryWilsonRelativeKernel, inv_one, one_mul] using h.2
  have hIntegral := integral_mono
    (p4Q2PZ37ABN_temporalFactor_integrable b) (integrable_const (1 : ℝ)) hPoint
  simpa [p4Q2PZ37ABN_originalTemporalWilsonMass] using hIntegral

/-- Original pointwise temporal response inequality.  The comparison
subtracts the scalar exp(-b), whose Haar character pairing vanishes.
The two signs of the actual SU(2) character are handled separately. -/
theorem p4Q2PZ37ABN_originalTemporalCharacter_pointwise_lower
    (b : ℝ) (hb : 0 ≤ b) (g : G) :
    b * Real.exp (-2 * b) * (χ g)^2 ≤
      χ g * (k b g - Real.exp (-b)) := by
  let x : ℝ := χ g
  let w : ℝ := k b g
  let a : ℝ := Real.exp (-b)
  let ell : ℝ := Real.exp (-2 * b)
  have hLower : ell ≤ w := by
    have h := specialUnitaryWilsonRelativeKernel_mem_Icc
      (by norm_num : 0 < 2) hb (1 : G) g
    simpa only [specialUnitaryWilsonRelativeKernel, inv_one, one_mul] using h.1
  have hLowerA : ell ≤ a := Real.exp_le_exp.mpr (by linarith)
  have hw : 0 ≤ w := (Real.exp_pos _).le
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have hExpForward : a * Real.exp (b * x) = w := by
    dsimp [a, x, w, p4Q2PZ35C_originalOneLinkCharacter,
      specialUnitaryWilsonBoltzmannCentralFunction]
    rw [← Real.exp_add]
    congr 1
    ring
  have hExpReverse : w * Real.exp (-b * x) = a := by
    dsimp [a, x, w, p4Q2PZ35C_originalOneLinkCharacter,
      specialUnitaryWilsonBoltzmannCentralFunction]
    rw [← Real.exp_add]
    congr 1
    ring
  change b * ell * x^2 ≤ x * (w - a)
  by_cases hx : 0 ≤ x
  · have hExp : a * (1 + b * x) ≤ w := by
      calc
        a * (1 + b * x) ≤ a * Real.exp (b * x) :=
          mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (b * x)]) ha
        _ = w := hExpForward
    have hStep : a * (b * x) ≤ w - a := by nlinarith only [hExp]
    calc
      b * ell * x^2 ≤ b * a * x^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLowerA hb) (sq_nonneg x)
      _ = (a * (b * x)) * x := by ring
      _ ≤ (w - a) * x := mul_le_mul_of_nonneg_right hStep hx
      _ = x * (w - a) := mul_comm _ _
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    have hExp : w * (1 - b * x) ≤ a := by
      calc
        w * (1 - b * x) ≤ w * Real.exp (-b * x) :=
          mul_le_mul_of_nonneg_left (by nlinarith only [Real.add_one_le_exp (-b * x)]) hw
        _ = a := hExpReverse
    have hStep : w - a ≤ w * (b * x) := by nlinarith only [hExp]
    calc
      b * ell * x^2 ≤ b * w * x^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLower hb) (sq_nonneg x)
      _ = x * (w * (b * x)) := by ring
      _ ≤ x * (w - a) := mul_le_mul_of_nonpos_left hStep hx'

/-- Unconditional explicit lower bound for the actual unnormalized
temporal Wilson character moment, obtained by integrating the original
pointwise inequality and exact genuine Haar zero/second moments. -/
theorem p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment_ge_explicit
    (b : ℝ) (hb : 0 ≤ b) :
    b * Real.exp (-2 * b) / 4 ≤
      p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b := by
  have hChi : Integrable χ μ :=
    p4Q2PZ37ABN_character_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSq : Integrable (fun g : G => (χ g)^2) μ :=
    (p4Q2PZ37ABN_character_continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hProduct : Integrable (fun g : G => k b g * χ g) μ :=
    ((p4Q2PZ37ABN_temporalFactor_continuous b).mul
      p4Q2PZ37ABN_character_continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hResidual : Integrable (fun g : G => χ g * (k b g - Real.exp (-b))) μ :=
    (p4Q2PZ37ABN_character_continuous.mul
      ((p4Q2PZ37ABN_temporalFactor_continuous b).sub continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  change b * Real.exp (-2 * b) / 4 ≤ ∫ g : G, k b g * χ g ∂μ
  calc
    b * Real.exp (-2 * b) / 4 =
        ∫ g : G, (b * Real.exp (-2 * b)) * (χ g)^2 ∂μ := by
      rw [integral_const_mul, p4Q2PZ37ABN_originalTemporalCharacter_haar_secondMoment]
      ring
    _ ≤ ∫ g : G, χ g * (k b g - Real.exp (-b)) ∂μ :=
      integral_mono (hSq.const_mul _) hResidual
        (fun g => p4Q2PZ37ABN_originalTemporalCharacter_pointwise_lower b hb g)
    _ = ∫ g : G, (k b g * χ g - Real.exp (-b) * χ g) ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      ring
    _ = (∫ g : G, k b g * χ g ∂μ) -
        Real.exp (-b) * (∫ g : G, χ g ∂μ) := by
      rw [integral_sub hProduct (hChi.const_mul _), integral_const_mul]
    _ = ∫ g : G, k b g * χ g ∂μ := by
      rw [p4Q2PZ35D4_originalOneLinkHaar_characterZero]
      ring

/-- The true normalized temporal Wilson coefficient inherits the same
explicit positive-coupling floor because its actual normalizer is in (0,1]. -/
theorem p4Q2PZ37ABN_originalTemporalWilsonCoefficient_ge_explicit
    (b : ℝ) (hb : 0 ≤ b) :
    b * Real.exp (-2 * b) / 4 ≤
      p4Q2PZ37ABN_originalTemporalWilsonCoefficient b := by
  have hZ := p4Q2PZ37ABN_originalTemporalWilsonMass_pos b
  have hZle := p4Q2PZ37ABN_originalTemporalWilsonMass_le_one b hb
  have hFloor : 0 ≤ b * Real.exp (-2 * b) / 4 := by positivity
  unfold p4Q2PZ37ABN_originalTemporalWilsonCoefficient
  apply (le_div_iff₀ hZ).2
  calc
    (b * Real.exp (-2 * b) / 4) *
        p4Q2PZ37ABN_originalTemporalWilsonMass b ≤
        (b * Real.exp (-2 * b) / 4) * 1 :=
      mul_le_mul_of_nonneg_left hZle hFloor
    _ = b * Real.exp (-2 * b) / 4 := mul_one _
    _ ≤ p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b :=
      p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment_ge_explicit b hb

theorem p4Q2PZ37ABN_originalTemporalWilsonCoefficient_pos
    (b : ℝ) (hb : 0 < b) :
    0 < p4Q2PZ37ABN_originalTemporalWilsonCoefficient b := by
  have hFloor : 0 < b * Real.exp (-2 * b) / 4 := by positivity
  exact lt_of_lt_of_le hFloor
    (p4Q2PZ37ABN_originalTemporalWilsonCoefficient_ge_explicit b hb.le)

/-- An upper bound for the same exact coefficient at every real coupling;
the original real character is at most one and the Wilson weight is positive. -/
theorem p4Q2PZ37ABN_originalTemporalWilsonCoefficient_le_one
    (b : ℝ) :
    p4Q2PZ37ABN_originalTemporalWilsonCoefficient b ≤ 1 := by
  have hProduct : Integrable (fun g : G => k b g * χ g) μ :=
    ((p4Q2PZ37ABN_temporalFactor_continuous b).mul
      p4Q2PZ37ABN_character_continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPoint (g : G) : k b g * χ g ≤ k b g := by
    have hChar : χ g ≤ 1 := by
      unfold p4Q2PZ35C_originalOneLinkCharacter
      linarith [specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num : 0 < 2) g]
    have hWeight : 0 ≤ k b g := (Real.exp_pos _).le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hChar hWeight
  have hIntegral : p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b ≤
      p4Q2PZ37ABN_originalTemporalWilsonMass b :=
    integral_mono hProduct (p4Q2PZ37ABN_temporalFactor_integrable b) hPoint
  unfold p4Q2PZ37ABN_originalTemporalWilsonCoefficient
  apply (div_le_iff₀ (p4Q2PZ37ABN_originalTemporalWilsonMass_pos b)).2
  simpa only [one_mul] using hIntegral

theorem p4Q2PZ37ABN_originalTemporalWilsonMass_continuous :
    Continuous p4Q2PZ37ABN_originalTemporalWilsonMass := by
  have hJoint : Continuous (fun q : ℝ × G => k q.1 q.2) := by
    unfold specialUnitaryWilsonBoltzmannCentralFunction
    exact Real.continuous_exp.comp
      (continuous_fst.neg.mul
        ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp continuous_snd))
  change Continuous (fun b : ℝ => ∫ g : G, k b g ∂μ)
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      («μ» := μ) (f := fun b : ℝ => fun g : G => k b g)
      (s := Set.univ) hJoint isCompact_univ)

theorem p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment_continuous :
    Continuous p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment := by
  have hKernel : Continuous (fun q : ℝ × G => k q.1 q.2) := by
    unfold specialUnitaryWilsonBoltzmannCentralFunction
    exact Real.continuous_exp.comp
      (continuous_fst.neg.mul
        ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp continuous_snd))
  have hJoint : Continuous (fun q : ℝ × G => k q.1 q.2 * χ q.2) :=
    hKernel.mul (p4Q2PZ37ABN_character_continuous.comp continuous_snd)
  change Continuous (fun b : ℝ => ∫ g : G, k b g * χ g ∂μ)
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      («μ» := μ) (f := fun b : ℝ => fun g : G => k b g * χ g)
      (s := Set.univ) hJoint isCompact_univ)

/-- Continuity of the actual original temporal coefficient, without an
assumption of a denominator bound or a continuity premise. -/
theorem p4Q2PZ37ABN_originalTemporalWilsonCoefficient_continuous :
    Continuous p4Q2PZ37ABN_originalTemporalWilsonCoefficient := by
  unfold p4Q2PZ37ABN_originalTemporalWilsonCoefficient
  exact p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment_continuous.div
    p4Q2PZ37ABN_originalTemporalWilsonMass_continuous
    (fun b => (p4Q2PZ37ABN_originalTemporalWilsonMass_pos b).ne')

/-- The coefficient loses its positive amplitude at zero coupling,
consistent with the existing original small-coupling obstruction. -/
theorem p4Q2PZ37ABN_originalTemporalWilsonCoefficient_zero :
    p4Q2PZ37ABN_originalTemporalWilsonCoefficient 0 = 0 := by
  simp [p4Q2PZ37ABN_originalTemporalWilsonCoefficient,
    p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment,
    p4Q2PZ37ABN_originalTemporalWilsonMass,
    specialUnitaryWilsonBoltzmannCentralFunction,
    p4Q2PZ35D4_originalOneLinkHaar_characterZero]

/-- A common explicit lower coefficient on any prescribed positive coupling
interval.  The floor is derived from the actual kernel, not supplied as input. -/
theorem p4Q2PZ37ABN_originalTemporalWilsonCoefficient_uniform_lower
    (b0 B b : ℝ) (hb0 : 0 < b0) (hLower : b0 ≤ b) (hUpper : b ≤ B) :
    b0 * Real.exp (-2 * B) / 4 ≤
      p4Q2PZ37ABN_originalTemporalWilsonCoefficient b := by
  have hb : 0 < b := lt_of_lt_of_le hb0 hLower
  have hExp : Real.exp (-2 * B) ≤ Real.exp (-2 * b) :=
    Real.exp_le_exp.mpr (by linarith)
  have hProduct : b0 * Real.exp (-2 * B) ≤ b * Real.exp (-2 * b) :=
    mul_le_mul hLower hExp (Real.exp_pos _).le hb.le
  have hFloor : b0 * Real.exp (-2 * B) / 4 ≤
      b * Real.exp (-2 * b) / 4 := by linarith
  exact hFloor.trans (p4Q2PZ37ABN_originalTemporalWilsonCoefficient_ge_explicit b hb.le)

theorem p4Q2PZ37ABN_originalTemporalWilsonCoefficient_positive_interval
    (b0 B b : ℝ) (hb0 : 0 < b0) (hLower : b0 ≤ b) (hUpper : b ≤ B) :
    0 < b0 * Real.exp (-2 * B) / 4 ∧
    b0 * Real.exp (-2 * B) / 4 ≤
      p4Q2PZ37ABN_originalTemporalWilsonCoefficient b ∧
    p4Q2PZ37ABN_originalTemporalWilsonCoefficient b ≤ 1 := by
  refine ⟨by positivity, ?_, p4Q2PZ37ABN_originalTemporalWilsonCoefficient_le_one b⟩
  exact p4Q2PZ37ABN_originalTemporalWilsonCoefficient_uniform_lower
    b0 B b hb0 hLower hUpper

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalCharacter_haar_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonMass_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalCharacter_pointwise_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonCoefficient_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonCoefficient_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonCoefficient_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonMass_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonCoefficient_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonCoefficient_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonCoefficient_uniform_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN_originalTemporalWilsonCoefficient_positive_interval

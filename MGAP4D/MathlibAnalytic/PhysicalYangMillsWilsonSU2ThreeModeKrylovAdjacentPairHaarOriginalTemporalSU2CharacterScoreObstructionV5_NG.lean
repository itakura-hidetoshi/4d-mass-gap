import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWeightedSignedFiberLobesV5_NF
import Mathlib.Tactic

/-!
# P4-Q2-NG — exact ORIGINAL SU(2) temporal real-trace character score normal form

NF identified an exact cancellation obstruction in the ACTUAL original
Wilson–Perron two-posterior signed Riesz fiber:
  r(A) = K_b(A,B) Psi(A) = P(A)-N(A),
with P,N > 0 at beta>0. Positive signed-lobe mass is NOT a proof of
nonconstant Psi or physical GI covariance.

NG does not add a new detector, probability measure or artificial
rank hypothesis. Instead it *exactly re-expresses* the ORIGINAL
one-link Wilson factor used in MQ as a product of:

1. its TRUE temporal SU(2) real fundamental-character factor
   exp{b[chi(x^{-1}g)-chi(x^{-1}B_e)]},
   chi(u) = Re tr(u)/2 = 1 - WilsonEnergy(u);
2. its TRUE right-spatial touching-plaquette Wilson action factor,
   independent of the source-side group value x=A(e).

The resulting receiver is the original signed two-interacting-posterior
contrast D times the original positive inverse Perron half-density and
right-spatial Wilson factor, integrated against this SAME temporal
character. In particular, if rho_(e,z)(g) is that true weighted signed
amplitude (NOT an independent-Haar posterior), then

  Psi_(e,z)(A) =
    exp[-b chi(A_e^{-1} B_e)] *
      ∫_SU2 exp[b chi(A_e^{-1} g)] rho_(e,z)(g) dHaar(g).

The proof makes the obstruction **exactly testable** as a character
moment functional equation:
  Q_(H,b,e,z) = 0  iff
  for ALL x in actual SU(2),
    ∫ exp[b chi(x^{-1}g)] rho(g) dHaar(g)
      = Psi_(e,z)(identity) * exp[b chi(x^{-1}B_e)].

Thus a genuine witness violating the equality (not an assumed rank
or invented detector) suffices for positive K_b receiver variance via NC.
Deriving that witness universally at beta>0 requires additional genuine
SU(2) harmonic / Wilson-integral analysis and remains OPEN.
This neither proves nonzero physical GI covariance, H1-C3 nor
continuum 4D Yang–Mills mass gap; never use Dobrushin.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- The literal real normalized SU(2) temporal fundamental character,
using the ORIGINAL Wilson energy and actual SU(2) group multiplication. -/
noncomputable def p4Q2NG_originalSU2TemporalCharacter
    (x g : Gauge) : ℝ :=
  1 - specialUnitaryWilsonPlaquetteEnergy 2 (x⁻¹ * g)

/-- Exact original SU(2) Wilson character is the REAL normalized
matrix trace of the physical temporal holonomy x^{-1} g. -/
theorem p4Q2NG_originalSU2TemporalCharacter_eq_trace
    (x g : Gauge) :
    p4Q2NG_originalSU2TemporalCharacter x g =
      (Matrix.trace (((x⁻¹ * g : Gauge) :
        Matrix (Fin 2) (Fin 2) ℂ))).re / 2 := by
  unfold p4Q2NG_originalSU2TemporalCharacter
    specialUnitaryWilsonPlaquetteEnergy
  ring

/-- The original TRUE right-spatial touching-plaquette Wilson
action increment, kept separate from the original source temporal
SU(2) trace coefficient; no independent spatial model is defined. -/
noncomputable def p4Q2NG_originalRightSpatialWilsonIncrement
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Gauge) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H e,
      (specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update B e g) p) -
       specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p))

/-- The original source-temporal Wilson factor rewritten using the
real SU(2) normalized matrix character. -/
noncomputable def p4Q2NG_originalTemporalCharacterFactor
    (b : ℝ) (x y g : Gauge) : ℝ :=
  Real.exp (b * (p4Q2NG_originalSU2TemporalCharacter x g -
    p4Q2NG_originalSU2TemporalCharacter x y))

/-- Original right-spatial action factor: independent of x=A(e).
It is part of the SAME original positive Wilson local factor. -/
noncomputable def p4Q2NG_originalRightSpatialWilsonFactor
    (H : ℕ) (b : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Gauge) : ℝ :=
  Real.exp (-b * p4Q2NG_originalRightSpatialWilsonIncrement H B e g)

/-- Genuine original Wilson local factor = temporal SU(2) real-trace
character factor TIMES original spatial touching-plaquette factor.
Nothing is truncated, approximated, or replaced. -/
theorem p4Q2NG_originalLocalFactor_eq_temporalCharacter_mul_spatial
    (H : ℕ) (b : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) (g : Gauge) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H 2 b A B e g =
      p4Q2NG_originalTemporalCharacterFactor b (A e) (B e) g *
        p4Q2NG_originalRightSpatialWilsonFactor H b B e g := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    p4Q2NG_originalTemporalCharacterFactor
    p4Q2NG_originalRightSpatialWilsonFactor
    p4Q2NG_originalRightSpatialWilsonIncrement
    p4Q2NG_originalSU2TemporalCharacter
  rw [← Real.exp_add]
  congr 1
  ring

/-- Strict positivity of the two EXACT original spatial/temporal
Wilson Boltzmann factors, with no spatial-volume assumption. -/
theorem p4Q2NG_originalTemporalSpatialFactors_pos
    (H : ℕ) (b : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (x g : Gauge) :
    0 < p4Q2NG_originalTemporalCharacterFactor b x (B e) g ∧
    0 < p4Q2NG_originalRightSpatialWilsonFactor H b B e g :=
  ⟨Real.exp_pos _, Real.exp_pos _⟩

section ActualSignedScore
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "chi" => p4Q2NG_originalSU2TemporalCharacter
local notation "PsiC" => p4Q2MU_originalSignedWilsonScoreContinuous H b hb
local notation "q" => p4Q2NC_originalSignedReceiverLinkScore H b hb
local notation "Q" => p4Q2NC_originalSignedReceiverLinkHaarVariance H b hb
include hb

/-- Exactly the original spatial factor times the ORIGINAL inverse
Perron joint half-density times the TWO genuine interacting Wilson
posterior rows' signed difference. This is an integrand coefficient,
NOT a synthetic posterior law or assumed detector. -/
noncomputable def p4Q2NG_originalSpatialPerronSignedContrast
    (e : Link) (z : Cfg × Cfg) (g : Gauge) : ℝ :=
  p4Q2NG_originalRightSpatialWilsonFactor H b z.2 e g *
    ((continuousJointSqrtDensity H 2 (by norm_num) b hb
       (z.1, Function.update z.2 e g))⁻¹ *
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb z.2 e g)

local notation "rho" => p4Q2NG_originalSpatialPerronSignedContrast H b hb

/-- Exact actual ND signed Wilson–Perron physical fiber in terms
of the actual SU(2) temporal character and original spatial contrast.
The true Wilson kernel and both posterior rows are unchanged. -/
theorem p4Q2NG_originalSignedPhysicalFiber_eq_character_mul_amplitude
    (e : Link) (z : Cfg × Cfg) (A : Cfg) (g : Gauge) :
    p4Q2ND_originalSignedPhysicalFiberIntegrand H b hb e z A g =
      p4Q2NG_originalTemporalCharacterFactor b (A e) (z.2 e) g *
        rho e z g := by
  unfold p4Q2ND_originalSignedPhysicalFiberIntegrand
    p4Q2NG_originalSpatialPerronSignedContrast
  rw [p4Q2NG_originalLocalFactor_eq_temporalCharacter_mul_spatial]
  ring

/-- The genuine actual signed receiver q on original SU(2) is the
temporal character integral against the real original
two-interacting-posterior Wilson–Perron signed coefficient. -/
theorem p4Q2NG_originalSignedReceiverScore_temporalCharacterIntegral
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    q e z x =
      ∫ g : Gauge,
        p4Q2NG_originalTemporalCharacterFactor b x (z.2 e) g *
          rho e z g ∂mu := by
  let A : Cfg := Function.update (fun _ : Link => (1 : Gauge)) e x
  have hA : A e = x := by simp [A]
  change p4Q2MQ_originalSignedLocalFiberProfile H b hb e z A = _
  rw [p4Q2ND_originalSignedProfile_eq_integral_truePhysicalFiber H b hb e z A]
  apply integral_congr_ae
  filter_upwards with g
  rw [p4Q2NG_originalSignedPhysicalFiber_eq_character_mul_amplitude
    H b hb e z A g, hA]

/-- The ORIGINAL non-normalized temporal SU(2) real-character
integral moment. Its coefficient is the exact original signed
Wilson–Perron two-posterior amplitude rho, not a new probability. -/
noncomputable def p4Q2NG_originalTemporalSU2CharacterMoment
    (e : Link) (z : Cfg × Cfg) (x : Gauge) : ℝ :=
  ∫ g : Gauge, Real.exp (b * chi x g) * rho e z g ∂mu

local notation "T" => p4Q2NG_originalTemporalSU2CharacterMoment H b hb

/-- MAIN original SU(2) harmonic-analysis normal form:
the true score is a temporal real-fundamental-character transform
times its exact positive right-boundary normalization factor. -/
theorem p4Q2NG_originalSignedReceiverScore_eq_characterMoment_normalized
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    q e z x =
      Real.exp (-b * chi x (z.2 e)) * T e z x := by
  rw [p4Q2NG_originalSignedReceiverScore_temporalCharacterIntegral H b hb e z x]
  change
    (∫ g : Gauge,
      Real.exp (b * (chi x g - chi x (z.2 e))) * rho e z g ∂mu) =
    Real.exp (-b * chi x (z.2 e)) *
      (∫ g : Gauge, Real.exp (b * chi x g) * rho e z g ∂mu)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with g
  have hExp :
      Real.exp (b * (chi x g - chi x (z.2 e))) =
        Real.exp (-b * chi x (z.2 e)) * Real.exp (b * chi x g) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hExp]
  ring

/-- Exact converse identity:
the actual character moment = a TRUE original right-boundary SU(2)
character exponential times the same actual integrated signed score. -/
theorem p4Q2NG_originalCharacterMoment_eq_exp_mul_signedScore
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    T e z x = Real.exp (b * chi x (z.2 e)) * q e z x := by
  have h := p4Q2NG_originalSignedReceiverScore_eq_characterMoment_normalized
    H b hb e z x
  have hc :
      Real.exp (b * chi x (z.2 e)) *
        Real.exp (-b * chi x (z.2 e)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    T e z x = (1 : ℝ) * T e z x := by ring
    _ = (Real.exp (b * chi x (z.2 e)) *
          Real.exp (-b * chi x (z.2 e))) * T e z x := by rw [hc]
    _ = Real.exp (b * chi x (z.2 e)) * q e z x := by rw [h]; ring

/-- EXACT source-link constancy criterion, avoiding any unproved
rank/injectivity assumption: the character transform MUST be a
multiple of the genuine SU(2) right-boundary exponential function. -/
theorem p4Q2NG_originalSignedScore_constant_iff_characterMoment_proportional
    (e : Link) (z : Cfg × Cfg) :
    (∀ x : Gauge, q e z x = q e z 1) ↔
      (∀ x : Gauge,
        T e z x =
          Real.exp (b * chi x (z.2 e)) * q e z 1) := by
  constructor
  · intro h x
    rw [p4Q2NG_originalCharacterMoment_eq_exp_mul_signedScore H b hb e z x, h x]
  · intro h x
    have hx := p4Q2NG_originalCharacterMoment_eq_exp_mul_signedScore H b hb e z x
    rw [h x] at hx
    exact mul_left_cancel₀ (Real.exp_ne_zero _) hx.symm

/-- Full remaining real analytic obstruction, with NO hidden positivity
assumption. The true SU(2) Haar score variance is zero precisely
when the exact character moment is the right-boundary exponential
times ONE constant from the actual receiver. -/
theorem p4Q2NG_originalSignedScoreHaarVariance_zero_iff_characterMoment_proportional
    (e : Link) (z : Cfg × Cfg) :
    Q e z = 0 ↔
      (∀ x : Gauge,
        T e z x =
          Real.exp (b * chi x (z.2 e)) * q e z 1) := by
  constructor
  · intro hZero
    apply (p4Q2NG_originalSignedScore_constant_iff_characterMoment_proportional
      H b hb e z).mp
    intro x
    exact p4Q2NC_originalSignedReceiverLinkHaarVariance_zero_forces_constant
      H b hb e z hZero x 1
  · intro hMom
    have hConst :=
      (p4Q2NG_originalSignedScore_constant_iff_characterMoment_proportional
        H b hb e z).mpr hMom
    change (∫ g : Gauge,
      (q e z g - ∫ h : Gauge, q e z h ∂mu)^2 ∂mu) = 0
    have hMean : (∫ h : Gauge, q e z h ∂mu) = q e z 1 := by
      calc
        (∫ h : Gauge, q e z h ∂mu) =
            ∫ _h : Gauge, q e z 1 ∂mu := by
              apply integral_congr_ae
              filter_upwards with h
              exact hConst h
        _ = q e z 1 := by simp
    calc
      (∫ g : Gauge, (q e z g -
          ∫ h : Gauge, q e z h ∂mu)^2 ∂mu) =
          ∫ _g : Gauge, (0 : ℝ) ∂mu := by
            apply integral_congr_ae
            filter_upwards with g
            rw [hMean, hConst g]
            simp
      _ = 0 := by simp

/-- A constructive criterion, rather than fabricated SU(2)
nondegeneracy: a WITNESSED violation of the exact ORIGINAL character
moment proportionality is equivalent to strictly positive Haar
variance of the true integrated two-posterior signed receiver score.
Finding that witness at all positive beta is the remaining task. -/
theorem p4Q2NG_originalSignedScoreHaarVariance_pos_iff_characterMoment_witness
    (e : Link) (z : Cfg × Cfg) :
    0 < Q e z ↔
      ∃ x : Gauge,
        T e z x ≠ Real.exp (b * chi x (z.2 e)) * q e z 1 := by
  constructor
  · intro hPos
    by_contra hNo
    push_neg at hNo
    have hZero :=
      (p4Q2NG_originalSignedScoreHaarVariance_zero_iff_characterMoment_proportional
        H b hb e z).2 hNo
    linarith
  · rintro ⟨x, hx⟩
    have hNe : Q e z ≠ 0 := by
      intro hZero
      exact hx
        ((p4Q2NG_originalSignedScoreHaarVariance_zero_iff_characterMoment_proportional
          H b hb e z).1 hZero x)
    have hNonneg :=
      p4Q2NC_originalSignedReceiverLinkHaarVariance_nonneg H b hb e z
    exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

end ActualSignedScore
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalSU2TemporalCharacter_eq_trace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalLocalFactor_eq_temporalCharacter_mul_spatial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalTemporalSpatialFactors_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalSignedPhysicalFiber_eq_character_mul_amplitude
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalSignedReceiverScore_temporalCharacterIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalSignedReceiverScore_eq_characterMoment_normalized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalCharacterMoment_eq_exp_mul_signedScore
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalSignedScore_constant_iff_characterMoment_proportional
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalSignedScoreHaarVariance_zero_iff_characterMoment_proportional
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NG_originalSignedScoreHaarVariance_pos_iff_characterMoment_witness

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedPosteriorL1LobesV5_ND
import Mathlib.Tactic

/-!
# P4-Q2-NE — EXACT equal positive/negative ORIGINAL posterior Haar mass

ND proved that BOTH actual interacting-Wilson conditional posterior
density rows are normalized and their difference D has Haar mean zero,
H-independent strictly positive Haar-L1 mass at every beta>0, and
both signs through the genuine signed SU(2) physical receiver fiber.

NE decomposes EXACTLY that SAME signed physical two-posterior density
contrast into its positive and negative real parts:
  D_+(g) = max(D(g), 0), D_-(g) = max(-D(g), 0).

Because both authentic original posterior rows have total Haar mass
one, their positive and negative difference-masses coincide:
  int D_+ = int D_- = (1/2) int |D|.

Combining with the previously formalized genuine quantitative ND
Haar-L1 bound gives TWO simultaneous H-INDEPENDENT signed-lobe floors:
  exp(-32b)*b²*V_temporal <=
    2*(exp(16b)-exp(-16b)) * int D_+
  exp(-32b)*b²*V_temporal <=
    2*(exp(16b)-exp(-16b)) * int D_-
and both integrals are strictly positive at all beta>0.

These are real original SU(2) Haar source-posterior contrast integrals,
not replacement independent Haar posteriors or a synthetic detector.
Weights in the ORIGINAL signed receiver transform could still cancel
after applying the real Wilson local factor and Perron half-density.
No receiver nonconstancy, GI covariance nonzero, uniform GI coercivity,
H1-C3 strong limit or continuum mass gap is claimed.

Pinned mathlib, no Dobrushin, new axiom, rank hypothesis, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NE_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NE_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NE_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NE_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NE_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Elementary real algebra: the positive part is half of
the sum of the point value and its absolute value. -/
private theorem p4Q2NE_max_pos_eq_abs (x : ℝ) :
    max x 0 = (x + |x|) / 2 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, abs_of_nonpos h]
    ring
  · rw [max_eq_left h, abs_of_nonneg h]
    ring

/-- Elementary real algebra: the negative part is half of
the absolute value minus the original signed value. -/
private theorem p4Q2NE_max_neg_eq_abs (x : ℝ) :
    max (-x) 0 = (|x| - x) / 2 := by
  rw [p4Q2NE_max_pos_eq_abs, abs_neg]
  ring

section SignedPosteriorHaarMass
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "D" =>
  p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
include hb

/-- Haar mass of the strictly positive lobe of the SAME authentic
normalized two-interacting-Wilson-posterior signed density contrast. -/
noncomputable def p4Q2NE_originalPosteriorPositiveLobeHaarMass
    (right : Cfg) (e : Link) : ℝ :=
  ∫ g : Gauge, max (D right e g) 0 ∂mu

/-- Haar mass of the strictly negative lobe of the SAME authentic
normalized two-interacting-Wilson-posterior signed density contrast. -/
noncomputable def p4Q2NE_originalPosteriorNegativeLobeHaarMass
    (right : Cfg) (e : Link) : ℝ :=
  ∫ g : Gauge, max (-(D right e g)) 0 ∂mu

local notation "PosMass" => p4Q2NE_originalPosteriorPositiveLobeHaarMass H b hb
local notation "NegMass" => p4Q2NE_originalPosteriorNegativeLobeHaarMass H b hb

/-- Exact positive signed lobe mass, half the absolute Haar-L1
contrast mass, because the TWO original posterior rows each normalize
to one. No unsigned reinterpretation of the signed detector. -/
theorem p4Q2NE_originalPosteriorPositiveLobeHaarMass_eq_half_abs
    (right : Cfg) (e : Link) :
    PosMass right e = (∫ g : Gauge, |D right e g| ∂mu) / 2 := by
  have hD :=
    p4Q2ND_originalPosteriorContrast_continuous H b hb right e
  have hIntD : Integrable (D right e) mu :=
    hD.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAbsInt : Integrable (fun g : Gauge => |D right e g|) mu :=
    hD.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZero :=
    p4Q2ND_originalPosteriorContrast_Haar_integral_zero H b hb right e
  change (∫ g : Gauge, max (D right e g) 0 ∂mu) =
    (∫ g : Gauge, |D right e g| ∂mu) / 2
  calc
    (∫ g : Gauge, max (D right e g) 0 ∂mu) =
        ∫ g : Gauge, (D right e g + |D right e g|) / 2 ∂mu := by
          apply integral_congr_ae
          filter_upwards with g
          exact p4Q2NE_max_pos_eq_abs (D right e g)
    _ = ((∫ g : Gauge, D right e g ∂mu) +
          (∫ g : Gauge, |D right e g| ∂mu)) / 2 := by
          rw [integral_div, integral_add hIntD hAbsInt]
    _ = (∫ g : Gauge, |D right e g| ∂mu) / 2 := by
          rw [hZero]
          ring

/-- Exact negative signed lobe Haar mass, the SAME half of the
original two-posterior absolute density contrast mass. -/
theorem p4Q2NE_originalPosteriorNegativeLobeHaarMass_eq_half_abs
    (right : Cfg) (e : Link) :
    NegMass right e = (∫ g : Gauge, |D right e g| ∂mu) / 2 := by
  have hD :=
    p4Q2ND_originalPosteriorContrast_continuous H b hb right e
  have hIntD : Integrable (D right e) mu :=
    hD.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAbsInt : Integrable (fun g : Gauge => |D right e g|) mu :=
    hD.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZero :=
    p4Q2ND_originalPosteriorContrast_Haar_integral_zero H b hb right e
  change (∫ g : Gauge, max (-(D right e g)) 0 ∂mu) =
    (∫ g : Gauge, |D right e g| ∂mu) / 2
  calc
    (∫ g : Gauge, max (-(D right e g)) 0 ∂mu) =
        ∫ g : Gauge, (|D right e g| - D right e g) / 2 ∂mu := by
          apply integral_congr_ae
          filter_upwards with g
          exact p4Q2NE_max_neg_eq_abs (D right e g)
    _ = ((∫ g : Gauge, |D right e g| ∂mu) -
          (∫ g : Gauge, D right e g ∂mu)) / 2 := by
          rw [integral_div, integral_sub hAbsInt hIntD]
    _ = (∫ g : Gauge, |D right e g| ∂mu) / 2 := by
          rw [hZero]
          ring

/-- The genuine signed two-Wilson-posterior contrast has EXACTLY
EQUAL positive and negative Haar masses at every finite volume. -/
theorem p4Q2NE_originalPosteriorSignedLobeHaarMass_balance
    (right : Cfg) (e : Link) :
    PosMass right e = NegMass right e := by
  rw [p4Q2NE_originalPosteriorPositiveLobeHaarMass_eq_half_abs,
    p4Q2NE_originalPosteriorNegativeLobeHaarMass_eq_half_abs]

/-- The POSITIVE lobe of the original signed two-posterior density
has an explicit H-independent quantitative HAAR mass lower bound
at every b>=0, derived from ND's proven L1 floor. -/
theorem p4Q2NE_originalPosteriorPositiveLobeHaarMass_uniform_lower
    (right : Cfg) (e : Link) :
    Real.exp (-32*b) *
        (b^2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ≤
      (2 * (Real.exp (16*b) - Real.exp (-16*b))) * PosMass right e := by
  have hL1 :=
    p4Q2ND_originalPosteriorContrast_HaarL1_uniform_lower
      H b hb right e
  calc
    Real.exp (-32*b) *
        (b^2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ≤
      (Real.exp (16*b) - Real.exp (-16*b)) *
        (∫ g : Gauge, |D right e g| ∂mu) := hL1
    _ = (2 * (Real.exp (16*b) - Real.exp (-16*b))) * PosMass right e := by
      rw [p4Q2NE_originalPosteriorPositiveLobeHaarMass_eq_half_abs]
      ring

/-- The NEGATIVE lobe has the SAME H-independent quantitative Haar
mass lower bound at every b>=0, without any independent-posterior or
physical detector replacement. -/
theorem p4Q2NE_originalPosteriorNegativeLobeHaarMass_uniform_lower
    (right : Cfg) (e : Link) :
    Real.exp (-32*b) *
        (b^2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ≤
      (2 * (Real.exp (16*b) - Real.exp (-16*b))) * NegMass right e := by
  rw [← p4Q2NE_originalPosteriorSignedLobeHaarMass_balance H b hb right e]
  exact p4Q2NE_originalPosteriorPositiveLobeHaarMass_uniform_lower
    H b hb right e

/-- At every genuinely positive beta the TWO original signed lobes
carry STRICTLY POSITIVE Haar mass, independently of finite H,e,right.
This is a posterior statement, not an integrated signed GI score claim. -/
theorem p4Q2NE_originalPosteriorBothLobeHaarMass_pos_of_beta_pos
    (bpos : 0 < b) (right : Cfg) (e : Link) :
    0 < PosMass right e ∧ 0 < NegMass right e := by
  let C : ℝ := Real.exp (16*b) - Real.exp (-16*b)
  have hC : 0 < C := by
    dsimp [C]
    apply sub_pos.mpr
    exact Real.exp_lt_exp.mpr (by nlinarith [bpos])
  have hDelta :
      0 < Real.exp (-32*b) *
        (b^2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) :=
    mul_pos (Real.exp_pos _)
      (mul_pos (pow_pos bpos 2)
        p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos)
  have hLower :=
    p4Q2NE_originalPosteriorPositiveLobeHaarMass_uniform_lower H b hb right e
  have hProdPos : 0 < (2*C) * PosMass right e := by
    exact lt_of_lt_of_le hDelta hLower
  have hPos : 0 < PosMass right e := by
    by_contra hNot
    have hMass : PosMass right e ≤ 0 := le_of_not_gt hNot
    have hProdNonpos : (2*C) * PosMass right e ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) hC.le) hMass
    exact (not_le_of_gt hProdPos) hProdNonpos
  exact ⟨hPos, by
    rw [← p4Q2NE_originalPosteriorSignedLobeHaarMass_balance H b hb right e]
    exact hPos⟩

end SignedPosteriorHaarMass
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NE_originalPosteriorPositiveLobeHaarMass_eq_half_abs
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NE_originalPosteriorNegativeLobeHaarMass_eq_half_abs
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NE_originalPosteriorSignedLobeHaarMass_balance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NE_originalPosteriorPositiveLobeHaarMass_uniform_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NE_originalPosteriorNegativeLobeHaarMass_uniform_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NE_originalPosteriorBothLobeHaarMass_pos_of_beta_pos

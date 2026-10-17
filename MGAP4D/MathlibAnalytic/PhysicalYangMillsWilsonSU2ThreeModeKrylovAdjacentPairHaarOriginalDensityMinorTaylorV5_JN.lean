import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorCenteredLogTangentV5_JM
import Mathlib.Tactic

/-!
# P4-Q2-JN: ORIGINAL interacting Wilson posterior density minor and actual Taylor tangent

Retain the ORIGINAL two normalized interacting-Wilson conditional
posterior densities at the actual SU(2) left boundaries, with the
original Perron physical vacuum. The full four-density 2x2 MINOR
at two inserted SU(2) right-link values is exactly

  [exp (-b * (D(g)-D(h))) - 1] * p0_b(h) * p1_b(g).

The equality is proved by exponentiating FR/GA's exact physical
log-posterior cross ratio, using positivity of both genuine posterior
densities (FK); no assumed derivative of the vacuum is involved.

The original SU(2) Wilson plaquette energies have true range [0,2].
Consequently |D(g)-D(h)|<=4; at 0<=b<=1/4 the pinned mathlib
exp Taylor remainder yields an actual second-order bound on the
genuine posterior 2x2 minor. The density product remains the original
interacting posterior factor, with its independently proved FK envelope.

These are genuinely UNLOGGED physical posterior minor results,
not merely another log-odds identity. They give a quantitative
first-order temporal Wilson coefficient without the illicit assumption
that either posterior density or the Perron vacuum is differentiable
in b. The spatial-source JK GI minor nonzero context, full unlogged
posterior Haar-L2 derivative, H1-C3 and continuum mass gap remain OPEN.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast

/-- First ACTUAL interacting Wilson density: identity left SU(2) boundary. -/
noncomputable def p4Q2JN_originalPosteriorIdentityDensity
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) (g : Gauge) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) b hb (originalWilsonExplicitIdentityBoundary H) right e g

/-- Second ACTUAL interacting Wilson density: left pi-rotation at link e. -/
noncomputable def p4Q2JN_originalPosteriorPiDensity
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) (g : Gauge) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) b hb (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g

/-- The TRUE normalized posterior density 2x2 minor at two physical
SU(2) right insertions g,h, without any artificial conditional law. -/
noncomputable def p4Q2JN_originalPosteriorTwoPointMinor
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) (g h : Gauge) : ℝ :=
  p4Q2JN_originalPosteriorIdentityDensity H b hb right e g *
      p4Q2JN_originalPosteriorPiDensity H b hb right e h -
    p4Q2JN_originalPosteriorIdentityDensity H b hb right e h *
      p4Q2JN_originalPosteriorPiDensity H b hb right e g

/-- Both authentic normalized Wilson densities are strictly positive,
even though their physical vacuum is not differentiated. -/
theorem p4Q2JN_originalPosteriorDensity_pos
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) (g : Gauge) :
    0 < p4Q2JN_originalPosteriorIdentityDensity H b hb right e g ∧
    0 < p4Q2JN_originalPosteriorPiDensity H b hb right e g := by
  constructor
  · exact (Real.exp_pos _).trans_le
      (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
        H 2 (by norm_num) b hb
        (originalWilsonExplicitIdentityBoundary H) right e g).1
  · exact (Real.exp_pos _).trans_le
      (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
        H 2 (by norm_num) b hb
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g).1

/-- Exponentiating the ORIGINAL normalized posterior log crossing
produces the exact physical two-point UNLOGGED density minor. -/
theorem p4Q2JN_originalPosteriorMinor_exact_temporalFactor
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) (g h : Gauge) :
    p4Q2JN_originalPosteriorTwoPointMinor H b hb right e g h =
      (Real.exp (-b * (D g - D h)) - 1) *
        (p4Q2JN_originalPosteriorIdentityDensity H b hb right e h *
          p4Q2JN_originalPosteriorPiDensity H b hb right e g) := by
  let p0 := p4Q2JN_originalPosteriorIdentityDensity H b hb right e
  let p1 := p4Q2JN_originalPosteriorPiDensity H b hb right e
  let u : ℝ := p0 g * p1 h
  let v : ℝ := p0 h * p1 g
  have h0g := (p4Q2JN_originalPosteriorDensity_pos H b hb right e g).1
  have h1g := (p4Q2JN_originalPosteriorDensity_pos H b hb right e g).2
  have h0h := (p4Q2JN_originalPosteriorDensity_pos H b hb right e h).1
  have h1h := (p4Q2JN_originalPosteriorDensity_pos H b hb right e h).2
  have hu : 0 < u := mul_pos h0g h1h
  have hv : 0 < v := mul_pos h0h h1g
  have hCross := p4Q2GA_originalSU2WilsonPosteriorLogContrast_relative_exact
    H b hb right e g h
  have hLog : Real.log u - Real.log v = -b * (D g - D h) := by
    dsimp [u, v]
    rw [Real.log_mul h0g.ne' h1h.ne', Real.log_mul h0h.ne' h1g.ne']
    change (Real.log (p0 g) - Real.log (p1 g)) -
      (Real.log (p0 h) - Real.log (p1 h)) =
      -b * (D g - D h) at hCross
    linarith [hCross]
  have hExp := congrArg Real.exp hLog
  rw [Real.exp_sub, Real.exp_log hu, Real.exp_log hv] at hExp
  have hFactor : u = Real.exp (-b * (D g - D h)) * v := by
    apply (div_eq_iff hv.ne').mp hExp
  change u - v = (Real.exp (-b * (D g - D h)) - 1) * v
  rw [hFactor]
  ring

/-- Original temporal SU(2) Wilson energy difference has a true
global four-unit oscillation bound, independent of finite lattice. -/
theorem p4Q2JN_temporalWilsonDifference_abs_le_four (g h : Gauge) :
    |D g - D h| ≤ (4 : ℝ) := by
  let R := specialUnitaryTwoRotation Real.pi
  have hg0 : 0 ≤ specialUnitaryWilsonPlaquetteEnergy 2 g :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) g
  have hg2 : specialUnitaryWilsonPlaquetteEnergy 2 g ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) g
  have hRg0 : 0 ≤ specialUnitaryWilsonPlaquetteEnergy 2 (R⁻¹ * g) :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) (R⁻¹ * g)
  have hRg2 : specialUnitaryWilsonPlaquetteEnergy 2 (R⁻¹ * g) ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) (R⁻¹ * g)
  have hh0 : 0 ≤ specialUnitaryWilsonPlaquetteEnergy 2 h :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) h
  have hh2 : specialUnitaryWilsonPlaquetteEnergy 2 h ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) h
  have hRh0 : 0 ≤ specialUnitaryWilsonPlaquetteEnergy 2 (R⁻¹ * h) :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) (R⁻¹ * h)
  have hRh2 : specialUnitaryWilsonPlaquetteEnergy 2 (R⁻¹ * h) ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) (R⁻¹ * h)
  apply abs_le.mpr
  dsimp [D, p4Q2FZ_originalSU2TemporalWilsonContrast]
  constructor <;> dsimp [R] at *
  · linarith
  · linarith

/-- Verified FK envelopes for the product of the TWO actual interacting
Wilson posterior densities in the physical two-context minor. -/
theorem p4Q2JN_originalPosteriorCrossProduct_bounds
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) (g h : Gauge) :
    Real.exp (-32 * b) ≤
      p4Q2JN_originalPosteriorIdentityDensity H b hb right e h *
        p4Q2JN_originalPosteriorPiDensity H b hb right e g ∧
      p4Q2JN_originalPosteriorIdentityDensity H b hb right e h *
        p4Q2JN_originalPosteriorPiDensity H b hb right e g ≤
          Real.exp (32 * b) := by
  let p0 := p4Q2JN_originalPosteriorIdentityDensity H b hb right e
  let p1 := p4Q2JN_originalPosteriorPiDensity H b hb right e
  have h0 := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) b hb (originalWilsonExplicitIdentityBoundary H) right e h
  have h1 := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) b hb (p4Q2FQ_originalSU2LeftPiRotationAtLink H e)
      right e g
  have h0pos := (p4Q2JN_originalPosteriorDensity_pos H b hb right e h).1
  have h1pos := (p4Q2JN_originalPosteriorDensity_pos H b hb right e g).2
  have hlo : Real.exp (-16 * b) * Real.exp (-16 * b) ≤ p0 h * p1 g :=
    mul_le_mul h0.1 h1.1 (Real.exp_nonneg _) h0pos.le
  have hhi : p0 h * p1 g ≤ Real.exp (16 * b) * Real.exp (16 * b) :=
    mul_le_mul h0.2 h1.2 h1pos.le (Real.exp_nonneg _)
  constructor
  · calc
      Real.exp (-32 * b) = Real.exp (-16 * b) * Real.exp (-16 * b) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ p0 h * p1 g := hlo
  · calc
      p0 h * p1 g ≤ Real.exp (16 * b) * Real.exp (16 * b) := hhi
      _ = Real.exp (32 * b) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- Pinned mathlib's genuine quadratic real exponential Taylor bound
applied to the ORIGINAL UNLOGGED physical posterior cross-density
minor, not a surrogate or an assumed derivative of posterior rows. -/
theorem p4Q2JN_originalPosteriorMinor_weightedTaylor
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) (g h : Gauge)
    (hSmall : ‖-b * (D g - D h)‖ ≤ 1) :
    ‖p4Q2JN_originalPosteriorTwoPointMinor H b hb right e g h -
        (-b * (D g - D h)) *
          (p4Q2JN_originalPosteriorIdentityDensity H b hb right e h *
            p4Q2JN_originalPosteriorPiDensity H b hb right e g)‖ ≤
      (b * (D g - D h)) ^ 2 *
        (p4Q2JN_originalPosteriorIdentityDensity H b hb right e h *
          p4Q2JN_originalPosteriorPiDensity H b hb right e g) := by
  let x : ℝ := -b * (D g - D h)
  let v : ℝ := p4Q2JN_originalPosteriorIdentityDensity H b hb right e h *
    p4Q2JN_originalPosteriorPiDensity H b hb right e g
  have hv : 0 ≤ v := (mul_pos
    (p4Q2JN_originalPosteriorDensity_pos H b hb right e h).1
    (p4Q2JN_originalPosteriorDensity_pos H b hb right e g).2).le
  have ht : ‖Real.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 :=
    Real.norm_exp_sub_one_sub_id_le hSmall
  rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]
  change ‖(Real.exp x - 1) * v - x * v‖ ≤ (-x) ^ 2 * v
  calc
    ‖(Real.exp x - 1) * v - x * v‖ =
        ‖Real.exp x - 1 - x‖ * ‖v‖ := by
      rw [← sub_mul, norm_mul]
    _ ≤ ‖x‖ ^ 2 * ‖v‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    _ = (-x) ^ 2 * v := by
      simp [Real.norm_eq_abs, abs_of_nonneg hv, sq_abs]

/-- Coupling-only condition 0<=b<=1/4 gives the actual Taylor radius
simultaneously for EVERY real SU(2) insertion pair. -/
theorem p4Q2JN_originalSU2_smallCoupling_TaylorRadius
    (b : ℝ) (hb : 0 ≤ b) (hsmall : b ≤ 1 / 4) (g h : Gauge) :
    ‖-b * (D g - D h)‖ ≤ 1 := by
  have hd := p4Q2JN_temporalWilsonDifference_abs_le_four g h
  calc
    ‖-b * (D g - D h)‖ = b * |D g - D h| := by
      simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]
    _ ≤ b * 4 := mul_le_mul_of_nonneg_left hd hb
    _ ≤ 1 := by linarith

/-- Universal small-positive frozen-coupling O(b²) bound for the true
Wilson density minor after retaining its actual interacting density
product as the leading coefficient. -/
theorem p4Q2JN_originalPosteriorMinor_weightedTaylor_uniform
    (b : ℝ) (hb : 0 ≤ b) (hsmall : b ≤ 1 / 4)
    (right : Cfg) (e : Link) (g h : Gauge) :
    ‖p4Q2JN_originalPosteriorTwoPointMinor H b hb right e g h -
        (-b * (D g - D h)) *
          (p4Q2JN_originalPosteriorIdentityDensity H b hb right e h *
            p4Q2JN_originalPosteriorPiDensity H b hb right e g)‖ ≤
      (b * (D g - D h)) ^ 2 * Real.exp (32 * b) := by
  have ht := p4Q2JN_originalPosteriorMinor_weightedTaylor
    H b hb right e g h
    (p4Q2JN_originalSU2_smallCoupling_TaylorRadius b hb hsmall g h)
  have hu := (p4Q2JN_originalPosteriorCrossProduct_bounds H b hb right e g h).2
  exact le_trans ht (mul_le_mul_of_nonneg_left hu (sq_nonneg _))

/-- An ACTUAL SU(2) two-point posterior density minor is NONZERO
whenever its genuine temporal Wilson crossing energies differ and
the frozen physical Wilson coupling is positive. No artificial frame. -/
theorem p4Q2JN_originalPosteriorMinor_ne_of_temporalDifference_ne
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) (g h : Gauge)
    (hd : D g ≠ D h) :
    p4Q2JN_originalPosteriorTwoPointMinor H b hb.le right e g h ≠ 0 := by
  rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]
  have hx : -b * (D g - D h) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hb.ne') (sub_ne_zero.mpr hd)
  have he : Real.exp (-b * (D g - D h)) - 1 ≠ 0 := by
    intro h
    have hEq : Real.exp (-b * (D g - D h)) = 1 := sub_eq_zero.mp h
    exact hx (Real.exp_eq_one_iff.mp hEq)
  exact mul_ne_zero he (mul_ne_zero
    (p4Q2JN_originalPosteriorDensity_pos H b hb.le right e h).1.ne'
    (p4Q2JN_originalPosteriorDensity_pos H b hb.le right e g).2.ne')

/-- The two explicit physical SU(2) inserted values give a positive
genuine density minor for EVERY positive frozen coupling. -/
theorem p4Q2JN_originalPosteriorMinor_one_pi_pos
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    0 < p4Q2JN_originalPosteriorTwoPointMinor H b hb.le right e
      (1 : Gauge) (specialUnitaryTwoRotation Real.pi) := by
  rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]
  rw [p4Q2FZ_originalSU2TemporalWilsonContrast_one,
      p4Q2FZ_originalSU2TemporalWilsonContrast_rotation]
  have hExp : 0 < Real.exp (4 * b) - 1 := by
    apply sub_pos.mpr
    exact Real.one_lt_exp_iff.mpr (by linarith)
  convert mul_pos hExp
    (mul_pos (p4Q2JN_originalPosteriorDensity_pos H b hb.le right e
      (specialUnitaryTwoRotation Real.pi)).1
    (p4Q2JN_originalPosteriorDensity_pos H b hb.le right e 1).2) using 1 <;> ring

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN_originalPosteriorDensity_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN_originalPosteriorMinor_exact_temporalFactor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN_temporalWilsonDifference_abs_le_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN_originalPosteriorCrossProduct_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN_originalPosteriorMinor_weightedTaylor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN_originalSU2_smallCoupling_TaylorRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN_originalPosteriorMinor_weightedTaylor_uniform
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN_originalPosteriorMinor_ne_of_temporalDifference_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JN_originalPosteriorMinor_one_pi_pos

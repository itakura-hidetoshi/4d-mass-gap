import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointRealFeatureCrossingV5_KH
import Mathlib.Tactic

/-!
# P4-Q2-KI — strict 2×2 original Wilson joint-density determinant

An exact physical two-point witness for the original interacting
Perron/Wilson joint kernel: choose all-identity left slice, all-pi-rotation
left slice, and insert identity/pi-rotation into one actual right link.
The KG/KH four-corner ratio is exp(4b), hence >1 for every b>0.

This is a concrete, theorem-derived rank-two witness for the genuine
joint density (NOT a rank assumption), and a finite two-point
separation step toward full SU(2) exponential-convolution injectivity.
No posterior substitution, sorry, new axioms, H1-C3 or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num)

private noncomputable def p4Q2KI_pi : Gauge :=
  specialUnitaryTwoRotation Real.pi

/-- The original SU(2) Wilson four-corner energy is exactly -4 for
the genuine identity/pi physical crossing pair. -/
theorem p4Q2KI_originalSU2_identity_pi_crossingEnergy_eq_neg_four :
    ((specialUnitaryWilsonPlaquetteEnergy 2
          (((1 : Gauge)⁻¹) * (1 : Gauge)) -
        specialUnitaryWilsonPlaquetteEnergy 2
          (((1 : Gauge)⁻¹) * p4Q2KI_pi)) -
      (specialUnitaryWilsonPlaquetteEnergy 2
          ((p4Q2KI_pi)⁻¹ * (1 : Gauge)) -
        specialUnitaryWilsonPlaquetteEnergy 2
          ((p4Q2KI_pi)⁻¹ * p4Q2KI_pi))) = -4 := by
  simp only [inv_one, one_mul, mul_one, inv_mul_cancel]
  rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
  rw [specialUnitaryWilsonPlaquetteEnergy_inv]
  dsimp only [p4Q2KI_pi]
  rw [originalWilsonExplicitPiRotation_energy_eq_two]
  norm_num

/-- The actual original Wilson crossing exponent at the physical
identity/pi pair is strictly positive at every positive coupling. -/
theorem p4Q2KI_originalSU2_identity_pi_crossingExp_gt_one
    (b : ℝ) (hb : 0 < b) :
    1 < Real.exp (4 * b) := by
  have h4 : 0 < 4 * b := mul_pos (by norm_num) hb
  simpa using (Real.exp_lt_exp.mpr h4)

/-- True Perron/Wilson joint density has a strictly positive 2×2
minor for actual SU(2) identity/pi left slices and right insertions.
No arbitrary rank assumption and no independent-Haar posterior. -/
theorem p4Q2KI_originalJoint_identity_pi_strictTwoPointMinor
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    rho b hb.le ((fun _ : Link => (1 : Gauge)),
      Function.update right e (1 : Gauge)) *
      rho b hb.le ((fun _ : Link => p4Q2KI_pi),
        Function.update right e p4Q2KI_pi) >
    rho b hb.le ((fun _ : Link => (1 : Gauge)),
      Function.update right e p4Q2KI_pi) *
      rho b hb.le ((fun _ : Link => p4Q2KI_pi),
        Function.update right e (1 : Gauge)) := by
  let L₀ : Cfg := fun _ => (1 : Gauge)
  let Lπ : Cfg := fun _ => p4Q2KI_pi
  let Bg : Cfg := Function.update right e (1 : Gauge)
  let Bh : Cfg := Function.update right e p4Q2KI_pi
  let x : ℝ := rho b hb.le (L₀, Bh) * rho b hb.le (Lπ, Bg)
  have hx : 0 < x := mul_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb.le (L₀, Bh))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb.le (Lπ, Bg))
  have hFour :=
    p4Q2KG_originalJointDensityFourCorner_eq_temporalExp
      H b hb.le L₀ Lπ right e 1 p4Q2KI_pi
  have hEnergy :
      ((specialUnitaryWilsonPlaquetteEnergy 2 ((L₀ e)⁻¹ * 1) -
        specialUnitaryWilsonPlaquetteEnergy 2 ((L₀ e)⁻¹ * p4Q2KI_pi)) -
      (specialUnitaryWilsonPlaquetteEnergy 2 ((Lπ e)⁻¹ * 1) -
        specialUnitaryWilsonPlaquetteEnergy 2 ((Lπ e)⁻¹ * p4Q2KI_pi))) = -4 := by
    simpa [L₀, Lπ] using
      p4Q2KI_originalSU2_identity_pi_crossingEnergy_eq_neg_four
  rw [hEnergy] at hFour
  have hFactor : Real.exp (-b * (-4)) = Real.exp (4 * b) := by
    congr 1
    ring
  rw [hFactor] at hFour
  have hExp : 1 < Real.exp (4 * b) :=
    p4Q2KI_originalSU2_identity_pi_crossingExp_gt_one b hb
  have hStrict : x < Real.exp (4 * b) * x :=
    (lt_mul_iff_one_lt_left hx).2 hExp
  change rho b hb.le (L₀, Bg) * rho b hb.le (Lπ, Bh) > x
  rw [hFour]
  exact hStrict

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KI_originalSU2_identity_pi_crossingEnergy_eq_neg_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KI_originalSU2_identity_pi_crossingExp_gt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KI_originalJoint_identity_pi_strictTwoPointMinor

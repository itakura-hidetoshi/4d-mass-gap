import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointRealFeatureCrossingV5_KH
import Mathlib.Tactic

/-!
# P4-Q2-KY — true physical Perron joint half-density four-corner crossing

KH establishes the exact original finite-volume interacting Wilson/Perron
joint DENSITY four-corner relation as a real SU(2) feature exponential.
Here strict positivity transports it to its unique positive square
root, with precisely HALF the exponent: beta/4, not beta/2.

Both the pointwise positive density square roots and the literal
original continuous joint half-density used by GN/JQ/KX are retained.
This is the algebraic interface for the forthcoming genuine
left-boundary factorization. No Wilson-section convolution is
identified with a GI expectation gap here. No independent posterior,
rank axiom, sorry/admit, H1-C3, or continuum claim is introduced.
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
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num)
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num)

/-- For arbitrary original left physical boundaries, right-link insertions
and every beta>=0, the exact true Perron joint positive square-root
four-corner identity has exponential coupling beta/4. -/
theorem p4Q2KY_originalJointDensitySqrtFourCorner_eq_realFeatureExponential
    (b : ℝ) (hb : 0 ≤ b)
    (left₁ left₂ right : Cfg) (e : Link) (g h : Gauge) :
    Real.sqrt (rho b hb (left₁, Function.update right e g)) *
        Real.sqrt (rho b hb (left₂, Function.update right e h)) =
      Real.exp ((b / 4) *
        inner ℝ (Phi (left₁ e) - Phi (left₂ e)) (Phi g - Phi h)) *
        (Real.sqrt (rho b hb (left₁, Function.update right e h)) *
          Real.sqrt (rho b hb (left₂, Function.update right e g))) := by
  let r11 : ℝ := rho b hb (left₁, Function.update right e g)
  let r12 : ℝ := rho b hb (left₁, Function.update right e h)
  let r21 : ℝ := rho b hb (left₂, Function.update right e g)
  let r22 : ℝ := rho b hb (left₂, Function.update right e h)
  let d : ℝ := inner ℝ (Phi (left₁ e) - Phi (left₂ e)) (Phi g - Phi h)
  have h11 : 0 ≤ r11 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left₁, Function.update right e g)).le
  have h12 : 0 ≤ r12 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left₁, Function.update right e h)).le
  have h21 : 0 ≤ r21 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left₂, Function.update right e g)).le
  have h22 : 0 ≤ r22 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left₂, Function.update right e h)).le
  have hFour : r11 * r22 = Real.exp ((b / 2) * d) * (r12 * r21) :=
    p4Q2KH_originalJointFourCorner_eq_realFeatureExponential
      H b hb left₁ left₂ right e g h
  have hExp : Real.exp ((b / 4) * d) ^ 2 = Real.exp ((b / 2) * d) := by
    calc
      _ = Real.exp ((b / 4) * d) * Real.exp ((b / 4) * d) := by ring
      _ = Real.exp (((b / 4) * d) + ((b / 4) * d)) := (Real.exp_add _ _).symm
      _ = Real.exp ((b / 2) * d) := by congr 1; ring
  have hSq :
      (Real.sqrt r11 * Real.sqrt r22) ^ 2 =
        (Real.exp ((b / 4) * d) * (Real.sqrt r12 * Real.sqrt r21)) ^ 2 := by
    calc
      _ = r11 * r22 := by rw [mul_pow, Real.sq_sqrt h11, Real.sq_sqrt h22]
      _ = Real.exp ((b / 2) * d) * (r12 * r21) := hFour
      _ = (Real.exp ((b / 4) * d) * (Real.sqrt r12 * Real.sqrt r21)) ^ 2 := by
        rw [mul_pow, hExp, mul_pow, Real.sq_sqrt h12, Real.sq_sqrt h21]
  have hL : 0 ≤ Real.sqrt r11 * Real.sqrt r22 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hR : 0 ≤ Real.exp ((b / 4) * d) * (Real.sqrt r12 * Real.sqrt r21) :=
    mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  change Real.sqrt r11 * Real.sqrt r22 =
    Real.exp ((b / 4) * d) * (Real.sqrt r12 * Real.sqrt r21)
  nlinarith

/-- Exactly the ORIGINAL continuous Perron joint half-density s used
in the physical GI receiver, not an auxiliary posterior square root.
The half-exponent cross ratio is independent of vacuum normalizers. -/
theorem p4Q2KY_originalJointHalfDensityFourCorner_eq_realFeatureExponential
    (b : ℝ) (hb : 0 ≤ b)
    (left₁ left₂ right : Cfg) (e : Link) (g h : Gauge) :
    s b hb (left₁, Function.update right e g) *
        s b hb (left₂, Function.update right e h) =
      Real.exp ((b / 4) *
        inner ℝ (Phi (left₁ e) - Phi (left₂ e)) (Phi g - Phi h)) *
        (s b hb (left₁, Function.update right e h) *
          s b hb (left₂, Function.update right e g)) := by
  change
    Real.sqrt (rho b hb (left₁, Function.update right e g)) *
        Real.sqrt (rho b hb (left₂, Function.update right e h)) =
      Real.exp ((b / 4) *
        inner ℝ (Phi (left₁ e) - Phi (left₂ e)) (Phi g - Phi h)) *
        (Real.sqrt (rho b hb (left₁, Function.update right e h)) *
          Real.sqrt (rho b hb (left₂, Function.update right e g)))
  exact p4Q2KY_originalJointDensitySqrtFourCorner_eq_realFeatureExponential
    H b hb left₁ left₂ right e g h

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KY_originalJointDensitySqrtFourCorner_eq_realFeatureExponential
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KY_originalJointHalfDensityFourCorner_eq_realFeatureExponential

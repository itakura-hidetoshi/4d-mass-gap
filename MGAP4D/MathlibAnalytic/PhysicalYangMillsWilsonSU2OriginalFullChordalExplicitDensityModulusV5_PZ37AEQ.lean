import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullChordalLogDensityLipschitzV5_PZ37AEP
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEQ — quantitative full-boundary physical rho and q variation

AEP proved the ORIGINAL two-sided full D_H Harnack inequalities
for both the literal joint sqrt-density rho_H and true JQ density q_H
with factor exp(c D_H), c = 13 beta0.

AEK proved the positive fixed-H original Wilson action density ceilings
M_rho(H) and M_q(H), without any finite-net sample or surrogate Haar law.

Consequently, for arbitrary true boundary pair configurations z,w:

  |rho_H(z)-rho_H(w)| <= (exp(c D_H(z,w))-1) M_rho(H),
  |q_H(z)-q_H(w)| <= (exp(c D_H(z,w))-1) M_q(H).

For every nonnegative radius R, if D_H(z,w)<=R, these strengthen to

  |rho_H(z)-rho_H(w)| <= c*exp(c R)*M_rho(H)*D_H(z,w)
  |q_H(z)-q_H(w)| <= c*exp(c R)*M_q(H)*D_H(z,w).

The abstract exponential estimate is proved from the standard tangent
bound exp(-x)>=1-x. This establishes an ACTUAL quantitative numerical
radius-local Lipschitz estimate on the SAME unchanged original physical
boundary pair-Haar metric, not just compactness continuity.

The relative log-density coefficient c is independent of H, while
the genuine absolute amplitude ceilings M_rho and M_q depend on H.
Neither uniform coercivity nor the continuum Yang-Mills gap follows.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Explicit exponential increment estimate, valid for all real x.
For nonnegative x it is the usual local Lipschitz envelope. -/
theorem p4Q2PZ37AEQ_real_exp_sub_one_le_x_mul_exp (x : ℝ) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have hTangent := Real.add_one_le_exp (-x)
  have hLin : 1 - x ≤ Real.exp (-x) := by
    linarith only [hTangent]
  have hMul :
      (1 - x) * Real.exp x ≤ 1 := by
    calc
      (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
        mul_le_mul_of_nonneg_right hLin (Real.exp_pos x).le
      _ = 1 := by
        rw [← Real.exp_add]
        simp
  nlinarith only [hMul]

/-- For 0<=x<=r the exponential increment is bounded linearly
by the explicit radius coefficient exp(r). -/
theorem p4Q2PZ37AEQ_real_exp_sub_one_local_linear
    (x r : ℝ) (hx : 0 ≤ x) (hxr : x ≤ r) :
    Real.exp x - 1 ≤ x * Real.exp r := by
  calc
    Real.exp x - 1 ≤ x * Real.exp x :=
      p4Q2PZ37AEQ_real_exp_sub_one_le_x_mul_exp x
    _ ≤ x * Real.exp r :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxr) hx

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AEQ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEQ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEQ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEQ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEQ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "rho" => continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "k" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "M_rho" => Real.sqrt ((k⁻¹) ^ 3)
local notation "M_q" =>
  Real.exp (b0 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) /
    Real.sqrt (k ^ 3)
local notation "c" => 13 * b0
local notation "Rfull" => fun z w : Pair => Real.exp (c * D z w)

/-- True all-link original joint sqrt-density: unconditional
fixed-H absolute modulus with the certified AEK amplitude ceiling. -/
theorem p4Q2PZ37AEQ_originalSqrtDensity_fullDistance_absVariation
    (z w : Pair) :
    |rho z - rho w| ≤ (Rfull z w - 1) * M_rho := by
  have hC : 0 ≤ c := mul_nonneg (by norm_num) hb0
  have hD : 0 ≤ D z w :=
    p4Q2PZ37ADL_originalFullDistance_nonneg H z w
  have ht : 1 ≤ Rfull z w := by
    change 1 ≤ Real.exp (c * D z w)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hC hD)
  have hBound :=
    (p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H).2
  exact p4Q2PZ37AEL_real_twoSidedHarnack_absVariation
    (rho z) (rho w) (Rfull z w) M_rho
    ht (hBound z).2 (hBound w).2
    (p4Q2PZ37AEP_originalSqrtDensity_fullDistanceHarnack H z w)
    (p4Q2PZ37AEP_originalSqrtDensity_fullDistanceReverse H z w)

/-- True original JQ physical density: full D_H finite-volume
absolute modulus using the genuine AEK Wilson action floor. -/
theorem p4Q2PZ37AEQ_originalJQDensity_fullDistance_absVariation
    (z w : Pair) :
    |q b0 hb0 z - q b0 hb0 w| ≤ (Rfull z w - 1) * M_q := by
  have hC : 0 ≤ c := mul_nonneg (by norm_num) hb0
  have hD : 0 ≤ D z w :=
    p4Q2PZ37ADL_originalFullDistance_nonneg H z w
  have ht : 1 ≤ Rfull z w := by
    change 1 ≤ Real.exp (c * D z w)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hC hD)
  have hBound :=
    (p4Q2PZ37AEK_originalPhysicalDensity_explicitWilsonBounds H).2
  exact p4Q2PZ37AEL_real_twoSidedHarnack_absVariation
    (q b0 hb0 z) (q b0 hb0 w) (Rfull z w) M_q
    ht (hBound z).2 (hBound w).2
    (p4Q2PZ37AEP_originalJQDensity_fullDistanceHarnack H z w)
    (p4Q2PZ37AEP_originalJQDensity_fullDistanceReverse H z w)

/-- The ORIGINAL rho has a fully explicit physical D_H local
Lipschitz constant for every specified finite radius r. -/
theorem p4Q2PZ37AEQ_originalSqrtDensity_fullBall_localLipschitz
    (z w : Pair) (r : ℝ) (hDle : D z w ≤ r) :
    |rho z - rho w| ≤
      (c * Real.exp (c * r) * M_rho) * D z w := by
  have hC : 0 ≤ c := mul_nonneg (by norm_num) hb0
  have hD : 0 ≤ D z w :=
    p4Q2PZ37ADL_originalFullDistance_nonneg H z w
  have hRad := mul_le_mul_of_nonneg_left hDle hC
  have hExp :=
    p4Q2PZ37AEQ_real_exp_sub_one_local_linear
      (c * D z w) (c * r) (mul_nonneg hC hD) hRad
  have hM : 0 ≤ M_rho := Real.sqrt_nonneg _
  calc
    |rho z - rho w| ≤ (Rfull z w - 1) * M_rho :=
      p4Q2PZ37AEQ_originalSqrtDensity_fullDistance_absVariation H z w
    _ ≤ ((c * D z w) * Real.exp (c * r)) * M_rho :=
      mul_le_mul_of_nonneg_right hExp hM
    _ = (c * Real.exp (c * r) * M_rho) * D z w := by ring

/-- The SAME original physical JQ q admits an explicit local
Lipschitz constant over every genuine D_H radius. -/
theorem p4Q2PZ37AEQ_originalJQDensity_fullBall_localLipschitz
    (z w : Pair) (r : ℝ) (hDle : D z w ≤ r) :
    |q b0 hb0 z - q b0 hb0 w| ≤
      (c * Real.exp (c * r) * M_q) * D z w := by
  have hC : 0 ≤ c := mul_nonneg (by norm_num) hb0
  have hD : 0 ≤ D z w :=
    p4Q2PZ37ADL_originalFullDistance_nonneg H z w
  have hRad := mul_le_mul_of_nonneg_left hDle hC
  have hExp :=
    p4Q2PZ37AEQ_real_exp_sub_one_local_linear
      (c * D z w) (c * r) (mul_nonneg hC hD) hRad
  have hk : 0 < k :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H b0
  have hM : 0 ≤ M_q := by
    exact div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
  calc
    |q b0 hb0 z - q b0 hb0 w| ≤ (Rfull z w - 1) * M_q :=
      p4Q2PZ37AEQ_originalJQDensity_fullDistance_absVariation H z w
    _ ≤ ((c * D z w) * Real.exp (c * r)) * M_q :=
      mul_le_mul_of_nonneg_right hExp hM
    _ = (c * Real.exp (c * r) * M_q) * D z w := by ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEQ_real_exp_sub_one_le_x_mul_exp
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEQ_real_exp_sub_one_local_linear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEQ_originalSqrtDensity_fullDistance_absVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEQ_originalJQDensity_fullDistance_absVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEQ_originalSqrtDensity_fullBall_localLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEQ_originalJQDensity_fullBall_localLipschitz

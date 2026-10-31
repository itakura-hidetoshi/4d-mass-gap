import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferRegressionV5_PZ37ACA
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorResidualBoundV5_PZ37ACI
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAbsoluteCrossSmallCouplingObstructionV5_PZ37ABM
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHaarPosteriorPlaquetteNormalizedFloorV5_PZ37AAI
import Mathlib.SetTheory.Cardinal.Finite

/-!
# P4-Q2-PZ37ACJ — numerical original physical source and GI error budgets

Keep the SAME physical source f, FF receiver F, Wilson transfer norm,
Perron representative, original energy E and both interacting posterior
laws.  ACA bounds the actual receiver variance by
  [||T||^(-1) (exp(8*b)^3-1) ||f||]^2.
The true inverse-transfer estimate ABM and elementary exponential bounds
therefore give, with the ORIGINAL finite slab action budget A_H,
  0 <= D_F = Var(F)-4*Cov(F,E)^2
       <= 576*b^2*exp((2*A_H+48)*b)*||f||^2.

Combining this proved source estimate with ACI's actual posterior residual
rho(b)<=1024*b^4*exp(64*b) yields
  (GI+4*k*Cov(F,E))^2
    <= 589824*b^6*exp((2*A_H+112)*b)*||f||^2.
For the ORIGINAL centered Gauss-law source, its genuine norm satisfies
||f0||^2<=6*P_H.  We use AAI's compatible proof of the same AAG/AAF bound;
the historically conflicting AAG and ZW import branches are not combined.
The resulting centered-source constant is 3538944*P_H.

These are unconditional finite-volume numerical upper bounds.  The action
budget and plaquette count retain their genuine H dependence.  No source
regression-smallness premise, covariance floor, uniform coercivity or
continuum mass-gap conclusion is introduced.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ACJ_budget_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACJ_budget_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACJ_budget_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACJ_budget_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACJ_budget_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACJ_budget_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

private theorem p4Q2PZ37ACJ_budget_expEightCube (b : ℝ) :
    Real.exp (8 * b) ^ 3 = Real.exp (24 * b) := by
  rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private theorem p4Q2PZ37ACJ_budget_expTwentyFour_sub_one_le (b : ℝ) :
    Real.exp (24 * b) - 1 ≤ 24 * b * Real.exp (24 * b) := by
  have hCancel : Real.exp (-24 * b) * Real.exp (24 * b) = (1 : ℝ) := by
    rw [← Real.exp_add, show -24 * b + 24 * b = (0 : ℝ) by ring, Real.exp_zero]
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-24 * b))
    (Real.exp_nonneg (24 * b))
  rw [hCancel] at h
  nlinarith only [h]

private theorem p4Q2PZ37ACJ_budget_harnackSquare (b A r : ℝ) :
    (Real.exp (b * A) * (24 * b * Real.exp (24 * b)) * r) ^ 2 =
      576 * b ^ 2 * Real.exp ((2 * A + 48) * b) * r ^ 2 := by
  have hExp : (Real.exp (b * A) * Real.exp (24 * b)) ^ 2 =
      Real.exp ((2 * A + 48) * b) := by
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = 576 * b ^ 2 * (Real.exp (b * A) * Real.exp (24 * b)) ^ 2 * r ^ 2 := by
      ring
    _ = _ := by rw [hExp]

private theorem p4Q2PZ37ACJ_budget_variance_mul_posterior (b A r : ℝ) :
    (576 * b ^ 2 * Real.exp ((2 * A + 48) * b) * r ^ 2) *
        (1024 * b ^ 4 * Real.exp (64 * b)) =
      589824 * b ^ 6 * Real.exp ((2 * A + 112) * b) * r ^ 2 := by
  have hExp : Real.exp ((2 * A + 48) * b) * Real.exp (64 * b) =
      Real.exp ((2 * A + 112) * b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = 589824 * b ^ 6 *
        (Real.exp ((2 * A + 48) * b) * Real.exp (64 * b)) * r ^ 2 := by ring
    _ = _ := by rw [hExp]

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "budget" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "P" => (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "k" => p4Q2PZ37ACH_originalPosteriorEnergyContrast H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H
local notation "rho" => p4Q2PZ37ACI_originalPosteriorResidualEnvelope
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local instance p4Q2PZ37ACJ_budget_links : Fintype Link := Fintype.ofFinite _

/-- The true FF receiver variance has an entirely numerical finite-volume
upper bound, using the original action budget and physical source norm. -/
theorem p4Q2PZ37ACJ_originalReceiver_variance_le_numericBudget
    (b : ℝ) (hb : 0 < b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Var (F b hb.le f e z) ≤
      576 * b ^ 2 * Real.exp ((2 * budget + 48) * b) * ‖f‖ ^ 2 := by
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb.le‖⁻¹
  have hL : 0 ≤ L := inv_nonneg.mpr
    (ContinuousLinearMap.opNorm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb.le))
  have hInv := p4Q2PZ37ABM_originalPhysicalTransferNorm_inv_le_exp_actionBudget H b hb
  change L ≤ Real.exp (b * budget) at hInv
  have hGap : 0 ≤ Real.exp (24 * b) - 1 := by
    have hOne : (1 : ℝ) ≤ Real.exp (24 * b) := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 24 * b by positivity))
    exact sub_nonneg.mpr hOne
  have hCoef := mul_le_mul_of_nonneg_right
    (mul_le_mul hInv (p4Q2PZ37ACJ_budget_expTwentyFour_sub_one_le b)
      hGap (Real.exp_nonneg (b * budget))) (norm_nonneg f)
  have hSq := pow_le_pow_left₀
    (mul_nonneg (mul_nonneg hL hGap) (norm_nonneg f)) hCoef 2
  have hFC := p4Q2PZ37ACA_originalReceiver_variance_le_FC H b hb.le f e z
  rw [p4Q2PZ37ACJ_budget_expEightCube] at hFC
  change Var (F b hb.le f e z) ≤ (L * (Real.exp (24 * b) - 1) * ‖f‖) ^ 2 at hFC
  calc
    _ ≤ (Real.exp (b * budget) * (24 * b * Real.exp (24 * b)) * ‖f‖) ^ 2 :=
      hFC.trans hSq
    _ = _ := p4Q2PZ37ACJ_budget_harnackSquare b budget ‖f‖

/-- A proved numerical upper bound for the actual source energy-orthogonal
regression defect. No smallness of that source residual is assumed. -/
theorem p4Q2PZ37ACJ_originalReceiverDefect_le_numericBudget
    (b : ℝ) (hb : 0 < b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Var (F b hb.le f e z) - 4 * (Cov (F b hb.le f e z) E) ^ 2 ≤
      576 * b ^ 2 * Real.exp ((2 * budget + 48) * b) * ‖f‖ ^ 2 := by
  calc
    _ ≤ Var (F b hb.le f e z) := sub_le_self _ (by positivity)
    _ ≤ _ := p4Q2PZ37ACJ_originalReceiver_variance_le_numericBudget H b hb f e z

/-- The SAME centered Gauss-law source has a fully numerical defect cap.
AAI proves the original AAG/AAF norm bound in the compatible ZW closure. -/
theorem p4Q2PZ37ACJ_centeredReceiverDefect_le_numericBudget
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Cfg × Cfg) :
    Var (F b hb.le f0 e z) - 4 * (Cov (F b hb.le f0 e z) E) ^ 2 ≤
      3456 * P * b ^ 2 * Real.exp ((2 * budget + 48) * b) := by
  have hNorm : ‖f0‖ ^ 2 ≤ 6 * P := by
    simpa only [Fintype.card_eq_nat_card] using
      (p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount H)
  have hScale : 0 ≤ 576 * b ^ 2 * Real.exp ((2 * budget + 48) * b) := by positivity
  calc
    _ ≤ 576 * b ^ 2 * Real.exp ((2 * budget + 48) * b) * ‖f0‖ ^ 2 :=
      p4Q2PZ37ACJ_originalReceiverDefect_le_numericBudget H b hb f0 e z
    _ ≤ (576 * b ^ 2 * Real.exp ((2 * budget + 48) * b)) * (6 * P) :=
      mul_le_mul_of_nonneg_left hNorm hScale
    _ = _ := by ring

/-- The original GI regression error has a genuine sixth-order squared
upper bound with the full finite-volume action budget retained. Both
source and posterior residual factors have been estimated, not assumed. -/
theorem p4Q2PZ37ACJ_originalGI_energyRegression_numeric_sq
    (b : ℝ) (hb : 0 < b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    (gap b hb.le f e z + 4 * k b hb.le z.2 e * Cov (F b hb.le f e z) E) ^ 2 ≤
      589824 * b ^ 6 * Real.exp ((2 * budget + 112) * b) * ‖f‖ ^ 2 := by
  have hD := p4Q2PZ37ACJ_originalReceiverDefect_le_numericBudget H b hb f e z
  have hRho := p4Q2PZ37ACI_originalPosteriorResidualEnvelope_le_quartic b hb.le
  have hScale : 0 ≤ 576 * b ^ 2 * Real.exp ((2 * budget + 48) * b) * ‖f‖ ^ 2 := by
    positivity
  have hMul := mul_le_mul hD hRho
    (p4Q2PZ37ACI_originalPosteriorResidualEnvelope_nonneg b) hScale
  calc
    _ ≤ (Var (F b hb.le f e z) - 4 * (Cov (F b hb.le f e z) E) ^ 2) * rho b :=
      p4Q2PZ37ACI_originalGI_energyRegression_explicit_sq H b hb.le f e z
    _ ≤ (576 * b ^ 2 * Real.exp ((2 * budget + 48) * b) * ‖f‖ ^ 2) *
        (1024 * b ^ 4 * Real.exp (64 * b)) := hMul
    _ = _ := p4Q2PZ37ACJ_budget_variance_mul_posterior b budget ‖f‖

/-- Evaluate the preceding error budget for the unchanged centered source
using its proved physical norm, with the actual spatial plaquette count. -/
theorem p4Q2PZ37ACJ_centeredGI_energyRegression_numeric_sq
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Cfg × Cfg) :
    (gap b hb.le f0 e z + 4 * k b hb.le z.2 e * Cov (F b hb.le f0 e z) E) ^ 2 ≤
      3538944 * P * b ^ 6 * Real.exp ((2 * budget + 112) * b) := by
  have hNorm : ‖f0‖ ^ 2 ≤ 6 * P := by
    simpa only [Fintype.card_eq_nat_card] using
      (p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount H)
  have hScale : 0 ≤ 589824 * b ^ 6 * Real.exp ((2 * budget + 112) * b) := by positivity
  calc
    _ ≤ 589824 * b ^ 6 * Real.exp ((2 * budget + 112) * b) * ‖f0‖ ^ 2 :=
      p4Q2PZ37ACJ_originalGI_energyRegression_numeric_sq H b hb f0 e z
    _ ≤ (589824 * b ^ 6 * Real.exp ((2 * budget + 112) * b)) * (6 * P) :=
      mul_le_mul_of_nonneg_left hNorm hScale
    _ = _ := by ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalReceiver_variance_le_numericBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalReceiverDefect_le_numericBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_centeredReceiverDefect_le_numericBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalGI_energyRegression_numeric_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_centeredGI_energyRegression_numeric_sq

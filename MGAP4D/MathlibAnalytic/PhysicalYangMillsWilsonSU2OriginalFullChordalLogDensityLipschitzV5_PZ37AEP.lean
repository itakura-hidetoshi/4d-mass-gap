import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullChordalDensityHarnackV5_PZ37AEP
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEP — original global log rho and log JQ Lipschitz

The original finite-H joint rho and true JQ inverse-transfer q are
strictly positive at every genuine original boundary pair. The new
all-link two-sided Harnack bound from AEP therefore implies

 |log rho_H(z) - log rho_H(w)| <= 13*beta0*D_H(z,w)
 |log q_H(z) - log q_H(w)| <= 13*beta0*D_H(z,w).

These estimates are unconditional and their numerical Lipschitz
coefficient is independent of H. They concern the full finite-volume
two-boundary original calibrated L1 distance, not an independent
product posterior, nor a continuum/infinite-volume coercivity theorem.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Genuine positive two-sided exponential comparisons give an
additive absolute logarithmic modulus, without taking logs of an
undefined or zero physical density. -/
theorem p4Q2PZ37AEP_real_log_abs_le_of_twoSidedExp
    (u v x : ℝ)
    (hu : 0 < u) (hv : 0 < v)
    (huv : u ≤ Real.exp x * v)
    (hvu : v ≤ Real.exp x * u) :
    |Real.log u - Real.log v| ≤ x := by
  have hlog1 : Real.log u - Real.log v ≤ x := by
    have h := Real.log_le_log hu huv
    rw [Real.log_mul (Real.exp_ne_zero x) hv.ne', Real.log_exp] at h
    linarith only [h]
  have hlog2 : Real.log v - Real.log u ≤ x := by
    have h := Real.log_le_log hv hvu
    rw [Real.log_mul (Real.exp_ne_zero x) hu.ne', Real.log_exp] at h
    linarith only [h]
  apply abs_le.mpr
  constructor
  · linarith only [hlog2]
  · exact hlog1

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AEPlog_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEPlog_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEPlog_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEPlog_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEPlog_borel : BorelSpace G :=
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
local notation "Rfull" => fun z w : Pair => Real.exp ((13 * b0) * D z w)

/-- Exact global physical rho logarithmic Lipschitz theorem, uniform
in the number of original SU(2) boundary links. -/
theorem p4Q2PZ37AEP_originalSqrtDensity_log_fullDistanceLipschitz
    (z w : Pair) :
    |Real.log (rho z) - Real.log (rho w)| ≤
      (13 * b0) * D z w := by
  have hz : 0 < rho z :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 z
  have hw : 0 < rho w :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 w
  exact p4Q2PZ37AEP_real_log_abs_le_of_twoSidedExp
    (rho z) (rho w) ((13 * b0) * D z w)
    hz hw
    (p4Q2PZ37AEP_originalSqrtDensity_fullDistanceHarnack H z w)
    (p4Q2PZ37AEP_originalSqrtDensity_fullDistanceReverse H z w)

/-- Pointwise strict positivity of the ORIGINAL JQ inverse-transfer
density, derived from AEK's existing unconditional genuine Wilson floor. -/
theorem p4Q2PZ37AEP_originalJQDensity_pos (z : Pair) :
    0 < q b0 hb0 z := by
  have hBounds := p4Q2PZ37AEK_originalPhysicalDensity_explicitWilsonBounds H
  exact lt_of_lt_of_le hBounds.1 (hBounds.2 z).1

/-- The unchanged JQ density has the SAME full finite-volume logarithmic
Lipschitz coefficient as rho, with NO H-dependent floor in the
logarithmic coefficient. -/
theorem p4Q2PZ37AEP_originalJQDensity_log_fullDistanceLipschitz
    (z w : Pair) :
    |Real.log (q b0 hb0 z) - Real.log (q b0 hb0 w)| ≤
      (13 * b0) * D z w := by
  exact p4Q2PZ37AEP_real_log_abs_le_of_twoSidedExp
    (q b0 hb0 z) (q b0 hb0 w) ((13 * b0) * D z w)
    (p4Q2PZ37AEP_originalJQDensity_pos H z)
    (p4Q2PZ37AEP_originalJQDensity_pos H w)
    (p4Q2PZ37AEP_originalJQDensity_fullDistanceHarnack H z w)
    (p4Q2PZ37AEP_originalJQDensity_fullDistanceReverse H z w)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEP_real_log_abs_le_of_twoSidedExp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalSqrtDensity_log_fullDistanceLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalJQDensity_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalJQDensity_log_fullDistanceLipschitz

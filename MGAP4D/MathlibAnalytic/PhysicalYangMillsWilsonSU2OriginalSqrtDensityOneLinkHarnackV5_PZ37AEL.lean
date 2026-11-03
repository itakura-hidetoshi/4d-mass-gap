import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalVacuumDensityExplicitHarnackV5_PZ37AEK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEL — original joint sqrt-density: quantitative one-link Harnack

AEK proved explicit positive pointwise bounds for the SAME genuine Wilson
Perron vacuum Omega_H and the ORIGINAL interacting joint half-density rho_H.
The literal fixed-coupling Wilson kernel and canonical Omega have existing
volume-independent exp(8*beta) one-link Harnack inequalities. At a fixed
unchanged first boundary, altering one original physical SU(2) link on the
second boundary changes both factors by at most exp(8*beta), and therefore
rho_H by at most exp(8*beta) after the joint square root.

This is a genuine physical one-link comparison, not a D_H Lipschitz estimate:
the factor does not approach one as the link chordal displacement tends to zero.
No proxy density, altered posterior, new physical model, or volume-uniform
continuum gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AEL_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEL_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEL_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEL_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEL_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

/-- Elementary product comparison. There is no independence assumption. -/
theorem p4Q2PZ37AEL_real_twoFactorHarnack
    (u v u' v' t : ℝ)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hv' : 0 ≤ v')
    (hu' : u' ≤ t * u) (hv : v' ≤ t * v) :
    u' * v' ≤ t ^ 2 * (u * v) := by
  calc
    u' * v' ≤ (t * u) * v' :=
      mul_le_mul_of_nonneg_right hu' hv'
    _ ≤ (t * u) * (t * v) :=
      mul_le_mul_of_nonneg_left hv (mul_nonneg ht hu)
    _ = t ^ 2 * (u * v) := by ring

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) b0 hb0
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "W" => continuousJointWeight H 2 (by norm_num) b0 hb0
local notation "rho" => continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "Tnorm" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "t" => Real.exp (8 * b0)
local notation "Replace" =>
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H 2

/-- For ONE actual Wilson SU(2) second-boundary link replacement, the
true, unchanged normalized joint weight has an exp(16*beta) comparison.
Both factors are genuine: original continuous vacuum and original kernel. -/
theorem p4Q2PZ37AEL_originalJointWeight_oneLinkHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    W (A, Replace B e g) ≤ t ^ 2 * W (A, Replace B e h) := by
  let Bg := Replace B e g
  let Bh := Replace B e h
  have ht : 0 ≤ t := (Real.exp_pos _).le
  have hOmega0 : 0 ≤ Omega A :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) b0 hb0 A).le
  have hKg : 0 ≤ K A Bg :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b0 A Bg).le
  have hOg : 0 ≤ Omega Bg :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) b0 hb0 Bg).le
  have hKh : 0 ≤ K A Bh :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b0 A Bh).le
  have hKernel : K A Bg ≤ t * K A Bh :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
      H 2 (by norm_num) b0 hb0 A B e g h
  have hVac : Omega Bg ≤ t * Omega Bh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
      H 2 (by norm_num) b0 hb0 B e g h
  have hFactors : K A Bg * Omega Bg ≤ t ^ 2 * (K A Bh * Omega Bh) :=
    p4Q2PZ37AEL_real_twoFactorHarnack
      (K A Bh) (Omega Bh) (K A Bg) (Omega Bg) t
      ht hKh hOg hKernel hVac
  have hProduct :
      Omega A * K A Bg * Omega Bg ≤
        t ^ 2 * (Omega A * K A Bh * Omega Bh) := by
    calc
      Omega A * K A Bg * Omega Bg = Omega A * (K A Bg * Omega Bg) := by ring
      _ ≤ Omega A * (t ^ 2 * (K A Bh * Omega Bh)) :=
        mul_le_mul_of_nonneg_left hFactors hOmega0
      _ = t ^ 2 * (Omega A * K A Bh * Omega Bh) := by ring
  have hTinv : 0 ≤ Tnorm⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  change Tnorm⁻¹ * (Omega A * K A Bg * Omega Bg) ≤
    t ^ 2 * (Tnorm⁻¹ * (Omega A * K A Bh * Omega Bh))
  calc
    Tnorm⁻¹ * (Omega A * K A Bg * Omega Bg) ≤
      Tnorm⁻¹ * (t ^ 2 * (Omega A * K A Bh * Omega Bh)) :=
      mul_le_mul_of_nonneg_left hProduct hTinv
    _ = t ^ 2 * (Tnorm⁻¹ * (Omega A * K A Bh * Omega Bh)) := by ring

/-- Genuine joint square-root density: its actual one-link Harnack
factor is exp(8*beta), rather than the squared-weight exp(16*beta). -/
theorem p4Q2PZ37AEL_originalSqrtDensity_oneLinkHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    rho (A, Replace B e g) ≤ t * rho (A, Replace B e h) := by
  have hW := p4Q2PZ37AEL_originalJointWeight_oneLinkHarnack H A B e g h
  have ht : 0 ≤ t := (Real.exp_pos _).le
  calc
    rho (A, Replace B e g) =
        Real.sqrt (W (A, Replace B e g)) := rfl
    _ ≤ Real.sqrt (t ^ 2 * W (A, Replace B e h)) :=
      Real.sqrt_le_sqrt hW
    _ = t * rho (A, Replace B e h) := by
      rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
      rfl

/-- The comparison also holds in the reverse direction, without
assuming a coordinatewise sign, monotonicity or posterior independence. -/
theorem p4Q2PZ37AEL_originalSqrtDensity_oneLinkReverse
    (A B : Cfg) (e : Link) (g h : G) :
    rho (A, Replace B e h) ≤ t * rho (A, Replace B e g) := by
  exact p4Q2PZ37AEL_originalSqrtDensity_oneLinkHarnack H A B e h g

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEL_real_twoFactorHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalJointWeight_oneLinkHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalSqrtDensity_oneLinkHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalSqrtDensity_oneLinkReverse

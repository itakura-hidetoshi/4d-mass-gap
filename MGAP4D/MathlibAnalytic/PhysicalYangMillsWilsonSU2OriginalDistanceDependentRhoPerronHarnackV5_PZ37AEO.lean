import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalDistanceDependentKernelVacuumHarnackV5_PZ37AEO
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEO — original rho and JQ density small-distance Harnack

The original normalized joint weight W_H is built from the SAME
genuine physical transfer norm, continuous Perron vacuum Omega_H,
and the interacting Wilson kernel K_H.

The new local action-derived factor
  R(g,h) = exp(beta0*(13*d_J(g,h)))
is proved in the AEO kernel/vacuum module to bound BOTH original
K_H and original Omega_H in each orientation. Their genuine product
gives W_H(B_g) <= R(g,h)^2 W_H(B_h).
Taking the original joint square root gives
  rho_H(A,B_g) <= R(g,h) rho_H(A,B_h).

The genuine original JQ density q_H = lambda_H^-1/rho_H inherits
the same ratio via the EXACT inverse-transfer cancellation theorem.
No independence, surrogate Haar measure, proxy Perron density, or
new positive floor has been substituted.

AEK's finite-volume global ceilings make the resulting one-link
absolute variation explicitly small-distance dependent:
  |rho_H(A,B_g)-rho_H(A,B_h)| <= (R-1) M_H,
and similarly for q_H. The factor R-1 -> 0 as d_J -> 0.

These are one-coordinate results on the genuine original pair-Haar
boundary space. All-coordinate descent and H-uniform coercivity are
not claimed, and neither is the continuum Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance

local instance p4Q2PZ37AEO2_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEO2_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEO2_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEO2_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEO2_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
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
local notation "Replace" =>
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink H 2
local notation "R" => fun g h : G => Real.exp (b0 * (13 * dJ g h))

local instance p4Q2PZ37AEO2_links : Fintype Link := Fintype.ofFinite _

/-- The actual distance-dependent factor is symmetric in g,h. -/
theorem p4Q2PZ37AEO_originalDistanceHarnackFactor_symm (g h : G) :
    R g h = R h g := by
  change Real.exp (b0 * (13 * dJ g h)) =
    Real.exp (b0 * (13 * dJ h g))
  rw [p4Q2PZ37ADK_trueChordalDistance_symm]

/-- The original factor is >=1 and becomes 1 when d_J=0. -/
theorem p4Q2PZ37AEO_originalDistanceHarnackFactor_ge_one (g h : G) :
    1 ≤ R g h := by
  change 1 ≤ Real.exp (b0 * (13 * dJ g h))
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  exact mul_nonneg hb0
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13)
      (p4Q2PZ37ADK_trueChordalDistance_nonneg g h))

/-- Product comparison with unchanged, genuine positive transfer norm.
The two factors K_H and Omega_H each contribute the SAME small-distance
R(g,h); the first-boundary Perron factor is unchanged. -/
theorem p4Q2PZ37AEO_originalJointWeight_oneLinkDistanceHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    W (A, Replace B e g) ≤ (R g h)^2 * W (A, Replace B e h) := by
  let Bg := Replace B e g
  let Bh := Replace B e h
  let t : ℝ := R g h
  have ht : 0 ≤ t := (Real.exp_pos _).le
  have hOmega0 : 0 ≤ Omega A :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) b0 hb0 A).le
  have hOg : 0 ≤ Omega Bg :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) b0 hb0 Bg).le
  have hKh : 0 ≤ K A Bh :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b0 A Bh).le
  have hKernel : K A Bg ≤ t * K A Bh :=
    p4Q2PZ37AEO_originalWilsonKernel_oneLinkDistanceHarnack H A B e g h
  have hVac : Omega Bg ≤ t * Omega Bh :=
    p4Q2PZ37AEO_originalContinuousVacuum_oneLinkDistanceHarnack H B e g h
  have hFactors : K A Bg * Omega Bg ≤ t ^ 2 * (K A Bh * Omega Bh) :=
    p4Q2PZ37AEL_real_twoFactorHarnack
      (K A Bh) (Omega Bh) (K A Bg) (Omega Bg) t
      ht hKh hOg hKernel hVac
  have hProd :
      Omega A * K A Bg * Omega Bg ≤
        t ^ 2 * (Omega A * K A Bh * Omega Bh) := by
    calc
      Omega A * K A Bg * Omega Bg = Omega A * (K A Bg * Omega Bg) := by ring
      _ ≤ Omega A * (t ^ 2 * (K A Bh * Omega Bh)) :=
        mul_le_mul_of_nonneg_left hFactors hOmega0
      _ = t ^ 2 * (Omega A * K A Bh * Omega Bh) := by ring
  have hTinv : 0 ≤ Tnorm⁻¹ := (inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b0 hb0)).le
  change Tnorm⁻¹ * (Omega A * K A Bg * Omega Bg) ≤
    t ^ 2 * (Tnorm⁻¹ * (Omega A * K A Bh * Omega Bh))
  calc
    Tnorm⁻¹ * (Omega A * K A Bg * Omega Bg) ≤
      Tnorm⁻¹ * (t ^ 2 * (Omega A * K A Bh * Omega Bh)) :=
      mul_le_mul_of_nonneg_left hProd hTinv
    _ = t ^ 2 * (Tnorm⁻¹ * (Omega A * K A Bh * Omega Bh)) := by ring

/-- Reverse one-link Harnack of the true joint weight. -/
theorem p4Q2PZ37AEO_originalJointWeight_oneLinkDistanceReverse
    (A B : Cfg) (e : Link) (g h : G) :
    W (A, Replace B e h) ≤ (R g h)^2 * W (A, Replace B e g) := by
  have hs := p4Q2PZ37AEO_originalJointWeight_oneLinkDistanceHarnack H A B e h g
  rw [p4Q2PZ37AEO_originalDistanceHarnackFactor_symm h g] at hs
  exact hs

/-- The genuine normalized joint sqrt-density has the same
distance-sensitive factor R(g,h), exactly half the exponent of W. -/
theorem p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    rho (A, Replace B e g) ≤ R g h * rho (A, Replace B e h) := by
  have hW := p4Q2PZ37AEO_originalJointWeight_oneLinkDistanceHarnack H A B e g h
  have ht : 0 ≤ R g h := (Real.exp_pos _).le
  calc
    rho (A, Replace B e g) =
        Real.sqrt (W (A, Replace B e g)) := rfl
    _ ≤ Real.sqrt ((R g h)^2 * W (A, Replace B e h)) :=
      Real.sqrt_le_sqrt hW
    _ = R g h * rho (A, Replace B e h) := by
      rw [Real.sqrt_mul (sq_nonneg (R g h)), Real.sqrt_sq ht]
      rfl

/-- Reverse original joint sqrt-density small-distance Harnack. -/
theorem p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceReverse
    (A B : Cfg) (e : Link) (g h : G) :
    rho (A, Replace B e h) ≤ R g h * rho (A, Replace B e g) := by
  have hs := p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceHarnack H A B e h g
  rw [p4Q2PZ37AEO_originalDistanceHarnackFactor_symm h g] at hs
  exact hs

/-- First-boundary distance-sensitive comparison follows from
the original exact symmetry, not from posterior independence. -/
theorem p4Q2PZ37AEO_originalSqrtDensity_firstBoundary_oneLinkDistanceHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    rho (Replace A e g, B) ≤ R g h * rho (Replace A e h, B) := by
  calc
    rho (Replace A e g, B) = rho (B, Replace A e g) :=
      p4Q2PZ37AEL_originalSqrtDensity_symm H _ _
    _ ≤ R g h * rho (B, Replace A e h) :=
      p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceHarnack H B A e g h
    _ = R g h * rho (Replace A e h, B) := by
      rw [p4Q2PZ37AEL_originalSqrtDensity_symm H B (Replace A e h)]

/-- The true JQ inverse-transfer Perron density retains the same
small-distance factor via its exact numerator/rho cancellation. -/
theorem p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    q b0 hb0 (A, Replace B e g) ≤
      R g h * q b0 hb0 (A, Replace B e h) := by
  let Bg := Replace B e g
  let Bh := Replace B e h
  have hTnonneg : 0 ≤ Tnorm⁻¹ := (inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b0 hb0)).le
  have hrhoG : 0 < rho (A, Bg) :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 (A, Bg)
  have hrhoH : 0 < rho (A, Bh) :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 (A, Bh)
  have hOpp : rho (A, Bh) ≤ R g h * rho (A, Bg) :=
    p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceReverse H A B e g h
  calc
    q b0 hb0 (A, Bg) = Tnorm⁻¹ / rho (A, Bg) :=
      p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H (A, Bg)
    _ ≤ R g h * (Tnorm⁻¹ / rho (A, Bh)) :=
      p4Q2PZ37AEL_real_commonNumeratorDivHarnack
        Tnorm⁻¹ (rho (A, Bg)) (rho (A, Bh)) (R g h)
        hTnonneg hrhoG hrhoH hOpp
    _ = R g h * q b0 hb0 (A, Bh) := by
      rw [p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H (A, Bh)]

/-- Reverse true JQ density distance-dependent Harnack. -/
theorem p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceReverse
    (A B : Cfg) (e : Link) (g h : G) :
    q b0 hb0 (A, Replace B e h) ≤
      R g h * q b0 hb0 (A, Replace B e g) := by
  have hs := p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceHarnack H A B e h g
  rw [p4Q2PZ37AEO_originalDistanceHarnackFactor_symm h g] at hs
  exact hs

/-- Explicit local small-distance ABSOLUTE variation of the genuine
joint sqrt-density, using AEK's actual finite-H global ceiling. -/
theorem p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistance_absVariation
    (A B : Cfg) (e : Link) (g h : G) :
    |rho (A, Replace B e g) - rho (A, Replace B e h)| ≤
      (R g h - 1) *
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
            H b0)⁻¹ ^ 3) := by
  let k := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
  have ht1 := p4Q2PZ37AEO_originalDistanceHarnackFactor_ge_one H g h
  have hBounds :=
    (p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H).2
  have hG : rho (A, Replace B e g) ≤ Real.sqrt (k⁻¹ ^ 3) :=
    (hBounds (A, Replace B e g)).2
  have hH : rho (A, Replace B e h) ≤ Real.sqrt (k⁻¹ ^ 3) :=
    (hBounds (A, Replace B e h)).2
  exact p4Q2PZ37AEL_real_twoSidedHarnack_absVariation
    (rho (A, Replace B e g)) (rho (A, Replace B e h))
    (R g h) (Real.sqrt (k⁻¹ ^ 3)) ht1 hG hH
    (p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceHarnack H A B e g h)
    (p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceReverse H A B e g h)

/-- Explicit local small-distance ABSOLUTE variation for the exact
original JQ Perron density, with the SAME original numerator. -/
theorem p4Q2PZ37AEO_originalPerronDensity_oneLinkDistance_absVariation
    (A B : Cfg) (e : Link) (g h : G) :
    |q b0 hb0 (A, Replace B e g) - q b0 hb0 (A, Replace B e h)| ≤
      (R g h - 1) *
        (Real.exp (b0 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) /
          Real.sqrt
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
              H b0) ^ 3)) := by
  let k := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
  let E := Real.exp (b0 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)
  have ht1 := p4Q2PZ37AEO_originalDistanceHarnackFactor_ge_one H g h
  have hBounds :=
    (p4Q2PZ37AEK_originalPhysicalDensity_explicitWilsonBounds H).2
  have hG : q b0 hb0 (A, Replace B e g) ≤ E / Real.sqrt (k ^ 3) :=
    (hBounds (A, Replace B e g)).2
  have hH : q b0 hb0 (A, Replace B e h) ≤ E / Real.sqrt (k ^ 3) :=
    (hBounds (A, Replace B e h)).2
  exact p4Q2PZ37AEL_real_twoSidedHarnack_absVariation
    (q b0 hb0 (A, Replace B e g)) (q b0 hb0 (A, Replace B e h))
    (R g h) (E / Real.sqrt (k ^ 3)) ht1 hG hH
    (p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceHarnack H A B e g h)
    (p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceReverse H A B e g h)

/-- The small-distance rho factor uses the SAME ORIGINAL full two-boundary
calibrated chordal D_H for a single physical link replacement. -/
theorem p4Q2PZ37AEO_originalSqrtDensity_oneLinkFullDistanceHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    rho (A, Replace B e g) ≤
      Real.exp (b0 * (13 *
        p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
          (A, Replace B e g) (A, Replace B e h))) *
      rho (A, Replace B e h) := by
  rw [p4Q2PZ37AEL_originalFullDistance_secondBoundary_oneLink]
  exact p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceHarnack H A B e g h

/-- The genuine q density has the same one-link original D_H calibration. -/
theorem p4Q2PZ37AEO_originalPerronDensity_oneLinkFullDistanceHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    q b0 hb0 (A, Replace B e g) ≤
      Real.exp (b0 * (13 *
        p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
          (A, Replace B e g) (A, Replace B e h))) *
      q b0 hb0 (A, Replace B e h) := by
  rw [p4Q2PZ37AEL_originalFullDistance_secondBoundary_oneLink]
  exact p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceHarnack H A B e g h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalDistanceHarnackFactor_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalDistanceHarnackFactor_ge_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalJointWeight_oneLinkDistanceHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalJointWeight_oneLinkDistanceReverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceReverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalSqrtDensity_firstBoundary_oneLinkDistanceHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceReverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistance_absVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalPerronDensity_oneLinkDistance_absVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalSqrtDensity_oneLinkFullDistanceHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalPerronDensity_oneLinkFullDistanceHarnack

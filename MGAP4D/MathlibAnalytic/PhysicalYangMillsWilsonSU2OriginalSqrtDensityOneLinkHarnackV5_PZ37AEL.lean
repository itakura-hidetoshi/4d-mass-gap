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


/-- Exact reciprocal inequality for a common nonnegative numerator.
It is applied to the TRUE inverse transfer norm, not a proxy weight. -/
theorem p4Q2PZ37AEL_real_commonNumeratorDivHarnack
    (c u v t : ℝ)
    (hc : 0 ≤ c) (hu : 0 < u) (hv : 0 < v)
    (hvu : v ≤ t * u) :
    c / u ≤ t * (c / v) := by
  have hCross : c * v ≤ (t * c) * u := by
    calc
      c * v ≤ c * (t * u) := mul_le_mul_of_nonneg_left hvu hc
      _ = (t * c) * u := by ring
  calc
    c / u ≤ (t * c) / v := (div_le_div_iff₀ hu hv).2 hCross
    _ = t * (c / v) := by ring



/-- A two-sided multiplicative Harnack comparison and a common true
global majorant provide an absolute one-step oscillation budget. -/
theorem p4Q2PZ37AEL_real_twoSidedHarnack_absVariation
    (u v t M : ℝ)
    (ht : 1 ≤ t) (hu : u ≤ M) (hv : v ≤ M)
    (huv : u ≤ t * v) (hvu : v ≤ t * u) :
    |u - v| ≤ (t - 1) * M := by
  have ht0 : 0 ≤ t - 1 := sub_nonneg.mpr ht
  have hStep1 : u - v ≤ (t - 1) * v := by
    linarith only [huv]
  have hStep2 : v - u ≤ (t - 1) * u := by
    linarith only [hvu]
  have hB1 : (t - 1) * v ≤ (t - 1) * M :=
    mul_le_mul_of_nonneg_left hv ht0
  have hB2 : (t - 1) * u ≤ (t - 1) * M :=
    mul_le_mul_of_nonneg_left hu ht0
  apply abs_le.mpr
  constructor
  · linarith only [hStep2, hB2]
  · linarith only [hStep1, hB1]


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


/-- The original symmetric Wilson one-slab kernel makes the ORIGINAL
continuous normalized joint density symmetric in the two boundaries. -/
theorem p4Q2PZ37AEL_originalJointWeight_symm (A B : Cfg) :
    W (A, B) = W (B, A) := by
  change Tnorm⁻¹ * (Omega A * K A B * Omega B) =
    Tnorm⁻¹ * (Omega B * K B A * Omega A)
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    H 2 (by norm_num) b0 hb0 A B]
  ring

/-- Genuine original joint square-root density also has exact
two-boundary symmetry (not posterior independence). -/
theorem p4Q2PZ37AEL_originalSqrtDensity_symm (A B : Cfg) :
    rho (A, B) = rho (B, A) := by
  change Real.sqrt (W (A, B)) = Real.sqrt (W (B, A))
  rw [p4Q2PZ37AEL_originalJointWeight_symm H A B]

/-- First-boundary one-link Harnack, obtained by actual Wilson-kernel
symmetry, retaining the ORIGINAL pair-Haar density. -/
theorem p4Q2PZ37AEL_originalSqrtDensity_firstBoundary_oneLinkHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    rho (Replace A e g, B) ≤ t * rho (Replace A e h, B) := by
  calc
    rho (Replace A e g, B) = rho (B, Replace A e g) :=
      p4Q2PZ37AEL_originalSqrtDensity_symm H _ _
    _ ≤ t * rho (B, Replace A e h) :=
      p4Q2PZ37AEL_originalSqrtDensity_oneLinkHarnack H B A e g h
    _ = t * rho (Replace A e h, B) := by
      rw [p4Q2PZ37AEL_originalSqrtDensity_symm H B (Replace A e h)]

/-- The actual original JQ Perron density has the SAME one-link
multiplicative bound, via the exact inverse transfer/rho identity.
No upper bound on the physical transfer is substituted here. -/
theorem p4Q2PZ37AEL_originalPerronDensity_oneLinkHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    q b0 hb0 (A, Replace B e g) ≤
      t * q b0 hb0 (A, Replace B e h) := by
  let Bg := Replace B e g
  let Bh := Replace B e h
  have hTnonneg : 0 ≤ Tnorm⁻¹ :=
    inv_nonneg.mpr (norm_nonneg _)
  have hrhoG : 0 < rho (A, Bg) :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 (A, Bg)
  have hrhoH : 0 < rho (A, Bh) :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 (A, Bh)
  have hOpp : rho (A, Bh) ≤ t * rho (A, Bg) :=
    p4Q2PZ37AEL_originalSqrtDensity_oneLinkReverse H A B e g h
  calc
    q b0 hb0 (A, Bg) = Tnorm⁻¹ / rho (A, Bg) :=
      p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H (A, Bg)
    _ ≤ t * (Tnorm⁻¹ / rho (A, Bh)) :=
      p4Q2PZ37AEL_real_commonNumeratorDivHarnack
        Tnorm⁻¹ (rho (A, Bg)) (rho (A, Bh)) t
        hTnonneg hrhoG hrhoH hOpp
    _ = t * q b0 hb0 (A, Bh) := by
      rw [p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H (A, Bh)]

/-- Reverse orientation of the original Perron density comparison. -/
theorem p4Q2PZ37AEL_originalPerronDensity_oneLinkReverse
    (A B : Cfg) (e : Link) (g h : G) :
    q b0 hb0 (A, Replace B e h) ≤
      t * q b0 hb0 (A, Replace B e g) := by
  exact p4Q2PZ37AEL_originalPerronDensity_oneLinkHarnack H A B e h g



/-- Unconditional explicit SINGLE-LINK absolute variation of the actual
joint sqrt-density, using AEK's global upper bound. This bound is
coarse: it does not shrink with the chordal size of the link change. -/
theorem p4Q2PZ37AEL_originalSqrtDensity_oneLink_absVariation
    (A B : Cfg) (e : Link) (g h : G) :
    |rho (A, Replace B e g) - rho (A, Replace B e h)| ≤
      (t - 1) *
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
            H b0)⁻¹ ^ 3) := by
  let k := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
  have ht1 : 1 ≤ t := by
    change 1 ≤ Real.exp (8 * b0)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hBounds :=
    (p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H).2
  have hG : rho (A, Replace B e g) ≤ Real.sqrt (k⁻¹ ^ 3) :=
    (hBounds (A, Replace B e g)).2
  have hH : rho (A, Replace B e h) ≤ Real.sqrt (k⁻¹ ^ 3) :=
    (hBounds (A, Replace B e h)).2
  exact p4Q2PZ37AEL_real_twoSidedHarnack_absVariation
    (rho (A, Replace B e g)) (rho (A, Replace B e h))
    t (Real.sqrt (k⁻¹ ^ 3)) ht1 hG hH
    (p4Q2PZ37AEL_originalSqrtDensity_oneLinkHarnack H A B e g h)
    (p4Q2PZ37AEL_originalSqrtDensity_oneLinkReverse H A B e g h)

/-- Unconditional explicit SINGLE-LINK absolute variation for the
ORIGINAL JQ Perron density, retaining the genuine physical numerator
and AEK's original density ceiling. -/
theorem p4Q2PZ37AEL_originalPerronDensity_oneLink_absVariation
    (A B : Cfg) (e : Link) (g h : G) :
    |q b0 hb0 (A, Replace B e g) - q b0 hb0 (A, Replace B e h)| ≤
      (t - 1) *
        (Real.exp (b0 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) /
          Real.sqrt
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
              H b0) ^ 3)) := by
  let k := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
  let E := Real.exp (b0 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)
  have ht1 : 1 ≤ t := by
    change 1 ≤ Real.exp (8 * b0)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hBounds :=
    (p4Q2PZ37AEK_originalPhysicalDensity_explicitWilsonBounds H).2
  have hG : q b0 hb0 (A, Replace B e g) ≤ E / Real.sqrt (k ^ 3) :=
    (hBounds (A, Replace B e g)).2
  have hH : q b0 hb0 (A, Replace B e h) ≤ E / Real.sqrt (k ^ 3) :=
    (hBounds (A, Replace B e h)).2
  exact p4Q2PZ37AEL_real_twoSidedHarnack_absVariation
    (q b0 hb0 (A, Replace B e g)) (q b0 hb0 (A, Replace B e h))
    t (E / Real.sqrt (k ^ 3)) ht1 hG hH
    (p4Q2PZ37AEL_originalPerronDensity_oneLinkHarnack H A B e g h)
    (p4Q2PZ37AEL_originalPerronDensity_oneLinkReverse H A B e g h)


end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEL_real_twoFactorHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalJointWeight_oneLinkHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalSqrtDensity_oneLinkHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalSqrtDensity_oneLinkReverse

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEL_real_commonNumeratorDivHarnack

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalJointWeight_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalSqrtDensity_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalSqrtDensity_firstBoundary_oneLinkHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalPerronDensity_oneLinkHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalPerronDensity_oneLinkReverse

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEL_real_twoSidedHarnack_absVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalSqrtDensity_oneLink_absVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEL_originalPerronDensity_oneLink_absVariation

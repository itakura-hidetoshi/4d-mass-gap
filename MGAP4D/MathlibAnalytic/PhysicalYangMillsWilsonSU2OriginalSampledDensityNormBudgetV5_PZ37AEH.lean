import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalDensityCompactNumeratorFloorV5_PZ37AEG
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEH — certified original physical density floor from a true finite net

AEG proved the exact original fixed-coupling identity
  q_H(z) = ‖T_H‖⁻¹ / rho_H(z)
for the unchanged physical Perron/transfer operator T_H, genuine original
joint sqrt-density rho_H, original FF Gauss-law source and interacting SU(2).

This module makes its finite-H lower-floor interface CHECKABLE from separate
real numerical certifications, without presenting those as already computed:

* a finite set s of ACTUAL original boundary pairs that is a D_H net of
  radius r, as defined in AEE;
* an independently verified true global rho_H oscillation certificate
  D_H(z,w) < r -> |rho_H(z)-rho_H(w)| < epsilon;
* a certified sample table rho_H(a) <= M for each a in s;
* an independently verified upper bound ‖T_H‖ <= U for the ACTUAL
  unnormalized physical Perron/transfer operator.

The verified inputs imply the original unmodified physical normalizer
  0 < 1 / (U*(M+epsilon)) <= q_H(z) for ALL original boundary pairs z.
The denominator and sample set have not been replaced by analytic surrogates.

We also prove actual rho_H continuous and uniformly continuous in the
original full calibrated D_H. Finally the sampled true-density certificate
is inserted into AEF's exact source-dependent Wilson numerator/covariance
modulus and AEE's gauge-opposite two-ball second-moment floor.

No finite net, numerical transfer-norm ceiling, rho samples, uniform
modulus radius, Wilson covariance amplitude, H-uniform coercivity, or
continuum Yang--Mills mass gap is claimed numerically certified.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Pure arithmetic: verified upper bounds on a positive normalizer and
a positive density factor bound the reciprocal physical product below. -/
theorem p4Q2PZ37AEH_realInverseProductFloor
    (t U p P : ℝ) (ht : 0 < t) (htU : t ≤ U)
    (hp : 0 < p) (hpP : p ≤ P) :
    (1 : ℝ) / (U * P) ≤ t⁻¹ / p := by
  have hU : 0 < U := ht.trans_le htU
  have hP : 0 < P := hp.trans_le hpP
  have htInv : U⁻¹ ≤ t⁻¹ :=
    (inv_le_inv₀ ht hU).2 htU
  have hpInv : P⁻¹ ≤ p⁻¹ :=
    (inv_le_inv₀ hp hP).2 hpP
  calc
    (1 : ℝ) / (U * P) = U⁻¹ * P⁻¹ := by
      rw [one_div, mul_inv_rev]
      ring
    _ ≤ t⁻¹ * P⁻¹ :=
      mul_le_mul_of_nonneg_right htInv (inv_nonneg.mpr hP.le)
    _ ≤ t⁻¹ * p⁻¹ :=
      mul_le_mul_of_nonneg_left hpInv (inv_nonneg.mpr ht.le)
    _ = t⁻¹ / p := by rw [div_eq_mul_inv]

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AEH_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEH_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEH_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEH_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEH_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "rho" => continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "N" => p4Q2PZ37AEF_originalCenteredCovarianceNumerator H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Tnorm" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖

local instance p4Q2PZ37AEH_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AEH_pairCompact : CompactSpace Pair := by
  infer_instance

/-- The actual physical joint sqrt-density, not a synthetic density,
is continuous on the genuine compact pair of SU(2) spatial boundaries. -/
theorem p4Q2PZ37AEH_originalSqrtDensity_continuous :
    Continuous (fun z : Pair => rho z) := by
  have hdensity :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_continuous
      H 2 (by norm_num) b0 hb0
  change Continuous (fun z : Pair =>
    Real.sqrt (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
      H 2 (by norm_num) b0 hb0 z))
  exact Real.continuous_sqrt.comp hdensity

/-- Genuine compactness yields a uniform modulus of the SAME original
rho_H in the SAME full two-boundary all-link calibrated D_H distance. -/
theorem p4Q2PZ37AEH_originalSqrtDensity_uniformChordalModulus
    (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧ ∀ z w : Pair,
      D z w < r → |rho z - rho w| < epsilon := by
  exact p4Q2PZ37ADM_compactContinuous_uniformDistanceModulus
    D (p4Q2PZ37ADM_originalFullDistance_jointContinuous H)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_eq_zero_iff H z w)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_nonneg H z w)
    (fun z : Pair => rho z)
    (p4Q2PZ37AEH_originalSqrtDensity_continuous H) epsilon heps

/-- A genuinely verified finite D_H net, genuine density modulus
and a finite verified table give a GLOBAL true rho_H bound. -/
theorem p4Q2PZ37AEH_originalCertifiedSqrtDensityNet_globalUpper
    (s : Finset Pair) (r epsilon M : ℝ)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hMod : ∀ z w : Pair, D z w < r →
      |rho z - rho w| < epsilon)
    (hSamples : ∀ a ∈ s, rho a ≤ M) :
    ∀ z : Pair, rho z < M + epsilon := by
  intro z
  obtain ⟨a, ha, haz⟩ := hNet z
  have hdelta := (abs_lt.mp (hMod a z haz)).1
  have hBound := hSamples a ha
  linarith only [hdelta, hBound]

/-- The actual original SU(2) boundary-pair net is nonempty, so every
verified finite sample majorant M dominates some strictly positive
original physical sqrt-density value. -/
theorem p4Q2PZ37AEH_originalCertifiedNet_sampleMajorant_pos
    (s : Finset Pair) (r M : ℝ)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hSamples : ∀ a ∈ s, rho a ≤ M) :
    0 < M := by
  let z0 : Pair := (originalWilsonExplicitIdentityBoundary H,
    originalWilsonExplicitIdentityBoundary H)
  obtain ⟨a, ha, _⟩ := hNet z0
  exact (continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 a).trans_le
    (hSamples a ha)

/-- Main AEH checkable original density-floor certificate. The only
numerical inputs are an ACTUAL finite D_H covering, TRUE rho_H samples
and modulus, and upper budget U on the ACTUAL physical transfer norm.
A positive H-dependent real formula follows, NOT an H-uniform floor. -/
theorem p4Q2PZ37AEH_originalCertifiedNet_transferNorm_densityFloor
    (s : Finset Pair) (r epsilon M U : ℝ)
    (heps : 0 < epsilon)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hMod : ∀ z w : Pair, D z w < r →
      |rho z - rho w| < epsilon)
    (hSamples : ∀ a ∈ s, rho a ≤ M)
    (hTransferUpper : Tnorm ≤ U) :
    0 < (1 : ℝ) / (U * (M + epsilon)) ∧
      ∀ z : Pair,
        (1 : ℝ) / (U * (M + epsilon)) ≤ q b0 hb0 z := by
  have hT : 0 < Tnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b0 hb0
  have hU : 0 < U := hT.trans_le hTransferUpper
  have hM : 0 < M :=
    p4Q2PZ37AEH_originalCertifiedNet_sampleMajorant_pos H s r M hNet hSamples
  have hBudget : 0 < M + epsilon := add_pos hM heps
  have hFloor : 0 < (1 : ℝ) / (U * (M + epsilon)) :=
    div_pos (by norm_num) (mul_pos hU hBudget)
  refine ⟨hFloor, ?_⟩
  intro z
  have hrho : 0 < rho z :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 z
  have hrhoBudget : rho z ≤ M + epsilon :=
    (p4Q2PZ37AEH_originalCertifiedSqrtDensityNet_globalUpper
      H s r epsilon M hNet hMod hSamples z).le
  have hAlgebra :=
    p4Q2PZ37AEH_realInverseProductFloor
      Tnorm U (rho z) (M + epsilon)
      hT hTransferUpper hrho hrhoBudget
  rw [p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H z]
  exact hAlgebra

/-- The finite-sampled genuine transfer/density floor is directly
admissible as the real denominator certificate of AEF's TRUE Wilson
source-dependent covariance. Separate real numerator bounds/moduli
remain explicit input and are NOT inferred from positivity alone. -/
theorem p4Q2PZ37AEH_originalCertifiedNet_givesCovarianceModulus
    (e : Link) (s : Finset Pair)
    (r epsilon M U R Nmax dN dq : ℝ)
    (heps : 0 < epsilon)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hRhoMod : ∀ z w : Pair, D z w < r →
      |rho z - rho w| < epsilon)
    (hSamples : ∀ a ∈ s, rho a ≤ M)
    (hTransferUpper : Tnorm ≤ U)
    (hNmax : ∀ z : Pair, |N e z| ≤ Nmax)
    (hNmod : ∀ z w : Pair, D z w < R →
      |N e z - N e w| ≤ dN)
    (hQmod : ∀ z w : Pair, D z w < R →
      |q b0 hb0 z - q b0 hb0 w| ≤ dq) :
    ∀ z w : Pair, D z w < R →
      |C b0 hb0 e z - C b0 hb0 e w| ≤
        (dN + (Nmax / ((1 : ℝ) / (U * (M + epsilon)))) * dq) /
          ((1 : ℝ) / (U * (M + epsilon))) := by
  obtain ⟨hPos, hFloor⟩ :=
    p4Q2PZ37AEH_originalCertifiedNet_transferNorm_densityFloor
      H s r epsilon M U heps hNet hRhoMod hSamples hTransferUpper
  exact p4Q2PZ37AEF_originalNumeratorDensity_givesCovarianceModulus
    H e R ((1 : ℝ) / (U * (M + epsilon))) Nmax dN dq
    hPos hFloor hNmax hNmod hQmod

/-- The unchanged original Wilson physical covariance, original
boundary pair-Haar and original two opposite gauge balls inherit
the finite-sampled density certificate through the EXACT AEF moment
theorem. The true physical amplitude-vs-error inequality is a
separate, explicitly visible condition. -/
theorem p4Q2PZ37AEH_originalCertifiedNet_givesDoubleMomentFloor
    (e : Link) (a : Pair) (s : Finset Pair)
    (r epsilon M U R Nmax dN dq : ℝ)
    (heps : 0 < epsilon) (hR : 0 < R)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hRhoMod : ∀ z w : Pair, D z w < r →
      |rho z - rho w| < epsilon)
    (hSamples : ∀ x ∈ s, rho x ≤ M)
    (hTransferUpper : Tnorm ≤ U)
    (hNmax : ∀ z : Pair, |N e z| ≤ Nmax)
    (hNmod : ∀ z w : Pair, D z w < R →
      |N e z - N e w| ≤ dN)
    (hQmod : ∀ z w : Pair, D z w < R →
      |q b0 hb0 z - q b0 hb0 w| ≤ dq)
    (hAmp : (dN + (Nmax / ((1 : ℝ) / (U * (M + epsilon)))) * dq) /
        ((1 : ℝ) / (U * (M + epsilon))) < C b0 hb0 e a) :
    (C b0 hb0 e a -
      (dN + (Nmax / ((1 : ℝ) / (U * (M + epsilon)))) * dq) /
        ((1 : ℝ) / (U * (M + epsilon)))) ^ 2 *
        (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
          (8 * Fintype.card Link)) ≤
      S b0 hb0 e := by
  obtain ⟨hPos, hFloor⟩ :=
    p4Q2PZ37AEH_originalCertifiedNet_transferNorm_densityFloor
      H s r epsilon M U heps hNet hRhoMod hSamples hTransferUpper
  exact p4Q2PZ37AEF_originalCertifiedNumeratorDensity_doubleMomentFloor
    H e a R ((1 : ℝ) / (U * (M + epsilon))) Nmax dN dq
    hR hPos hFloor hNmax hNmod hQmod hAmp

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEH_realInverseProductFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEH_originalSqrtDensity_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEH_originalSqrtDensity_uniformChordalModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEH_originalCertifiedSqrtDensityNet_globalUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEH_originalCertifiedNet_sampleMajorant_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEH_originalCertifiedNet_transferNorm_densityFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEH_originalCertifiedNet_givesCovarianceModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEH_originalCertifiedNet_givesDoubleMomentFloor

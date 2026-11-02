import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCovarianceFiniteNetErrorCertificateV5_PZ37AEE
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEF — original physical covariance numerator/denominator modulus

ACI proves an EXACT ratio for the true centered Gauss-law physical
Wilson FF energy covariance. Its numerator is the true normalized
SU(2) Haar integral of the actual source-dependent link receiver times
the original Wilson character. Its denominator is the SAME strictly
positive physical one-slab Perron/transfer joint density-cancellation
weight from JQ, not an invented posterior normalization.

This file names the unchanged numerator and proves the ratio exactly,
then separates five distinct items in a checkable finite-H interface:
  (1) positive certified lower floor lambda for original density q_H;
  (2) certified upper bound Nmax for |original numerator N_e|;
  (3) certified numerator D_H oscillation bound dN at radius R;
  (4) certified denominator D_H oscillation bound dq at radius R;
  (5) genuine positive original physical covariance at center a.

The real-algebra quotient inequality gives
  |C_e(z)-C_e(w)| <= (dN+(Nmax/lambda)*dq)/lambda
whenever D_H(z,w)<R. Combining it with AEE's true gauge-opposite
double-ball moment proof yields a two-ball lower bound with this EXACT
separate numerator/denominator error certificate. A literal half-radius
rational specialization and a strictly CONDITIONAL FC/GI threshold
corollary keep the original physical quantities unchanged.

ACI/AED already establish qualitative physical nonzero covariance;
we also show the original Haar numerator itself is nonzero somewhere.
Neither q_H's global numeric lambda, numerator numeric bound, a
numeric D_H modulus, nor an evaluated C_e(a) is supplied here.
No synthetic finite group, nonphysical source/receiver, new physical
posterior, H-uniform coercivity, GI numeric success, physical spectral
gap or continuum four-dimensional Yang--Mills mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Division by a TRUE positive denominator with a certified lower
floor turns a numerator absolute bound into a ratio absolute bound.
Neither the numerator nor the denominator is replaced by a surrogate. -/
theorem p4Q2PZ37AEF_realAbsQuotient_le_of_denFloor
    (n q lambda Nmax : ℝ) (hlambda : 0 < lambda)
    (hq : lambda ≤ q) (hN : |n| ≤ Nmax) :
    |n / q| ≤ Nmax / lambda := by
  have hqpos : 0 < q := hlambda.trans_le hq
  have hDiv : |n / q| * q = |n| := by
    rw [abs_div, abs_of_pos hqpos]
    field_simp
  have hProd : |n / q| * lambda ≤ Nmax := by
    calc
      _ ≤ |n / q| * q := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
      _ = |n| := hDiv
      _ ≤ Nmax := hN
  exact (le_div_iff₀ hlambda).mpr hProd

/-- EXACT quotient-variation certificate. The cross term uses the
amplitude at the SECOND point, thus only the first density needs the
lambda floor for its relative fluctuation, while the second density
is merely required positive. No hidden independence or Lipschitz law. -/
theorem p4Q2PZ37AEF_realQuotientVariation_le
    (n₁ n₂ q₁ q₂ lambda dN dq M : ℝ)
    (hlambda : 0 < lambda) (hq₁ : lambda ≤ q₁) (hq₂ : 0 < q₂)
    (hN : |n₁ - n₂| ≤ dN)
    (hQ : |q₁ - q₂| ≤ dq)
    (hM : |n₂ / q₂| ≤ M) :
    |n₁ / q₁ - n₂ / q₂| ≤ (dN + M * dq) / lambda := by
  have hq₁pos : 0 < q₁ := hlambda.trans_le hq₁
  have hId :
      (n₁ / q₁ - n₂ / q₂) * q₁ =
        (n₁ - n₂) + (n₂ / q₂) * (q₂ - q₁) := by
    field_simp [hq₁pos.ne', hq₂.ne']
    ring
  have hAbs :
      |n₁ / q₁ - n₂ / q₂| * q₁ ≤
        |n₁ - n₂| + |n₂ / q₂| * |q₂ - q₁| := by
    calc
      _ = |(n₁ / q₁ - n₂ / q₂) * q₁| := by
        rw [abs_mul, abs_of_pos hq₁pos]
      _ = |(n₁ - n₂) + (n₂ / q₂) * (q₂ - q₁)| := by rw [hId]
      _ ≤ |n₁ - n₂| + |(n₂ / q₂) * (q₂ - q₁)| := abs_add_le _ _
      _ = _ := by rw [abs_mul]
  have hdq : 0 ≤ dq := (abs_nonneg _).trans hQ
  have hQrev : |q₂ - q₁| ≤ dq := by
    simpa only [abs_sub_comm] using hQ
  have hMul :
      |n₂ / q₂| * |q₂ - q₁| ≤ M * dq := by
    calc
      _ ≤ |n₂ / q₂| * dq :=
        mul_le_mul_of_nonneg_left hQrev (abs_nonneg _)
      _ ≤ M * dq := mul_le_mul_of_nonneg_right hM hdq
  have hCross :
      |n₁ / q₁ - n₂ / q₂| * lambda ≤ dN + M * dq := by
    calc
      _ ≤ |n₁ / q₁ - n₂ / q₂| * q₁ :=
        mul_le_mul_of_nonneg_left hq₁ (abs_nonneg _)
      _ ≤ |n₁ - n₂| + |n₂ / q₂| * |q₂ - q₁| := hAbs
      _ ≤ dN + M * dq := add_le_add hN hMul
  exact (le_div_iff₀ hlambda).mpr hCross

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local notation "chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AEF_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEF_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEF_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEF_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEF_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AEF_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

local instance p4Q2PZ37AEF_links : Fintype Link := Fintype.ofFinite _

/-- This is exactly ACI's true SU(2) Haar integral numerator, with the
original centered physical source f0, original link FF receiver from
JQ, and original Wilson one-link character. NOT a new physical law. -/
def p4Q2PZ37AEF_originalCenteredCovarianceNumerator
    (e : Link) (z : Pair) : ℝ :=
  ∫ g : G,
    p4Q2JQ_originalPhysicalSourceLinkReceiver H
      b0 p4Q2PZ37ADC_fixedCoupling_pos.le f0 e z g * chi g ∂mu

local notation "N" => p4Q2PZ37AEF_originalCenteredCovarianceNumerator H

/-- Re-express the true original physical fixed-coupling covariance as
its EXACT ACI Haar numerator divided by its EXACT JQ density weight. -/
theorem p4Q2PZ37AEF_originalCovariance_eq_trueNumerator_div_density
    (e : Link) (z : Pair) :
    C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e z =
      N e z / q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z := by
  exact p4Q2PZ37ACI_originalEnergyCovariance_eq_receiverCharacter
    H b0 p4Q2PZ37ADC_fixedCoupling_pos.le f0 e z

/-- The true physical density denominator is strictly positive at
every boundary pair, retaining all original Perron/transfer factors. -/
theorem p4Q2PZ37AEF_originalDensity_pos (z : Pair) :
    0 < q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z :=
  p4Q2JQ_originalPhysicalGIDensityWeight_pos
    H b0 p4Q2PZ37ADC_fixedCoupling_pos.le z

/-- The TRUE SU(2) Haar numerator of the genuine physical covariance
is nonzero at some original boundary configuration for EVERY physical
link, inherited from AED's positive genuine covariance maximizer. -/
theorem p4Q2PZ37AEF_originalEveryLink_nonzeroTrueNumerator
    (e : Link) :
    ∃ z : Pair, N e z ≠ 0 := by
  obtain ⟨z, hz, _hMax⟩ :=
    p4Q2PZ37AED_originalPositiveMaximumCovariance_exists H e
  refine ⟨z, ?_⟩
  intro hN
  have hC : C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e z = 0 := by
    rw [p4Q2PZ37AEF_originalCovariance_eq_trueNumerator_div_density H e z,
      hN, zero_div]
  exact (ne_of_gt hz) hC

/-- A pointwise original physical numerator certification and a
pointwise density floor give an EXACT physical covariance bound. -/
theorem p4Q2PZ37AEF_originalCertifiedCovariance_abs_le
    (e : Link) (z : Pair) (lambda Nmax : ℝ)
    (hlambda : 0 < lambda)
    (hDenFloor : lambda ≤ q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z)
    (hNumerator : |N e z| ≤ Nmax) :
    |C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e z| ≤
      Nmax / lambda := by
  rw [p4Q2PZ37AEF_originalCovariance_eq_trueNumerator_div_density H e z]
  exact p4Q2PZ37AEF_realAbsQuotient_le_of_denFloor
    (N e z) (q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z)
    lambda Nmax hlambda hDenFloor hNumerator

/-- A certified original physical numerator/density two-point error,
plus an actual numerator amplitude ceiling, controls the genuine
physical Wilson covariance oscillation by the precise quotient rule. -/
theorem p4Q2PZ37AEF_originalCertifiedTwoPointCovarianceError
    (e : Link) (z w : Pair)
    (lambda Nmax dN dq : ℝ)
    (hlambda : 0 < lambda)
    (hDenFloorZ : lambda ≤ q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z)
    (hDenFloorW : lambda ≤ q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w)
    (hNumeratorW : |N e w| ≤ Nmax)
    (hNumErr : |N e z - N e w| ≤ dN)
    (hDenErr : |q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z -
        q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w| ≤ dq) :
    |C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e w| ≤
      (dN + (Nmax / lambda) * dq) / lambda := by
  rw [p4Q2PZ37AEF_originalCovariance_eq_trueNumerator_div_density H e z,
    p4Q2PZ37AEF_originalCovariance_eq_trueNumerator_div_density H e w]
  have hDenWPos : 0 < q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w :=
    hlambda.trans_le hDenFloorW
  have hCw :
      |N e w / q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w| ≤
        Nmax / lambda :=
    p4Q2PZ37AEF_realAbsQuotient_le_of_denFloor
      (N e w) (q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w)
      lambda Nmax hlambda hDenFloorW hNumeratorW
  exact p4Q2PZ37AEF_realQuotientVariation_le
    (N e z) (N e w)
    (q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z)
    (q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w)
    lambda dN dq (Nmax / lambda)
    hlambda hDenFloorZ hDenWPos hNumErr hDenErr hCw

/-- The exact original D_H uniform covariance modulus is reduced to
SEPARATE, potentially verifiable certificates for the genuine
Perron/transfer density, genuine Haar numerator, and true finite-H
global numerator amplitude. No numeric Lipschitz bound is asserted. -/
theorem p4Q2PZ37AEF_originalNumeratorDensity_givesCovarianceModulus
    (e : Link) (R lambda Nmax dN dq : ℝ)
    (hlambda : 0 < lambda)
    (hDenFloor : ∀ z : Pair,
      lambda ≤ q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z)
    (hNmax : ∀ z : Pair, |N e z| ≤ Nmax)
    (hNmod : ∀ z w : Pair, D z w < R →
      |N e z - N e w| ≤ dN)
    (hQmod : ∀ z w : Pair, D z w < R →
      |q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z -
        q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w| ≤ dq) :
    ∀ z w : Pair, D z w < R →
      |C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e w| ≤
      (dN + (Nmax / lambda) * dq) / lambda := by
  intro z w hD
  exact p4Q2PZ37AEF_originalCertifiedTwoPointCovarianceError
    H e z w lambda Nmax dN dq hlambda
    (hDenFloor z) (hDenFloor w) (hNmax w)
    (hNmod z w hD) (hQmod z w hD)

/-- ALL physical objects are unchanged: separately certified genuine
numerator and denominator stability produce a double-ball physical
covariance second-moment floor. The numerical lambda, Nmax, dN, dq
and amplitude are explicit data/premises, NOT asserted to be known.
The radius R remains the same original all-link calibrated D_H radius. -/
theorem p4Q2PZ37AEF_originalCertifiedNumeratorDensity_doubleMomentFloor
    (e : Link) (a : Pair) (R lambda Nmax dN dq : ℝ)
    (hR : 0 < R) (hlambda : 0 < lambda)
    (hDenFloor : ∀ z : Pair,
      lambda ≤ q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z)
    (hNmax : ∀ z : Pair, |N e z| ≤ Nmax)
    (hNmod : ∀ z w : Pair, D z w < R →
      |N e z - N e w| ≤ dN)
    (hQmod : ∀ z w : Pair, D z w < R →
      |q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z -
        q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w| ≤ dq)
    (hAmp : (dN + (Nmax / lambda) * dq) / lambda <
      C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e a) :
    (C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e a -
        (dN + (Nmax / lambda) * dq) / lambda) ^ 2 *
      (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
        (8 * Fintype.card Link)) ≤
      S b0 p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  let eps : ℝ := (dN + (Nmax / lambda) * dq) / lambda
  have hDaa : D a a < R := by
    rw [p4Q2PZ37ADL_originalFullDistance_self H a]
    exact hR
  have hDNP : 0 ≤ dN := by
    have h := hNmod a a hDaa
    simpa only [sub_self, abs_zero] using h
  have hDQP : 0 ≤ dq := by
    have h := hQmod a a hDaa
    simpa only [sub_self, abs_zero] using h
  have hNP : 0 ≤ Nmax :=
    (abs_nonneg (N e a)).trans (hNmax a)
  have hEps : 0 ≤ eps := by
    dsimp [eps]
    exact div_nonneg
      (add_nonneg hDNP (mul_nonneg (div_nonneg hNP hlambda.le) hDQP))
      hlambda.le
  have hMod :=
    p4Q2PZ37AEF_originalNumeratorDensity_givesCovarianceModulus
      H e R lambda Nmax dN dq hlambda hDenFloor hNmax hNmod hQmod
  exact p4Q2PZ37AEE_certifiedTwoSignError_doubleMomentFloor
    H e a R eps hR hEps hAmp hMod

/-- The same genuine numerator/density certificate specialized to
R=1/2 has the exact rational finite-H factor from AED. The fixed
physical half-radius modulus is an EXPLICIT premise, not certified. -/
theorem p4Q2PZ37AEF_originalCertifiedHalfRadiusNumeratorDensity_doubleMomentFloor
    (e : Link) (a : Pair) (lambda Nmax dN dq : ℝ)
    (hlambda : 0 < lambda)
    (hDenFloor : ∀ z : Pair,
      lambda ≤ q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z)
    (hNmax : ∀ z : Pair, |N e z| ≤ Nmax)
    (hNmod : ∀ z w : Pair, D z w < (1 / 2 : ℝ) →
      |N e z - N e w| ≤ dN)
    (hQmod : ∀ z w : Pair, D z w < (1 / 2 : ℝ) →
      |q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z -
        q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w| ≤ dq)
    (hAmp : (dN + (Nmax / lambda) * dq) / lambda <
      C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e a) :
    (C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e a -
        (dN + (Nmax / lambda) * dq) / lambda) ^ 2 *
      (2 * (1 / (8 * (2 * (Fintype.card Link : ℝ) + 1))) ^
        (8 * Fintype.card Link)) ≤
      S b0 p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have h :=
    p4Q2PZ37AEF_originalCertifiedNumeratorDensity_doubleMomentFloor
      H e a (1 / 2) lambda Nmax dN dq
      (by norm_num) hlambda hDenFloor hNmax hNmod hQmod hAmp
  rw [p4Q2PZ37AED_originalHalfRadius_polynomial_eq_rational H] at h
  exact h

/-- A strictly CONDITIONALLY certified original FC comparison is
required to infer a positive original GI SQUARED mean. This is
not a numerical computation or a uniform-in-H Yang--Mills theorem. -/
theorem p4Q2PZ37AEF_originalCertifiedNumeratorDensity_FC_givesGI
    (e : Link) (a : Pair) (R lambda Nmax dN dq : ℝ)
    (hR : 0 < R) (hlambda : 0 < lambda)
    (hDenFloor : ∀ z : Pair,
      lambda ≤ q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z)
    (hNmax : ∀ z : Pair, |N e z| ≤ Nmax)
    (hNmod : ∀ z w : Pair, D z w < R →
      |N e z - N e w| ≤ dN)
    (hQmod : ∀ z w : Pair, D z w < R →
      |q b0 p4Q2PZ37ADC_fixedCoupling_pos.le z -
        q b0 p4Q2PZ37ADC_fixedCoupling_pos.le w| ≤ dq)
    (hAmp : (dN + (Nmax / lambda) * dq) / lambda <
      C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e a)
    (hNumeric :
      (B b0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 <
        272 * ((C b0 p4Q2PZ37ADC_fixedCoupling_pos.le e a -
            (dN + (Nmax / lambda) * dq) / lambda) ^ 2 *
          (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
            (8 * Fintype.card Link)))) :
    0 < Budget b0 p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have hMoment :=
    p4Q2PZ37AEF_originalCertifiedNumeratorDensity_doubleMomentFloor
      H e a R lambda Nmax dN dq hR hlambda
      hDenFloor hNmax hNmod hQmod hAmp
  have hScaled :=
    mul_le_mul_of_nonneg_left hMoment
      (show (0 : ℝ) ≤ 272 by norm_num)
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget H e
    (hNumeric.trans_le hScaled)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEF_realAbsQuotient_le_of_denFloor
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEF_realQuotientVariation_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEF_originalCovariance_eq_trueNumerator_div_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEF_originalDensity_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEF_originalEveryLink_nonzeroTrueNumerator
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEF_originalCertifiedCovariance_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEF_originalCertifiedTwoPointCovarianceError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEF_originalNumeratorDensity_givesCovarianceModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEF_originalCertifiedNumeratorDensity_doubleMomentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEF_originalCertifiedHalfRadiusNumeratorDensity_doubleMomentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEF_originalCertifiedNumeratorDensity_FC_givesGI

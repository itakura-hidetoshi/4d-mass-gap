import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAJAEventualPowerWitnessV5_PZ37AKE
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopEigenvector
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKG — original Wilson small-coupling AJA witness obstruction

This is about the ORIGINAL SU(2) Wilson transfer, signed centered ZW source,
Haar probability and AJA budget, not AKF's abstract countermodel.
The old positive AIL endpoint tau_H is retained without modification.

For 0 < beta <= tau_H, AIL gives P f0 < -3 beta V/4 at every boundary.
For the existing nonnegative unit top vector psi, write I = integral psi.
The actual kernel satisfies K <= 1, hence lambda = <P psi,psi> <= I^2.
Cauchy on the same Haar probability gives 0 <= I <= 1, so lambda <= I.
Symmetry then gives <f0,psi> <= -3 beta V/4. This overlap survives every
normalized Wilson power. The unchanged AIW margin satisfies m <= beta V/2,
and AIL makes the original negative region the whole space, so B=m^2.
Consequently every original natural power has energy >= (9/4) B > B.

No top-simplicity assumption, substitute source, changed margin or new
physical axiom is introduced. The small-coupling interval is H-dependent.
This disproves the all-positive-coupling AJA-witness assertion, NOT a
mass-gap assertion and NOT witness existence at couplings outside the
AIL interval. This leaf is uncertified until its exact-source CI completes.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- An actual nonnegative L2 vector paired with a kernel bounded above by
one has quadratic pairing at most the square of its mass. -/
theorem realL2_nonnegative_kernelPairing_le_mass_sq_akg
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (K : Lp ℝ 2 (mu.prod mu)) (f : Lp ℝ 2 mu)
    (hK : ∀ᵐ z ∂(mu.prod mu), K z ≤ 1)
    (hf : ∀ᵐ x ∂mu, 0 ≤ f x) :
    realL2HilbertSchmidtKernelPairing K f f ≤ (∫ x, f x ∂mu) ^ 2 := by
  have hprodInt : Integrable (realL2ExternalTensorFunction f f) (mu.prod mu) := by
    rw [← memLp_one_iff_integrable]
    exact (realL2ExternalTensorFunction_memLp_two f f).mono_exponent (by norm_num)
  have hfst : ∀ᵐ z ∂(mu.prod mu), 0 ≤ f z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := mu) (ν := mu)).ae hf
  have hsnd : ∀ᵐ z ∂(mu.prod mu), 0 ≤ f z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := mu)).ae hf
  rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
  calc
    (∫ z, inner ℝ (K z) (realL2ExternalTensor f f z) ∂(mu.prod mu)) ≤
        ∫ z, realL2ExternalTensorFunction f f z ∂(mu.prod mu) := by
      apply integral_mono_ae (MeasureTheory.L2.integrable_inner K
        (realL2ExternalTensor f f)) hprodInt
      filter_upwards [hK, hfst, hsnd, realL2ExternalTensor_coeFn f f]
        with z hk hf1 hf2 ht
      rw [ht]
      simp only [realL2ExternalTensorFunction, real_inner_eq_re_inner (𝕜 := ℝ),
        RCLike.inner_apply, RCLike.re_to_real, conj_trivial]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hk (mul_nonneg hf1 hf2)
    _ = (∫ x, f x ∂mu) ^ 2 := by
      change (∫ z : X × X, f z.1 * f z.2 ∂(mu.prod mu)) = _
      rw [integral_prod_mul, pow_two]

/-- A negative a.e. floor for one L2 vector gives an upper bound on its
pairing with an actual nonnegative L2 vector. -/
theorem realL2_inner_le_neg_floor_mul_mass_akg
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (f g : Lp ℝ 2 mu) (a : ℝ)
    (hf : ∀ᵐ x ∂mu, f x ≤ -a)
    (hg : ∀ᵐ x ∂mu, 0 ≤ g x) :
    inner ℝ f g ≤ -a * ∫ x, g x ∂mu := by
  have hgInt : Integrable (fun x => g x) mu :=
    (Lp.memLp g).integrable (by norm_num)
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, inner ℝ (f x) (g x) ∂mu) ≤ ∫ x, (-a) * g x ∂mu := by
      apply integral_mono_ae (MeasureTheory.L2.integrable_inner f g)
        (hgInt.const_mul (-a))
      filter_upwards [hf, hg] with x hx hgx
      simp only [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
        RCLike.re_to_real, conj_trivial]
      calc
        g x * f x = f x * g x := mul_comm _ _
        _ ≤ (-a) * g x := mul_le_mul_of_nonneg_right hx hgx
    _ = -a * ∫ x, g x ∂mu := by rw [integral_const_mul]

/-- One genuine unit fixed direction suffices for an all-power lower bound;
it is not assumed to span the full fixed eigenspace. -/
theorem realHilbert_fixedUnit_power_normSq_ge_neg_overlap_akg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E) (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (psi : E) (hUnit : ‖psi‖ = 1) (hFix : S psi = psi)
    (x : E) (a : ℝ) (ha : 0 ≤ a)
    (hOverlap : inner ℝ x psi ≤ -a) (n : ℕ) :
    a ^ 2 ≤ ‖(S ^ n) x‖ ^ 2 := by
  have hInv : ∀ k : ℕ, inner ℝ ((S ^ k) x) psi = inner ℝ x psi := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply]
        have h := hSymm ((S ^ k) x) psi
        change inner ℝ (S ((S ^ k) x)) psi =
          inner ℝ ((S ^ k) x) (S psi) at h
        rw [hFix] at h
        exact h.trans ih
  have hCS := abs_real_inner_le_norm ((S ^ n) x) psi
  rw [hInv n, hUnit, mul_one] at hCS
  have hAbs : a ≤ |inner ℝ x psi| := by
    have h := neg_le_abs (inner ℝ x psi)
    linarith only [hOverlap, h]
  exact pow_le_pow_left₀ ha (hAbs.trans hCS) 2

local notation "GK" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKG_group : IsTopologicalGroup GK :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKG_compact : CompactSpace GK :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKG_countable : SecondCountableTopology GK :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKG_measurable : MeasurableSpace GK :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKG_borel : BorelSpace GK :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKG_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "CfgK" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muK" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "PhysK" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fK" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "VK" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "pK" => p4Q2PZ37AFZ_plaquetteCount H
local notation "PK" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "SK" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "psiK" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector H 2 (by norm_num)
local notation "tauK" => p4Q2PZ37AIL_elementarySmallCoupling H
local notation "uK" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mK" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AKG_probability : IsProbabilityMeasure muK := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The ACTUAL nonnegative normalized Wilson top vector has Haar mass at
least the ACTUAL raw transfer norm. The original kernel bound K<=1 is used. -/
theorem p4Q2PZ37AKG_originalNonnegativeTop_mass_ge_norm
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖PK beta hbeta‖ ≤ ∫ A : CfgK, (psiK beta hbeta : Lp ℝ 2 muK) A ∂muK := by
  let P : PhysK →L[ℝ] PhysK := PK beta hbeta
  let psi : PhysK := psiK beta hbeta
  let g : Lp ℝ 2 muK := psi
  let K : Lp ℝ 2 (muK.prod muK) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H 2 (by norm_num) beta hbeta
  let I : ℝ := ∫ A : CfgK, g A ∂muK
  have hg : ∀ᵐ A ∂muK, 0 ≤ g A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta
  have hUnit : ‖psi‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) beta hbeta
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta
  have hK : ∀ᵐ z ∂(muK.prod muK), K z ≤ 1 := by
    have hRep := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H 2 (by norm_num) beta hbeta
    filter_upwards [hRep] with z hz
    change K z = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H 2 beta z.1 z.2 at hz
    rw [hz]
    exact (le_abs_self _).trans
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H 2 (by norm_num) beta hbeta z.1 z.2)
  have hPair : realL2HilbertSchmidtKernelPairing K g g = inner ℝ (P psi) psi := by
    change realL2HilbertSchmidtKernelPairing K g g =
      inner ℝ (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta g) g
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
      H 2 (by norm_num) beta hbeta g g).symm
  have hQuad : inner ℝ (P psi) psi = ‖P‖ :=
    realHilbert_inner_eq_opNorm_of_unit_eigen P psi hUnit hEigen
  have hSq : ‖P‖ ≤ I ^ 2 := by
    have h := realL2_nonnegative_kernelPairing_le_mass_sq_akg muK K g hK hg
    rw [hPair, hQuad] at h
    exact h
  let c : PhysK := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hc : ‖c‖ = 1 := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hIeq : inner ℝ c psi = I := by
    change inner ℝ (Lp.const 2 muK (1 : ℝ)) g = I
    exact realL2_inner_const_one_eq_integral g
  have hIle : I ≤ 1 := by
    have h := real_inner_le_norm c psi
    rw [hIeq, hc, hUnit, one_mul] at h
    exact h
  have hI0 : 0 ≤ I := integral_nonneg_of_ae hg
  have hISq : I ^ 2 ≤ I := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hIle hI0
  exact hSq.trans hISq

/-- On AIL's unchanged explicit small-coupling interval, the original
centered ZW source has a quantitatively negative ACTUAL top overlap. -/
theorem p4Q2PZ37AKG_originalSource_nonnegativeTop_overlap_le
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tauK) :
    inner ℝ fK (psiK beta hbeta.le) ≤ -(3 * beta * VK / 4) := by
  let P : PhysK →L[ℝ] PhysK := PK beta hbeta.le
  let psi : PhysK := psiK beta hbeta.le
  let g : Lp ℝ 2 muK := psi
  let a : ℝ := 3 * beta * VK / 4
  let I : ℝ := ∫ A : CfgK, g A ∂muK
  have hV : 0 < VK := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hNorm : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hRaw : ∀ᵐ A ∂muK, ((P fK : PhysK) : Lp ℝ 2 muK) A ≤ -a := by
    filter_upwards [p4Q2PZ37AIW_originalPhysicalTransfer_coeFn H beta hbeta.le fK]
      with A hA
    change ((P fK : PhysK) : Lp ℝ 2 muK) A =
      decomposableOneSliceTransferIntegral H 2 beta fK A at hA
    rw [hA]
    exact (p4Q2PZ37AIL_originalTransfer_lt_negThreeQuarterVariance
      H beta hbeta hSmall A).le
  have hg : ∀ᵐ A ∂muK, 0 ≤ g A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta.le
  have hPair : inner ℝ (P fK) psi ≤ -a * I :=
    realL2_inner_le_neg_floor_mul_mass_akg muK (P fK : Lp ℝ 2 muK) g a hRaw hg
  have hSymm : (P : PhysK →ₗ[ℝ] PhysK).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta.le
  have hEq : inner ℝ (P fK) psi = ‖P‖ * inner ℝ fK psi := by
    calc
      inner ℝ (P fK) psi = inner ℝ fK (P psi) := hSymm fK psi
      _ = ‖P‖ * inner ℝ fK psi := by rw [hEigen, real_inner_smul_right]
  have hMass : ‖P‖ ≤ I :=
    p4Q2PZ37AKG_originalNonnegativeTop_mass_ge_norm H beta hbeta.le
  have hBound : ‖P‖ * inner ℝ fK psi ≤ ‖P‖ * (-a) := by
    calc
      ‖P‖ * inner ℝ fK psi = inner ℝ (P fK) psi := hEq.symm
      _ ≤ -a * I := hPair
      _ ≤ -a * ‖P‖ := mul_le_mul_of_nonpos_left hMass (neg_nonpos.mpr ha)
      _ = ‖P‖ * (-a) := mul_comm _ _
  change inner ℝ fK psi ≤ -a
  by_contra hNot
  have hGt : -a < inner ℝ fK psi := lt_of_not_ge hNot
  exact (not_lt_of_ge hBound) (mul_lt_mul_of_pos_left hGt hNorm)

/-- Every ORIGINAL normalized Wilson power retains the genuine nonnegative
top overlap. No all-top rank, injectivity, or spectral-limit hypothesis. -/
theorem p4Q2PZ37AKG_originalAllPowers_energy_ge_threeQuarterVariance
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tauK) (n : ℕ) :
    (3 * beta * VK / 4) ^ 2 ≤ ‖((SK beta hbeta.le) ^ n) fK‖ ^ 2 := by
  let P : PhysK →L[ℝ] PhysK := PK beta hbeta.le
  let S : PhysK →L[ℝ] PhysK := SK beta hbeta.le
  let psi : PhysK := psiK beta hbeta.le
  have hUnit : ‖psi‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) beta hbeta.le
  have hNorm : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta.le
  have hFix : S psi = psi := by
    change ‖P‖⁻¹ • P psi = psi
    rw [hEigen, smul_smul, inv_mul_cancel₀ hNorm.ne', one_smul]
  have hSymm : (S : PhysK →ₗ[ℝ] PhysK).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hV : 0 < VK := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  exact realHilbert_fixedUnit_power_normSq_ge_neg_overlap_akg S hSymm psi hUnit hFix
    fK (3 * beta * VK / 4) (by positivity)
    (p4Q2PZ37AKG_originalSource_nonnegativeTop_overlap_le H beta hbeta hSmall) n

/-- Compare to the SAME AJA certificate. On AIL's interval the original
negative set has mass one; AIW bounds the original normalized margin. -/
theorem p4Q2PZ37AKG_originalSmallCoupling_AJA_le_halfVariance_sq
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tauK) :
    (mK beta hbeta.le) ^ 2 *
      Measure.real muK {A : CfgK | uK beta hbeta.le A < -(mK beta hbeta.le)} ≤
        (beta * VK / 2) ^ 2 := by
  have hMass :
      Measure.real muK {A : CfgK | uK beta hbeta.le A < -(mK beta hbeta.le)} = 1 := by
    rw [p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original H beta hbeta.le]
    exact p4Q2PZ37AIL_originalFullNegativeRegion_realMeasure_one H beta hbeta hSmall
  have hp : 0 < pK := p4Q2PZ37AHN_count_pos H
  have hV : 0 < VK := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hExp : Real.exp (-(beta * pK)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hbeta.le hp.le))
  have hMargin := (p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds H beta hbeta.le).2
  have hScaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hExp hbeta.le) hV.le
  have hm : mK beta hbeta.le ≤ beta * VK / 2 := by
    linarith only [hMargin, hScaled]
  have hm0 : 0 ≤ mK beta hbeta.le :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta).le
  rw [hMass, mul_one]
  exact pow_le_pow_left₀ hm0 hm 2

/-- Actual-model quantitative obstruction: on AIL's original interval,
ALL natural powers lie at least 9/4 times above the original AJA budget. -/
theorem p4Q2PZ37AKG_originalAllPowers_ge_nineQuarters_AJA
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tauK) (n : ℕ) :
    (9 / 4 : ℝ) * ((mK beta hbeta.le) ^ 2 *
      Measure.real muK {A : CfgK | uK beta hbeta.le A < -(mK beta hbeta.le)}) ≤
        ‖((SK beta hbeta.le) ^ n) fK‖ ^ 2 := by
  have hPower := p4Q2PZ37AKG_originalAllPowers_energy_ge_threeQuarterVariance
    H beta hbeta hSmall n
  have hBudget := p4Q2PZ37AKG_originalSmallCoupling_AJA_le_halfVariance_sq
    H beta hbeta hSmall
  nlinarith only [hPower, hBudget]

/-- No strict ORIGINAL AJA witness exists on the specified nonempty
small-coupling interval. This is not a statement about a surrogate model. -/
theorem p4Q2PZ37AKG_originalSmallCoupling_no_AJA_power_witness
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ tauK) :
    ¬ ∃ n : ℕ, ‖((SK beta hbeta.le) ^ n) fK‖ ^ 2 <
      (mK beta hbeta.le) ^ 2 *
        Measure.real muK {A : CfgK | uK beta hbeta.le A < -(mK beta hbeta.le)} := by
  rintro ⟨n, hWitness⟩
  have hPower := p4Q2PZ37AKG_originalAllPowers_ge_nineQuarters_AJA
    H beta hbeta hSmall n
  have hPositive := p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  linarith only [hPower, hPositive, hWitness]

/-- A specified physical coupling counterexample for EVERY finite H:
use the already defined positive AIL endpoint, not an abstract sequence. -/
theorem p4Q2PZ37AKG_originalAIL_endpoint_no_AJA_power_witness :
    ¬ ∃ n : ℕ,
      ‖((SK tauK (p4Q2PZ37AIL_elementarySmallCoupling_pos H).le) ^ n) fK‖ ^ 2 <
        (mK tauK (p4Q2PZ37AIL_elementarySmallCoupling_pos H).le) ^ 2 *
          Measure.real muK {A : CfgK |
            uK tauK (p4Q2PZ37AIL_elementarySmallCoupling_pos H).le A <
              -(mK tauK (p4Q2PZ37AIL_elementarySmallCoupling_pos H).le)} :=
  p4Q2PZ37AKG_originalSmallCoupling_no_AJA_power_witness H tauK
    (p4Q2PZ37AIL_elementarySmallCoupling_pos H) le_rfl

/-- The all-positive-coupling witness assertion is false for the ORIGINAL
source and AJA margin. No assertion is made beyond AIL's interval. -/
theorem p4Q2PZ37AKG_not_all_positive_couplings_have_original_AJA_witness :
    ¬ (∀ beta : ℝ, ∀ hbeta : 0 < beta, ∃ n : ℕ, 2 ≤ n ∧
      ‖((SK beta hbeta.le) ^ n) fK‖ ^ 2 <
        (mK beta hbeta.le) ^ 2 *
          Measure.real muK {A : CfgK | uK beta hbeta.le A < -(mK beta hbeta.le)}) := by
  intro hEvery
  obtain ⟨n, _hn, hWitness⟩ := hEvery tauK (p4Q2PZ37AIL_elementarySmallCoupling_pos H)
  exact p4Q2PZ37AKG_originalAIL_endpoint_no_AJA_power_witness H ⟨n, hWitness⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Eleven new theorems, each with a separate kernel axiom audit. -/
#print axioms MGAP4D.MathlibAnalytic.realL2_nonnegative_kernelPairing_le_mass_sq_akg
#print axioms MGAP4D.MathlibAnalytic.realL2_inner_le_neg_floor_mul_mass_akg
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fixedUnit_power_normSq_ge_neg_overlap_akg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKG_originalNonnegativeTop_mass_ge_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKG_originalSource_nonnegativeTop_overlap_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKG_originalAllPowers_energy_ge_threeQuarterVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKG_originalSmallCoupling_AJA_le_halfVariance_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKG_originalAllPowers_ge_nineQuarters_AJA
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKG_originalSmallCoupling_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKG_originalAIL_endpoint_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKG_not_all_positive_couplings_have_original_AJA_witness

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalMassSquaredWardFullTopFloorV5_PZ37AKK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKN: direct ORIGINAL AJA comparison retaining the halfweight

Keep the original SU(2) Wilson P, S=P/||P||, centered ZW source f0, Haar,
full top Q, original negative margin m and original negative region.
Let w be the ORIGINAL spatial halfweight, lambda=||P||, Z=Zcross,
a=beta*exp(-2*beta*p)*V, J=integral w*psi and F=<f0,psi> for the actual
nonnegative unit top vector. Retaining w in the existing Ward proof gives
  P f0 <= c*f0-a*w, (lambda-c)*F <= -a*J, lambda <= J^2.
Since c>=0 and F<0 are already proved for the same model,
  a^2 <= lambda*F^2.
The ORIGINAL margin is m=(a/2)*(Z/lambda). The genuine Gaussian partition
bound gives Z^2<=4*lambda whenever beta^2*p/2<=log(4). Consequently
  B_original <= m^2 <= F^2 <= ||Q f0||^2 <= ||S^n f0||^2.
This is an actual no-witness theorem, not a conditional positive witness.
In particular the original fixed beta0=log(3/2)/64 satisfies that bound
at every H<=10, including H=1 beyond the old logarithmic no-go test.
No conclusion for all larger H or all larger beta, and no mass gap claim.
All mathematical declarations below await exact-source kernel verification.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1050000

/-- Bounded measurable original weights preserve L1 integrability. -/
theorem realL2_bounded_weight_integrable_akn
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : Lp ℝ 2 mu) (w : X → ℝ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    Integrable (fun x => w x * g x) mu := by
  have hg : Integrable (fun x => g x) mu :=
    (Lp.memLp g).integrable (by norm_num)
  apply hg.norm.mono' (hw.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards with x
  rw [norm_mul, Real.norm_of_nonneg (hw0 x)]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hw1 x) (norm_nonneg (g x))

/-- Keep the same endpoint weight in the nonnegative kernel mass-square bound. -/
theorem realL2_weighted_kernelPairing_le_mass_sq_akn
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (K : Lp ℝ 2 (mu.prod mu)) (g : Lp ℝ 2 mu)
    (w : X → ℝ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hK : ∀ᵐ z ∂(mu.prod mu), K z ≤ w z.1 * w z.2)
    (hg : ∀ᵐ x ∂mu, 0 ≤ g x) :
    realL2HilbertSchmidtKernelPairing K g g ≤
      (∫ x, w x * g x ∂mu) ^ 2 := by
  have hbase : Integrable (realL2ExternalTensorFunction g g) (mu.prod mu) := by
    rw [← memLp_one_iff_integrable]
    exact (realL2ExternalTensorFunction_memLp_two g g).mono_exponent (by norm_num)
  have hww : Measurable (fun z : X × X => w z.1 * w z.2) :=
    (hw.comp measurable_fst).mul (hw.comp measurable_snd)
  have hweighted : Integrable
      (fun z : X × X => (w z.1 * w z.2) *
        realL2ExternalTensorFunction g g z) (mu.prod mu) := by
    apply hbase.norm.mono'
      (hww.aestronglyMeasurable.mul hbase.aestronglyMeasurable)
    filter_upwards with z
    have hww1 : w z.1 * w z.2 ≤ 1 := by
      calc
        w z.1 * w z.2 ≤ 1 * w z.2 :=
          mul_le_mul_of_nonneg_right (hw1 z.1) (hw0 z.2)
        _ ≤ 1 := by simpa only [one_mul] using hw1 z.2
    rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (hw0 z.1) (hw0 z.2))]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hww1
      (norm_nonneg (realL2ExternalTensorFunction g g z))
  have hfst : ∀ᵐ z ∂(mu.prod mu), 0 ≤ g z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := mu) (ν := mu)).ae hg
  have hsnd : ∀ᵐ z ∂(mu.prod mu), 0 ≤ g z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := mu)).ae hg
  rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
  calc
    (∫ z, inner ℝ (K z) (realL2ExternalTensor g g z) ∂(mu.prod mu)) ≤
        ∫ z, (w z.1 * w z.2) *
          realL2ExternalTensorFunction g g z ∂(mu.prod mu) := by
      apply integral_mono_ae
        (MeasureTheory.L2.integrable_inner K (realL2ExternalTensor g g)) hweighted
      filter_upwards [hK, hfst, hsnd, realL2ExternalTensor_coeFn g g]
        with z hk hg1 hg2 ht
      rw [ht]
      simp only [realL2ExternalTensorFunction, real_inner_eq_re_inner (𝕜 := ℝ),
        RCLike.inner_apply, RCLike.re_to_real, conj_trivial]
      calc
        (g z.1 * g z.2) * K z = K z * (g z.1 * g z.2) := mul_comm _ _
        _ ≤ (w z.1 * w z.2) * (g z.1 * g z.2) :=
          mul_le_mul_of_nonneg_right hk (mul_nonneg hg1 hg2)
    _ = (∫ x, w x * g x ∂mu) ^ 2 := by
      change (∫ z : X × X,
        (w z.1 * w z.2) * (g z.1 * g z.2) ∂(mu.prod mu)) = _
      have hfun : (fun z : X × X =>
          (w z.1 * w z.2) * (g z.1 * g z.2)) =
          (fun z : X × X => (w z.1 * g z.1) * (w z.2 * g z.2)) := by
        funext z
        ring
      rw [hfun, integral_prod_mul, pow_two]

/-- Pair a weighted negative floor with the genuine nonnegative vector. -/
theorem realL2_inner_le_negative_weighted_mass_akn
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (f g : Lp ℝ 2 mu) (w : X → ℝ) (a : ℝ)
    (hInt : Integrable (fun x => w x * g x) mu)
    (hf : ∀ᵐ x ∂mu, f x ≤ -a * w x)
    (hg : ∀ᵐ x ∂mu, 0 ≤ g x) :
    inner ℝ f g ≤ -a * (∫ x, w x * g x ∂mu) := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, inner ℝ (f x) (g x) ∂mu) ≤
        ∫ x, (-a) * (w x * g x) ∂mu := by
      apply integral_mono_ae (MeasureTheory.L2.integrable_inner f g)
        (hInt.const_mul (-a))
      filter_upwards [hf, hg] with x hx hgx
      simp only [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
        RCLike.re_to_real, conj_trivial]
      calc
        g x * f x = f x * g x := mul_comm _ _
        _ ≤ (-a * w x) * g x := mul_le_mul_of_nonneg_right hx hgx
        _ = (-a) * (w x * g x) := by ring
    _ = -a * (∫ x, w x * g x ∂mu) := by rw [integral_const_mul]

/-- The retained weighted mass yields a stronger scaled overlap floor. -/
theorem real_weighted_overlap_scaled_floor_akn
    (lambda a J F c : ℝ) (hlambda : 0 < lambda)
    (ha : 0 ≤ a) (hJ : 0 ≤ J) (hF : F ≤ 0) (hc : 0 ≤ c)
    (hMass : lambda ≤ J ^ 2)
    (hPair : (lambda - c) * F ≤ -a * J) :
    a ^ 2 ≤ lambda * F ^ 2 := by
  have hcF : c * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hF
  have hab : a * J ≤ lambda * (-F) := by nlinarith only [hPair, hcF]
  have hSquare := pow_le_pow_left₀ (mul_nonneg ha hJ) hab 2
  have hScaled := mul_le_mul_of_nonneg_left hMass (sq_nonneg a)
  by_contra hn
  have hlt : lambda * F ^ 2 < a ^ 2 := lt_of_not_ge hn
  have hmul := mul_lt_mul_of_pos_left hlt hlambda
  nlinarith only [hSquare, hScaled, hmul]

/-- Exact original margin algebra; no unknown top-smallness premise. -/
theorem real_original_margin_le_overlap_of_partition_sq_akn
    (lambda a Z m F : ℝ) (hlambda : 0 < lambda)
    (hZ : Z ^ 2 ≤ 4 * lambda)
    (hm : m * lambda = a * Z / 2)
    (hFloor : a ^ 2 ≤ lambda * F ^ 2) :
    m ^ 2 ≤ F ^ 2 := by
  have hSquare := congrArg (fun t : ℝ => t ^ 2) hm
  have hScaledZ := mul_le_mul_of_nonneg_left hZ (sq_nonneg a)
  have hScaledFloor := mul_le_mul_of_nonneg_left hFloor hlambda.le
  by_contra hn
  have hlt : F ^ 2 < m ^ 2 := lt_of_not_ge hn
  have hmul := mul_lt_mul_of_pos_right hlt (pow_pos hlambda 2)
  nlinarith only [hSquare, hScaledZ, hScaledFloor, hmul]

local notation "GN" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKN_group : IsTopologicalGroup GN := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKN_compact : CompactSpace GN := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKN_countable : SecondCountableTopology GN := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKN_measurable : MeasurableSpace GN := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKN_borel : BorelSpace GN := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKN_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "CfgN" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muN" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "PhysN" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fN" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fcN" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "VN" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "pN" => p4Q2PZ37AFZ_plaquetteCount H
local notation "WN" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "wN" => periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2
local notation "KCN" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "TN" => decomposableOneSliceTransferIntegral H 2
local notation "PN" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "SN" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "psiN" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector H 2 (by norm_num)
local notation "ZN" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "rN" => p4Q2PZ37ABN_originalTemporalWilsonCoefficient
local notation "cN" => p4Q2PZ37AKI_originalAffineCoefficient H
local notation "uN" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mN" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AKN_probability : IsProbabilityMeasure muN := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- A bound on the unchanged halfweight, not a substitute weight. -/
theorem p4Q2PZ37AKN_originalHalfWeight_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) (A : CfgN) : wN beta A ≤ 1 := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (div_nonneg hbeta (by norm_num)))
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg H 2 (by norm_num) A)

/-- Retain the actual boundary halfweight in the original affine Ward bound. -/
theorem p4Q2PZ37AKN_originalTransfer_weightedAffineUpper
    (beta : ℝ) (hbeta : 0 < beta) (B : CfgN) :
    TN beta fN B ≤ cN beta * fcN B -
      (beta * Real.exp (-(2 * beta * pN)) * VN) * wN beta B := by
  let e : ℝ := Real.exp (-(beta * (pN / 2)))
  let q : ℝ := Real.exp (-(beta * pN))
  let w : ℝ := wN beta B
  let M : ℝ := ∫ A : CfgN, KCN beta A B * (fcN A) ^ 2 ∂muN
  have he : 0 < e := Real.exp_pos _
  have hq : 0 < q := Real.exp_pos _
  have hw : 0 < w := periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos H 2 beta B
  have he2 : e * e = q := by
    dsimp [e, q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hq2 : q * q = Real.exp (-(2 * beta * pN)) := by
    dsimp [q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hwe : w * e = q * Real.exp (-(beta * fcN B)) := by
    dsimp [w, e, q, periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H B]
    ring
  have hM : q * VN ≤ M := p4Q2PZ37AIS_originalCrossingSecondMoment_wardLower H beta B
  have hScalar := p4Q2PZ37AIE_real_centeredLaplace_quadraticUpper
    beta (pN / 2) (fcN B) hbeta.le (by positivity)
    (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H B)
  have hCorr : 0 ≤ (beta * e) * (fcN B) ^ 2 := by positivity
  have hScalar' : fcN B * Real.exp (-(beta * fcN B)) ≤ fcN B := by
    change 0 ≤ (beta * Real.exp (-(beta * (pN / 2)))) * (fcN B) ^ 2 at hCorr
    nlinarith only [hScalar, hCorr]
  have hFirst : w * e * (ZN beta * (rN beta) ^ 4 * fcN B) ≤ cN beta * fcN B := by
    rw [hwe]
    calc
      _ = cN beta * (fcN B * Real.exp (-(beta * fcN B))) := by
        dsimp [p4Q2PZ37AKI_originalAffineCoefficient, q]
        ring
      _ ≤ cN beta * fcN B :=
        mul_le_mul_of_nonneg_left hScalar'
          (p4Q2PZ37AKI_originalAffineCoefficient_bounds H beta hbeta).1
  have hSecond : (beta * Real.exp (-(2 * beta * pN)) * VN) * w ≤
      w * e * (beta * e * M) := by
    calc
      _ = (beta * q * w) * (q * VN) := by rw [← hq2]; ring
      _ ≤ (beta * q * w) * M := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = w * e * (beta * e * M) := by
        calc
          _ = beta * w * (e * e) * M := by rw [he2]; ring
          _ = _ := by ring
  have hUpper := p4Q2PZ37AIN_originalRightWeightedTransfer_quadraticUpper H beta hbeta.le B
  have hCancel : w * Real.exp ((beta / 2) * WN B) = 1 := by
    dsimp [w, periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight]
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  calc
    TN beta fN B = w * (Real.exp ((beta / 2) * WN B) * TN beta fN B) := by
      rw [← mul_assoc, hCancel, one_mul]
    _ ≤ w * (e * (ZN beta * (rN beta) ^ 4 * fcN B - (beta * e) * M)) :=
      mul_le_mul_of_nonneg_left hUpper hw.le
    _ = w * e * (ZN beta * (rN beta) ^ 4 * fcN B) - w * e * (beta * e * M) := by ring
    _ ≤ cN beta * fcN B - (beta * Real.exp (-(2 * beta * pN)) * VN) * w :=
      sub_le_sub hFirst hSecond

/-- The same halfweight appears in the actual unit-top kernel pairing. -/
theorem p4Q2PZ37AKN_originalHalfWeightedTop_massSq_ge_norm
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖PN beta hbeta‖ ≤
      (∫ A : CfgN, wN beta A * (psiN beta hbeta : Lp ℝ 2 muN) A ∂muN) ^ 2 := by
  let P : PhysN →L[ℝ] PhysN := PN beta hbeta
  let psi : PhysN := psiN beta hbeta
  let g : Lp ℝ 2 muN := psi
  let K : Lp ℝ 2 (muN.prod muN) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2 H 2 (by norm_num) beta hbeta
  have hg : ∀ᵐ A ∂muN, 0 ≤ g A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta
  have hw0 : ∀ A : CfgN, 0 ≤ wN beta A :=
    fun A => (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos H 2 beta A).le
  have hw1 : ∀ A : CfgN, wN beta A ≤ 1 :=
    p4Q2PZ37AKN_originalHalfWeight_le_one H beta hbeta
  have hK : ∀ᵐ z ∂(muN.prod muN), K z ≤ wN beta z.1 * wN beta z.2 := by
    have hRep := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H 2 (by norm_num) beta hbeta
    filter_upwards [hRep] with z hz
    change K z = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta z.1 z.2 at hz
    rw [hz]
    have hKC : KCN beta z.1 z.2 ≤ 1 := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_nonneg H 2 (by norm_num) z.1 z.2)
    change wN beta z.1 * KCN beta z.1 z.2 * wN beta z.2 ≤ wN beta z.1 * wN beta z.2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKC (hw0 z.1)) (hw0 z.2)
  have hPair : realL2HilbertSchmidtKernelPairing K g g = inner ℝ (P psi) psi := by
    change realL2HilbertSchmidtKernelPairing K g g =
      inner ℝ (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta g) g
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
      H 2 (by norm_num) beta hbeta g g).symm
  have hUnit : ‖psi‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm H 2 (by norm_num) beta hbeta
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen H 2 (by norm_num) beta hbeta
  have hQuad : inner ℝ (P psi) psi = ‖P‖ :=
    realHilbert_inner_eq_opNorm_of_unit_eigen P psi hUnit hEigen
  have h := realL2_weighted_kernelPairing_le_mass_sq_akn muN K g (wN beta)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H 2 beta).measurable
    hw0 hw1 hK hg
  rw [hPair, hQuad] at h
  exact h

/-- Direct all-positive-coupling scaled top-overlap floor for the original source. -/
theorem p4Q2PZ37AKN_originalOverlap_scaledHalfWeightedFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    (beta * Real.exp (-(2 * beta * pN)) * VN) ^ 2 ≤
      ‖PN beta hbeta.le‖ * (inner ℝ fN (psiN beta hbeta.le)) ^ 2 := by
  let P : PhysN →L[ℝ] PhysN := PN beta hbeta.le
  let psi : PhysN := psiN beta hbeta.le
  let g : Lp ℝ 2 muN := psi
  let a : ℝ := beta * Real.exp (-(2 * beta * pN)) * VN
  let c : ℝ := cN beta
  let J : ℝ := ∫ A : CfgN, wN beta A * g A ∂muN
  let F : ℝ := inner ℝ fN psi
  have hNorm : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos H 2 (by norm_num) beta hbeta.le
  have hV : 0 < VN := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hg : ∀ᵐ A ∂muN, 0 ≤ g A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta.le
  have hw0 : ∀ A : CfgN, 0 ≤ wN beta A :=
    fun A => (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos H 2 beta A).le
  have hJ : 0 ≤ J := by
    apply integral_nonneg_of_ae
    filter_upwards [hg] with A hgA
    exact mul_nonneg (hw0 A) hgA
  have hInt : Integrable (fun A : CfgN => wN beta A * g A) muN :=
    realL2_bounded_weight_integrable_akn muN g (wN beta)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H 2 beta).measurable
      hw0 (p4Q2PZ37AKN_originalHalfWeight_le_one H beta hbeta.le)
  have hSource : (fun A : CfgN => (fN : Lp ℝ 2 muN) A) =ᵐ[muN] fcN := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal)) (μ := muN) fcN
  have hRaw : ∀ᵐ A ∂muN,
      (((P fN : PhysN) : Lp ℝ 2 muN) - c • (fN : Lp ℝ 2 muN)) A ≤ -a * wN beta A := by
    filter_upwards [Lp.coeFn_sub ((P fN : PhysN) : Lp ℝ 2 muN) (c • (fN : Lp ℝ 2 muN)),
      Lp.coeFn_smul c (fN : Lp ℝ 2 muN),
      p4Q2PZ37AIW_originalPhysicalTransfer_coeFn H beta hbeta.le fN, hSource]
      with A hSub hSmul hPA hfA
    simp only [Pi.sub_apply] at hSub
    simp only [Pi.smul_apply, smul_eq_mul] at hSmul
    rw [hSub, hSmul, hPA, hfA]
    have h := p4Q2PZ37AKN_originalTransfer_weightedAffineUpper H beta hbeta A
    change TN beta fN A - c * fcN A ≤ -a * wN beta A
    linarith only [h]
  have hPair := realL2_inner_le_negative_weighted_mass_akn muN
    (((P fN : PhysN) : Lp ℝ 2 muN) - c • (fN : Lp ℝ 2 muN)) g
    (wN beta) a hInt hRaw hg
  change inner ℝ (P fN - c • fN) psi ≤ -a * J at hPair
  rw [inner_sub_left (𝕜 := ℝ) (P fN : PhysN) (c • fN) psi,
    real_inner_smul_left (fN : PhysN) psi c] at hPair
  have hSymm : (P : PhysN →ₗ[ℝ] PhysN).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric H 2 (by norm_num) beta hbeta.le
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen H 2 (by norm_num) beta hbeta.le
  have hEq : inner ℝ (P fN) psi = ‖P‖ * F := by
    calc
      inner ℝ (P fN) psi = inner ℝ fN (P psi) := hSymm fN psi
      _ = ‖P‖ * F := by
        rw [hEigen]
        exact real_inner_smul_right (fN : PhysN) psi ‖P‖
  rw [hEq] at hPair
  have hAffine : (‖P‖ - c) * F ≤ -a * J := by nlinarith only [hPair]
  have hF : F ≤ 0 := by
    have h := p4Q2PZ37AKI_originalSource_top_overlap_allPositive H beta hbeta
    have hd : 0 ≤ p4Q2PZ37AKI_originalWardTopFloor H beta := by
      unfold p4Q2PZ37AKI_originalWardTopFloor
      positivity
    exact h.trans (neg_nonpos.mpr hd)
  exact real_weighted_overlap_scaled_floor_akn ‖P‖ a J F c hNorm ha hJ hF
    (p4Q2PZ37AKI_originalAffineCoefficient_bounds H beta hbeta).1
    (p4Q2PZ37AKN_originalHalfWeightedTop_massSq_ge_norm H beta hbeta.le) hAffine

/-- The original partition comparison is proved from a scalar quadratic region. -/
theorem p4Q2PZ37AKN_originalPartition_sq_le_four_norm
    (beta : ℝ) (hbeta : 0 < beta)
    (hQuadratic : beta ^ 2 * pN / 2 ≤ Real.log 4) :
    (ZN beta) ^ 2 ≤ 4 * ‖PN beta hbeta.le‖ := by
  have hZ := p4Q2PZ37AIF_originalCrossingPartition_pos H beta
  have hExp : ZN beta ≤ 4 * Real.exp (-(beta * pN)) := by
    calc
      ZN beta ≤ Real.exp (pN * (-beta + beta ^ 2 / 2)) :=
        p4Q2PZ37AIQ_originalCrossingPartition_le_gaussian H beta
      _ = Real.exp (-(beta * pN)) * Real.exp (beta ^ 2 * pN / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(beta * pN)) * Real.exp (Real.log 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hQuadratic) (Real.exp_pos _).le
      _ = 4 * Real.exp (-(beta * pN)) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        ring
  have hMul := mul_le_mul_of_nonneg_right hExp hZ.le
  have hNorm := p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean H beta hbeta.le
  nlinarith only [hMul, hNorm]

/-- Actual original Haar budget lies below the complete top energy on the
quadratic region. Top-smallness is a conclusion's negation, not a premise. -/
theorem p4Q2PZ37AKN_originalAJA_budget_le_fullTop_of_quadratic
    (beta : ℝ) (hbeta : 0 < beta)
    (hQuadratic : beta ^ 2 * pN / 2 ≤ Real.log 4) :
    (mN beta hbeta.le) ^ 2 *
      Measure.real muN {A : CfgN | uN beta hbeta.le A < -(mN beta hbeta.le)} ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 := by
  let lambda : ℝ := ‖PN beta hbeta.le‖
  let a : ℝ := beta * Real.exp (-(2 * beta * pN)) * VN
  let F : ℝ := inner ℝ fN (psiN beta hbeta.le)
  have hNorm : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos H 2 (by norm_num) beta hbeta.le
  have hm : mN beta hbeta.le * lambda = a * ZN beta / 2 := by
    rw [p4Q2PZ37AIW_originalNormalizedNegativeMargin_eq_relativeFactor H beta hbeta.le]
    change (a / 2 * (ZN beta / lambda)) * lambda = a * ZN beta / 2
    field_simp [hNorm.ne']
    <;> ring
  have hMargin : (mN beta hbeta.le) ^ 2 ≤ F ^ 2 :=
    real_original_margin_le_overlap_of_partition_sq_akn
      lambda a (ZN beta) (mN beta hbeta.le) F hNorm
      (p4Q2PZ37AKN_originalPartition_sq_le_four_norm H beta hbeta hQuadratic) hm
      (p4Q2PZ37AKN_originalOverlap_scaledHalfWeightedFloor H beta hbeta)
  have hMass := p4Q2PZ37AJW_originalNegativeRegion_realMeasure_le_one H beta hbeta.le
  calc
    _ ≤ (mN beta hbeta.le) ^ 2 * 1 := mul_le_mul_of_nonneg_left hMass (sq_nonneg _)
    _ = (mN beta hbeta.le) ^ 2 := mul_one _
    _ ≤ F ^ 2 := hMargin
    _ ≤ ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 :=
      p4Q2PZ37AKK_originalNonnegativeTop_overlap_sq_le_fullTop H beta hbeta

/-- An actual all-natural-power obstruction in the enlarged quadratic region. -/
theorem p4Q2PZ37AKN_originalQuadratic_no_AJA_power_witness
    (beta : ℝ) (hbeta : 0 < beta)
    (hQuadratic : beta ^ 2 * pN / 2 ≤ Real.log 4) :
    ¬ ∃ n : ℕ, ‖((SN beta hbeta.le) ^ n) fN‖ ^ 2 <
      (mN beta hbeta.le) ^ 2 *
        Measure.real muN {A : CfgN | uN beta hbeta.le A < -(mN beta hbeta.le)} := by
  rintro ⟨n, hn⟩
  exact (not_lt_of_ge
    ((p4Q2PZ37AKN_originalAJA_budget_le_fullTop_of_quadratic H beta hbeta hQuadratic).trans
      (p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower H beta hbeta n))) hn

/-- The actual fixed beta0 is in the new region at each original H<=10.
All numerical bounds are proved; no measured top/budget comparison is input. -/
theorem p4Q2PZ37AKN_originalFixedCoupling_quadratic_at_le_ten
    (hH : H ≤ 10) : beta0 ^ 2 * pN / 2 ≤ Real.log 4 := by
  have hb0 : 0 ≤ beta0 := p4Q2PZ37ADC_fixedCoupling_pos.le
  have hb : beta0 ≤ (1 / 128 : ℝ) := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    change Real.log (3 / 2 : ℝ) / 64 ≤ (1 / 128 : ℝ)
    norm_num at hlog
    linarith only [hlog]
  have hHR : (H : ℝ) ≤ 10 := by exact_mod_cast hH
  have hCube : ((H : ℝ) + 1) ^ 3 ≤ (11 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (H : ℝ) + 1) (by linarith only [hHR]) 3
  have hp : pN ≤ 31944 := by
    rw [p4Q2PZ37AIB_plaquetteCount_exact]
    norm_num at hCube ⊢
    nlinarith only [hCube]
  have hbSq := pow_le_pow_left₀ hb0 hb 2
  have hMul1 := mul_le_mul_of_nonneg_right hbSq (p4Q2PZ37AHN_count_pos H).le
  have hMul2 := mul_le_mul_of_nonneg_left hp (sq_nonneg (1 / 128 : ℝ))
  have hSmall : beta0 ^ 2 * pN / 2 < 1 := by nlinarith only [hMul1, hMul2]
  have hlog2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    norm_num at hlog2
    linarith only [heq, hlog2]
  exact hSmall.le.trans hlog4

/-- A fully unconditional original fixed-coupling no-witness family H<=10,
including the formerly open candidate H=1. No source or budget is replaced. -/
theorem p4Q2PZ37AKN_originalFixedCoupling_le_ten_no_AJA_power_witness
    (hH : H ≤ 10) :
    ¬ ∃ n : ℕ,
      ‖((SN beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n) fN‖ ^ 2 <
        (mN beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
          Measure.real muN {A : CfgN |
            uN beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
              -(mN beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)} :=
  p4Q2PZ37AKN_originalQuadratic_no_AJA_power_witness H beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKN_originalFixedCoupling_quadratic_at_le_ten H hH)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.realL2_bounded_weight_integrable_akn
#print axioms MGAP4D.MathlibAnalytic.realL2_weighted_kernelPairing_le_mass_sq_akn
#print axioms MGAP4D.MathlibAnalytic.realL2_inner_le_negative_weighted_mass_akn
#print axioms MGAP4D.MathlibAnalytic.real_weighted_overlap_scaled_floor_akn
#print axioms MGAP4D.MathlibAnalytic.real_original_margin_le_overlap_of_partition_sq_akn
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKN_originalHalfWeight_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKN_originalTransfer_weightedAffineUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKN_originalHalfWeightedTop_massSq_ge_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKN_originalOverlap_scaledHalfWeightedFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKN_originalPartition_sq_le_four_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKN_originalAJA_budget_le_fullTop_of_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKN_originalQuadratic_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKN_originalFixedCoupling_quadratic_at_le_ten
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKN_originalFixedCoupling_le_ten_no_AJA_power_witness

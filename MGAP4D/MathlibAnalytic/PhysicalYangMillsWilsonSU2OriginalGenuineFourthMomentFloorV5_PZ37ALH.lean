import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSharpEvenLaplacePhysicalNormV5_PZ37ALG
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALH — genuine Haar fourth moment and Wilson norm correction

ALG's sharp even exponential inequality and ALB's true diagonal-center
pair-Haar symmetry imply a genuine positive higher-order correction
to the full original SU(2) Wilson one-slab physical norm. Reapplying
ALG's sharp bound at half-argument and the exact exponential
double-angle identity proves

  1 + x^2/2 + x^4/32 <= (exp(x)+exp(-x))/2.

This lower coefficient is deliberately not called optimal. In
the unchanged original crossing-weighted pair Haar, introduce the
TRUE fourth physical source moment

  M4_H(beta) = int Kcross_H(beta,A,B)*(f_H(A)+f_H(B))^4 dmu_pair.

The existing exact normalized independent boundary Haar identity
int (f(A)+f(B))^2 = 2 V_H and the elementary square inequality
prove int (f(A)+f(B))^4 >= (2 V_H)^2. Combined with the TRUE
Wilson crossing kernel floor, obtain the positive finite-H bound

  M4_H(beta) >= kFloor_H(beta)*(2 V_H)^2
             >= kFloor_H(beta)*(2 vBox_H)^2 > 0.

The full physical norm has the ORIGINAL both-halfweights estimate

  ||P_H(beta)|| >= exp(-beta*p_H)
    * (Zcross_H(beta) + beta^2/2*M2_H(beta)
       + beta^4/32*M4_H(beta)).

No Gaussian measure, independent crossed kernel, or new operator is
introduced. Finite-volume moments alone cannot establish an H-uniform
coercivity estimate, original r22 mass, AJA witness, Hamiltonian gap,
or continuum Yang-Mills mass gap.

Append-only / tighten-only / overwrite-forbidden / same-root.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

/-- A dyadic fourth-order correction from ALG's already authenticated
optimal quadratic bound and the exponential double angle. The factor
1/32 is proven, not asserted to be the optimal cosh quartic 1/24. -/
theorem p4Q2PZ37ALH_real_expSymm_ge_fourth (x : ℝ) :
    1 + x ^ 2 / 2 + x ^ 4 / 32 ≤
      (Real.exp x + Real.exp (-x)) / 2 := by
  let u : ℝ := Real.exp (x / 2)
  let v : ℝ := Real.exp (-(x / 2))
  let a : ℝ := 2 + x ^ 2 / 4
  have hHalf : a ≤ u + v := by
    dsimp [a, u, v]
    have h := p4Q2PZ37ALG_real_expSymm_ge_halfQuadratic (x / 2)
    nlinarith only [h]
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have huv : 0 ≤ u + v :=
    add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hSq : a ^ 2 ≤ (u + v) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hHalf) (add_nonneg huv ha)
    nlinarith only [h]
  have hu : u ^ 2 = Real.exp x := by
    dsimp [u]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hv : v ^ 2 = Real.exp (-x) := by
    dsimp [v]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have huvOne : u * v = 1 := by
    dsimp [u, v]
    rw [← Real.exp_add]
    simp
  dsimp [a] at hSq
  nlinarith only [hSq, hu, hv, huvOne]

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALH_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALH_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALH_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALH_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALH_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALH_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pairH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "KC" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "Lpair" => p4Q2PZ37ALB_originalPairCrossingLaplace H
local notation "M2pair" => p4Q2PZ37ALC_originalPairCrossingSecondMoment H
local notation "kFloor" => p4Q2PZ37ALE_originalCrossingKernelFloor H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "vBox" => p4Q2PZ37ALF_originalIdentityBoxVarianceFloor H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "PW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num)

local instance p4Q2PZ37ALH_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

local instance p4Q2PZ37ALH_pairProbability : IsProbabilityMeasure pairH := by
  change IsProbabilityMeasure (Measure.prod muH muH)
  infer_instance

/-- Exact fourth moment of the ORIGINAL SU(2) Wilson crossing kernel,
original centered Gauss-law physical source, and original normalized
product Haar. No new physical distribution is introduced. -/
def p4Q2PZ37ALH_originalPairCrossingFourthMoment (beta : ℝ) : ℝ :=
  ∫ P : Cfg × Cfg,
    KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 4 ∂pairH

local notation "M4pair" => p4Q2PZ37ALH_originalPairCrossingFourthMoment H

/-- Finite-volume compactness makes the true unweighted fourth
moment integrable before any Jensen/Cauchy algebra. -/
theorem p4Q2PZ37ALH_originalPairSourceFourth_integrable :
    Integrable (fun P : Cfg × Cfg =>
      (fCont P.1 + fCont P.2) ^ 4) pairH := by
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  exact ((hf1.add hf2).pow 4).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Integrability of the TRUE original crossing-weighted fourth moment. -/
theorem p4Q2PZ37ALH_originalPairCrossingFourth_integrable (beta : ℝ) :
    Integrable (fun P : Cfg × Cfg =>
      KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 4) pairH := by
  have hKC : Continuous (fun P : Cfg × Cfg => KC beta P.1 P.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous
      H 2 beta
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  exact (hKC.mul ((hf1.add hf2).pow 4)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Original crossing fourth moment is nonnegative for every beta.
The physical kernel is a positive exponential, not an action. -/
theorem p4Q2PZ37ALH_originalPairCrossingFourth_nonneg (beta : ℝ) :
    0 ≤ M4pair beta := by
  unfold p4Q2PZ37ALH_originalPairCrossingFourthMoment
  apply integral_nonneg
  intro P
  exact mul_nonneg
    (p4Q2PZ37AIN_originalCrossingKernel_pos H beta P.1 P.2).le
    (by positivity)

/-- True probability-Haar Jensen inequality for the UNWEIGHTED
two-boundary original source: E[S^4] >= E[S²]^2.
The identity E[S²]=2 V_H comes from ALE's genuine product-Haar Fubini
and zero unweighted mixed term, NOT any crossed-kernel independence. -/
theorem p4Q2PZ37ALH_originalUnweightedPairFourth_ge_varianceSq :
    (2 * Vsrc) ^ 2 ≤
      (∫ P : Cfg × Cfg,
        (fCont P.1 + fCont P.2) ^ 4 ∂pairH) := by
  have hSecond :=
    p4Q2PZ37ALE_originalPairSourceSquare_integrable H
  have hFourth :=
    p4Q2PZ37ALH_originalPairSourceFourth_integrable H
  have hLower :
      Integrable (fun P : Cfg × Cfg =>
        (4 * Vsrc) * (fCont P.1 + fCont P.2) ^ 2 -
          (2 * Vsrc) ^ 2) pairH :=
    (hSecond.const_mul (4 * Vsrc)).sub (integrable_const _)
  have hPoint (P : Cfg × Cfg) :
      (4 * Vsrc) * (fCont P.1 + fCont P.2) ^ 2 -
          (2 * Vsrc) ^ 2 ≤
        (fCont P.1 + fCont P.2) ^ 4 := by
    nlinarith only
      [sq_nonneg ((fCont P.1 + fCont P.2) ^ 2 - (2 * Vsrc))]
  have hMono := integral_mono hLower hFourth hPoint
  have hLowerValue :
      (∫ P : Cfg × Cfg,
        (4 * Vsrc) * (fCont P.1 + fCont P.2) ^ 2 -
          (2 * Vsrc) ^ 2 ∂pairH) = (2 * Vsrc) ^ 2 := by
    rw [integral_sub (hSecond.const_mul (4 * Vsrc))
      (integrable_const _), integral_const_mul,
      p4Q2PZ37ALE_originalUnweightedPairSourceSquare_eq_twiceVariance H]
    simp
    ring
  rw [hLowerValue] at hMono
  exact hMono

/-- The genuine exponentially weighted Wilson fourth moment has an
explicit positive floor, using the ORIGINAL crossing KERNEL bound and
normalized unweighted product-Haar Jensen. No factorization of
crossing-weighted moments is made. -/
theorem p4Q2PZ37ALH_originalPairFourth_ge_trueHaarVarianceSq
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    kFloor beta * (2 * Vsrc) ^ 2 ≤ M4pair beta := by
  have hFourth :=
    p4Q2PZ37ALH_originalPairSourceFourth_integrable H
  have hWeighted :=
    p4Q2PZ37ALH_originalPairCrossingFourth_integrable H beta
  have hPoint (P : Cfg × Cfg) :
      kFloor beta * (fCont P.1 + fCont P.2) ^ 4 ≤
        KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 4 :=
    mul_le_mul_of_nonneg_right
      (p4Q2PZ37ALE_originalCrossingKernel_ge_floor H beta hbeta P.1 P.2)
      (by positivity)
  have hInt :=
    integral_mono (hFourth.const_mul (kFloor beta)) hWeighted hPoint
  rw [integral_const_mul] at hInt
  have hJensen :=
    p4Q2PZ37ALH_originalUnweightedPairFourth_ge_varianceSq H
  exact
    (mul_le_mul_of_nonneg_left hJensen
      (p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta).le).trans hInt

/-- Strict positivity of the fourth moment follows from the ORIGINAL
AHN positive Haar variance, without assuming a numerical Haar mass. -/
theorem p4Q2PZ37ALH_originalPairCrossingFourth_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < M4pair beta := by
  have hk := p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta
  have hv := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hPos : 0 < kFloor beta * (2 * Vsrc) ^ 2 := by
    have hs : 0 < (2 * Vsrc) ^ 2 := by positivity
    exact mul_pos hk hs
  exact hPos.trans_le
    (p4Q2PZ37ALH_originalPairFourth_ge_trueHaarVarianceSq H beta hbeta)

/-- The ORIGINAL pair-Haar exponential Laplace integral has a genuine
non-Gaussian fourth-order positive correction at arbitrary real beta,t. -/
theorem p4Q2PZ37ALH_originalPairLaplace_ge_genuineFourthMoment
    (beta t : ℝ) :
    Zcross beta +
        (t ^ 2 / 2) * M2pair beta +
        (t ^ 4 / 32) * M4pair beta ≤ Lpair beta t := by
  have hKCInt := p4Q2PZ37AIV_originalCrossingKernel_pair_integrable H beta
  have hM2Int :=
    p4Q2PZ37ALC_originalPairCrossingSecondMoment_integrable H beta
  have hM4Int :=
    p4Q2PZ37ALH_originalPairCrossingFourth_integrable H beta
  have hPlus := p4Q2PZ37ALB_originalPairLaplace_integrable H beta t
  have hMinus := p4Q2PZ37ALB_originalPairLaplace_integrable H beta (-t)
  have hLowerInt :
      Integrable (fun P : Cfg × Cfg =>
        KC beta P.1 P.2 +
          (t ^ 2 / 2) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) +
          (t ^ 4 / 32) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 4)) pairH :=
    (hKCInt.add (hM2Int.const_mul (t ^ 2 / 2))).add
      (hM4Int.const_mul (t ^ 4 / 32))
  have hSymInt :
      Integrable (fun P : Cfg × Cfg =>
        KC beta P.1 P.2 *
          ((Real.exp (t * (fCont P.1 + fCont P.2)) +
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2)) pairH := by
    have hI := (hPlus.add hMinus).const_mul (1 / 2 : ℝ)
    convert hI using 1
    ext P
    dsimp only [Pi.add_apply]
    ring
  have hPointwise (P : Cfg × Cfg) :
      KC beta P.1 P.2 +
          (t ^ 2 / 2) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) +
          (t ^ 4 / 32) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 4) ≤
        KC beta P.1 P.2 *
          ((Real.exp (t * (fCont P.1 + fCont P.2)) +
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2) := by
    let s : ℝ := fCont P.1 + fCont P.2
    have hKC : 0 ≤ KC beta P.1 P.2 :=
      (p4Q2PZ37AIN_originalCrossingKernel_pos H beta P.1 P.2).le
    have hExp :
        1 + (t * s) ^ 2 / 2 + (t * s) ^ 4 / 32 ≤
          (Real.exp (t * s) + Real.exp ((-t) * s)) / 2 := by
      simpa only [neg_mul] using
        p4Q2PZ37ALH_real_expSymm_ge_fourth (t * s)
    calc
      _ = KC beta P.1 P.2 *
          (1 + (t * s) ^ 2 / 2 + (t * s) ^ 4 / 32) := by
            dsimp [s]
            ring
      _ ≤ KC beta P.1 P.2 *
          ((Real.exp (t * s) + Real.exp ((-t) * s)) / 2) :=
        mul_le_mul_of_nonneg_left hExp hKC
      _ = _ := by rfl
  have hValue :
      (∫ P : Cfg × Cfg,
        KC beta P.1 P.2 +
          (t ^ 2 / 2) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) +
          (t ^ 4 / 32) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 4) ∂pairH) =
      Zcross beta +
        (t ^ 2 / 2) * M2pair beta +
        (t ^ 4 / 32) * M4pair beta := by
    rw [integral_add
      (hKCInt.add (hM2Int.const_mul (t ^ 2 / 2)))
      (hM4Int.const_mul (t ^ 4 / 32)),
      integral_add hKCInt (hM2Int.const_mul (t ^ 2 / 2)),
      integral_const_mul, integral_const_mul,
      p4Q2PZ37AIV_originalCrossingKernel_pair_integral H beta]
    rfl
  calc
    Zcross beta + (t ^ 2 / 2) * M2pair beta +
        (t ^ 4 / 32) * M4pair beta =
      (∫ P : Cfg × Cfg,
        KC beta P.1 P.2 +
          (t ^ 2 / 2) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) +
          (t ^ 4 / 32) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 4) ∂pairH) :=
      hValue.symm
    _ ≤ (∫ P : Cfg × Cfg,
        KC beta P.1 P.2 *
          ((Real.exp (t * (fCont P.1 + fCont P.2)) +
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2) ∂pairH) :=
      integral_mono hLowerInt hSymInt hPointwise
    _ = Lpair beta t :=
      (p4Q2PZ37ALB_originalPairLaplace_symmetrized H beta t).symm

/-- A fourth-order truly physical original Wilson operator norm floor
with no claim that the operator norm equals the constant-vector integral. -/
theorem p4Q2PZ37ALH_originalPhysicalNorm_ge_genuineFourthMoment
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta + (beta ^ 2 / 2) * M2pair beta +
        (beta ^ 4 / 32) * M4pair beta) ≤
      ‖PW beta hbeta‖ := by
  have hLaplace :=
    p4Q2PZ37ALH_originalPairLaplace_ge_genuineFourthMoment H beta (-beta)
  have hScale :=
    mul_le_mul_of_nonneg_left hLaplace (Real.exp_pos (-(beta * pH))).le
  have hPhysical :=
    p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_pairLaplace
      H beta hbeta
  convert hScale.trans hPhysical using 1
  ring

/-- Original independent geometric identity box gives explicit finite-H
TWO- and FOURTH-order genuine Wilson norm corrections. The fourth
term is strictly positive for all beta>0, despite finite-volume decay. -/
theorem p4Q2PZ37ALH_originalPhysicalNorm_ge_explicitFourthBox
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta +
        (beta ^ 2 / 2) * (2 * kFloor beta * vBox) +
        (beta ^ 4 / 32) * (kFloor beta * (2 * vBox) ^ 2)) ≤
      ‖PW beta hbeta‖ := by
  have hVar := p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_le_sourceVariance H
  have hvPos := p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos H
  have hVPos := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hKF := (p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta).le
  have hSq : (2 * vBox) ^ 2 ≤ (2 * Vsrc) ^ 2 := by
    have hFactor :
        0 ≤ (Vsrc - vBox) * (Vsrc + vBox) :=
      mul_nonneg (sub_nonneg.mpr hVar) (by linarith only [hvPos, hVPos])
    nlinarith only [hFactor]
  have hM2 :=
    p4Q2PZ37ALF_originalPairSecondMoment_ge_identityBoxFloor H beta hbeta
  have hM4 :=
    (mul_le_mul_of_nonneg_left hSq hKF).trans
      (p4Q2PZ37ALH_originalPairFourth_ge_trueHaarVarianceSq H beta hbeta)
  have hScaled2 :=
    mul_le_mul_of_nonneg_left hM2
      (show 0 ≤ (beta ^ 2 / 2 : ℝ) by positivity)
  have hScaled4 :=
    mul_le_mul_of_nonneg_left hM4
      (show 0 ≤ (beta ^ 4 / 32 : ℝ) by positivity)
  have hInner :
      Zcross beta +
        (beta ^ 2 / 2) * (2 * kFloor beta * vBox) +
        (beta ^ 4 / 32) * (kFloor beta * (2 * vBox) ^ 2) ≤
      Zcross beta + (beta ^ 2 / 2) * M2pair beta +
        (beta ^ 4 / 32) * M4pair beta := by
    linarith only [hScaled2, hScaled4]
  exact (mul_le_mul_of_nonneg_left hInner
    (Real.exp_pos (-(beta * pH))).le).trans
      (p4Q2PZ37ALH_originalPhysicalNorm_ge_genuineFourthMoment
        H beta hbeta)

/-- A STRICT extra quartic gain beyond ALG's sharp quadratic identity
box floor, using ONLY independently established original true Haar
variance, crossing kernel positivity and beta>0. -/
theorem p4Q2PZ37ALH_originalPhysicalNorm_strictly_gt_ALG_boxFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta + (beta ^ 2 / 2) * (2 * kFloor beta * vBox)) <
      ‖PW beta hbeta.le‖ := by
  have hk := p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta
  have hv := p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos H
  have hTerm :
      0 < (beta ^ 4 / 32) * (kFloor beta * (2 * vBox) ^ 2) := by
    have hβ : 0 < (beta ^ 4 / 32 : ℝ) := by positivity
    have hsq : 0 < (2 * vBox) ^ 2 := by positivity
    exact mul_pos hβ (mul_pos hk hsq)
  have hInner :
      Zcross beta + (beta ^ 2 / 2) * (2 * kFloor beta * vBox) <
      Zcross beta + (beta ^ 2 / 2) * (2 * kFloor beta * vBox) +
        (beta ^ 4 / 32) * (kFloor beta * (2 * vBox) ^ 2) :=
    lt_add_of_pos_right _ hTerm
  have hScale :=
    mul_lt_mul_of_pos_left hInner (Real.exp_pos (-(beta * pH)))
  exact hScale.trans_le
    (p4Q2PZ37ALH_originalPhysicalNorm_ge_explicitFourthBox
      H beta hbeta.le)

/-- Exact unchanged physical H22 beta0 and plaquette count 292008.
This is a finite-H bound, NOT a certificate for H22 r22 or AJA. -/
theorem p4Q2PZ37ALH_originalH22_fixedCoupling_physicalNorm_fourthBox :
    Real.exp (-(p4Q2PZ37ADC_fixedCoupling * (292008 : ℝ))) *
      (p4Q2PZ37AIF_originalCrossingPartition 22
          p4Q2PZ37ADC_fixedCoupling +
        (p4Q2PZ37ADC_fixedCoupling ^ 2 / 2) *
          (2 * p4Q2PZ37ALE_originalCrossingKernelFloor 22
            p4Q2PZ37ADC_fixedCoupling *
            p4Q2PZ37ALF_originalIdentityBoxVarianceFloor 22) +
        (p4Q2PZ37ADC_fixedCoupling ^ 4 / 32) *
          (p4Q2PZ37ALE_originalCrossingKernelFloor 22
            p4Q2PZ37ADC_fixedCoupling *
            (2 * p4Q2PZ37ALF_originalIdentityBoxVarianceFloor 22) ^ 2)) ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          22 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
            p4Q2PZ37ADC_fixedCoupling_pos.le‖ := by
  have h :=
    p4Q2PZ37ALH_originalPhysicalNorm_ge_explicitFourthBox
      22 p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
  rw [p4Q2PZ37AKX_originalH22_plaquetteCount_exact] at h
  exact h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ALH_real_expSymm_ge_fourth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPairCrossingFourthMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPairSourceFourth_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPairCrossingFourth_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPairCrossingFourth_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalUnweightedPairFourth_ge_varianceSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPairFourth_ge_trueHaarVarianceSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPairCrossingFourth_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPairLaplace_ge_genuineFourthMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPhysicalNorm_ge_genuineFourthMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPhysicalNorm_ge_explicitFourthBox
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalPhysicalNorm_strictly_gt_ALG_boxFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALH_originalH22_fixedCoupling_physicalNorm_fourthBox

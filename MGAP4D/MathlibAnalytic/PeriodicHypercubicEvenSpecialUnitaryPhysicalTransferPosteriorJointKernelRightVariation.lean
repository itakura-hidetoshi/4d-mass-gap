import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointTransferExactBCF

/-!
# Actual normalized-kernel right variation and positive L2 envelopes

The right-link change of the raw Wilson kernel costs exp(8 beta). The continuous
joint half-density costs another exp(8 beta), including the continuous vacuum.
Thus the FULL normalized kernel has two-sided Harnack factor exp(16 beta).
Integrating its difference against a SIGNED input gives an actual pointwise
majorant with coefficient exp(16 beta)-1 and the positive transfer of |input|.

The positive envelope lives in the original joint law and its L2 norm is exactly
the existing normalized pair-transfer norm of the absolute input. A direct
one-link posterior residual is bounded by this L2 envelope; global initial
widths can also be fed to the existing chronological prefix propagation.

Only the displayed local multiplicative coefficient is volume independent.
The envelope, its sup norm and the full propagated energy need not be volume
uniform or spatially small. No support-distance tail, physicality, transfer
commutation or continuum claim is made. No measure or frozen vector is replaced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

local instance kernelRightVariationPairProbability (H N : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance kernelRightVariationJointProbability (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- Local change coefficient after retaining BOTH numerator and half-density. -/
def kernelRightVariationRate (beta : ℝ) : ℝ := Real.exp (16 * beta) - 1

theorem kernelRightVariationRate_nonneg (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ kernelRightVariationRate beta :=
  sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) hbeta))

@[simp] theorem kernelRightVariationRate_zero : kernelRightVariationRate 0 = 0 := by
  simp [kernelRightVariationRate]

private theorem abs_sub_le_of_two_sided_harnack (a b c : ℝ)
    (hc : 1 ≤ c) (hab : a ≤ c * b) (hba : b ≤ c * a) :
    |a - b| ≤ (c - 1) * a := by
  by_cases h : a ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith
  · have h' : b ≤ a := le_of_not_ge h
    rw [abs_of_nonneg (sub_nonneg.mpr h')]
    calc
      a - b ≤ (c - 1) * b := by linarith
      _ ≤ (c - 1) * a := mul_le_mul_of_nonneg_left h' (sub_nonneg.mpr hc)

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "μP" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "KP" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
local notation "OmegaC" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative H N hN beta hbeta
local notation "SqrtD" => continuousJointSqrtDensity H N hN beta hbeta
local notation "lambda" => ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "NormTransfer" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "Rate" => kernelRightVariationRate beta
local notation "Agree" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff

/-- The continuous joint half-density has the volume-independent exp(8 beta)
right-link Harnack factor. The vacuum contribution is retained explicitly. -/
theorem continuousJointSqrtDensity_right_harnack (B A : Cfg) (e : Link) (g h : GaugeT) :
    SqrtD (B, Function.update A e g) ≤
      Real.exp (8 * beta) * SqrtD (B, Function.update A e h) := by
  let c := Real.exp (8 * beta)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hK := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_le_exp_eight_mul_update_right
    H N hN beta hbeta B A e g h
  have hO := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_le_exp_eight_mul_update_right
    H N hN beta hbeta A e g h
  have hprod := mul_le_mul hK hO
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta (Function.update A e g)).le
    (mul_nonneg hc
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta B (Function.update A e h)).le)
  have hscale := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta)))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos H N hN beta hbeta B).le)
  have hw : continuousJointWeight H N hN beta hbeta (B, Function.update A e g) ≤
      c ^ 2 * continuousJointWeight H N hN beta hbeta (B, Function.update A e h) := by
    change lambda⁻¹ * (OmegaC B * K B (Function.update A e g) * OmegaC (Function.update A e g)) ≤
      c ^ 2 * (lambda⁻¹ * (OmegaC B * K B (Function.update A e h) * OmegaC (Function.update A e h)))
    convert hscale using 1 <;> ring
  change Real.sqrt (continuousJointWeight H N hN beta hbeta (B, Function.update A e g)) ≤
    c * Real.sqrt (continuousJointWeight H N hN beta hbeta (B, Function.update A e h))
  calc
    _ ≤ Real.sqrt (c ^ 2 * continuousJointWeight H N hN beta hbeta (B, Function.update A e h)) :=
      Real.sqrt_le_sqrt hw
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Kernel from the existing pair-Haar input to the original joint output. -/
def jointTransferKernel (x z : Joint) : ℝ :=
  (lambda ^ 2)⁻¹ * KP (x, z) / SqrtD z

/-- All factors in the actual normalized kernel are nonnegative. -/
theorem jointTransferKernel_nonneg (x z : Joint) :
    0 ≤ jointTransferKernel H N hN beta hbeta x z := by
  apply div_nonneg
  · exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (mul_pos
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta x.1 z.1)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta x.2 z.2)).le
  · exact (continuousJointSqrtDensity_pos H N hN beta hbeta z).le

/-- Actual numerator and reciprocal half-density combine to exp(16 beta). -/
theorem jointTransferKernel_right_harnack (x : Joint) (B A : Cfg)
    (e : Link) (g h : GaugeT) :
    jointTransferKernel H N hN beta hbeta x (B, Function.update A e g) ≤
      Real.exp (16 * beta) * jointTransferKernel H N hN beta hbeta x (B, Function.update A e h) := by
  let c := Real.exp (8 * beta)
  let zg : Joint := (B, Function.update A e g)
  let zh : Joint := (B, Function.update A e h)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hNum : KP (x, zg) ≤ c * KP (x, zh) := by
    have hMul := mul_le_mul_of_nonneg_left
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta x.2 A e g h)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta x.1 B).le
    change K x.1 B * K x.2 (Function.update A e g) ≤ c * (K x.1 B * K x.2 (Function.update A e h))
    convert hMul using 1; ring
  have hDen : SqrtD zh ≤ c * SqrtD zg :=
    continuousJointSqrtDensity_right_harnack H N hN beta hbeta B A e h g
  have hgpos := continuousJointSqrtDensity_pos H N hN beta hbeta zg
  have hhpos := continuousJointSqrtDensity_pos H N hN beta hbeta zh
  have hKP : 0 ≤ KP (x, zh) :=
    (mul_pos (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta x.1 zh.1)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta x.2 zh.2)).le
  have hcross : KP (x, zg) * SqrtD zh ≤ (c ^ 2 * KP (x, zh)) * SqrtD zg := by
    calc
      _ ≤ (c * KP (x, zh)) * SqrtD zh := mul_le_mul_of_nonneg_right hNum hhpos.le
      _ ≤ (c * KP (x, zh)) * (c * SqrtD zg) :=
        mul_le_mul_of_nonneg_left hDen (mul_nonneg hc hKP)
      _ = _ := by ring
  have hquot := (div_le_div_iff₀ hgpos hhpos).mpr hcross
  have hfinal := mul_le_mul_of_nonneg_left hquot (inv_nonneg.mpr (sq_nonneg lambda))
  have hc2 : Real.exp (16 * beta) = c ^ 2 := by
    dsimp [c]
    rw [pow_two, ← Real.exp_add]
    congr 1; ring
  rw [hc2]
  change (lambda ^ 2)⁻¹ * KP (x, zg) / SqrtD zg ≤
    c ^ 2 * ((lambda ^ 2)⁻¹ * KP (x, zh) / SqrtD zh)
  convert hfinal using 1 <;> ring

/-- Two-sided Harnack gives a signed difference bound against either endpoint. -/
theorem jointTransferKernel_right_difference (x : Joint) (B A : Cfg)
    (e : Link) (g h : GaugeT) :
    |jointTransferKernel H N hN beta hbeta x (B, Function.update A e g) -
      jointTransferKernel H N hN beta hbeta x (B, Function.update A e h)| ≤
      Rate * jointTransferKernel H N hN beta hbeta x (B, Function.update A e g) :=
  abs_sub_le_of_two_sided_harnack _ _ _
    (Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) hbeta))
    (jointTransferKernel_right_harnack H N hN beta hbeta x B A e g h)
    (jointTransferKernel_right_harnack H N hN beta hbeta x B A e h g)

/-- Every normalized kernel section is integrable against the original input. -/
theorem jointTransferKernel_integrable (f : PairL2) (z : Joint) :
    Integrable (fun x => jointTransferKernel H N hN beta hbeta x z * f x) μP := by
  convert (pairTransferIntegrand_integrable H N hN beta hbeta f z).const_mul
    ((lambda ^ 2)⁻¹ / SqrtD z) using 1
  funext x
  dsimp [jointTransferKernel]
  ring

/-- Pointwise integral representation of the already constructed exact BCF. -/
theorem jointTransferBCF_eq_integral_kernel (f : PairL2) (z : Joint) :
    jointTransferBCF H N hN beta hbeta f z =
      ∫ x, jointTransferKernel H N hN beta hbeta x z * f x ∂μP := by
  change (lambda ^ 2)⁻¹ * (∫ x, KP (x, z) * f x ∂μP) / SqrtD z = _
  calc
    _ = ((lambda ^ 2)⁻¹ / SqrtD z) * (∫ x, KP (x, z) * f x ∂μP) := by ring
    _ = ∫ x, ((lambda ^ 2)⁻¹ / SqrtD z) * (KP (x, z) * f x) ∂μP :=
      (integral_const_mul _ _).symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by dsimp [jointTransferKernel]; ring)

/-- Absolute value of the input as an ACTUAL vector in the same pair-Haar L2. -/
def pairAbsoluteInput (f : PairL2) : PairL2 :=
  (Lp.memLp f).norm.toLp (fun x => ‖f x‖)

theorem pairAbsoluteInput_ae_eq (f : PairL2) :
    pairAbsoluteInput H N f =ᵐ[μP] fun x => ‖f x‖ := (Lp.memLp f).norm.coeFn_toLp

/-- Positive envelope, built by the same physical transfer and half-density. -/
def jointTransferEnvelope (f : PairL2) : BoundedContinuousFunction Joint ℝ :=
  jointTransferBCF H N hN beta hbeta (pairAbsoluteInput H N f)

theorem jointTransferEnvelope_eq_integral (f : PairL2) (z : Joint) :
    jointTransferEnvelope H N hN beta hbeta f z =
      ∫ x, jointTransferKernel H N hN beta hbeta x z * ‖f x‖ ∂μP := by
  rw [jointTransferEnvelope, jointTransferBCF_eq_integral_kernel]
  apply integral_congr_ae
  filter_upwards [pairAbsoluteInput_ae_eq H N f] with x hx
  rw [hx]

theorem jointTransferEnvelope_nonneg (f : PairL2) (z : Joint) :
    0 ≤ jointTransferEnvelope H N hN beta hbeta f z := by
  rw [jointTransferEnvelope_eq_integral]
  exact integral_nonneg fun x => mul_nonneg
    (jointTransferKernel_nonneg H N hN beta hbeta x z) (norm_nonneg _)

/-- Lossless joint-L2 norm identity, with the original normalized transfer. -/
theorem jointTransferEnvelope_rep_norm (f : PairL2) :
    ‖BCFRep (jointTransferEnvelope H N hN beta hbeta f)‖ =
      ‖NormTransfer (pairAbsoluteInput H N f)‖ :=
  jointTransferBCF_rep_norm H N hN beta hbeta (pairAbsoluteInput H N f)

private theorem jointTransferKernel_normInput_integrable (f : PairL2) (z : Joint) :
    Integrable (fun x => jointTransferKernel H N hN beta hbeta x z * ‖f x‖) μP := by
  apply (jointTransferKernel_integrable H N hN beta hbeta f z).norm.congr
  exact Eventually.of_forall fun x => by
    change ‖jointTransferKernel H N hN beta hbeta x z * f x‖ =
      jointTransferKernel H N hN beta hbeta x z * ‖f x‖
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (jointTransferKernel_nonneg H N hN beta hbeta x z)]

/-- A SIGNED input is allowed. The endpoint-dependent positive envelope remains
inside the estimate, rather than being replaced by a global density floor. -/
theorem jointTransferBCF_right_update_variation (f : PairL2) (B A : Cfg)
    (e : Link) (g h : GaugeT) :
    |jointTransferBCF H N hN beta hbeta f (B, Function.update A e g) -
      jointTransferBCF H N hN beta hbeta f (B, Function.update A e h)| ≤
      Rate * jointTransferEnvelope H N hN beta hbeta f (B, Function.update A e g) := by
  let zg : Joint := (B, Function.update A e g)
  let zh : Joint := (B, Function.update A e h)
  have hDiff : jointTransferBCF H N hN beta hbeta f zg - jointTransferBCF H N hN beta hbeta f zh =
      ∫ x, (jointTransferKernel H N hN beta hbeta x zg -
        jointTransferKernel H N hN beta hbeta x zh) * f x ∂μP := by
    rw [jointTransferBCF_eq_integral_kernel, jointTransferBCF_eq_integral_kernel,
      ← integral_sub (jointTransferKernel_integrable H N hN beta hbeta f zg)
        (jointTransferKernel_integrable H N hN beta hbeta f zh)]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  change |jointTransferBCF H N hN beta hbeta f zg - jointTransferBCF H N hN beta hbeta f zh| ≤ _
  rw [hDiff, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, Rate * (jointTransferKernel H N hN beta hbeta x zg * ‖f x‖) ∂μP := by
      apply norm_integral_le_of_norm_le
        ((jointTransferKernel_normInput_integrable H N hN beta hbeta f zg).const_mul Rate)
      apply Eventually.of_forall
      intro x
      rw [norm_mul, Real.norm_eq_abs]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (jointTransferKernel_right_difference H N hN beta hbeta x B A e g h) (norm_nonneg (f x))
    _ = Rate * jointTransferEnvelope H N hN beta hbeta f zg := by
      rw [integral_const_mul, jointTransferEnvelope_eq_integral]

/-- Initial right-link variation of the concrete exact BCF, in the existing
AgreeOff interface. This is derived, not supplied as an oscillation premise. -/
theorem jointTransferBCF_right_variation (f : PairL2) (B : Cfg) (e : Link)
    (A C : Cfg) (hAgree : Agree A C e) :
    |jointTransferBCF H N hN beta hbeta f (B, A) - jointTransferBCF H N hN beta hbeta f (B, C)| ≤
      Rate * jointTransferEnvelope H N hN beta hbeta f (B, A) := by
  classical
  have hC : Function.update A e (C e) = C := by
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simpa only [Function.update_of_ne hj] using hAgree j hj
  simpa only [Function.update_eq_self, hC] using
    jointTransferBCF_right_update_variation H N hN beta hbeta f B A e (A e) (C e)

/-- Constructed nonnegative initial profile for all chronological prefixes. -/
def kernelRightInitialVariation (f : PairL2) : Link → ℝ :=
  fun _ => Rate * ‖jointTransferEnvelope H N hN beta hbeta f‖

theorem kernelRightInitialVariation_nonneg (f : PairL2) (e : Link) :
    0 ≤ kernelRightInitialVariation H N hN beta hbeta f e :=
  mul_nonneg (kernelRightVariationRate_nonneg beta hbeta) (norm_nonneg _)

theorem kernelRightInitialVariation_bound (f : PairL2) (B : Cfg) (e : Link)
    (A C : Cfg) (hAgree : Agree A C e) :
    |jointTransferBCF H N hN beta hbeta f (B, A) - jointTransferBCF H N hN beta hbeta f (B, C)| ≤
      kernelRightInitialVariation H N hN beta hbeta f e := by
  have hW : jointTransferEnvelope H N hN beta hbeta f (B, A) ≤
      ‖jointTransferEnvelope H N hN beta hbeta f‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      (jointTransferEnvelope H N hN beta hbeta f).norm_coe_le_norm (B, A))
  exact (jointTransferBCF_right_variation H N hN beta hbeta f B e A C hAgree).trans
    (mul_le_mul_of_nonneg_left hW (kernelRightVariationRate_nonneg beta hbeta))

/-- Averaging over the actual posterior fiber preserves the endpoint-dependent
majorant. No response data or small-coupling cutoff is required here. -/
theorem jointTransferPosteriorResidual_abs_le_envelope (f : PairL2) (e : Link) (z : Joint) :
    |jointTransferBCF H N hN beta hbeta f z -
      posteriorMean H N hN beta hbeta e (jointTransferBCF H N hN beta hbeta f) z| ≤
      Rate * jointTransferEnvelope H N hN beta hbeta f z := by
  classical
  let F := jointTransferBCF H N hN beta hbeta f
  let mu := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
    H N hN beta hbeta z.1 z.2 e
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta z.1 z.2 e
  have hUpdate : Continuous (fun g : GaugeT => Function.update z.2 e g) := by
    apply continuous_pi
    intro j
    by_cases hj : j = e
    · subst j; simpa only [Function.update_self] using (continuous_id : Continuous (fun g : GaugeT => g))
    · simpa only [Function.update_of_ne hj] using (continuous_const : Continuous (fun _ : GaugeT => z.2 j))
  have hFiber : Continuous (fun g : GaugeT => F (z.1, Function.update z.2 e g)) :=
    F.continuous.comp (continuous_const.prodMk hUpdate)
  have hOsc : ∀ g : GaugeT, |F z - F (z.1, Function.update z.2 e g)| ≤
      Rate * jointTransferEnvelope H N hN beta hbeta f z := by
    intro g
    apply jointTransferBCF_right_variation H N hN beta hbeta f z.1 e z.2
    intro j hj
    rw [Function.update_of_ne hj]
  have hInt := periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorConditionalIntegral_direct_difference_abs_le
    H N hN beta hbeta z.1 z.2 e (fun _ : GaugeT => F z)
    (fun g : GaugeT => F (z.1, Function.update z.2 e g)) continuous_const hFiber
    (Rate * jointTransferEnvelope H N hN beta hbeta f z) hOsc
  change |(∫ _ : GaugeT, F z ∂mu) - (∫ g : GaugeT, F (z.1, Function.update z.2 e g) ∂mu)| ≤ _ at hInt
  have hConst : (∫ _ : GaugeT, F z ∂mu) = F z := by simp
  rw [hConst] at hInt
  exact hInt

/-- Genuine one-link L2 residual energy has a constructed, coefficient-one
positive envelope; no volume count or inverse-density comparison is inserted. -/
theorem jointTransferPosteriorResidualEnergy_le (f : PairL2) (e : Link) :
    posteriorStageResidualEnergy H N hN beta hbeta [] e (jointTransferBCF H N hN beta hbeta f) ≤
      Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N f)‖ ^ 2 := by
  let F := jointTransferBCF H N hN beta hbeta f
  let W := jointTransferEnvelope H N hN beta hbeta f
  have hWlp : MemLp (fun z => W z) 2 μJ :=
    MemLp.of_bound W.continuous.aestronglyMeasurable ‖W‖ (Eventually.of_forall W.norm_coe_le_norm)
  have h := posteriorStageResidualEnergy_le_of_ae_majorant H N hN beta hbeta [] e F
    F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm
    (fun z => Rate * W z) (hWlp.const_mul Rate) (Eventually.of_forall fun z => by
      change ‖F z - posteriorMean H N hN beta hbeta e F z‖ ≤ ‖Rate * W z‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (kernelRightVariationRate_nonneg beta hbeta)
          (jointTransferEnvelope_nonneg H N hN beta hbeta f z))]
      exact jointTransferPosteriorResidual_abs_le_envelope H N hN beta hbeta f e z)
  have hInt : (∫ z, W z ^ 2 ∂μJ) = ‖BCFRep W‖ ^ 2 := by
    rw [realL2_norm_sq_eq_integral_norm_sq (BCFRep W)]
    apply integral_congr_ae
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μJ ℝ W] with z hz
    change W z ^ 2 = ‖(BoundedContinuousFunction.toLp 2 μJ ℝ W) z‖ ^ 2
    rw [hz]
    simp only [Real.norm_eq_abs, sq_abs]
  have hScale : (∫ z, (Rate * W z) ^ 2 ∂μJ) =
      Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N f)‖ ^ 2 := by
    simp_rw [mul_pow]
    rw [integral_const_mul, hInt]
    rw [jointTransferEnvelope_rep_norm]
  exact h.trans_eq hScale

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic

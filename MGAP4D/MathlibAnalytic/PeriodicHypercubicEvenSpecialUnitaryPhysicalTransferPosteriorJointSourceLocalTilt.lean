import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointResamplingDirichlet

/-!
# Source-one-link structure of the actual signed kernel defect

A right output-link update factors the ORIGINAL normalized kernel as
  J(y,z') = c(z,e,g) * ell(y.right(e), z.right(e), g) * J(y,z).
Only ell depends on the source, and it sees exactly ONE source link. The output
factor c retains the spatial action AND the original joint half-density.
The local source multiplier satisfies |ell-1| <= exp(2 beta)-1.

The signed response V_x = integral J (ell-1) x is constructed before taking
absolute values. The original defect is exactly (1-c) O_x - c V_x. A two-input
cross-multiplied contrast cancels the common additive output drift, without
dividing by an observable or replacing the original frozen vector.

These are model-derived locality identities and a local multiplier bound, NOT
spatial clustering of V_x or the actual frozen energy. The kernel-weighted input
may still be nonlocal. The output drift remains in the original energy, and no
independence, source-support cancellation, new law or physicality is assumed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped BigOperators

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

namespace GroundStatePosteriorJoint

/-- The source dependence of one right-link update is a single Wilson factor. -/
def sourceRightLinkTilt (N : ℕ) (beta : ℝ)
    (u a g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta * (specialUnitaryWilsonPlaquetteEnergy N (u⁻¹ * g) -
    specialUnitaryWilsonPlaquetteEnergy N (u⁻¹ * a)))

theorem sourceRightLinkTilt_pos (N : ℕ) (beta : ℝ)
    (u a g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 < sourceRightLinkTilt N beta u a g := Real.exp_pos _

@[simp] theorem sourceRightLinkTilt_current (N : ℕ) (beta : ℝ)
    (u a : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    sourceRightLinkTilt N beta u a a = 1 := by
  simp [sourceRightLinkTilt]

@[simp] theorem sourceRightLinkTilt_beta_zero (N : ℕ)
    (u a g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    sourceRightLinkTilt N 0 u a g = 1 := by
  simp [sourceRightLinkTilt]

/-- Consecutive changes on this same source link compose exactly. -/
theorem sourceRightLinkTilt_cocycle (N : ℕ) (beta : ℝ)
    (u a g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    sourceRightLinkTilt N beta u a g * sourceRightLinkTilt N beta u g h =
      sourceRightLinkTilt N beta u a h := by
  unfold sourceRightLinkTilt
  rw [← Real.exp_add]
  congr 1
  ring

/-- The source multiplier uses width two, not the full half-density width. -/
theorem sourceRightLinkTilt_sub_one_abs_le (N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u a g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |sourceRightLinkTilt N beta u a g - 1| ≤ Real.exp (2 * beta) - 1 := by
  let t := -beta * (specialUnitaryWilsonPlaquetteEnergy N (u⁻¹ * g) -
    specialUnitaryWilsonPlaquetteEnergy N (u⁻¹ * a))
  have hd := abs_le.mp (specialUnitaryWilsonPlaquetteEnergy_sub_abs_le_two
    N hN (u⁻¹ * g) (u⁻¹ * a))
  have htLow : -(2 * beta) ≤ t := by
    have hh := mul_le_mul_of_nonneg_left hd.2 hbeta
    dsimp [t]
    nlinarith
  have htHigh : t ≤ 2 * beta := by
    have hh := mul_le_mul_of_nonneg_left hd.1 hbeta
    dsimp [t]
    nlinarith
  have hUpper : sourceRightLinkTilt N beta u a g ≤ Real.exp (2 * beta) :=
    Real.exp_le_exp.mpr htHigh
  have hOne : 1 ≤ Real.exp (2 * beta) * sourceRightLinkTilt N beta u a g := by
    change 1 ≤ Real.exp (2 * beta) * Real.exp t
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith)
  have hRate : 0 ≤ Real.exp (2 * beta) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  by_cases h : sourceRightLinkTilt N beta u a g ≤ 1
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hs := mul_le_mul_of_nonneg_left h hRate
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
    linarith

section GeneralCarrier

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "μP" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure H N hN beta hbeta
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
local notation "SA" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
local notation "CA" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N
local notation "Act" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N
local notation "PE" => specialUnitaryWilsonPlaquetteEnergy N
local notation "SqrtD" => continuousJointSqrtDensity H N hN beta hbeta
local notation "lam" => ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖
local notation "J" => jointTransferKernel H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta

/-- Exact single summand, before the previous crossing-action oscillation bound. -/
theorem crossingAction_right_update_sub (A B : Cfg) (e : Link) (g : GaugeT) :
    CA A (Function.update B e g) - CA A B =
      PE ((A e)⁻¹ * g) - PE ((A e)⁻¹ * B e) := by
  classical
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_eq_finset_sum,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_eq_finset_sum,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single e]
  · simp only [Function.update_self]
  · intro t _ ht
    rw [Function.update_of_ne ht]
    exact sub_self _
  · simp

/-- Keep the output spatial-action change separate from the one-link source factor. -/
theorem oneSlabKernel_right_update_eq_sourceTilt (A B : Cfg) (e : Link) (g : GaugeT) :
    K A (Function.update B e g) =
      Real.exp (-beta * (1 / 2 : ℝ) * (SA (Function.update B e g) - SA B)) *
        sourceRightLinkTilt N beta (A e) (B e) g * K A B := by
  have hAction : Act A (Function.update B e g) - Act A B =
      (PE ((A e)⁻¹ * g) - PE ((A e)⁻¹ * B e)) +
        (1 / 2 : ℝ) * (SA (Function.update B e g) - SA B) := by
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    linarith [crossingAction_right_update_sub H N A B e g]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    sourceRightLinkTilt, ← Real.exp_add, ← Real.exp_add]
  congr 1
  linear_combination -beta * hAction

/-- Output-only factor, including the ORIGINAL joint half-density. -/
def outputRightLinkTilt (z : Joint) (e : Link) (g : GaugeT) : ℝ :=
  Real.exp (-beta * (1 / 2 : ℝ) * (SA (Function.update z.2 e g) - SA z.2)) *
    SqrtD z / SqrtD (z.1, Function.update z.2 e g)

theorem outputRightLinkTilt_pos (z : Joint) (e : Link) (g : GaugeT) :
    0 < outputRightLinkTilt H N hN beta hbeta z e g :=
  div_pos (mul_pos (Real.exp_pos _) (continuousJointSqrtDensity_pos H N hN beta hbeta z))
    (continuousJointSqrtDensity_pos H N hN beta hbeta _)

/-- Actual kernel update: all source dependence outside J is ONE source link. -/
theorem jointTransferKernel_right_update_eq_sourceTilt (y z : Joint) (e : Link) (g : GaugeT) :
    J y (z.1, Function.update z.2 e g) =
      outputRightLinkTilt H N hN beta hbeta z e g *
        sourceRightLinkTilt N beta (y.2 e) (z.2 e) g * J y z := by
  change (lam ^ 2)⁻¹ * (K y.1 z.1 * K y.2 (Function.update z.2 e g)) /
      SqrtD (z.1, Function.update z.2 e g) =
    outputRightLinkTilt H N hN beta hbeta z e g *
      sourceRightLinkTilt N beta (y.2 e) (z.2 e) g *
        ((lam ^ 2)⁻¹ * (K y.1 z.1 * K y.2 z.2) / SqrtD z)
  rw [oneSlabKernel_right_update_eq_sourceTilt H N beta y.2 z.2 e g]
  unfold outputRightLinkTilt
  field_simp [(continuousJointSqrtDensity_pos H N hN beta hbeta z).ne',
    (continuousJointSqrtDensity_pos H N hN beta hbeta (z.1, Function.update z.2 e g)).ne',
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos H N hN beta hbeta).ne']

/-- Changing any other source coordinates does not change the kernel update ratio.
Cross multiplication avoids all division by the kernel or an observable. -/
theorem jointTransferKernel_update_cross_eq_of_sourceLink_eq
    (y v z : Joint) (e : Link) (g : GaugeT) (hlink : y.2 e = v.2 e) :
    J y (z.1, Function.update z.2 e g) * J v z =
      J v (z.1, Function.update z.2 e g) * J y z := by
  rw [jointTransferKernel_right_update_eq_sourceTilt H N hN beta hbeta y z e g,
    jointTransferKernel_right_update_eq_sourceTilt H N hN beta hbeta v z e g, hlink]
  ring

/-- Signed source response to the ONE-link multiplier; no absolute input. -/
def sourceLinkResponse (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) : ℝ :=
  ∫ y, J y z * (sourceRightLinkTilt N beta (y.2 e) (z.2 e) g - 1) * x y ∂μP

private theorem sourceLinkResponse_integrand_eq
    (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) (y : Joint) :
    J y z * (sourceRightLinkTilt N beta (y.2 e) (z.2 e) g - 1) * x y =
      (outputRightLinkTilt H N hN beta hbeta z e g)⁻¹ *
        (J y (z.1, Function.update z.2 e g) * x y) - J y z * x y := by
  rw [jointTransferKernel_right_update_eq_sourceTilt H N hN beta hbeta y z e g]
  field_simp [(outputRightLinkTilt_pos H N hN beta hbeta z e g).ne']

/-- Integrability follows from the two existing actual kernel sections. -/
theorem sourceLinkResponse_integrable (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Integrable (fun y => J y z *
      (sourceRightLinkTilt N beta (y.2 e) (z.2 e) g - 1) * x y) μP := by
  have h1 := (jointTransferKernel_integrable H N hN beta hbeta x
    (z.1, Function.update z.2 e g)).const_mul
      (outputRightLinkTilt H N hN beta hbeta z e g)⁻¹
  have h2 := jointTransferKernel_integrable H N hN beta hbeta x z
  exact (h1.sub h2).congr (Eventually.of_forall fun y =>
    (sourceLinkResponse_integrand_eq H N hN beta hbeta x e z g y).symm)

theorem sourceLinkResponse_eq (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    sourceLinkResponse H N hN beta hbeta x e z g =
      (outputRightLinkTilt H N hN beta hbeta z e g)⁻¹ *
        Obs x (z.1, Function.update z.2 e g) - Obs x z := by
  unfold sourceLinkResponse
  simp_rw [sourceLinkResponse_integrand_eq H N hN beta hbeta x e z g]
  rw [integral_sub
    ((jointTransferKernel_integrable H N hN beta hbeta x
      (z.1, Function.update z.2 e g)).const_mul
        (outputRightLinkTilt H N hN beta hbeta z e g)⁻¹)
    (jointTransferKernel_integrable H N hN beta hbeta x z),
    integral_const_mul, ← jointTransferBCF_eq_integral_kernel,
    ← jointTransferBCF_eq_integral_kernel]

/-- Constructed local multiplier estimate, retaining the existing positive envelope. -/
theorem sourceLinkResponse_abs_le_envelope (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |sourceLinkResponse H N hN beta hbeta x e z g| ≤
      (Real.exp (2 * beta) - 1) * jointTransferEnvelope H N hN beta hbeta x z := by
  have hW : Integrable (fun y => J y z * ‖x y‖) μP := by
    apply (jointTransferKernel_integrable H N hN beta hbeta x z).norm.congr
    exact Eventually.of_forall fun y => by
      change ‖J y z * x y‖ = J y z * ‖x y‖
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (jointTransferKernel_nonneg H N hN beta hbeta y z)]
  rw [← Real.norm_eq_abs]
  unfold sourceLinkResponse
  calc
    _ ≤ ∫ y, (Real.exp (2 * beta) - 1) * (J y z * ‖x y‖) ∂μP := by
      apply norm_integral_le_of_norm_le (hW.const_mul (Real.exp (2 * beta) - 1))
      apply Eventually.of_forall
      intro y
      calc
        _ = J y z * |sourceRightLinkTilt N beta (y.2 e) (z.2 e) g - 1| * ‖x y‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (jointTransferKernel_nonneg H N hN beta hbeta y z), Real.norm_eq_abs]
        _ ≤ J y z * (Real.exp (2 * beta) - 1) * ‖x y‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (sourceRightLinkTilt_sub_one_abs_le N hN beta hbeta (y.2 e) (z.2 e) g)
              (jointTransferKernel_nonneg H N hN beta hbeta y z)) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul, jointTransferEnvelope_eq_integral]

/-- Exact drift/response decomposition of #5222's ORIGINAL signed difference. -/
theorem jointTransferLinkDifference_eq_sourceTilt (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    jointTransferLinkDifference H N hN beta hbeta x e z g =
      (1 - outputRightLinkTilt H N hN beta hbeta z e g) * Obs x z -
        outputRightLinkTilt H N hN beta hbeta z e g *
          sourceLinkResponse H N hN beta hbeta x e z g := by
  rw [jointTransferLinkDifference_eq, sourceLinkResponse_eq]
  field_simp [(outputRightLinkTilt_pos H N hN beta hbeta z e g).ne']
  ring

/-- A two-input contrast cancels common additive output drift exactly.
This does NOT remove that drift from either original observable separately. -/
theorem jointTransferSourceContrast_eq (x v : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Obs v z * jointTransferLinkDifference H N hN beta hbeta x e z g -
      Obs x z * jointTransferLinkDifference H N hN beta hbeta v e z g =
    outputRightLinkTilt H N hN beta hbeta z e g *
      (Obs x z * sourceLinkResponse H N hN beta hbeta v e z g -
        Obs v z * sourceLinkResponse H N hN beta hbeta x e z g) := by
  rw [jointTransferLinkDifference_eq_sourceTilt, jointTransferLinkDifference_eq_sourceTilt]
  ring

/-- The COMBINED drift/response square is genuinely posterior integrable. -/
theorem sourceTiltDefect_sq_posterior_integrable (x : PairL2) (e : Link) (z : Joint) :
    Integrable (fun g => ((1 - outputRightLinkTilt H N hN beta hbeta z e g) * Obs x z -
      outputRightLinkTilt H N hN beta hbeta z e g *
        sourceLinkResponse H N hN beta hbeta x e z g) ^ 2) (Nu z.1 z.2 e) := by
  simpa only [jointTransferLinkDifference_eq_sourceTilt] using
    jointTransferLinkDifference_sq_posterior_integrable H N hN beta hbeta x e z

/-- The COMBINED square also has a genuine outer joint integral. -/
theorem sourceTiltDefect_sq_joint_integrable (x : PairL2) (e : Link) :
    Integrable (fun z => ∫ g,
      ((1 - outputRightLinkTilt H N hN beta hbeta z e g) * Obs x z -
        outputRightLinkTilt H N hN beta hbeta z e g *
          sourceLinkResponse H N hN beta hbeta x e z g) ^ 2 ∂Nu z.1 z.2 e) μJ := by
  simpa only [jointTransferLinkDifference_eq_sourceTilt] using
    jointTransferLinkResamplingSquare_integrable H N hN beta hbeta x e

/-- Exact substitution in the existing resampling energy, without separate-term bounds. -/
theorem jointTransferLinkResamplingEnergy_eq_sourceTilt (x : PairL2) (e : Link) :
    jointTransferLinkResamplingEnergy H N hN beta hbeta x e =
      ∫ z, ∫ g, ((1 - outputRightLinkTilt H N hN beta hbeta z e g) * Obs x z -
        outputRightLinkTilt H N hN beta hbeta z e g *
          sourceLinkResponse H N hN beta hbeta x e z g) ^ 2 ∂Nu z.1 z.2 e ∂μJ := by
  unfold jointTransferLinkResamplingEnergy
  simp only [jointTransferLinkDifference_eq_sourceTilt]

end GeneralCarrier

section FrozenFamily

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure Hn 2 Pos (beta n) (hbeta n)
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure Hn 2 Pos (beta n) (hbeta n)
local notation "Orbit" => physicalYangMillsSU2AdjacentFinePairOrbitVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "FrozenVec" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "Obs" => jointTransferBCF Hn 2 Pos (beta n) (hbeta n)
local notation "Out" => outputRightLinkTilt Hn 2 Pos (beta n) (hbeta n)
local notation "Resp" => sourceLinkResponse Hn 2 Pos (beta n) (hbeta n)

/-- The actual frozen family, with its old orbit and final coupling, has this
exact 1/12 source-local formula. No decay of either term is asserted. -/
theorem fineFrozenInitialEnergy_eq_sourceTilt :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n) FrozenVec =
      (1 / 12 : ℝ) * ∑ e : Link,
        ∫ z, ∫ g, ((1 - Out z e g) * Obs Orbit z - Out z e g * Resp Orbit e z g) ^ 2
          ∂Nu z.1 z.2 e ∂μJ := by
  rw [fineFrozenInitialEnergy_eq_resampling]
  simp_rw [jointTransferLinkResamplingEnergy_eq_sourceTilt]

end FrozenFamily

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
